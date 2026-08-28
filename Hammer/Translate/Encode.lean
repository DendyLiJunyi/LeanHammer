import Hammer.Basic
import Hammer.Util
import Hammer.Translate.SMTLib
import Hammer.Premise.Features

/-!
# Encoding Lean `Expr` into SMT-LIB

This is the only step in the pipeline with real content. CIC is far more expressive than
many-sorted first-order logic, so the translation is necessarily partial. The trade-offs:

* **Translate precisely what we understand**: propositional connectives, quantifiers,
  equality, and arithmetic and comparisons over `Nat` / `Int` / `Real`.
* **Abstract everything else into uninterpreted symbols.** Abstraction preserves `unsat`:
  it only discards equational information, making the problem harder rather than easier,
  so a solver's `unsat` verdict remains trustworthy.
* **Drop premises that fail to translate.** Only a failure on the goal aborts the call.

## Handling `Nat`

`Nat` maps to SMT's `Int`, with a `≥ 0` guard on every `Nat` quantifier and a
non-negativity axiom for every symbol returning `Nat`. Truncated subtraction `a - b`
becomes `(ite (<= b a) (- a b) 0)`; division and modulo get `ite` guards matching Lean's
"division by zero is zero, modulo by zero is the dividend". Lean's `Int` division happens
to be exactly SMT-LIB's Euclidean `div` / `mod` (measured: `(-7)/2 = -4`, `(-7)%2 = 1`),
so only the zero-divisor guard is needed.

## Known incompleteness and risk

SMT assumes every sort is nonempty, whereas Lean types can be empty, which is unsound for
`∃` over an empty type. See `Config.assumeNonempty`: by default we require a synthesizable
`Nonempty` instance before declaring an uninterpreted sort.
-/

namespace Hammer

open Lean Meta

/-- An SMT sort, plus one bit recording that it really came from Lean's `Nat`. -/
structure SortInfo where
  smt   : String
  isNat : Bool := false
  deriving Inhabited, BEq

def SortInfo.bool : SortInfo := ⟨"Bool", false⟩
def SortInfo.int  : SortInfo := ⟨"Int", false⟩
def SortInfo.nat  : SortInfo := ⟨"Int", true⟩
def SortInfo.real : SortInfo := ⟨"Real", false⟩

/-- The encoder's read-only environment: variables bound by SMT quantifiers, plus the
configuration. -/
structure EncCtx where
  bound : Std.HashMap FVarId (String × SortInfo) := ∅
  cfg   : Hammer.Config := {}

/-- The encoder's mutable state. `decls` accumulates in order of first use, which
automatically satisfies SMT-LIB's declare-before-use requirement. -/
structure EncState where
  sorts   : Std.HashMap ExprStructEq SortInfo := ∅
  syms    : Std.HashMap ExprStructEq (String × SortInfo) := ∅
  decls   : Array Command := #[]
  /-- Axioms emitted alongside a declaration, e.g. non-negativity for `Nat` symbols. -/
  sideAx  : Array Sexp := #[]
  used    : Std.HashSet String := ∅
  counter : Nat := 0

abbrev EncM := ReaderT EncCtx (StateRefT EncState MetaM)

/-- Placeholder standing for a translated value argument inside an abstraction key. Used
only for hashing; never elaborated. -/
private def hole : Expr := mkConst `Hammer.«_hole»

private def freshSym (base : String) : EncM String := do
  let s ← get
  let base := if base.isEmpty then "f" else base
  if !s.used.contains base then
    modify fun s => { s with used := s.used.insert base }
    return base
  let nm := s!"{base}_{s.counter}"
  modify fun s => { s with used := s.used.insert nm, counter := s.counter + 1 }
  return nm

private def freshVar : EncM String := do
  let s ← get
  modify fun s => { s with counter := s.counter + 1 }
  return s!"x{s.counter}"

/--
Whether `e` mentions a variable currently in scope of an SMT quantifier.

This is the shared source of two unsoundnesses: abstracting `Fin n` into a sort
independent of `n`, or abstracting `@Foo n a` into a symbol independent of `n`. Once the
dependency is lost, a true statement turns into a contradiction.
(`Fin.pos : ∀ {n} (i : Fin n), 0 < n` did exactly that, making every problem unsat.)
-/
private def mentionsBound (e : Expr) : EncM Bool := do
  let bound := (← read).bound
  if bound.isEmpty then return false
  return e.hasAnyFVar fun fid => bound.contains fid

private def intLit (i : Int) : Sexp :=
  if i < 0 then Sexp.mk "-" [.atom (toString (-i))] else .atom (toString i)

/-- Guess a readable base name for an SMT symbol from an expression. -/
private def baseNameOf (e : Expr) : MetaM String := do
  match e.getAppFn with
  | .const n _ => return sanitize n
  | .fvar fid  => return sanitize (← fid.getUserName)
  | _          => return "t"

/-- Type to SMT sort. Throws when unencodable; the caller decides whether to drop the
premise or fail outright. -/
partial def toSortInfo (t : Expr) : EncM SortInfo := do
  let t ← instantiateMVars t
  let t ← whnfR t
  match t with
  | .sort u => if u.isZero then return .bool else throwError "sort {t} is not encodable"
  | .forallE .. => throwError "function type {t} is higher-order and not encodable"
  | _ =>
    if ← isProp t then throwError "{t} is a proposition; its elements are proofs"
    if (← isClass? t).isSome then throwError "{t} is a type class"
    match t.getAppFnArgs with
    | (``Nat, _)  => return .nat
    | (``Int, _)  => return .int
    | (``Bool, _) => return .bool
    -- `Real` / `Rat` come from Mathlib; match on the name so we need no dependency.
    | (n, _) =>
      if n == `Real || n == `Rat || n == `NNRat then return .real
      if ← mentionsBound t then
        throwError "type {t} depends on a quantified variable; abstracting it into a sort would discard that dependency"
      let key : ExprStructEq := t
      if let some si := (← get).sorts[key]? then return si
      if t.hasExprMVar then throwError "type {t} contains metavariables"
      unless (← read).cfg.assumeNonempty do
        let .sort u ← whnfR (← inferType t)
          | throwError "{t} is not a type"
        unless (← trySynthInstance (mkApp (mkConst ``Nonempty [u]) t)) matches .some _ do
          throwError "cannot establish that {t} is nonempty; SMT sorts must be nonempty"
      let nm ← freshSym (← baseNameOf t)
      let si : SortInfo := ⟨nm, false⟩
      modify fun s => { s with
        sorts := s.sorts.insert key si
        decls := s.decls.push (.declareSort nm) }
      return si

/-- Whether an argument can be translated as a value. If not, it belongs to the symbol's
identity instead (type arguments, instances, proofs). -/
private def classifyArg (a : Expr) : EncM (Option SortInfo) := do
  try
    let t ← inferType a
    return some (← toSortInfo t)
  catch _ => return none

/-- Built-in arithmetic, returning an operator tag and its arguments. The tag is our own
notation, not directly an SMT name. -/
private def arithOp? (e : Expr) : Option (String × Array Expr) :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_,_,_,_,a,b]) => some ("+", #[a,b])
  | (``HSub.hSub, #[_,_,_,_,a,b]) => some ("-", #[a,b])
  | (``HMul.hMul, #[_,_,_,_,a,b]) => some ("*", #[a,b])
  | (``HDiv.hDiv, #[_,_,_,_,a,b]) => some ("/", #[a,b])
  | (``HMod.hMod, #[_,_,_,_,a,b]) => some ("%", #[a,b])
  | (``Neg.neg,   #[_,_,a])       => some ("neg", #[a])
  | (``Nat.add,   #[a,b])         => some ("+", #[a,b])
  | (``Nat.sub,   #[a,b])         => some ("-", #[a,b])
  | (``Nat.mul,   #[a,b])         => some ("*", #[a,b])
  | (``Nat.div,   #[a,b])         => some ("/", #[a,b])
  | (``Nat.mod,   #[a,b])         => some ("%", #[a,b])
  | (``Int.add,   #[a,b])         => some ("+", #[a,b])
  | (``Int.sub,   #[a,b])         => some ("-", #[a,b])
  | (``Int.mul,   #[a,b])         => some ("*", #[a,b])
  | (``Int.neg,   #[a])           => some ("neg", #[a])
  | (``Nat.succ,  #[a])           => some ("succ", #[a])
  | _ => none

/-- Built-in comparisons, returning the SMT relation name and both arguments. -/
private def cmpOp? (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LT.lt, #[_,_,a,b]) => some ("<", a, b)
  | (``LE.le, #[_,_,a,b]) => some ("<=", a, b)
  | (``GT.gt, #[_,_,a,b]) => some (">", a, b)
  | (``GE.ge, #[_,_,a,b]) => some (">=", a, b)
  | (``Nat.lt, #[a,b])    => some ("<", a, b)
  | (``Nat.le, #[a,b])    => some ("<=", a, b)
  | (``Int.lt, #[a,b])    => some ("<", a, b)
  | (``Int.le, #[a,b])    => some ("<=", a, b)
  | _ => none

/-- Split `p : α → Prop` into a binder name and a body, eta-expanding when needed. -/
private def asPredicate (p : Expr) : MetaM (Name × Expr) := do
  match p with
  | .lam n _ b _ => return (n, b)
  | _ => return (`x, mkApp p (.bvar 0) |>.liftLooseBVars 0 0)

/-- Non-negativity axiom for a symbol returning `Nat`, with guards on any `Nat`
arguments. -/
private def mkNatBound (nm : String) (argSorts : Array SortInfo) : EncM Sexp := do
  if argSorts.isEmpty then
    return Sexp.mk ">=" [.atom nm, .atom "0"]
  let mut binders : List Sexp := []
  let mut vars : List Sexp := []
  let mut guards : List Sexp := []
  for (si, i) in argSorts.zipIdx do
    let v := s!"n{i}"
    binders := binders ++ [.app [.atom v, .atom si.smt]]
    vars := vars ++ [.atom v]
    if si.isNat then guards := guards ++ [Sexp.mk ">=" [.atom v, .atom "0"]]
  let body := Sexp.implies (Sexp.andN guards) (Sexp.mk ">=" [Sexp.mk nm vars, .atom "0"])
  return .app [.atom "forall", .app binders, body]


mutual

/-- Translate a proposition into an SMT formula. -/
partial def encodeForm (e : Expr) : EncM Sexp := do
  let e ← instantiateMVars e
  match e with
  | .forallE n d b _ =>
      if ← isProp d then
        if b.hasLooseBVars then
          throwError "a ∀ whose body depends on the proof is not encodable"
        return Sexp.implies (← encodeForm d) (← encodeForm b)
      else
        let si ← toSortInfo d
        withLocalDeclD n d fun x => do
          let v ← freshVar
          let body ← withReader (fun c => { c with bound := c.bound.insert x.fvarId! (v, si) }) do
            encodeForm (b.instantiate1 x)
          let body := if si.isNat then Sexp.implies (Sexp.mk ">=" [.atom v, .atom "0"]) body else body
          return .app [.atom "forall", .app [.app [.atom v, .atom si.smt]], body]
  | .mdata _ b => encodeForm b
  | .letE .. => encodeForm (← whnf e)
  | _ =>
    match e.getAppFnArgs with
    | (``True,  _)        => return Sexp.true'
    | (``False, _)        => return Sexp.false'
    | (``Not, #[a])       => return Sexp.not' (← encodeForm a)
    | (``And, #[a,b])     => return Sexp.andN [← encodeForm a, ← encodeForm b]
    | (``Or,  #[a,b])     => return Sexp.orN  [← encodeForm a, ← encodeForm b]
    | (``Iff, #[a,b])     => return Sexp.mk "=" [← encodeForm a, ← encodeForm b]
    | (``Eq,  #[α,a,b])   => encodeEq α a b false
    | (``Ne,  #[α,a,b])   => encodeEq α a b true
    | (``Exists, #[α, p]) =>
        let si ← toSortInfo α
        let (n, body) ← asPredicate p
        withLocalDeclD n α fun x => do
          let v ← freshVar
          let body ← withReader (fun c => { c with bound := c.bound.insert x.fvarId! (v, si) }) do
            encodeForm (body.instantiate1 x)
          let body := if si.isNat then Sexp.andN [Sexp.mk ">=" [.atom v, .atom "0"], body] else body
          return .app [.atom "exists", .app [.app [.atom v, .atom si.smt]], body]
    | (``ite, #[α, c, _, t, f]) =>
        if ← isProp α then
          return Sexp.mk "ite" [← encodeForm c, ← encodeForm t, ← encodeForm f]
        else throwError "the branches of this ite are not propositions"
    | _ =>
      if let some (op, a, b) := cmpOp? e then
        let (ta, sa) ← encodeTerm a
        let (tb, _)  ← encodeTerm b
        if sa.smt == "Int" || sa.smt == "Real" then
          return Sexp.mk op [ta, tb]
        else throwError "comparison sort {sa.smt} is not numeric"
      let (s, si) ← encodeApp e
      if si.smt != "Bool" then throwError "{e} is not a proposition"
      return s

/-- `a = b` and `a ≠ b`. Equality between propositions degenerates to `↔`. -/
partial def encodeEq (α a b : Expr) (negated : Bool) : EncM Sexp := do
  let eq ←
    if (← whnfR α) matches .sort .zero then
      pure (Sexp.mk "=" [← encodeForm a, ← encodeForm b])
    else
      let (ta, _) ← encodeTerm a
      let (tb, _) ← encodeTerm b
      pure (Sexp.mk "=" [ta, tb])
  return if negated then Sexp.not' eq else eq

/-- Translate a term into an SMT term, along with its sort. -/
partial def encodeTerm (e : Expr) : EncM (Sexp × SortInfo) := do
  let e ← instantiateMVars e
  -- Propositions become `Bool` terms.
  if ← isProp (← inferType e) then
    return (← encodeForm e, .bool)
  match e with
  | .mdata _ b => encodeTerm b
  | .letE .. => encodeTerm (← whnf e)
  | _ =>
  let si ← toSortInfo (← inferType e)
  -- Numeric literals
  if si.smt == "Int" then
    if let some n := e.nat? then return (intLit (Int.ofNat n), si)
    if let some i := e.int? then return (intLit i, si)
  match e.getAppFnArgs with
  | (``Bool.true, _)  => return (Sexp.true', .bool)
  | (``Bool.false, _) => return (Sexp.false', .bool)
  | (``ite, #[_, c, _, t, f]) =>
      let cf ← encodeForm c
      let (tt, _) ← encodeTerm t
      let (tf, _) ← encodeTerm f
      return (Sexp.mk "ite" [cf, tt, tf], si)
  | _ =>
  if si.smt == "Int" || si.smt == "Real" then
    if let some (op, args) := arithOp? e then
      return (← encodeArith op args si, si)
  encodeApp e

/-- Arithmetic operators, guarded to match Lean's total-function semantics. -/
partial def encodeArith (op : String) (args : Array Expr) (si : SortInfo) : EncM Sexp := do
  let enc (i : Nat) : EncM Sexp := return (← encodeTerm args[i]!).1
  match op with
  | "+" => return Sexp.mk "+" [← enc 0, ← enc 1]
  | "*" => return Sexp.mk "*" [← enc 0, ← enc 1]
  | "neg" => return Sexp.mk "-" [← enc 0]
  | "succ" => return Sexp.mk "+" [← enc 0, .atom "1"]
  | "-" =>
      let a ← enc 0; let b ← enc 1
      -- Subtraction on `Nat` is truncated.
      if si.isNat then
        return Sexp.mk "ite" [Sexp.mk "<=" [b, a], Sexp.mk "-" [a, b], .atom "0"]
      else
        return Sexp.mk "-" [a, b]
  | "/" =>
      let a ← enc 0; let b ← enc 1
      if si.smt == "Real" then
        -- In Lean, `x / 0 = 0`.
        return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0.0"], .atom "0.0", Sexp.mk "/" [a, b]]
      else
        return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0"], .atom "0", Sexp.mk "div" [a, b]]
  | "%" =>
      let a ← enc 0; let b ← enc 1
      if si.smt == "Real" then throwError "there is no % on Real"
      -- In Lean, `n % 0 = n`.
      return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0"], a, Sexp.mk "mod" [a, b]]
  | _ => throwError "unknown operator {op}"

/-- Fallback: treat `e` as an application of an uninterpreted symbol. -/
partial def encodeApp (e : Expr) : EncM (Sexp × SortInfo) := do
  let e := e.headBeta
  -- A variable bound by an SMT quantifier.
  if let .fvar fid := e then
    if let some (v, si) := (← read).bound[fid]? then
      return (.atom v, si)
  let si ← toSortInfo (← inferType e)
  let f := e.getAppFn
  let args := e.getAppArgs
  if let .fvar fid := f then
    if (← read).bound.contains fid && !args.isEmpty then
      throwError "higher-order application of a quantified variable is not encodable"
  let kinds ← args.mapM classifyArg
  -- Value arguments get translated; the rest fold into the symbol's identity, which
  -- amounts to monomorphizing on the spot.
  let keyE : Expr :=
    mkAppN f (args.zipWith (fun a k => if k.isSome then hole else a) kinds)
  let key : ExprStructEq := keyE
  let valueArgs := (args.zip kinds).filterMap fun (a, k) => k.map (a, ·)
  if ← mentionsBound keyE then
    throwError "the uninterpreted part of {e} depends on a quantified variable"
  if let some (nm, _) := (← get).syms[key]? then
    let encoded ← valueArgs.mapM fun (a, _) => return (← encodeTerm a).1
    return (Sexp.mk nm encoded.toList, si)
  if keyE.hasExprMVar then throwError "{e} contains metavariables"
  let nm ← freshSym (← baseNameOf e)
  let argSorts := valueArgs.map (·.2)
  modify fun s => { s with
    syms := s.syms.insert key (nm, si)
    decls := s.decls.push (.declareFun nm (argSorts.map (·.smt)).toList si.smt) }
  if si.isNat then
    let ax ← mkNatBound nm argSorts
    modify fun s => { s with sideAx := s.sideAx.push ax }
  let encoded ← valueArgs.mapM fun (a, _) => return (← encodeTerm a).1
  return (Sexp.mk nm encoded.toList, si)

end

end Hammer
