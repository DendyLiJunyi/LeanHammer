import Hammer.Basic
import Hammer.Util
import Hammer.Translate.SMTLib
import Hammer.Premise.Features

/-!
# Lean `Expr` → SMT-LIB 的编码

这是整条链路里唯一有"内容"的一步。CIC 比多排序一阶逻辑表达力强得多，所以翻译必然
是部分的。设计取舍如下：

* **看得懂的就精确翻译**：命题连接词、量词、等式、`Nat`/`Int`/`Real` 上的算术与比较。
* **看不懂的就抽象成不解释符号**。抽象是保 `unsat` 的：它只会丢掉等式信息，让问题
  更难而不是更容易，所以求解器说 `unsat` 时结论依然可信。
* **翻译失败的前提直接丢掉**，只有目标翻译失败才算整体失败。

## `Nat` 的处理

`Nat` 映射到 SMT 的 `Int`，并为每个 `Nat` 量词加 `≥ 0` 守卫、为每个返回 `Nat` 的
符号加非负公理。截断减法 `a - b` 翻成 `(ite (<= b a) (- a b) 0)`；除法/取模按 Lean 的
"除以 0 得 0 / 得被除数"补 `ite` 守卫。Lean 的 `Int` 除法恰好就是 SMT-LIB 的欧几里得
`div`/`mod`（已实测：`(-7)/2 = -4`，`(-7)%2 = 1`），所以只需补零除守卫。

## 已知的不完备与风险

SMT 假设每个排序非空，而 Lean 的类型可以是空的。对空类型上的 `∃` 这会引入不健全。
本项目的收尾本来就是信任公理，这个洞记在这里，逆向翻译会一并堵上。
-/

namespace Hammer

open Lean Meta

/-- 一个 SMT 排序，外加"它其实来自 Lean 的 `Nat`"这一位信息。 -/
structure SortInfo where
  smt   : String
  isNat : Bool := false
  deriving Inhabited, BEq

def SortInfo.bool : SortInfo := ⟨"Bool", false⟩
def SortInfo.int  : SortInfo := ⟨"Int", false⟩
def SortInfo.nat  : SortInfo := ⟨"Int", true⟩
def SortInfo.real : SortInfo := ⟨"Real", false⟩

/-- 编码器的只读环境：SMT 量词绑定的变量，以及配置。 -/
structure EncCtx where
  bound : Std.HashMap FVarId (String × SortInfo) := ∅
  cfg   : Hammer.Config := {}

/-- 编码器的可变状态。`decls` 按首次使用顺序累积，因此天然满足"先声明后使用"。 -/
structure EncState where
  sorts   : Std.HashMap ExprStructEq SortInfo := ∅
  syms    : Std.HashMap ExprStructEq (String × SortInfo) := ∅
  decls   : Array Command := #[]
  /-- 由声明附带产生的公理，例如 `Nat` 符号的非负性。 -/
  sideAx  : Array Sexp := #[]
  used    : Std.HashSet String := ∅
  counter : Nat := 0

abbrev EncM := ReaderT EncCtx (StateRefT EncState MetaM)

/-- 抽象键里占位"已翻译的值参数"的哑常量。只用于哈希，不会被繁饰。 -/
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
`e` 是否提到了当前处于 SMT 量词作用域内的变量。

这是两类不健全的共同来源：把 `Fin n` 抽象成一个与 `n` 无关的排序，或者把
`@Foo n a` 抽象成一个与 `n` 无关的符号——依赖一旦丢掉，一条真命题就会变成矛盾。
（`Fin.pos : ∀ {n} (i : Fin n), 0 < n` 正是这样把整个问题变成 unsat 的。）
-/
private def mentionsBound (e : Expr) : EncM Bool := do
  let bound := (← read).bound
  if bound.isEmpty then return false
  return e.hasAnyFVar fun fid => bound.contains fid

private def intLit (i : Int) : Sexp :=
  if i < 0 then Sexp.mk "-" [.atom (toString (-i))] else .atom (toString i)

/-- 从一个表达式猜一个可读的 SMT 符号基名。 -/
private def baseNameOf (e : Expr) : MetaM String := do
  match e.getAppFn with
  | .const n _ => return sanitize n
  | .fvar fid  => return sanitize (← fid.getUserName)
  | _          => return "t"

/-- 类型 → SMT 排序。不可编码时抛错（调用方决定是丢前提还是整体失败）。 -/
partial def toSortInfo (t : Expr) : EncM SortInfo := do
  let t ← instantiateMVars t
  let t ← whnfR t
  match t with
  | .sort u => if u.isZero then return .bool else throwError "sort {t} 不可编码"
  | .forallE .. => throwError "函数类型 {t} 是高阶的，不可编码"
  | _ =>
    if ← isProp t then throwError "{t} 是命题，它的元素是证明"
    if (← isClass? t).isSome then throwError "{t} 是类型类"
    match t.getAppFnArgs with
    | (``Nat, _)  => return .nat
    | (``Int, _)  => return .int
    | (``Bool, _) => return .bool
    -- `Real` / `Rat` 来自 Mathlib，这里按名字认，不引依赖。
    | (n, _) =>
      if n == `Real || n == `Rat || n == `NNRat then return .real
      if ← mentionsBound t then
        throwError "类型 {t} 依赖于被量化的变量，抽象成排序会丢掉依赖"
      let key : ExprStructEq := t
      if let some si := (← get).sorts[key]? then return si
      if t.hasExprMVar then throwError "类型 {t} 含元变量"
      unless (← read).cfg.assumeNonempty do
        let .sort u ← whnfR (← inferType t)
          | throwError "{t} 不是一个类型"
        unless (← trySynthInstance (mkApp (mkConst ``Nonempty [u]) t)) matches .some _ do
          throwError "无法确认 {t} 非空；SMT 排序必须非空"
      let nm ← freshSym (← baseNameOf t)
      let si : SortInfo := ⟨nm, false⟩
      modify fun s => { s with
        sorts := s.sorts.insert key si
        decls := s.decls.push (.declareSort nm) }
      return si

/-- 一个参数能否作为"值"翻译；否则它属于符号的身份（类型参数、实例、证明）。 -/
private def classifyArg (a : Expr) : EncM (Option SortInfo) := do
  try
    let t ← inferType a
    return some (← toSortInfo t)
  catch _ => return none

/-- 内建算术：返回 (SMT 算子标记, 参数)。标记是内部记号，不直接是 SMT 名字。 -/
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

/-- 内建比较：返回 SMT 关系名与两个参数。 -/
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

/-- 把 `p : α → Prop` 化成 `(binder 名, 定义域, 体)`，必要时做 η 展开。 -/
private def asPredicate (p : Expr) : MetaM (Name × Expr) := do
  match p with
  | .lam n _ b _ => return (n, b)
  | _ => return (`x, mkApp p (.bvar 0) |>.liftLooseBVars 0 0)

/-- 返回 `Nat` 的符号的非负公理，参数里的 `Nat` 也加上守卫。 -/
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

/-- 把一个命题翻成 SMT 公式。 -/
partial def encodeForm (e : Expr) : EncM Sexp := do
  let e ← instantiateMVars e
  match e with
  | .forallE n d b _ =>
      if ← isProp d then
        if b.hasLooseBVars then
          throwError "依赖于证明的 ∀ 不可编码"
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
        else throwError "ite 的分支不是命题"
    | _ =>
      if let some (op, a, b) := cmpOp? e then
        let (ta, sa) ← encodeTerm a
        let (tb, _)  ← encodeTerm b
        if sa.smt == "Int" || sa.smt == "Real" then
          return Sexp.mk op [ta, tb]
        else throwError "比较的排序 {sa.smt} 不是数值"
      let (s, si) ← encodeApp e
      if si.smt != "Bool" then throwError "{e} 不是命题"
      return s

/-- `a = b` / `a ≠ b`：命题上的等号退化成 `↔`。 -/
partial def encodeEq (α a b : Expr) (negated : Bool) : EncM Sexp := do
  let eq ←
    if (← whnfR α) matches .sort .zero then
      pure (Sexp.mk "=" [← encodeForm a, ← encodeForm b])
    else
      let (ta, _) ← encodeTerm a
      let (tb, _) ← encodeTerm b
      pure (Sexp.mk "=" [ta, tb])
  return if negated then Sexp.not' eq else eq

/-- 把一个项翻成 SMT 项，同时给出它的排序。 -/
partial def encodeTerm (e : Expr) : EncM (Sexp × SortInfo) := do
  let e ← instantiateMVars e
  -- 命题当作 `Bool` 项。
  if ← isProp (← inferType e) then
    return (← encodeForm e, .bool)
  match e with
  | .mdata _ b => encodeTerm b
  | .letE .. => encodeTerm (← whnf e)
  | _ =>
  let si ← toSortInfo (← inferType e)
  -- 数值字面量
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

/-- 算术算子，按 Lean 的全函数语义补守卫。 -/
partial def encodeArith (op : String) (args : Array Expr) (si : SortInfo) : EncM Sexp := do
  let enc (i : Nat) : EncM Sexp := return (← encodeTerm args[i]!).1
  match op with
  | "+" => return Sexp.mk "+" [← enc 0, ← enc 1]
  | "*" => return Sexp.mk "*" [← enc 0, ← enc 1]
  | "neg" => return Sexp.mk "-" [← enc 0]
  | "succ" => return Sexp.mk "+" [← enc 0, .atom "1"]
  | "-" =>
      let a ← enc 0; let b ← enc 1
      -- `Nat` 的减法是截断的。
      if si.isNat then
        return Sexp.mk "ite" [Sexp.mk "<=" [b, a], Sexp.mk "-" [a, b], .atom "0"]
      else
        return Sexp.mk "-" [a, b]
  | "/" =>
      let a ← enc 0; let b ← enc 1
      if si.smt == "Real" then
        -- Lean 里 `x / 0 = 0`。
        return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0.0"], .atom "0.0", Sexp.mk "/" [a, b]]
      else
        return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0"], .atom "0", Sexp.mk "div" [a, b]]
  | "%" =>
      let a ← enc 0; let b ← enc 1
      if si.smt == "Real" then throwError "Real 上没有 %"
      -- Lean 里 `n % 0 = n`。
      return Sexp.mk "ite" [Sexp.mk "=" [b, .atom "0"], a, Sexp.mk "mod" [a, b]]
  | _ => throwError "未知算子 {op}"

/-- 兜底：把 `e` 当成一个不解释符号的应用。 -/
partial def encodeApp (e : Expr) : EncM (Sexp × SortInfo) := do
  let e := e.headBeta
  -- SMT 量词绑定的变量。
  if let .fvar fid := e then
    if let some (v, si) := (← read).bound[fid]? then
      return (.atom v, si)
  let si ← toSortInfo (← inferType e)
  let f := e.getAppFn
  let args := e.getAppArgs
  if let .fvar fid := f then
    if (← read).bound.contains fid && !args.isEmpty then
      throwError "对量词变量的高阶应用不可编码"
  let kinds ← args.mapM classifyArg
  -- 值参数被翻译；其余参数并入符号的身份，等价于就地单态化。
  let keyE : Expr :=
    mkAppN f (args.zipWith (fun a k => if k.isSome then hole else a) kinds)
  let key : ExprStructEq := keyE
  let valueArgs := (args.zip kinds).filterMap fun (a, k) => k.map (a, ·)
  if ← mentionsBound keyE then
    throwError "{e} 的不解释部分依赖于被量化的变量"
  if let some (nm, _) := (← get).syms[key]? then
    let encoded ← valueArgs.mapM fun (a, _) => return (← encodeTerm a).1
    return (Sexp.mk nm encoded.toList, si)
  if keyE.hasExprMVar then throwError "{e} 含元变量"
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
