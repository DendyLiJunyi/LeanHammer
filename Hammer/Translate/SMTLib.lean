import Lean

/-!
# Representing and printing SMT-LIB 2

Terms and formulas ride on a minimal S-expression type, with a thin command layer on top.
That way the translator never wrestles with a bespoke SMT syntax tree, and supporting a
new theory just means emitting a few more atoms.
-/

namespace Hammer

/-- S-expressions. All of SMT-LIB's syntax is one of these. -/
inductive Sexp where
  | atom (s : String)
  | app  (xs : List Sexp)
  deriving Inhabited, BEq

namespace Sexp

/-- `(f a b …)`. -/
def mk (f : String) (args : List Sexp) : Sexp :=
  if args.isEmpty then .atom f else .app (.atom f :: args)

def true' : Sexp := .atom "true"
def false' : Sexp := .atom "false"

def not' : Sexp → Sexp
  | .atom "true" => false'
  | .atom "false" => true'
  | e => mk "not" [e]

/-- Fold into `(and …)`, collapsing the trivial cases. -/
def andN (xs : List Sexp) : Sexp :=
  let xs := xs.filter (· != true')
  match xs with
  | []  => true'
  | [x] => x
  | _   => mk "and" xs

def orN (xs : List Sexp) : Sexp :=
  let xs := xs.filter (· != false')
  match xs with
  | []  => false'
  | [x] => x
  | _   => mk "or" xs

def implies (a b : Sexp) : Sexp :=
  if a == true' then b else if b == true' then true' else mk "=>" [a, b]

partial def render : Sexp → String
  | .atom s => s
  | .app xs => "(" ++ String.intercalate " " (xs.map render) ++ ")"

instance : ToString Sexp := ⟨render⟩

end Sexp

/-- An SMT-LIB command. Only the handful we actually emit. -/
inductive Command where
  /-- `(declare-sort S 0)` -/
  | declareSort (name : String)
  /-- `(declare-fun f (A B) R)`. An empty `args` means a constant. -/
  | declareFun (name : String) (args : List String) (ret : String)
  /-- `(assert (! φ :named lbl))`. A `none` label emits a plain assert. -/
  | assert (label : Option String) (body : Sexp)
  /-- A line emitted verbatim, for `set-option`, `set-logic`, comments, and the like. -/
  | raw (line : String)

namespace Command

def render : Command → String
  | .declareSort n => s!"(declare-sort {n} 0)"
  | .declareFun n args ret =>
      s!"(declare-fun {n} ({String.intercalate " " args}) {ret})"
  | .assert none body => s!"(assert {body.render})"
  | .assert (some lbl) body => s!"(assert (! {body.render} :named {lbl}))"
  | .raw l => l

instance : ToString Command := ⟨render⟩

end Command

/-- A complete SMT-LIB problem: preamble, declarations, assertions. -/
structure Problem where
  /-- Whether to request an unsat core, which also gives every assert a `:named` label. -/
  produceCores : Bool := true
  commands     : Array Command := #[]

namespace Problem

/-- Render to text that z3 / cvc5 can consume directly. -/
def render (p : Problem) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "(set-logic ALL)"
  if p.produceCores then
    out := out.push "(set-option :produce-unsat-cores true)"
  for c in p.commands do
    out := out.push c.render
  out := out.push "(check-sat)"
  if p.produceCores then
    out := out.push "(get-unsat-core)"
  out := out.push "(exit)"
  return String.intercalate "\n" out.toList ++ "\n"

end Problem

end Hammer
