import Lean

/-!
# SMT-LIB 2 的表示与打印

用一个极小的 S-表达式类型承载项与公式，再加一层命令层。这样翻译阶段不必和
"某个具体的 SMT 语法树"较劲，加新理论只是多产生几个 atom。
-/

namespace Hammer

/-- S-表达式：SMT-LIB 的全部语法都是它。 -/
inductive Sexp where
  | atom (s : String)
  | app  (xs : List Sexp)
  deriving Inhabited, BEq

namespace Sexp

/-- `(f a b …)`。 -/
def mk (f : String) (args : List Sexp) : Sexp :=
  if args.isEmpty then .atom f else .app (.atom f :: args)

def true' : Sexp := .atom "true"
def false' : Sexp := .atom "false"

def not' : Sexp → Sexp
  | .atom "true" => false'
  | .atom "false" => true'
  | e => mk "not" [e]

/-- 折叠成 `(and …)`，并消去平凡情形。 -/
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

/-- 一条 SMT-LIB 命令。只保留我们真正会产生的那几种。 -/
inductive Command where
  /-- `(declare-sort S 0)` -/
  | declareSort (name : String)
  /-- `(declare-fun f (A B) R)`；`args` 为空即常量。 -/
  | declareFun (name : String) (args : List String) (ret : String)
  /-- `(assert (! φ :named lbl))`；`label` 为 `none` 时不加标注。 -/
  | assert (label : Option String) (body : Sexp)
  /-- 原样输出的一行，用于 `set-option` / `set-logic` 等。 -/
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

/-- 一个完整的 SMT-LIB 问题：序言 + 声明 + 断言。 -/
structure Problem where
  /-- 是否请求 unsat core（会给每条断言加 `:named` 标签）。 -/
  produceCores : Bool := true
  commands     : Array Command := #[]

namespace Problem

/-- 渲染成可直接喂给 z3 / cvc5 的文本。 -/
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
