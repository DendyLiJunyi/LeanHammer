import Lean

/-!
# 小工具

`Expr` 遍历、名字清洗、以及一些在多个阶段都要用的判定。
-/

namespace Hammer

open Lean Meta

/-- 逻辑连接词与量词的常量名；做特征提取时要忽略它们，否则每条引理看起来都相关。 -/
def logicalSymbols : Std.HashSet Name :=
  Std.HashSet.ofList
    [``Eq, ``Ne, ``Iff, ``And, ``Or, ``Not, ``Exists, ``True, ``False,
     ``HEq, ``ite, ``dite, ``Decidable, ``DecidableEq,
     ``OfNat.ofNat, ``instOfNatNat, ``Membership.mem]

/-- 前提收集时整体跳过的命名空间。 -/
def blacklistedNamespaces : Array Name :=
  #[`Lean, `Std.Internal, `Qq, `Aesop, `Mathlib.Tactic, `Mathlib.Meta,
    `Tactic, `Simp, `Elab, `Parser, `IO, `EIO, `ST, `Hammer]

/-- 一个名字是否属于被拉黑的命名空间。 -/
def isBlacklisted (n : Name) : Bool :=
  blacklistedNamespaces.any fun ns => ns.isPrefixOf n

/-- 编译器/繁饰器生成的辅助定义，对用户不可见，不该作为前提。 -/
def isNoise (n : Name) : Bool := Id.run do
  if n.isInternal || n.hasMacroScopes then return true
  let s := n.toString
  for bad in ["_proof_", "_eq_", "_unfold", "match_", "eq_def", "proof_",
              "._", "sizeOf_spec", "noConfusion", "casesOn", "recOn", "brecOn",
              "below", "ibelow", "binductionOn", "ndrec", "rec_", "injEq",
              "toCtorIdx", "ofNat_toCtorIdx"] do
    if (s.splitOn bad).length > 1 then return true
  return false

/-- 收集 `e` 中出现的所有常量名。 -/
def constantsIn (e : Expr) : Std.HashSet Name :=
  (e.foldConsts ∅ fun n acc => acc.insert n)

/-- 一个表达式是否为 `Prop`（作为类型看）。 -/
def isPropType (e : Expr) : MetaM Bool := do
  return (← whnf (← inferType e)).isProp

/-- 把 Lean 名字变成合法的 SMT-LIB 符号。 -/
def sanitize (n : Name) : String :=
  let s := n.toString
  let s := s.foldl (init := "") fun acc c =>
    if c.isAlphanum || c == '_' then acc.push c
    else if c == '.' then acc.push '_'
    else acc ++ "u" ++ toString c.toNat
  if s.isEmpty then "sym"
  else if s.front.isDigit then "s" ++ s
  else s

end Hammer
