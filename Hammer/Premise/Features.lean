import Hammer.Util

/-!
# 前提的特征

一条引理的"特征"就是它陈述里出现的常量名集合。前提选择完全建立在这上面：
和目标共享稀有符号的引理更可能有用。
-/

namespace Hammer

open Lean

/-- 一条候选前提。 -/
structure Fact where
  /-- 展示用的名字（全局常量名，或局部假设的用户名）。 -/
  name    : Name
  /-- 命题本身。 -/
  type    : Expr
  /-- 证明项：局部假设是 `fvar`，全局引理是 `mkConst`（可能带宇宙参数）。 -/
  proof   : Expr
  /-- 出现在 `type` 里的常量，已滤掉逻辑连接词。 -/
  symbols : Std.HashSet Name
  /-- 局部假设永远进入最终问题，不参与相关度打分。 -/
  isLocal : Bool := false
  /-- 陈述里还有未被实例化的类型/宇宙变量。 -/
  isPoly  : Bool := false

/-- 提取特征符号：去掉逻辑骨架，只留"内容"符号。 -/
def featuresOf (e : Expr) : Std.HashSet Name :=
  (constantsIn e).fold (init := ∅) fun acc n =>
    if logicalSymbols.contains n || isNoise n then acc else acc.insert n

/-- 一条引理的"体积"，用来惩罚超长的陈述。 -/
partial def sizeOf' (e : Expr) : Nat :=
  match e with
  | .app f a       => 1 + sizeOf' f + sizeOf' a
  | .lam _ t b _   => 1 + sizeOf' t + sizeOf' b
  | .forallE _ t b _ => 1 + sizeOf' t + sizeOf' b
  | .letE _ t v b _ => 1 + sizeOf' t + sizeOf' v + sizeOf' b
  | .mdata _ b     => sizeOf' b
  | .proj _ _ b    => 1 + sizeOf' b
  | _              => 1

end Hammer
