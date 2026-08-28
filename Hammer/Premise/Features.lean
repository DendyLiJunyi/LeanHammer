import Hammer.Util

/-!
# Premise features

A lemma's "features" are simply the constant names occurring in its statement. Premise
selection rests entirely on these: a lemma sharing rare symbols with the goal is far more
likely to be useful.
-/

namespace Hammer

open Lean

/-- One candidate premise. -/
structure Fact where
  /-- Display name: the global constant name, or the user name of a local hypothesis. -/
  name    : Name
  /-- The proposition itself. -/
  type    : Expr
  /-- Proof term: an `fvar` for local hypotheses, `mkConst` (possibly with universe
  parameters) for global lemmas. -/
  proof   : Expr
  /-- Constants occurring in `type`, with logical connectives filtered out. -/
  symbols : Std.HashSet Name
  /-- Local hypotheses always enter the final problem and skip relevance scoring. -/
  isLocal : Bool := false
  /-- The statement still has uninstantiated type or universe variables. -/
  isPoly  : Bool := false

/-- Extract feature symbols: drop the logical skeleton, keep the content. -/
def featuresOf (e : Expr) : Std.HashSet Name :=
  (constantsIn e).fold (init := ∅) fun acc n =>
    if logicalSymbols.contains n || isNoise n then acc else acc.insert n

/-- Rough size of a statement, used to penalize very long lemmas. -/
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
