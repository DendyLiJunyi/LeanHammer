import Hammer.Premise.Collect
import Hammer.Basic

/-!
# Relevance filtering (MePo style)

Start from the goal's symbol set and expand iteratively: each round accepts the lemmas
whose overlap with the current relevant-symbol set is high enough, folds their symbols
into that set, then lowers the threshold and goes again. Rare symbols carry more weight --
sharing something obscure like `Nat.succ_le_succ` with the goal says far more than
sharing `Eq`.
-/

namespace Hammer

open Lean Meta

/-- Symbol frequency table. -/
abbrev FreqTable := Std.HashMap Name Nat

def buildFreqTable (facts : Array Fact) : FreqTable := Id.run do
  let mut t : FreqTable := ∅
  for f in facts do
    for s in f.symbols do
      t := t.insert s ((t.getD s 0) + 1)
  return t

/-- Rare symbols weigh more. Weight tends to 1 as `freq` grows, and reaches roughly 3
for the rarest symbols. -/
def symWeight (t : FreqTable) (s : Name) : Float :=
  let f := (t.getD s 1).toFloat
  1.0 + 2.0 / Float.log (2.0 + f)

/-- A lemma's score against the current relevant-symbol set, in `[0,1]`. -/
def factScore (t : FreqTable) (relevant : Std.HashSet Name) (f : Fact) : Float := Id.run do
  if f.symbols.isEmpty then return 0.0
  let mut hit := 0.0
  let mut total := 0.0
  for s in f.symbols do
    let w := symWeight t s
    total := total + w
    if relevant.contains s then hit := hit + w
  if total == 0.0 then return 0.0
  return hit / total

/--
Iterative relevance filtering. `goalSyms` is the symbol set of the goal together with its
local hypotheses; the result is the top `maxPremises` global lemmas, best score first.
-/
def selectPremises (cfg : Hammer.Config) (goalSyms : Std.HashSet Name)
    (pool : Array Fact) : Array Fact := Id.run do
  let freq := buildFreqTable pool
  let mut relevant := goalSyms
  let mut chosen : Array (Fact × Float) := #[]
  let mut taken : Std.HashSet Name := ∅
  let mut threshold : Float := 0.62
  let mut round := 0
  while chosen.size < cfg.maxPremises && round < 12 do
    let mut newlyChosen : Array (Fact × Float) := #[]
    for f in pool do
      if taken.contains f.name then continue
      let s := factScore freq relevant f
      if s ≥ threshold then
        newlyChosen := newlyChosen.push (f, s)
    if newlyChosen.isEmpty then
      threshold := threshold * 0.85
      round := round + 1
      if threshold < 0.05 then break
      continue
    -- Within a round, prefer shorter lemmas.
    let sorted := newlyChosen.qsort fun (f1, s1) (f2, s2) =>
      if s1 == s2 then sizeOf' f1.type < sizeOf' f2.type else s1 > s2
    for (f, s) in sorted do
      if chosen.size ≥ cfg.maxPremises then break
      chosen := chosen.push (f, s)
      taken := taken.insert f.name
      relevant := f.symbols.fold (init := relevant) fun acc n => acc.insert n
    threshold := threshold * 0.9
    round := round + 1
  return chosen.map (·.1)

end Hammer
