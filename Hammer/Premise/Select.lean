import Hammer.Premise.Collect
import Hammer.Basic

/-!
# 相关度过滤（MePo 风格）

从目标的符号集出发迭代扩张：每轮接受与当前"相关符号集"重合度足够高的引理，
把它们的符号并进来，然后降低阈值再来一轮。稀有符号权重更高——
和目标共享 `Nat.succ_le_succ` 里那种冷门符号，比共享 `Eq` 有意义得多。
-/

namespace Hammer

open Lean Meta

/-- 符号出现频率表。 -/
abbrev FreqTable := Std.HashMap Name Nat

def buildFreqTable (facts : Array Fact) : FreqTable := Id.run do
  let mut t : FreqTable := ∅
  for f in facts do
    for s in f.symbols do
      t := t.insert s ((t.getD s 0) + 1)
  return t

/-- 稀有符号权重高。`freq` 越大权重越接近 1，越小则可到 3 左右。 -/
def symWeight (t : FreqTable) (s : Name) : Float :=
  let f := (t.getD s 1).toFloat
  1.0 + 2.0 / Float.log (2.0 + f)

/-- 一条引理相对当前相关符号集的得分，取值 `[0,1]`。 -/
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
迭代相关度过滤。`goalSyms` 是目标（含局部假设）的符号集，返回按得分从高到低排序的
前 `maxPremises` 条全局引理。
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
    -- 同一轮里，短的引理优先。
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
