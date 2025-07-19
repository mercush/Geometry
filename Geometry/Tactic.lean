import Geometry.AlgebraicEuclid
open Lean Meta Elab Tactic


macro "algebraic_euclid" : tactic =>
  `(tactic|
    -- Try to extract from any hypothesis that matches the pattern
    (repeat (any_goals first
    | simp_all only [euclid_simp]
    | (obtain ⟨t, ht⟩) -- Maybe should be {}
    | rw [Segment.length_sq_iff]
    | constructor))
    <;>
    grind (splits := 0) -cutsat -linarith -mbtc)

macro "degen" : tactic =>
  `(tactic|grind (splits := 0) -cutsat -linarith -mbtc)
