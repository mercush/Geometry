import Geometry.AlgebraicEuclid
open Lean Meta Elab Tactic


macro "algebraic_euclid" : tactic =>
  `(tactic|
    -- Try to extract from any hypothesis that matches the pattern
    (repeat first
    | simp_all only [euclid_simp]
    | rw [Segment.length_sq_iff]
    | constructor)
    <;> grind (splits := 0) -cutsat -linarith -mbtc (ringSteps := 10000000))
