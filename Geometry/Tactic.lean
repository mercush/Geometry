import Geometry.AlgebraicEuclid
open Lean Meta Elab Tactic Term


macro "algebraic_euclid" : tactic =>
  `(tactic|
    -- Try to extract from any hypothesis that matches the pattern
    (repeat (any_goals first
    | simp_all only [euclid_simp]
    | (obtain ⟨t, ht⟩) -- Maybe should be {}
    | rw [Segment.length_sq_iff]
    | rw [EuclidPoint.pointEq]
    | constructor))
    <;>
    set_option trace.grind.ring.internalize true in
    set_option trace.grind.debug.ring.basis true in
    set_option trace.grind.ematch.instance true in
    grind (splits := 0) -splitMatch -splitIte -splitIndPred -splitImp -linarith -cutsat)

macro "nondegen" : tactic =>
  `(tactic|grind (splits := 0) -splitMatch -splitIte -splitIndPred -splitImp -linarith -cutsat)
