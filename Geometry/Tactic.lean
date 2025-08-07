import Geometry.AlgebraicEuclid
open Lean Meta Elab Tactic Term


macro "algebraic_euclid" : tactic =>
  `(tactic|
    (repeat (any_goals first
        | simp_all only [euclid_simp]
        | rw [Segment.length_sq_iff]
        | rw [EuclidPoint.pointEq]
        | constructor))
      <;>
      (set_option trace.grind.ring.internalize true in
       set_option trace.grind.debug.ring.basis true in
       set_option trace.grind.ematch.instance true in
       grind (splits := 0) -splitMatch -splitIte -splitIndPred -splitImp -linarith -cutsat (ringSteps := 10000000000000)) )


macro "nondegen" : tactic =>
  `(tactic|grind (splits := 0) -splitMatch -splitIte -splitIndPred -splitImp -linarith -cutsat)


-- elab "algebraic_euclid" : tactic => do
--   evalTactic (← `(tactic| wlog h : A = EuclidPoint.mk 0 0 ∧ B = EuclidPoint.mk 1 0))

--   let goals ← getGoals
--   match goals with
--   | [symGoal, mainGoal] =>
--       setGoals [symGoal]
--       evalTactic (← `(tactic| sorry))

--       setGoals [mainGoal]
--       evalTactic (← `(tactic|
--         (repeat (any_goals first
--           | simp_all only [euclid_simp]
--           | rw [Segment.length_sq_iff]
--           | rw [EuclidPoint.pointEq]
--           | constructor))
--         <;>
--         (set_option trace.grind.ring.internalize true in
--          set_option trace.grind.debug.ring.basis true in
--          set_option trace.grind.ematch.instance true in
--          grind (splits := 0) -splitMatch -splitIte -splitIndPred -splitImp -linarith -cutsat (ringSteps := 1000000))))

--       -- Clear remaining goals (if any)
--       let remainingGoals ← getGoals
--       setGoals remainingGoals
--   | _ =>
--       throwError "Expected exactly 2 goals from wlog, got {goals.length}"
