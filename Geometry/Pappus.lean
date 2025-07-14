import Geometry.AlgebraicEuclid
set_option maxHeartbeats 10000000

theorem Pappus (A B C A' B' C' P Q R : EuclidPoint) (h₁ : Col A B C) {t₁ t₂ : ℝ}
  (h₂ : Col A' B' C')
  (h₃ : P ∈ Line.mk (A -ₛ B'))
  (h₄ : P ∈ Line.mk (A' -ₛ B))
  (h₅ : Q ∈ Line.mk (A -ₛ C'))
  (h₆ : Q ∈ Line.mk (A' -ₛ C))
  (h₇ : R ∈ Line.mk (B -ₛ C'))
  (h₈ : R ∈ Line.mk (B' -ₛ C))
  : Col P Q R := by
  have g₁ : t₁ * ((C'.x - A.x) * (B.y - A.y) - (C'.y - A.y) * (B.x - A.x)) = 1 := by sorry
  have g₂ : t₂ * ((B'.x - A.x) * (B.y - A.y) - (B'.y - A.y) * (B.x - A.x)) = 1 := by sorry
  simp_all only [euclid_simp]

  set_option maxRecDepth 1000000 in
  grind (ringSteps := 1000000)
