import Geometry.AlgebraicEuclid
import Geometry.Basic

theorem Proposition15 (x₁ x₂ x₃ x₄ x₅ : EuclidPoint) (t₁ t₂ t₃ t₄ : ℝ)
  (h₁ : Between x₁ x₅ x₂)
  (h₂ : Between x₃ x₅ x₄)
  (h₄ : Uneq x₅ x₁ t₁)
  (h₅ : Uneq x₅ x₂ t₂)
  (h₆ : Uneq x₅ x₃ t₃)
  (h₇ : Uneq x₅ x₄ t₄) :
  (Angle.mk h₄ h₆) = (Angle.mk h₅ h₇) := by sorry
