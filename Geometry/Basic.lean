import Geometry.AlgebraicEuclid
import Geometry.Tactic

theorem Proposition4 (x₁ x₂ x₃ y₁ y₂ y₃: EuclidPoint) (t₁ t₂ : ℝ)
  (h₁ : |x₁ -ₛ x₂| = |y₁ -ₛ y₂|)
  (h₂ : |x₁ -ₛ x₃| = |y₁ -ₛ y₃|)
  (h_zero₁ : Uneq x₁ x₂ t₁)
  (h_zero₂ : Uneq x₁ x₃ t₂)
  (h₃ : Angle.mk h_zero₁ h_zero₂ = Angle.mk
  (by simp_all [euclid_simp] : Uneq y₁ y₂ t₁)
  (by simp_all [euclid_simp] : Uneq y₁ y₃ t₂))
  :
  |x₂ -ₛ x₃| = |y₂ -ₛ y₃| := by
  algebraic_euclid

theorem Proposition5 (x₁ x₂ x₃: EuclidPoint) (t₁ t₂ t₃ : ℝ)
  (h₁ : |x₁ -ₛ x₂| = |x₁ -ₛ x₃|)
  (h₂ : Uneq x₂ x₁ t₁)
  (h₃ : Uneq x₂ x₃ t₂)
  (h₄ : Uneq x₃ x₁ t₃):
  Angle.mk h₂ h₃ = Angle.mk h₃~ h₄
  := by
  algebraic_euclid

theorem Proposition6 (x₁ x₂ x₃ : EuclidPoint) (t₁ t₂ t₃ s₁ : ℝ)
  (h₁ : Uneq x₂ x₁ t₁)
  (h₂ : Uneq x₂ x₃ t₂)
  (h₃ : Uneq x₃ x₁ t₃)
  (h₄ : Angle.mk h₁ h₂ = Angle.mk h₂~ h₃)
  (h₅ : Noncol x₁ x₂ x₃ s₁)
  : |x₁ -ₛ x₂| = |x₁ -ₛ x₃| := by
  algebraic_euclid

theorem Proposition8 (x₁ x₂ x₃ y₁ y₂ y₃ : EuclidPoint) (t₁ t₂ : ℝ)
  (h₁ : |x₁ -ₛ x₂| = |y₁ -ₛ y₂|)
  (h₂ : |x₂ -ₛ x₃| = |y₂ -ₛ y₃|)
  (h₃ : |x₁ -ₛ x₃| = |y₁ -ₛ y₃|)
  (h₄ : Uneq x₁ x₂ t₁)
  (h₅ : Uneq x₃ x₁ t₂) :
  WeakAngleEq (Angle.mk h₄ h₅~)
  (Angle.mk (by simp_all [euclid_simp] : Uneq y₁ y₂ t₁)
  (by simp_all [euclid_simp, ←h₃, Segment.length_symm] : Uneq y₁ y₃ t₂))
  := by
  algebraic_euclid

theorem Proposition13 (x₁ x₂ x₃ x₄ : EuclidPoint) (t₁ t₂ t₃ : ℝ)
  (h₁ : Uneq x₄ x₁ t₁)
  (h₂ : Uneq x₄ x₂ t₂)
  (h₃ : Uneq x₄ x₃ t₃)
  (h₄ : Between x₁ x₄ x₂)
  : ((Angle.mk h₁ h₃) + (Angle.mk h₃ h₂)) = (∟ + ∟)
  := by
  algebraic_euclid

  theorem Proposition30 (x₁ x₂ x₃ x₄ x₅ x₆ : EuclidPoint) (t : ℝ)
  (h₁ : (x₁ -ₛ x₂) || (x₃ -ₛ x₄))
  (h₂ : (x₃ -ₛ x₄) || (x₅ -ₛ x₆))
  (h₃ : Uneq x₃ x₄ t)
  : (x₁ -ₛ x₂) || (x₅ -ₛ x₆) := by
  algebraic_euclid

theorem Proposition32 (x₁ x₂ x₃ : EuclidPoint) (t₁ t₂ t₃ : ℝ)
  (h₁ : Uneq x₁ x₂ t₁)
  (h₂ : Uneq x₁ x₃ t₂)
  (h₃ : Uneq x₂ x₃ t₃)
  :
  (Angle.mk h₁ h₂ +
  Angle.mk h₃ h₁~ +
  Angle.mk h₂~ h₃~) = (∟ + ∟) := by
  algebraic_euclid

theorem Proposition33 (x₁ x₂ x₃ x₄ : EuclidPoint) (t₁ : ℝ)
  (h₁ : (x₁ -ₛ x₂) || (x₃ -ₛ x₄))
  (h₂ : (x₁ -ₛ x₃) || (x₂ -ₛ x₄))
  (h₃ : Noncol x₁ x₂ x₃ t₁)
  : |x₁ -ₛ x₃| = |x₂ -ₛ x₄| := by
  algebraic_euclid

theorem Proposition37 (x₁ x₂ x₃ x₄ : EuclidPoint)
  (h₁ : (x₃ -ₛ x₄) || (x₁ -ₛ x₂)) :
  Area x₁ x₂ x₃ = Area x₁ x₂ x₄ := by
  algebraic_euclid

theorem Proposition47 (z₁ z₂ z₃ : EuclidPoint)
  (h₁ : (z₂ -ₛ z₁) ⊥ (z₃ -ₛ z₁)) :
  |z₃ -ₛ z₂|^2 = |z₂ -ₛ z₁|^2 + |z₃ -ₛ z₁|^2 := by
  algebraic_euclid

theorem Proposition48 (z₁ z₂ z₃ : EuclidPoint)
  (h₁ : |z₃ -ₛ z₂|^2 = |z₂ -ₛ z₁|^2 + |z₃ -ₛ z₁|^2) :
  (z₂ -ₛ z₁) ⊥ (z₃ -ₛ z₁) := by
  algebraic_euclid

-- BONUS
lemma BetweenCol (x y z : EuclidPoint)
  (h₁ : Between x y z) :
  Col x y z := by
  algebraic_euclid
