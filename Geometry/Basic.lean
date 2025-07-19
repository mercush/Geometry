import Geometry.AlgebraicEuclid
import Geometry.Tactic

theorem Proposition4 (x₁ x₂ x₃ y₁ y₂ y₃: EuclidPoint)
  (h₁ : |x₁ - x₂| = |y₁ - y₂|)
  (h₂ : |x₁ - x₃| = |y₁ - y₃|)
  (h_zero₁ : |x₁ - x₂| ≠ 0)
  (h_zero₂ : |x₁ - x₃| ≠ 0)
  (h₃ : ∠ h_zero₁ h_zero₂ =
  ∠ (by degen : |y₁ - y₂| ≠ 0) (by degen : |y₁ - y₃| ≠ 0))
  :
  |x₂ - x₃| = |y₂ - y₃| := by

  algebraic_euclid

theorem Proposition5 (x₁ x₂ x₃: EuclidPoint)
  (h₁ : |x₁ - x₂| = |x₁ - x₃|)
  (h₂ : |x₂ - x₁| ≠ 0)
  (h₃ : |x₂ - x₃| ≠ 0)
  (h₄ : |x₃ - x₁| ≠ 0):
  ∠ h₂ h₃ = ∠ (by degen : |x₃ - x₂| ≠ 0) h₄
  := by
  algebraic_euclid

theorem Proposition6 (x₁ x₂ x₃ : EuclidPoint)
  (h₁ : |x₂ - x₁| ≠ 0)
  (h₂ : |x₂ - x₃| ≠ 0)
  (h₃ : |x₃ - x₁| ≠ 0)
  (h₄ : ∠ h₁ h₂ = ∠ (by degen : |x₃ - x₂| ≠ 0) h₃)
  (h₅ : Noncol x₁ x₂ x₃)
  : |x₁ - x₂| = |x₁ - x₃| := by
  algebraic_euclid

theorem Proposition8 (x₁ x₂ x₃ y₁ y₂ y₃ : EuclidPoint)
  (h₁ : |x₁ - x₂| = |y₁ - y₂|)
  (h₂ : |x₂ - x₃| = |y₂ - y₃|)
  (h₃ : |x₁ - x₃| = |y₁ - y₃|)
  (h₄ : |x₁ - x₂| ≠ 0)
  (h₅ : |x₃ - x₁| ≠ 0) :
  WeakAngleEq (∠ h₄ (by degen : |x₁ - x₃| ≠ 0))
  (∠ (by degen : |y₁ - y₂| ≠ 0)
  (by degen : |y₁ - y₃| ≠ 0))
  := by
  algebraic_euclid

theorem Proposition13 (x₁ x₂ x₃ x₄ : EuclidPoint)
  (h₁ : |x₄ - x₁| ≠ 0)
  (h₂ : |x₄ - x₂| ≠ 0)
  (h₃ : |x₄ - x₃| ≠ 0)
  (h₄ : Between x₁ x₄ x₂)
  : ((∠ h₁ h₃) + (∠ h₃ h₂)) = (∟ + ∟)
  := by
  algebraic_euclid

  theorem Proposition30 (x₁ x₂ x₃ x₄ x₅ x₆ : EuclidPoint)
  (h₁ : (x₁ - x₂) || (x₃ - x₄))
  (h₂ : (x₃ - x₄) || (x₅ - x₆))
  (h₃ : |x₃ - x₄| ≠ 0)
  : (x₁ - x₂) || (x₅ - x₆) := by
  algebraic_euclid

theorem Proposition32 (x₁ x₂ x₃ : EuclidPoint)
  (h₁ : |x₁ - x₂| ≠ 0)
  (h₂ : |x₁ - x₃| ≠ 0)
  (h₃ : |x₂ - x₃| ≠ 0)
  :
  (∠ h₁ h₂ + ∠ h₃ (by degen : |x₂ - x₁| ≠ 0) +
  ∠ (by degen : |x₃ - x₁| ≠ 0) (by degen : |x₃ - x₂| ≠ 0)) = (∟ + ∟) := by
  algebraic_euclid

theorem Proposition33 (x₁ x₂ x₃ x₄ : EuclidPoint)
  (h₁ : (x₁ - x₂) || (x₃ - x₄))
  (h₂ : (x₁ - x₃) || (x₂ - x₄))
  (h₃ : Noncol x₁ x₂ x₃)
  : |x₁ - x₃| = |x₂ - x₄| := by
  algebraic_euclid

theorem Proposition37 (x₁ x₂ x₃ x₄ : EuclidPoint)
  (h₁ : (x₃ - x₄) || (x₁ - x₂)) :
  Area x₁ x₂ x₃ = Area x₁ x₂ x₄ := by
  algebraic_euclid

theorem Proposition47 (z₁ z₂ z₃ : EuclidPoint)
  (h₁ : (z₂ - z₁) ⊥ (z₃ - z₁)) :
  |z₃ - z₂|^2 = |z₂ - z₁|^2 + |z₃ - z₁|^2 := by
  algebraic_euclid

theorem Proposition48 (z₁ z₂ z₃ : EuclidPoint)
  (h₁ : |z₃ - z₂|^2 = |z₂ - z₁|^2 + |z₃ - z₁|^2) :
  (z₂ - z₁) ⊥ (z₃ - z₁) := by
  algebraic_euclid

-- BONUS
lemma BetweenCol (x y z : EuclidPoint)
  (h₁ : Between x y z) :
  Col x y z := by
  algebraic_euclid

theorem MediansConcurrent (A B C M₁ M₂ M₃ G : EuclidPoint)
  (h₂ : 2 * M₁.x = B.x + C.x)
  (h₃ : 2 * M₁.y = B.y + C.y)

  (h₄ : 2 * M₂.x = A.x + C.x)
  (h₅ : 2 * M₂.y = A.y + C.y)

  (h₆ : 2 * M₃.x = A.x + B.x)
  (h₇ : 2 * M₃.y = A.y + B.y)

  (h₈ : 3 * G.x = A.x + B.x + C.x)
  (h₉ : 3 * G.y = A.y + B.y + C.y)

  : Col A G M₁ ∧ Col B G M₂ ∧ Col C G M₃ := by
  algebraic_euclid
