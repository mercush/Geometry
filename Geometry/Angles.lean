import Geometry.AlgebraicEuclid

-- TAngle definition
structure TAngle' where
  cos : ℝ
  sin : ℝ
  h : sin ≠ 0

def TAngle.eq (a b : TAngle') : Prop :=
  a.cos * b.sin = b.cos * a.sin

def TAngle.eq.eqv : Equivalence TAngle.eq where
  refl := by intro x; unfold eq; grind
  symm := by intro x y; unfold eq; grind
  trans := by intro x y z h1 h2; unfold eq at *; have := x.h; have := y.h; grind

instance TAngle.instSetoid : Setoid TAngle' where
  r := TAngle.eq
  iseqv := TAngle.eq.eqv

def TAngle := Quotient TAngle.instSetoid

noncomputable
def TAngle.mk (x₂ x₁ x₄ : EuclidPoint) : TAngle :=
  Quotient.mk'
  (TAngle'.mk
  ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
  ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x))
  sorry)

notation "∠T" => TAngle.mk

def TAngle.mk' (cos sin : ℝ): TAngle :=
  Quotient.mk' (TAngle'.mk cos sin sorry)

@[euclid_simp]
lemma TAngle.coordToTrig {x₁ x₂ x₄ : EuclidPoint} :
  TAngle.mk x₂ x₁ x₄ = TAngle.mk' ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
    ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x)) := rfl

@[euclid_simp]
lemma TAngle.eq' {cos₁ sin₁ : ℝ} {cos₂ sin₂ : ℝ} :
  TAngle.mk' cos₁ sin₁ = TAngle.mk' cos₂ sin₂ ↔
  cos₁ * sin₂ = cos₂ * sin₁ := by
  constructor
  · intro h; unfold eq at *; sorry
  · intro h; unfold eq at *; sorry

-- Addition of TAngles
noncomputable
def addTAngles (a b : TAngle) : TAngle :=
  Quotient.lift₂
    -- The operation on the underlying type
    (fun a' b' => TAngle.mk'
      (a'.cos * b'.cos - a'.sin * b'.sin)
      (a'.sin * b'.cos + a'.cos * b'.sin))
    (by intro a1 b1 a2 b2 h1 h2; rw [TAngle.eq']; sorry)
    a b

noncomputable
instance : Add TAngle where
  add := addTAngles

@[euclid_simp]
lemma TAngle.addEq {cos₁ sin₁ : ℝ} {cos₂ sin₂ : ℝ} :
  TAngle.mk' cos₁ sin₁ + TAngle.mk' cos₂ sin₂ =
  TAngle.mk'
    (cos₁ * cos₂ - sin₁ * sin₂)
    (sin₁ * cos₂ + cos₁ * sin₂) := rfl

@[euclid_simp]
def rightTAngle : TAngle :=
  TAngle.mk' 0 1

notation "∟T" => rightTAngle

-- Weak equality of TAngles
-- @[euclid_simp]
def WeakTAngleEq (a b : TAngle) : Prop :=
  Quotient.lift₂
    (fun a' b' => a'.cos * b'.sin = b'.cos * a'.sin)
    (by sorry)
    a b

@[euclid_simp]
lemma WeakTAngleEq_def (cos₁ sin₁ norm₁ : ℝ) (nonzero₁ : norm₁ ≠ 0)
  (cos₂ sin₂ norm₂ : ℝ) (nonzero₂ : norm₂ ≠ 0) :
  WeakTAngleEq (TAngle.mk' cos₁ sin₁) (TAngle.mk' cos₂ sin₂) ↔
  cos₁ * norm₂ = cos₂ * norm₁ := by
  sorry
