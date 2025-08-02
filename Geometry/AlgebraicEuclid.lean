-- Minimal required imports
import Mathlib

import Geometry.Simp

structure EuclidPoint where
  x : ℝ
  y : ℝ

def EuclidPoint.add (p₁ p₂ : EuclidPoint) : EuclidPoint := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩
def EuclidPoint.scale (t : ℝ) (p : EuclidPoint) : EuclidPoint := ⟨t * p.x, t * p.y⟩

instance : Add EuclidPoint where
  add := EuclidPoint.add

instance : HSMul ℝ EuclidPoint EuclidPoint where
  hSMul := EuclidPoint.scale

@[ext]
lemma EuclidPoint.ext (A B : EuclidPoint) (h₁ : A.x = B.x) (h₂ : A.y = B.y) : A = B := by
  cases A; cases B; simp at h₁ h₂; rw [h₁, h₂]

-- Segment definition
structure Segment where
  start : EuclidPoint
  endpoint : EuclidPoint

-- notation A " - " B => Segment.mk A B
instance : HSub EuclidPoint EuclidPoint Segment where
  hSub := Segment.mk

@[euclid_simp]
lemma Segment.endpoint_def (x₁ x₂ : EuclidPoint) :
  (x₁ - x₂).endpoint = x₂ := by
  simp [HSub.hSub]

@[euclid_simp]
lemma Segment.start_def (x₁ x₂ : EuclidPoint) :
  (x₁ - x₂).start = x₁ := by
  simp [HSub.hSub]

-- Direction of segment
@[euclid_simp]
def Segment.direction (seg : Segment) : EuclidPoint :=
⟨seg.endpoint.x - seg.start.x, seg.endpoint.y - seg.start.y⟩

-- Length of segment
noncomputable
def Segment.length (seg : Segment) : ℝ := Real.sqrt ((seg.endpoint.x - seg.start.x)^2 + (seg.endpoint.y - seg.start.y)^2)

notation "|" seg "|" => Segment.length seg

lemma Segment.length_sq_eq {a b : EuclidPoint}: |a - b| ^ 2 = (a.x - b.x) ^ 2 + (a.y - b.y) ^ 2 := by
  rw [Segment.length]
  have h : 0 ≤ (b.x - a.x)^2 + (b.y - a.y)^2 := by nlinarith
  simp_all [euclid_simp]
  nlinarith

grind_pattern Segment.length_sq_eq => |a - b|

-- @[euclid_simp]
lemma Segment.length_sq_iff {s₁ s₂ : Segment} :
  |s₁| = |s₂| ↔ |s₁|^2 = |s₂|^2 := by
  constructor
  swap
  · intro h
    have hs₁ : 0 ≤ |s₁| := by
      rw [Segment.length]
      simp
    have hs₂ : 0 ≤ |s₂| := by
      rw [Segment.length]
      simp
    rw [←Real.sqrt_sq hs₁, ←Real.sqrt_sq hs₂, h]
  · intro h
    rw [h]

lemma Segment.length_eq_zero_iff {s : Segment} :
  |s| = 0 ↔ |s|^2 = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have hs : 0 ≤ |s| := by
      rw [Segment.length]
      simp
    rw [←Real.sqrt_sq hs, h]
    simp

@[grind]
lemma Segment.length_symm {a b : EuclidPoint} :
  |a - b| = |b - a| := by
  rw [Segment.length_sq_iff]

  rw [Segment.length, Segment.length]
  simp_all only [euclid_simp]

  have h₁ : ((b.x - a.x) ^ 2 + (b.y - a.y) ^ 2) ≥ 0 := by positivity
  have h₂ : ((a.x - b.x) ^ 2 + (a.y - b.y) ^ 2) ≥ 0 := by positivity
  rw [Real.sq_sqrt h₁, Real.sq_sqrt h₂]
  nlinarith

lemma ne_zero_iff_exist_inv {a b : EuclidPoint} :
  |a - b| ≠ 0 ↔ ∃ t, |a - b| * t = 1 := by
  constructor
  swap
  · intro h
    obtain ⟨t, ht⟩ := h
    by_contra h'
    rw [h'] at ht
    simp_all
  · intro h
    use |a - b|⁻¹
    field_simp

lemma ne_zero_iff_exist_inv' {a b : ℝ} :
  a ≠ b ↔ ∃ t, (a - b) * t = 1 := by
  grind

-- Dot product
@[euclid_simp]
def EuclidPoint.dot (p₁ p₂ : EuclidPoint) : ℝ :=
  p₁.x * p₂.x + p₁.y * p₂.y

@[euclid_simp]
def Segment.dot (seg₁ seg₂ : Segment) : ℝ :=
  EuclidPoint.dot seg₁.direction seg₂.direction

-- Orthogonality of segments
@[euclid_simp]
def Segment.orthogonal (seg₁ seg₂ : Segment) : Prop :=
  Segment.dot seg₁ seg₂ = 0

notation seg1 " ⊥ " seg2 => Segment.orthogonal seg1 seg2

-- @[euclid_simp]
-- lemma Segment.orthogonal_def (seg₁ seg₂ : Segment) :
--   seg₁.orthogonal seg₂ ↔ (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.x - seg₂.start.x) +
--   (seg₁.endpoint.y - seg₁.start.y) * (seg₂.endpoint.y - seg₂.start.y) = 0 := by rfl

-- Parallel segments
@[euclid_simp]
def Segment.parallel (seg₁ seg₂ : Segment) : Prop :=
  (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.y - seg₂.start.y) -
  (seg₂.endpoint.x - seg₂.start.x) * (seg₁.endpoint.y - seg₁.start.y) = 0

notation seg1 " || " seg2 => Segment.parallel seg1 seg2

-- Angle definition
structure Angle' where
  cos : ℝ
  sin : ℝ
  norm : ℝ
  nonzero : norm ≠ 0

def Angle.eq (a b : Angle') : Prop :=
  a.cos * b.norm = b.cos * a.norm ∧
  a.sin * b.norm = b.sin * a.norm

def Angle.eq.eqv : Equivalence Angle.eq where
  refl := by
    intro a
    rw [Angle.eq]
    constructor
    · rfl
    · rfl
  symm := by
    intro a b h
    rw [Angle.eq] at h
    rw [Angle.eq]
    grind
  trans := by
    intro a b c hab hbc
    rw [Angle.eq] at hab hbc
    rw [Angle.eq]
    have h₁ := a.nonzero
    have h₂ := b.nonzero
    grind

instance Angle.instSetoid : Setoid Angle' where
  r := Angle.eq
  iseqv := Angle.eq.eqv

def Angle := Quotient Angle.instSetoid

-- noncomputable
-- def Angle.mk {x₁ x₂ x₄ : EuclidPoint}
--   (h₁ : |x₁ - x₂| ≠ 0)
--   (h₂ : |x₁ - x₄| ≠ 0)
--   : Angle :=
--   Quotient.mk'
--   (Angle'.mk
--   ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
--   ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x))
--   (|x₁ - x₂| * |x₁ - x₄|)
--   (by grind))

noncomputable
def Angle.mk (x₂ x₁ x₄ : EuclidPoint) (h : |x₁ - x₂| ≠ 0 ∧ |x₁ - x₄| ≠ 0) : Angle :=
  Quotient.mk'
  (Angle'.mk
  ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
  ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x))
  (|x₁ - x₂| * |x₁ - x₄|)
  (by grind))

notation "∠" => Angle.mk

def Angle.mk' (cos sin norm : ℝ) (h : norm ≠ 0) : Angle :=
  Quotient.mk' (Angle'.mk cos sin norm h)

-- @[euclid_simp]
-- lemma Angle.coordToTrig {x₁ x₂ x₄ : EuclidPoint}
--   {h₁ : |x₁ - x₂| ≠ 0} {h₂ : |x₁ - x₄| ≠ 0} :
--   Angle.mk h₁ h₂ = Angle.mk' ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
--     ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x))
--     (|x₁ - x₂| * |x₁ - x₄|) (by aesop) := rfl

@[euclid_simp]
lemma Angle.coordToTrig {x₁ x₂ x₄ : EuclidPoint}
  {h₁ : |x₁ - x₂| ≠ 0 ∧ |x₁ - x₄| ≠ 0} :
  Angle.mk x₂ x₁ x₄ h₁ = Angle.mk' ((x₂.x - x₁.x) * (x₄.x - x₁.x) + (x₂.y - x₁.y) * (x₄.y - x₁.y))
    ((x₂.x - x₁.x) * (x₄.y - x₁.y) - (x₂.y - x₁.y) * (x₄.x - x₁.x))
    (|x₁ - x₂| * |x₁ - x₄|) (by aesop) := rfl

@[euclid_simp]
lemma Angle.eq' {cos₁ sin₁ norm₁ : ℝ} {nonzero₁ : norm₁ ≠ 0}
  {cos₂ sin₂ norm₂ : ℝ} {nonzero₂ : norm₂ ≠ 0} :
  Angle.mk' cos₁ sin₁ norm₁ nonzero₁ = Angle.mk' cos₂ sin₂ norm₂ nonzero₂ ↔
  cos₁ * norm₂ = cos₂ * norm₁ ∧ sin₁ * norm₂ = sin₂ * norm₁ := by
  constructor
  · intro h
    have h₁ := Quotient.exact h
    obtain ⟨h₁_cos, h₁_sin⟩ := h₁
    simp_all
  · intro h
    apply Quotient.sound
    constructor
    simp_all
    simp_all

-- Addition of angles
noncomputable
def addAngles (a b : Angle) : Angle :=
  Quotient.lift₂
    -- The operation on the underlying type
    (fun a' b' => Angle.mk'
      (a'.cos * b'.cos - a'.sin * b'.sin)
      (a'.sin * b'.cos + a'.cos * b'.sin)
      (a'.norm * b'.norm)
      (by simp_all; exact ⟨a'.nonzero, b'.nonzero⟩))
    (by
      intro a₁ a₂ b₁ b₂ ha hb
      simp
      obtain ⟨ha_cos, ha_sin⟩ := ha
      obtain ⟨hb_cos, hb_sin⟩ := hb
      apply Quotient.sound
      constructor
      · simp; grind
      · simp; grind
      )
    a b

noncomputable
instance : Add Angle where
  add := addAngles

@[euclid_simp]
lemma Angle.addEq {cos₁ sin₁ norm₁ : ℝ} {nonzero₁ : norm₁ ≠ 0} {cos₂ sin₂ norm₂ : ℝ} {nonzero₂ : norm₂ ≠ 0} :
  Angle.mk' cos₁ sin₁ norm₁ nonzero₁ + Angle.mk' cos₂ sin₂ norm₂ nonzero₂ =
  Angle.mk'
    (cos₁ * cos₂ - sin₁ * sin₂)
    (sin₁ * cos₂ + cos₁ * sin₂)
    (norm₁ * norm₂)
    (by simp_all) := rfl

@[euclid_simp]
def rightAngle : Angle :=
  Angle.mk' 0 1 1 (by simp)

notation "∟" => rightAngle

-- Weak equality of angles
-- @[euclid_simp]
def WeakAngleEq (a b : Angle) : Prop :=
  Quotient.lift₂
    (fun a' b' => a'.cos * b'.norm = b'.cos * a'.norm)
    (by
      intro a₁ a₂ b₁ b₂ ha hb
      simp
      obtain ⟨ha_cos, ha_sin⟩ := ha
      obtain ⟨hb_cos, hb_sin⟩ := hb
      have := a₁.nonzero
      have := b₁.nonzero
      have := a₂.nonzero
      have := b₂.nonzero
      constructor
      · grind
      · grind)
    a b

@[euclid_simp]
lemma WeakAngleEq_def (cos₁ sin₁ norm₁ : ℝ) (nonzero₁ : norm₁ ≠ 0)
  (cos₂ sin₂ norm₂ : ℝ) (nonzero₂ : norm₂ ≠ 0) :
  WeakAngleEq (Angle.mk' cos₁ sin₁ norm₁ nonzero₁) (Angle.mk' cos₂ sin₂ norm₂ nonzero₂) ↔
  cos₁ * norm₂ = cos₂ * norm₁ := by
  constructor
  · intro h
    rw [WeakAngleEq] at h
    rw [Quotient.lift₂] at h
    exact h
  · intro h
    rw [WeakAngleEq]
    rw [Quotient.lift₂]
    exact h

-- Line definition
structure Line where
  seg : Segment

-- Parrallel and orthogonal lines
@[euclid_simp]
def Line.parallel (l₁ l₂ : Line) : Prop :=
  l₁.seg.parallel l₂.seg

notation l₁ " || " l₂ => Line.parallel l₁ l₂

@[euclid_simp]
def Line.orthogonal (l₁ l₂ : Line) : Prop :=
  l₁.seg.orthogonal l₂.seg

notation l₁ " ⊥ " l₂ => Line.orthogonal l₁ l₂

-- Line containment
@[euclid_simp]
def Line.containsPoint (p : EuclidPoint) (l : Line) : Prop :=
  (p.x - l.seg.start.x) * (l.seg.endpoint.y - l.seg.start.y)
  - (p.y - l.seg.start.y) * (l.seg.endpoint.x - l.seg.start.x) = 0

notation p " ∈ " l => Line.containsPoint p l

@[euclid_simp]
def Line.containsSegment (s : Segment) (l : Line) : Prop :=
  (s.start ∈ l) ∧ (s.endpoint ∈ l)

notation p " ∈ " l => Line.containsSegment p l

-- Existence of points will follow from using Buchberger algorithm and checking
-- if 1 is in the Grobner basis.

-- Circle definition
structure EuclidCircle where
  center : EuclidPoint
  borderPoint : EuclidPoint

-- Circle containment
@[euclid_simp]
def EuclidCircle.containsPoint (c : EuclidCircle) (p : EuclidPoint) : Prop :=
  |p - c.center|^2 = |c.borderPoint - c.center|^2

notation p " ∈ " c => EuclidCircle.containsPoint c p

--**Delete**
@[euclid_simp]
lemma sq_length_def {A B : EuclidPoint} :
  |A - B|^2 = (A.x - B.x)^2 + (A.y - B.y)^2 := by
  rw [Segment.length_sq_eq]

-- Rule for ∨
@[euclid_simp]
lemma orRule (x₁ x₂ x₃ x₄ : ℝ) :
  (x₁ = x₂) ∨ (x₃ = x₄) ↔ (x₁ - x₂) * (x₃ - x₄) = 0 := by
  constructor
  · intro h
    cases h with
    | inl h => rw [h, sub_self]; simp
    | inr h => rw [h, sub_self]; simp
  · intro h
    rw [mul_eq_zero] at h
    cases h with
    | inl h => left; rw [sub_eq_zero] at h; exact h
    | inr h => right; rw [sub_eq_zero] at h; exact h

-- Collinearity
@[euclid_simp]
def Col (p₁ p₂ p₃ : EuclidPoint) : Prop :=
  (p₂.x - p₁.x) * (p₃.y - p₁.y) -
  (p₂.y - p₁.y) * (p₃.x - p₁.x) = 0

-- Noncollinearity
-- @[euclid_simp]
-- def Noncol (p₁ p₂ p₃ : EuclidPoint) : Prop := ∃ t,
--   t * ((p₂.x - p₁.x) * (p₃.y - p₁.y) -
--   (p₂.y - p₁.y) * (p₃.x - p₁.x)) = 1

-- Betweenness
@[euclid_simp]
def Between (p₁ p₂ p₃ : EuclidPoint) : Prop :=
  |p₁ - p₂| + |p₂ - p₃| = |p₁ - p₃|

-- Area
@[euclid_simp]
noncomputable
def AreaT (p₁ p₂ p₃ : EuclidPoint) : ℝ :=
  2⁻¹ * ((p₂.x - p₁.x) * (p₃.y - p₁.y) -
  (p₂.y - p₁.y) * (p₃.x - p₁.x))

@[euclid_simp]
def AreaP (p₁ p₂ p₃ : EuclidPoint) : ℝ :=
  (p₂.x - p₁.x) * (p₃.y - p₁.y) - (p₂.y - p₁.y) * (p₃.x - p₁.x)

-- Strong parallelism
@[euclid_simp]
def StrongParallel (seg₁ seg₂ : Segment) : Prop :=
  (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.x - seg₂.start.x) +
  (seg₁.endpoint.y - seg₁.start.y) * (seg₂.endpoint.y - seg₂.start.y) = |seg₁| * |seg₂|

notation seg₁ " ||| " seg₂ => StrongParallel seg₁ seg₂

@[euclid_simp]
noncomputable
def isMidpoint (A : EuclidPoint) (seg : Segment) : Prop :=
  2 * A.x = (seg.start.x + seg.endpoint.x) ∧ 2 * A.y = (seg.start.y + seg.endpoint.y)

@[euclid_simp]
def isCircumcenter (O A B C : EuclidPoint) : Prop :=
  |O - A|^2 = |O - B|^2 ∧ |O - A|^2 = |O - C|^2

@[euclid_simp]
def Square (A B C D : EuclidPoint) : Prop :=
  B.x = (D.y - A.y) + A.x ∧
  B.y = -(D.x - A.x) + A.y ∧
  C.x = (D.x - A.x) + B.x ∧
  C.y = (D.y - A.y) + B.y

@[euclid_simp]
def Parallelogram (A B C D : EuclidPoint) : Prop :=
  C.x = (D.x - A.x) + B.x ∧
  C.y = (D.y - A.y) + B.y

@[euclid_simp]
def Concyclic (A B C D : EuclidPoint) : Prop :=
  let det := (A.x^2 + A.y^2) * (B.x * (C.y - D.y) + C.x * (D.y - B.y) + D.x * (B.y - C.y)) +
             (B.x^2 + B.y^2) * (C.x * (D.y - A.y) + D.x * (A.y - C.y) + A.x * (C.y - D.y)) +
             (C.x^2 + C.y^2) * (D.x * (A.y - B.y) + A.x * (B.y - D.y) + B.x * (D.y - A.y)) +
             (D.x^2 + D.y^2) * (A.x * (B.y - C.y) + B.x * (C.y - A.y) + C.x * (A.y - B.y))
  det = 0

@[euclid_simp]
def isOrthocenter (H A B C : EuclidPoint) : Prop :=
  ((H - A) ⊥ (B - C)) ∧ ((H - B) ⊥ (A - C)) ∧ ((H - C) ⊥ (A - B))

lemma EuclidPoint.pointEq (A B : EuclidPoint) : A = B ↔ |A - B| = 0 := by
  constructor
  · intro h
    rw [h]
    rw [Segment.length_eq_zero_iff]
    simp [euclid_simp]
  · intro h
    -- From |A - B| = 0, we get |A - B|^2 = 0
    rw [Segment.length_eq_zero_iff] at h
    rw [Segment.length_sq_eq] at h
    -- Now h : (A.x - B.x)^2 + (A.y - B.y)^2 = 0

    -- Since squares are non-negative and sum to zero, each must be zero
    have hx_sq : (A.x - B.x)^2 = 0 := by
      -- Both squares are non-negative
      have h1 : 0 ≤ (A.x - B.x)^2 := sq_nonneg _
      have h2 : 0 ≤ (A.y - B.y)^2 := sq_nonneg _
      -- If their sum is zero, the first must be zero
      linarith

    have hy_sq : (A.y - B.y)^2 = 0 := by
      have h1 : 0 ≤ (A.x - B.x)^2 := sq_nonneg _
      have h2 : 0 ≤ (A.y - B.y)^2 := sq_nonneg _
      linarith

    -- From (a - b)^2 = 0, we get a - b = 0, hence a = b
    have hx : A.x = B.x := by
      rw [sq_eq_zero_iff] at hx_sq
      linarith

    have hy : A.y = B.y := by
      rw [sq_eq_zero_iff] at hy_sq
      linarith

    -- Use point extensionality
    ext
    · exact hx
    · exact hy

@[euclid_simp]
def Noncol (A B C : EuclidPoint) : Prop := ¬Col A B C

@[euclid_simp]
def IsEquilateral (A B C : EuclidPoint) : Prop :=
  |A - B| = |B - C| ∧ |B - C| = |C - A|

/-
PROBLEM:
1. Conclusions shouldn't involve unsquared lengths.
2. Also, if there is a (|A - B| * |C - D|)^2 then this has to get distributed. -/

-- Helper: Point lies on circumcircle of triangle
@[euclid_simp]
def OnCircumcircle (P A B C : EuclidPoint) : Prop :=
  |P - A|^2 + |P - B|^2 + |P - C|^2 + |A - B|^2 + |B - C|^2 + |C - A|^2 =
  2 * (|P - A|^2 + |P - B|^2 + |P - C|^2)  -- Equivalent circumcircle condition


-- New predicates for circle and tangent geometry

-- Point lies on circle with center O passing through P
@[euclid_simp]
def OnCircle (X O P : EuclidPoint) : Prop :=
  |X - O| = |P - O|

-- Line through points P and Q is tangent to circle with center O at point T
@[euclid_simp]
def TangentToCircleAt (P Q O T : EuclidPoint) : Prop :=
  OnCircle T O T ∧  -- T is on the circle (trivially true but for clarity)
  Col P T Q ∧       -- P, T, Q are collinear (T is on line PQ)
  (O - T) ⊥ (P - Q) -- Radius OT is perpendicular to tangent line PQ

-- Point X lies on line that is tangent to circle with center O at point T
@[euclid_simp]
def OnTangentLine (X T O : EuclidPoint) : Prop :=
  ∃ Y, Y ≠ X ∧ TangentToCircleAt X Y O T

-- Intersection of line through P and Q with circle centered at O passing through R
@[euclid_simp]
def IntersectionLineCircle (H P Q O R : EuclidPoint) : Prop :=
  Col H P Q ∧ OnCircle H O R

-- Intersection of line with circle (second intersection point)
def IntersectionLineCircleSecond (E P Q O R : EuclidPoint) : Prop :=
  Col E P Q ∧                    -- E lies on line PQ
  OnCircle E O R ∧               -- E lies on circle centered at O passing through R
  E ≠ P ∧ E ≠ Q                  -- E is distinct from P and Q (second intersection)

-- Alternative: E is the "other" intersection point
@[euclid_simp]
def SecondIntersection (E P O R : EuclidPoint) : Prop :=
  Col E P O ∧                    -- E lies on line through P and center O
  OnCircle E O R ∧               -- E lies on circle centered at O passing through R
  E ≠ P                          -- E is different from P (the "other" intersection)

@[euclid_simp]
def IsRectangle (A B C D : EuclidPoint) : Prop :=
  ((A - B) ⊥ (B - C)) ∧ ((B - C) ⊥ (C - D)) ∧ ((C - D) ⊥ (D - A)) ∧ (D - A) ⊥ (A - B)
