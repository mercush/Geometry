import Mathlib
import Geometry.Simp

-- Point definition
structure EuclidPoint where
  x : ℝ
  y : ℝ

def O := EuclidPoint.mk 0 0
def I := EuclidPoint.mk 1 0

def EuclidPoint.add (p₁ p₂ : EuclidPoint) : EuclidPoint := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩
def EuclidPoint.sub (p₁ p₂ : EuclidPoint) : EuclidPoint := ⟨p₁.x - p₂.x, p₁.y - p₂.y⟩
def EuclidPoint.scale (t : ℝ) (p : EuclidPoint) : EuclidPoint := ⟨t * p.x, t * p.y⟩

notation p₁ " +ₚ " p₂ => EuclidPoint.add p₁ p₂

@[euclid_simp]
lemma EuclidPoint.add_def (p₁ p₂ : EuclidPoint) :
  (p₁ +ₚ p₂) = EuclidPoint.mk (p₁.x + p₂.x) (p₁.y + p₂.y) := rfl

notation t " •ₚ " p => EuclidPoint.scale t p

@[euclid_simp]
lemma EuclidPoint.scale_def (t : ℝ) (p : EuclidPoint) :
  (t •ₚ p) = EuclidPoint.mk (t * p.x) (t * p.y) := rfl

-- Segment definition
structure Segment where
  start : EuclidPoint
  endpoint : EuclidPoint

notation A " -ₛ " B => Segment.mk A B

-- Direction of segment
def Segment.direction (seg : Segment) : EuclidPoint :=
⟨seg.endpoint.x - seg.start.x, seg.endpoint.y - seg.start.y⟩

@[euclid_simp]
lemma Segment.direction_def (seg : Segment) :
  seg.direction = ⟨seg.endpoint.x - seg.start.x, seg.endpoint.y - seg.start.y⟩ := rfl


-- Length of segment
noncomputable
def Segment.length (seg : Segment) : ℝ := Real.sqrt ((seg.endpoint.x - seg.start.x)^2 + (seg.endpoint.y - seg.start.y)^2)

notation "|" seg "|" => Segment.length seg

lemma Segment.length_def (seg : Segment) :
  seg.length = Real.sqrt ((seg.endpoint.x - seg.start.x)^2 + (seg.endpoint.y - seg.start.y)^2) := rfl

lemma Segment.length_sq_eq {a b : EuclidPoint}: |a -ₛ b| ^ 2 = (a.x - b.x) ^ 2 + (a.y - b.y) ^ 2 := by
  rw [Segment.length_def]
  have h : 0 ≤ (b.x - a.x)^2 + (b.y - a.y)^2 := by nlinarith
  simp
  rw [Real.sq_sqrt h]
  nlinarith

grind_pattern Segment.length_sq_eq => |a -ₛ b|

-- @[euclid_simp]
lemma Segment.length_sq_iff {s₁ s₂ : Segment} :
  |s₁| = |s₂| ↔ |s₁|^2 = |s₂|^2 := by
  constructor
  swap
  · intro h
    have hs₁ : 0 ≤ |s₁| := by
      rw [Segment.length_def]
      simp
    have hs₂ : 0 ≤ |s₂| := by
      rw [Segment.length_def]
      simp
    rw [←Real.sqrt_sq hs₁, ←Real.sqrt_sq hs₂, h]
  · intro h
    rw [h]

lemma Segment.length_eq_zero_iff {s : Segment} :
  |s|^2 = 0 ↔ |s| = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ |s| := by
      rw [Segment.length_def]
      simp
    rw [←Real.sqrt_sq hs, h]
    simp
  · intro h
    rw [h]
    simp

@[grind]
lemma Segment.length_symm {a b : EuclidPoint} :
  |a -ₛ b| = |b -ₛ a| := by
  rw [Segment.length_def, Segment.length_def]
  simp
  ring_nf

-- Unequal definition
@[euclid_simp]
def Uneq (a b : EuclidPoint) (t : ℝ) : Prop :=
  |a -ₛ b| * t = 1

lemma Uneq.symm {a b : EuclidPoint} {t : ℝ} (h : Uneq a b t) :
  Uneq b a t := by
  simp_all only [euclid_simp]
  rw [Segment.length_symm] at h
  exact h

lemma uneq_if {a b : EuclidPoint} {t : ℝ} :
  Uneq a b t → |a -ₛ b| ≠ 0 := by
  intro h
  simp_all [euclid_simp]
  by_contra h'
  rw [h'] at h
  simp_all

postfix:max "~" => Uneq.symm

-- Dot product
def EuclidPoint.dot (p₁ p₂ : EuclidPoint) : ℝ :=
  p₁.x * p₂.x + p₁.y * p₂.y

@[euclid_simp]
lemma EuclidPoint.dot_def (p₁ p₂ : EuclidPoint) :
  p₁.dot p₂ = p₁.x * p₂.x + p₁.y * p₂.y := rfl

def Segment.dot (seg₁ seg₂ : Segment) : ℝ :=
  EuclidPoint.dot seg₁.direction seg₂.direction

@[euclid_simp]
lemma Segment.dot_def (seg₁ seg₂ : Segment) :
  seg₁.dot seg₂ = (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.x - seg₂.start.x) +
  (seg₁.endpoint.y - seg₁.start.y) * (seg₂.endpoint.y - seg₂.start.y) := rfl

-- Orthogonality of segments
def Segment.orthogonal (seg₁ seg₂ : Segment) : Prop :=
  Segment.dot seg₁ seg₂ = 0

notation seg1 " ⊥ " seg2 => Segment.orthogonal seg1 seg2

@[euclid_simp]
lemma Segment.orthogonal_def (seg₁ seg₂ : Segment) :
  seg₁.orthogonal seg₂ ↔ (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.x - seg₂.start.x) +
  (seg₁.endpoint.y - seg₁.start.y) * (seg₂.endpoint.y - seg₂.start.y) = 0 := by rfl

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

noncomputable
def Angle.mk {x₁ x₂ x₃ x₄ : EuclidPoint} {t₁ t₂ : ℝ}
  (h₁ : Uneq x₁ x₂ t₁) -- |x₁ -ₛ x₂| ≠ 0)
  (h₂ : Uneq x₃ x₄ t₂)-- |x₁ -ₛ x₃| ≠ 0)
  : Angle :=
  Quotient.mk'
  (Angle'.mk
  ((x₂.x - x₁.x) * (x₄.x - x₃.x) + (x₂.y - x₁.y) * (x₄.y - x₃.y))
  ((x₂.x - x₁.x) * (x₄.y - x₃.y) - (x₂.y - x₁.y) * (x₄.x - x₃.x))
  (|x₁ -ₛ x₂| * |x₃ -ₛ x₄|)
  (by apply uneq_if at h₁; apply uneq_if at h₂; aesop))

notation "∠" => Angle.mk

def Angle.mk' (cos sin norm : ℝ) (h : norm ≠ 0) : Angle :=
  Quotient.mk' (Angle'.mk cos sin norm h)

@[euclid_simp]
lemma Angle.coordToTrig {x₁ x₂ x₃ x₄ : EuclidPoint} {t₁ t₂ : ℝ}
  {h₁ : Uneq x₁ x₂ t₁} {h₂ : Uneq x₃ x₄ t₂} :
  Angle.mk h₁ h₂ = Angle.mk' ((x₂.x - x₁.x) * (x₄.x - x₃.x) + (x₂.y - x₁.y) * (x₄.y - x₃.y))
    ((x₂.x - x₁.x) * (x₄.y - x₃.y) - (x₂.y - x₁.y) * (x₄.x - x₃.x))
    (|x₁ -ₛ x₂| * |x₃ -ₛ x₄|) (by apply uneq_if at h₁; apply uneq_if at h₂; aesop) := rfl

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
def Line.parallel (l₁ l₂ : Line) : Prop :=
  l₁.seg.parallel l₂.seg

notation l₁ " || " l₂ => Line.parallel l₁ l₂

@[euclid_simp]
lemma Line.parallel_def (l₁ l₂ : Line) :
  l₁.parallel l₂ ↔ l₁.seg.parallel l₂.seg := by rfl

def Line.orthogonal (l₁ l₂ : Line) : Prop :=
  l₁.seg.orthogonal l₂.seg

notation l₁ " ⊥ " l₂ => Line.orthogonal l₁ l₂

@[euclid_simp]
lemma Line.orthogonal_def (l₁ l₂ : Line) :
  l₁.orthogonal l₂ ↔ l₁.seg.orthogonal l₂.seg := by rfl

-- Line containment
def Line.containsPoint (p : EuclidPoint) (l : Line) : Prop :=
  (p.x - l.seg.start.x) * (l.seg.endpoint.y - l.seg.start.y)
  - (p.y - l.seg.start.y) * (l.seg.endpoint.x - l.seg.start.x) = 0

notation p " ∈ " l => Line.containsPoint p l

def Line.containsSegment (s : Segment) (l : Line) : Prop :=
  (s.start ∈ l) ∧ (s.endpoint ∈ l)

notation p " ∈ " l => Line.containsSegment p l

@[euclid_simp]
lemma Line.containsPoint_def (p : EuclidPoint) (l : Line) :
  (p ∈ l) ↔ (p.x - l.seg.start.x) * (l.seg.endpoint.y - l.seg.start.y)
  - (p.y - l.seg.start.y) * (l.seg.endpoint.x - l.seg.start.x) = 0 := by rfl

@[euclid_simp]
lemma Line.containsSegment_def (s : Segment) (l : Line) :
  (s ∈ l) ↔ (s.start ∈ l) ∧ (s.endpoint ∈ l) := by rfl
-- Existence of points will follow from using Buchberger algorithm and checking
-- if 1 is in the Grobner basis.

-- Circle definition
structure EuclidCircle where
  center : EuclidPoint
  sq_radius : ℝ

-- Circle containment
def EuclidCircle.containsPoint (c : EuclidCircle) (p : EuclidPoint) : Prop :=
  (p.x - c.center.x)^2 + (p.y - c.center.y)^2 = c.sq_radius

notation p " ∈ " c => EuclidCircle.containsPoint c p

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
@[euclid_simp]
def Noncol (p₁ p₂ p₃ : EuclidPoint) (t : ℝ): Prop :=
  t * ((p₂.x - p₁.x) * (p₃.y - p₁.y) -
  (p₂.y - p₁.y) * (p₃.x - p₁.x)) = 1

-- Betweenness
@[euclid_simp]
def Between (p₁ p₂ p₃ : EuclidPoint) : Prop :=
  |p₁ -ₛ p₂| + |p₂ -ₛ p₃| = |p₁ -ₛ p₃|

-- Area
@[euclid_simp]
noncomputable
def Area (p₁ p₂ p₃ : EuclidPoint) : ℝ :=
  2⁻¹ * ((p₂.x - p₁.x) * (p₃.y - p₁.y) -
  (p₂.y - p₁.y) * (p₃.x - p₁.x))
