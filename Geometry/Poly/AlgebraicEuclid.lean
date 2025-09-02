import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

variable (σ : Type*) [Finite σ]

-- Point with polynomial coordinates
structure PolyPoint where
  x : MvPolynomial σ ℝ
  y : MvPolynomial σ ℝ

def PolyPoint.add (p₁ p₂ : PolyPoint σ) : PolyPoint σ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩
def PolyPoint.scale (t : MvPolynomial σ ℝ) (p : PolyPoint σ) : PolyPoint σ := ⟨t * p.x, t * p.y⟩

instance : Add (PolyPoint σ) where
  add := PolyPoint.add

instance : HSMul (MvPolynomial σ ℝ) (PolyPoint σ) (PolyPoint σ) where
  hSMul := PolyPoint.scale

-- Polynomial segment definition
structure PolySegment (σ : Type*) where
  start : PolyPoint σ
  endpoint : PolyPoint σ

instance : HSub (PolyPoint σ) (PolyPoint σ) (PolySegment σ) where
  hSub := PolySegment.mk

-- Direction of polynomial segment
def PolySegment.direction (seg : PolySegment σ) : PolyPoint σ :=
⟨seg.endpoint.x - seg.start.x, seg.endpoint.y - seg.start.y⟩

-- Squared length of polynomial segment
def PolySegment.lengthSq (seg : PolySegment σ) : MvPolynomial σ ℝ := 
  (seg.endpoint.x - seg.start.x)^2 + (seg.endpoint.y - seg.start.y)^2

-- Dot product of polynomial points
def PolyPoint.dot (p₁ p₂ : PolyPoint σ) : MvPolynomial σ ℝ :=
  p₁.x * p₂.x + p₁.y * p₂.y

-- Dot product of polynomial segments
def PolySegment.dot (seg₁ seg₂ : PolySegment σ) : MvPolynomial σ ℝ :=
  PolyPoint.dot seg₁.direction seg₂.direction

-- Orthogonality of polynomial segments
def PolySegment.orthogonal (seg₁ seg₂ : PolySegment σ) : Prop :=
  PolySegment.dot seg₁ seg₂ = 0

notation seg1 " ⊥ " seg2 => PolySegment.orthogonal seg1 seg2

-- Parallel polynomial segments
def PolySegment.parallel (seg₁ seg₂ : PolySegment σ) : Prop :=
  (seg₁.endpoint.x - seg₁.start.x) * (seg₂.endpoint.y - seg₂.start.y) -
  (seg₂.endpoint.x - seg₂.start.x) * (seg₁.endpoint.y - seg₁.start.y) = 0

notation seg1 " || " seg2 => PolySegment.parallel seg1 seg2

-- Polynomial collinearity
def PolyCol (p₁ p₂ p₃ : PolyPoint σ) : Prop :=
  (p₂.x - p₁.x) * (p₃.y - p₁.y) -
  (p₂.y - p₁.y) * (p₃.x - p₁.x) = 0

-- Polynomial noncollinearity  
def PolyNoncol (A B C : PolyPoint σ) : Prop := ¬PolyCol A B C

-- Polynomial betweenness (using squared lengths to avoid square roots)
def PolyBetween (p₁ p₂ p₃ : PolyPoint σ) : Prop :=
  let d₁₂ := (p₁ - p₂).lengthSq
  let d₂₃ := (p₂ - p₃).lengthSq  
  let d₁₃ := (p₁ - p₃).lengthSq
  -- Using (a + b)² = c² for betweenness when a,b,c ≥ 0
  d₁₂ + d₂₃ + 2 * MvPolynomial.X (sorry : σ) = d₁₃  -- Need to handle sqrt properly

-- Polynomial area (parallelogram area, not triangle)
def PolyAreaP (p₁ p₂ p₃ : PolyPoint σ) : MvPolynomial σ ℝ :=
  (p₂.x - p₁.x) * (p₃.y - p₁.y) - (p₂.y - p₁.y) * (p₃.x - p₁.x)

-- Polynomial midpoint predicate
def PolyIsMidpoint (A : PolyPoint σ) (seg : PolySegment σ) : Prop :=
  2 * A.x = (seg.start.x + seg.endpoint.x) ∧ 2 * A.y = (seg.start.y + seg.endpoint.y)

-- Polynomial circumcenter predicate
def PolyIsCircumcenter (O A B C : PolyPoint σ) : Prop :=
  (O - A).lengthSq = (O - B).lengthSq ∧ (O - A).lengthSq = (O - C).lengthSq

-- Polynomial parallelogram
def PolyParallelogram (A B C D : PolyPoint σ) : Prop :=
  C.x = (D.x - A.x) + B.x ∧
  C.y = (D.y - A.y) + B.y

-- Polynomial orthocenter
def PolyIsOrthocenter (H A B C : PolyPoint σ) : Prop :=
  ((H - A) ⊥ (B - C)) ∧ ((H - B) ⊥ (A - C)) ∧ ((H - C) ⊥ (A - B))

-- Point equality via squared distance
def PolyPointEq (A B : PolyPoint σ) : Prop := (A - B).lengthSq = 0

-- Polynomial equilateral triangle
def PolyIsEquilateral (A B C : PolyPoint σ) : Prop :=
  (A - B).lengthSq = (B - C).lengthSq ∧ (B - C).lengthSq = (C - A).lengthSq

-- Point on circle
def PolyOnCircle (X O P : PolyPoint σ) : Prop :=
  (X - O).lengthSq = (P - O).lengthSq

-- Tangent to circle at point
def PolyTangentToCircleAt (P Q O T : PolyPoint σ) : Prop :=
  PolyOnCircle T O T ∧  -- T is on the circle
  PolyCol P T Q ∧       -- P, T, Q are collinear
  (O - T) ⊥ (P - Q)     -- Radius OT is perpendicular to tangent line PQ

-- Intersection of line and circle
def PolyIntersectionLineCircle (H P Q O R : PolyPoint σ) : Prop :=
  PolyCol H P Q ∧ PolyOnCircle H O R

-- Rectangle predicate
def PolyIsRectangle (A B C D : PolyPoint σ) : Prop :=
  ((A - B) ⊥ (B - C)) ∧ ((B - C) ⊥ (C - D)) ∧ ((C - D) ⊥ (D - A)) ∧ (D - A) ⊥ (A - B)

-- Incenter predicate
def PolyIsIncenter (I A B C : PolyPoint σ) : Prop :=
  ∃ (D E F : PolyPoint σ),
    PolyCol D B C ∧ ((I - D) ⊥ (B - C)) ∧
    PolyCol E A C ∧ ((I - E) ⊥ (A - C)) ∧
    PolyCol F A B ∧ ((I - F) ⊥ (A - B)) ∧
    (I - D).lengthSq = (I - E).lengthSq ∧ (I - E).lengthSq = (I - F).lengthSq

-- Foot of perpendicular
def PolyIsFoot (F P A B : PolyPoint σ) : Prop :=
  PolyCol F A B ∧ (P - F) ⊥ (A - B)

-- Reflection of point
def PolyIsReflection (P' P A B : PolyPoint σ) : Prop :=
  ∃ (M : PolyPoint σ), PolyIsMidpoint M (P - P') ∧ ((P - P') ⊥ (A - B)) ∧ PolyCol M A B