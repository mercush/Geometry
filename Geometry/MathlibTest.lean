import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

open EuclideanGeometry

variable {V : Type*}
  {P : Type*}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P]
  [NormedAddTorsor V P]

theorem test (a b c p : P) (h : angle b p c = Real.pi) :
dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p = dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  unfold dist
  unfold angle at h
  grind
