import Geometry.Tactic
import Geometry.Angles

variable (C D E F G H I J K L
  M N O P Q R S T U V X Y Z : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

set_option autoImplicit true

theorem Converse_IsoscelesTriangleAltitudeMedian
  (h1 : |A - B| = |A - C|)
  (h2 : isMidpoint D (B - C))
  (h3 : Noncol A B C)
  : (A - D) ⊥ (B - C) := by algebraic_euclid
