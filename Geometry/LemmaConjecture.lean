import Geometry.Tactic
import Geometry.Angles

variable (C D E F G H I J K L M N O P Q R S T U V W X Y Z : EuclidPoint)
variable (A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1 W1 X1 Y1 Z1 : EuclidPoint)
variable (A2 B2 C2 D2 E2 F2 G2 H2 I2 J2 K2 L2 M2 N2 O2 P2 Q2 R2 S2 T2 U2 V2 W2 X2 Y2 Z2 : EuclidPoint)
variable (A3 B3 C3 D3 E3 F3 G3 H3 I3 J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3 X3 Y3 Z3 : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

/-
There are two things that could go wrong.
1. AlgebraicEuclid isn't able to prove the intermediate steps.
2. The SMT solver in grind isn't good enough to combine the intermediate steps to get the final result.
-/
theorem equidistance_construction
  (h1 : ((G2 - B) ⊥ (B - A)))
  (h2 : (M ∈ EuclidCircle.mk G1 A) ∧ M ∈ EuclidCircle.mk G2 B)
  (h3 : (N ∈ EuclidCircle.mk G1 A) ∧ N ∈ EuclidCircle.mk G2 M)
  (h4 : (C - M) || (B - A))
  (h5 : C ∈ EuclidCircle.mk G1 A)
  (h6 : (D - M) || (B - A))
  (h7 : D ∈ EuclidCircle.mk G2 B)
  (h8 : (E - A) || (C - A))
  (h9 : (E - B) || (D - B))
  (h10 : (X - C) || (D - C))
  (h11 : Col P A N ∧ Col P C X)
  :
  -- Conclusion: E is equidistant from P and Q
  |E - P| = |E - Q|
  := by
    have : ∠T E A B = ∠T A C M := by algebraic_euclid
    have : ∠T E B A = ∠T B D M := by algebraic_euclid
    have : ∠T B D M = ∠T A B M := by algebraic_euclid
    have : ∠T A C M = ∠T B A M := by algebraic_euclid
    have : ∃ T : EuclidPoint, Col T A M ∧ Col T M N := by sorry
    obtain ⟨T, hT1, hT2⟩ := this
    have : isMidpoint T (A - M) := by algebraic_euclid
    have : isMidpoint M (P - Q) := by algebraic_euclid
    algebraic_euclid
