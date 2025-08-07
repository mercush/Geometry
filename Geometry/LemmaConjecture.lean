import Geometry.Tactic

variable (C D E F G H I J K L M N O P Q R S T U V W X Y Z : EuclidPoint)
variable (A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1 W1 X1 Y1 Z1 : EuclidPoint)
variable (A2 B2 C2 D2 E2 F2 G2 H2 I2 J2 K2 L2 M2 N2 O2 P2 Q2 R2 S2 T2 U2 V2 W2 X2 Y2 Z2 : EuclidPoint)
variable (A3 B3 C3 D3 E3 F3 G3 H3 I3 J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3 X3 Y3 Z3 : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 1 0

theorem parallel_DB_A1C1
  (h1 : Col C M A1)
  (h2 : |M - G1| = |A - G1|)
  (h3 : (G1 - B) ⊥ (B - A))
  (h4 : |C - G1|^2 = |B - A|^2 + |A - G1|^2)
  (h5 : (M - C) ⊥ (C1 - A))
  (nondeg1 : A ≠ B)
  (nondeg2 : ¬Col A B C)
  (nondeg3 : M ≠ C)
  :
  (D - B) || (A1 - C1)
  := by
    algebraic_euclid
