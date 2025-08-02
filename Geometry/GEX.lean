import Geometry.AlgebraicEuclid
import Geometry.Tactic

variable (C D E F G H I J K L M N O P Q R S T U V X Y Z : EuclidPoint)
abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

variable (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  x13 x14 x15 x16 x17 : ℝ)

variable (t1 t2 t3 t4 t5 t6 : ℝ)

variable (u1 u2 u3 u4 u5 u6 : ℝ)
-- _GDD_FULL / more / E006-1 / Done
theorem gex'
  (h5 : 2 * x12 - x4 = 0)
  (h6 : 2 * x10 - x8 - x6 = 0)
  (h7 : 2 * x9 - x7 - x5 = 0)
  (h1 : x9 * x16 + (-x10 + x4) * x15 - x4 * x9 = 0)
  (h2 : x5 * x16 - x6 * x15 = 0)
  (h3 : x7 * x14 + (x12 - x8) * x13 - x7 * x12 = 0)
  (h4 : x5 * x14 - x6 * x13 = 0)
  (h8 : x5 * x8 + (-x6 + x4) * x7 = 0)
  (h9 : x4 * x7 - x4 * x5 = 0)
  (nondegen1 : t1 * x4 * x5 = 1) :
  x16^2 - 2 * x14 * x16 + x15^2 - 2 * x13 * x15 = 0
  := by grind


-- _GDD_FULL / 01-20 / 01 / Done
theorem gex2
  (h₁ : 2 * G.y - E.y - D.y = 0)
  (h₂ : 2 * G.x - E.x = 0)
  (h₃ : 2 * F.y - C.y - B.y = 0)
  (h₄ : 2 * F.x - C.x - B.x = 0)
  (h₅ : C.y * E.y + C.x * E.x - B.y * C.y = 0)
  (h₆ : C.x * E.y - C.y * E.x = 0)
  (h₇ : B.y * D.y - B.y * C.y = 0)
  (g₁ : t1 * (C.y^2+C.x^2) = 1)
  (g₂ : t2 * B.y^2 = 1) :
  (E.y - D.y) * G.y + E.x * G.x + (-E.y + D.y) * F.y - E.x * F.x = 0
  := by grind

-- 1_TOP_TEN / 07_2altitude / Done
theorem perpendicular_lines
  -- Initial polynomial set as hypotheses
  (h1 : 2 * x14 - x6 - x4 = 0)
  (h2 : 2 * x13 - x5 = 0)
  (h3 : 2 * x12 - x10 - x8 = 0)
  (h4 : 2 * x11 - x9 = 0)
  (h5 : x6 * x10 + x5 * x9 - x4 * x6 = 0)
  (h6 : x5 * x10 - x6 * x9 = 0)
  (h7 : x4 * x8 - x4 * x6 = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * (x6^2 + x5^2) = 1)
  (nondeg2 : t2 * x4^2 = 1)
  :
  -- Conclusion: DE ⊥ GF
  (x10 - x8) * x14 + x9 * x13 + (-x10 + x8) * x12 - x9 * x11 = 0
  := by
    grind

-- 1_TOP_TEN / 09_orth
theorem angle_equality
  -- Initial polynomial set as hypotheses
  (h1 : F.x * G.y - F.y * G.x = 0)
  (h2 : C.x * G.y + (-C.y + B.y) * G.x - B.y * C.x = 0)
  (h3 : E.x * F.y + (-E.y + B.y) * F.x - B.y * E.x = 0)
  (h4 : C.x * F.y + (D.y - C.y) * F.x - C.x * D.y = 0)
  (h5 : C.y * E.y + C.x * E.x - B.y * C.y = 0)
  (h6 : C.x * E.y - C.y * E.x = 0)
  (h7 : B.y * D.y - B.y * C.y = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * B.y * C.x^2 * (C.y^3 - 2 * B.y * C.y^2 + (C.x^2 + B.y^2) * C.y) = 1)
  (nondeg2 : t2 * B.y * C.x^3 = 1)
  (nondeg3 : t3 * (C.y^2 + C.x^2) = 1)
  (nondeg4 : t4 * B.y^2 = 1)
  :
  -- Conclusion: ∠[DGA] = ∠[AGE]
  E.x * G.y^3 + ((-E.y - D.y) * G.x - D.y * E.x) * G.y^2 + (E.x * G.x^2 + 2 * D.y * E.y * G.x) * G.y + (-E.y - D.y) * G.x^3 + D.y * E.x * G.x^2 = 0
  := by
    grind

theorem gex_1_TOP_TEN_09_orth
  (h1 : (D - C) ⊥ (B - A))
  (h2 : Col D A B)
  (h3 : (E - B) ⊥ (A - C))
  (h4 : Col E A C)
  (h5 : Col F B E)
  (h6 : Col F C D)
  (h7 : Col G A F)
  (h8 : Col G B C)
  (nondegen1 : |G - D| ≠ 0)
  (nondegen2 : |G - A| ≠ 0)
  (nondegen3 : |G - E| ≠ 0)
  (nondegen4 : C.x^3 ≠ 0)
  (nondegen5 : C.x^2 + C.y^2 ≠ 0):
  WeakAngleEq (∠ D G A (by nondegen)) (∠ A G E (by nondegen))
  -- The problem appears to be with how angles are defined.
  := by
  algebraic_euclid

-- _GDD_FULL / 01-20 / 02
theorem perpendicular_OA1_B1C1
  -- Initial polynomial set as hypotheses
  (h1 : (2 * x6 - 2 * x4) * x14 + 2 * x5 * x13 - x6^2 - x5^2 + x4^2 = 0)
  (h2 : 2 * x4 * x14 - x4^2 = 0)
  (h3 : 2 * x12 - x4 = 0)
  (h4 : 2 * x10 - x6 = 0)
  (h5 : 2 * x9 - x5 = 0)
  (h6 : 2 * x8 - x6 - x4 = 0)
  (h7 : 2 * x7 - x5 = 0)
  -- Nondegenerate condition using auxiliary variable
  (nondeg : t1 * x4 * x5 = 1)
  :
  -- Conclusion: OA1 ⊥ B1C1
  (x12 - x10) * x14 - x9 * x13 - x8 * x12 + x8 * x10 + x7 * x9 = 0
  := by
    grind

-- _Book / 00EE / 01 / E009-1
theorem parallel_CD_EF
  (h1 : (D.y - B.y) * F.y + D.x * F.x + B.y * D.y - B.y^2 = 0)
  (h2 : Col F B D)
  (h3 : (C.y - B.y) * E.y + C.x * E.x + B.y * C.y - B.y^2 = 0)
  (h4 : Col E C B)
  (h5 : (D - B) ⊥ (D - A))
  (h6 : D ∈ EuclidCircle.mk A C)
  (h7 : (C - B) ⊥ (C - A))
  (nondeg : C.y ≠ B.y)
  :
  (C - D) || (E - F)
  := by algebraic_euclid

theorem gex_Book_00EE_01_E009_1
  (h1 : (C - B) ⊥ (C - A))
  (h2 : D ∈ EuclidCircle.mk A C)
  (h3 : (D - B) ⊥ (D - A))
  (h4 : Col E B C)
  (h5 : E ∈ EuclidCircle.mk A B)
  (h6 : Col F B D)
  (h7 : F ∈ EuclidCircle.mk A B)
  (nondegen1 : B.y ≠ C.y) :
  (C - D) || (E - F)
  := by algebraic_euclid

-- _GDD_FULL / more / E015-6
theorem parallel_CE_GB
  -- Initial polynomial set as hypotheses
  (h1 : x11 * x14 - x12 * x13 + x7 * x12 - x8 * x11 = 0)
  (h2 : x5 * x14 - x6 * x13 - x5 * x12 + x6 * x11 = 0)
  (h3 : 2 * x12 - x6 - x4 = 0)
  (h4 : 2 * x11 - x5 = 0)
  (h5 : 2 * x10 - x4 = 0)
  (h6 : 2 * x8 - x6 = 0)
  (h7 : 2 * x7 - x5 = 0)
  -- Nondegenerate condition using auxiliary variable
  (nondeg : t1 * x4 * x5 = 1)
  :
  -- Conclusion: CE || GB
  x5 * x14 + (x10 - x6) * x13 - x4 * x5 = 0
  := by
    grind

-- _GDD_FULL / more /E021-3
theorem parallel_AD_BE
  -- Initial polynomial set as hypotheses
  (h1 : x6 * x10 + x5 * x9 + x6^2 + x5^2 = 0)
  (h2 : x5 * x10 - x6 * x9 = 0)
  (h3 : x6 * x8 + x5 * x7 - x6^2 - x5^2 = 0)
  (h4 : x4 * x8 - x4^2 = 0)
  (h5 : x6^2 + x5^2 - x4^2 = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * x4^2 = 1)
  (nondeg2 : t2 * x4 * x5 = 1)
  :
  -- Conclusion: AD || BE
  x7 * x10 - x8 * x9 - x4 * x7 = 0
  := by
    grind

-- Other / ndgs / 01
theorem parallel_GH_EF
  -- Initial polynomial set as hypotheses
  (h1 : (x12 - x6) * x16 + (x11 - x5) * x15 + x6 * x12 + x5 * x11 - x6^2 - x5^2 = 0)
  (h2 : (x11 - x5) * x16 + (-x12 + x6) * x15 + x5 * x12 - x6 * x11 = 0)
  (h3 : (x10 - x8) * x14 + (x9 - x7) * x13 + x8 * x10 + x7 * x9 - x8^2 - x7^2 = 0)
  (h4 : (x9 - x7) * x14 + (-x10 + x8) * x13 + x7 * x10 - x8 * x9 = 0)
  (h5 : x12^2 - 2 * x4 * x12 + x11^2 - x6^2 + 2 * x4 * x6 - x5^2 = 0)
  (h6 : x10^2 - 2 * x4 * x10 + x9^2 - x6^2 + 2 * x4 * x6 - x5^2 = 0)
  (h7 : x4 * x8 - x4 * x6 = 0)
  (h8 : x4 * x7 + x4 * x5 = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * ((x6 - x4) * x12 + x5 * x11 - x6^2 + x4 * x6 - x5^2)= 1)
  (nondeg2 : t2 * ((x6 - x4) * x10 - x5 * x9 - x6^2 + x4 * x6 - x5^2)= 1)
  (nondeg3 : t3 * x4^2 = 1)
  :
  -- Conclusion: GH || EF
  (x11 - x9) * x16 + (-x12 + x10) * x15 + (-x11 + x9) * x14 + (x12 - x10) * x13 = 0
  := by
    grind

-- Other / ndgs / 02
theorem perpendicular_BC_AF
  -- Initial polynomial set as hypotheses
  (h1 : x7 * x12 + (-x8 + x4) * x11 - x4 * x7 = 0)
  (h2 : x5 * x12 + (x10 - x6) * x11 - x5 * x10 = 0)
  (h3 : x4 * x10 - x4 * x6 = 0)
  (h4 : x6 * x8 + x5 * x7 - x4 * x6 = 0)
  (h5 : x5 * x8 - x6 * x7 = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * (x4 * x5^3) * (x6^2 + x5^2) * x4^2 = 1)
  -- (nondeg2 : t2 * (x6^2 + x5^2) = 1)
  -- (nondeg3 : t3 * x4^2 = 1)
  :
  -- Conclusion: BC ⊥ AF
  (x6 - x4) * x12 + x5 * x11 = 0
  := by
    grind

-- _Book / 00EE / 02 / E028-2
theorem perpendicular_DB_FA
  -- Initial polynomial set as hypotheses (already in Groebner basis form!)
  (h1 : F.y - C.y - C.x = 0)
  (h2 : F.x + C.y - C.x - B.y = 0)

  (h3 : G.y - C.x - B.y = 0)
  (h4 : G.x + C.y - B.y = 0)

  (h5 : D.y - C.y + C.x = 0)
  (h6 : D.x - C.y - C.x = 0)

  (h7 : E.y + C.x = 0)
  (h8 : E.x - C.y = 0)
  -- No nondegenerate conditions needed!
  :
  -- Conclusion: DB ⊥ FA
  (D.y - B.y) * F.y + D.x * F.x = 0
  := by
    grind

theorem Squares_On_Triangle_Sides_Perpendicular
  (h1 : Square E A C D)
  (h2 : Square B G F C) :
  (D - B) ⊥ (A - F) := by
  algebraic_euclid

-- _Book / 00EE / 03 / E037-20
-- Primitives needed:
-- Degeneracy: B ≠ A, D ≠ A
theorem perpendicular_AE_ED
  -- Initial polynomial set as hypotheses
  (h1 : 2 * x4 * x7 * x8 * x10 + (-x4 * x8^2 + x4 * x7^2) * x9 = 0)
  (h2 : (x8 - x6) * x10 + x7 * x9 - x8^2 + x6 * x8 - x7^2 = 0)
  (h3 : x8^2 - 2 * x6 * x8 + x7^2 = 0)
  (h4 : 2 * x6 - x4 = 0)
  -- Nondegenerate condition using auxiliary variable
  (nondeg : t1 * x4^3 * x8 = 1)
  :
  -- Conclusion: AE ⊥ ED
  x10^2 - x8 * x10 + x9^2 - x7 * x9 = 0
  := by
    grind

theorem IMO_2008_P1B
  -- Triangle ABC with orthocenter H
  (h1 : isOrthocenter H A B C)
  -- Midpoints of sides
  (h2 : isMidpoint D (C - B))
  (h3 : isMidpoint E (C - A))
  (h4 : isMidpoint F (A - B))
  -- P lies on line AB and on circle centered at D through H
  (h5 : Col P A B)
  (h6 : P ∈ EuclidCircle.mk D H)
  (h7 : P ≠ F)
  -- Q lies on line AB and on circle centered at E through H
  (h8 : Col Q A B)
  (h9 : Q ∈ EuclidCircle.mk E H)
  (h10 : Q ≠ F)
  -- R lies on line AC and on circle centered at D through H
  (h11 : Col R A C)
  (h12 : R ∈ EuclidCircle.mk D H)
  (h13 : R ≠ E)
  -- S lies on line BC and on circle centered at E through H
  (h14 : Col S B C)
  (h15 : S ∈ EuclidCircle.mk E H)
  (h16 : S ≠ D)
  -- Nondegeneracy conditions
  (h17 : Noncol A B C)
  (h18 : P ≠ Q)
  (h19 : R ≠ S)
  :
  -- Conclusion: P, Q, R, S are concyclic
  Concyclic P Q R S := by
  algebraic_euclid

theorem IMO_2021_P3
  -- D is on the angle bisector of angle ABC
  (h1 : |A - B| ≠ 0)
  (h2 : |A - D| ≠ 0)
  (h3 : |C - B| ≠ 0)
  (h4 : |C - D| ≠ 0)
  (h5 : ∠ h1 h2 = ∠ h3 h4)  -- D bisects angle ABC
  -- E is on line AC
  (h6 : Col E A C)
  -- F is on line AB
  (h7 : Col F A B)
  -- X is on line BC
  (h8 : Col X B C)
  -- Additional collinearities from construction
  (h9 : Col X A C)  -- X also on line AC
  -- P is circumcenter of triangle ADC
  (h10 : isCircumcenter P A D C)
  -- Q is circumcenter of triangle EXD
  (h11 : isCircumcenter Q E X D)
  -- Y is on line BCD
  (h12 : Col Y B C)
  (h13 : Col Y B D)
  -- Y is on line FE
  (h14 : Col Y F E)
  -- Nondegeneracy conditions
  (h15 : Noncol A B C)
  (h16 : Noncol A D C)
  (h17 : Noncol E X D)
  (h18 : |A - D| ≠ 0)
  (h19 : |B - C| ≠ 0)
  :
  -- Conclusion: Y, P, Q are collinear
  Col Y P Q := by
  algebraic_euclid
