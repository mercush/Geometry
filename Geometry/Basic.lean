import Geometry.Tactic

variable (C D E F G H I J K L
  M N O P Q R S T U V X Y Z : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

theorem Proposition4
  (h1 : |A - B| = |D - E|)
  (h2 : |A - C| = |D - F|)
  (h3 : |A - B| ≠ 0 ∧ |A - C| ≠ 0)
  (h4 : |D - E| ≠ 0 ∧ |D - F| ≠ 0)
  (h5 : ∠ B A C h3 = ∠ E D F h4)
  : |C - A| = |F - D| :=
  by algebraic_euclid

theorem Proposition5
  (h1 : |A - B| = |A - C|)
  (h3 : |B - C| ≠ 0)
  (h4 : |A - C| ≠ 0) :
  (∠ A B C (by nondegen)) = (∠ B C A (by nondegen))
  := by
  algebraic_euclid

theorem Proposition6
  (h2 : |A - C| ≠ 0)
  (h3 : |B - C| ≠ 0)
  (h4 : ∠ A B C (by nondegen)= ∠ B C A (by nondegen))
  (nondegen1 : Noncol A B C)
  : |A - B| = |A - C| := by
  algebraic_euclid

theorem Proposition7
  (h1 : |C - A| = |C - B|)
  (h2 : |D - A| = |D - B|)
  (h3 : Col A C B)
  (h4 : Col A D B)
  : C = D := by
  algebraic_euclid

theorem Proposition13
  (h1 : |D - A| ≠ 0)
  (h2 : |D - C| ≠ 0)
  (h3 : |D - B| ≠ 0)
  (h4 : Between A D B)
  : ((∠ A D C (by nondegen)) + (∠ C D B (by nondegen))) = (∟ + ∟)
  := by
  algebraic_euclid

theorem Proposition30
  (h1 : (A - B) || (C - D))
  (h2 : (C - D) || (E - F))
  (nondegen1 : |C - D| ≠ 0)
  : (A - B) || (E - F) := by
  algebraic_euclid

theorem Proposition32
  (h1 : |A - B| ≠ 0)
  (h2 : |A - C| ≠ 0)
  (h3 : |B - C| ≠ 0)
  (h4 : |B - A| ≠ 0)
  : ((∠ B A C (by nondegen)) + (∠ C B A (by nondegen)) + (∠ A C B (by nondegen))) = (∟ + ∟) := by
  algebraic_euclid

theorem Proposition33
  (h1 : (A - B) || (C - D))
  (h2 : (A - C) || (B - D))
  (nondegen1 : Noncol A B C)
  : |A - C| = |B - D| := by
  algebraic_euclid

theorem Proposition36
  (h1 : (C - D) || (A - B)) :
  AreaP A B C = AreaP A B D := by
  algebraic_euclid

theorem Proposition37
  (h1 : (C - D) || (A - B)) :
  AreaT A B C = AreaT A B D := by
  algebraic_euclid

theorem Proposition41
  : 2 * AreaT A B C = AreaP A B C := by
  algebraic_euclid

theorem Proposition47
  (h1 : (A - B) ⊥ (A - C)) :
  |C - B|^2 = |B - A|^2 + |C - A|^2 := by
  algebraic_euclid

theorem Proposition48
  (h1 : |C - B|^2 = |B - A|^2 + |C - A|^2) :
  (B - A) ⊥ (C - A) := by
  algebraic_euclid

-- BONUS
lemma BetweenCol
  (h1 : Between A B C) :
  Col A B C := by
  algebraic_euclid

lemma StrongParallel_imp_Parallel
  (h1 : (A - B) ||| (A - C)) :
  (A - B) || (A - C) := by
  algebraic_euclid

theorem MediansConcurrent
  (h4 : Col A G (Midpoint (B - C)))
  (h5 : Col B G (Midpoint (A - C)))
  : Col C G (Midpoint (A - B)) := by
  algebraic_euclid

theorem OrthonormalsConcurrent
  (h1 : Col X A B)
  (h2 : Col Y B C)
  (h3 : Col Z C A)
  (h4 : (A - Y) ⊥ (B - C))
  (h5 : (B - Z) ⊥ (C - A))
  (h6 : ((C - X) ⊥ (A - B)))
  (h7 : Col G A Y)
  (h8 : Col G B Z) :
  Col G C X
  := by
  algebraic_euclid

-- _GDD_FULL / more / E006-1
theorem gex_GDD_FULL_more_E006_1
  (h1 : (D - C) || (B - A))
  (h2 : (D - A) || (C - B))
  (h7 : Col G D (Midpoint (A - B)))
  (h8 : Col G A C)
  (h9 : Col H A C)
  (h10 : Col H B (Midpoint (D - C)))
  (h12 : Noncol A B C)
  : |G - A| = |G - H| := by
  algebraic_euclid

theorem IsoscelesPerpendicularBisector
  (h1 : |A - B| = |A - C|)
  : (A - (Midpoint (B - C))) ⊥ (B - C) := by
  algebraic_euclid

theorem PerpendicularBisectorsConcurrent
  (h4 : (O - (Midpoint (A - B))) ⊥ (A - B))
  (h5 : (O - (Midpoint (B - C))) ⊥ (B - C))
  : (O - (Midpoint (A - C))) ⊥ (A - C) := by
  algebraic_euclid

theorem ParallelogramOppositeSidesEqual
  (h1 : (A - B) || (D - C))
  (h2 : (A - D) || (B - C))
  (h3 : Noncol A B C)
  : |A - B| = |D - C| ∧ |A - D| = |B - C| := by
  algebraic_euclid

theorem ParallelogramDiagonalsBisect
  (h1 : (A - B) || (D - C))
  (h2 : (A - D) || (B - C))
  (h4 : Noncol A B D)
  : Midpoint (A - C) = Midpoint (B - D) := by
  algebraic_euclid

theorem ParallelogramLaw
  (h1 : (A - B) || (D - C))
  (h2 : (A - D) || (B - C))
  (h3 : Noncol A B D)
  : |A - B|^2 + |B - C|^2 + |C - D|^2 + |D - A|^2 = |A - C|^2 + |B - D|^2 := by
  algebraic_euclid

theorem StewartTheorem
  (h1 : Between B D C)
  : |A - D|^2 * |B - C| + |B - D| * |D - C| * |B - C| =
    |A - B|^2 * |D - C| + |A - C|^2 * |B - D| := by
  algebraic_euclid

theorem ApolloniusTheorem
  : 2 * (|A - B|^2 + |A - C|^2) = 4 * |A - (Midpoint (B - C))|^2 + |B - C|^2 := by
  algebraic_euclid

theorem gex_GDD_FULL_01_20_01
  (h1 : (D - C) ⊥ (A - B))
  (h2 : Col D A B)
  (h3 : (E - B) ⊥ (A - C))
  (h4 : Col E A C)
  (h7 : |C - A| ≠ 0) :
  ((Midpoint (B - C)) - (Midpoint (D - E))) ⊥ (D - E) := by
  algebraic_euclid

theorem gex_1_TOP_TEN_07_2altitude
  (h1 : (D - C) ⊥ (B - A))
  (h2 : Col D A B)
  (h3 : (E - B) ⊥ (A - C))
  (h4 : Col E A C)
  (h7 : |A - C| ≠ 0) :
  (D - E) ⊥ ((Midpoint (B - C)) - (Midpoint (E - D))) := by
  algebraic_euclid

theorem gex_GDD_FULL_01_20_02
  (h4 : isCircumcenter O A B C) :
  (O - (Midpoint (B - C))) ⊥ ((Midpoint (A - C)) - (Midpoint (A - B))) := by
  algebraic_euclid

theorem gex_GDD_FULL_more_E015_6
  (h4 : (G - (Midpoint (A - C))) || ((Midpoint (C - B)) - A))
  (h5 : (G - (Midpoint (C - B))) || (C - A)) :
  -- Conclusion: CE parallel to GB
  (C - (Midpoint (B - A))) || (G - B) := by
  algebraic_euclid

theorem gex_Other_ndgs_02
  (h1 : Col D A C)
  (h2 : (B - D) ⊥ (A - C))
  (h3 : Col E A B)
  (h4 : (C - E) ⊥ (A - B))
  (h5 : Col F B D)
  (h6 : Col F C E)
  (h7 : Noncol A B C) :
  (B - C) ⊥ (A - F) := by
  algebraic_euclid

theorem gex_Book_00EE_02_E028_2
  (h1 : Square E A C D)
  (h2 : Square B G F C) :
  (D - B) ⊥ (A - F) := by
  algebraic_euclid

theorem RhombusDiagonalsPerpendicular
  (h1 : |A - B| = |B - C|)
  (h2 : |C - D| = |D - A|)
  (h3 : |A - B| = |C - D|)
  (h4 : (A - B) || (D - C))
  (h5 : Midpoint (A - C) = Midpoint (B - D)) :
  (A - C) ⊥ (B - D)
  := by
  algebraic_euclid

theorem Pappus_Theorem
  (h1 : Col A B C)
  (h2 : Col P Q R)
  (h4 : Col X A Q)
  (h5 : Col X B P)
  (h6 : Col Y A R)
  (h7 : Col Y C P)
  (h8 : Col Z B R)
  (h9 : Col Z C Q)
  (h10 : ¬(A - Q) || (B - P))
  :
  Col X Y Z
  := by algebraic_euclid

theorem MidpointTheorem :
  (((Midpoint (A - B)) - (Midpoint (A - C))) || (B - C)) ∧ 4 * |(Midpoint (A - B)) - (Midpoint (A - C))|^2 = |B - C|^2
  := by
  algebraic_euclid

theorem CevaTheorem
  (h1 : Col D B C)
  (h2 : Col E C A)
  (h3 : Col F A B)
  (h4 : Col A G D)
  (h5 : Col B G E)
  (h6 : Col C G F)
  (h7 : Noncol A B C)
  :
  |A - F|^2 * |B - D|^ 2 * |C - E| ^ 2 = |F - B| ^ 2 * |D - C| ^ 2 * |E - A| ^ 2
  := by
  algebraic_euclid

theorem MenelausTheorem
  (h1 : Col D B C)
  (h2 : Col E C A)
  (h3 : Col F A B)
  (h4 : Col D E F)
  (h5 : Noncol A B C)
  :
  |A - F|^2 * |B - D|^2 * |C - E|^2 = |F - B|^2 * |D - C|^2 * |E - A|^2
  := by
  algebraic_euclid

theorem VarignonTheorem
  :
  (((Midpoint (A - B)) - (Midpoint (B - C))) || ((Midpoint (D - A)) - (Midpoint (C - D)))) ∧ ((Midpoint (B - C)) - (Midpoint (B - C))) || ((Midpoint (A - B)) - (Midpoint (B - C)))
  := by
  algebraic_euclid

theorem BritishFlagTheorem
  -- Rectangle ABCD with point P
  (A B C D P : EuclidPoint)
  -- ABCD is a rectangle
  (h1 : IsRectangle A B C D)
  -- Non-degeneracy
  (h2 : Noncol A B C ∧ Noncol B C D)
  :
  -- Sum of squares to opposite corners are equal
  |A - P|^2 + |C - P|^2 = |B - P|^2 + |D - P|^2
  := by
  algebraic_euclid

theorem HeronsTheorem :
  let a := |B - C|
  let b := |C - A|
  let c := |A - B|
  let s := (a + b + c) / 2
  (AreaT A B C)^2 = s * (s - a) * (s - b) * (s - c)
  := by
  algebraic_euclid

theorem MedianToHypotenuseTheorem
  (h1 : (A - B) ⊥ (A - C)) :
  4 * |A - (Midpoint (B - C))|^2 = |B - C|^2
  := by
  algebraic_euclid

theorem IntersectingChordsTheorem
  (h1 : |O - A| = |O - B|)      -- A and B are on the same circle centered at O
  (h2 : |O - B| = |O - C|)      -- C is also on the circle
  (h3 : |O - C| = |O - D|)      -- D is also on the circle
  (h6 : Between A P B)          -- P is between A and B (chord AB passes through P)
  (h7 : Between C P D)          -- P is between C and D (chord CD passes through P)
  (h9 : |C - D| ≠ 0)
  (h12 : |C - P| ≠ 0)
  :
  |A - P| * |P - B| = |C - P| * |P - D|
  := by
  algebraic_euclid

theorem HalfAngle
  (h1 : |O - A| = |O - B|)
  (h2 : |O - B| = |O - C|)
  (h3 : |C - A| ≠ 0)
  (h4 : |C - B| ≠ 0)
  (h5 : |O - B| ≠ 0):
  ∠ A C B (by nondegen) + ∠ A C B (by nondegen) = ∠ A O B (by nondegen) := by algebraic_euclid

theorem TriangleHeightAreaTheorem
  (h1 : Col B H C)
  (h2 : (A - H) ⊥ (B - C))
  (h5 : Noncol A B C)
  :
  4 * (AreaT A B C)^2 = |B - C|^2 * |A - H|^2
  := by
  algebraic_euclid

theorem Squares_On_Triangle_Sides_Perpendicular
  (h1 : Square E A C D)
  (h2 : Square B G F C) :
  (D - B) ⊥ (A - F) := by
  algebraic_euclid

theorem IsoscelesTriangleAltitudeMedian
  (h1 : |A - B| = |A - C|)
  (h2 : Col B D C)
  (h3 : (A - D) ⊥ (B - C))
  (h4 : Noncol A B C)
  : D = Midpoint (B - C) := by algebraic_euclid

theorem MidpointCollinear : Col A (Midpoint (A - B)) B ∧ |A - (Midpoint (A - B))| = |(Midpoint (A - B)) - B| := by
  algebraic_euclid

theorem PerpendicularBisectorProperty
  (h2 : (P - (Midpoint (A - B))) ⊥ (A - B))
  : |P - A| = |P - B| := by
  algebraic_euclid

theorem RightAngleMidpointProperty
  (h1 : (A - B) ⊥ (A - C))
  : |A - (Midpoint (B - C))| = |(Midpoint (B - C)) - B| ∧ |A - (Midpoint (B - C))| = |(Midpoint (B - C)) - C| := by
  algebraic_euclid

theorem SquareArea
  (h1 : Square P Q R S)
  (h2 : |P - Q| ≠ 0)
  : AreaP P Q R = |P - Q|^2 := by
  algebraic_euclid

theorem TriangleMedianLength : 4 * |A - (Midpoint (B - C))|^2 = 2 * |A - B|^2 + 2 * |A - C|^2 - |B - C|^2 := by
  algebraic_euclid

theorem RotationPreservesDistance
  (h : U.x^2 + U.y^2 = 1)
  : |A - B| = |(Rotate B A U) - A| := by
  algebraic_euclid
