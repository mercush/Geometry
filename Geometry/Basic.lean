import Geometry.Tactic

variable (C D E F G H I J K L
  M N O P Q R S T U V X Y Z : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

theorem Proposition4

  (h1 : |A - B| = |P - Q|)
  (h2 : |A - C| = |P - R|)
  (nondegen1 : |A - B| ≠ 0)
  (nondegen2 : |A - C| ≠ 0)
  (h3 : ∠ B A C (by nondegen) =
  ∠ Q P R (by nondegen))
  :
  |B - C| = |Q - R|
  := by
  algebraic_euclid

theorem Proposition5
  (h1 : |A - B| = |A - C|)
  (nondegen1 : |B - A| ≠ 0)
  (nondegen2 : |B - C| ≠ 0)
  (nondegen3 : |C - A| ≠ 0):
  ∠ A B C (by nondegen) = ∠ B C A (by nondegen)
  := by
  algebraic_euclid

theorem Proposition6
  (h1 : |B - A| ≠ 0)
  (h2 : |B - C| ≠ 0)
  (h3 : |C - A| ≠ 0)
  (h4 : ∠ A B C (by nondegen) = ∠ B C A (by nondegen))
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

theorem Proposition8
  (h1 : |A - B| = |P - Q|)
  (h2 : |B - C| = |Q - R|)
  (h3 : |A - C| = |P - R|)
  (nondegen1 : |A - B| ≠ 0)
  (nondegen2 : |C - A| ≠ 0) :
  WeakAngleEq (∠ B A C (by nondegen)) (∠ Q P R (by nondegen)) := by
  algebraic_euclid

theorem Proposition10
  (h1 : isMidpoint M (A - B))
  : |A - M| = |M - B| := by
  algebraic_euclid

theorem Proposition13
  (h1 : |D - A| ≠ 0)
  (h2 : |D - B| ≠ 0)
  (h3 : |D - C| ≠ 0)
  (h4 : Between A D B)
  : ((∠ A D C (by nondegen)) + (∠ C D B (by nondegen))) = (∟ + ∟)
  := by
  algebraic_euclid

theorem Proposition15
  (h1 : Col A C B)
  (h2 : Col D C E)
  (h3 : |C - A| ≠ 0)
  (h4 : |C - B| ≠ 0)
  (h5 : |C - D| ≠ 0)
  (h6 : |C - E| ≠ 0)
  (h7 : Between A C B)
  (h8 : Between D C E)
  : ∠ A C D (by nondegen) = ∠ B C E (by nondegen) := by
  algebraic_euclid

theorem Proposition30
  (h1 : (A - B) || (C - D))
  (h2 : (C - D) || (E - F))
  (nondegen1 : |C - D| ≠ 0)
  : (A - B) || (E - F) := by
  algebraic_euclid

theorem Proposition32
  (nondegen1 : |A - B| ≠ 0)
  (nondegen2 : |A - C| ≠ 0)
  (nondegen3 : |B - C| ≠ 0)
  :
  (∠ B A C (by nondegen) + ∠ C B A (by nondegen) +
  ∠ A C B (by nondegen)) = (∟ + ∟) := by
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
  (h1 : isMidpoint X (B - C))
  (h2 : isMidpoint Y (A - C))
  (h3 : isMidpoint Z (A - B))
  (h4 : Col A G X)
  (h5 : Col B G Y)
  : Col C G Z := by
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
  (h3 : isMidpoint E (D - C))
  (h4 : isMidpoint F (A - B))
  (h7 : Col G D F)
  (h8 : Col G A C)
  (h9 : Col H A C)
  (h10 : Col H B E)
  (h12 : Noncol A B C)
  : |G - A| = |G - H| := by
  algebraic_euclid

theorem IsoscelesPerpendicularBisector
  (h1 : |A - B| = |A - C|)
  (h2 : isMidpoint D (B - C))
  : (A - D) ⊥ (B - C) := by
  algebraic_euclid

theorem PerpendicularBisectorsConcurrent
  (h1 : isMidpoint P (A - B))
  (h2 : isMidpoint Q (B - C))
  (h3 : isMidpoint R (A - C))
  (h4 : (O - P) ⊥ (A - B))
  (h5 : (O - Q) ⊥ (B - C))
  (h6 : Noncol A B C)
  : (O - R) ⊥ (A - C) := by
  algebraic_euclid

theorem AngleBisectorTheorem
  (h1 : Col B D C)
  (h2 : Between B D C)
  (h3 : |A - B| ≠ 0)
  (h4 : |A - D| ≠ 0)
  (h5 : |A - C| ≠ 0)
  (h8 : ∠ B A D (by nondegen) = ∠ D A C (by nondegen))
  (h9 : Noncol A B C)
  : |B - D| * |A - C| = |D - C| * |A - B| := by
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
  (h3 : isMidpoint M (A - C))
  (h4 : Noncol A B D)
  : isMidpoint M (B - D) := by
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
  (h1 : isMidpoint D (B - C))
  : 2 * (|A - B|^2 + |A - C|^2) = 4 * |A - D|^2 + |B - C|^2 := by
  algebraic_euclid

theorem gex_GDD_FULL_01_20_01
  (h1 : (D - C) ⊥ (A - B))
  (h2 : Col D A B)
  (h3 : (E - B) ⊥ (A - C))
  (h4 : Col E A C)
  (h5 : isMidpoint F (B - C))
  (h6 : isMidpoint G (D - E))
  (h7 : |C - A| ≠ 0) :
  (F - G) ⊥ (D - E) := by
  algebraic_euclid

theorem gex_1_TOP_TEN_07_2altitude
  (h1 : (D - C) ⊥ (B - A))
  (h2 : Col D A B)
  (h3 : (E - B) ⊥ (A - C))
  (h4 : Col E A C)
  (h5 : isMidpoint F (E - D))
  (h6 : isMidpoint G (B - C))
  (h7 : |A - C| ≠ 0) :
  (D - E) ⊥ (G - F) := by
  algebraic_euclid

theorem gex_GDD_FULL_01_20_02
  (h1 : isMidpoint P (B - C))
  (h2 : isMidpoint Q (A - C))
  (h3 : isMidpoint R (A - B))
  (h4 : isCircumcenter O A B C) :
  (O - P) ⊥ (Q - R) := by
  algebraic_euclid

theorem gex_GDD_FULL_more_E015_6
  (h1 : isMidpoint D (A - C))
  (h2 : isMidpoint E (B - A))
  (h3 : isMidpoint F (C - B))
  (h4 : (G - D) || (F - A))
  (h5 : (G - F) || (C - A))
  (h6 : Noncol A B C) :
  -- Conclusion: CE parallel to GB
  (C - E) || (G - B) := by
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
  (h5 : isMidpoint M (A - C))
  (h6 : isMidpoint M (B - D)) :
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
  := by
  algebraic_euclid

theorem MidpointTheorem
  (h1 : isMidpoint D (A - B))
  (h2 : isMidpoint E (A - C)) :
  ((D - E) || (B - C)) ∧ 4 * |D - E|^2 = |B - C|^2
  := by
  algebraic_euclid

theorem CevaTheorem
  (h1 : Col D B C)  -- D lies on side BC
  (h2 : Col E C A)  -- E lies on side CA
  (h3 : Col F A B)  -- F lies on side AB
  (h4 : Col A G D)  -- Line AD passes through point G
  (h5 : Col B G E)  -- Line BE passes through point G
  (h6 : Col C G F)  -- Line CF passes through point G
  (h7 : Noncol A B C)  -- Triangle ABC is non-degenerate
  :
  |A - F|^2 * |B - D|^ 2 * |C - E| ^ 2 = |F - B| ^ 2 * |D - C| ^ 2 * |E - A| ^ 2
  := by
  algebraic_euclid

theorem MenelausTheorem
  (h1 : Col D B C)  -- D lies on side BC (or its extension)
  (h2 : Col E C A)  -- E lies on side CA (or its extension)
  (h3 : Col F A B)  -- F lies on side AB (or its extension)
  (h4 : Col D E F)  -- The three points D, E, F are collinear
  (h5 : Noncol A B C)  -- Triangle ABC is non-degenerate
  :
  |A - F|^2 * |B - D|^2 * |C - E|^2 = |F - B|^2 * |D - C|^2 * |E - A|^2
  := by
  algebraic_euclid

theorem VarignonTheorem
  (h1 : isMidpoint E (A - B))  -- E is midpoint of AB
  (h2 : isMidpoint F (B - C))  -- F is midpoint of BC
  (h3 : isMidpoint G (C - D))  -- G is midpoint of CD
  (h4 : isMidpoint H (D - A))  -- H is midpoint of DA
  :
  ((E - F) || (H - G)) ∧ (F - G) || (E - H)
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
  (h1 : (A - B) ⊥ (A - C))      -- Right angle at A
  (h2 : isMidpoint M (B - C))   -- M is midpoint of hypotenuse BC
  (h3 : |A - B| ≠ 0)           -- Non-degeneracy conditions
  (h4 : |A - C| ≠ 0)
  :
  4 * |A - M|^2 = |B - C|^2
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

theorem TriangleHeightAreaTheorem
  (h1 : Col B H C)              -- H lies on line BC (foot of altitude)
  (h2 : (A - H) ⊥ (B - C))      -- AH is perpendicular to BC (altitude)
  (h5 : Noncol A B C)          -- Triangle is non-degenerate
  :
  4 * (AreaT A B C)^2 = |B - C|^2 * |A - H|^2
  := by
  algebraic_euclid
