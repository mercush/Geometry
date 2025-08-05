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

theorem HeronsTheorem:
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

variable (A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1 W1 X1 Y1 Z1 : EuclidPoint)

-- Point lies on circle with center O and radius passing through point A
def isOnCircle (P O A : EuclidPoint) : Prop := |P - O| = |A - O|

-- Incenter: center of inscribed circle
def isIncenter (I A B C : EuclidPoint) : Prop :=
  ∃ (D E F : EuclidPoint),
    Col D B C ∧ ((I - D) ⊥ (B - C)) ∧
    Col E A C ∧ ((I - E) ⊥ (A - C)) ∧
    Col F A B ∧ ((I - F) ⊥ (A - B)) ∧
    |I - D| = |I - E| ∧ |I - E| = |I - F|

-- Foot of perpendicular from P to line AB
def isFoot (F P A B : EuclidPoint) : Prop :=
  Col F A B ∧ (P - F) ⊥ (A - B)

-- Reflection of point P across line AB
def isReflection (P' P A B : EuclidPoint) : Prop :=
  ∃ (M : EuclidPoint), isMidpoint M (P - P') ∧ ((P - P') ⊥ (A - B)) ∧ Col M A B

-- Tangent line from external point
def isTangentToCircle (P T O A : EuclidPoint) : Prop :=
  isOnCircle T O A ∧ (P - T) ⊥ (O - T)

-- Angle bisector
def isAngleBisector (D A B C : EuclidPoint) 
  {h1 : |A - B| ≠ 0} 
  {h2 : |A - D| ≠ 0} 
  {h3 : |A - C| ≠ 0} : Prop :=
  Col D B C ∧ ∠ B A D (by nondegen) = ∠ D A C (by nondegen)

-- Now the IMO problems:

-- IMO 2000 Problem 1
theorem IMO_2000_P1
  (h1 : ∃ (O1 O2 : EuclidPoint), isOnCircle A O1 A ∧ isOnCircle B O1 A ∧ 
        isOnCircle A O2 B ∧ isOnCircle B O2 B)
  (h2 : ∃ (O1 O2 : EuclidPoint), isOnCircle M O1 A ∧ isOnCircle M O2 B ∧
        isOnCircle N O1 A ∧ isOnCircle N O2 B ∧ M ≠ N)
  (h3 : ∃ (O1 : EuclidPoint), Col C M A ∧ Col C M B ∧ isOnCircle C O1 A)
  (h4 : ∃ (O2 : EuclidPoint), Col D M A ∧ Col D M B ∧ isOnCircle D O2 B)
  (h5 : Col E A C ∧ Col E B D)
  (h6 : Col P A N ∧ Col P C D)
  (h7 : Col Q B N ∧ Col Q C D)
  :
  |E - P| = |E - Q| := by
  algebraic_euclid

-- IMO 2000 Problem 6 (simplified version)
theorem IMO_2000_P6
  (h1 : isOrthocenter H A B C)
  (h2 : isIncenter I A B C)
  (h3 : isFoot H1 H B C)
  (h4 : isFoot H2 H A C) 
  (h5 : isFoot H3 H A B)
  -- Reflections across incircle tangent points (simplified)
  (h6 : ∃ (T1 T2 : EuclidPoint), isReflection X1 H1 T1 T2)
  (h7 : ∃ (T1 T2 : EuclidPoint), isReflection X2 H2 T1 T2)
  (h8 : ∃ (T2 T3 : EuclidPoint), isReflection Y2 H2 T2 T3)
  (h9 : ∃ (T2 T3 : EuclidPoint), isReflection Y3 H3 T2 T3)
  (h10 : Col Z X1 X2 ∧ Col Z Y2 Y3)
  (nondegen : Noncol A B C)
  :
  |I - Z| = |I - T1| := by
  algebraic_euclid

-- IMO 2002 Problem 2a
theorem IMO_2002_P2a
  (h1 : isMidpoint O (B - C))
  (h2 : isOnCircle A O B)
  (h3 : isOnCircle D O B)
  (h4 : Col D A B)  -- D on line AB (extended)
  (h5 : isOnCircle E O B)
  (h6 : Col E O A)  -- E on line OA
  (h7 : isOnCircle F O B) 
  (h8 : Col F O A)  -- F on line OA
  (h9 : Col J O A ∧ Col J A D ∧ Col J A C)  -- J intersection of OA extended and AC
  (nondegen1 : |B - C| ≠ 0)
  (nondegen2 : |C - E| ≠ 0)
  (nondegen3 : |C - J| ≠ 0)
  (nondegen4 : |J - E| ≠ 0)
  (nondegen5 : |J - F| ≠ 0)
  :
  ∠ E C J (by nondegen) = ∠ E J F (by nondegen) := by
  algebraic_euclid

-- IMO 2004 Problem 1
theorem IMO_2004_P1
  (h1 : isMidpoint O (B - C))
  (h2 : isOnCircle M O B ∧ Col M A B)
  (h3 : isOnCircle N O B ∧ Col N A C)
  (h4 : isAngleBisector R B A C)
  (h5 : isAngleBisector R M O N)
  -- Circles through B, M, R and C, N, R
  (h6 : ∃ (O1 O2 : EuclidPoint), 
        isOnCircle B O1 B ∧ isOnCircle M O1 B ∧ isOnCircle R O1 B ∧
        isOnCircle C O2 C ∧ isOnCircle N O2 C ∧ isOnCircle R O2 C)
  -- P is second intersection of these circles
  (h7 : ∃ (O1 O2 : EuclidPoint),
        isOnCircle P O1 B ∧ isOnCircle P O2 C ∧ P ≠ R)
  (nondegen : Noncol A B C)
  :
  Col P B C := by
  algebraic_euclid

-- IMO 2005 Problem 5
theorem IMO_2005_P5
  (h1 : |D - A| = |D - B| ∧ |D - B| = |D - C|) -- D equidistant from A, B, C
  (h2 : Col E B C)
  (h3 : |F - D| = |F - E| ∧ Col F A D) -- F on AD, equidistant from D and E
  (h4 : Col P A C ∧ Col P B D) -- P intersection of AC and BD
  (h5 : Col Q E F ∧ Col Q B D) -- Q intersection of EF and BD
  (h6 : Col R E F ∧ Col R A C) -- R intersection of EF and AC
  -- Circles through A, P, D and B, P, C
  (h7 : ∃ (O1 O2 : EuclidPoint),
        isOnCircle A O1 A ∧ isOnCircle P O1 A ∧ isOnCircle D O1 A ∧
        isOnCircle B O2 B ∧ isOnCircle P O2 B ∧ isOnCircle C O2 B)
  -- M is second intersection
  (h8 : ∃ (O1 O2 : EuclidPoint),
        isOnCircle M O1 A ∧ isOnCircle M O2 B ∧ M ≠ P)
  (nondegen : Noncol A B C)
  :
  ∃ (O3 : EuclidPoint), isOnCircle P O3 P ∧ isOnCircle Q O3 P ∧  
                         isOnCircle R O3 P ∧ isOnCircle M O3 P := by
  algebraic_euclid

-- IMO 2010 Problem 2
theorem IMO_2010_P2
  (h1 : isCircumcenter O A B C)
  (h2 : isIncenter I A B C)
  (h3 : Col D A I ∧ isOnCircle D O A) -- D on AI extended, on circumcircle
  (h4 : Col F B C) -- F on line BC
  (h5 : Col E A C ∧ Col E B A ∧ Col E F A ∧ isOnCircle E O A) -- E construction
  (h6 : isMidpoint G (I - F))
  (h7 : Col K D G ∧ Col K E I) -- K intersection of DG and EI
  (nondegen : Noncol A B C)
  :
  |O - A| = |O - K| := by
  algebraic_euclid

-- IMO 2012 Problem 1
theorem IMO_2012_P1
  -- J, K, L, M are excenters of triangle ABC
  (h1 : ∃ (ra rb rc : ℝ), ra > 0 ∧ rb > 0 ∧ rc > 0 ∧
        |J - B| = ra ∧ |J - C| = ra ∧  -- J is A-excenter
        |K - A| = rb ∧ |K - C| = rb ∧  -- K is B-excenter  
        |L - A| = rc ∧ |L - B| = rc)   -- L is C-excenter
  (h2 : Col F J K ∧ Col F B L) -- F intersection of JK and BL
  (h3 : Col G J L ∧ Col G C K) -- G intersection of JL and CK
  (h4 : Col S F A ∧ Col S B C) -- S intersection of FA and BC
  (h5 : Col T G A ∧ Col T C B) -- T intersection of GA and CB
  (nondegen : Noncol A B C)
  :
  |J - S| = |J - T| := by
  algebraic_euclid

-- IMO 2014 Problem 4
theorem IMO_2014_P4
  (h1 : Col P B C) -- P on line BC
  (h2 : Col Q B C) -- Q on line BC  
  (h3 : ∠ B A P (by nondegen) = ∠ C A B (by nondegen)) -- Angle condition for P
  (h4 : ∠ C A Q (by nondegen) = ∠ B A C (by nondegen)) -- Angle condition for Q
  (h5 : isReflection M A P) -- M reflection of A across P
  (h6 : isReflection N A Q) -- N reflection of A across Q
  (h7 : Col X B M ∧ Col X C N) -- X intersection of BM and CN
  (h8 : isCircumcenter O A B C)
  (nondegen : Noncol A B C)
  :
  |O - X| = |O - A| := by
  algebraic_euclid

-- IMO 2016 Problem 1
theorem IMO_2016_P1
  (h1 : Col F B A ∨ Col F B Z) -- F on line AB extended or BZ extended
  (h2 : isAngleBisector F B A Z) -- BF bisects angle BAZ
  (h3 : isTangentToCircle C B F B) -- C on tangent to circle at B through F
  (h4 : Col C A F) -- C on line AF
  (h5 : Col D A Z) -- D on line AZ
  (h6 : Col D A C) -- D on line AC (extended)
  (h7 : ∠ C A D (by nondegen) = ∠ D A E (by nondegen)) -- AE angle bisector
  (h8 : Col E A D) -- E on line AD (extended)
  (h9 : isMidpoint M C F)
  -- Parallelogram construction
  (h10 : (E - A) || (M - X) ∧ (A - M) || (E - X)) -- EAMX is parallelogram
  (h11 : Col Y F X ∧ Col Y E M) -- Y intersection of FX and EM
  (nondegen : Noncol A B Z)
  :
  Col Y B D := by
  algebraic_euclid

-- IMO 2020 Problem 1  
theorem IMO_2020_P1
  (h1 : isAngleBisector X P B A) -- X on angle bisector of angle BPA
  (h2 : isAngleBisector Y P A B) -- Y on angle bisector of angle APB
  (h3 : Col Z A P ∧ Col Z A B ∧ Col Z X A) -- Z construction
  (h4 : Col T P A ∧ Col T P A ∧ Col T Z P) -- T construction  
  (h5 : Col D P T ∧ Col D P B ∧ Col D A Z) -- D intersection
  (h6 : Col U B P ∧ Col U B A ∧ Col U Y B) -- U construction
  (h7 : Col V P B ∧ Col V P B ∧ Col V U P) -- V construction
  (h8 : Col C P V ∧ Col C P A ∧ Col C B U) -- C intersection
  -- O is on angle bisectors
  (h9 : isAngleBisector O A D P ∧ isAngleBisector O P C B)
  (nondegen : Noncol P A B)
  :
  |O - A| = |O - B| := by
  algebraic_euclid
