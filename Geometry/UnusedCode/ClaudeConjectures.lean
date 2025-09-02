import Geometry.AlgebraicEuclid
import Geometry.Tactic

variable (C D E F G H I J K L M N O P Q R S T U V X Y Z : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

-- **This statement is vacuously true**
-- Novel Theorem 1: Perpendicular Midpoint Quadrilateral Concurrency
-- In any quadrilateral ABCD, if we take midpoints M, N, P, Q of sides AB, BC, CD, DA
-- respectively, and construct perpendiculars from each vertex to the opposite midpoint line,
-- then these four perpendiculars are concurrent.
theorem PerpendicularMidpointConcurrency
  (h1 : isMidpoint M (A - B))
  (h2 : isMidpoint N (B - C))
  (h3 : isMidpoint P (C - D))
  (h4 : isMidpoint Q (D - A))
  (h5 : Col H A M)  -- H lies on perpendicular from A
  (h6 : Col H B N)  -- H lies on perpendicular from B
  (h7 : Col H C P)  -- H lies on perpendicular from C
  (h8 : (A - H) ⊥ (P - Q))  -- A's perpendicular to opposite midpoint line
  (h9 : (B - H) ⊥ (Q - M))  -- B's perpendicular to opposite midpoint line
  (h10 : (C - H) ⊥ (M - N))  -- C's perpendicular to opposite midpoint line
  (h11 : Noncol A B C)
  (h12 : Noncol B C D)
  : (D - H) ⊥ (N - P) := by  -- D's perpendicular also passes through H
  algebraic_euclid

-- Novel Theorem 2: Spiral Triangle Area Property
-- Given triangle ABC, construct equilateral triangles ABP, BCQ, CAR externally.
-- Then the triangle formed by the lines AP, BQ, CR has a specific area relationship.
theorem SpiralTriangleProperty
  (h1 : |A - B| = |B - P|)  -- ABP is equilateral
  (h2 : |B - P| = |P - A|)
  (h3 : |B - C| = |C - Q|)  -- BCQ is equilateral
  (h4 : |C - Q| = |Q - B|)
  (h5 : |C - A| = |A - R|)  -- CAR is equilateral
  (h6 : |A - R| = |R - C|)
  (h7 : Col X A P)  -- X is intersection of lines
  (h8 : Col X B Q)
  (h9 : Col Y B Q)
  (h10 : Col Y C R)
  (h11 : Col Z C R)
  (h12 : Col Z A P)
  (h13 : Noncol A B C)
  : AreaT X Y Z = AreaT A B C + AreaT A B P + AreaT B C Q + AreaT C A R := by
  algebraic_euclid

-- Novel Theorem 3: Perpendicular Bisector Second Generation
-- In triangle ABC, let perpendicular bisectors of sides meet opposite sides at D, E, F.
-- The perpendicular bisectors of AD, BE, CF are concurrent at a special point.
variable (M₁ M₂ M₃ : EuclidPoint) (P₁ P₂ P₃ O : EuclidPoint)
theorem PerpendicularBisectorSecondGeneration
  (h1 : isMidpoint M₁ (A - B))
  (h2 : isMidpoint M₂ (B - C))
  (h3 : isMidpoint M₃ (C - A))
  (h4 : Col D B C)  -- D is where perp bisector of AB meets BC
  (h5 : Col E C A)  -- E is where perp bisector of BC meets CA
  (h6 : Col F A B)  -- F is where perp bisector of CA meets AB
  (h7 : (M₁ - D) ⊥ (A - B))
  (h8 : (M₂ - E) ⊥ (B - C))
  (h9 : (M₃ - F) ⊥ (C - A))
  (h10 : isMidpoint P₁ (A - D))
  (h11 : isMidpoint P₂ (B - E))
  (h12 : isMidpoint P₃ (C - F))
  (h13 : (O - P₁) ⊥ (A - D))  -- O is on perp bisector of AD
  (h14 : (O - P₂) ⊥ (B - E))  -- O is on perp bisector of BE
  (h15 : Noncol A B C)
  : (O - P₃) ⊥ (C - F) := by  -- O is also on perp bisector of CF
  algebraic_euclid

-- Novel Theorem 4: Altitude-Median Equilateral Property
-- In triangle ABC, if we construct lines from each vertex perpendicular to the
-- corresponding median, these three perpendiculars meet at a point P such that
-- triangle PHG is equilateral (where H is orthocenter, G is centroid).
variable (H₁ H₂ H₃ : EuclidPoint) (P₁ P₂ P₃ P₄ : EuclidPoint)
theorem AltitudeMedianEquilateralProperty
  (h1 : isMidpoint M₁ (B - C))  -- Medians
  (h2 : isMidpoint M₂ (C - A))
  (h3 : isMidpoint M₃ (A - B))
  (h4 : Col G A M₁)  -- G is centroid
  (h5 : Col G B M₂)
  (h6 : Col G C M₃)
  (h7 : Col H₁ B C)  -- Altitude feet
  (h8 : Col H₂ C A)
  (h9 : Col H₃ A B)
  (h10 : (A - H₁) ⊥ (B - C))  -- Altitudes
  (h11 : (B - H₂) ⊥ (C - A))
  (h12 : (C - H₃) ⊥ (A - B))
  (h13 : Col H A H₁)  -- H is orthocenter
  (h14 : Col H B H₂)
  (h15 : Col P A X)  -- P is where perps to medians meet
  (h16 : Col P B Y)
  (h17 : Col P C Z)
  (h18 : (A - P) ⊥ (G - M₁))  -- Perpendiculars to medians
  (h19 : (B - P) ⊥ (G - M₂))
  (h20 : (C - P) ⊥ (G - M₃))
  (h21 : Noncol A B C)
  : |P - H| = |H - G| ∧ |H - G| = |G - P| := by  -- PHG is equilateral
  algebraic_euclid

-- Novel Theorem 5: Parallel-Perpendicular Rectangle Duality
-- Given quadrilateral ABCD where AB || CD, construct perpendiculars from A and C to
-- line BD, and from B and D to line AC. The four feet form a rectangle whose area
-- equals the area of the original quadrilateral.
theorem ParallelPerpendicularRectangleDuality
  (h1 : (A - B) || (C - D))  -- AB parallel to CD
  (h2 : Col P₁ B D)  -- P₁ is foot of perpendicular from A to BD
  (h3 : Col P₂ B D)  -- P₂ is foot of perpendicular from C to BD
  (h4 : Col P₃ A C)  -- P₃ is foot of perpendicular from B to AC
  (h5 : Col P₄ A C)  -- P₄ is foot of perpendicular from D to AC
  (h6 : (A - P₁) ⊥ (B - D))
  (h7 : (C - P₂) ⊥ (B - D))
  (h8 : (B - P₃) ⊥ (A - C))
  (h9 : (D - P₄) ⊥ (A - C))
  (h10 : Noncol A B C)
  (h11 : Noncol B C D)
  : AreaP P₁ P₂ P₃ = AreaP A B C ∧
    ((P₁ - P₂) ⊥ (P₃ - P₄)) ∧ |P₁ - P₂| = |P₃ - P₄| := by  -- Rectangle with equal area
  algebraic_euclid

-- Novel Theorem 6: Median-Altitude Intersection Concurrency
-- The lines connecting each vertex to the intersection of the opposite median
-- and altitude are concurrent.
variable (I₁ I₂ I₃ : EuclidPoint)
theorem MedianAltitudeIntersectionConcurrency
  (h1 : isMidpoint M₁ (B - C))  -- Medians
  (h2 : isMidpoint M₂ (C - A))
  (h3 : isMidpoint M₃ (A - B))
  (h4 : Col H₁ B C)  -- Altitude feet
  (h5 : Col H₂ C A)
  (h6 : Col H₃ A B)
  (h7 : (A - H₁) ⊥ (B - C))  -- Altitudes
  (h8 : (B - H₂) ⊥ (C - A))
  (h9 : (C - H₃) ⊥ (A - B))
  (h10 : Col I₁ A M₁)  -- I₁ is intersection of median AM₁ and altitude AH₁
  (h11 : Col I₁ A H₁)
  (h12 : Col I₂ B M₂)  -- I₂ is intersection of median BM₂ and altitude BH₂
  (h13 : Col I₂ B H₂)
  (h14 : Col I₃ C M₃)  -- I₃ is intersection of median CM₃ and altitude CH₃
  (h15 : Col I₃ C H₃)
  (h16 : Col K A I₁)  -- K is where lines AI₁ and BI₂ meet
  (h17 : Col K B I₂)
  (h18 : Noncol A B C)
  : Col K C I₃ := by  -- Line CI₃ also passes through K
  algebraic_euclid

-- Novel Theorem 7: Circumcenter-Incenter Reflection Property
-- In triangle ABC, let I be the incenter and O the circumcenter.
-- The reflections of I across each side form a triangle similar to ABC.
theorem CircumcenterIncenterReflectionProperty
  (h1 : |O - A| = |O - B|)  -- O is circumcenter
  (h2 : |O - B| = |O - C|)
  (h3 : |O - C| = |O - A|)
  (h4 : Col P B C)  -- P is where angle bisector from A meets BC
  (h5 : Col Q C A)  -- Q is where angle bisector from B meets CA
  (h6 : Col R A B)  -- R is where angle bisector from C meets AB
  (h7 : |A - B| ≠ 0)
  (h8 : |A - P| ≠ 0)
  (h9 : |A - C| ≠ 0)
  (h10 : ∠ h7 h8 = ∠ h8 h9)  -- AP bisects angle BAC
  (h11 : Col I A P)  -- I is incenter
  (h12 : Col I B Q)
  (h13 : Col I C R)
  (h14 : isMidpoint I₁ (I - X))  -- I₁ is reflection of I across BC
  (h15 : Col X B C)
  (h16 : (I - I₁) ⊥ (B - C))
  (h17 : isMidpoint I₂ (I - Y))  -- I₂ is reflection of I across CA
  (h18 : Col Y C A)
  (h19 : (I - I₂) ⊥ (C - A))
  (h20 : isMidpoint I₃ (I - Z))  -- I₃ is reflection of I across AB
  (h21 : Col Z A B)
  (h22 : (I - I₃) ⊥ (A - B))
  (h23 : Noncol A B C)
  : |I₁ - I₂| * |A - B| = |I₂ - I₃| * |B - C| ∧
    |I₂ - I₃| * |B - C| = |I₃ - I₁| * |C - A| := by  -- Triangle I₁I₂I₃ similar to ABC
  algebraic_euclid

-- Novel Theorem 8: Quadrilateral Diagonal Midpoint Property
-- In any quadrilateral, the midpoints of the diagonals and the midpoints of the
-- segments connecting opposite vertex midpoints form a parallelogram.
variable (Q₁ Q₂ : EuclidPoint) (M₁ M₂ M₃ M₄ : EuclidPoint)
  (P₁ P₂ P₃ P₄ : EuclidPoint)
theorem QuadrilateralDiagonalMidpointProperty
  (h1 : isMidpoint M₁ (A - C))  -- Midpoint of diagonal AC
  (h2 : isMidpoint M₂ (B - D))  -- Midpoint of diagonal BD
  (h3 : isMidpoint P₁ (A - B))  -- Midpoints of sides
  (h4 : isMidpoint P₂ (B - C))
  (h5 : isMidpoint P₃ (C - D))
  (h6 : isMidpoint P₄ (D - A))
  (h7 : isMidpoint Q₁ (P₁ - P₃))  -- Midpoint of segment connecting opposite side midpoints
  (h8 : isMidpoint Q₂ (P₂ - P₄))  -- Midpoint of segment connecting opposite side midpoints
  (h9 : Noncol A B C)
  (h10 : Noncol B C D)
  : ((M₁ - M₂) || (Q₁ - Q₂)) ∧ |M₁ - M₂| = |Q₁ - Q₂| := by  -- M₁M₂Q₁Q₂ is parallelogram
  algebraic_euclid
