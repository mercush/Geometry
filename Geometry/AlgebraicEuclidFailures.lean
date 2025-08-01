import Geometry.AlgebraicEuclid
import Geometry.Tactic

variable (C D E F G H I J K L
  M N O P Q R S T U V X Y Z : EuclidPoint)

abbrev A := EuclidPoint.mk 0 0
abbrev B := EuclidPoint.mk 0 1

theorem Proposition26_ASA
  (h1 : |A - B| = |P - Q|)  -- Included side equal
  (h2 : |A - B| ≠ 0)
  (h3 : |A - C| ≠ 0)
  (h4 : |B - C| ≠ 0)
  (h5 : |P - R| ≠ 0)
  (h6 : |Q - R| ≠ 0)
  (h5 : ∠ B A C (by nondegen)= ∠ Q P R (by nondegen))  -- Angle A = Angle P
  (h6 : ∠ A B C (by nondegen) = ∠ P Q R (by nondegen))  -- Angle B = Angle Q
  (h7 : Noncol A B C)
  (h8 : Noncol P Q R)
  : |A - C|^2 = |P - R|^2 := by
  algebraic_euclid

theorem Proposition27
  (h1 : Col A B E)
  (h2 : Col C D F)
  (h3 : Col B C G)  -- Transversal
  (h4 : Col E F G)
  (h5 : |A - B| ≠ 0)
  (h6 : |B - E| ≠ 0)
  (h7 : |C - D| ≠ 0)
  (h8 : |B - C| ≠ 0)
  (h9 : ∠ h5 h8 = ∠ h6 h7)  -- Alternate interior angles equal
  : (A - B) || (C - D) := by
  algebraic_euclid

theorem Proposition29
  (h1 : (A - B) || (C - D))
  (h2 : Col A B E)
  (h3 : Col C D F)
  (h4 : Col B C G)  -- Transversal
  (h5 : Col E F G)
  (h6 : |A - B| ≠ 0)
  (h7 : |B - E| ≠ 0)
  (h8 : |C - D| ≠ 0)
  (h9 : |B - C| ≠ 0)
  : ∠ h6 h9 = ∠ h7 h8 := by
  algebraic_euclid

theorem Proposition34
  (h1 : (A - B) || (D - C))
  (h2 : (A - D) || (B - C))
  (h3 : |A - B| ≠ 0)
  (h4 : |A - D| ≠ 0)
  (h5 : |B - C| ≠ 0)
  (h6 : |D - C| ≠ 0)
  (h7 : Noncol A B C)
  : |A - B| = |D - C| ∧ |A - D| = |B - C| ∧
    ∠ h3 h4 = ∠ h5 h6 := by
  algebraic_euclid

theorem Proposition43
  (h1 : (A - B) || (D - C))
  (h2 : (A - D) || (B - C))
  (h3 : Col A E C)  -- E on diagonal AC
  (h4 : Col B F D)  -- F on diagonal BD
  (h5 : (E - F) || (A - B))
  (h6 : Noncol A B C)
  : AreaP A E F = AreaP E B C := by
  algebraic_euclid

theorem QuadrilateralAngleSum
  (h1 : |A - B| ≠ 0)
  (h2 : |A - D| ≠ 0)
  (h3 : |B - A| ≠ 0)
  (h4 : |B - C| ≠ 0)
  (h5 : |C - B| ≠ 0)
  (h6 : |C - D| ≠ 0)
  (h7 : |D - C| ≠ 0)
  (h8 : |D - A| ≠ 0)
  (h9 : Noncol A B C)
  (h10 : Noncol B C D)
  (h11 : Noncol C D A)
  : (∠ h1 h2) + (∠ h3 h4) + (∠ h5 h6) + (∠ h7 h8) = (∟ + ∟) + (∟ + ∟) := by
  algebraic_euclid

theorem RightTriangleAltitudeTheorem
  (h1 : (C - A) ⊥ (C - B))     -- Right angle at C
  (h2 : Col D A B)             -- D lies on hypotenuse AB
  (h3 : (C - D) ⊥ (A - B))     -- CD is altitude to AB
  (h4 : |C - A| ≠ 0)          -- Nondegeneracy
  (h5 : |C - B| ≠ 0)          -- Nondegeneracy
  (h6 : |A - B| ≠ 0)          -- Nondegeneracy
  : |C - D|^2 = |A - D| * |D - B| := by
  algebraic_euclid

-- IMO-style Problem: Right Triangle Altitude Theorem
-- In a right triangle ABC with right angle at C, if D is the foot of the
-- altitude from C to the hypotenuse AB, then CD² = AD · DB
theorem IMO_2021_Problem_4
  -- Triangle ABC
  (h1 : Noncol A B C)
  -- Quadrilateral ABDE with DE || AB
  (h2 : (D - E) || (A - B))
  -- Points F and G on segments AC and BC respectively
  (h3 : Col A F C)
  (h4 : Col B G C)
  (h5 : Between A F C)
  (h6 : Between B G C)
  -- FG || AB
  (h7 : (F - G) || (A - B))
  -- Quadrilaterals ABGF and ABDE have the same area
  (h8 : AreaP A B G = AreaP A B D)
  -- Nondegeneracy conditions
  (h9 : |A - B| ≠ 0)
  (h10 : |C - D| ≠ 0)
  :
  -- The midpoint of CD lies on line AB
  Col A (EuclidPoint.mk ((C.x + D.x)/2) ((C.y + D.y)/2)) B := by
  algebraic_euclid

theorem IMO_2025_Problem_2
  -- Setup: two intersecting circles and key points
  (h1 : (A ∈ EuclidCircle.mk M A) ∧ (A ∈ EuclidCircle.mk N A))  -- A on both circles
  (h2 : (B ∈ EuclidCircle.mk M A) ∧ (B ∈ EuclidCircle.mk N A))  -- B on both circles
  (h3 : (Col C M N) ∧ (C ∈ EuclidCircle.mk M A))               -- C on line MN and circle Ω
  (h4 : (Col D M N) ∧ (D ∈ EuclidCircle.mk N A))               -- D on line MN and circle Γ
  (h5 : isCircumcenter P A C D)                            -- P is circumcenter of ACD
  (h6 : (Col E A P) ∧ (E ∈ EuclidCircle.mk M A) ∧ (E ≠ A))       -- E on line AP and circle Ω
  (h7 : (Col F A P) ∧ (F ∈ EuclidCircle.mk N A) ∧ (F ≠ A))       -- F on line AP and circle Γ
  (h8 : isOrthocenter H P M N)                             -- H is orthocenter of PMN
  -- Nondegeneracy
  (h9 : Noncol A C D ∧ Noncol P M N ∧ Noncol B E F)
  :
  -- Simplified conclusion: some specific geometric relationship holds
  ∃ T : EuclidPoint, ((H - T) || (A - P)) ∧
    isCircumcenter O B E F ∧ |T - O| = |B - O|  -- T on circumcircle
  := by
  algebraic_euclid

theorem CevaTheorem_ConverseDirect
  (h1 : Col D B C)  -- D lies on side BC
  (h2 : Col E C A)  -- E lies on side CA
  (h3 : Col F A B)  -- F lies on side AB
  (h4 : |A - F| * |B - D| * |C - E| = |F - B| * |D - C| * |E - A|)  -- Ceva's ratio condition
  (h5 : Noncol A B C)  -- Triangle ABC is non-degenerate
  (h6 : Col A G D)  -- Line AD passes through point G
  (h7 : Col B G E)  -- Line BE passes through point G
  (h8 : ¬((A - D) || (B - E)))  -- Lines AD and BE are not parallel (so G exists)
  :
  Col C G F  -- Then CF also passes through G
  := by
  algebraic_euclid

theorem TangentIntersectionParallel
  -- Given points
  (A B C D E : EuclidPoint)

  -- CIRCLE A B (circle with center A passing through B)
  -- This is implicit in the OnCircle conditions

  -- ON_CIRCLE C A B (C is on circle with center A passing through B)
  (h1 : OnCircle C A B)

  -- ON_TLINE C D A C (line CD is tangent to circle centered at A at point C)
  (h2 : TangentToCircleAt C D A C)

  -- ON_TLINE B D A B (line BD is tangent to circle centered at A at point B)
  (h3 : TangentToCircleAt B D A B)

  -- INTERSECTION_LC E C A A C (E is intersection of line CA with circle AC)
  -- This means E is the second intersection of line CA with circle centered at A through C
  (h4 : SecondIntersection E C A C)

  -- Non-degeneracy conditions
  -- (h5 : A ≠ B ∧ A ≠ C ∧ B ≠ C)
  (h6 : |A - B| ≠ 0)
  (h7 : Noncol A B C)
  -- (h7 : D ≠ B ∧ D ≠ C)  -- D is external to the tangent points

  :
  -- SHOW: PARALLEL A D B E (AD is parallel to BE)
  (A - D) || (B - E)
  := by
  algebraic_euclid

theorem PtolemyTheorem
  (h1 : Concyclic A B C D)  -- ABCD is a cyclic quadrilateral
  (h2 : Noncol A B C)                -- Non-degenerate conditions
  (h3 : Noncol B C D)
  (h4 : Noncol C D A)
  (h5 : Noncol D A B)
  :
  -- The product of diagonals equals the sum of products of opposite sides
  |A - C| * |B - D| = |A - B| * |C - D| + |A - D| * |B - C|
  := by
  algebraic_euclid

theorem RightTriangleAltitudeTheorem
  (h1 : (A - B) ⊥ (A - C))      -- Right angle at A
  (h2 : Col B M C)              -- M lies on line BC
  (h3 : (A - M) ⊥ (B - C))      -- AM is perpendicular to BC (altitude condition)
  (h4 : |A - B| ≠ 0)           -- Non-degeneracy conditions
  (h5 : |A - C| ≠ 0)
  (h6 : |B - C| ≠ 0)
  (h7 : |B - M| ≠ 0)           -- M is not at B
  (h8 : |M - C| ≠ 0)           -- M is not at C
  (h9 : Noncol A B C)  -- Triangle ABC is non-degenerate
  :
  |A - M|^2 = |B - M| * |M - C|
  := by
  algebraic_euclid
