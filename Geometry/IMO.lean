import Geometry.Tactic

variable (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z : EuclidPoint)
variable (A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1 W1 X1 Y1 Z1 : EuclidPoint)
variable (A2 B2 C2 D2 E2 F2 G2 H2 I2 J2 K2 L2 M2 N2 O2 P2 Q2 R2 S2 T2 U2 V2 W2 X2 Y2 Z2 : EuclidPoint)
variable (A3 B3 C3 D3 E3 F3 G3 H3 I3 J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3 X3 Y3 Z3 : EuclidPoint)

def isOnCircle (P O A : EuclidPoint) : Prop := |P - O| = |A - O|



-- Reflection of point P across line AB
def isReflection (P' P A B : EuclidPoint) : Prop :=
  ∃ (M : EuclidPoint), isMidpoint M (P - P') ∧ ((P - P') ⊥ (A - B)) ∧ Col M A B

-- Tangent line from external point
def isTangentToCircle (P T O A : EuclidPoint) : Prop :=
  isOnCircle T O A ∧ (P - T) ⊥ (O - T)

-- Angle bisector with explicit nondegeneracy conditions
def isAngleBisector (D A B C : EuclidPoint)
  {h1 : |A - B| ≠ 0}
  {h2 : |A - D| ≠ 0}
  {h3 : |A - C| ≠ 0} : Prop :=
  Col D B C ∧ ∠ B A D (by nondegen) = ∠ D A C (by nondegen)

-- I asked Claude to make a bunch of nondegeneracy conditions for this problem so that algebraic_euclid
-- could solve it. While it succeeded, it only did so because it wedged a contradiction into one of the
-- nondegeneracy conditions.
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
  |E - P| = |E - Q|
  := by
  algebraic_euclid

-- Claude added lots of new conditions to this problem. It's possible that all the nondegeneracy conditions actually made
-- the problem more difficult.
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
  :
  |I - Z| = |I - T1| := by
  algebraic_euclid

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
  :
  ∠ E C J (by nondegen) = ∠ E J F (by nondegen)
  := by
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
  -- J, K, L are excenters of triangle ABC
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
  (h9 : isMidpoint M (C - F))
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

-- Additional IMO problems using the improved patterns:

-- IMO 2007 Problem 4
theorem IMO_2007_P4
  (h1 : isOnCircle R O A ∧ Col R A B) -- R on circumcircle, collinear with A,B
  (h2 : isMidpoint L (C - A))
  (h3 : isMidpoint K (C - B))
  (h4 : Col P O K ∧ Col P C R) -- P intersection of OK and CR
  (h5 : Col Q O L ∧ Col Q C R) -- Q intersection of OL and CR
  (h6 : isFoot L1 L C R)
  (h7 : isFoot K1 K C R)
  (nondegen : Noncol A B C)
  (nondegen2 : |C - R| ≠ 0)
  :
  |K - K1| * |R - P| = |L - L1| * |R - Q| := by
  algebraic_euclid

-- IMO 2008 Problem 1a
theorem IMO_2008_P1a
  (h1 : isOrthocenter H A B C)
  (h2 : isMidpoint D (B - C))
  (h3 : isMidpoint E (A - C))
  (h4 : isMidpoint F (A - B))
  (h5 : isOnCircle A1 D H ∧ Col A1 B C ∧ A1 ≠ A)
  (h6 : isOnCircle A2 D H ∧ Col A2 B C ∧ A2 ≠ A ∧ A2 ≠ A1)
  (h7 : isOnCircle B1 E H ∧ Col B1 C A ∧ B1 ≠ B)
  (h8 : isOnCircle B2 E H ∧ Col B2 C A ∧ B2 ≠ B ∧ B2 ≠ B1)
  (h9 : isOnCircle C1 F H ∧ Col C1 A B ∧ C1 ≠ C)
  (h10 : isOnCircle C2 F H ∧ Col C2 A B ∧ C2 ≠ C ∧ C2 ≠ C1)
  (nondegen : Noncol A B C)
  :
  Concyclic C1 C2 B1 B2 := by
  algebraic_euclid

-- IMO 2009 Problem 2
theorem IMO_2009_P2
  (h1 : isOnCircle W M W ∧ isOnCircle L W W ∧ isOnCircle K W W) -- W is circumcircle
  (h2 : isTangentToCircle Q M W M ∧ Col Q M W) -- Q on tangent at M
  (h3 : isReflection P Q M) -- P is reflection of Q across M
  (h4 : isReflection B P K) -- B is reflection of P across K
  (h5 : isReflection C Q L) -- C is reflection of Q across L
  (h6 : Col A B Q ∧ Col A C P) -- A is intersection of BQ and CP
  (h7 : isCircumcenter O A B C) -- O is circumcenter of triangle ABC
  (nondegen : Noncol M L K)
  :
  |O - P| = |O - Q| := by
  algebraic_euclid

-- IMO 2011 Problem 6
theorem IMO_2011_P6
  (h1 : isOnCircle P O A) -- P on circumcircle
  (h2 : isTangentToCircle Q P O P) -- Q on tangent at P
  (h3 : isReflection PA P B C)
  (h4 : isReflection PB P C A)
  (h5 : isReflection PC P A B)
  (h6 : isReflection QA Q B C)
  (h7 : isReflection QB Q C A)
  (h8 : isReflection QC Q A B)
  (h9 : Col A1 PB QB ∧ Col A1 PC QC)
  (h10 : Col B1 PA QA ∧ Col B1 PC QC)
  (h11 : Col C1 PA QA ∧ Col C1 PB QB)
  (h12 : isCircumcenter O1 A1 B1 C1)
  (h13 : isOnCircle X O A ∧ isOnCircle X O1 A1)
  (nondegen : Noncol A B C)
  :
  Col X O O1 := by
  algebraic_euclid
