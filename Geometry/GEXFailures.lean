import Geometry.AlgebraicEuclid
import Geometry.Tactic

variable (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  x13 x14 x15 x16 x17 : ℝ)

variable (t1 t2 t3 t4 t5 t6 : ℝ)

variable (u1 u2 u3 u4 u5 u6 : ℝ)

-- 1_TOP_TEN / 08_9point
-- Grind isn't failing due to timeout. Possibly the problem is that the
-- concyclic constraint is wrong but also likely not.
theorem apollonius
  (h1 : 2 * x14 - x6 = 0)
  (h2 : 2 * x13 - x5 = 0)
  (h3 : 2 * x12 - x6 - x4 = 0)
  (h4 : 2 * x11 - x5 = 0)
  (h5 : 2 * x10 - x4 = 0)
  (h6 : (x6 - x4) * x8 + x5 * x7 = 0)
  (h7 : x5 * x8 + (-x6 + x4) * x7 - x4 * x5 = 0)
  (nondeg : t1 * (x6^2 - 2 * x4 * x6 + x5^2 + x4^2) = 1)
  :
  -x10^2*x11*x14 + x10^2*x11*x8 + x10^2*x12*x13 - x10^2*x12*x7 -
  x10^2*x13*x8 + x10^2*x14*x7 - x10*x11^2*x13 + x10*x11^2*x7 + x10*x11*x13^2 + x10*x11*x14^2 -
  x10*x11*x7^2 - x10*x11*x8^2 - x10*x12^2*x13 + x10*x12^2*x7 - x10*x13^2*x7 + x10*x13*x7^2 +
  x10*x13*x8^2 - x10*x14*x7 + x11^2*x13*x8 - x11^2*x14*x7 - x11*x13^2*x8 - x11*x14^2*x8 + x11*x14*x7^2 +
  x11*x14*x8^2 + x12^2*x13*x8 - x12^2*x14*x7 + x12*x13^2*x7 - x12*x13*x7^2 - x12*x13*x8^2 + x12*x14^2*x7 = 0
  := by grind

theorem apollonius_v2
  (h1 : 2 * x14 - x6 = 0)
  (h2 : 2 * x13 - x5 = 0)
  (h3 : 2 * x12 - x6 - x4 = 0)
  (h4 : 2 * x11 - x5 = 0)
  (h5 : 2 * x10 - x4 = 0)
  (h6 : x9 = 0)
  (h7 : x8 - u1 * x4 * x5^2 = 0)
  (h8 : x7 + u1 * x4 * x5 * x6 - u1 * x4^2 * x5 = 0)
  (nondegen1 : u1 * x6^2 - 2 * u1 * x4 * x6 + u1 * x5^2 + u1 * x4^2 - 1 = 0)
  :
  -x10^2*x11*x14 + x10^2*x11*x8 + x10^2*x12*x13 - x10^2*x12*x7 -
  x10^2*x13*x8 + x10^2*x14*x7 - x10*x11^2*x13 + x10*x11^2*x7 + x10*x11*x13^2 + x10*x11*x14^2 -
  x10*x11*x7^2 - x10*x11*x8^2 - x10*x12^2*x13 + x10*x12^2*x7 - x10*x13^2*x7 + x10*x13*x7^2 +
  x10*x13*x8^2 - x10*x14*x7 + x11^2*x13*x8 - x11^2*x14*x7 - x11*x13^2*x8 - x11*x14^2*x8 + x11*x14*x7^2 +
  x11*x14*x8^2 + x12^2*x13*x8 - x12^2*x14*x7 + x12*x13^2*x7 - x12*x13*x7^2 - x12*x13*x8^2 + x12*x14^2*x7 = 0
  := by
    grind

-- Other / ndg1 / 44
-- Probably legitimately not enough compute
theorem parallel_DB_A1C1
  -- Initial polynomial set as hypotheses
  (h1 : (x10 - x6) * x14 - x6 * x10 - x5 * x9 + x6^2 + x5^2 = 0)
  (h2 : (x10 - x6) * x11 - x5 * x10 + x6 * x9 = 0)
  (h3 : x10^2 - 2 * x8 * x10 + x9^2 - 2 * x7 * x9 = 0)
  (h4 : (2 * x6 - 2 * x4) * x8 - 2 * x5 * x7 - x6^2 - x5^2 + x4^2 = 0)
  (h5 : 2 * x4 * x8 - x4^2 = 0)
  -- Nondegenerate conditions using auxiliary variables
  (nondeg1 : t1 * x4 * (x10 - x6) - 1 = 0)
  (nondeg2 : t2 * x4 * x5 - 1 = 0)
  :
  -- Conclusion: DB || A1C1
  x9 * x14 + (x10 - x4) * x11 = 0
  := by
    grind

-- Same theorem but with Groebner basis
theorem parallel_DB_A1C1_groebner
  -- Groebner basis as hypotheses
  (h1 : x14 - u4 * x4 * x5 * x9 - x6 + u4 * x4 * x5^2 = 0)
  (h2 : x13 = 0)
  (h3 : x12 = 0)
  (h4 : x11 + u3 * x4 * x6 * x9 - u3 * x4 * x5 * x6 - x5 = 0)
  (h5 : x10^2 - 2 * x8 * x10 + x9^2 - 2 * x7 * x9 = 0)
  (h6 : u4 * x4 * x10 - u4 * x4 * x6 - 1 = 0)
  (h7 : 2 * x8 - x4 = 0)
  (h8 : 2 * x7 - 4 * u1 * x4 * x6^2 + 4 * u1 * x4^2 * x6 - x5 = 0)
  (h9 : 4 * u1 * x4 * x5 - 1 = 0)
  (h10 : -u3 + u4 = 0)
  :
  -- Conclusion: DB || A1C1
  x9 * x14 + (x10 - x4) * x11 = 0
  := by
    grind
