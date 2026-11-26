import LongCycleFinite.K5CompactCert.Checks

/-! # Exact endpoint constants for the cutoff-five middle region -/

namespace LongCycleFinite.K5MiddleCert

open K5CompactCert

/-- The rounded bound for the ratio of the pole radius to x, at x ≥ 11. -/
def alpha : ℚ := 2599961 / 2500000

/-- The rounded upper bound on the exponential at −11. -/
def r0 : ℚ := 21 / 1250000

/-- The majorant of the four exponential tilt coefficients at radius at least 11. -/
def C : ℚ := 1 / 11 ^ 3 + 1 / (2 * 11 ^ 2) + 1 / (6 * 11) + 1 / 24

def vFormula : ℚ := C * alpha ^ 4 * 11 ^ 4 * r0

/-- Upper bound for the tilt cost at the physical radius. -/
def v0 : ℚ := roundUp vFormula

def headFormula : ℚ :=
  C * r0 * (2 * alpha ^ 5 * 11 ^ 5 + 2 * alpha ^ 7 * 11 ^ 7 / (46 * piLo ^ 2)) /
    (piLo * (1 - v0))

/-- Rounded head budget after division by the sine. -/
def head : ℚ := roundUp headFormula

def tailAt (n : ℕ) : ℚ := 14 * n / 2 ^ ((n - 5) / 2)

/-- Rounded tail budget, with both starting parities. -/
def tail : ℚ := roundUp (max (tailAt 49) (tailAt 50))

def driftFormula : ℚ := C * r0 * alpha ^ 6 * 11 ^ 6 / piLo

/-- Rounded insertion drift after division by the sine. -/
def J : ℚ := roundUp driftFormula

theorem endpoint_arithmetic :
    0 < alpha ∧ 1 + (piHi / 11) ^ 2 ≤ alpha ^ 2 ∧
      0 < r0 ∧ 1 ≤ r0 * expTaylor 11 64 := by decide +kernel

theorem rounded_values :
    C = 657 / 10648 ∧ v0 = 1387 / 78125 ∧ head = 423943 / 2500000 ∧
      tail = 1669 / 10000000 ∧ J = 7395613 / 10000000 := by decide +kernel

theorem main_arithmetic :
    0 < v0 ∧ v0 < 8877 / 500000 ∧ head < 17 / 100 ∧ head + tail < 1 / 4 ∧
      0 < J ∧ J < 1 := by decide +kernel

theorem exponential_arithmetic :
    smallArgument (16 * v0) 1 ≤ 1 / 4 ∧
      expUpper (16 * v0) 1 = 1660637 / 1250000 ∧ expUpper (16 * v0) 1 < 2 := by
  decide +kernel

theorem reserve_arithmetic :
    18 * alpha ^ 3 / piLo < 7 ∧ 2 + (49 / 45 : ℚ) + 1 / 4 < 4 ∧ 4 * J / 49 < 1 / 2 := by
  decide +kernel

end LongCycleFinite.K5MiddleCert
