import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Factorial.Basic

/-! # Rational checks for the compact region at cutoff five

The checks quantify over cell data. The real analytic use of the Taylor and interval quantities
is a separate step. In particular none of the definitions below refers to a real root.
-/

namespace LongCycleFinite.K5CompactCert

def piLo : ℚ := 314159 / 100000
def piHi : ℚ := 314160 / 100000

/-- The common rounding precision of the printed rational bounds. -/
def den : ℚ := 10000000

def roundUp (x : ℚ) : ℚ := (Rat.ceil (x * den) : ℚ) / den

/-- The sum of the exponential series from order zero through the given degree. -/
def expTaylor (x : ℚ) (degree : ℕ) : ℚ :=
  (List.range (degree + 1)).foldl
    (fun acc i ↦ acc + x ^ i / (Nat.factorial i : ℚ)) 0

/-- The small-argument Taylor sum with a geometric upper bound for its tail. -/
def expTaylorUpper (x : ℚ) : ℚ :=
  expTaylor x 12 + x ^ 13 / (Nat.factorial 13 : ℚ) / (1 - x / 14)

def smallArgument (x : ℚ) (halves : ℕ) : ℚ := x / 2 ^ halves

/-- Repeated upward-rounded squaring after reducing the argument by a power of two. -/
def expUpper (x : ℚ) (halves : ℕ) : ℚ :=
  Nat.rec (roundUp (expTaylorUpper (smallArgument x halves)))
    (fun _ bound ↦ roundUp (bound ^ 2)) halves

/-- All values taken from a single rational cell. The residue bound uses order 44 and the
combined budget uses denominator 49. -/
structure Cell where
  index : ℕ
  a : ℚ
  b : ℚ
  rLo : ℚ
  rHi : ℚ
  rho : ℚ
  lambda : ℚ
  rightHalves : ℕ
  lossHalves : ℕ
  costHalves : ℕ
  loss : ℚ
  cost : ℚ
  invD : ℚ
  expCost : ℚ
  error44 : ℚ
  drift : ℚ
  phase49 : ℚ

namespace Cell

def hLo (c : Cell) : ℚ := c.rLo / (1 + c.rLo) ^ 2
def hHi (c : Cell) : ℚ := c.rHi / (1 + c.rHi) ^ 2
def vHi (c : Cell) : ℚ := (1 - c.rLo) / (1 + c.rLo)

def m2 (c : Cell) : ℚ := roundUp c.hHi
def m3 (c : Cell) : ℚ := roundUp (c.hHi * c.vHi)
def m4 (c : Cell) : ℚ :=
  roundUp (c.hHi * max |1 - 6 * c.hLo| |1 - 6 * c.hHi|)
def m5 (c : Cell) : ℚ :=
  roundUp (c.hHi * c.vHi * max |1 - 12 * c.hLo| |1 - 12 * c.hHi|)

def b1 (c : Cell) : ℚ := roundUp (c.rHi / (1 + c.rHi))
def b2 (c : Cell) : ℚ := roundUp (c.m2 / 2)
def b3 (c : Cell) : ℚ := roundUp (c.m3 / 6)
def b4 (c : Cell) : ℚ := roundUp (c.m4 / 24)

def re2Lo (c : Cell) : ℚ := c.a ^ 2 - piHi ^ 2
def re3Lo (c : Cell) : ℚ := c.a ^ 3 - 3 * piHi ^ 2 * c.b
def re4Lo (c : Cell) : ℚ := c.a ^ 4 - 6 * piHi ^ 2 * c.b ^ 2 + piLo ^ 4
def re4Hi (c : Cell) : ℚ := c.b ^ 4 - 6 * piLo ^ 2 * c.a ^ 2 + piHi ^ 4

def fourthLoss (c : Cell) : ℚ :=
  if 1 ≤ 6 * c.hLo then max 0 c.re4Hi
  else if 6 * c.hHi ≤ 1 then max 0 (-c.re4Lo)
  else max |c.re4Lo| |c.re4Hi|

def computedLoss (c : Cell) : ℚ :=
  max 0 (-c.re2Lo) * c.b2 + max 0 (-c.re3Lo) * c.b3 + c.fourthLoss * c.b4

def radius (c : Cell) : ℚ := c.rho * c.lambda

def computedCost (c : Cell) : ℚ :=
  c.b1 * c.radius + c.b2 * c.radius ^ 2 + c.b3 * c.radius ^ 3 + c.b4 * c.radius ^ 4

def residueFactor (c : Cell) : ℚ := max c.rho (c.lambda * c.rho ^ 2 / (2 * piLo ^ 2))
def reciprocalS (c : Cell) : ℚ := roundUp (c.rho / piLo)

def computedDrift (c : Cell) : ℚ :=
  (c.m2 * c.rho ^ 3 + c.m3 * c.rho ^ 4 / 2 + c.m4 * c.rho ^ 5 / 6 +
    c.m5 * c.rho ^ 6 / 24) / piLo

/-- Data for the closed eighth-grid interval, with a positive radius and admissible multiplier. -/
def Geometry (c : Cell) : Prop :=
  c.index < 88 ∧
  c.a = (c.index : ℚ) / 8 ∧ c.b = ((c.index + 1 : ℕ) : ℚ) / 8 ∧
  0 < c.rLo ∧ c.rLo ≤ c.rHi ∧ c.rHi ≤ 1 ∧
  0 < c.rho ∧ c.b ^ 2 + piHi ^ 2 ≤ c.rho ^ 2 ∧
  1 < c.lambda ∧ c.lambda ≤ 3 ∧
  c.lambda ^ 2 * (c.b ^ 2 + piLo ^ 2) ≤ c.b ^ 2 + 9 * piLo ^ 2 ∧
  21 / 20 ≤ c.lambda ∧ (20 * c.lambda).den = 1

/-- Rational checks for the exponential enclosures and the two tilt exponents. -/
def Enclosures (c : Cell) : Prop :=
  smallArgument c.b c.rightHalves ≤ 1 / 4 ∧
  c.rLo * expUpper c.b c.rightHalves ≤ 1 ∧
  1 ≤ c.rHi * expTaylor c.a 64 ∧
  0 ≤ c.loss ∧ c.computedLoss ≤ c.loss ∧ smallArgument c.loss c.lossHalves ≤ 1 / 4 ∧
  expUpper c.loss c.lossHalves ≤ c.invD ∧
  0 ≤ c.cost ∧ c.computedCost ≤ c.cost ∧ smallArgument c.cost c.costHalves ≤ 1 / 4 ∧
  expUpper c.cost c.costHalves ≤ c.expCost

/-- Arithmetic of the residue, drift and combined budget at the worst orders 44 and 49. -/
def Budgets (c : Cell) : Prop :=
  c.residueFactor * c.expCost * c.invD * c.reciprocalS / c.lambda ^ 44 ≤ c.error44 ∧
  c.computedDrift ≤ c.drift ∧
  (3 * c.error44 + (2 + c.error44) * c.drift / 49) / 2 ≤ c.phase49 ∧
  c.error44 ≤ 949 / 400000 ∧ c.drift ≤ 95990813 / 10000000 ∧ c.phase49 ≤ 391801 / 2000000

/-- The combined rational well-formedness and inequalities, prior to analytic interpretation. -/
def Valid (c : Cell) : Prop := c.Geometry ∧ c.Enclosures ∧ c.Budgets

instance (c : Cell) : Decidable c.Valid := by
  unfold Valid Geometry Enclosures Budgets
  infer_instance

end Cell

end LongCycleFinite.K5CompactCert
