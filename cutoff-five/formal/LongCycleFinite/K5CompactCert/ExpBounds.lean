import LongCycleFinite.K5CompactCert.Checks
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Real exponential bounds used by the rational compact cells -/

namespace LongCycleFinite.K5CompactCert

private theorem foldl_add_as_sum {α : Type*} [AddMonoid α] (f : ℕ → α) (l : List ℕ)
    (a : α) : l.foldl (fun acc i ↦ acc + f i) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, add_assoc]

private theorem list_range_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/-- Casting the executable Taylor sum into the real exponential series. -/
theorem cast_expTaylor (q : ℚ) (n : ℕ) :
    (expTaylor q n : ℝ) = ∑ i ∈ Finset.range (n + 1), (q : ℝ) ^ i / (i.factorial : ℝ) := by
  simp only [expTaylor, foldl_add_as_sum, zero_add, list_range_sum]
  change (Rat.castHom ℝ) (∑ i ∈ Finset.range (n + 1), q ^ i / (i.factorial : ℚ)) = _
  simp [map_sum]

/-- A nonnegative argument makes every term of the exponential series nonnegative. -/
theorem expTaylor_le_exp {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    (expTaylor q n : ℝ) ≤ Real.exp q := by
  rw [cast_expTaylor]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hq) _

private theorem exp_le_taylor_geometric {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 4) :
    Real.exp y ≤ (∑ i ∈ Finset.range 13, y ^ i / (i.factorial : ℝ)) +
      y ^ 13 / (Nat.factorial 13 : ℝ) / (1 - y / 14) := by
  have he := Real.exp_bound' h0 (h1.trans (by norm_num)) (n := 15) (by decide)
  rw [Finset.sum_range_succ _ 14, Finset.sum_range_succ _ 13] at he
  have ht : y ^ 15 * (15 + 1 : ℝ) / ((Nat.factorial 15 : ℝ) * 15) ≤
      y ^ 13 / (Nat.factorial 13 : ℝ) * (y / 14) ^ 2 := by
    norm_num [Nat.factorial]
    ring_nf
    nlinarith only [pow_nonneg h0 15]
  let r : ℝ := y / 14
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : 0 < 1 - r := by dsimp [r]; linarith
  have hgeom : 1 + r + r ^ 2 ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ hr1).2
    nlinarith only [pow_nonneg hr 3]
  have hstep : y ^ 14 / (Nat.factorial 14 : ℝ) =
      y ^ 13 / (Nat.factorial 13 : ℝ) * r := by
    dsimp [r]
    norm_num [Nat.factorial]
    ring
  calc
    Real.exp y ≤ (∑ i ∈ Finset.range 13, y ^ i / (i.factorial : ℝ)) +
        y ^ 13 / (Nat.factorial 13 : ℝ) * (1 + r + r ^ 2) := by
      rw [hstep] at he
      change y ^ 15 * (15 + 1 : ℝ) / ((Nat.factorial 15 : ℝ) * 15) ≤
        y ^ 13 / (Nat.factorial 13 : ℝ) * r ^ 2 at ht
      linarith only [he, ht]
    _ ≤ _ := by
      rw [div_eq_mul_one_div (y ^ 13 / (Nat.factorial 13 : ℝ))]
      have hm : 0 ≤ y ^ 13 / (Nat.factorial 13 : ℝ) := by positivity
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hgeom hm)

/-- The precise rational upper bound used at the reduced arguments. -/
theorem exp_le_expTaylorUpper {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 4) :
    Real.exp q ≤ (expTaylorUpper q : ℝ) := by
  have h1' : (q : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr h1
  simpa [expTaylorUpper, cast_expTaylor] using
    (exp_le_taylor_geometric (y := q) (by exact_mod_cast h0) (by simpa using h1'))

/-- Rounding in the arithmetic checker is always upwards. -/
theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  unfold roundUp
  apply (le_div_iff₀ (by decide +kernel : 0 < den)).2
  exact Rat.le_ceil

private theorem pow_le_roundedSquares (q : ℚ) (z : ℝ) (hz : 0 ≤ z) (hle : z ≤ (q : ℝ))
    (steps : ℕ) :
    z ^ (2 ^ steps : ℕ) ≤
      ((Nat.rec q (fun _ bound ↦ roundUp (bound ^ 2)) steps : ℚ) : ℝ) := by
  induction steps with
  | zero => simpa using hle
  | succ steps ih =>
    let w : ℚ := Nat.rec q (fun _ bound ↦ roundUp (bound ^ 2)) steps
    change z ^ (2 ^ (steps + 1) : ℕ) ≤ (roundUp (w ^ 2) : ℝ)
    have ih' : z ^ (2 ^ steps : ℕ) ≤ Rat.castHom ℝ w := by
      simpa only [Rat.coe_castHom, w] using ih
    calc
      z ^ (2 ^ (steps + 1) : ℕ) = (z ^ (2 ^ steps : ℕ)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (Rat.castHom ℝ w) ^ 2 := pow_le_pow_left₀ (pow_nonneg hz _) ih' 2
      _ ≤ (roundUp (w ^ 2) : ℝ) := by
        rw [← map_pow]
        exact Rat.cast_le.mpr (le_roundUp _)

/-- The rounded exponential remains an upper bound after scaling and repeated squaring. -/
theorem exp_le_expUpper {q : ℚ} (h0 : 0 ≤ q) {halves : ℕ}
    (hsmall : smallArgument q halves ≤ 1 / 4) :
    Real.exp q ≤ (expUpper q halves : ℝ) := by
  let y := smallArgument q halves
  have hy : 0 ≤ y := by
    change 0 ≤ q / 2 ^ halves
    positivity
  have hscale : ((2 ^ halves : ℕ) : ℝ) * (y : ℝ) = (q : ℝ) := by
    simp [y, smallArgument, mul_div_cancel₀]
  have hbound := (exp_le_expTaylorUpper hy hsmall).trans
    (Rat.cast_le.mpr (le_roundUp (expTaylorUpper y)))
  rw [← hscale, Real.exp_nat_mul]
  exact pow_le_roundedSquares _ _ (Real.exp_nonneg _) hbound halves

namespace Cell

/-- The rational endpoints of a valid cell enclose the actual value of exp(-x). -/
theorem r_bounds {c : Cell} (hv : c.Valid) {x : ℝ} (ha : (c.a : ℝ) ≤ x)
    (hb : x ≤ (c.b : ℝ)) :
    (c.rLo : ℝ) ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ (c.rHi : ℝ) := by
  obtain ⟨_, ha', hb', hrLo, hr, _⟩ := hv.1
  obtain ⟨hsmall, hlo, hhi, _⟩ := hv.2.1
  have ha0 : 0 ≤ c.a := by rw [ha']; positivity
  have hb0 : 0 ≤ c.b := by rw [hb']; positivity
  have rlo0 : 0 ≤ (c.rLo : ℝ) := by exact_mod_cast hrLo.le
  have rhi0 : 0 ≤ (c.rHi : ℝ) := by exact_mod_cast hrLo.le.trans hr
  rw [Real.exp_neg, ← one_div]
  constructor
  · apply (le_div_iff₀ (Real.exp_pos x)).2
    calc
      (c.rLo : ℝ) * Real.exp x ≤ (c.rLo : ℝ) * (expUpper c.b c.rightHalves : ℝ) :=
        mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hb).trans (exp_le_expUpper hb0 hsmall)) rlo0
      _ ≤ 1 := by simpa using (Rat.cast_le (K := ℝ)).mpr hlo
  · apply (div_le_iff₀ (Real.exp_pos x)).2
    calc
      1 ≤ (c.rHi : ℝ) * (expTaylor c.a 64 : ℝ) :=
        by simpa using (Rat.cast_le (K := ℝ)).mpr hhi
      _ ≤ (c.rHi : ℝ) * Real.exp x :=
        mul_le_mul_of_nonneg_left ((expTaylor_le_exp ha0 64).trans (Real.exp_le_exp.mpr ha)) rhi0

/-- The verified exponential bounds for the cost and loss of a valid cell. -/
theorem exponent_bounds {c : Cell} (hv : c.Valid) :
    Real.exp (c.cost : ℝ) ≤ (c.expCost : ℝ) ∧ Real.exp (c.loss : ℝ) ≤ (c.invD : ℝ) := by
  obtain ⟨_, _, _, hLoss0, _, hLossSmall, hLoss, hCost0, _, hCostSmall, hCost⟩ := hv.2.1
  exact ⟨(exp_le_expUpper hCost0 hCostSmall).trans (Rat.cast_le.mpr hCost),
    (exp_le_expUpper hLoss0 hLossSmall).trans (Rat.cast_le.mpr hLoss)⟩

end Cell

end LongCycleFinite.K5CompactCert
