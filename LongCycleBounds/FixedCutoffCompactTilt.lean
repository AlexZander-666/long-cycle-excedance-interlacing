import LongCycleBounds.FixedCutoffSignedTilt
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Evaluation and geometric truncation of signed finite-degree exponential tilts. -/

noncomputable section

namespace LongCycleBounds.FixedCutoff

open MarkedTwo Real PowerSeries Finset

/-- Evaluate a single Taylor monomial at a complex argument. -/
def weightedCoeff (P : PowerSeries ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  ((coeff j P : ℝ) : ℂ) * z ^ j

/-- The entire function whose Taylor coefficients are the formal tilt. -/
def tiltValue (b : ℕ → ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (∑ i ∈ range d, (b (i + 1) : ℂ) * z ^ (i + 1))

private theorem factor_weighted_at {a : ℕ} (ha : 0 < a) (b : ℝ) (z : ℂ) (n : ℕ) :
    weightedCoeff (factor a ha b) z (a * n) = ((b : ℂ) * z ^ a) ^ n / n.factorial := by
  simp only [weightedCoeff, factor, coeff_expand, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ ha, linearExp, coeff_mk]
  push_cast
  rw [mul_pow, ← pow_mul]
  ring

private theorem factor_weighted_off {a j : ℕ} (ha : 0 < a) (b : ℝ) (z : ℂ)
    (hj : j ∉ Set.range (fun n : ℕ ↦ a * n)) :
    weightedCoeff (factor a ha b) z j = 0 := by
  have ndvd : ¬a ∣ j := fun ⟨i, hi⟩ ↦ hj ⟨i, hi.symm⟩
  simp [weightedCoeff, factor, coeff_expand, ndvd]

private theorem factor_weighted_sum {a : ℕ} (ha : 0 < a) (b : ℝ) (z : ℂ) :
    HasSum (weightedCoeff (factor a ha b) z) (Complex.exp ((b : ℂ) * z ^ a)) := by
  have inj : Function.Injective (fun n : ℕ ↦ a * n) := fun _ _ h ↦
    Nat.eq_of_mul_eq_mul_left ha h
  apply (inj.hasSum_iff (f := weightedCoeff (factor a ha b) z) ?_).mp
  · rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp _).congr_fun
      (fun n ↦ factor_weighted_at ha b z n)
  · exact fun j hj ↦ factor_weighted_off ha b z hj

private theorem factor_weighted_summable {a : ℕ} (ha : 0 < a) (b : ℝ) (z : ℂ) :
    Summable (fun j ↦ ‖weightedCoeff (factor a ha b) z j‖) := by
  let f (j : ℕ) := ‖weightedCoeff (factor a ha b) z j‖
  let e (n : ℕ) := a * n
  have inj : Function.Injective e := fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left ha h
  have hs : Summable (f ∘ e) := (NormedSpace.norm_expSeries_div_summable ((b : ℂ) * z ^ a)).congr
    (fun n ↦ (congrArg norm (factor_weighted_at ha b z n)).symm)
  apply ((inj.hasSum_iff (f := f) ?_).mp hs.hasSum).summable
  intro j hj
  simp only [f, factor_weighted_off ha b z hj, norm_zero]

private theorem weightedCoeff_mul (P Q : PowerSeries ℝ) (z : ℂ) (j : ℕ) :
    weightedCoeff (P * Q) z j =
      ∑ i ∈ range (j + 1), weightedCoeff P z i * weightedCoeff Q z (j - i) := by
  unfold weightedCoeff
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Complex.ofReal_sum, sum_mul]
  apply sum_congr rfl
  intro i hi
  have h : i + (j - i) = j := by have := mem_range.mp hi; omega
  rw [Complex.ofReal_mul, ← h, pow_add, h]
  ring

/-- A uniform coefficient envelope is multiplied by at most the exponential cost. -/
theorem tilted_bound (b : ℕ → ℝ) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (P : PowerSeries ℝ) (d j : ℕ) (h : ∀ i ≤ j, |scaledCoeff P R i| ≤ M) :
    |scaledCoeff (tilt b d * P) R j| ≤ M * exp (cost b R d) := by
  have e := signed_tilt_bias b hR hM P d j h
  have tri := abs_sub_le (scaledCoeff (tilt b d * P) R j) (scaledCoeff P R j) 0
  simp only [sub_zero] at tri
  linarith only [tri, e, h j le_rfl]

private theorem tilt_coeff_bound (b : ℕ → ℝ) (d i : ℕ) {R : ℝ} (hR : 0 < R) :
    |coeff i (tilt b d)| * R ^ i ≤ exp (cost b R d) := by
  have h : ∀ j ≤ i, |scaledCoeff (1 : PowerSeries ℝ) R j| ≤ R := by
    intro j _
    by_cases hj : j = 0 <;> simp [scaledCoeff, coeff_one, hj, abs_of_pos hR, hR.le]
  have e := tilted_bound b hR.le hR.le (1 : PowerSeries ℝ) d i h
  rw [mul_one, scaledCoeff, abs_mul, abs_of_pos (pow_pos hR _), pow_succ] at e
  apply le_of_mul_le_mul_left _ hR
  linarith only [e]

private theorem weighted_norm_bound (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ} (hR : 0 < R)
    (i : ℕ) :
    ‖weightedCoeff (tilt b d) z i‖ ≤ exp (cost b R d) * (‖z‖ / R) ^ i := by
  rw [weightedCoeff, norm_mul, Complex.norm_real, norm_pow]
  have e : ‖z‖ ^ i = R ^ i * (‖z‖ / R) ^ i := by rw [← mul_pow, mul_comm R, div_mul_cancel₀ _ hR.ne']
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (tilt_coeff_bound b d i hR) (by positivity)

private theorem tilt_weighted_summable (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ < R) : Summable (fun i ↦ ‖weightedCoeff (tilt b d) z i‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (weighted_norm_bound b d z hR)
    ((summable_geometric_of_lt_one (by positivity) ((div_lt_one₀ hR).mpr hz)).mul_left _)

private theorem tilt_weighted_sum (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ < R) : HasSum (weightedCoeff (tilt b d) z) (tiltValue b d z) := by
  induction d with
  | zero =>
    have eq : weightedCoeff (tilt b 0) z = fun j : ℕ ↦ if j = 0 then 1 else 0 := by
      funext j
      by_cases hj : j = 0 <;> simp [weightedCoeff, tilt, coeff_one, hj]
    rw [eq]
    simpa [tiltValue] using (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  | succ d ih =>
    have sa := factor_weighted_summable (show 0 < d + 1 by omega) (b (d + 1)) z
    have sb := tilt_weighted_summable b d z hR hz
    have conv := hasSum_sum_range_mul_of_summable_norm sa sb
    rw [(factor_weighted_sum (show 0 < d + 1 by omega) (b (d + 1)) z).tsum_eq, ih.tsum_eq] at conv
    have hv : Complex.exp ((b (d + 1) : ℂ) * z ^ (d + 1)) * tiltValue b d z =
        tiltValue b (d + 1) z := by rw [tiltValue, tiltValue, sum_range_succ, Complex.exp_add, mul_comm]
    rw [hv] at conv
    exact conv.congr_fun (fun j ↦ by rw [tilt, weightedCoeff_mul])

/-- The evaluation of the compact tilt truncation has a geometric tail bound. -/
theorem tilt_truncation (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ < R) (j : ℕ) :
    ‖(∑ i ∈ range (j + 1), weightedCoeff (tilt b d) z i) - tiltValue b d z‖ ≤
      exp (cost b R d) * (‖z‖ / R) ^ (j + 1) / (1 - ‖z‖ / R) := by
  let q := ‖z‖ / R
  let A := exp (cost b R d)
  let f := weightedCoeff (tilt b d) z
  let F (i : ℕ) := f (i + (j + 1))
  have q0 : 0 ≤ q := by dsimp [q]; positivity
  have q1 : q < 1 := (div_lt_one₀ hR).mpr hz
  have sb := (summable_geometric_of_lt_one q0 q1).mul_left (A * q ^ (j + 1))
  have key (i : ℕ) : ‖F i‖ ≤ (A * q ^ (j + 1)) * q ^ i := by
    have hi := weighted_norm_bound b d z hR (i + (j + 1))
    change ‖F i‖ ≤ A * q ^ (i + (j + 1)) at hi
    rw [pow_add] at hi
    linarith only [hi]
  have sa : Summable (fun i ↦ ‖F i‖) := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) key sb
  have hs := tilt_weighted_sum b d z hR hz
  have rep := hs.summable.sum_add_tsum_nat_add (j + 1)
  rw [hs.tsum_eq] at rep
  change (∑ i ∈ range (j + 1), f i) + (∑' i, F i) = _ at rep
  rw [← rep, sub_add_cancel_left, norm_neg]
  calc
    _ ≤ ∑' i, ‖F i‖ := norm_tsum_le_tsum_norm sa
    _ ≤ ∑' i, (A * q ^ (j + 1)) * q ^ i := sa.tsum_le_tsum key sb
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one q0 q1, div_eq_mul_inv]

/-- Explicit lower and upper bounds from the absolute logarithmic cost. -/
theorem tilt_value_bounds (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖ ≤ R) :
    exp (-cost b R d) ≤ ‖tiltValue b d z‖ ∧ ‖tiltValue b d z‖ ≤ exp (cost b R d) := by
  let v : ℂ := ∑ i ∈ range d, (b (i + 1) : ℂ) * z ^ (i + 1)
  have bound : |v.re| ≤ cost b R d := by
    apply (Complex.abs_re_le_norm v).trans
    apply (norm_sum_le _ _).trans
    unfold cost
    apply sum_le_sum
    intro i _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (abs_nonneg _)
  change exp (-cost b R d) ≤ ‖Complex.exp v‖ ∧ ‖Complex.exp v‖ ≤ exp (cost b R d)
  rw [Complex.norm_exp]
  exact ⟨exp_le_exp.mpr (abs_le.mp bound).1, exp_le_exp.mpr (abs_le.mp bound).2⟩

#print axioms tilted_bound
#print axioms tilt_truncation
#print axioms tilt_value_bounds

end LongCycleBounds.FixedCutoff
