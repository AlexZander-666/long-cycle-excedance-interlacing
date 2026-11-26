import LongCycleBounds.FixedCutoffCompactTilt

/-! Split a nonnegative formal tilt by the order of the remaining coefficient. -/

noncomputable section
namespace LongCycleBounds.FixedFour49
open Real PowerSeries Finset MarkedTwo FixedCutoff

private theorem factor_coeff_zero {a : ℕ} (ha : 0 < a) (b : ℝ) :
    coeff 0 (factor a ha b) = 1 := by
  simp [factor, coeff_expand, linearExp]

private theorem tilt_coeff_zero (b : ℕ → ℝ) (d : ℕ) :
    coeff 0 (tilt b d) = 1 := by
  induction d with
  | zero => simp [tilt]
  | succ d ih =>
    rw [tilt, coeff_zero_eq_constantCoeff, map_mul, ← coeff_zero_eq_constantCoeff,
      factor_coeff_zero, ih, mul_one]

private theorem tilt_coeff_nonneg (b : ℕ → ℝ) (hb : ∀ a, 0 < a → 0 ≤ b a) (d i : ℕ) :
    0 ≤ coeff i (tilt b d) := by
  induction d generalizing i with
  | zero => simp [tilt, coeff_one]; positivity
  | succ d ih =>
    rw [tilt, coeff_mul]
    apply sum_nonneg
    intro pair _
    apply mul_nonneg _ (ih _)
    rw [factor, coeff_expand]
    split_ifs
    · simp only [linearExp, coeff_mk]
      exact div_nonneg (pow_nonneg (hb _ (Nat.succ_pos d)) _) (by positivity)
    · exact le_rfl

private def weight (b : ℕ → ℝ) (d : ℕ) (R : ℝ) (i : ℕ) :=
  coeff i (tilt b d)*R^i

private theorem wt_nonneg (b : ℕ → ℝ) (hb : ∀ a, 0 < a → 0 ≤ b a) (d : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (i : ℕ) : 0 ≤ weight b d R i :=
  mul_nonneg (tilt_coeff_nonneg b hb d i) (pow_nonneg hR i)

private theorem convolution (b : ℕ → ℝ) (d j : ℕ) (R : ℝ) (F : PowerSeries ℝ) :
    scaledCoeff (tilt b d*F) R j =
      ∑ i ∈ range (j+1), weight b d R i * scaledCoeff F R (j-i) := by
  unfold scaledCoeff
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro i hi
  have h : i + (j-i+1) = j+1 := by have := mem_range.mp hi; omega
  dsimp only [weight]
  rw [← h, pow_add]
  ring

private theorem mass_prefix (b : ℕ → ℝ) (d j : ℕ) {R : ℝ} (hR : 0 < R) :
    (∑ i ∈ range (j+1), weight b d R i) ≤ exp (cost b R d) := by
  let F : PowerSeries ℝ := mk fun i ↦ (R^(i+1))⁻¹
  have coeff_eq (i : ℕ) : scaledCoeff F R i = 1 := by
    simp [scaledCoeff, F, (pow_pos hR (i+1)).ne']
  have estimate := tilted_bound b hR.le (show (0:ℝ)≤1 by norm_num) F d j
    (fun i _ ↦ by simp [coeff_eq])
  rw [convolution] at estimate
  simp only [coeff_eq, mul_one, one_mul] at estimate
  exact (le_abs_self _).trans estimate

private theorem mass_positive (b : ℕ → ℝ) (d j : ℕ) {R : ℝ} (hR : 0 < R) :
    (∑ i ∈ range j, weight b d R (i+1)) ≤ exp (cost b R d) - 1 := by
  have estimate := mass_prefix b d j hR
  rw [sum_range_succ'] at estimate
  simp only [weight, tilt_coeff_zero, pow_zero, mul_one] at estimate ⊢
  linarith only [estimate]

private theorem scaled_weight (b : ℕ → ℝ) (d i : ℕ) (R : ℝ) :
    weight b d R i = (1/2:ℝ)^i * weight b d (2*R) i := by
  unfold weight
  have e : (1/2:ℝ)^i * (2*R)^i = R^i := by
    rw [← mul_pow, show (1/2:ℝ)*(2*R)=R by ring]
  rw [← e]
  ring

/-- Bound the effect of a nonnegative tilt using a stronger envelope up to
half of the insertion order and a geometric bound for the remaining terms. -/
theorem split_tilt_bias (b : ℕ → ℝ) (hb : ∀ a, 0<a → 0≤b a) (d j : ℕ)
    {R M L : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (F : PowerSeries ℝ)
    (head : ∀ i ≤ j/2, |scaledCoeff F R (j-i)| ≤ M)
    (all : ∀ i ≤ j, |scaledCoeff F R i| ≤ L) :
    |scaledCoeff (tilt b d*F) R j - scaledCoeff F R j| ≤
      M*(exp (cost b R d)-1) + L*(1/2:ℝ)^(j/2)*exp (cost b (2*R) d) := by
  let r : ℝ := (1/2:ℝ)^(j/2)
  have rp : 0 ≤ r := by dsimp [r]; positivity
  have h2R : 0 < 2*R := by positivity
  have half (i : ℕ) (hi : j/2 < i) :
      weight b d R i ≤ r * weight b d (2*R) i := by
    rw [scaled_weight]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi.le)
      (wt_nonneg b hb d h2R.le i)
  rw [convolution, sum_range_succ']
  simp only [show weight b d R 0 = 1 by simp [weight, tilt_coeff_zero], Nat.sub_zero,
    one_mul, add_sub_cancel_right]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i ∈ range j, (M*weight b d R (i+1) + (L*r)*weight b d (2*R) (i+1)) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (wt_nonneg b hb d hR.le _)]
      by_cases hi : i+1 ≤ j/2
      · have h := mul_le_mul_of_nonneg_left (head (i+1) hi) (wt_nonneg b hb d hR.le (i+1))
        nlinarith only [h, mul_nonneg (mul_nonneg hL rp) (wt_nonneg b hb d h2R.le (i+1))]
      · have left := mul_le_mul_of_nonneg_left (all (j-(i+1)) (Nat.sub_le ..))
          (wt_nonneg b hb d hR.le (i+1))
        have right := mul_le_mul_of_nonneg_right (half (i+1) (by omega)) hL
        nlinarith only [left, right, mul_nonneg hM (wt_nonneg b hb d hR.le (i+1))]
    _ ≤ _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      have a := mul_le_mul_of_nonneg_left (mass_positive b d j hR) hM
      have bnd := mass_prefix b d j h2R
      rw [sum_range_succ'] at bnd
      simp only [show weight b d (2*R) 0 = 1 by simp [weight, tilt_coeff_zero]] at bnd
      have c := mul_le_mul_of_nonneg_left (show _ ≤ _ by linarith only [bnd] :
        (∑ i ∈ range j, weight b d (2*R) (i+1)) ≤ exp (cost b (2*R) d)) (mul_nonneg hL rp)
      exact add_le_add a c

#print axioms split_tilt_bias
end LongCycleBounds.FixedFour49
