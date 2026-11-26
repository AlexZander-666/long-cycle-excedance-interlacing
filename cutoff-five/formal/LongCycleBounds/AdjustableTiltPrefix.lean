import LongCycleBounds.AdjustableTiltTerm

/-! The finite Taylor convolution and the absent tail use disjoint indices.
Their combined cost is the maximum of three pointwise constants. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PowerSeries MarkedTwo PoleBridge FixedCutoff QuadraticCutoff Finset

def extendedTerm (P : PowerSeries ℝ) (x R : ℝ) (j i : ℕ) :=
  if i ≤ j then weighted P R i * scaledCoeff (logistic (time x)) R (j-i) else 0

theorem term_error (P : PowerSeries ℝ) {x R : ℝ} (hx : 0 ≤ x) (hr : radius x ≤ R)
    (hthird : R ≤ ‖den x 3‖) (j i : ℕ) :
    |extendedTerm P x R j i - principalTerm P x R j i| ≤
      |weighted P R i| * max R (R^2/(2*π^2)) := by
  have R0 : 0 ≤ R := (radius_pos x).le.trans hr
  by_cases inside : i ≤ j
  · rw [extendedTerm, if_pos inside, principal_inside P x R inside, ← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have diff : scaledCoeff (logistic (time x)) R (j-i) - scaledCoeff (nearestLogistic x) R (j-i) =
        scaledCoeff (compactLogisticTail x) R (j-i) := by
      unfold scaledCoeff compactLogisticTail time
      rw [map_sub, mul_sub]
    rw [diff]
    have h := logistic_coefficient hx R0 hthird (j-i)
    split_ifs at h <;> exact h.trans (by first | exact le_max_left _ _ | exact le_max_right _ _)
  · rw [extendedTerm, if_neg inside, zero_sub, abs_neg]
    have rho : 2 ≤ radius x := by
      apply (sq_le_sq₀ (by norm_num) (radius_pos x).le).mp
      rw [show radius x^2=x^2+π^2 from sq_sqrt (by positivity)]
      nlinarith [pi_gt_three, sq_nonneg (π-3), sq_nonneg x]
    calc
      _ ≤ 2 * |weighted P R i| := principal_outside P x hr (by omega)
      _ = |weighted P R i| * 2 := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ((rho.trans hr).trans (le_max_left _ _)) (abs_nonneg _)

theorem prefix_error (b : ℕ → ℝ) (d : ℕ) {x R : ℝ} (hx : 0 ≤ x) (hr : radius x ≤ R)
    (hthird : R ≤ ‖den x 3‖) {j n : ℕ} (hn : j ≤ n) :
    |scaledCoeff (tilt b d * logistic (time x)) R j -
        2 * (((R : ℂ) / nearestPole x)^(j+1) *
          ∑ i ∈ range (n+1), weightedCoeff (tilt b d) (nearestPole x) i).re| ≤
        max R (R^2/(2*π^2)) * exp (cost b R d) := by
  let P := tilt b d
  let M := max R (R^2/(2*π^2))
  have Rp : 0 < R := (radius_pos x).trans_le hr
  have m0 : 0 ≤ M := Rp.le.trans (le_max_left _ _)
  have row : scaledCoeff (P * logistic (time x)) R j =
      ∑ i ∈ range (n+1), extendedTerm P x R j i := by
    rw [scaled_convolution]
    calc
      _ = ∑ i ∈ range (j+1), extendedTerm P x R j i := by
        apply sum_congr rfl
        intro i hi
        simp [extendedTerm, show i ≤ j by have := mem_range.mp hi; omega]
      _ = _ := by
        apply sum_subset (range_mono (by omega))
        intro i _ hi
        simp only [mem_range, not_lt] at hi
        simp [extendedTerm, show ¬ i ≤ j by omega]
  change |scaledCoeff (P * _) R j - _| ≤ M * _
  rw [row, mul_sum, Complex.re_sum, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ range (n+1), |extendedTerm P x R j i - principalTerm P x R j i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (n+1), |weighted P R i| * M :=
      sum_le_sum fun i _ ↦ term_error P hx hr hthird j i
    _ ≤ _ := by
      rw [← sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (tilt_prefix_mass b d n Rp) m0

#print axioms term_error
#print axioms prefix_error
end LongCycleBounds.AdjustablePoleRadius
