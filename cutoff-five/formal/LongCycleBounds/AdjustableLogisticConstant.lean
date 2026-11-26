import LongCycleBounds.AdjustablePoleRadius

/-! The separate order-zero estimate used at the finite convolution endpoint. -/

noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PowerSeries MarkedTwo PoleBridge

theorem logistic_constant {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    |scaledCoeff (compactLogisticTail x) R 0| ≤ R := by
  let t := -exp (-x)
  have ht : t ≤ 0 := neg_nonpos.mpr (exp_pos _).le
  have a : 0 ≤ 1/(1-t) ∧ 1/(1-t) ≤ 1 :=
    ⟨by positivity [show 0 < 1-t by linarith],
      (div_le_one₀ (by linarith : 0 < 1-t)).mpr (by linarith)⟩
  have rho : 2 ≤ radius x := by
    apply (sq_le_sq₀ (by norm_num) (radius_pos x).le).mp
    rw [show radius x ^ 2 = x^2+π^2 from sq_sqrt (by positivity)]
    nlinarith [pi_gt_three, sq_nonneg (π-3), sq_nonneg x]
  have b : |((nearestPole x)⁻¹).re| ≤ 1/2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_inv, nearestPole_norm, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) rho
  have hnonneg : 0 ≤ ((nearestPole x)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg (by simpa [nearestPole, den, Complex.add_re] using hx) (Complex.normSq_nonneg _)
  have diff : |1/(1-t)-2*((nearestPole x)⁻¹).re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self ((nearestPole x)⁻¹).re, a.1, a.2]
  simp only [scaledCoeff, compactLogisticTail, map_sub, logistic, nearestLogistic, coeff_mk,
    logisticMoment, if_true, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one]
  change |R*(1/(1-t)-2*((nearestPole x)⁻¹).re)| ≤ R
  rw [abs_mul, abs_of_nonneg hR]
  exact mul_le_of_le_one_right hR diff

#print axioms logistic_constant
end LongCycleBounds.AdjustablePoleRadius
