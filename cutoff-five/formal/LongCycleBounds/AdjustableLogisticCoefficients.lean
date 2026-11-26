import LongCycleBounds.AdjustableLogisticConstant

/-! Positive-order Taylor coefficients after removing the nearest pair of odd poles.
The conjugate-pair expansion follows FixedCutoffCompactLogistic, now with a
variable radius up to the first omitted pole. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius

open Real PowerSeries MarkedTwo PoleBridge ComplexConjugate

private theorem logistic_pos_coeff (x : ℝ) (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    ((coeff j (logistic (-exp (-x))) : ℝ) : ℂ) = oddPoleSum (j + 1) x := by
  have eq := eulerian_eq_oddPoleSum j hj x hx
  simp only [logistic, coeff_mk, logisticMoment, if_neg (by omega : j ≠ 0), sub_neg_eq_add]
  push_cast
  apply (div_eq_iff (by exact_mod_cast j.factorial_ne_zero)).2
  simpa [mul_comm] using eq

private theorem conjugate_odd_den (x : ℝ) (i : ℕ) :
    den x (2 * ((-(i + 1 : ℤ) : ℤ) : ℝ) + 1) = conj (den x (2 * (i : ℝ) + 1)) := by
  apply Complex.ext <;> simp [den, Complex.add_re, Complex.add_im]
  ring

private theorem radius_pole_sum (x : ℝ) (q : ℕ) (R : ℝ)
    (sf : Summable (fun i : ℕ ↦ ((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q)) :
    ((R : ℂ) ^ q * oddPoleSum q x).re =
      2 * (∑' i : ℕ, ((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q).re := by
  let F (i : ℤ) := ((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q
  have same (i : ℕ) : F (-(i + 1 : ℤ)) = conj (F i) := by
    simp only [F, conjugate_odd_den, map_pow, map_div₀, Complex.conj_ofReal, Int.cast_natCast]
  have sn : Summable (fun i : ℕ ↦ F (-(i + 1 : ℤ))) := by
    simp only [same]
    exact Complex.summable_conj.mpr sf
  have both := Summable.of_nat_of_neg_add_one (show Summable (fun i : ℕ ↦ F i) from sf) sn
  have identity : (R : ℂ) ^ q * oddPoleSum q x = ∑' i : ℤ, F i := by
    unfold oddPoleSum
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    unfold F den
    push_cast
    rw [div_pow]
    ring
  rw [identity, ← tsum_nat_add_neg_add_one both]
  simp only [same]
  change (∑' i : ℕ, (((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q +
    conj (((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q))).re = _
  rw [Summable.tsum_add sf (Complex.summable_conj.mpr sf), ← Complex.conj_tsum]
  simp only [Complex.add_re, Complex.conj_re]
  ring

/-- At every positive order the Taylor remainder is bounded by the omitted pole mass. -/
theorem logistic_positive {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) (hr : R ≤ ‖den x 3‖)
    (j : ℕ) (hj : 1 ≤ j) : |scaledCoeff (compactLogisticTail x) R j| ≤ R^2/(2*π^2) := by
  let q := j + 1
  let t := -exp (-x)
  let f (i : ℕ) := ((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q
  let F (i : ℕ) := ((R : ℂ) / den x (2 * (i : ℝ) + 3)) ^ q
  obtain ⟨converges, bound⟩ := omitted_summable_and_mass x R hR hr q (by dsimp [q]; omega)
  have sf : Summable (fun i ↦ ‖F i‖) := by simpa only [F, norm_pow] using converges
  have eq (i : ℕ) : f (i + 1) = F i := by
    unfold f F
    push_cast
    ring_nf
  have full : Summable f := (summable_nat_add_iff (f := f) 1).1
    (sf.of_norm.congr fun i ↦ (eq i).symm)
  have sum := radius_pole_sum x q R full
  change ((R : ℂ) ^ q * oddPoleSum q x).re = 2 * (∑' i, f i).re at sum
  rw [full.tsum_eq_zero_add] at sum
  simp only [eq, Complex.add_re] at sum
  have a : R ^ q * coeff j (logistic t) = ((R : ℂ) ^ q * oddPoleSum q x).re := by
    rw [← logistic_pos_coeff x hx (by omega : 1 ≤ j)]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have b : R ^ q * coeff j (nearestLogistic x) = 2 * (f 0).re := by
    simp only [nearestLogistic, coeff_mk, f, Nat.cast_zero, mul_zero, zero_add, q]
    change R ^ (j + 1) * (2 * ((nearestPole x)⁻¹ ^ (j + 1)).re) = _
    rw [show den x 1 = nearestPole x from rfl, div_eq_mul_inv, mul_pow]
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  unfold scaledCoeff compactLogisticTail
  rw [map_sub, mul_sub]
  change |R ^ q * coeff j (logistic t) - R ^ q * coeff j (nearestLogistic x)| ≤ _
  rw [a, b, sum, show ∀ u v : ℝ, 2 * (u + v) - 2 * u = 2 * v by intros; ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := (Complex.abs_re_le_norm (∑' i, F i)).trans (norm_tsum_le_tsum_norm sf)
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans
  simpa only [F, norm_pow] using bound

/-- The order-zero endpoint and the absolutely convergent higher coefficients
have different bounds. Both are valid on the closed interval of radii. -/
theorem logistic_coefficient {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) (hr : R ≤ ‖den x 3‖)
    (j : ℕ) :
    |scaledCoeff (compactLogisticTail x) R j| ≤ if j = 0 then R else R^2/(2*π^2) := by
  cases j with
  | zero => simpa using logistic_constant hx hR
  | succ j => simpa using logistic_positive hx hR hr (j+1) (by omega)

#print axioms logistic_positive
#print axioms logistic_coefficient
end LongCycleBounds.AdjustablePoleRadius
