import LongCycleBounds.MarkedCompactLogistic
import LongCycleBounds.MarkedInsertion

/-! A larger radius for the logistic coefficients after removal of the first pole pair. -/

noncomputable section

namespace LongCycleBounds.FixedCutoff

open MarkedTwo Real PowerSeries PoleBridge ComplexConjugate

private theorem outer_sq (x : ℝ) : compactRadius x ^ 2 = x ^ 2 + 4 * π ^ 2 :=
  sq_sqrt (by positivity)

private theorem rho_sq (x : ℝ) : radius x ^ 2 = x ^ 2 + π ^ 2 :=
  sq_sqrt (by positivity)

theorem compactRadius_mono {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) :
    compactRadius x ≤ compactRadius X :=
  sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ hx hX 2) le_rfl)

theorem radius_le_compact (x : ℝ) : radius x < compactRadius x := by
  apply (sq_lt_sq₀ (radius_pos x).le (compactRadius_pos x).le).mp
  rw [rho_sq, outer_sq]
  nlinarith [sq_pos_of_pos pi_pos]

theorem compactRadius_ge_one (x : ℝ) : 1 ≤ compactRadius x := by
  apply (sq_le_sq₀ (by norm_num) (compactRadius_pos x).le).mp
  rw [outer_sq]
  nlinarith [pi_gt_three, mul_pos pi_pos (show 0 < π - 3 by linarith [pi_gt_three])]

/-- The geometric error ratio on the compact interval is bounded by its value at \(X\). -/
theorem compact_ratio_bound {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) :
    radius x / compactRadius x ≤ radius X / compactRadius X := by
  apply (div_le_div_iff₀ (compactRadius_pos x) (compactRadius_pos X)).mpr
  apply (sq_le_sq₀ (mul_nonneg (radius_pos x).le (compactRadius_pos X).le)
    (mul_nonneg (radius_pos X).le (compactRadius_pos x).le)).mp
  rw [mul_pow, mul_pow, rho_sq, rho_sq, outer_sq, outer_sq]
  have xx := pow_le_pow_left₀ hx hX 2
  nlinarith only [mul_nonneg (sq_nonneg π) (sub_nonneg.mpr xx)]

private theorem den_sq (x l : ℝ) : ‖den x l‖ ^ 2 = x ^ 2 + (l * π) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [den, Complex.add_re, Complex.add_im]
  ring

private theorem logistic_pos_coeff (x : ℝ) (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    ((coeff j (logistic (-exp (-x))) : ℝ) : ℂ) = oddPoleSum (j + 1) x := by
  have eq := eulerian_eq_oddPoleSum j hj x hx
  simp only [logistic, coeff_mk, logisticMoment, if_neg (by omega : j ≠ 0), sub_neg_eq_add]
  push_cast
  apply (div_eq_iff (by exact_mod_cast j.factorial_ne_zero)).2
  simpa [mul_comm] using eq

private def envelope (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)

private theorem envelope_nonneg (i : ℕ) : 0 ≤ envelope i :=
  sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

private theorem envelope_mass : Summable envelope ∧ ∑' i, envelope i ≤ 1 := by
  have sum (m : ℕ) : (∑ i ∈ Finset.range m, envelope i) = 1 - 1 / ((m : ℝ) + 1) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [envelope, Nat.cast_succ]
      ring
  have fin (m : ℕ) : (∑ i ∈ Finset.range m, envelope i) ≤ 1 := by
    rw [sum]
    exact sub_le_self _ (by positivity)
  exact ⟨summable_of_sum_range_le envelope_nonneg fin,
    Real.tsum_le_of_sum_range_le envelope_nonneg fin⟩

private theorem tail_term {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) {q : ℕ} (hq : 2 ≤ q)
    (i : ℕ) :
    ‖((compactRadius x : ℂ) / den x (2 * (i : ℝ) + 3)) ^ q‖ ≤
      (compactRadius X / π) ^ 2 * envelope i := by
  let R := compactRadius x
  let l : ℝ := 2 * (i : ℝ) + 3
  let D := ‖den x l‖
  have lp : 0 < l := by dsimp [l]; positivity
  have l3 : 3 ≤ l := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have rpos : 0 < R := compactRadius_pos x
  have ds : D ^ 2 = x ^ 2 + (l * π) ^ 2 := den_sq x l
  have rD : R ≤ D := by
    apply (sq_le_sq₀ rpos.le (norm_nonneg _)).mp
    rw [outer_sq, ds]
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * π)
      (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ l by linarith) pi_pos.le) 2
    linarith only [h, show (2 * π) ^ 2 = 4 * π ^ 2 by ring]
  have Dpi : l * π ≤ D := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [ds]
    nlinarith only [sq_nonneg x]
  have dp : 0 < D := rpos.trans_le rD
  have q0 : 0 ≤ R / D := by positivity
  have q1 : R / D ≤ 1 := (div_le_one₀ dp).mpr rD
  have frac : R / D ≤ (compactRadius X / π) / l := by
    calc
      _ ≤ compactRadius X / (l * π) :=
        div_le_div₀ (compactRadius_pos X).le (compactRadius_mono hx hX) (by positivity) Dpi
      _ = _ := by rw [div_div, mul_comm]
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg rpos.le]
  change (R / D) ^ q ≤ _
  calc
    _ ≤ (R / D) ^ 2 := pow_le_pow_of_le_one q0 q1 hq
    _ ≤ ((compactRadius X / π) / l) ^ 2 := pow_le_pow_left₀ q0 frac 2
    _ ≤ _ := by
      rw [div_pow, div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (i : ℝ) + 2 := by positivity
      unfold envelope
      field_simp
      dsimp [l]
      nlinarith only [Nat.cast_nonneg (α := ℝ) i, sq_nonneg (i : ℝ)]

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

/-- The uniform bound includes the actual constant coefficient of the subtracted series. -/
def compactTailBound (X : ℝ) : ℝ :=
  2 * (compactRadius X / π) ^ 2 + 2 * compactRadius X

theorem compact_tail_bound {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) (j : ℕ) :
    |scaledCoeff (compactLogisticTail x) (compactRadius x) j| ≤ compactTailBound X := by
  let R := compactRadius x
  let t := -exp (-x)
  have rp : 0 < R := compactRadius_pos x
  by_cases hj : j = 0
  · subst j
    have tneg : t ≤ 0 := neg_nonpos.mpr (exp_pos _).le
    have l0 : 0 ≤ 1 / (1 - t) ∧ 1 / (1 - t) ≤ 1 :=
      ⟨div_nonneg (by norm_num) (by linarith),
        (div_le_one₀ (by linarith : 0 < 1 - t)).mpr (by linarith)⟩
    have rho2 : 2 ≤ radius x := by
      apply (sq_le_sq₀ (by norm_num) (radius_pos x).le).mp
      rw [rho_sq]
      nlinarith [pi_gt_three, sq_nonneg (π - 3), sq_nonneg x]
    have nr : |((nearestPole x)⁻¹).re| ≤ 1 / 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_inv, nearestPole_norm, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) rho2
    simp only [scaledCoeff, compactLogisticTail, map_sub, logistic, nearestLogistic, coeff_mk,
      logisticMoment, if_true, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one]
    change |R * (1 / (1 - t) - 2 * ((nearestPole x)⁻¹).re)| ≤ _
    rw [abs_mul, abs_of_pos rp]
    have z := abs_sub (1 / (1 - t)) (2 * ((nearestPole x)⁻¹).re)
    rw [abs_of_nonneg l0.1, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at z
    calc
      _ ≤ R * 2 := mul_le_mul_of_nonneg_left (by linarith only [z, l0.2, nr]) rp.le
      _ ≤ compactTailBound X := by
        unfold compactTailBound
        linarith [compactRadius_mono hx hX, sq_nonneg (compactRadius X / π)]
  · let q := j + 1
    let f (i : ℕ) := ((R : ℂ) / den x (2 * (i : ℝ) + 1)) ^ q
    let F (i : ℕ) := ((R : ℂ) / den x (2 * (i : ℝ) + 3)) ^ q
    let M := (compactRadius X / π) ^ 2
    have cmp (i : ℕ) : ‖F i‖ ≤ M * envelope i := tail_term hx hX (by dsimp [q]; omega) i
    have se := envelope_mass.1.mul_left M
    have sf : Summable (fun i ↦ ‖F i‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) cmp se
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
    have mass : ‖∑' i, F i‖ ≤ M := by
      apply (norm_tsum_le_tsum_norm sf).trans ((sf.tsum_le_tsum cmp se).trans ?_)
      rw [tsum_mul_left]
      exact mul_le_of_le_one_right (sq_nonneg _) envelope_mass.2
    have h := (Complex.abs_re_le_norm (∑' i, F i)).trans mass
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    unfold compactTailBound
    linarith only [h, (compactRadius_pos X).le]

#print axioms compact_ratio_bound
#print axioms compact_tail_bound

end LongCycleBounds.FixedCutoff
