import LongCycleBounds.FixedCutoffCompactLogistic
import LongCycleBounds.FixedCutoffCompactTilt

/-! Uniform nearest-pole asymptotics for any fixed degree of the short-cycle tilt. -/

noncomputable section

namespace LongCycleBounds.FixedCutoff

open MarkedTwo Real PowerSeries Finset PoleBridge

private theorem tilted_nearest_coeff (P : PowerSeries ℝ) (x : ℝ) (j : ℕ) :
    scaledCoeff (P * nearestLogistic x) (radius x) j =
      2 * (((radius x : ℂ) / nearestPole x) ^ (j + 1) *
        ∑ i ∈ range (j + 1), weightedCoeff P (nearestPole x) i).re := by
  let z := nearestPole x
  have zn : z ≠ 0 := by
    have nn : 0 < ‖z‖ := by rw [show ‖z‖ = radius x from nearestPole_norm x]; exact radius_pos x
    exact norm_ne_zero_iff.mp nn.ne'
  unfold scaledCoeff
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  rw [mul_sum, Complex.re_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  have idx : i + (j - i + 1) = j + 1 := by have := mem_range.mp hi; omega
  simp only [nearestLogistic, coeff_mk, weightedCoeff]
  change radius x ^ (j + 1) * (coeff i P * (2 * (z⁻¹ ^ (j - i + 1)).re)) =
    2 * (((radius x : ℂ) / z) ^ (j + 1) * (((coeff i P : ℝ) : ℂ) * z ^ i)).re
  have re : ((radius x : ℂ) / z) ^ (j + 1) * (((coeff i P : ℝ) : ℂ) * z ^ i) =
      ((radius x ^ (j + 1) * coeff i P : ℝ) : ℂ) * z⁻¹ ^ (j - i + 1) := by
    rw [div_pow, ← idx, pow_add z, inv_pow]
    push_cast
    field_simp
  rw [re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem scaledCoeff_radius_shift (P : PowerSeries ℝ) {ρ R : ℝ}
    (hR : 0 < R) (j : ℕ) :
    scaledCoeff P ρ j = (ρ / R) ^ (j + 1) * scaledCoeff P R j := by
  unfold scaledCoeff
  rw [← mul_assoc, ← mul_pow, div_mul_cancel₀ _ hR.ne']

private theorem nearest_error_bound (b : ℕ → ℝ) (d j : ℕ) (x : ℝ) :
    |scaledCoeff (tilt b d * nearestLogistic x) (radius x) j -
        2 * (tiltValue b d (nearestPole x) * ((radius x : ℂ) / nearestPole x) ^ (j + 1)).re| ≤
      2 * (exp (cost b (compactRadius x) d) * (radius x / compactRadius x) ^ (j + 1) /
        (1 - radius x / compactRadius x)) := by
  let ρ := radius x
  let R := compactRadius x
  let z := nearestPole x
  let A := ((ρ : ℂ) / z) ^ (j + 1)
  let S := ∑ i ∈ range (j + 1), weightedCoeff (tilt b d) z i
  let B := tiltValue b d z
  have zEq : ‖z‖ = ρ := nearestPole_norm x
  have aNorm : ‖A‖ = 1 := by
    dsimp [A]
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (radius_pos x).le,
      zEq, div_self (radius_pos x).ne', one_pow]
  have err := tilt_truncation b d z (compactRadius_pos x)
    (zEq.symm ▸ radius_le_compact x) j
  rw [zEq] at err
  rw [tilted_nearest_coeff]
  change |2 * (A * S).re - 2 * (B * A).re| ≤ _
  have e : 2 * (A * S).re - 2 * (B * A).re = 2 * (A * (S - B)).re := by
    rw [mul_sub, Complex.sub_re, mul_comm A B]
    ring
  rw [e, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  rw [norm_mul, aNorm, one_mul]
  exact err

/-- Explicit pointwise error after retaining exactly the two nearest conjugate poles. -/
theorem compact_scaled_row_bound {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) (b : ℕ → ℝ)
    (d j : ℕ) :
    let ρ := radius x
    let R := compactRadius x
    let q := ρ / R
    |scaledCoeff (tilt b d * logistic (time x)) ρ j -
        2 * (tiltValue b d (nearestPole x) * ((ρ : ℂ) / nearestPole x) ^ (j + 1)).re| ≤
      (compactTailBound X + 2 / (1 - q)) * exp (cost b R d) * q ^ (j + 1) := by
  dsimp only
  let ρ := radius x
  let R := compactRadius x
  let q := ρ / R
  let P := tilt b d
  let E := P * compactLogisticTail x
  let A := P * nearestLogistic x
  have rpos : 0 < R := compactRadius_pos x
  have q0 : 0 ≤ q := div_nonneg (radius_pos x).le rpos.le
  have env : 0 ≤ compactTailBound X :=
    add_nonneg (by positivity) (mul_nonneg (by norm_num) (compactRadius_pos X).le)
  have eq : P * logistic (time x) = A + E := by
    change P * logistic (time x) = P * nearestLogistic x +
      P * (logistic (time x) - nearestLogistic x)
    rw [mul_sub]
    ring
  have tailR := tilted_bound b rpos.le env (compactLogisticTail x) d j
    (fun i _ ↦ compact_tail_bound hx hX i)
  have tail : |scaledCoeff E ρ j| ≤ compactTailBound X * exp (cost b R d) * q ^ (j + 1) := by
    rw [scaledCoeff_radius_shift E rpos, abs_mul, abs_of_nonneg (pow_nonneg q0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right tailR (pow_nonneg q0 _)
  rw [eq, scaledCoeff, map_add, mul_add]
  change |scaledCoeff A ρ j + scaledCoeff E ρ j -
    2 * (tiltValue b d (nearestPole x) * ((ρ : ℂ) / nearestPole x) ^ (j + 1)).re| ≤ _
  rw [add_comm, add_sub_assoc]
  apply (abs_add_le _ _).trans ((add_le_add tail (nearest_error_bound b d j x)).trans_eq ?_)
  change compactTailBound X * exp (cost b R d) * q ^ (j + 1) +
    2 * (exp (cost b R d) * q ^ (j + 1) / (1 - q)) =
      (compactTailBound X + 2 / (1 - q)) * exp (cost b R d) * q ^ (j + 1)
  ring

private theorem cost_bound {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) (b : ℕ → ℝ) (d : ℕ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i| ≤ 1) :
    cost b (compactRadius x) d ≤ (d : ℝ) * (compactRadius X) ^ d := by
  unfold cost
  calc
    _ ≤ ∑ _i ∈ range d, (compactRadius X) ^ d := by
      apply sum_le_sum
      intro i hi
      have ix := mem_range.mp hi
      have hp := pow_nonneg (compactRadius_pos x).le (i + 1)
      calc
        _ ≤ 1 * (compactRadius x) ^ (i + 1) :=
          mul_le_mul_of_nonneg_right (hb _ (by omega) (by omega)) hp
        _ ≤ (compactRadius X) ^ (i + 1) := by
          rw [one_mul]
          exact pow_le_pow_left₀ (compactRadius_pos x).le (compactRadius_mono hx hX) _
        _ ≤ _ := pow_le_pow_right₀ (compactRadius_ge_one X) (by omega)
    _ = _ := by simp [nsmul_eq_mul]

/-- On a fixed compact interval the error is geometrically small, with a positive uniform
lower bound on the retained complex amplitude. All constants are independent of the marks. -/
theorem compact_scaled_row_uniform (d : ℕ) {X : ℝ} (_hX : 0 ≤ X) :
    ∃ q M m U : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < M ∧ 0 < m ∧ 0 < U ∧
      ∀ {x : ℝ}, 0 ≤ x → x ≤ X → ∀ b : ℕ → ℝ,
        (∀ i, 1 ≤ i → i ≤ d → |b i| ≤ 1) →
        m ≤ ‖tiltValue b d (nearestPole x)‖ ∧ ‖tiltValue b d (nearestPole x)‖ ≤ U ∧
        ∀ j : ℕ, |scaledCoeff (tilt b d * logistic (time x)) (radius x) j -
          2 * (tiltValue b d (nearestPole x) * ((radius x : ℂ) / nearestPole x) ^ (j + 1)).re| ≤
          M * q ^ (j + 1) := by
  let q := radius X / compactRadius X
  let K := (d : ℝ) * (compactRadius X) ^ d
  let G := compactTailBound X + 2 / (1 - q)
  have q0 : 0 ≤ q := div_nonneg (radius_pos X).le (compactRadius_pos X).le
  have q1 : q < 1 := (div_lt_one₀ (compactRadius_pos X)).mpr (radius_le_compact X)
  have G0 : 0 < G := by
    unfold G compactTailBound
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (by positivity) (mul_nonneg (by norm_num) (compactRadius_pos X).le))
      (div_pos (by norm_num) (sub_pos.mpr q1))
  refine ⟨q, G * exp K, exp (-K), exp K, q0, q1, mul_pos G0 (exp_pos _),
    exp_pos _, exp_pos _, ?_⟩
  intro x hx hX b hb
  let r := radius x / compactRadius x
  have r0 : 0 ≤ r := div_nonneg (radius_pos x).le (compactRadius_pos x).le
  have rq : r ≤ q := compact_ratio_bound hx hX
  have co : cost b (compactRadius x) d ≤ K := cost_bound hx hX b d hb
  have near : ‖nearestPole x‖ ≤ compactRadius x :=
    (nearestPole_norm x).trans_le (radius_le_compact x).le
  obtain ⟨low, high⟩ := tilt_value_bounds b d (nearestPole x) near
  refine ⟨(exp_le_exp.mpr (neg_le_neg co)).trans low, high.trans (exp_le_exp.mpr co), ?_⟩
  intro j
  have div : 2 / (1 - r) ≤ 2 / (1 - q) := by
    apply div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr q1)
    linarith only [rq]
  have coeff : (compactTailBound X + 2 / (1 - r)) * exp (cost b (compactRadius x) d) ≤
      G * exp K :=
    mul_le_mul (add_le_add le_rfl div) (exp_le_exp.mpr co) (exp_pos _).le G0.le
  exact (compact_scaled_row_bound hx hX b d j).trans
    (mul_le_mul coeff (pow_le_pow_left₀ r0 rq (j + 1)) (pow_nonneg r0 _)
      (mul_nonneg G0.le (exp_pos _).le))

#print axioms compact_scaled_row_bound
#print axioms compact_scaled_row_uniform

end LongCycleBounds.FixedCutoff
