import LongCycleBounds.FixedCutoffReadout

/-! Exact low-order moments and uniform insertion bounds at fixed cutoff four. -/

noncomputable section

namespace LongCycleBounds.FixedFour

open Real Polynomial LongCycles Finset Band FixedCutoff PoleBridge

private theorem eulerian_two : eulerian 2 = 1 + X := by
  rw [show 2 = 1 + 1 by decide, longEulerian_succ, longEulerian_one]
  simp

private theorem eulerian_three : eulerian 3 = 1 + C (4 : ℝ) * X + X ^ 2 := by
  change eulerian (2 + 1) = _
  rw [longEulerian_succ, eulerian_two]
  simp [C_ofNat]
  ring

/-- The three actual coefficients in the finite exponential tilt. -/
theorem tilt_forms (w : ℕ → ℝ) (w1 : w 1 = 0) (x : ℝ) :
    let r := exp (-x)
    tiltCoefficient w 1 x = r / (1 + r) ∧
    tiltCoefficient w 2 x = (1 - w 2) * r / (2 * (1 + r) ^ 2) ∧
    tiltCoefficient w 3 x = (1 - w 3) * r * (1 - r) / (6 * (1 + r) ^ 3) := by
  dsimp only
  have hd : 1 + exp (-x) ≠ 0 := by positivity
  constructor
  · simp [tiltCoefficient, cycleMoment, moment, w1, longEulerian_zero, neg_div]
  constructor
  · simp [tiltCoefficient, cycleMoment, moment, longEulerian_one]
    field_simp
    ring
  · simp [tiltCoefficient, cycleMoment, moment, eulerian_two]
    field_simp
    ring

/-- Nonnegative cubic tilt with both uniform and exponentially small coefficient bounds. -/
theorem tilt_caps (w : ℕ → ℝ) (w1 : w 1 = 0) (unit : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1)
    {x : ℝ} (hx : 0 ≤ x) :
    let r := exp (-x)
    (0 ≤ tiltCoefficient w 1 x ∧ tiltCoefficient w 1 x ≤ 1 / 2 ∧ tiltCoefficient w 1 x ≤ r) ∧
    (0 ≤ tiltCoefficient w 2 x ∧ tiltCoefficient w 2 x ≤ 1 / 8 ∧ tiltCoefficient w 2 x ≤ r / 2) ∧
    (0 ≤ tiltCoefficient w 3 x ∧ tiltCoefficient w 3 x ≤ 1 / 24 ∧ tiltCoefficient w 3 x ≤ r / 6) := by
  let r := exp (-x)
  have rp : 0 < r := exp_pos _
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have den : 0 < 1 + r := by positivity
  have hd1 : 1 ≤ 1 + r := by linarith only [rp]
  have hd2 : 1 ≤ (1 + r) ^ 2 := one_le_pow₀ hd1
  have hd3 : 1 ≤ (1 + r) ^ 3 := one_le_pow₀ hd1
  have bounds (j : ℕ) : 0 ≤ 1 - w j ∧ 1 - w j ≤ 1 :=
    ⟨by linarith only [(unit j).2], by linarith only [(unit j).1]⟩
  obtain ⟨a, b, c⟩ := tilt_forms w w1 x
  change _ ∧ _ ∧ _
  rw [a, b, c]
  have w2r := mul_le_of_le_one_left rp.le (bounds 2).2
  have w3r := mul_le_of_le_one_left rp.le (bounds 3).2
  have w3r' := mul_le_mul_of_nonneg_right w3r (sub_nonneg.mpr r1)
  have w3rNonneg := mul_nonneg (mul_nonneg (bounds 3).1 rp.le) (sub_nonneg.mpr r1)
  have w3rle := w3r'.trans (mul_le_of_le_one_right rp.le (by linarith only [rp]))
  refine ⟨⟨by positivity, ?_, div_le_self rp.le hd1⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [div_le_div_iff₀ den (by norm_num)]
    linarith only [r1]
  · exact div_nonneg (mul_nonneg (bounds 2).1 rp.le) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [w2r, sq_nonneg (r - 1)]
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [w2r, mul_le_mul_of_nonneg_right hd2 rp.le]
  · exact div_nonneg w3rNonneg (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [w3r', sq_nonneg (r - 1/2), hd3]
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [w3rle, mul_le_mul_of_nonneg_right hd3 rp.le]

private theorem cycleMoment_three_abs {x : ℝ} (hx : 0 ≤ x) :
    |cycleMoment 3 x| ≤ exp (-x) := by
  let r := exp (-x)
  have rp : 0 < r := exp_pos _
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have den : 0 < 1 + r := by positivity
  have hf : cycleMoment 3 x = (-r) * (1 - r) / (1 + r) ^ 3 := by
    simp [cycleMoment, moment, eulerian_two, r, sub_eq_add_neg]
  rw [hf, abs_div, abs_mul, abs_neg, abs_of_pos rp,
    abs_of_nonneg (sub_nonneg.mpr r1), abs_of_pos (pow_pos den 3)]
  apply (div_le_iff₀ (pow_pos den 3)).mpr
  have e := mul_le_of_le_one_right rp.le (show 1 - r ≤ 1 by linarith only [rp])
  exact e.trans (le_mul_of_one_le_right rp.le
    (one_le_pow₀ (show 1 ≤ 1 + r by linarith only [rp])))

private theorem cycleMoment_four_abs {x : ℝ} (hx : 0 ≤ x) :
    |cycleMoment 4 x| ≤ exp (-x) := by
  let r := exp (-x)
  have rp : 0 < r := exp_pos _
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have den : 0 < 1 + r := by positivity
  have hf : cycleMoment 4 x = (-r) * (1 - 4 * r + r ^ 2) / (1 + r) ^ 4 := by
    simp [cycleMoment, moment, eulerian_three, r, sub_eq_add_neg]
  have cap : |1 - 4 * r + r ^ 2| ≤ (1 + r) ^ 4 := by
    apply abs_le.mpr
    have r2 : 0 ≤ r ^ 2 := sq_nonneg r
    have r3 : 0 ≤ r ^ 3 := pow_nonneg rp.le 3
    have r4 : 0 ≤ r ^ 4 := pow_nonneg rp.le 4
    constructor <;> nlinarith only [rp, r2, r3, r4]
  rw [hf, abs_div, abs_mul, abs_neg, abs_of_pos rp, abs_of_pos (pow_pos den 4)]
  exact (div_le_iff₀ (pow_pos den 4)).mpr (mul_le_mul_of_nonneg_left cap rp.le)

/-- Uniform bounds on the three genuine coefficients in the differentiated insertion row. -/
theorem drift_caps (w : ℕ → ℝ) (unit : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1) {x : ℝ}
    (hx : 0 ≤ x) :
    |drift w 1 x| ≤ exp (-x) ∧
    |drift w 2 x| ≤ exp (-x) / 2 ∧
    |drift w 3 x| ≤ exp (-x) / 6 := by
  have diff (j : ℕ) : |w (j + 1) - w j| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [(unit (j + 1)).1, (unit j).2],
      by linarith only [(unit (j + 1)).2, (unit j).1]⟩
  have bound (j : ℕ) : |drift w j x| ≤ |cycleMoment (j + 1) x| / j.factorial := by
    rw [drift, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < j.factorial)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (abs_nonneg _) (diff j)) (by positivity)
  have h2 : |cycleMoment 2 x| ≤ exp (-x) := by
    simpa using cycleMoment_abs hx 2
  have h3 := cycleMoment_three_abs hx
  have h4 := cycleMoment_four_abs hx
  refine ⟨?_, ?_, ?_⟩
  · exact (by simpa using bound 1 : |drift w 1 x| ≤ |cycleMoment 2 x|).trans h2
  · apply (bound 2).trans
    norm_num
    linarith only [h3]
  · apply (bound 3).trans
    norm_num
    linarith only [h4]

theorem tilt_cost_caps (w : ℕ → ℝ) (w1 : w 1 = 0) (unit : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    cost (fun j ↦ tiltCoefficient w j x) R 3 ≤ R/2 + R^2/8 + R^3/24 ∧
    cost (fun j ↦ tiltCoefficient w j x) R 3 ≤
      exp (-x) * (R + R^2/2 + R^3/6) := by
  obtain ⟨⟨a0, a, ar⟩, ⟨b0, b, br⟩, ⟨c0, c, cr⟩⟩ := tilt_caps w w1 unit hx
  simp only [cost, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num
  rw [abs_of_nonneg a0, abs_of_nonneg b0, abs_of_nonneg c0]
  constructor
  · linarith only [mul_le_mul_of_nonneg_right a hR, mul_le_mul_of_nonneg_right b (sq_nonneg R),
      mul_le_mul_of_nonneg_right c (pow_nonneg hR 3)]
  · nlinarith only [mul_le_mul_of_nonneg_right ar hR, mul_le_mul_of_nonneg_right br (sq_nonneg R),
      mul_le_mul_of_nonneg_right cr (pow_nonneg hR 3)]

theorem drift_cost_cap (w : ℕ → ℝ) (unit : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1) {x R : ℝ}
    (hx : 0 ≤ x) (hR : 0 ≤ R) :
    (∑ i ∈ range 3, |drift w (i + 1) x| * R ^ (i + 2)) ≤
      exp (-x) * (R ^ 2 + R ^ 3 / 2 + R ^ 4 / 6) := by
  obtain ⟨u, v, z⟩ := drift_caps w unit hx
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_right u (sq_nonneg R),
    mul_le_mul_of_nonneg_right v (pow_nonneg hR 3),
    mul_le_mul_of_nonneg_right z (pow_nonneg hR 4)]

#print axioms tilt_forms
#print axioms tilt_caps
#print axioms drift_caps
#print axioms tilt_cost_caps
#print axioms drift_cost_cap

end LongCycleBounds.FixedFour
