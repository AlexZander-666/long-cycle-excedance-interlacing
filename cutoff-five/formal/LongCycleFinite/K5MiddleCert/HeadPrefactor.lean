import LongCycleFinite.K5MiddleCert.Verified

/-! The real head budget with the certified radius, tilt cost and sine normalization. -/

namespace LongCycleFinite.K5MiddleCert

open Real K5CompactCert

theorem head_prefactor {n : ℕ} (hn : 49 ≤ n) {x R v : ℝ} (hx : 11 ≤ x) (hRp : 0 < R)
    (hR : R ≤ (alpha : ℝ) * x) (hv : 0 ≤ v) (hcost : v ≤ (C : ℝ) * exp (-x) * R ^ 4)
    (hsmall : v ≤ (v0 : ℝ)) :
    (2 + 2 * R ^ 2 / (((n - 3 : ℕ) : ℝ) * π ^ 2)) * (exp v - 1) ≤
      (head : ℝ) * (π / R) := by
  let P : ℝ := piLo
  let D : ℝ := 46 * P ^ 2
  let U : ℝ := 1 - (v0 : ℝ)
  have hp : 0 < P := by norm_num [P, piLo]
  have hP : P ≤ π := by
    norm_num [P, piLo]
    linarith [pi_gt_d6]
  have hd : 0 < D := by dsimp [D]; positivity
  have hu : 0 < U := sub_pos.mpr (v0_lt.trans (by norm_num))
  have hC : 0 ≤ (C : ℝ) := by norm_num [C]
  have hn' : (46 : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := by exact_mod_cast (show 46 ≤ n - 3 by omega)
  have hD : D ≤ ((n - 3 : ℕ) : ℝ) * π ^ 2 :=
    mul_le_mul hn' (pow_le_pow_left₀ hp.le hP 2) (sq_nonneg _) (by norm_num)
  have hmass : 2 + 2 * R ^ 2 / (((n - 3 : ℕ) : ℝ) * π ^ 2) ≤ 2 + 2 * R ^ 2 / D :=
    add_le_add (le_refl _) (div_le_div_of_nonneg_left (by positivity) hd hD)
  have hv' : exp v - 1 ≤ (C : ℝ) * exp (-x) * R ^ 4 / U :=
    (exp_sub_one_le hv hsmall).trans (div_le_div_of_nonneg_right hcost hu.le)
  have hnonneg : 0 ≤ exp v - 1 := by simpa using exp_le_exp.mpr hv
  have hmass0 : 0 ≤ 2 + 2 * R ^ 2 / D := by positivity
  have h5 := radius_power_decay hx hRp.le hR (m := 5) (by decide)
  have h7 := radius_power_decay hx hRp.le hR (m := 7) (by decide)
  have hsums :
      2 * (exp (-x) * R ^ 5) + 2 * (exp (-x) * R ^ 7) / D ≤
        2 * ((alpha : ℝ) ^ 5 * 11 ^ 5 * (r0 : ℝ)) +
          2 * ((alpha : ℝ) ^ 7 * 11 ^ 7 * (r0 : ℝ)) / D :=
    add_le_add (mul_le_mul_of_nonneg_left h5 (by norm_num))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (by norm_num)) hd.le)
  have hhead : 0 ≤ (head : ℝ) := by norm_num [rounded_values.2.2.1]
  rw [← mul_div_assoc (head : ℝ) π R]
  apply (le_div_iff₀ hRp).2
  calc
    (2 + 2 * R ^ 2 / (((n - 3 : ℕ) : ℝ) * π ^ 2)) * (exp v - 1) * R ≤
        (2 + 2 * R ^ 2 / D) * ((C : ℝ) * exp (-x) * R ^ 4 / U) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul hmass hv' hnonneg hmass0) hRp.le
    _ = (C : ℝ) * (2 * (exp (-x) * R ^ 5) + 2 * (exp (-x) * R ^ 7) / D) / U := by ring
    _ ≤ (C : ℝ) * (2 * ((alpha : ℝ) ^ 5 * 11 ^ 5 * (r0 : ℝ)) +
        2 * ((alpha : ℝ) ^ 7 * 11 ^ 7 * (r0 : ℝ)) / D) / U :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsums hC) hu.le
    _ = ((C : ℝ) * (r0 : ℝ) *
        (2 * (alpha : ℝ) ^ 5 * 11 ^ 5 + 2 * (alpha : ℝ) ^ 7 * 11 ^ 7 / D) / (P * U)) * P := by
      field_simp [hp.ne', hu.ne', hd.ne']
    _ ≤ (head : ℝ) * P := mul_le_mul_of_nonneg_right head_formula_le hp.le
    _ ≤ (head : ℝ) * π := mul_le_mul_of_nonneg_left hP hhead

#print axioms head_prefactor

end LongCycleFinite.K5MiddleCert
