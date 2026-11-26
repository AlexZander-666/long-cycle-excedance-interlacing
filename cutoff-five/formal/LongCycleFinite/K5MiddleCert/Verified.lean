import LongCycleFinite.K5MiddleCert.Checks
import LongCycleFinite.K5CompactCert.ExpBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Real scalar bounds for the certified middle-region budgets -/

namespace LongCycleFinite.K5MiddleCert

open K5CompactCert Real

theorem v0_positive : 0 < (v0 : ℝ) := Rat.cast_pos.mpr main_arithmetic.1

theorem v0_lt : (v0 : ℝ) < 8877 / 500000 := by
  simpa using (Rat.cast_lt (K := ℝ)).mpr main_arithmetic.2.1

theorem head_lt : (head : ℝ) < 17 / 100 := by
  simpa using (Rat.cast_lt (K := ℝ)).mpr main_arithmetic.2.2.1

theorem head_add_tail_lt : (head : ℝ) + (tail : ℝ) < 1 / 4 := by
  simpa using (Rat.cast_lt (K := ℝ)).mpr main_arithmetic.2.2.2.1

theorem tail_lt : (tail : ℝ) < 167 / 1000000 := by
  have h : tail < 167 / 1000000 := by decide +kernel
  simpa using (Rat.cast_lt (K := ℝ)).mpr h

theorem J_lt : (J : ℝ) < 1 := by
  simpa using (Rat.cast_lt (K := ℝ)).mpr main_arithmetic.2.2.2.2.2

theorem J_tight : (J : ℝ) < 37 / 50 := by
  have h : J < 37 / 50 := by decide +kernel
  simpa using (Rat.cast_lt (K := ℝ)).mpr h

theorem v_formula_le :
    (C : ℝ) * (alpha : ℝ) ^ 4 * 11 ^ 4 * (r0 : ℝ) ≤ (v0 : ℝ) := by
  simpa [v0, vFormula] using (Rat.cast_le (K := ℝ)).mpr (le_roundUp vFormula)

theorem head_formula_le :
    (C : ℝ) * (r0 : ℝ) *
        (2 * (alpha : ℝ) ^ 5 * 11 ^ 5 + 2 * (alpha : ℝ) ^ 7 * 11 ^ 7 /
          (46 * (piLo : ℝ) ^ 2)) / ((piLo : ℝ) * (1 - (v0 : ℝ))) ≤ (head : ℝ) := by
  simpa [head, headFormula] using (Rat.cast_le (K := ℝ)).mpr (le_roundUp headFormula)

theorem drift_formula_le :
    (C : ℝ) * (r0 : ℝ) * (alpha : ℝ) ^ 6 * 11 ^ 6 / (piLo : ℝ) ≤ (J : ℝ) := by
  simpa [J, driftFormula] using (Rat.cast_le (K := ℝ)).mpr (le_roundUp driftFormula)

/-- The real endpoint is enclosed using the certified positive Taylor truncation at 11. -/
theorem exp_neg_eleven : exp (-11) ≤ (r0 : ℝ) := by
  have h := expTaylor_le_exp (q := 11) (by decide) 64
  have hr : 0 ≤ (r0 : ℝ) := (Rat.cast_pos.mpr endpoint_arithmetic.2.2.1).le
  have hone : 1 ≤ (r0 : ℝ) * (expTaylor 11 64 : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr endpoint_arithmetic.2.2.2
  rw [exp_neg, ← one_div]
  exact (div_le_iff₀ (exp_pos _)).mpr (hone.trans
    (mul_le_mul_of_nonneg_left (by simpa using h) hr))

/-- The certified upper radius ratio applies on the whole half-line x ≥ 11. -/
theorem radius_le_alpha {x : ℝ} (hx : 11 ≤ x) :
    sqrt (x ^ 2 + π ^ 2) ≤ (alpha : ℝ) * x := by
  have hpi : π ≤ (piHi : ℝ) := by norm_num [piHi]; linarith [pi_lt_d6]
  have halpha : 0 < (alpha : ℝ) := Rat.cast_pos.mpr endpoint_arithmetic.1
  have ha : 1 + ((piHi : ℝ) / 11) ^ 2 ≤ (alpha : ℝ) ^ 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr endpoint_arithmetic.2.1
  have hx0 : 0 ≤ x := by linarith
  have hpi2 : π ^ 2 ≤ ((piHi : ℝ) / 11) ^ 2 * x ^ 2 := by
    calc
      π ^ 2 ≤ (piHi : ℝ) ^ 2 := pow_le_pow_left₀ pi_pos.le hpi 2
      _ = ((piHi : ℝ) / 11) ^ 2 * 11 ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hx 2) (sq_nonneg _)
  apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg halpha.le hx0)).mp
  rw [sq_sqrt (by positivity)]
  calc
    x ^ 2 + π ^ 2 ≤ (1 + ((piHi : ℝ) / 11) ^ 2) * x ^ 2 := by linarith only [hpi2]
    _ ≤ ((alpha : ℝ) * x) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right ha (sq_nonneg x)

/-- Every power needed in the middle region is controlled by the endpoint at 11. -/
theorem x_power_decay {x : ℝ} (hx : 11 ≤ x) {m : ℕ} (hm : m ≤ 7) :
    exp (-x) * x ^ m ≤ 11 ^ m * (r0 : ℝ) := by
  let d := (x - 11) / 7
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hxexp : x ≤ 11 * exp d := by
    have h := add_one_le_exp d
    dsimp [d] at h
    linarith
  have hpow := pow_le_pow_left₀ hx0 hxexp m
  rw [mul_pow, ← exp_nat_mul] at hpow
  have hm' : (m : ℝ) ≤ 7 := by exact_mod_cast hm
  have hexp : exp (-x) * exp ((m : ℝ) * d) ≤ exp (-11) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hm' hd
    dsimp [d] at h
    dsimp [d]
    linarith only [h]
  calc
    exp (-x) * x ^ m ≤ exp (-x) * (11 ^ m * exp ((m : ℝ) * d)) :=
      mul_le_mul_of_nonneg_left hpow (exp_nonneg _)
    _ = 11 ^ m * (exp (-x) * exp ((m : ℝ) * d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hexp.trans exp_neg_eleven) (by positivity)

/-- The same decay estimate with any radius bounded by the certified ratio. -/
theorem radius_power_decay {x R : ℝ} (hx : 11 ≤ x) (hR0 : 0 ≤ R)
    (hR : R ≤ (alpha : ℝ) * x) {m : ℕ} (hm : m ≤ 7) :
    exp (-x) * R ^ m ≤ (alpha : ℝ) ^ m * 11 ^ m * (r0 : ℝ) := by
  calc
    exp (-x) * R ^ m ≤ exp (-x) * ((alpha : ℝ) * x) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hR m) (exp_nonneg _)
    _ = (alpha : ℝ) ^ m * (exp (-x) * x ^ m) := by rw [mul_pow]; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (x_power_decay hx hm)
        (pow_nonneg (Rat.cast_pos.mpr endpoint_arithmetic.1).le _)

/-- The larger radius multiplies the quartic cost by at most 16 in the application. -/
theorem exp_sixteen_v0 : exp (16 * (v0 : ℝ)) < 2 := by
  have h0 : 0 ≤ 16 * v0 := mul_nonneg (by norm_num) main_arithmetic.1.le
  have h := exp_le_expUpper h0 exponential_arithmetic.1
  have h2 : (expUpper (16 * v0) 1 : ℝ) < 2 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr exponential_arithmetic.2.2
  simpa using h.trans_lt h2

/-- A geometric bound for the accelerated tilt in the head. -/
theorem exp_sub_one_le {v : ℝ} (hv : 0 ≤ v) (hle : v ≤ (v0 : ℝ)) :
    exp v - 1 ≤ v / (1 - (v0 : ℝ)) := by
  have hv0 : (v0 : ℝ) < 1 := v0_lt.trans (by norm_num)
  have hv1 := hle.trans_lt hv0
  have h := exp_bound_div_one_sub_of_interval hv hv1
  have id : 1 / (1 - v) - 1 = v / (1 - v) := by
    field_simp [ne_of_gt (sub_pos.mpr hv1)]
    ring
  calc
    exp v - 1 ≤ 1 / (1 - v) - 1 := sub_le_sub_right h 1
    _ = v / (1 - v) := id
    _ ≤ _ := div_le_div_of_nonneg_left hv (sub_pos.mpr hv0) (sub_le_sub_left hle 1)

/-- The cubic factor in the tail estimate has the required strict reserve. -/
theorem tail_cubic_factor : 18 * (alpha : ℝ) ^ 3 / π < 7 := by
  have hlo : (piLo : ℝ) ≤ π := by norm_num [piLo]; linarith [pi_gt_d6]
  have hlo0 : 0 < (piLo : ℝ) := by norm_num [piLo]
  have ha : 0 ≤ (alpha : ℝ) := (Rat.cast_pos.mpr endpoint_arithmetic.1).le
  have hc : 18 * (alpha : ℝ) ^ 3 / (piLo : ℝ) < 7 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr reserve_arithmetic.1
  exact (div_le_div_of_nonneg_left (by positivity) hlo0 hlo).trans_lt hc

/-- The scalar multiplying the doubled-radius tail on the specified middle interval. -/
theorem tail_prefactor {p : ℕ} (hp : 48 ≤ p) {x R : ℝ} (hx : 11 ≤ x)
    (hxupper : x ≤ 3 * sqrt (p : ℝ)) (hR0 : 0 ≤ R) (hR : R ≤ (alpha : ℝ) * x) :
    2 * R ^ 3 / (π * x) < 7 * ((p + 1 : ℕ) : ℝ) := by
  have xp : 0 < x := by linarith
  have pp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hs : x ^ 2 ≤ 9 * (p : ℝ) := by
    calc
      x ^ 2 ≤ (3 * sqrt (p : ℝ)) ^ 2 := pow_le_pow_left₀ xp.le hxupper 2
      _ = _ := by rw [mul_pow, sq_sqrt pp.le]; norm_num
  calc
    2 * R ^ 3 / (π * x) ≤ 2 * ((alpha : ℝ) * x) ^ 3 / (π * x) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hR 3) (by norm_num)) (by positivity)
    _ = (18 * (alpha : ℝ) ^ 3 / π) * (x ^ 2 / 9) := by
      field_simp [xp.ne', pi_pos.ne']
      ring
    _ ≤ (18 * (alpha : ℝ) ^ 3 / π) * (p : ℝ) := by
      have ha : 0 ≤ (alpha : ℝ) := (Rat.cast_pos.mpr endpoint_arithmetic.1).le
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (by norm_num)).mpr
        (by linarith only [hs])) (by positivity)
    _ < 7 * (p : ℝ) := mul_lt_mul_of_pos_right tail_cubic_factor pp
    _ ≤ _ := by push_cast; linarith

private theorem tail_nat (m : ℕ) (hm : 22 ≤ m) :
    140000000 * (2 * m + 6) ≤ 1669 * 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ]
    omega

/-- The tail allowance is valid at every needed order, including the lower boundary j = n−5. -/
theorem tail_bound {n j : ℕ} (hn : 49 ≤ n) (hj : n - 5 ≤ j) :
    14 * (n : ℝ) / 2 ^ (j / 2) ≤ (tail : ℝ) := by
  have h := tail_nat (j / 2) (by omega)
  have h' : 140000000 * n ≤ 1669 * 2 ^ (j / 2) := by omega
  have hr : 140000000 * (n : ℝ) ≤ 1669 * 2 ^ (j / 2) := by exact_mod_cast h'
  rw [show (tail : ℝ) = 1669 / 10000000 by
    simpa using congrArg (Rat.castHom ℝ) rounded_values.2.2.2.1]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hr]

theorem bare_mass_reserve {n : ℕ} (hn : 49 ≤ n) :
    2 + (n : ℝ) / ((n - 4 : ℕ) : ℝ) + 1 / 4 < 4 := by
  have hn' : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n)]
    norm_num
  rw [hd]
  have hratio : (n : ℝ) / ((n : ℝ) - 4) ≤ 49 / 45 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have reserve : 2 + (49 / 45 : ℝ) + 1 / 4 < 4 := by norm_num
  linarith

theorem insertion_reserve {n : ℕ} (hn : 49 ≤ n) :
    4 * (J : ℝ) / n < 1 / 2 := by
  have hn' : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ (J : ℝ) := (Rat.cast_pos.mpr main_arithmetic.2.2.2.2.1).le
  have hc : 4 * (J : ℝ) / 49 < 1 / 2 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr reserve_arithmetic.2.2
  exact (div_le_div_of_nonneg_left (by positivity) (by norm_num) hn').trans_lt hc

end LongCycleFinite.K5MiddleCert
