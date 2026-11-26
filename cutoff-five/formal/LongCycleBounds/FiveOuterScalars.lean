import LongCycleBounds.OuterDecayEnvelope
import LongCycleFinite.K5CompactCert.ExpBounds

/-! Scalar exterior estimates at upper size 49 for a quartic tilt. -/

namespace LongCycleBounds.FiveCutoff.Exterior

open Real LongCycleFinite.K5CompactCert

/-- The rational anchor lies below the exterior square-root threshold at size 49. -/
private theorem anchor_exp :
    3 * (1 + (69 / 10 : ℝ) ^ 2) ^ 5 < exp (3 * (69 / 10)) := by
  have h : 3 * (1 + (69 / 10 : ℚ) ^ 2) ^ 5 < expTaylor (207 / 10) 64 := by
    decide +kernel
  have hreal : 3 * (1 + (69 / 10 : ℝ) ^ 2) ^ 5 < (expTaylor (207 / 10) 64 : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr h
  have hTaylor := expTaylor_le_exp (q := 207 / 10) (by norm_num) 64
  rw [show (3 : ℝ) * (69 / 10) = 207 / 10 by norm_num]
  exact hreal.trans_le (by simpa using hTaylor)

/-- The fifth-power loss is strictly less than one third throughout the exterior. -/
theorem fifth_power {n : ℕ} (hn : 49 ≤ n) {x : ℝ}
    (outer : 3 * sqrt ((n - 1 : ℕ) : ℝ) ≤ x) :
    3 * (exp (-x) * (n : ℝ) ^ 5) < 1 := by
  let t := sqrt ((n - 1 : ℕ) : ℝ)
  have ht0 : 0 ≤ t := sqrt_nonneg _
  have hsq : t ^ 2 = ((n - 1 : ℕ) : ℝ) := sq_sqrt (by positivity)
  have hsize : 1 + t ^ 2 = (n : ℝ) := by
    rw [hsq, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hn' : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (69 / 10 : ℝ) ≤ t := by
    apply (sq_le_sq₀ (by norm_num) ht0).mp
    linarith only [hsize, hn']
  have hcomp := OuterDecayEnvelope.compare (by norm_num : (0 : ℝ) < 69 / 10)
    ht 5 (c := 3) (by norm_num)
  have hanchor : 3 * ((1 + (69 / 10 : ℝ) ^ 2) ^ 5 * exp (-(3 * (69 / 10)))) < 1 := by
    rw [exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_lt_one (exp_pos _)]
    exact anchor_exp
  have hdecay : exp (-x) * (n : ℝ) ^ 5 ≤
      (1 + (69 / 10 : ℝ) ^ 2) ^ 5 * exp (-(3 * (69 / 10))) := by
    calc
      exp (-x) * (n : ℝ) ^ 5 ≤ exp (-(3 * t)) * (n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right (exp_le_exp.mpr (neg_le_neg outer)) (by positivity)
      _ = (1 + t ^ 2) ^ 5 * exp (-(3 * t)) := by rw [hsize, mul_comm]
      _ ≤ _ := hcomp
  exact (mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 3)).trans_lt hanchor

/-- The power of two has the marked-label reserve starting at upper size 49. -/
theorem reserve {n : ℕ} (hn : 49 ≤ n) :
    3600 * (n : ℝ) ^ 5 ≤ (2 : ℝ) ^ (n - 9) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (49 : ℝ) ≤ n := by exact_mod_cast hn
    have growth : (n : ℝ) + 1 ≤ (11 / 10) * (n : ℝ) := by linarith
    have step := pow_le_pow_left₀ (by positivity) growth 5
    rw [mul_pow] at step
    rw [show n + 1 - 9 = (n - 9) + 1 by omega, pow_succ (2 : ℝ) (n - 9), Nat.cast_succ]
    nlinarith only [step, ih, pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 5]

#print axioms fifth_power
#print axioms reserve

end LongCycleBounds.FiveCutoff.Exterior
