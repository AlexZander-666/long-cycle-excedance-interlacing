import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Comparison of polynomial label errors along a square-root boundary. -/

noncomputable section

namespace LongCycleBounds.OuterDecayEnvelope

open Real

/-- Once 2d ≤ c a, the error (1+t²)^d exp(-ct) is controlled by its value at a. -/
theorem compare {a t c : ℝ} (a0 : 0 < a) (at' : a ≤ t) (d : ℕ)
    (start : (2*d : ℝ) ≤ c*a) :
    (1+t^2)^d * exp (-(c*t)) ≤ (1+a^2)^d * exp (-(c*a)) := by
  let z := (t-a)/a
  have z0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr at') a0.le
  have az : a*z = t-a := by dsimp [z]; field_simp
  have eq : a*(1+z) = t := by linarith only [az, mul_add a 1 z, mul_one a]
  have r : 1+t^2 ≤ (1+a^2)*(1+z)^2 := by
    rw [← eq]
    nlinarith only [z0, sq_nonneg z]
  have ex : 1+z ≤ exp z := by linarith [Real.add_one_le_exp z]
  have rd := pow_le_pow_left₀ (by positivity) r d
  have base := pow_le_pow_left₀ (by positivity : 0 ≤ 1+z) ex (2*d)
  rw [mul_pow, ←pow_mul] at rd
  rw [←exp_nat_mul] at base
  have cz := mul_le_mul_of_nonneg_right start z0
  have slope : ((2*d : ℕ) : ℝ)*z ≤ c*(t-a) := by
    push_cast
    rw [← az]
    linarith only [cz,mul_assoc c a z]
  have v := base.trans (exp_le_exp.mpr slope)
  have upper := rd.trans (mul_le_mul_of_nonneg_left v (by positivity))
  calc
    _ ≤ ((1+a^2)^d*exp (c*(t-a))) * exp (-(c*t)) :=
      mul_le_mul_of_nonneg_right upper (exp_pos _).le
    _ = _ := by rw [mul_assoc,←exp_add]; congr 2; ring

/-- The exterior eighth-power estimate starts at upper index 202. -/
theorem eighth_power {n : ℕ} (hn : 202 ≤ n) {x : ℝ}
    (outer : 3*sqrt ((n-1 : ℕ) : ℝ) ≤ x) : exp (-x)*(n : ℝ)^8 ≤ 1 := by
  let t := sqrt ((n-1 : ℕ) : ℝ)
  let a := sqrt 201
  have aa : a^2=201 := sq_sqrt (by norm_num)
  have ap : 0<a := sqrt_pos.mpr (by norm_num)
  have tt : t^2=((n-1 : ℕ) : ℝ) := sq_sqrt (by positivity)
  have castn : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have at' : a≤t := sqrt_le_sqrt (by exact_mod_cast (show 201 ≤ n-1 by omega))
  have al : (85 : ℝ) ≤ 6*a := by nlinarith only [aa,ap]
  have cmp := compare ap at' 8 (c := 3) (by norm_num; linarith only [al])
  have lower : (2718/1000 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have base : (202 : ℝ)^16 ≤ exp (6*a) := by
    calc
      _ ≤ (2718/1000 : ℝ)^85 := by norm_num
      _ ≤ (exp 1)^85 := pow_le_pow_left₀ (by norm_num) lower _
      _ = exp 85 := by rw [←exp_nat_mul]; norm_num
      _ ≤ _ := exp_le_exp.mpr al
  have s0 : (202 : ℝ)^8 ≤ exp (3*a) := by
    apply (sq_le_sq₀ (by positivity) (exp_pos _).le).mp
    rw [←pow_mul,←exp_nat_mul]
    simpa only [Nat.reduceMul, Nat.cast_ofNat, ←mul_assoc, show (2:ℝ)*3=6 by norm_num] using base
  have step : (1+a^2)^8 * exp (-(3*a)) ≤ 1 := by
    rw [aa,exp_neg,←div_eq_mul_inv,div_le_one (exp_pos _)]
    norm_num at *
    exact s0
  have fin := cmp.trans step
  have cv : 1+t^2=(n:ℝ) := by linarith only [tt,castn]
  rw [cv,mul_comm] at fin
  exact (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (neg_le_neg outer)) (by positivity)).trans fin

/-- At upper size 101 the sixth-power exterior error already fits a quarter-unit budget. -/
theorem sixth_power {n : ℕ} (hn : 101 ≤ n) {x : ℝ}
    (outer : 3*sqrt ((n-1 : ℕ) : ℝ) ≤ x) : 4 * (exp (-x)*(n : ℝ)^6) < 1 := by
  let t := sqrt ((n-1 : ℕ) : ℝ)
  have tt : t^2=((n-1 : ℕ) : ℝ) := sq_sqrt (by positivity)
  have castn : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have t10 : 10 ≤ t := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [tt,castn]
    have : (101 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [this]
  have cmp := compare (by norm_num : (0 : ℝ) < 10) t10 6 (c := 3) (by norm_num)
  have cv : 1+t^2=(n:ℝ) := by linarith only [tt,castn]
  rw [cv,mul_comm] at cmp
  have h30 : 4*(101:ℝ)^6 < exp 30 := by
    calc
      _ < (8/3 : ℝ)^30 := by norm_num
      _ ≤ (exp 1)^30 := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
      _ = exp 30 := by rw [←exp_nat_mul]; norm_num
  have head : 4*((1+(10:ℝ)^2)^6 * exp (-(3*10))) < 1 := by
    rw [exp_neg, ←mul_assoc, ←div_eq_mul_inv, div_lt_one (exp_pos _)]
    norm_num at h30 ⊢
    exact h30
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right (exp_le_exp.mpr (neg_le_neg outer)) (by positivity)).trans cmp)
    (by norm_num : (0:ℝ) ≤ 4)) head

#print axioms sixth_power
#print axioms compare
#print axioms eighth_power
end LongCycleBounds.OuterDecayEnvelope
