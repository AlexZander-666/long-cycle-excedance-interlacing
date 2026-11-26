import LongCycleBounds.FiveMiddleProfile
import LongCycleBounds.FixedFour49Budget
import LongCycleBounds.FixedFour49PoleMass
import LongCycleFinite.K5MiddleCert.Verified

/-! Transfer the middle-interval budgets to the actual profile. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real FixedCutoff Band PoleBridge MarkedTwo LongCycleFinite.K5MiddleCert
open LongCycleFinite.K5CompactCert (piLo)

private theorem C_val : (C:ℝ) = 657/10648 := by norm_num [C]

theorem middle_b_nonneg {w : ℕ → ℝ} (w1 : w 1 = 0) (wt : ∀ a ≥ 5, w a = 1)
    (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) {x : ℝ} (hx : 11 ≤ x) (a : ℕ) (ha : 0 < a) :
    0 ≤ tiltCoefficient w a x := by
  by_cases large : 5 ≤ a
  · simp [tiltCoefficient,wt a large]
  have x0 : 0 ≤ x := by linarith
  obtain ⟨h1,h2,h3⟩ := FixedFour.tilt_caps w w1 unit x0
  have er := (exp_le_exp.mpr (show -x ≤ -11 by linarith)).trans exp_neg_eleven
  have rsmall : exp (-x) ≤ 1/6 := er.trans (by norm_num [r0])
  have shape := shape_bounds (exp_pos (-x)).le (exp_le_one_iff.mpr (by linarith))
  have q := quartic_tilt w x
  have last : 0 ≤ tiltCoefficient w 4 x := by
    rw [q]
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr (unit 4).2) shape.1)
      (by linarith only [shape.2.1,rsmall])) (by norm_num)
  have hi : a ≤ 4 := by omega
  interval_cases a <;> first | exact h1.1 | exact h2.1 | exact h3.1 | exact last

theorem middle_costs {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 11 ≤ x) :
    let b := fun a ↦ tiltCoefficient w a x
    cost b (radius x) 4 ≤ (v0:ℝ) ∧ exp (cost b (2*radius x) 4) < 2 := by
  dsimp only
  have rx : 11 ≤ radius x := hx.trans (FixedFour49.radius_bounds (by linarith : 9≤x)).1
  have x0 : 0 ≤ x := by linarith
  have decay := radius_power_decay hx (radius_pos x).le (radius_le_alpha hx) (m:=4) (by decide)
  have cap := mul_le_mul_of_nonneg_left decay (show 0 ≤ (C:ℝ) by rw [C_val]; norm_num)
  have u : (657/10648:ℝ)*exp (-x)*(radius x)^4 ≤ v0 := by
    rw [C_val] at cap
    have target := v_formula_le
    rw [C_val] at target
    linarith only [cap,target]
  refine ⟨(middle_profile_cost w1 unit x0 rx).trans u, ?_⟩
  apply lt_of_le_of_lt _ exp_sixteen_v0
  apply exp_le_exp.mpr
  have large := middle_profile_cost w1 unit x0 (show 11 ≤ 2*radius x by linarith)
  nlinarith only [large,u]

theorem middle_drift_sum {w : ℕ → ℝ} (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 11 ≤ x) :
    (∑ i ∈ Finset.range 4, |drift w (i+1) x| *(radius x)^(i+2)) ≤ (J:ℝ)*s x := by
  let R := radius x
  have rp : 0 < R := radius_pos x
  have rx : 11 ≤ R := hx.trans (FixedFour49.radius_bounds (by linarith : 9≤x)).1
  have costle := middle_drift_cost unit (by linarith : 0≤x) rx
  have decay := radius_power_decay hx rp.le (radius_le_alpha hx) (m:=6) (by decide)
  have c0 : 0 ≤ (C:ℝ) := by rw [C_val]; norm_num
  have pi0 : 0 < (piLo:ℝ) := by norm_num [piLo]
  have pil : (piLo:ℝ) ≤ π := by norm_num [piLo]; linarith [pi_gt_d6]
  have jp : (0:ℝ) ≤ J := (Rat.cast_pos.mpr main_arithmetic.2.2.2.2.1).le
  have je := (div_le_iff₀ pi0).mp drift_formula_le
  have ce := mul_le_mul_of_nonneg_left decay c0
  rw [C_val] at ce je
  have scaled := mul_le_mul_of_nonneg_right costle (sq_nonneg R)
  have eq : (∑ i ∈ Finset.range 4, |drift w (i+1) x| *R^(i+2)) =
      cost (fun i ↦ drift w i x) R 4 * R := by
    simp only [cost,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show i+2=i+1+1 by omega,pow_succ,mul_assoc]
  change _ ≤ (J:ℝ)*(π/R)
  rw [eq,←mul_div_assoc,le_div_iff₀ rp]
  nlinarith only [scaled,ce,je,mul_le_mul_of_nonneg_left pil jp]

/-- The half-order pole estimate also covers the shortest quartic insertion coefficient. -/
theorem middle_half_order (x : ℝ) (hx : 0 ≤ x) {n j i : ℕ} (hn : 49 ≤ n)
    (hj : n-5 ≤ j) (hi : i ≤ j/2) :
    |scaledCoeff (MarkedTwo.logistic (time x)) (radius x) (j-i)| ≤
      2 + 2*(radius x)^2/(((n-3:ℕ):ℝ)*π^2) := by
  simpa only [Nat.sub_sub] using FixedFour49.logistic_half_order_bound x hx
    (n:=n-1) (j:=j) (i:=i) (by omega) (by omega) hi

#print axioms middle_b_nonneg
#print axioms middle_costs
#print axioms middle_drift_sum
#print axioms middle_half_order
end LongCycleBounds.FiveCutoff
