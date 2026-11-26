import LongCycleBounds.FixedCutoffCompactLogistic

/-! Nonprincipal poles at any common radius up through the third pole. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PoleBridge Finset

private theorem den_sq (x l : ℝ) : ‖den x l‖ ^ 2 = x^2+(l*π)^2 := by
  rw [Complex.sq_norm]
  simp [den, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

/-- Squared decay at all omitted poles, with additional powers bounded uniformly. -/
theorem omitted_term (x R : ℝ) (hR : 0 ≤ R) (hthird : R ≤ ‖den x 3‖)
    (q : ℕ) (hq : 2 ≤ q) (i : ℕ) :
    ‖(R : ℂ) / den x (2*(i:ℝ)+3)‖ ^ q ≤
    (R^2/(4*π^2))*(1/((i:ℝ)+1)-1/((i:ℝ)+2)) := by
  let l : ℝ := 2*(i:ℝ)+3
  let D := ‖den x l‖
  have hl : 3 ≤ l := by dsimp [l]; linarith [Nat.cast_nonneg (α:=ℝ) i]
  have lp : 0 < l := by linarith
  have ds : D^2 = x^2+(l*π)^2 := den_sq x l
  have lpi : l*π ≤ D := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith only [ds, sq_nonneg x]
  have dp : 0 < D := (mul_pos lp pi_pos).trans_le lpi
  have rD : R ≤ D := hthird.trans (by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [den_sq,ds]
    exact add_le_add_right (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hl pi_pos.le) 2) _)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR]
  change (R/D)^q ≤ _
  calc
    _ ≤ (R/D)^2 := pow_le_pow_of_le_one (div_nonneg hR dp.le) ((div_le_one₀ dp).mpr rD) hq
    _ ≤ (R/(l*π))^2 := pow_le_pow_left₀ (div_nonneg hR dp.le)
      (div_le_div_of_nonneg_left hR (mul_pos lp pi_pos) lpi) 2
    _ = (R^2/(4*π^2))*(4/l^2) := by field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have a : 0 < (i:ℝ)+1 := by positivity
      have b : 0 < (i:ℝ)+2 := by positivity
      field_simp
      dsimp [l]
      nlinarith [sq_nonneg (i:ℝ)]
/-- Both omitted half-planes have total norm at most R²/(2π²). -/
theorem omitted_summable_and_mass (x R : ℝ) (hR : 0 ≤ R) (hthird : R ≤ ‖den x 3‖)
    (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun i : ℕ ↦ ‖(R : ℂ) / den x (2*(i:ℝ)+3)‖ ^ q) ∧
    2*(∑' i : ℕ, ‖(R : ℂ) / den x (2*(i:ℝ)+3)‖ ^ q) ≤ R^2/(2*π^2) := by
  let A := R^2/(4*π^2)
  let f (i : ℕ) := ‖(R : ℂ) / den x (2*(i:ℝ)+3)‖ ^ q
  have a0 : 0 ≤ A := by dsimp [A]; positivity
  have partialSum (m : ℕ) : (∑ i ∈ range m, f i) ≤ A * (1-1/((m:ℝ)+1)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, Nat.cast_succ]
      have term := omitted_term x R hR hthird q hq m
      change f m ≤ A*(1/((m:ℝ)+1)-1/((m:ℝ)+2)) at term
      rw [show (m:ℝ)+1+1=(m:ℝ)+2 by ring]
      linarith only [ih,term]
  have uniform (m : ℕ) : (∑ i ∈ range m, f i) ≤ A :=
    (partialSum m).trans (by nlinarith only [mul_nonneg a0 (show 0 ≤ 1/((m:ℝ)+1) by positivity)])
  have mass := Real.tsum_le_of_sum_range_le (f:=f) (fun i => by dsimp [f]; positivity) uniform
  refine ⟨summable_of_sum_range_le (f := f) (fun i => by dsimp [f]; positivity) uniform, ?_⟩
  change 2*(∑' i, f i) ≤ _
  calc
    _ ≤ 2*A := by linarith only [mass]
    _ = _ := by dsimp [A]; ring

theorem omitted_mass (x R : ℝ) (hR : 0 ≤ R) (hthird : R ≤ ‖den x 3‖)
    (q : ℕ) (hq : 2 ≤ q) :
    2*(∑' i : ℕ, ‖(R : ℂ) / den x (2*(i:ℝ)+3)‖ ^ q) ≤ R^2/(2*π^2) :=
  (omitted_summable_and_mass x R hR hthird q hq).2

#print axioms omitted_summable_and_mass
#print axioms omitted_mass
end LongCycleBounds.AdjustablePoleRadius
