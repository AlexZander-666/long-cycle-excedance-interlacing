import LongCycleBounds.AdjustableTiltPrefix

/-! Pass from all finite, disjoint coefficient budgets to the actual entire tilt. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PowerSeries MarkedTwo PoleBridge FixedCutoff QuadraticCutoff Finset Filter
open scoped Topology

theorem tilt_prefix_tendsto (b : ℕ → ℝ) (d : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖ < R) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ range (n+1), weightedCoeff (tilt b d) z i)
      atTop (𝓝 (tiltValue b d z)) := by
  have Rp := (norm_nonneg z).trans_lt hz
  let q := ‖z‖ / R
  have q0 : 0 ≤ q := div_nonneg (norm_nonneg _) Rp.le
  have q1 : q < 1 := (div_lt_one₀ Rp).mpr hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ tilt_truncation b d z Rp hz n)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one q0 q1).mul_const q
  have hp : Tendsto (fun n : ℕ ↦ q^(n+1)) atTop (𝓝 0) := by simpa [pow_succ] using ht
  simpa only [mul_zero, zero_div] using ((hp.const_mul (exp (cost b R d))).div_const (1-q))

theorem enlarged_error (b : ℕ → ℝ) (d j : ℕ) {x R : ℝ} (hx : 0 ≤ x) (hr : radius x < R)
    (hthird : R ≤ ‖den x 3‖) :
    |scaledCoeff (tilt b d * logistic (time x)) R j -
        2 * (((R : ℂ) / nearestPole x)^(j+1) * tiltValue b d (nearestPole x)).re| ≤
        max R (R^2/(2*π^2)) * exp (cost b R d) := by
  let A := ((R : ℂ) / nearestPole x)^(j+1)
  have hs := tilt_prefix_tendsto b d (nearestPole x) ((nearestPole_norm x).trans_lt hr)
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp (hs.const_mul A)
  have ht := ((hRe.const_mul 2).const_sub (scaledCoeff (tilt b d * logistic (time x)) R j)).abs
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop j] with n hn
  exact prefix_error b d hx hr.le hthird hn

#print axioms tilt_prefix_tendsto
#print axioms enlarged_error
end LongCycleBounds.AdjustablePoleRadius
