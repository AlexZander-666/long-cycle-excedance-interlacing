import LongCycleBounds.AdjustableTiltError
import LongCycleBounds.FixedCutoffReadout

/-! Transfer the adjustable pole estimate to the permutation enumerator. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real MarkedTwo PoleBridge FixedCutoff

/-- The scaled quantity is the original normalized row, with the exact factorial
and (1-t) normalization. Short weights may be arbitrary real numbers. -/
theorem profile_error {k : ℕ} (hk : 2 ≤ k) (w : ℕ → ℝ) (w1 : w 1 = 0)
    (tail : ∀ a ≥ k, w a = 1) {x R : ℝ} (hx : 0 ≤ x) (hr : radius x < R)
    (hthird : R ≤ ‖den x 3‖) (j : ℕ) :
    let b := fun a ↦ tiltCoefficient w a x
    |gain (radius x) j x * CycleProfile.normalizedRow w j x -
      2 * (tiltValue b (k-1) (nearestPole x) * compactRotation x^(j+1)).re| ≤
      max (radius x) (radius x*R/(2*π^2)) *
        (radius x/R)^j * exp (cost b R (k-1)) := by
  dsimp only
  rw [← scaled_eq_gain hk w w1 tail hx]
  exact physical_error _ _ _ hx hr hthird

/-- A single order-44 relative budget covers every subsequent coefficient in
the same cell, including the four predecessor terms of the five-cutoff drift. -/
theorem profile_error_from_44 (w : ℕ → ℝ) (w1 : w 1 = 0)
    (tail : ∀ a ≥ 5, w a = 1) {x R : ℝ} (hx : 0 ≤ x) (hr : radius x < R)
    (hthird : R ≤ ‖den x 3‖) {ε : ℝ} (j : ℕ) (hj : 44 ≤ j)
    (cell : let b := fun a ↦ tiltCoefficient w a x
            max (radius x) (radius x*R/(2*π^2)) * (radius x/R)^44 * exp (cost b R 4) <
              ε * (s x * ‖tiltValue b 4 (nearestPole x)‖)) :
    let b := fun a ↦ tiltCoefficient w a x
    |gain (radius x) j x * CycleProfile.normalizedRow w j x -
      2 * (tiltValue b 4 (nearestPole x) * compactRotation x^(j+1)).re| <
        ε * (s x * ‖tiltValue b 4 (nearestPole x)‖) := by
  dsimp only at cell ⊢
  have Rp := (radius_pos x).trans hr
  have q0 := div_nonneg (radius_pos x).le Rp.le
  have q1 := (div_lt_one₀ Rp).mpr hr
  apply (profile_error (by decide : 2 ≤ 5) w w1 tail hx hr hthird j).trans_lt
  apply lt_of_le_of_lt _ cell
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one q0 q1.le hj)
      ((radius_pos x).le.trans (le_max_left _ _))) (exp_pos _).le

#print axioms profile_error
#print axioms profile_error_from_44
end LongCycleBounds.AdjustablePoleRadius
