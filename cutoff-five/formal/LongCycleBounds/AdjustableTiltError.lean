import LongCycleBounds.AdjustableTiltLimit

/-! An effective, variable-radius two-pole estimate for the actual tilted
logistic coefficients, with no geometric-series loss at the cutoff. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PowerSeries MarkedTwo PoleBridge FixedCutoff

theorem physical_error (b : ℕ → ℝ) (d j : ℕ) {x R : ℝ} (hx : 0 ≤ x)
    (hr : radius x < R) (hthird : R ≤ ‖den x 3‖) :
    |scaledCoeff (tilt b d * logistic (time x)) (radius x) j -
        2 * (tiltValue b d (nearestPole x) * compactRotation x^(j+1)).re| ≤
      max (radius x) (radius x * R / (2*π^2)) * (radius x/R)^j * exp (cost b R d) := by
  let ρ := radius x
  let q := ρ/R
  let P := tilt b d * logistic (time x)
  let B := tiltValue b d (nearestPole x)
  let A := ((R : ℂ)/nearestPole x)^(j+1)
  have rp : 0 < ρ := radius_pos x
  have Rp : 0 < R := rp.trans hr
  have qpos : 0 < q := div_pos rp Rp
  have qr : q*R=ρ := div_mul_cancel₀ _ Rp.ne'
  have row : scaledCoeff P ρ j = q^(j+1)*scaledCoeff P R j := by
    simp [scaledCoeff, ← mul_assoc, ← mul_pow, qr]
  have rot : compactRotation x=(q:ℂ)*((R:ℂ)/nearestPole x) := by
    rw [compactRotation, ← mul_div_assoc, ← Complex.ofReal_mul, qr]
  have amp : (B*compactRotation x^(j+1)).re = q^(j+1)*(A*B).re := by
    rw [rot,mul_pow,show B*((q:ℂ)^(j+1)*A)=(q:ℂ)^(j+1)*(A*B) by ring,
      ← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have maxeq : q * max R (R^2/(2*π^2)) = max ρ (ρ*R/(2*π^2)) := by
    rw [mul_max_of_nonneg _ _ qpos.le,qr,← qr]
    congr 1
    ring
  change |scaledCoeff P ρ j-2*(B*compactRotation x^(j+1)).re| ≤ _
  rw [row,amp,show ∀ y v : ℝ, q^(j+1)*y - 2*(q^(j+1)*v)=q^(j+1)*(y-2*v) by intros;ring,
    abs_mul,abs_of_pos (pow_pos qpos _)]
  have e := enlarged_error b d j hx hr hthird
  change |scaledCoeff P R j - 2*(A*B).re| ≤ _ at e
  calc
    _ ≤ q^(j+1)*(max R (R^2/(2*π^2))*exp (cost b R d)) :=
      mul_le_mul_of_nonneg_left e (pow_nonneg qpos.le _)
    _ = _ := by
      rw [pow_succ, show ∀ v c : ℝ, q^j*q*(v*c)=(q*v)*q^j*c by intros;ring,maxeq]

#print axioms physical_error
end LongCycleBounds.AdjustablePoleRadius
