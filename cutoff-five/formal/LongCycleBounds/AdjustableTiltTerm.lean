import LongCycleBounds.AdjustableLogisticCoefficients
import LongCycleBounds.QuadraticCutoffTiltMass

/-! Compare one coefficient of an arbitrary tilt against its contribution at
the nearest pair. Below the Taylor cutoff this is precisely the logistic
remainder. Above the cutoff the rotation contributes at most two. -/
noncomputable section
namespace LongCycleBounds.AdjustablePoleRadius
open Real PowerSeries MarkedTwo PoleBridge FixedCutoff QuadraticCutoff

def principalTerm (P : PowerSeries ℝ) (x R : ℝ) (j i : ℕ) : ℝ :=
  2 * (((R : ℂ) / nearestPole x) ^ (j + 1) * weightedCoeff P (nearestPole x) i).re

theorem principal_inside (P : PowerSeries ℝ) (x R : ℝ) {j i : ℕ} (hi : i ≤ j) :
    principalTerm P x R j i = weighted P R i * scaledCoeff (nearestLogistic x) R (j-i) := by
  let z := nearestPole x
  have zn : z ≠ 0 := norm_ne_zero_iff.mp ((nearestPole_norm x).trans_ne (radius_pos x).ne')
  have idx : i + (j-i+1) = j+1 := by omega
  have eq : ((R : ℂ) / z) ^ (j+1) * (((coeff i P : ℝ) : ℂ) * z^i) =
      ((R^(j+1) * coeff i P : ℝ) : ℂ) * z⁻¹ ^ (j-i+1) := by
    rw [div_pow, ← idx, pow_add z, inv_pow]
    push_cast
    field_simp
  simp only [principalTerm, weightedCoeff, weighted, scaledCoeff, nearestLogistic, coeff_mk]
  change 2 * (((R : ℂ) / z) ^ (j+1) * (((coeff i P : ℝ) : ℂ) * z^i)).re = _
  rw [eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← idx, pow_add]
  ring

theorem principal_outside (P : PowerSeries ℝ) (x : ℝ) {R : ℝ} (hr : radius x ≤ R)
    {j i : ℕ} (hi : j+1 ≤ i) : |principalTerm P x R j i| ≤ 2 * |weighted P R i| := by
  let ρ := radius x
  have rp : 0 < ρ := radius_pos x
  have Rp : 0 < R := rp.trans_le hr
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi
  have powers : (R/ρ)^(j+1)*ρ^(j+1+a) ≤ R^(j+1+a) := by
    rw [pow_add ρ (j+1) a, pow_add R (j+1) a, ← mul_assoc, ← mul_pow, div_mul_cancel₀ _ rp.ne']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ rp.le hr a) (pow_nonneg Rp.le _)
  unfold principalTerm
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  simp only [weightedCoeff, norm_mul, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Rp.le, nearestPole_norm, weighted, abs_mul,
    abs_of_nonneg (pow_nonneg Rp.le _), Real.norm_eq_abs]
  change (R/ρ)^(j+1) * (|coeff _ P| * ρ^(j+1+a)) ≤ _
  linarith only [mul_le_mul_of_nonneg_right powers (abs_nonneg (coeff (j+1+a) P))]

#print axioms principal_inside
#print axioms principal_outside
end LongCycleBounds.AdjustablePoleRadius
