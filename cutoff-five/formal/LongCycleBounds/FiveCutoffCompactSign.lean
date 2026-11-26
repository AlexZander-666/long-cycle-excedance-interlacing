import LongCycleBounds.AdjustableProfileError
import LongCycleBounds.FixedCutoffAnalyticAssembly
import LongCycleBounds.CycleProfileInsertion

/-! Bridge the two scalar cell inequalities to the true derivative sign at
any root of the predecessor, from upper order 49. The elementary rotation
argument is the cutoff-independent one used in FixedFour49Compact. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Finset PoleBridge FixedCutoff MarkedTwo AdjustablePoleRadius

private theorem rotation_formula (x : ℝ) :
    compactRotation x = (c x : ℂ) - (s x : ℂ) * Complex.I := by
  have h := PoleBridge.pole_den x 1 le_rfl
  change (radius x : ℂ) / den x 1 = _
  rw [← h]
  apply Complex.ext <;> simp [PoleTails.pole]

private theorem phase_gap {x : ℝ} {p : ℕ}
    {ε : ℝ} (B : ℂ)
    (Y : ℕ → ℝ)
    (pred : |Y p - 2 * (B * compactRotation x ^ (p+1)).re| < ε*(s x*‖B‖))
    (succ : |Y (p+1) - 2 * (B * compactRotation x ^ (p+1+1)).re| < ε*(s x*‖B‖))
    (zero : Y p = 0) :
    (2-3*ε) * (s x * ‖B‖) < |Y (p+1)| := by
  let z := compactRotation x
  let S := B*z^(p+1)
  have qr : ‖z‖ = 1 := compactRotation_norm x
  have hnS : ‖S‖ = ‖B‖ := by simp [S,norm_pow,qr]
  have s0 : 0 ≤ s x := (div_pos pi_pos (radius_pos x)).le
  have s1 : s x ≤ 1 := (sq_le_sq₀ s0 (by norm_num)).mp
    (by nlinarith only [circle x, sq_nonneg (c x)])
  have hc : |c x| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by
    rw [sq_abs]
    nlinarith only [circle x, sq_nonneg (s x)])
  have er := pred
  rw [zero,zero_sub,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at er
  change 2*|S.re| < ε*(s x*‖B‖) at er
  have im := Complex.norm_le_abs_re_add_abs_im S
  rw [hnS] at im
  have step : (S*z).re = c x*S.re+s x*S.im := by
    rw [show z=(c x:ℂ)-(s x:ℂ)*Complex.I from rotation_formula x]
    simp [Complex.mul_re,Complex.sub_re,Complex.sub_im]
    ring
  have rev := abs_sub (S*z).re (c x*S.re)
  rw [step,add_sub_cancel_left,abs_mul,abs_of_nonneg s0,←step] at rev
  have eC : |c x*S.re|≤|S.re| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hc
  have adv := succ
  rw [pow_succ,←mul_assoc] at adv
  change |Y (p+1)-2*(S*z).re| < ε*(s x*‖B‖) at adv
  have ed := abs_sub (Y (p+1)) (Y (p+1)-2*(S*z).re)
  rw [sub_sub_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ed
  nlinarith only [mul_le_mul_of_nonneg_left im s0, mul_le_of_le_one_left (abs_nonneg S.re) s1,
    er, adv, ed, rev, eC]

private theorem short_cap {x : ℝ} {j : ℕ}
    {ε : ℝ} (e0 : 0≤ε) (B : ℂ) (Y : ℕ → ℝ)
    (est : |Y j - 2 * (B * compactRotation x ^ (j+1)).re| < ε*(s x*‖B‖)) :
    |Y j| ≤ (2+ε) * ‖B‖ := by
  have s0 : 0 ≤ s x := le_of_lt (div_pos pi_pos (radius_pos x))
  have s1 : s x ≤ 1 :=
    (sq_le_sq₀ s0 (by norm_num)).mp (by nlinarith only [circle x, sq_nonneg (c x)])
  have de := mul_le_of_le_one_left (norm_nonneg B) s1
  have tri := abs_sub_le (Y j) (2 * (B * compactRotation x ^ (j+1)).re) 0
  simp only [sub_zero, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at tri
  have rr := Complex.abs_re_le_norm (B * compactRotation x ^ (j+1))
  rw [norm_mul,norm_pow,compactRotation_norm,one_pow,mul_one] at rr
  linarith only [tri, rr, est, mul_le_mul_of_nonneg_left de e0, norm_nonneg B]

theorem compact_gap_of_cell {w : ℕ → ℝ} (w1 : w 1 = 0) (tail : ∀ a ≥ 5, w a = 1)
    {x R : ℝ} (hx : 0 ≤ x) (hr : radius x < R) (hthird : R ≤ ‖den x 3‖)
    {p : ℕ} (hp : 48 ≤ p) (zero : CycleProfile.normalizedRow w p x = 0)
    (cell : let b := fun a ↦ tiltCoefficient w a x
            max (radius x) (radius x*R/(2*π^2)) * (radius x/R)^44 * exp (cost b R 4) <
              (3/1000) * (s x * ‖tiltValue b 4 (nearestPole x)‖))
    (budget : (∑ i ∈ range 4, |drift w (i+1) x| * (radius x)^(i+2)) ≤ (48/5)*s x) :
    ScaledGapAt w 5 p x := by
  let b := fun a ↦ tiltCoefficient w a x
  let B := tiltValue b 4 (nearestPole x)
  let Y := scaledCoeff (profileSeries w 5 x) (radius x)
  let ε : ℝ := 3/1000
  let K : ℝ := 48/5
  have e0 : 0 < ε := by norm_num [ε]
  have g0 : 0 < 2-3*ε := by norm_num [ε]
  have num : (2+ε)*K < 49*(2-3*ε) := by norm_num [ε,K]
  have hY : Y p = 0 := by
    dsimp only [Y]
    rw [scaled_eq_gain (by decide : 2 ≤ 5) w w1 tail hx,zero,mul_zero]
  have lo := (tilt_value_bounds b 4 (nearestPole x) (nearestPole_norm x).le).1
  have est (j : ℕ) (hj : 44 ≤ j) :
      |Y j - 2*(B*compactRotation x^(j+1)).re| < ε*(s x*‖B‖) := by
    dsimp only [Y]
    rw [scaled_eq_gain (by decide : 2 ≤ 5) w w1 tail hx]
    exact profile_error_from_44 w w1 tail hx hr hthird j hj cell
  have adv := phase_gap B Y (est p (by omega)) (est (p+1) (by omega)) hY
  have shorts (i : ℕ) (hi : i ∈ range 4) : |Y (p+1-(i+2))| ≤ (2+ε)*‖B‖ := by
    have hi' := mem_range.mp hi
    exact short_cap e0.le B Y (est _ (by omega))
  have s0 : 0 < s x := div_pos pi_pos (radius_pos x)
  have cap :
      |∑ i∈range 4, drift w (i+1) x * (radius x)^(i+2) * Y (p+1-(i+2))| ≤
        (K * s x) * ((2+ε)*‖B‖) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ i∈range 4, (|drift w (i+1) x| * (radius x)^(i+2))*((2+ε)*‖B‖) := by
        apply sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos (radius_pos x) _)]
        exact mul_le_mul_of_nonneg_left (shorts i hi)
          (mul_nonneg (abs_nonneg _) (pow_nonneg (radius_pos x).le _))
      _ = _ * ((2+ε)*‖B‖) := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right budget (by positivity)
  change |(∑ i∈range 4, drift w (i+1) x * (radius x)^(i+2) * Y (p+1-(i+2))) /
    ((p:ℝ)+1)| < |Y (p+1)|
  apply lt_trans _ adv
  rw [abs_div, abs_of_pos (by positivity : 0<(p:ℝ)+1), div_lt_iff₀ (by positivity)]
  apply cap.trans_lt
  have H : (49:ℝ) ≤ (p:ℝ)+1 := by exact_mod_cast (show 49 ≤ p+1 by omega)
  have pr : 0 < ‖B‖ := (exp_pos _).trans_le lo
  have gap : (2+ε)*K < ((p:ℝ)+1)*(2-3*ε) := num.trans_le
    (mul_le_mul_of_nonneg_right H g0.le)
  nlinarith only [mul_lt_mul_of_pos_right gap (mul_pos s0 pr)]


theorem compact_sign_of_cell {w : ℕ → ℝ} (w1 : w 1 = 0) (tail : ∀ a ≥ 5, w a = 1)
    {x R : ℝ} (hx : 0 ≤ x) (hr : radius x < R) (hthird : R ≤ ‖den x 3‖)
    {p : ℕ} (hp : 48 ≤ p) (zero : CycleProfile.normalizedRow w p x = 0)
    (cell : let b := fun a ↦ tiltCoefficient w a x
            max (radius x) (radius x*R/(2*π^2)) * (radius x/R)^44 * exp (cost b R 4) <
              (3/1000) * (s x * ‖tiltValue b 4 (nearestPole x)‖))
    (budget : (∑ i ∈ range 4, |drift w (i+1) x| * (radius x)^(i+2)) ≤ (48/5)*s x) :
    0 < CycleProfile.normalizedRow w (p+1) x * (-deriv (CycleProfile.normalizedRow w p) x) := by
  exact scaled_gap_to_normalized_sign (by decide : 2 ≤ 5) (by omega : 5-1 ≤ p)
    w w1 tail hx (radius_pos x)
    (CycleProfile.normalizedRow_insertion (by decide : 3 ≤ 5) (by omega) w w1 tail x)
    (compact_gap_of_cell w1 tail hx hr hthird hp zero cell budget)

#print axioms compact_gap_of_cell
#print axioms compact_sign_of_cell
end LongCycleBounds.FiveCutoff
