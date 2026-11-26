import LongCycleBounds.FixedFourCompactEstimate
import LongCycleBounds.FixedCutoffAnalyticAssembly

/-! Compact-range insertion at cutoff four, with upper row threshold 512. -/

noncomputable section

namespace LongCycleBounds.FixedFour

open Real Finset PoleBridge FixedCutoff MarkedTwo

private theorem pi_upper : π < (16 / 5 : ℝ) :=
  pi_lt_d2.trans (by norm_num)

private theorem radius_sq (x : ℝ) : radius x ^ 2 = x ^ 2 + π ^ 2 :=
  sq_sqrt (by positivity)

private theorem sine_lower {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16) : (3/17 : ℝ) ≤ s x := by
  have hρ : radius x ≤ 17 := by
    apply (sq_le_sq₀ (radius_pos x).le (by norm_num)).mp
    rw [radius_sq]
    have a := pow_le_pow_left₀ hx h16 2
    have b := pow_le_pow_left₀ pi_pos.le pi_upper.le 2
    nlinarith only [a,b]
  unfold s
  apply (le_div_iff₀ (radius_pos x)).2
  linarith only [hρ, pi_gt_three]

private theorem rotation_formula (x : ℝ) :
    compactRotation x = (c x : ℂ) - (s x : ℂ) * Complex.I := by
  have h := PoleBridge.pole_den x 1 le_rfl
  change (radius x : ℂ) / den x 1 = _
  rw [← h]
  apply Complex.ext <;> simp [PoleTails.pole]

private theorem exponent_real (x a b c : ℝ) :
    (((a : ℂ) * nearestPole x + (b : ℂ) * nearestPole x ^ 2) +
      (c : ℂ) * nearestPole x ^ 3).re =
      a*x + b*(x^2-π^2) + c*(x^3-3*π^2*x) := by
  have re : (nearestPole x).re = x := by simp [nearestPole, den, Complex.add_re, Complex.mul_re]
  have im : (nearestPole x).im = π := by simp [nearestPole, den, Complex.add_im, Complex.mul_im]
  have re2 : (nearestPole x ^ 2).re = x ^ 2 - π ^ 2 := by
    rw [pow_two, Complex.mul_re, re, im]
    ring
  have im2 : (nearestPole x ^ 2).im = 2*x*π := by
    rw [pow_two, Complex.mul_im, re, im]
    ring
  have re3 : (nearestPole x ^ 3).re = x ^ 3 - 3*π^2*x := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, Complex.mul_re, re2, im2, re, im]
    ring
  simp [Complex.add_re, Complex.mul_re, re, re2, re3]

/-- The cubic term cannot decrease the real pole exponent below the stated uniform cap. -/
theorem compact_amplitude_lower {w : ℕ → ℝ} (w1 : w 1 = 0)
    (unit : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : 0 ≤ x) :
    exp (-5) < ‖compactAmplitude w x‖ := by
  obtain ⟨⟨a0, _, _⟩, ⟨b0,b1,_⟩, ⟨c0,c1,_⟩⟩ := tilt_caps w w1 unit hx
  unfold compactAmplitude FixedCutoff.tiltValue
  rw [Complex.norm_exp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reduceAdd, pow_one]
  rw [exponent_real]
  apply exp_lt_exp.mpr
  have geom : -2*π^3 ≤ x^3-3*π^2*x := by
    nlinarith only [mul_nonneg (sq_nonneg (x-π)) (show 0≤x+2*π by positivity)]
  have cb := mul_le_mul_of_nonneg_left geom c0
  have cπ := mul_le_mul_of_nonneg_right c1 (pow_nonneg pi_pos.le 3)
  have bπ := mul_le_mul_of_nonneg_right b1 (sq_nonneg π)
  have p2 := pow_le_pow_left₀ pi_pos.le pi_upper.le 2
  have p3 := pow_le_pow_left₀ pi_pos.le pi_upper.le 3
  nlinarith only [cb,cπ,bπ,p2,p3,mul_nonneg a0 hx,mul_nonneg b0 (sq_nonneg x)]

private theorem error_relative {D σ : ℝ} (lo : exp (-5) < D) (hs : 3/17 ≤ σ) :
    1/1000000 < σ*D/16 := by
  have e1 : exp 1 ≤ (11/4 : ℝ) := by linarith [exp_one_lt_d9]
  have ep : exp 5 ≤ (11/4 : ℝ)^5 := by
    rw [show (5 : ℝ) = (5 : ℕ) * (1 : ℝ) by norm_num, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos 1).le e1 _
  have lower : ((11/4 : ℝ)^5)⁻¹ ≤ exp (-5) := by
    rw [exp_neg]
    exact inv_anti₀ (exp_pos _) ep
  have hl : (0 : ℝ) < D := (exp_pos _).trans lo
  nlinarith only [mul_le_mul_of_nonneg_right hs hl.le, lo, lower]

private theorem phase_gap {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16) {p : ℕ}
    (B : ℂ) (lo : exp (-5) < ‖B‖)
    (Y : ℕ → ℝ)
    (pred : |Y p - 2 * (B * compactRotation x ^ (p+1)).re| < 1/1000000)
    (succ : |Y (p+1) - 2 * (B * compactRotation x ^ (p+1+1)).re| < 1/1000000)
    (zero : Y p = 0) :
    (3/2) * (s x * ‖B‖) < |Y (p+1)| := by
  let z := compactRotation x
  let S := B*z^(p+1)
  have qr : ‖z‖ = 1 := compactRotation_norm x
  have hnS : ‖S‖ = ‖B‖ := by simp [S,norm_pow,qr]
  have hs := sine_lower hx h16
  have s0 : 0 ≤ s x := by linarith
  have s1 : s x ≤ 1 := (sq_le_sq₀ s0 (by norm_num)).mp
    (by nlinarith only [circle x, sq_nonneg (c x)])
  have hc : |c x| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by
    rw [sq_abs]
    nlinarith only [circle x, sq_nonneg (s x)])
  have rel := error_relative lo hs
  have er := pred.trans rel
  rw [zero,zero_sub,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at er
  change 2*|S.re| < s x*‖B‖/16 at er
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
  have adv := succ.trans rel
  rw [pow_succ,←mul_assoc] at adv
  change |Y (p+1)-2*(S*z).re| < s x*‖B‖/16 at adv
  have ed := abs_sub (Y (p+1)) (Y (p+1)-2*(S*z).re)
  rw [sub_sub_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ed
  nlinarith only [mul_le_mul_of_nonneg_left im s0, mul_le_of_le_one_left (abs_nonneg S.re) s1,
    er, adv, ed, rev, eC, rel]

private theorem short_cap {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16) {j : ℕ}
    (B : ℂ) (lo : exp (-5) < ‖B‖) (Y : ℕ → ℝ)
    (est : |Y j - 2 * (B * compactRotation x ^ (j+1)).re| < 1/1000000) :
    |Y j| ≤ 3 * ‖B‖ := by
  have rel := error_relative lo (sine_lower hx h16)
  have s0 : 0 ≤ s x := le_of_lt (div_pos pi_pos (radius_pos x))
  have s1 : s x ≤ 1 :=
    (sq_le_sq₀ s0 (by norm_num)).mp (by nlinarith only [circle x, sq_nonneg (c x)])
  have de := mul_le_of_le_one_left (norm_nonneg B) s1
  have tri := abs_sub_le (Y j) (2 * (B * compactRotation x ^ (j+1)).re) 0
  simp only [sub_zero, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at tri
  have rr := Complex.abs_re_le_norm (B * compactRotation x ^ (j+1))
  rw [norm_mul,norm_pow,compactRotation_norm,one_pow,mul_one] at rr
  linarith only [tri, rr, est, rel, de, norm_nonneg B]

private theorem weighted_radius {x : ℝ} (hx : 0 ≤ x) :
    exp (-x)*(radius x)^2 ≤ π^2 ∧ exp (-x)*(radius x)^3 ≤ π^3 ∧
    exp (-x)*(radius x)^4 ≤ π^4 := by
  let ρ := radius x
  let a := exp (-x/2)
  have a0 : 0 < a := exp_pos _
  have a1 : a ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have x0 : 0 ≤ x/2 := by linarith
  have e := sum_le_exp_of_nonneg x0 3
  norm_num [Finset.sum_range_succ] at e
  have p : π^2 ≥ 8 := by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) pi_gt_three.le 2]
  have g : ρ^2 ≤ π^2*exp (x/2) := by
    have u := mul_le_mul_of_nonneg_left e (sq_nonneg π)
    have v := mul_nonneg (sub_nonneg.mpr p) (sq_nonneg x)
    rw [show ρ^2=x^2+π^2 from radius_sq x]
    nlinarith only [u, v, mul_nonneg (sq_nonneg π) hx]
  have inv : a * exp (x/2) = 1 := by
    rw [show a=exp (-(x/2)) by dsimp [a]; congr 1; ring, ← exp_add, neg_add_cancel,exp_zero]
  have g' := mul_le_mul_of_nonneg_left g a0.le
  have b : a * ρ^2 ≤ π^2 := by
    calc
      _ ≤ a * (π^2 * exp (x/2)) := g'
      _ = _ := by rw [mul_left_comm, inv, mul_one]
  have eq : exp (-x) = a^2 := by
    rw [pow_two, show a=exp (-x/2) by rfl, ← exp_add]
    congr 1
    ring
  have b2 : exp (-x)*ρ^2 ≤ π^2 := by
    rw [eq, pow_two, mul_assoc]
    exact (mul_le_mul_of_nonneg_left b a0.le).trans (mul_le_of_le_one_left (sq_nonneg π) a1)
  have b4 : exp (-x)*ρ^4 ≤ π^4 := by
    rw [eq]
    have cut := pow_le_pow_left₀ (mul_nonneg a0.le (sq_nonneg ρ)) b 2
    simpa only [mul_pow, ←pow_mul, show (2*2:ℕ)=4 by decide] using cut
  have b3 : exp (-x)*ρ^3 ≤ π^3 := by
    have ρ0 := (radius_pos x).le
    apply (sq_le_sq₀ (mul_nonneg (exp_pos _).le (pow_nonneg ρ0 _)) (pow_nonneg pi_pos.le _)).mp
    have m := mul_le_mul b2 b4 (mul_nonneg (exp_pos _).le (pow_nonneg ρ0 _)) (sq_nonneg π)
    convert m using 1 <;> ring
  exact ⟨b2,b3,b4⟩

private theorem compact_drift_bound {w : ℕ→ℝ} (unit : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    {x : ℝ} (hx : 0≤x) :
    (∑ i∈range 3, |drift w (i+1) x| * (radius x)^(i+2)) ≤
      (16/5 : ℝ)^2+(16/5 : ℝ)^3/2+(16/5 : ℝ)^4/6 := by
  obtain ⟨a,b,c⟩ := weighted_radius hx
  have d := drift_cost_cap w unit hx (radius_pos x).le
  have p2 := pow_le_pow_left₀ pi_pos.le pi_upper.le 2
  have p3 := pow_le_pow_left₀ pi_pos.le pi_upper.le 3
  have p4 := pow_le_pow_left₀ pi_pos.le pi_upper.le 4
  nlinarith only [a,b,c,d,p2,p3,p4]

/-- At every genuine lower zero with (0\le x\le16), the compact test
works from upper row index 512 over the entire independent weight square. -/
theorem compact_gap {w : ℕ → ℝ} (w1 : w 1 = 0) (tail : ∀ a ≥ 4, w a = 1)
    (unit : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16)
    {p : ℕ} (hp : 511 ≤ p) (zero : CycleProfile.normalizedRow w p x = 0) :
    ScaledGapAt w 4 p x := by
  let B := compactAmplitude w x
  let Y := compactRow w x
  have hY : Y p = 0 := by
    change scaledCoeff (profileSeries w 4 x) (radius x) p = 0
    rw [scaled_eq_gain (by decide : 2 ≤ 4) w w1 tail hx, zero, mul_zero]
  have lo : exp (-5) < ‖B‖ := compact_amplitude_lower w1 unit hx
  have est (j : ℕ) (hj : 508 ≤ j) :=
    compact_error w1 unit hx h16 hj
  have adv := phase_gap hx h16 B lo Y (est p (by omega)) (est (p+1) (by omega)) hY
  have shorts (i : ℕ) (hi : i ∈ range 3) : |Y (p+1-(i+2))| ≤ 3*‖B‖ := by
    have hi' := mem_range.mp hi
    exact short_cap hx h16 B lo Y (est _ (by omega))
  let F := (16/5 : ℝ)^2+(16/5 : ℝ)^3/2+(16/5 : ℝ)^4/6
  have cap :
      |∑ i∈range 3, drift w (i+1) x * (radius x)^(i+2) * Y (p+1-(i+2))| ≤
        F * (3*‖B‖) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ i∈range 3, (|drift w (i+1) x| * (radius x)^(i+2))*(3*‖B‖) := by
        apply sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos (radius_pos x) _)]
        exact mul_le_mul_of_nonneg_left (shorts i hi)
          (mul_nonneg (abs_nonneg _) (pow_nonneg (radius_pos x).le _))
      _ = _ * (3*‖B‖) := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (compact_drift_bound unit hx) (by positivity)
  change |(∑ i∈range 3, drift w (i+1) x * (radius x)^(i+2) * Y (p+1-(i+2))) /
    ((p:ℝ)+1)| < |Y (p+1)|
  apply lt_trans _ adv
  rw [abs_div, abs_of_pos (by positivity : 0<(p:ℝ)+1), div_lt_iff₀ (by positivity)]
  apply cap.trans_lt
  have H : (512:ℝ) ≤ (p:ℝ)+1 := by exact_mod_cast (show 512 ≤ p+1 by omega)
  have hs := sine_lower hx h16
  have pr : 0 < ‖B‖ := (exp_pos _).trans lo
  have num : F*3 < (3/2)*(3/17)*(512 : ℝ) := by norm_num [F]
  have scale := mul_le_mul hs H (by norm_num) (by positivity)
  have gap : F*3 < (3/2)*(s x*((p:ℝ)+1)) := by linarith only [num,scale]
  nlinarith only [mul_lt_mul_of_pos_right gap pr]

#print axioms compact_amplitude_lower
#print axioms compact_gap

end LongCycleBounds.FixedFour
