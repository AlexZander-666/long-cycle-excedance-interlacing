import LongCycleBounds.FixedFourCoefficients
import LongCycleBounds.FixedCutoffAnalyticAssembly

/-! Numerical middle-angle insertion at cutoff four. -/

noncomputable section

namespace LongCycleBounds.FixedFour

open Real PoleBridge Band Bulk MarkedTwo FixedCutoff Finset

private theorem radius_budget {x : ℝ} (hx : 16 ≤ x) :
    16 ≤ radius x ∧ exp (-x) * (radius x)^6 < 16/5 := by
  let R := radius x
  have rp : 0 < R := radius_pos x
  have rsq : R^2 = x^2+π^2 := sq_sqrt (by positivity)
  have x0 : 0 ≤ x := by linarith
  have x2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) hx 2
  have r16 : 16 ≤ R := (sq_le_sq₀ (by norm_num) rp.le).mp (by
    nlinarith only [rsq,x2,sq_nonneg π])
  have rux : R ≤ (33/32)*x := by
    apply (sq_le_sq₀ rp.le (by positivity)).mp
    have bp : π ≤ 16/5 := (pi_lt_d2.trans (by norm_num)).le
    nlinarith only [rsq,x2,pow_le_pow_left₀ pi_pos.le bp 2]
  let h := (x-16)/6
  have ru : R ≤ (33/2)*exp h := by
    have he := add_one_le_exp h
    dsimp [h] at he ⊢
    linarith only [he,rux,hx]
  have pow := pow_le_pow_left₀ rp.le ru 6
  rw [mul_pow, ←exp_nat_mul] at pow
  have numeric : ((5 : ℝ)/16)*(33/2)^6 < exp 16 := by
    have b : (8/3:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have t := pow_le_pow_left₀ (by norm_num : 0≤(8/3:ℝ)) b 16
    rw [← exp_nat_mul] at t
    norm_num at t
    linarith only [t]
  have e : exp (-x)*exp (6*h)=exp (-16) := by
    rw [←exp_add]
    congr 1
    dsimp [h]
    ring
  refine ⟨r16, ?_⟩
  apply (mul_le_mul_of_nonneg_left pow (exp_pos (-x)).le).trans_lt
  change exp (-x)*((33/2)^6*exp (6*h)) < _
  rw [show exp (-x)*((33/2)^6*exp (6*h))=(33/2)^6*(exp (-x)*exp (6*h)) by ring,
    e,exp_neg,←div_eq_mul_inv,div_lt_iff₀ (exp_pos _)]
  linarith only [numeric]

private theorem cubic_budget {R : ℝ} (hR : 16 ≤ R) :
    R + R^2/2+R^3/6 ≤ (21/100)*R^3 := by
  have r0 : 0 ≤ R := by linarith
  have R2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) hR 2
  have P := mul_le_mul_of_nonneg_right R2 r0
  have Q := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
  nlinarith only [P,Q,pow_nonneg r0 3]

private theorem tilt_bias {w : ℕ → ℝ} (w1 : w 1 = 0)
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : 16 ≤ x) (j : ℕ) :
    |scaledCoeff (profileSeries w 4 x) (radius x) j -
      scaledCoeff (logistic (time x)) (radius x) j| < s x/4 := by
  let R := radius x
  let b := fun a ↦ tiltCoefficient w a x
  let v := cost b R 3
  have rp : 0<R := radius_pos x
  have x0 : 0 ≤ x := by linarith
  have pos : 0≤v := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg rp.le _)
  obtain ⟨r16,small⟩ := radius_budget hx
  have cap : v ≤ (21/100)*exp (-x)*R^3 := by
    apply (tilt_cost_caps w w1 unit x0 rp.le).2.trans
    have p := mul_le_mul_of_nonneg_left (cubic_budget r16) (exp_pos (-x)).le
    nlinarith only [p]
  have cum : v*R^3 < 27/40 := by
    nlinarith only [mul_le_mul_of_nonneg_right cap (pow_nonneg rp.le 3),small]
  have sm : v≤1/2 := by
    have r2 : (2:ℝ)≤R := by linarith
    have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) r2 3
    nlinarith only [mul_nonneg pos (show (0:ℝ)≤R^3-8 by linarith),cum]
  have e : exp v-1≤2*v := by
    have a := exp_bound_div_one_sub_of_interval pos (by linarith : v<1)
    have br : 1/(1-v)≤1+2*v := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [mul_nonneg pos (show 0≤1-2*v by linarith)]
    linarith only [a,br]
  have bias := signed_tilt_bias b rp.le (show 0≤R^2/2 by positivity)
    (logistic (time x)) 3 j (fun i _ ↦ middle_logistic_mass x hx i)
  change |scaledCoeff (profileSeries w 4 x) (radius x) j -
      scaledCoeff (logistic (time x)) (radius x) j| ≤ R^2/2*(exp v-1) at bias
  change _ < (π/R)/4
  rw [div_div,lt_div_iff₀ (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right bias rp.le,
    mul_le_mul_of_nonneg_left e (show 0≤R^3/2 by positivity),cum,pi_gt_three]

private theorem logistic_total {n j : ℕ} (hn : 8≤(n:ℝ)) (hj : 1≤j)
    (hi : (n:ℝ)≤2*((j+1:ℕ):ℝ)) (x : ℝ) (hx : 0≤x) (ang : 1≤(n:ℝ)*(s x)^2) :
    scaledCoeff (logistic (time x)) (radius x) j=2*(total (c x) (s x) (j+1)).re := by
  rw [logistic_scaled_moment x hj]
  congr 1
  rw [time,scaledMoment_poles _ (by omega) _ _ hx]
  have he := congrArg Complex.re (complete_normalization x n (j+1) hn ang hi)
  have eq : radius x^(j+1)*(oddPoleSum (j+1) x).re=2*(total (c x) (s x) (j+1)).re := by
    simpa [Complex.mul_re,←Complex.ofReal_pow] using he
  linarith only [eq]

private theorem middle_phase {n : ℕ} (hn : 512 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (angle : 1 ≤ (n:ℝ)*(s x)^2) (Y : ℕ → ℝ)
    (bias : ∀ j, |Y j-scaledCoeff (logistic (time x)) (radius x) j| < s x/4)
    (zero : Y (n-1) = 0) : s x/2 < |Y n| := by
  let V := scaledCoeff (logistic (time x)) (radius x)
  have nc : (512:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<s x := div_pos pi_pos (radius_pos x)
  have su : s x≤1 := (sq_le_sq₀ hs.le (by norm_num)).mp (by
    nlinarith only [circle x,sq_nonneg (c x)])
  have cu : |c x|≤1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
    rw [sq_abs]
    nlinarith only [circle x,sq_nonneg (s x)]
  have prev := logistic_total (by linarith : 8≤(n:ℝ)) (by omega : 1≤n-1)
    (by rw [Nat.sub_add_cancel (by omega : 1≤n)];linarith) x hx angle
  rw [Nat.sub_add_cancel (by omega : 1≤n)] at prev
  change V (n-1)=2*(total (c x) (s x) n).re at prev
  have after := logistic_total (by linarith : 8≤(n:ℝ)) (by omega : 1≤n)
    (by push_cast;linarith) x hx angle
  change V n=2*(total (c x) (s x) (n+1)).re at after
  have bv (j : ℕ) : |Y j-V j|<s x/4 := bias j
  have vz := bv (n-1)
  rw [zero,zero_sub,abs_neg] at vz
  have pt : |(total (c x) (s x) n).re| ≤ 1/8 := by
    rw [prev,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at vz
    linarith only [vz,su]
  have phase := central_pole_gap (c x) (s x) n (circle x) hs (by linarith) angle pt
  have dbl : s x < |V n-c x*V (n-1)| := by
    rw [after,prev,show ∀ z w : ℝ, 2*z-c x*(2*w)=2*(z-c x*w) by intro z w;ring,
      abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith only [phase]
  have u := abs_sub (V n) (c x*V (n-1))
  rw [abs_mul] at u
  have w := abs_sub (Y n) (Y n-V n)
  rw [sub_sub_cancel] at w
  nlinarith only [dbl,u,w,bv n,vz,mul_le_mul_of_nonneg_right cu (abs_nonneg (V (n-1)))]

/-- The middle sign test applies from upper index 512 and down to the same
endpoint (x=16) as the compact estimate. -/
theorem middle_gap {w : ℕ → ℝ} (w1 : w 1 = 0) (tail : ∀ a ≥ 4, w a = 1)
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : 16 ≤ x)
    {p : ℕ} (hp : 511 ≤ p) (outer : x ≤ 3*sqrt (p:ℝ))
    (zero : CycleProfile.normalizedRow w p x = 0) : ScaledGapAt w 4 p x := by
  let n := p+1
  let R := radius x
  let Y := scaledCoeff (profileSeries w 4 x) R
  let V := scaledCoeff (logistic (time x)) R
  have x0 : 0 ≤ x := by linarith
  have rp : 0 < R := radius_pos x
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by dsimp [n]; omega)
  have hs : 0<s x := div_pos pi_pos rp
  have su : s x≤1 := (sq_le_sq₀ hs.le (by norm_num)).mp (by
    nlinarith only [circle x,sq_nonneg (c x)])
  obtain ⟨r16,small⟩ := radius_budget hx
  have ang : 1 ≤ (n:ℝ)*(s x)^2 := by
    have v := fixed_central_angle (n:=p+2) (by omega) x x0
      (by simpa only [Nat.add_sub_cancel] using outer)
    simpa [n,Nat.cast_add] using v
  have ns : 1≤(n:ℝ)*s x := by
    nlinarith only [ang,mul_nonneg (mul_nonneg np.le hs.le) (sub_nonneg.mpr su)]
  have yz : Y (n-1)=0 := by
    change scaledCoeff (profileSeries w 4 x) (radius x) (n-1)=0
    rw [show n-1=p by rfl,scaled_eq_gain (by decide : 2≤4) w w1 tail x0,
      zero,mul_zero]
  have bias (j : ℕ) : |Y j-V j| < s x/4 := tilt_bias w1 unit hx j
  have phase := middle_phase (show 512≤n by dsimp [n]; omega) x0 ang Y bias yz
  have sh (j : ℕ) : |Y j|≤(3/5)*R^2 := by
    have z := abs_sub_le (Y j) (V j) 0
    simp only [sub_zero] at z
    have h : |V j|≤R^2/2 := middle_logistic_mass x hx j
    have sq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) r16 2
    nlinarith only [z,h,bias j,su,sq]
  have d := drift_cost_cap w unit x0 rp.le
  have d' : (∑ i∈range 3, |drift w (i+1) x| * R ^ (i+2)) ≤
      (21/100)*exp (-x)*R^4 := by
    have u := mul_le_mul_of_nonneg_right (cubic_budget r16) (mul_nonneg (exp_pos (-x)).le rp.le)
    change (∑ i∈range 3, |drift w (i+1) x| * R ^ (i+2)) ≤ _ at d
    nlinarith only [d,u]
  have cap : |∑ i∈range 3, drift w (i+1) x * R^(i+2)*Y (n-(i+2))| < 1/2 := by
    apply (abs_sum_le_sum_abs ..).trans_lt
    calc
      _ ≤ ∑ i∈range 3, (|drift w (i+1) x| * R^(i+2))*((3/5)*R^2) := by
        apply sum_le_sum
        intro i _
        rw [abs_mul,abs_mul,abs_of_pos (pow_pos rp _)]
        exact mul_le_mul_of_nonneg_left (sh _) (mul_nonneg (abs_nonneg _) (pow_nonneg rp.le _))
      _ ≤ ((21/100)*exp (-x)*R^4)*((3/5)*R^2) := by
        rw [←sum_mul]
        exact mul_le_mul_of_nonneg_right d' (by positivity)
      _ < _ := by nlinarith only [small]
  change |(∑ i∈range 3, drift w (i+1) x * R^(i+2)*Y (n-(i+2)))/((p:ℝ)+1)| < |Y n|
  rw [← show (n:ℝ)=(p:ℝ)+1 by simp [n]]
  apply lt_trans _ phase
  rw [abs_div,abs_of_pos np,div_lt_iff₀ np]
  nlinarith only [cap,ns]

#print axioms middle_gap

end LongCycleBounds.FixedFour
