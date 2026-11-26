import LongCycleBounds.MarkedMiddleBudget
import LongCycleBounds.FixedPoleMass

/-! Middle-angle strict sign from the centered nearest-pole gap, with the
pole moment index one above the logistic index and upper row index at least 512. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo.Half
open Real PoleBridge Band Bulk
open scoped Real

private theorem alpha_beta_bound {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) :
    |alpha u x| ≤ exp (-x) ∧ |beta u x| ≤ exp (-x) := by
  let r := exp (-x)
  have r0 : 0 < r := exp_pos _
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have up : 0 ≤ 1-u := by linarith
  have den : 0 < 1+r := by linarith
  have d2 : 1 ≤ (1+r)^2 := one_le_pow₀ (by linarith)
  have d3 : 1 ≤ (1+r)^3 := one_le_pow₀ (by linarith)
  have a : alpha u x=-(u*r)/(1+r)^2 := by unfold alpha time r; ring
  have b : beta u x=-(((1-u)*r)*(1-r))/(2*(1+r)^3) := by unfold beta time r; ring
  rw [a,b]
  have sd : 0 < 2*(1+r)^3 := by positivity
  rw [abs_div,abs_div,abs_of_pos (pow_pos den _),abs_of_pos sd,abs_neg,abs_neg,
    abs_of_nonneg (mul_nonneg hu r0.le),
    abs_of_nonneg (mul_nonneg (mul_nonneg up r0.le) (sub_nonneg.mpr r1))]
  change _ ≤ r ∧ _ ≤ r
  constructor
  · apply (div_le_iff₀ (pow_pos den _)).2
    exact (mul_le_of_le_one_left r0.le hu1).trans (le_mul_of_one_le_right r0.le d2)
  · apply (div_le_iff₀ sd).2
    have p : (1-u)*r*(1-r) ≤ r := by
      apply (mul_le_of_le_one_right (mul_nonneg up r0.le) (by linarith)).trans
      exact mul_le_of_le_one_left r0.le (by linarith)
    apply p.trans
    exact le_mul_of_one_le_right r0.le (by linarith)


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

theorem marked_middle_sign {u x : ℝ} (hu : 0≤u) (hu1 : u≤1) (hx : 16≤x)
    {n : ℕ} (hn : 512≤n) (upper : x≤3*sqrt ((n-1:ℕ):ℝ))
    (zero : normalizedRow u (n-1) x=0) :
    0<normalizedRow u n x*(-deriv (normalizedRow u (n-1)) x) := by
  let R := radius x
  let Y := scaledRow u (time x) R
  let V := scaledCoeff (logistic (time x)) R
  have rp : 0<R := radius_pos x
  have nc : (512:ℝ)≤n := by exact_mod_cast hn
  have np : (0:ℝ)<n := by linarith
  have x0 : 0≤x := by linarith
  have hs : 0<s x := div_pos pi_pos rp
  have su : s x≤1 := by nlinarith [circle x,sq_nonneg (c x),sq_nonneg (s x-1)]
  have cu : |c x|≤1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
    rw [sq_abs]
    nlinarith [circle x,sq_nonneg (s x)]
  have ang : 1≤(n:ℝ)*(s x)^2 := by
    have prev := fixed_central_angle (n:=n+1) (by omega) x x0
      (by simpa only [show n+1-2=n-1 by omega] using upper)
    simpa using prev
  have prev := logistic_total (by linarith : 8≤(n:ℝ)) (by omega : 1≤n-1)
    (by rw [Nat.sub_add_cancel (by omega : 1≤n)];linarith) x x0 ang
  rw [Nat.sub_add_cancel (by omega : 1≤n)] at prev
  change V (n-1)=2*(total (c x) (s x) n).re at prev
  have after := logistic_total (by linarith : 8≤(n:ℝ)) (by omega : 1≤n)
    (by push_cast;linarith) x x0 ang
  change V n=2*(total (c x) (s x) (n+1)).re at after
  have bias (j : ℕ) : |Y j-V j| < s x/12 := middle_row_bias hu hu1 hx j
  have yz : Y (n-1)=0 := by dsimp only [Y];rw [scaledRow_normalized,zero,mul_zero]
  have vz := bias (n-1)
  rw [yz,zero_sub,abs_neg] at vz
  have pt : |(total (c x) (s x) n).re| ≤ 1/8 := by
    rw [prev,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at vz
    linarith only [vz,su]
  have phase := central_pole_gap (c x) (s x) n (circle x) hs (by linarith) ang pt
  have dbl : s x < |V n-c x*V (n-1)| := by
    rw [after,prev,show ∀ z w : ℝ, 2*z-c x*(2*w)=2*(z-c x*w) by intro z w;ring,
      abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith only [phase]
  have gap : 5*s x/6 < |Y n| := by
    have u := abs_sub (V n) (c x*V (n-1))
    rw [abs_mul] at u
    have w := abs_sub (Y n) (Y n-V n)
    rw [sub_sub_cancel] at w
    nlinarith only [dbl,u,w,bias n,vz,mul_le_mul_of_nonneg_right cu (abs_nonneg (V (n-1)))]
  obtain ⟨r2,rad⟩ := middle_radius_budget hx
  change 2≤R at r2
  change exp (-x)*R^5<1/5 at rad
  have short (j : ℕ) : |Y j| ≤ R^2 := by
    have h := abs_sub (Y j-V j) (-V j)
    rw [sub_neg_eq_add,sub_add_cancel,abs_neg] at h
    have mass : |V j|≤R^2/2 := middle_logistic_mass x hx j
    nlinarith only [h,mass,bias j,su,r2,sq_nonneg (R-2)]
  obtain ⟨a,b⟩ := alpha_beta_bound hu hu1 x0
  have bounds (f : ℝ) (hf : |f|≤exp (-x)) (m : ℕ) (hm : m≤3) (j : ℕ) :
      |f*R^m*Y j| < 1/5 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg rp.le _)]
    have mp : R^m ≤ R^3 := pow_le_pow_right₀ (by linarith) hm
    have fs := mul_le_mul hf mp (pow_nonneg rp.le _) (exp_pos _).le
    have all := mul_le_mul fs (short j) (abs_nonneg _) (by positivity)
    nlinarith only [all,rad]
  have num := (abs_add_le (alpha u x*R^2*Y (n-2)) (beta u x*R^3*Y (n-3))).trans_lt
    (add_lt_add (bounds _ a 2 (by decide) _) (bounds _ b 3 le_rfl _))
  have ns : 1≤(n:ℝ)*s x := by
    nlinarith only [ang,mul_nonneg (mul_nonneg np.le hs.le) (sub_nonneg.mpr su)]
  have strong : |(alpha u x*R^2*Y (n-2)+beta u x*R^3*Y (n-3))/(n:ℝ)| < |Y n| := by
    apply lt_trans _ gap
    rw [abs_div,abs_of_pos np,div_lt_iff₀ np]
    nlinarith only [num,ns]
  have e := sign_of_scaled_gap u x R rp (n-3) (by
    have e1 : n-3+1=n-2 := by omega
    have e3 : n-3+3=n := by omega
    have er : ((n-3:ℕ):ℝ)+3=(n:ℝ) := by exact_mod_cast e3
    simpa only [e1,e3,er] using strong)
  simpa only [show n-3+2=n-1 by omega,show n-3+3=n by omega] using e

#print axioms marked_middle_sign
end LongCycleBounds.MarkedTwo.Half
