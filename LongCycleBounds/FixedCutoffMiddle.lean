import LongCycleBounds.FixedCutoffSignedTilt
import LongCycleBounds.MarkedMiddleBudget
import LongCycleBounds.FixedPoleMass

/-! The middle-angle sign test for any signed finite tilt with a fixed degree.
The upper degree only affects the cutoff X in the exponential budget. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real PoleBridge Band Bulk MarkedTwo Finset Filter
open scoped Real Topology

theorem coarse_cost {d : ℕ} {R r : ℝ} (hr : 0≤r) (hR : 1≤R) (b : ℕ→ℝ)
    (hb : ∀ i, 1≤ i → i≤d → |b i|≤r) : cost b R d ≤ d*r*R^d := by
  unfold cost
  calc
    _ ≤ ∑ _i ∈ range d, r*R^d := by
      apply sum_le_sum
      intro i hi
      have h : i+1≤d := mem_range.mp hi
      exact mul_le_mul (hb _ (by omega) h) (pow_le_pow_right₀ hR h)
        (pow_nonneg (by linarith) _) hr
    _ = _ := by simp;ring

/-- The same real cutoff works at every large n and for every profile in the unit cube. -/
theorem eventual_middle_budget (d : ℕ) :
    ∃ X : ℝ, 16≤X ∧ ∀ x≥X, (d:ℝ)*exp (-x)*(radius x)^(d+4) < 1/32 := by
  let a : ℝ := 1/(64*((d:ℝ)+1)*2^(d+4))
  have ap : 0<a := by dsimp [a];positivity
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((isLittleO_pow_exp_atTop (n:=d+4)).bound ap)
  refine ⟨max A 16,le_max_right ..,?_⟩
  intro x hx
  have x16 := (le_max_right A 16).trans hx
  have xx : 0≤x := by linarith
  have rad : radius x≤2*x := by
    have sq : (radius x)^2=x^2+π^2 := sq_sqrt (by positivity)
    apply (sq_le_sq₀ (radius_pos x).le (by positivity)).mp
    nlinarith only [sq,pi_lt_four,pi_pos,mul_nonneg (by linarith : 0≤x-4) (by linarith : 0≤x+4),mul_pos (by linarith [pi_lt_four] : 0<4-π) (by linarith [pi_pos] : 0<4+π)]
  have h := hA x ((le_max_left A 16).trans hx)
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg xx _),abs_of_pos (exp_pos x)] at h
  rw [exp_neg,←div_eq_mul_inv]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (radius_pos x).le rad (d+4)) (by positivity)) _
  rw [mul_pow]
  have e : (d:ℝ)/exp x * (2^(d+4)*x^(d+4)) ≤ (d:ℝ)*2^(d+4)*a := by
    have s := mul_le_mul_of_nonneg_left h (by positivity : 0≤(d:ℝ)*2^(d+4)/exp x)
    field_simp at s ⊢
    linarith only [s]
  apply e.trans_lt
  dsimp [a]
  field_simp
  nlinarith only [show (0:ℝ)≤d by positivity,show 0<(2:ℝ)^(d+4) by positivity,
    mul_nonneg (show (0:ℝ)≤d by positivity) (show 0≤(2:ℝ)^(d+4) by positivity)]

theorem middle_tilt_bias {d : ℕ} {x : ℝ} (hx : 16≤x) (_hd : 1≤d) (b : ℕ→ℝ)
    (hb : ∀ i, 1≤ i → i≤d → |b i|≤exp (-x))
    (budget : (d:ℝ)*exp (-x)*(radius x)^(d+4)<1/32) (j : ℕ) :
    |scaledCoeff (tilt b d*logistic (time x)) (radius x) j -
      scaledCoeff (logistic (time x)) (radius x) j| < s x/32 := by
  let R := radius x
  let v := cost b R d
  have rp : 0<R := radius_pos x
  have r2 : 2≤R := (middle_radius_budget hx).1
  have r1 : 1≤R := by linarith
  have pos : 0≤v := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg rp.le _)
  have cap : v ≤ (d:ℝ)*exp (-x)*R^d := coarse_cost (exp_pos _).le r1 b hb
  have cum : v*R^3<1/32 := by
    have a := mul_le_mul_of_nonneg_right cap (pow_nonneg rp.le 3)
    have p := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ r1 (show d+3≤d+4 by omega))
      (show 0≤(d:ℝ)*exp (-x) by positivity)
    rw [pow_add] at p
    change (d:ℝ)*exp (-x)*R^(d+4)<_ at budget
    nlinarith only [a,p,budget]
  have sm : v≤1/2 := by
    have h := le_mul_of_one_le_right pos (one_le_pow₀ r1 (n:=3))
    linarith only [h,cum]
  have e : exp v-1≤2*v := by
    have a := exp_bound_div_one_sub_of_interval pos (by linarith : v<1)
    have b' : 1/(1-v)≤1+2*v := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [mul_nonneg pos (show 0≤1-2*v by linarith)]
    linarith
  have bias := signed_tilt_bias b rp.le (show 0≤R^2/2 by positivity)
    (logistic (time x)) d j (fun i _ ↦ middle_logistic_mass x hx i)
  change _ ≤ R^2/2*(exp v-1) at bias
  change _ < (π/R)/32
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


theorem middle_root_gap {n d : ℕ} (hn : 1024≤n) {x : ℝ} (hx : 16≤x)
    (hd : 1≤d) (upper : x≤3*sqrt ((n-1:ℕ):ℝ)) (b : ℕ→ℝ)
    (hb : ∀ i, 1≤ i → i≤d → |b i|≤exp (-x))
    (budget : (d:ℝ)*exp (-x)*(radius x)^(d+4)<1/32)
    (zero : scaledCoeff (tilt b d*logistic (time x)) (radius x) (n-1)=0) :
    15*s x/16 < |scaledCoeff (tilt b d*logistic (time x)) (radius x) n| := by
  let R := radius x
  let Y := scaledCoeff (tilt b d*logistic (time x)) R
  let V := scaledCoeff (logistic (time x)) R
  have rp : 0<R := radius_pos x
  have nc : (1024:ℝ)≤n := by exact_mod_cast hn
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
  have bias (j : ℕ) : |Y j-V j| < s x/32 := middle_tilt_bias hx hd b hb budget j
  have yz : Y (n-1)=0 := zero
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
  have gap : 15*s x/16 < |Y n| := by
    have u := abs_sub (V n) (c x*V (n-1))
    rw [abs_mul] at u
    have w := abs_sub (Y n) (Y n-V n)
    rw [sub_sub_cancel] at w
    nlinarith only [dbl,u,w,bias n,vz,mul_le_mul_of_nonneg_right cu (abs_nonneg (V (n-1)))]
  exact gap

/-- The insertion may contain all d differences of neighboring marks. -/
theorem middle_insertion_gap {n d : ℕ} (hn : 1024≤n) {x : ℝ} (hx : 16≤x)
    (hd : 1≤d) (upper : x≤3*sqrt ((n-1:ℕ):ℝ)) (b C : ℕ→ℝ)
    (hb : ∀ i, 1≤ i → i≤d → |b i|≤exp (-x))
    (hC : ∀ i, 1≤ i → i≤d → |C i|≤exp (-x))
    (budget : (d:ℝ)*exp (-x)*(radius x)^(d+4)<1/32)
    (zero : scaledCoeff (tilt b d*logistic (time x)) (radius x) (n-1)=0) :
    let R := radius x
    let Y := scaledCoeff (tilt b d*logistic (time x)) R
    |(∑ i ∈ range d, C (i+1)*R^(i+2)*Y (n-(i+2)))/(n:ℝ)| < |Y n| := by
  dsimp only
  let R := radius x
  let Y := scaledCoeff (tilt b d*logistic (time x)) R
  let V := scaledCoeff (logistic (time x)) R
  have rp : 0<R := radius_pos x
  have r2 : 2≤R := (middle_radius_budget hx).1
  have r1 : 1≤R := by linarith
  have hs : 0<s x := div_pos pi_pos rp
  have su : s x≤1 := by nlinarith [circle x,sq_nonneg (c x),sq_nonneg (s x-1)]
  have sh (j : ℕ) : |Y j|≤R^2 := by
    have e := middle_tilt_bias hx hd b hb budget j
    change |Y j-V j|<s x/32 at e
    have z := abs_sub_le (Y j) (V j) 0
    simp only [sub_zero] at z
    have h : |V j|≤R^2/2 := middle_logistic_mass x hx j
    nlinarith only [z,h,e,su,r2,sq_nonneg (R-2)]
  have mass : |∑ i ∈ range d, C (i+1)*R^(i+2)*Y (n-(i+2))|<1/32 := by
    apply (abs_sum_le_sum_abs ..).trans_lt
    calc
      _ ≤ ∑ _i ∈ range d, exp (-x)*R^(d+4) := by
        apply sum_le_sum
        intro i hi
        have h : i+1≤d := mem_range.mp hi
        rw [abs_mul,abs_mul,abs_of_pos (pow_pos rp _)]
        apply (mul_le_mul (mul_le_mul_of_nonneg_right (hC _ (by omega) h)
          (pow_nonneg rp.le _)) (sh _) (abs_nonneg _) (by positivity)).trans
        rw [mul_assoc,←pow_add]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ r1 (by omega)) (exp_pos _).le
      _ < _ := by simpa only [sum_const,card_range,nsmul_eq_mul,←mul_assoc] using budget
  have ang : 1≤(n:ℝ)*(s x)^2 := by
    have prev := fixed_central_angle (n:=n+1) (by omega) x (by linarith)
      (by simpa only [show n+1-2=n-1 by omega] using upper)
    simpa using prev
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have ns : 1≤(n:ℝ)*s x := by
    nlinarith only [ang,mul_nonneg (mul_nonneg np.le hs.le) (sub_nonneg.mpr su)]
  apply lt_trans _ (middle_root_gap hn hx hd upper b hb budget zero)
  change |(∑ i ∈ range d, C (i+1)*R^(i+2)*Y (n-(i+2)))/(n:ℝ)| < _
  rw [abs_div,abs_of_pos np,div_lt_iff₀ np]
  nlinarith only [mass,ns]

#print axioms middle_insertion_gap
#print axioms eventual_middle_budget
#print axioms middle_tilt_bias
#print axioms middle_root_gap
end LongCycleBounds.FixedCutoff
