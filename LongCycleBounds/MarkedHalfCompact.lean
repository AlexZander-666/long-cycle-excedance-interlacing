import LongCycleBounds.MarkedCompactSign

/-! Compact marked-row bounds for upper sizes at least 512. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo.Half
open Real PoleBridge

private theorem tilt_parameters {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) :
    0 ≤ compactA x ∧ compactA x ≤ 1/2 ∧ compactA x ≤ exp (-x) ∧
      0 ≤ compactB u x ∧ compactB u x ≤ 1/8 ∧ compactB u x ≤ exp (-x)/2 := by
  let r := exp (-x)
  have r0 : 0 < r := exp_pos _
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have om : 0 ≤ 1-u := by linarith
  have den : 0 < 1+r := by linarith
  have one_le : 1 ≤ 1+r := by linarith
  have ds : 1 ≤ (1+r)^2 := by nlinarith only [r0,sq_nonneg r]
  have a : compactA x = r/(1+r) := by simp [compactA,time,r]
  have b : compactB u x = ((1-u)*r)/(2*(1+r)^2) := by
    dsimp [compactB,time,r]
    ring
  rw [a,b]
  refine ⟨by positivity,?_,?_,by positivity,?_,?_⟩
  · apply (div_le_iff₀ den).2
    linarith
  · apply (div_le_iff₀ den).2
    nlinarith only [sq_nonneg r]
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_nonneg hu r0.le, sq_nonneg (r-1)]
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_nonneg hu r0.le,mul_le_mul_of_nonneg_left ds r0.le]

private theorem compact_exponent {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) :
    compactA x * compactRadius x + compactB u x * compactRadius x^2 ≤ 17 := by
  let R := compactRadius x
  have R0 : 0 < R := compactRadius_pos x
  have Re : R^2=x^2+4*π^2 := sq_sqrt (by positivity)
  have Rle : R ≤ x+2*π := by
    apply (sq_le_sq₀ R0.le (by positivity)).mp
    rw [Re]
    nlinarith only [mul_nonneg hx pi_pos.le]
  have bp : π < 16/5 := pi_lt_d2.trans (by norm_num)
  have b2 : π^2 ≤ (16/5)^2 := pow_le_pow_left₀ pi_pos.le bp.le 2
  obtain ⟨a0,a1,ar,b0,b1,br⟩ := tilt_parameters hu hu1 hx
  have aR : compactA x * R ≤ x*exp (-x)+π := by
    have h := mul_le_mul_of_nonneg_left Rle a0
    have h1 := mul_le_mul_of_nonneg_right ar hx
    have h2 := mul_le_mul_of_nonneg_right a1 pi_pos.le
    linarith only [h,h1,h2]
  have bR : compactB u x * R^2 ≤ x^2*exp (-x)/2+π^2/2 := by
    rw [Re]
    have h1 := mul_le_mul_of_nonneg_right br (sq_nonneg x)
    have h2 := mul_le_mul_of_nonneg_right b1 (sq_nonneg π)
    linarith only [h1,h2]
  have e := quadratic_le_exp_of_nonneg hx
  have prod : exp x*exp (-x)=1 := by rw [←exp_add,add_neg_cancel,exp_zero]
  have both := mul_le_mul_of_nonneg_right e (exp_pos (-x)).le
  rw [prod] at both
  change compactA x*R+compactB u x*R^2 ≤ 17
  linarith only [aR,bR,both,bp,b2,exp_pos (-x)]

private theorem compactRotation_value (x : ℝ) :
    compactRotation x = (c x:ℂ)-(s x:ℂ)*Complex.I := by
  have h := PoleBridge.pole_den x 1 le_rfl
  change (radius x:ℂ)/den x 1 = _
  rw [←h]
  apply Complex.ext <;> simp [PoleTails.pole]


private theorem tail_small : exp (-15 : ℝ) < 1/1000000 := by
  have e : (8/3 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
  have p : (1000000:ℝ) < exp 15 := calc
    _ < (8/3:ℝ)^15 := by norm_num
    _ < (exp 1)^15 := pow_lt_pow_left₀ e (by norm_num) (by decide)
    _ = _ := by rw [←exp_nat_mul]; norm_num
  rw [exp_neg, ←one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) p

private theorem product_decay {q A v : ℝ} (q0 : 0≤q) (qv : q≤exp (-v))
    {j : ℕ} (limit : 4+A-(j+1:ℕ)*v ≤ -15) :
    32*exp A*q^(j+1) < 1/1000000 := by
  have fe : (32:ℝ) ≤ exp 4 := calc
    _ ≤ (5/2:ℝ)^4 := by norm_num
    _ ≤ (exp 1)^4 := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) 4
    _ = _ := by rw [←exp_nat_mul]; norm_num
  calc
    _ ≤ exp 4*exp A*(exp (-v))^(j+1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right fe (exp_pos _).le)
        (pow_le_pow_left₀ q0 qv _) (by positivity) (by positivity)
    _ = exp (4+A-(j+1:ℕ)*v) := by
      rw [←exp_nat_mul,←exp_add,←exp_add]
      congr 1
      ring
    _ < _ := (exp_le_exp.mpr limit).trans_lt tail_small

/-- The contour moves relatively farther from the poles for x ≤ 8. For x ≥ 8
the absolute size of the tilt is small on the contour itself. -/
theorem compact_scaled_row {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hx : 0 ≤ x) (h16 : x ≤ 16) {j : ℕ} (hj : 509 ≤ j) :
    |scaledRow u (time x) (radius x) j-
      2*(compactTilt u x * compactRotation x^(j+1)).re| < 1/1000000 := by
  let q := radius x/compactRadius x
  let A := compactA x*compactRadius x+compactB u x*compactRadius x^2
  have err := compact_scaled_row_of_tilt hu1 hx h16 j
  change _ ≤ 32*exp A*q^(j+1) at err
  have q0 : 0≤q := div_nonneg (radius_pos x).le (compactRadius_pos x).le
  have jc : (509:ℝ) ≤ j := by exact_mod_cast hj
  apply err.trans_lt
  by_cases h8 : x ≤ 8
  · have q9 : q ≤ 9/10 := by
      apply (div_le_iff₀ (compactRadius_pos x)).2
      apply (sq_le_sq₀ (radius_pos x).le (mul_nonneg (by norm_num : (0:ℝ)≤9/10) (compactRadius_pos x).le)).mp
      have a : radius x^2=x^2+π^2 := sq_sqrt (by positivity)
      have b : compactRadius x^2=x^2+4*π^2 := sq_sqrt (by positivity)
      have xs : x^2≤64 := by nlinarith only [mul_self_le_mul_self hx h8]
      have ps : 9 < π^2 := by nlinarith only [pi_gt_three, sq_nonneg (π-3)]
      nlinarith only [a,b,xs,ps]
    apply product_decay q0 (v:=1/10) (q9.trans (by
      rw [show (9:ℝ)/10=1-1/10 by norm_num]
      exact one_sub_le_exp_neg (1/10:ℝ)))
    have old : A ≤ 17 := compact_exponent hu hu1 hx
    push_cast
    linarith
  · have x8 : (8:ℝ) ≤ x := le_of_not_ge h8
    have E : 180 ≤ exp x := calc
      _ ≤ (5/2:ℝ)^8 := by norm_num
      _ ≤ (exp 1)^8 := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) 8
      _ = exp 8 := by rw [←exp_nat_mul]; norm_num
      _ ≤ exp x := exp_le_exp.mpr x8
    have er : 180*exp (-x) ≤ 1 := by
      rw [exp_neg, ←div_eq_mul_inv, div_le_one (exp_pos _)]
      exact E
    have R := (compact_geometry hx h16).2.2.1
    have R0 := (compactRadius_pos x).le
    obtain ⟨a0,_,a,b0,_,b⟩ := tilt_parameters hu hu1 hx
    have A1 : A ≤ 1 := by
      dsimp [A]
      nlinarith only [er,mul_le_mul a R.le R0 (exp_pos _).le,
        mul_le_mul b (pow_le_pow_left₀ R0 R.le 2) (sq_nonneg _) (by positivity)]
    have q24 : q ≤ 24/25 := (compact_geometry hx h16).2.2.2.le
    apply product_decay q0 (v:=1/25) (q24.trans (by
      rw [show (24:ℝ)/25=1-1/25 by norm_num]
      exact one_sub_le_exp_neg (1/25:ℝ)))
    push_cast
    linarith

/-- At a zero of the genuine predecessor, rotation of the retained pair
gives a gap even when the two leading residues nearly cancel. -/
theorem compact_scaled_row_gap {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) (h16 : x ≤ 16)
    {n : ℕ} (hn : 512 ≤ n) (zero : scaledRow u (time x) (radius x) (n-1)=0) :
    (3/2:ℝ)*‖compactTilt u x‖*s x < |scaledRow u (time x) (radius x) n| := by
  let B := compactTilt u x
  let q := compactRotation x
  let S := B*q^n
  have B4 : 1/4 < ‖B‖ := compactTilt_lower hu hu1 hx
  have qr : ‖q‖=1 := compactRotation_norm x
  have Seq : ‖S‖=‖B‖ := by simp [S,norm_pow,qr]
  have p := compact_scaled_row hu hu1 hx h16 (by omega : 509 ≤ n-1)
  rw [zero,zero_sub,abs_neg,show n-1+1=n by omega,abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at p
  have re0 : |S.re| ≤ ‖B‖/100 := by
    change 2*|S.re| < 1/1000000 at p
    linarith
  have im := Complex.norm_le_abs_re_add_abs_im S
  rw [Seq] at im
  have im0 : (99/100:ℝ)*‖B‖ ≤ |S.im| := by linarith only [im,re0]
  have s0 : (3/17:ℝ) ≤ s x := by
    unfold s
    apply (le_div_iff₀ (radius_pos x)).2
    linarith [(compact_geometry hx h16).2.1,pi_gt_three]
  have c1 : |c x| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by
    rw [sq_abs]
    nlinarith only [circle x,sq_nonneg (s x)])
  have step : (S*q).re = c x*S.re+s x*S.im := by
    rw [show q=(c x:ℂ)-(s x:ℂ)*Complex.I from compactRotation_value x]
    simp [Complex.mul_re,Complex.sub_re,Complex.sub_im]
    ring
  have reverse := abs_sub (S*q).re (c x*S.re)
  rw [step,add_sub_cancel_left,abs_mul,abs_of_nonneg (by linarith : 0 ≤ s x)] at reverse
  rw [←step] at reverse
  have reErr : |c x*S.re| ≤ ‖B‖/100 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul c1 re0 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have qest := mul_le_mul_of_nonneg_left im0 (show 0 ≤ s x by linarith)
  have adv := compact_scaled_row hu hu1 hx h16 (by omega : 509 ≤ n)
  rw [pow_succ,←mul_assoc] at adv
  change |scaledRow u (time x) (radius x) n-2*(S*q).re| < _ at adv
  have error := abs_sub (scaledRow u (time x) (radius x) n)
    (scaledRow u (time x) (radius x) n-2*(S*q).re)
  rw [sub_sub_cancel,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at error
  change (3/2:ℝ)*‖B‖*s x < |scaledRow u (time x) (radius x) n|
  nlinarith only [error,adv,reverse,reErr,qest,B4,
    mul_le_mul_of_nonneg_right s0 (norm_nonneg B)]

private theorem compact_short_row {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) (h16 : x ≤ 16)
    {j : ℕ} (hj : 509 ≤ j) :
    |scaledRow u (time x) (radius x) j| ≤ 3*‖compactTilt u x‖ := by
  let B := compactTilt u x
  let q := compactRotation x
  let Y := scaledRow u (time x) (radius x) j
  have e : |Y-2*(B*q^(j+1)).re| < 1/1000000 := compact_scaled_row hu hu1 hx h16 hj
  have lo : 1/4 < ‖B‖ := compactTilt_lower hu hu1 hx
  have mag := Complex.abs_re_le_norm (B*q^(j+1))
  rw [norm_mul,norm_pow,show ‖q‖=1 from compactRotation_norm x,one_pow,mul_one] at mag
  have tri := abs_add_le (Y-2*(B*q^(j+1)).re) (2*(B*q^(j+1)).re)
  rw [sub_add_cancel,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at tri
  linarith only [tri,e,lo,mag]

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

private theorem compact_exp_radius {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3) :
    exp (-x)*(radius x)^m ≤ (16/5:ℝ)^m := by
  let A : ℝ := 16/5
  have ap : 0 < A := by norm_num [A]
  have bp : π < A := pi_lt_d2.trans (by norm_num [A])
  have xp : 0 ≤ x+π := by positivity
  have rad : radius x^2=x^2+π^2 := sq_sqrt (by positivity)
  have r : radius x ≤ x+π := by
    apply (sq_le_sq₀ (radius_pos x).le xp).mp
    rw [rad]
    nlinarith only [mul_nonneg hx pi_pos.le]
  have m0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have mA : (m:ℝ) ≤ A := (by exact_mod_cast hm3 : (m:ℝ) ≤ 3).trans (by norm_num [A])
  have e := mul_le_mul_of_nonneg_right (add_one_le_exp (x/(m:ℝ))) ap.le
  have l : x+A ≤ A*exp (x/(m:ℝ)) := by
    have y : x ≤ (x/(m:ℝ))*A := by
      calc
        x = x/(m:ℝ)*m := (div_mul_cancel₀ x m0.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left mA (div_nonneg hx m0.le)
    linarith only [e,y]
  have h := pow_le_pow_left₀ (radius_pos x).le ((r.trans (by linarith [bp])).trans l) m
  have ep : (exp (x/(m:ℝ)))^m=exp x := by
    rw [←exp_nat_mul]
    congr 1
    field_simp
  rw [mul_pow,ep] at h
  calc
    _ ≤ exp (-x)*(A^m*exp x) := mul_le_mul_of_nonneg_left h (exp_pos _).le
    _ = _ := by rw [mul_left_comm,←exp_add,neg_add_cancel,exp_zero,mul_one]

/-- The compact estimates imply the strict insertion sign of the actual rows,
including the reciprocal endpoint at x=0. -/
theorem marked_compact_sign {u x : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) (h16 : x ≤ 16)
    {n : ℕ} (hn : 512 ≤ n) (zero : normalizedRow u (n-1) x=0) :
    0 < normalizedRow u n x*(-deriv (normalizedRow u (n-1)) x) := by
  let B := ‖compactTilt u x‖
  let ρ := radius x
  let Y := scaledRow u (time x) ρ
  have B4 : 1/4 < B := compactTilt_lower hu hu1 hx
  have pzero : Y (n-1)=0 := by
    dsimp only [Y]
    rw [scaledRow_normalized,zero,mul_zero]
  have gap : (3/2:ℝ)*B*s x < |Y n| := compact_scaled_row_gap hu hu1 hx h16 hn pzero
  have low : (3/17:ℝ) ≤ s x := by
    unfold s
    apply (le_div_iff₀ (radius_pos x)).2
    linarith [(compact_geometry hx h16).2.1,pi_gt_three]
  obtain ⟨a,b⟩ := alpha_beta_bound hu hu1 hx
  have estimate (f : ℝ) (hf : |f| ≤ exp (-x)) (m : ℕ) (hm : 1 ≤ m) (hm3 : m ≤ 3)
      (j : ℕ) (hj : 509 ≤ j) : |f*ρ^m*Y j| ≤ (16/5:ℝ)^m*(3*B) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (radius_pos x).le _)]
    have power : |f| * ρ^m ≤ (16/5:ℝ)^m :=
      (mul_le_mul_of_nonneg_right hf (pow_nonneg (radius_pos x).le _)).trans
        (compact_exp_radius hx hm hm3)
    exact mul_le_mul power (compact_short_row hu hu1 hx h16 hj) (abs_nonneg _) (by positivity)
  have num := (abs_add_le (alpha u x*ρ^2*Y (n-2)) (beta u x*ρ^3*Y (n-3))).trans
    (add_le_add (estimate _ a 2 (by omega) (by omega) _ (by omega))
      (estimate _ b 3 (by omega) (by omega) _ (by omega)))
  have nc : (512:ℝ) ≤ n := by exact_mod_cast hn
  have np : (0:ℝ) < n := by linarith
  have Bp : 0 < B := by linarith
  have strong :
      |(alpha u x*ρ^2*Y (n-2)+beta u x*ρ^3*Y (n-3))/(n:ℝ)| < (3/2:ℝ)*B*s x := by
    rw [abs_div,abs_of_pos np]
    apply (div_lt_iff₀ np).2
    have bn : (3/17:ℝ)*B*512 ≤ B*s x*(n:ℝ) := by
      rw [mul_comm (3/17:ℝ) B]
      exact mul_le_mul (mul_le_mul_of_nonneg_left low Bp.le) nc (by norm_num)
        (mul_nonneg Bp.le (by linarith))
    nlinarith only [num,bn,Bp]
  have e := sign_of_scaled_gap u x ρ (radius_pos x) (n-3) (by
    have m1 : n-3+1=n-2 := by omega
    have m3 : n-3+3=n := by omega
    have cast : ((n-3:ℕ):ℝ)+3=(n:ℝ) := by exact_mod_cast m3
    simpa only [m1,m3,cast] using strong.trans gap)
  simpa only [show n-3+3=n by omega,show n-3+2=n-1 by omega] using e

#print axioms compact_scaled_row
#print axioms compact_scaled_row_gap
#print axioms marked_compact_sign

end LongCycleBounds.MarkedTwo.Half
