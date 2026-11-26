import LongCycleBounds.MarkedOuterMoments

/-! Exterior derivative sign for the marked rows with upper index at least 512. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo.Half
open Finset Real Outer

/-- A single Taylor monomial proves the required exponential cutoff without
an asymptotic estimate or optimization over integer n. -/
theorem outer_radius {n : ℕ} (hn : 512 ≤ n) {x : ℝ}
    (outer : 3*sqrt ((n-1:ℕ):ℝ) ≤ x) : exp (-x)*(n:ℝ)^8 ≤ 1 := by
  have h : (512:ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  have h0 : 0 ≤ (n:ℝ)-1 := by linarith
  rw [hsub] at outer
  have xp : 0≤x := le_trans (by positivity) outer
  have sq := sq_le_sq' (by linarith [sqrt_nonneg ((n:ℝ)-1)]) outer
  have s : (8:ℝ)*n≤x^2 := by nlinarith only [sq,Real.sq_sqrt h0,h]
  have p := pow_le_pow_left₀ (by positivity) s 16
  rw [mul_pow,←pow_mul] at p
  have minimum := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤512) h 8
  have numerical : ((32:ℕ).factorial:ℝ) ≤ (8:ℝ)^16*512^8 := by norm_num [Nat.factorial]
  have lim := numerical.trans (mul_le_mul_of_nonneg_left minimum (by positivity))
  have q := mul_le_mul_of_nonneg_right lim (by positivity : 0≤(n:ℝ)^8)
  have taylor := pow_div_factorial_le_exp x xp 32
  have bound : (n:ℝ)^8 ≤ exp x := by
    apply le_trans _ taylor
    rw [le_div_iff₀ (by positivity)]
    calc (n:ℝ)^8*(32:ℕ).factorial = ((32:ℕ).factorial:ℝ)*(n:ℝ)^8 := by ring
      _ ≤ _ := q
      _ = (8:ℝ)^16 * (n:ℝ)^16 := by ring
      _ ≤ x^32 := p
  rw [exp_neg,inv_mul_le_iff₀ (exp_pos x),mul_one]
  exact bound

private theorem small_exp {v : ℝ} (h0 : 0≤v) (hh : v ≤ 1/2) : exp v ≤ 1+2*v := by
  apply (exp_bound_div_one_sub_of_interval h0 (by linarith)).trans
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg h0 (show 0≤1-2*v by linarith)]

private theorem coeffs {u x : ℝ} (hu0 : 0≤u) (hu1 : u≤1) :
    0 ≤ -time x/(1-time x) ∧ -time x/(1-time x) ≤ exp (-x) ∧
    0 ≤ (u-1)*time x/(2*(1-time x)^2) ∧
      (u-1)*time x/(2*(1-time x)^2) ≤ exp (-x)/2 := by
  have r := exp_pos (-x)
  unfold time
  simp only [neg_neg,sub_neg_eq_add]
  refine ⟨by positivity,?_,?_,?_⟩
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (exp (-x))]
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hu0 r.le,sq_nonneg (exp (-x)),pow_nonneg r.le 3]

/-- Uniform, relative, coefficientwise estimate for every positive
integer label and every order through n. -/
theorem outer_positive_label {n j h : ℕ} (hn : 512≤n) (hj : 0<j) (hjn : j≤n)
    (hh : 1≤h) {u x : ℝ} (hu0 : 0≤u) (hu1 : u≤1) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) :
    let T := labelCoefficient (-time x/(1-time x)) ((u-1)*time x/(2*(1-time x)^2)) (h:ℝ) j
    (h:ℝ)^j ≤ T ∧ T ≤ (h:ℝ)^j*(1+1/(n:ℝ)^4) := by
  obtain ⟨ha,har,hb,hbr⟩ := coeffs hu0 hu1 (x:=x)
  let a := -time x/(1-time x)
  let b := (u-1)*time x/(2*(1-time x)^2)
  let y := (j:ℝ)/(h:ℝ)
  have hr : 0< (h:ℝ) := by exact_mod_cast (show 0<h by omega)
  have nr : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
  have jl : (j:ℝ)≤n := by exact_mod_cast hjn
  have hl : (1:ℝ)≤h := by exact_mod_cast hh
  have yn : y≤n := by
    apply (div_le_iff₀ hr).2
    nlinarith [mul_nonneg (by positivity : 0≤(n:ℝ)) (sub_nonneg.mpr hl)]
  have yn0 : 0≤y := by dsimp [y];positivity
  have ex := outer_radius hn outer
  have e0 : 0≤exp (-x) := (exp_pos _).le
  have pow4 : (1:ℝ)≤(n:ℝ)^4 := one_le_pow₀ (by linarith)
  have coef : 2*(a*y+b*y^2) ≤ 1/(n:ℝ)^4 := by
    have one := mul_le_mul har yn yn0 e0
    have two := mul_le_mul hbr (pow_le_pow_left₀ yn0 yn 2) (by positivity) (by positivity)
    change a*y≤_ at one
    change b*y^2≤_ at two
    rw [le_div_iff₀ (by positivity)]
    have cmp : (2*(n:ℝ)+(n:ℝ)^2)*(n:ℝ)^4 ≤ (n:ℝ)^8 := by
      have h2 := mul_nonneg (by positivity : 0≤(n:ℝ)) (show 0≤(n:ℝ)-2 by linarith)
      have d : 0≤(n:ℝ)^4-(n:ℝ)^2-2*n := by nlinarith only [sq_nonneg ((n:ℝ)^2-2),h2,nr]
      nlinarith only [mul_nonneg (by positivity : 0≤(n:ℝ)^4) d]
    nlinarith only [mul_le_mul_of_nonneg_right one (by positivity : 0≤(n:ℝ)^4),
      mul_le_mul_of_nonneg_right two (by positivity : 0≤(n:ℝ)^4),
      mul_le_mul_of_nonneg_left cmp e0,ex]
  have z : 0≤a*y+b*y^2 := add_nonneg (mul_nonneg ha yn0) (mul_nonneg hb (sq_nonneg _))
  have sm := small_exp z (by have := (div_le_one (by positivity : 0<(n:ℝ)^4)).2 pow4;linarith)
  have raw := label_bounds ha hb hr j hj
  exact ⟨raw.1,raw.2.trans (mul_le_mul_of_nonneg_left (by change exp (a*y+b*y^2) ≤ _;linarith) (by positivity))⟩

/-- The zero label, including its first surviving power of the exterior
radius. The order restriction 5 ≤ j suffices independently of n-j. -/
theorem outer_zero_label {n j : ℕ} (hn : 512≤n) (hj : 5≤j) (hjn : j≤n)
    {u x : ℝ} (hu0 : 0≤u) (hu1 : u≤1) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) :
    |labelCoefficient (-time x/(1-time x)) ((u-1)*time x/(2*(1-time x)^2)) 0 j| ≤
      exp (-x)/(n:ℝ)^4 := by
  obtain ⟨ha,har,hb,hbr⟩ := coeffs hu0 hu1 (x:=x)
  let a := -time x/(1-time x)
  let b := (u-1)*time x/(2*(1-time x)^2)
  let ρ := exp (x/2)
  have rp : 0<ρ := exp_pos _
  have prod : exp (-x)*ρ^2=1 := by
    dsimp [ρ]
    rw [sq,←exp_add,←exp_add]
    convert exp_zero using 2
    ring
  have ex := outer_radius hn outer
  have hp : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have npos : (0:ℝ)<n := by linarith
  have r0 := exp_pos (-x)
  have powle : (n:ℝ)^4 ≤ ρ := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) rp.le
    apply le_of_mul_le_mul_left (a:=exp (-x)) _ r0
    rw [prod,←pow_mul]
    exact ex
  have r1 : 1 ≤ ρ := (one_le_pow₀ hp).trans powle
  have r2 : exp (-x)*ρ ≤ 1 := by
    rw [←prod]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg rp.le (sub_nonneg.mpr r1)]) r0.le
  have et : a*ρ+b*ρ^2≤2 := by
    nlinarith only [mul_le_mul_of_nonneg_right har rp.le,
      mul_le_mul_of_nonneg_right hbr (sq_nonneg ρ),prod,r2]
  have e9 : exp (a*ρ+b*ρ^2) ≤ 9 := by
    apply (exp_le_exp.mpr et).trans
    rw [show (2:ℝ)=1+1 by norm_num,exp_add]
    nlinarith [mul_self_lt_mul_self (exp_pos 1).le exp_one_lt_three]
  have f : (j.factorial:ℝ)≤(n:ℝ)^j := by
    exact_mod_cast j.factorial_le_pow.trans (Nat.pow_le_pow_left hjn j)
  have eN : exp (a*ρ+b*ρ^2) ≤ n := e9.trans (by exact_mod_cast (show 9≤n by omega))
  have numer : (j.factorial:ℝ)*exp (a*ρ+b*ρ^2)*(n:ℝ)^4 ≤ ρ^(j-2) := calc
    _ ≤ ((n:ℝ)^j*n)*(n:ℝ)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul f eN (exp_pos _).le (by positivity)) (by positivity)
    _ = (n:ℝ)^(j+5) := by rw [pow_add];ring
    _ ≤ (n:ℝ)^(4*(j-2)) := pow_le_pow_right₀ hp (by omega)
    _ = ((n:ℝ)^4)^(j-2) := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) powle _
  apply (coeff_bias_zero_label ha hb rp j).trans
  rw [div_le_div_iff₀ (pow_pos rp _) (pow_pos npos _)]
  have split : ρ^j=ρ^2*ρ^(j-2) := by rw [←pow_add];congr 1;omega
  rw [split,←mul_assoc,prod,one_mul]
  exact numer

/-- Positive labels use the zero-based indexing of Outer.moment, so the
ordinary signed moment *adds* to the raw row in the discrepancy. -/
theorem raw_outer_error {n j : ℕ} (hn : 512≤n) (hj : 5≤j) (hjn : j≤n)
    {u x : ℝ} (hu0 : 0≤u) (hu1 : u≤1) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) :
    |rawRow u j x+Outer.moment j x| ≤
      (exp (-x)+∑' i, weight j x i)/(n:ℝ)^4 := by
  have hp0 : (0:ℝ)<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0<n-1 by omega)
  have hx : 0<x := lt_of_lt_of_le (by positivity) outer
  let t := time x
  let a := -t/(1-t)
  let b := (u-1)*t/(2*(1-t)^2)
  let T (i : ℕ) := labelCoefficient a b i j
  have hnorm : ‖t‖ < 1 := by simp [t,time,Real.norm_eq_abs,exp_lt_one_iff,hx]
  have hs := markedRow_label_expansion u t hnorm (by dsimp [t,time];linarith [exp_pos (-x)]) j
  have sh := hs.summable.tsum_eq_zero_add
  rw [hs.tsum_eq] at sh
  have original : rawRow u j x = T 0 + ∑' i : ℕ, t^(i+1)*T (i+1) := by
    change (row j u).eval t/(1-t)^j/(1-t)=_
    rw [div_div,←pow_succ]
    simpa [T,a,b] using sh
  let E (i : ℕ) := t^(i+1)*T (i+1)+(-1:ℝ)^i*weight j x i
  have bound (i : ℕ) : ‖E i‖ ≤ weight j x i/(n:ℝ)^4 := by
    obtain ⟨lo,hi⟩ := outer_positive_label hn (by omega : 0<j) hjn (show 1 ≤ i+1 by omega) hu0 hu1 outer
    change ((i+1:ℕ):ℝ)^j ≤ T (i+1) at lo
    change T (i+1) ≤ ((i+1:ℕ):ℝ)^j*(1+1/(n:ℝ)^4) at hi
    have e : E i = -((-1:ℝ)^i)*(exp (-x))^(i+1)*(T (i+1)-((i+1:ℕ):ℝ)^j) := by
      have tv : t=(-1)*exp (-x) := by simp [t,time]
      simp only [E,tv,mul_pow,weight,Nat.cast_succ,pow_succ (-1:ℝ) i]
      ring
    rw [e,Real.norm_eq_abs,abs_mul,abs_mul]
    simp only [abs_neg,abs_pow,abs_one,one_pow,one_mul,abs_of_pos (exp_pos _),
      abs_of_nonneg (sub_nonneg.mpr lo)]
    unfold weight
    rw [Nat.cast_succ] at hi ⊢
    simp only [div_eq_mul_inv] at hi ⊢
    nlinarith only [mul_le_mul_of_nonneg_left hi (pow_nonneg (exp_pos (-x)).le (i+1))]
  have hrs : Summable (fun i : ℕ ↦ weight j x i/(n:ℝ)^4) := (summable_weight j x hx).div_const _
  have herr := (norm_tsum_le_tsum_norm (hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound)).trans
    ((hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound).tsum_le_tsum bound hrs)
  have hraw : rawRow u j x+Outer.moment j x=T 0+∑' i, E i := by
    rw [original,add_assoc,Outer.moment]
    congr 1
    exact (((summable_nat_add_iff 1).mpr hs.summable).tsum_add (summable_signed_weight j x hx)).symm
  rw [hraw]
  rw [Real.norm_eq_abs] at herr
  have zero : |T 0| ≤ exp (-x)/(n:ℝ)^4 := by
    simpa [T,a,b,t] using outer_zero_label hn hj hjn hu0 hu1 outer
  rw [tsum_div_const] at herr
  rw [add_div]
  exact (abs_add_le ..).trans (add_le_add zero herr)

private theorem arithmetic {N : ℝ} (h : 512 ≤ N) :
    8*N*(1+(N+2)*(N+1)) ≤ N^4 ∧ 8*(N+N^2) < N^8 := by
  let a := N-512
  have ha : 0≤a := sub_nonneg.mpr h
  have he : N=512+a := by dsimp [a];ring
  constructor
  · rw [he,←sub_nonneg];ring_nf;positivity
  · rw [he,←sub_pos];ring_nf;positivity

private theorem outer_x {p : ℕ} (hp : 512≤p+1) {x : ℝ} (outer : 3*sqrt (p:ℝ)≤x) :
    2≤x := by
  have pn : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have h := sqrt_le_sqrt pn
  rw [sqrt_one] at h
  linarith

private theorem raw_peak_error {p j : ℕ} (hn : 512≤p+1) (hj : 5≤j) (hjn : j≤p+1)
    {u x : ℝ} (hu0 : 0≤u) (hu1 : u≤1) (outer : 3*sqrt (p:ℝ)≤x) :
    8*((p:ℝ)+1)*|rawRow u j x+Outer.moment j x| ≤
      weight p x (mode p x (by linarith [outer_x hn outer])) := by
  have hx := outer_x hn outer
  let W := weight p x (mode p x (by linarith))
  have hW : 0≤W := (weight_pos ..).le
  have r0 : exp (-x)≤W := by
    have he : weight p x 0=exp (-x) := by simp [weight]
    rw [←he]
    exact weight_le_mode p x _ 0
  have err := raw_outer_error hn hj hjn hu0 hu1 (by simpa using outer)
  have mass := outer_mass hjn hx
  have pn : 512≤(p:ℝ)+1 := by exact_mod_cast hn
  let N := (p:ℝ)+1
  have ar := (arithmetic pn).1
  change _ ≤ ((p:ℝ)+3)*((p:ℝ)+2)*W at mass
  rw [Nat.cast_succ] at err
  have main := (le_div_iff₀ (by positivity)).mp err
  change 8*N*_ ≤ W
  have pN : 0<N^4 := by dsimp [N];positivity
  apply le_of_mul_le_mul_right (a:=N^4) _ pN
  change _ ≤ W*N^4
  dsimp [N] at *
  nlinarith only [mul_le_mul_of_nonneg_right ar hW,
    mul_le_mul_of_nonneg_left (main.trans (add_le_add r0 mass)) (by positivity : 0≤8*((p:ℝ)+1))]

private theorem insertion_bounds {u x : ℝ} (h0 : 0≤u) (h1 : u≤1) (hx : 0≤x) :
    |alpha u x| ≤ exp (-x) ∧ |beta u x| ≤ exp (-x) := by
  let r := exp (-x)
  have a : 0<r := exp_pos _
  have b : r≤1 := exp_le_one_iff.mpr (by linarith)
  change |u*(-r)/(1-(-r))^2| ≤ r ∧ |(1-u)*(-r)*(1+(-r))/(2*(1-(-r))^3)| ≤ r
  simp only [sub_neg_eq_add,←sub_eq_add_neg]
  have hh : 0<1+r := by linarith
  constructor
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)) (by positivity)),
      ←neg_div,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h1 a.le,sq_nonneg r,pow_nonneg a.le 3]
  · have sign := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h1) (neg_nonpos.mpr a.le)) (sub_nonneg.mpr b)
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg sign (by positivity)),←neg_div,div_le_iff₀ (by positivity)]
    have small := mul_le_mul (show 1-u≤1 by linarith) (show 1-r≤1 by linarith) (sub_nonneg.mpr b) zero_le_one
    nlinarith only [mul_le_mul_of_nonneg_right small a.le,a.le,sq_nonneg r,pow_nonneg a.le 3,pow_nonneg a.le 4]

/-- Actual derivative sign on the full exterior for every real mark in [0,1].
The upper index is m+3 and the cutoff uses its predecessor m+2. -/
theorem marked_outer_sign (u x : ℝ) (m : ℕ) (hn : 512≤ m+3)
    (hu0 : 0≤u) (hu1 : u≤1) (outer : 3*sqrt ((m+2:ℕ):ℝ)≤x)
    (zero : normalizedRow u (m+2) x=0) :
    0<normalizedRow u (m+3) x * (-deriv (normalizedRow u (m+2)) x) := by
  let p := m+2
  let N := (p:ℝ)+1
  have hn' : 512≤p+1 := hn
  have nr : 512≤N := by dsimp [N];exact_mod_cast hn'
  have cut : 3*sqrt (p:ℝ)≤x := outer
  have x2 := outer_x hn' cut
  have hx : 0<x := by linarith
  let M := mode p x hx
  let W := weight p x M
  have wp : 0<W := weight_pos ..
  have prev : rawRow u p x=0 := by simp [rawRow,p,zero]
  have small (j : ℕ) (hj : 5≤j) (le : j≤p+1) :
      8*N*|rawRow u j x+Outer.moment j x| ≤ W := raw_peak_error hn' hj le hu0 hu1 cut
  have eps (j : ℕ) (hj : 5≤j) (le : j≤p+1) :
      |rawRow u j x+Outer.moment j x| ≤ W/8 := by
    nlinarith only [small j hj le,mul_nonneg (show 0≤N-1 by linarith)
      (abs_nonneg (rawRow u j x+Outer.moment j x))]
  have ps : 5≤p := by dsimp [p];omega
  have next := small p ps (by omega)
  rw [prev,zero_add] at next
  have q := mode_index_mul_le p x hx
  change (M:ℝ)*x ≤ p at q
  have pm : (M:ℝ)+2 ≤ N := by
    dsimp [N]
    have hp1 : (2:ℝ)≤p := by exact_mod_cast (show 2≤p by omega)
    nlinarith only [q,hp1,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (sub_nonneg.mpr x2)]
  have split : 5*sqrt (p:ℝ)/2≤x := by linarith [sqrt_nonneg (p:ℝ)]
  have rob := robust_derivative_moment p (by omega) x hx split
  change W/2 < |Outer.moment (p+1) x|+((M:ℝ)+2)*|Outer.moment p x| at rob
  have big : W/4 < |rawRow u (p+1) x| := by
    have diff := abs_sub (rawRow u (p+1) x+Outer.moment (p+1) x) (rawRow u (p+1) x)
    rw [add_sub_cancel_left] at diff
    nlinarith only [diff,rob,next,mul_le_mul_of_nonneg_right pm (abs_nonneg (Outer.moment p x)),
      eps (p+1) (by omega) le_rfl]
  have short (j : ℕ) (hj : 5≤j) (le : j≤p) : |rawRow u j x| ≤ 2*W := by
    have plain := signed_weight_bound j x hx
    change |Outer.moment j x| ≤ weight j x (mode j x hx) at plain
    let i := mode j x hx
    have weight_le : weight j x i≤weight p x i := by
      unfold weight
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i]) le)
        (by positivity)
    have bound := plain.trans (weight_le.trans (weight_le_mode p x hx i))
    have diff := abs_sub (rawRow u j x+Outer.moment j x) (Outer.moment j x)
    rw [add_sub_cancel_right] at diff
    linarith only [diff,eps j hj (by omega),bound,wp]
  let I := (m+2:ℝ)*alpha u x*rawRow u (m+1) x+
    (m+2:ℝ)*(m+1)*beta u x*rawRow u m x
  let r := exp (-x)
  have ab := insertion_bounds hu0 hu1 hx.le
  have sm (y : ℝ) (b : ℝ) (hy : |y|≤2*W) (hb : |b|≤r) : |b*y| ≤ r*(2*W) := by
    rw [abs_mul]
    exact mul_le_mul hb hy (abs_nonneg _) (exp_pos _).le
  have sn := sm _ _ (short (m+1) (by omega) (by dsimp [p];omega)) ab.1
  have sp := sm _ _ (short m (by omega) (by dsimp [p];omega)) ab.2
  have hM : (m:ℝ)+2≤N := by dsimp [N,p];push_cast;linarith
  have hMM : ((m:ℝ)+2)*((m:ℝ)+1) ≤ N^2 := by
    rw [sq]
    exact mul_le_mul hM (by linarith) (by positivity) (by linarith)
  have iu : |I| ≤ (N+N^2)*(r*(2*W)) := by
    dsimp [I]
    rw [mul_assoc ((m:ℝ)+2) (alpha u x),
      mul_assoc (((m:ℝ)+2)*((m:ℝ)+1)) (beta u x)]
    apply (abs_add_le ..).trans
    rw [abs_mul ((m:ℝ)+2),abs_mul (((m:ℝ)+2)*((m:ℝ)+1)),abs_of_nonneg (by positivity : 0≤(m:ℝ)+2),
      abs_of_nonneg (by positivity : 0≤((m:ℝ)+2)*((m:ℝ)+1)),add_mul N]
    exact add_le_add (mul_le_mul hM sn (abs_nonneg _) (by linarith))
      (mul_le_mul hMM sp (abs_nonneg _) (sq_nonneg _))
  have radius := outer_radius hn' (by simpa using cut)
  rw [Nat.cast_succ] at radius
  change r*N^8≤1 at radius
  have rad : 8*(N+N^2)*r<1 :=
    (mul_lt_mul_of_pos_right (arithmetic nr).2 (exp_pos _)).trans_le (by linarith only [radius])
  have gap : |I| < |rawRow u (p+1) x| := by
    nlinarith only [iu,mul_lt_mul_of_pos_right rad wp,big]
  let A := rawRow u (p+1) x
  have good : 0<A*(A-I) := by
    have sq := (sq_lt_sq).2 gap
    change I^2<A^2 at sq
    nlinarith only [sq,sq_nonneg (A-I)]
  let b := 1-time x
  have bp : 0<b := by dsimp [b,time];linarith [exp_pos (-x)]
  have norm (i : ℕ) : normalizedRow u i x=b*rawRow u i x := by
    unfold rawRow
    change _=b*(_/b)
    field_simp
  rw [(normalizedRow_hasDerivAt u x m).deriv,norm (m+3),norm (m+1),norm m]
  change 0<b*A*(-(((m:ℝ)+2)*alpha u x*(b*rawRow u (m+1) x)+
    ((m:ℝ)+2)*((m:ℝ)+1)*beta u x*(b*rawRow u m x)-b*A))
  have res := mul_pos (sq_pos_of_pos bp) good
  dsimp only [I] at res
  nlinarith only [res]

#print axioms outer_radius
#print axioms marked_outer_sign

end LongCycleBounds.MarkedTwo.Half
