import Mathlib.Analysis.Complex.ExponentialBounds
import LongCycleBounds.MarkedLabelExpansion
import LongCycleBounds.MarkedSign

/-! Uniform transposition-mark errors on individual exterior labels. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Real

/-- A single Taylor monomial proves the required exponential cutoff without
an asymptotic estimate or optimization over integer n. -/
theorem outer_radius {n : ℕ} (hn : 1024 ≤ n) {x : ℝ}
    (outer : 3*sqrt ((n-1:ℕ):ℝ) ≤ x) : exp (-x)*(n:ℝ)^8 ≤ 1 := by
  have h : (1024:ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  have h0 : 0 ≤ (n:ℝ)-1 := by linarith
  rw [hsub] at outer
  have xp : 0≤x := le_trans (by positivity) outer
  have sq := sq_le_sq' (by linarith [sqrt_nonneg ((n:ℝ)-1)]) outer
  have s : (27/4:ℝ)*n≤x^2 := by nlinarith only [sq,Real.sq_sqrt h0,h]
  have p := pow_le_pow_left₀ (by positivity) s 16
  rw [mul_pow,←pow_mul] at p
  have minimum := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1024) h 8
  have numerical : ((32:ℕ).factorial:ℝ) ≤ (27/4:ℝ)^16*1024^8 := by norm_num [Nat.factorial]
  have lim := numerical.trans (mul_le_mul_of_nonneg_left minimum (by positivity))
  have q := mul_le_mul_of_nonneg_right lim (by positivity : 0≤(n:ℝ)^8)
  have taylor := pow_div_factorial_le_exp x xp 32
  have bound : (n:ℝ)^8 ≤ exp x := by
    apply le_trans _ taylor
    rw [le_div_iff₀ (by positivity)]
    calc (n:ℝ)^8*(32:ℕ).factorial = ((32:ℕ).factorial:ℝ)*(n:ℝ)^8 := by ring
      _ ≤ _ := q
      _ = (27/4:ℝ)^16 * (n:ℝ)^16 := by ring
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
theorem outer_positive_label {n j h : ℕ} (hn : 1024≤n) (hj : 0<j) (hjn : j≤n)
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
theorem outer_zero_label {n j : ℕ} (hn : 1024≤n) (hj : 5≤j) (hjn : j≤n)
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

#print axioms outer_zero_label
#print axioms outer_radius
#print axioms outer_positive_label
end LongCycleBounds.MarkedTwo
