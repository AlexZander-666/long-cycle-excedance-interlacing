import LongCycleBounds.FullStripPoleExpansion
import LongCycleBounds.LinearCenteredGap
import LongCycleBounds.MarkedSign

/-! A telescoping majorant controls every positive-frequency logistic moment
at the physical radius. The constant coefficient is treated separately. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Real PowerSeries PoleBridge PoleTails Band Finset
open scoped Real

theorem logistic_scaled_moment (x : ℝ) {j : ℕ} (hj : 1≤j) :
    scaledCoeff (logistic (time x)) (radius x) j =
      2*scaledMoment (radius x) (time x) (j+1) := by
  simp only [scaledCoeff,logistic,logisticMoment,coeff_mk,if_neg (by omega : j≠0),
    scaledMoment,moment,Nat.add_one_sub_one]
  ring

private theorem pole_step (x : ℝ) (hx : 0<x) {q : ℕ} (hq : 2≤q) (i : ℕ) :
    ‖signedOddPole (c x) (s x) i ^q‖ ≤ (radius x)^2*
      (1/(x+2*(i:ℝ))-1/(x+2*((i:ℝ)+1))) := by
  let l := 2*(i:ℝ)+1
  let D := ‖den x l‖
  let R := radius x
  have rpos : 0<R := radius_pos x
  have one : 1≤l := by dsimp [l];linarith [Nat.cast_nonneg (α:=ℝ) i]
  have dl : D^2=x^2+(l*π)^2 := by
    dsimp [D]
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [den,Complex.add_re,Complex.add_im]
    ring
  have rr : R^2=x^2+π^2 := sq_sqrt (by positivity)
  have rd : R≤D := by
    apply (sq_le_sq₀ rpos.le (norm_nonneg _)).mp
    rw [rr,dl]
    apply add_le_add_right
    exact pow_le_pow_left₀ pi_pos.le (le_mul_of_one_le_left pi_pos.le one) 2
  have dp := rpos.trans_le rd
  have nz1 : 0<x+2*(i:ℝ) := by positivity
  have nz2 : 0<x+2*((i:ℝ)+1) := by positivity
  have lpos : 0≤l := by linarith
  have proof : (x+2*(i:ℝ))*(x+2*((i:ℝ)+1)) ≤ 2*D^2 := by
    rw [dl]
    have base : (x+2*(i:ℝ))*(x+2*((i:ℝ)+1))=(x+l)^2-1 := by dsimp [l];ring
    rw [base]
    nlinarith only [sq_nonneg (x-l),mul_nonneg (sq_nonneg l)
      (show 0≤π^2-1 by nlinarith [pi_gt_three,sq_nonneg (π-3)])]
  rw [signedOddPole,Int.cast_natCast,pole_den x l one,norm_pow,norm_div,Complex.norm_real,
    Real.norm_of_nonneg rpos.le]
  change (R/D)^q ≤ R^2*_
  apply (pow_le_pow_of_le_one (div_nonneg rpos.le dp.le) ((div_le_one dp).2 rd) hq).trans
  rw [div_pow,div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
  field_simp
  nlinarith only [proof]

theorem all_pole_mass (x : ℝ) (hx : 0<x) {q : ℕ} (hq : 2≤q) :
    (∑' i : ℤ, ‖signedOddPole (c x) (s x) i ^q‖) ≤ 2*(radius x)^2/x := by
  let f (i : ℤ) := ‖signedOddPole (c x) (s x) i ^q‖
  let g (i : ℕ) := (radius x)^2/(x+2*(i:ℝ))
  have step (i : ℕ) : f i ≤ g i - g (i+1) := by
    simpa only [g,f,Nat.cast_succ,mul_sub,mul_one_div] using pole_step x hx hq i
  have fin (m : ℕ) : (∑ i∈range m, f i) ≤ g 0 - g m := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ];linarith only [ih,step m]
  have bound (m : ℕ) : (∑ i∈range m, f i) ≤ g 0 := (fin m).trans (sub_le_self _ (by dsimp [g];positivity))
  have pos (i : ℕ) : 0≤f i := norm_nonneg _
  have sm := summable_of_sum_range_le pos bound
  have le := Real.tsum_le_of_sum_range_le pos bound
  have same (r : ℝ) : pole (c x) (s x) (-r)=star (pole (c x) (s x) r) := by
    apply Complex.ext <;> simp [pole]
    ring
  have neg (i : ℕ) : f (-(i+1:ℤ))=f i := by
    simp only [f,signedOddPole,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one]
    rw [show 2*(-((i:ℝ)+1))+1= -(2*i+1) by ring,same,←star_pow,norm_star]
  have sa := summable_norm_signed_odd_pole x hq
  change Summable f at sa
  change ∑' i : ℤ, f i ≤ _
  rw [←tsum_nat_add_neg_add_one sa]
  simp only [neg,sm.tsum_add sm]
  simp only [g,Nat.cast_zero,mul_zero,add_zero] at le
  rw [mul_div_assoc]
  linarith only [le]

theorem middle_logistic_mass (x : ℝ) (hx : 16≤x) (j : ℕ) :
    |scaledCoeff (logistic (time x)) (radius x) j| ≤ (radius x)^2/2 := by
  have xp : 0<x := by linarith
  have rh : (radius x)^2=x^2+π^2 := sq_sqrt (by positivity)
  have r2 : (2:ℝ)≤radius x := by nlinarith [radius_pos x,sq_nonneg π,sq_nonneg (x-16)]
  by_cases z : j=0
  · subst j
    simp only [scaledCoeff,logistic,coeff_mk,logisticMoment,if_true,Nat.factorial_zero,
      Nat.cast_one,div_one,zero_add,pow_one]
    have h : 0<1-time x := by dsimp [time];linarith [exp_pos (-x)]
    rw [abs_of_nonneg (by positivity)]
    have f : 1/(1-time x)≤1 := (div_le_one h).2 (by dsimp [time];linarith [exp_pos (-x)])
    nlinarith only [mul_le_mul_of_nonneg_left f (radius_pos x).le,mul_nonneg (radius_pos x).le (sub_nonneg.mpr r2)]
  · rw [logistic_scaled_moment x (by omega)]
    have sm := summable_norm_signed_odd_pole x (q:=j+1) (by omega)
    have est := (norm_tsum_le_tsum_norm sm).trans (all_pole_mass x xp (q:=j+1) (by omega))
    rw [signed_odd_pole_tsum x xp.le (by omega),norm_mul,Complex.norm_real,Complex.norm_ofNat,
      Real.norm_eq_abs] at est
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    apply est.trans
    rw [div_le_iff₀ xp]
    nlinarith only [mul_nonneg (sq_nonneg (radius x)) (show 0≤x-4 by linarith)]

#print axioms all_pole_mass
#print axioms middle_logistic_mass
end LongCycleBounds.MarkedTwo
