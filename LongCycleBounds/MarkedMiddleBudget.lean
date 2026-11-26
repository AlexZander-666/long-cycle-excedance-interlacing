import LongCycleBounds.MarkedMiddleMass
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit exponential slack in the intermediate angular regime. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Real PoleBridge
open scoped Real

theorem middle_radius_budget {x : ℝ} (hx : 16 ≤ x) :
    2 ≤ radius x ∧ exp (-x)*(radius x)^5 < 1/5 := by
  let R := radius x
  have rp : 0<R := radius_pos x
  have rad : R^2=x^2+π^2 := sq_sqrt (by positivity)
  have r2 : 2≤R := by nlinarith [sq_nonneg (x-16),sq_nonneg π]
  have p4 : π≤4 := le_of_lt pi_lt_four
  have ru : R ≤ x+1 := by
    apply (sq_le_sq₀ rp.le (by linarith)).mp
    nlinarith only [rad,pow_le_pow_left₀ pi_pos.le p4 2,hx]
  let h := (x-16)/5
  have aux : R ≤ 17*exp h := by
    have := add_one_le_exp h
    dsimp [h] at *
    linarith
  have pow := pow_le_pow_left₀ rp.le aux 5
  rw [mul_pow,←exp_nat_mul] at pow
  have numeric : (5:ℝ)*17^5 < exp 16 := by
    have b : (27/10:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have t := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) b 16
    rw [←exp_nat_mul] at t
    norm_num at t
    linarith only [t]
  have e : exp (-x)*exp (5*h)=exp (-16) := by rw [←exp_add];congr 1;dsimp [h];ring
  constructor
  · exact r2
  · apply (mul_le_mul_of_nonneg_left pow (exp_pos (-x)).le).trans_lt
    change exp (-x)*(17^5*exp ((5:ℝ)*h)) < _
    rw [show exp (-x)*(17^5*exp (5*h))=17^5*(exp (-x)*exp (5*h)) by ring,e,exp_neg]
    rw [←div_eq_mul_inv,div_lt_iff₀ (exp_pos _)]
    linarith only [numeric]

private theorem marked_parameters {u x : ℝ} (h0 : 0≤u) (h1 : u≤1) :
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
    nlinarith [mul_nonneg h0 r.le,sq_nonneg (exp (-x)),pow_nonneg r.le 3]

theorem middle_row_bias {u x : ℝ} (h0 : 0≤u) (h1 : u≤1) (hx : 16≤x) (j : ℕ) :
    |scaledRow u (time x) (radius x) j-scaledCoeff (logistic (time x)) (radius x) j| < s x/12 := by
  let R := radius x
  let r := exp (-x)
  let a := -time x/(1-time x)
  let b := (u-1)*time x/(2*(1-time x)^2)
  have rp : 0<R := radius_pos x
  have rx : 0<r := exp_pos _
  obtain ⟨r2,small⟩ := middle_radius_budget hx
  change 2≤R at r2
  change r*R^5<1/5 at small
  have ha := marked_parameters (x:=x) h0 h1
  obtain ⟨a0,ar,b0,br⟩ := ha
  change 0≤a at a0
  change 0≤b at b0
  change a≤r at ar
  change b≤r/2 at br
  let v := a*R+b*R^2
  have v0 : 0≤v := add_nonneg (mul_nonneg a0 rp.le) (mul_nonneg b0 (sq_nonneg _))
  have vv : v≤r*R^2 := by
    dsimp only [v]
    nlinarith only [mul_le_mul_of_nonneg_right ar rp.le,mul_le_mul_of_nonneg_right br (sq_nonneg R),
      mul_nonneg (mul_nonneg rx.le rp.le) (sub_nonneg.mpr r2)]
  have vs : v≤1/2 := by
    have p := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith : 1≤R) (by decide : 2≤5)) rx.le
    linarith only [small,p,vv]
  have ex : exp v - 1≤2*v := by
    have he := exp_bound_div_one_sub_of_interval v0 (by linarith : v<1)
    have y : 1/(1-v) ≤ 1+2*v := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [mul_nonneg v0 (show 0≤1-2*v by linarith)]
    linarith only [he,y]
  have t0 : time x ≤ 0 := neg_nonpos.mpr rx.le
  have t1 : -1≤time x := neg_le_neg (exp_le_one_iff.mpr (by linarith))
  have est := scaledRow_logistic_bias h1 t1 t0 rp.le (show 0≤R^2/2 by positivity) j
    (fun i _ ↦ middle_logistic_mass x hx i)
  change _ ≤ R^2/2*(exp v-1) at est
  have scaled : |scaledRow u (time x) R j-scaledCoeff (logistic (time x)) R j| * R < 1/5 := by
    nlinarith only [mul_le_mul_of_nonneg_right est rp.le,
      mul_le_mul_of_nonneg_left ex (by positivity : 0≤R^3/2),
      mul_le_mul_of_nonneg_right vv (by positivity : 0≤R^3),small]
  change _ < (π/R)/12
  rw [div_div,lt_div_iff₀ (by positivity)]
  nlinarith only [scaled,pi_gt_three]

#print axioms middle_radius_budget
#print axioms middle_row_bias
end LongCycleBounds.MarkedTwo
