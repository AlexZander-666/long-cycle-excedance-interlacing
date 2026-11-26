import LongCycleBounds.MarkedCompactLogistic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A scaled Taylor coefficient estimate for the nearest conjugate pair. -/

noncomputable section
namespace LongCycleBounds.MarkedTwo

open Real PowerSeries Finset PoleBridge

def tiltSeries (a b : ℝ) : PowerSeries ℝ := linearExp a*quadraticExp b

def tiltValue (a b : ℝ) (z : ℂ) : ℂ := Complex.exp ((a:ℂ)*z+(b:ℂ)*z^2)

private def weightedCoeff (P : PowerSeries ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  ((coeff j P:ℝ):ℂ)*z^j

private theorem quadratic_weighted_hasSum (b : ℝ) (z : ℂ) :
    HasSum (weightedCoeff (quadraticExp b) z) (Complex.exp ((b:ℂ)*z^2)) := by
  let f := weightedCoeff (quadraticExp b) z
  let e (n : ℕ) := 2*n
  have inj : Function.Injective e := fun _ _ h ↦ by dsimp [e] at h;omega
  apply (inj.hasSum_iff (f:=f) ?_).mp
  · rw [Complex.exp_eq_exp_ℂ]
    apply (NormedSpace.expSeries_div_hasSum_exp ((b:ℂ)*z^2)).congr_fun
    intro n
    simp only [f,e,Function.comp_apply,weightedCoeff,quadraticExp,coeff_mk,
      Nat.mul_mod_right,if_true,Nat.mul_div_cancel_left _ (by norm_num : 0<2)]
    push_cast
    rw [mul_pow,←pow_mul]
    ring
  · intro n hn
    have odd : n%2≠0 := by
      intro even
      apply hn
      exact ⟨n/2,by dsimp [e];omega⟩
    simp [f,weightedCoeff,quadraticExp,odd]

private theorem quadratic_weighted_norm (b : ℝ) (z : ℂ) :
    Summable (fun j ↦ ‖weightedCoeff (quadraticExp b) z j‖) := by
  let f (j : ℕ) := ‖weightedCoeff (quadraticExp b) z j‖
  let e (n : ℕ) := 2*n
  have inj : Function.Injective e := fun _ _ h ↦ by dsimp [e] at h;omega
  have he (n : ℕ) : weightedCoeff (quadraticExp b) z (e n) =
      ((b:ℂ)*z^2)^n/(n.factorial:ℂ) := by
    simp only [e,weightedCoeff,quadraticExp,coeff_mk,Nat.mul_mod_right,if_true,
      Nat.mul_div_cancel_left _ (by norm_num : 0<2)]
    push_cast
    rw [mul_pow,←pow_mul]
    ring
  have hs : Summable (f ∘ e) := (NormedSpace.norm_expSeries_div_summable ((b:ℂ)*z^2)).congr
    (fun n ↦ (congrArg norm (he n)).symm)
  apply ((inj.hasSum_iff (f:=f) ?_).mp hs.hasSum).summable
  intro n hn
  have odd : n%2≠0 := by
    intro even
    apply hn
    exact ⟨n/2,by dsimp [e];omega⟩
  simp [f,weightedCoeff,quadraticExp,odd]

private theorem linear_weighted (a : ℝ) (z : ℂ) (j : ℕ) :
    weightedCoeff (linearExp a) z j = ((a:ℂ)*z)^j/j.factorial := by
  simp only [weightedCoeff,linearExp,coeff_mk]
  push_cast
  rw [mul_pow]
  ring

private theorem weightedCoeff_mul (P Q : PowerSeries ℝ) (z : ℂ) (j : ℕ) :
    weightedCoeff (P*Q) z j =
      ∑ i ∈ range (j+1), weightedCoeff P z i*weightedCoeff Q z (j-i) := by
  unfold weightedCoeff
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro i hi
  have h : i+(j-i)=j := by have := mem_range.mp hi;omega
  rw [Complex.ofReal_mul,←h,pow_add]
  rw [h]
  ring

private theorem tilt_hasSum (a b : ℝ) (z : ℂ) :
    HasSum (weightedCoeff (tiltSeries a b) z) (tiltValue a b z) := by
  have sa : Summable (fun j ↦ ‖weightedCoeff (linearExp a) z j‖) := by
    simp_rw [linear_weighted]
    exact NormedSpace.norm_expSeries_div_summable _
  have sb := quadratic_weighted_norm b z
  have conv := hasSum_sum_range_mul_of_summable_norm sa sb
  have va : (∑' j, weightedCoeff (linearExp a) z j) = Complex.exp ((a:ℂ)*z) := by
    simp_rw [linear_weighted]
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq
  rw [va,(quadratic_weighted_hasSum b z).tsum_eq,←Complex.exp_add] at conv
  exact conv.congr_fun fun j ↦ weightedCoeff_mul _ _ z j

private theorem tilt_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (j : ℕ) :
    0≤coeff j (tiltSeries a b) := by
  unfold tiltSeries
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_nonneg
  intro i _
  simp only [linearExp,quadraticExp,coeff_mk]
  split <;> positivity

private theorem tilt_real_hasSum (a b R : ℝ) :
    HasSum (fun i ↦ coeff i (tiltSeries a b)*R^i) (exp (a*R+b*R^2)) := by
  have raw := Complex.hasSum_re (tilt_hasSum a b (R:ℂ))
  unfold weightedCoeff tiltValue at raw
  simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_add,
    ←Complex.ofReal_exp,Complex.ofReal_re] at raw
  exact raw

private theorem tilt_partial_bound {a b R : ℝ} (ha : 0≤a) (hb : 0≤b) (hR : 0≤R)
    (j : ℕ) : ∑ i ∈ range (j+1), coeff i (tiltSeries a b)*R^i ≤ exp (a*R+b*R^2) := by
  have hs := tilt_real_hasSum a b R
  rw [←hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ (fun i _ ↦ mul_nonneg (tilt_nonneg ha hb i) (pow_nonneg hR _))

private theorem tilt_truncation {a b R : ℝ} (ha : 0≤a) (hb : 0≤b) (hR : 0<R)
    (z : ℂ) (hz : ‖z‖≤R) (j : ℕ) :
    ‖(∑ i ∈ range (j+1), weightedCoeff (tiltSeries a b) z i)-tiltValue a b z‖ ≤
      (‖z‖/R)^(j+1)*exp (a*R+b*R^2) := by
  let A (i : ℕ) := coeff i (tiltSeries a b)*R^i
  let F (i : ℕ) := weightedCoeff (tiltSeries a b) z (i+(j+1))
  let q := ‖z‖/R
  have q0 : 0≤q := by dsimp [q];positivity
  have q1 : q≤1 := (div_le_one₀ hR).mpr hz
  have ra := tilt_real_hasSum a b R
  have SF : Summable (fun i ↦ A (i+(j+1))) := (summable_nat_add_iff (j+1)).2 ra.summable
  have key (i : ℕ) : ‖F i‖ ≤ q^(j+1)*A (i+(j+1)) := by
    dsimp only [F,weightedCoeff]
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (tilt_nonneg ha hb _)]
    have u : ‖z‖^((i+(j+1))) = q^((i+(j+1)))*R^((i+(j+1))) := by
      rw [←mul_pow]
      dsimp [q]
      field_simp
    rw [u]
    change _ ≤ _
    have ex := pow_le_pow_of_le_one q0 q1 (show j+1 ≤ i+(j+1) by omega)
    dsimp only [A]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_right ex (mul_nonneg (tilt_nonneg ha hb _) (pow_nonneg hR.le _))
  have sa : Summable (fun i ↦ ‖F i‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) key (SF.mul_left _)
  have rep := (tilt_hasSum a b z).summable.sum_add_tsum_nat_add (j+1)
  rw [(tilt_hasSum a b z).tsum_eq] at rep
  change (∑ i ∈ range (j+1), weightedCoeff (tiltSeries a b) z i)+(∑' i, F i) = _ at rep
  rw [←rep,sub_add_cancel_left,norm_neg]
  calc
    _ ≤ ∑' i, ‖F i‖ := norm_tsum_le_tsum_norm sa
    _ ≤ ∑' i, q^(j+1)*A (i+(j+1)) := sa.tsum_le_tsum key (SF.mul_left _)
    _ ≤ _ := by
      rw [tsum_mul_left]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg q0 _)
      change (∑' i, A (i+(j+1))) ≤ _
      have sm := ra.summable.sum_add_tsum_nat_add (j+1)
      rw [ra.tsum_eq] at sm
      have positive : 0 ≤ ∑ i ∈ range (j+1), A i :=
        sum_nonneg fun i _ ↦ mul_nonneg (tilt_nonneg ha hb i) (pow_nonneg hR.le _)
      change (∑ i ∈ range (j+1), A i)+(∑' i, A (i+(j+1))) = _ at sm
      linarith only [sm,positive]

/-- Applying the tilt to the pole-subtracted real series preserves a uniform
coefficient envelope apart from the exponential factor. -/
private theorem tilt_scaled_bound {a b R M : ℝ} (ha : 0≤a) (hb : 0≤b) (hR : 0<R)
    (hm : 0≤M) (P : PowerSeries ℝ) (h : ∀ i, |scaledCoeff P R i|≤M) (j : ℕ) :
    |scaledCoeff (tiltSeries a b*P) R j| ≤ M*exp (a*R+b*R^2) := by
  have eq : scaledCoeff (tiltSeries a b*P) R j =
      ∑ i ∈ range (j+1), (coeff i (tiltSeries a b)*R^i)*scaledCoeff P R (j-i) := by
    unfold scaledCoeff
    rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum]
    apply sum_congr rfl
    intro i hi
    have e : i+(j-i+1)=j+1 := by have := mem_range.mp hi;omega
    have pe : R^(j+1) = R^i*R^(j-i+1) := by rw [←pow_add,e]
    rw [pe]
    ring
  rw [eq]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i ∈ range (j+1), (coeff i (tiltSeries a b)*R^i)*M := by
      apply sum_le_sum
      intro i _
      have term : 0≤coeff i (tiltSeries a b)*R^i :=
        mul_nonneg (tilt_nonneg ha hb i) (pow_nonneg hR.le _)
      rw [abs_mul,abs_of_nonneg term]
      exact mul_le_mul_of_nonneg_left (h _) term
    _ ≤ _ := by
      rw [←sum_mul,mul_comm M]
      exact mul_le_mul_of_nonneg_right (tilt_partial_bound ha hb hR.le j) hm

private theorem tilted_nearest_coeff (a b x : ℝ) (j : ℕ) :
    scaledCoeff (tiltSeries a b*nearestLogistic x) (radius x) j =
      2*(((radius x:ℂ)/nearestPole x)^(j+1)*
        ∑ i ∈ range (j+1), weightedCoeff (tiltSeries a b) (nearestPole x) i).re := by
  let z := nearestPole x
  have zn : z≠0 := by
    have nn : 0<‖z‖ := by rw [show ‖z‖=radius x from nearestPole_norm x];exact radius_pos x
    exact norm_ne_zero_iff.mp nn.ne'
  unfold scaledCoeff
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum]
  rw [mul_sum,Complex.re_sum,mul_sum]
  apply sum_congr rfl
  intro i hi
  have idx : i+(j-i+1)=j+1 := by have := mem_range.mp hi;omega
  simp only [nearestLogistic,coeff_mk,weightedCoeff]
  change radius x^(j+1)*(coeff i (tiltSeries a b)*(2*(z⁻¹^(j-i+1)).re)) =
    2*(((radius x:ℂ)/z)^(j+1)*(((coeff i (tiltSeries a b):ℝ):ℂ)*z^i)).re
  have re : ((radius x:ℂ)/z)^(j+1)*(((coeff i (tiltSeries a b):ℝ):ℂ)*z^i) =
      ((radius x^(j+1)*coeff i (tiltSeries a b):ℝ):ℂ)*z⁻¹^(j-i+1) := by
    rw [div_pow,←idx, pow_add z, inv_pow]
    push_cast
    field_simp
  rw [re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Radial Cauchy-type bound for the genuine marked coefficient.
The bound uses the exact odd-pole series and its absolute majorant. -/
theorem compact_scaled_row_of_tilt {u x : ℝ} (hu1 : u≤1)
    (hx : 0≤x) (h16 : x≤16) (j : ℕ) :
    let t := -exp (-x)
    let a := -t/(1-t)
    let b := (u-1)*t/(2*(1-t)^2)
    let z := nearestPole x
    let R := compactRadius x
    |scaledRow u t (radius x) j-2*(tiltValue a b z*((radius x:ℂ)/z)^(j+1)).re| ≤
      32*exp (a*R+b*R^2)*(radius x/R)^(j+1) := by
  dsimp only
  let t := -exp (-x)
  let a := -t/(1-t)
  let b := (u-1)*t/(2*(1-t)^2)
  let R := compactRadius x
  let z := nearestPole x
  let ρ := radius x
  change |scaledRow u t ρ j-2*(tiltValue a b z*((ρ:ℂ)/z)^(j+1)).re| ≤
    32*exp (a*R+b*R^2)*(ρ/R)^(j+1)
  have tn : t≤0 := neg_nonpos.mpr (exp_pos _).le
  have tl : -1≤t := neg_le_neg (exp_le_one_iff.mpr (by linarith))
  have a0 : 0≤a := by unfold a; exact div_nonneg (neg_nonneg.mpr tn) (by linarith)
  have b0 : 0≤b := by
    unfold b
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) tn) (by positivity)
  have R0 : 0<R := compactRadius_pos x
  have ρ0 : 0<ρ := radius_pos x
  have mag : ‖z‖=ρ := nearestPole_norm x
  have qsmall : ρ/R ≤ 1 := (compact_geometry hx h16).2.2.2.le.trans (by norm_num)
  have zle : ‖z‖≤R := (div_le_one₀ R0).mp (by rwa [mag])
  let P := tiltSeries a b
  let Q := P*nearestLogistic x
  let E := P*compactLogisticTail x
  have realRow : scaledRow u t ρ j = scaledCoeff Q ρ j + scaledCoeff E ρ j := by
    rw [scaledRow_exact u t ρ tl tn j]
    have e : linearExp a*(quadraticExp b*logistic t) = Q+E := by
      change _ = P*nearestLogistic x+P*(logistic t-nearestLogistic x)
      rw [mul_sub,←mul_assoc]
      change P*logistic t = P*nearestLogistic x+(P*logistic t-P*nearestLogistic x)
      ring
    change scaledCoeff (linearExp a*(quadraticExp b*logistic t)) ρ j = _
    rw [e,scaledCoeff,map_add,mul_add]
    rfl
  have normBound : |scaledCoeff E ρ j| ≤
      (30*exp (a*R+b*R^2))*(ρ/R)^(j+1) := by
    have rr : scaledCoeff E ρ j = (ρ/R)^(j+1)*scaledCoeff E R j := by
      unfold scaledCoeff
      rw [←mul_assoc,←mul_pow,div_mul_cancel₀ _ R0.ne']
    rw [rr,abs_mul,abs_of_pos (pow_pos (div_pos ρ0 R0) _),mul_comm]
    exact mul_le_mul_of_nonneg_right (tilt_scaled_bound a0 b0 R0 (by norm_num) _
      (compact_logistic_tail_bound hx h16) _) (by positivity)
  have mainBound :
      |scaledCoeff Q ρ j-2*(tiltValue a b z*((ρ:ℂ)/z)^(j+1)).re| ≤
      2*exp (a*R+b*R^2)*(ρ/R)^(j+1) := by
    rw [show scaledCoeff Q ρ j = _ from tilted_nearest_coeff a b x j]
    let q : ℂ := ((ρ:ℂ)/z)^(j+1)
    let S := ∑ i ∈ range (j+1), weightedCoeff P z i
    change |2*(q*S).re-2*(tiltValue a b z*q).re| ≤ _
    have nz : ‖q‖=1 := by
      simp only [q,norm_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg ρ0.le,mag]
      simp [ρ0.ne']
    rw [mul_comm (tiltValue a b z) q,←mul_sub,←Complex.sub_re,←mul_sub,
      abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have est := Complex.abs_re_le_norm (q*(S-tiltValue a b z))
    rw [norm_mul,nz,one_mul] at est
    have tail := tilt_truncation a0 b0 R0 z zle j
    rw [mag] at tail
    exact (mul_le_mul_of_nonneg_left (est.trans tail) (by norm_num)).trans_eq (by ring)
  rw [realRow,add_sub_right_comm]
  exact (abs_add_le ..).trans ((add_le_add mainBound normBound).trans_eq (by ring))

#print axioms compact_scaled_row_of_tilt

end LongCycleBounds.MarkedTwo
