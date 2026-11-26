import LongCycleBounds.MarkedLogistic
import LongCycleBounds.PoleBridge
import Mathlib.Analysis.Real.Pi.Bounds

/-! Removing the nearest conjugate pair from the actual logistic series. -/

noncomputable section
namespace LongCycleBounds.MarkedTwo

open Real PowerSeries PoleBridge ComplexConjugate
open scoped Real

def compactRadius (x : ℝ) : ℝ := √(x^2+4*π^2)

def nearestPole (x : ℝ) : ℂ := den x 1

def nearestLogistic (x : ℝ) : PowerSeries ℝ :=
  mk fun j ↦ 2*((nearestPole x)⁻¹^(j+1)).re

def compactLogisticTail (x : ℝ) : PowerSeries ℝ :=
  logistic (-exp (-x))-nearestLogistic x

theorem compactRadius_pos (x : ℝ) : 0 < compactRadius x := by
  unfold compactRadius
  positivity

private theorem compactRadius_sq (x : ℝ) : compactRadius x^2 = x^2+4*π^2 :=
  sq_sqrt (by positivity)

private theorem den_sq (x l : ℝ) : ‖den x l‖^2 = x^2+(l*π)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [den,Complex.add_re,Complex.add_im]
  ring

theorem nearestPole_norm (x : ℝ) : ‖nearestPole x‖ = radius x := by
  apply (sq_eq_sq₀ (norm_nonneg _) (radius_pos x).le).mp
  rw [nearestPole,den_sq,show radius x^2=x^2+π^2 from sq_sqrt (by positivity),one_mul]

theorem compact_geometry {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16) :
    3 < radius x ∧ radius x < 17 ∧ compactRadius x < 18 ∧
      radius x/compactRadius x < 24/25 := by
  have p3 := pi_gt_three
  have p4 : π < 16/5 := pi_lt_d2.trans (by norm_num)
  have rad : radius x^2=x^2+π^2 := sq_sqrt (by positivity)
  have big := compactRadius_sq x
  have xs : x^2 ≤ 256 := by
    have hh := pow_le_pow_left₀ hx h16 2
    norm_num at hh
    exact hh
  have PP : 9 < π^2 ∧ π^2 < (16/5)^2 := by
    refine ⟨?_,pow_lt_pow_left₀ p4 pi_pos.le (by decide : (2:ℕ) ≠ 0)⟩
    have low := pow_lt_pow_left₀ p3 (by norm_num : (0:ℝ)≤3) (by decide : (2:ℕ) ≠ 0)
    norm_num at low
    exact low
  have pp9 := PP.1
  have pp10 := PP.2
  have rp := radius_pos x
  have bp := compactRadius_pos x
  refine ⟨?_,?_,?_,?_⟩
  · exact (sq_lt_sq₀ (by norm_num) rp.le).mp (by nlinarith only [rad,pp9,sq_nonneg x])
  · exact (sq_lt_sq₀ rp.le (by norm_num)).mp (by nlinarith only [rad,xs,pp10])
  · exact (sq_lt_sq₀ bp.le (by norm_num)).mp (by nlinarith only [big,xs,pp10])
  · rw [div_lt_iff₀ bp]
    apply (sq_lt_sq₀ rp.le (by positivity)).mp
    nlinarith only [rad,big,xs,pp9]

private theorem logistic_pos_coeff (x : ℝ) (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    ((coeff j (logistic (-exp (-x))):ℝ):ℂ) = oddPoleSum (j+1) x := by
  have eq := eulerian_eq_oddPoleSum j hj x hx
  simp only [logistic,coeff_mk,logisticMoment,if_neg (by omega : j≠0),sub_neg_eq_add]
  push_cast
  apply (div_eq_iff (by exact_mod_cast j.factorial_ne_zero)).2
  simpa [mul_comm] using eq

private def tailEnvelope (i : ℕ) : ℝ := 9 * (1/((i:ℝ)+1) - 1/((i:ℝ)+2))

private theorem tailEnvelope_nonneg (i : ℕ) : 0 ≤ tailEnvelope i := by
  unfold tailEnvelope
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith)))

private theorem tailEnvelope_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, tailEnvelope i) = 9 * (1-1/((m:ℝ)+1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    unfold tailEnvelope
    push_cast
    ring

private theorem tailEnvelope_mass : Summable tailEnvelope ∧ ∑' i, tailEnvelope i ≤ 9 := by
  have fin (m : ℕ) : (∑ i ∈ Finset.range m, tailEnvelope i) ≤ 9 := by
    rw [tailEnvelope_sum]
    have h : 0 ≤ 1/((m:ℝ)+1) := by positivity
    linarith
  exact ⟨summable_of_sum_range_le tailEnvelope_nonneg fin,
    Real.tsum_le_of_sum_range_le tailEnvelope_nonneg fin⟩

private theorem tail_term {x : ℝ} (hx : 0≤x) (h16 : x≤16) {q : ℕ} (hq : 2≤q) (i : ℕ) :
    ‖((compactRadius x:ℂ)/den x (2*(i:ℝ)+3))^q‖ ≤ tailEnvelope i := by
  let R := compactRadius x
  let l : ℝ := 2*(i:ℝ)+3
  let D := ‖den x l‖
  have lp : 0<l := by dsimp [l]; positivity
  have l3 : 3≤l := by dsimp [l]; linarith [Nat.cast_nonneg (α:=ℝ) i]
  have rpos : 0<R := compactRadius_pos x
  have ds : D^2=x^2+(l*π)^2 := den_sq x l
  have rD : R≤D := by
    apply (sq_le_sq₀ rpos.le (norm_nonneg _)).mp
    rw [show R^2=x^2+4*π^2 from compactRadius_sq x,ds]
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*π)
      (mul_le_mul_of_nonneg_right (show (2:ℝ)≤l by linarith) pi_pos.le) 2
    linarith only [h,show (2*π)^2=4*π^2 by ring]
  have R18 : R<18 := (compact_geometry hx h16).2.2.1
  have Rpi : R≤6*π := by linarith [pi_gt_three]
  have Dpi : l*π ≤ D := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [ds]
    nlinarith only [sq_nonneg x]
  have dp : 0<D := rpos.trans_le rD
  have bounds : 0≤R/D ∧ R/D ≤ 1 := ⟨by positivity,
    (div_le_one₀ dp).mpr rD⟩
  have frac : R/D ≤ 6/l := by
    calc
      _ ≤ (6*π)/(l*π) := div_le_div₀ (by positivity) Rpi (by positivity) Dpi
      _ = _ := by field_simp [ne_of_gt pi_pos]
  rw [norm_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg rpos.le]
  change (R/D)^q ≤ _
  calc
    _ ≤ (R/D)^2 := pow_le_pow_of_le_one bounds.1 bounds.2 hq
    _ ≤ (6/l)^2 := pow_le_pow_left₀ bounds.1 frac 2
    _ ≤ _ := by
      have hi0 : (0:ℝ) ≤ (i:ℝ) := by positivity
      dsimp [l,tailEnvelope]
      field_simp
      nlinarith only [hi0]

private theorem conjugate_odd_den (x : ℝ) (i : ℕ) :
    den x (2*((-(i+1:ℤ) : ℤ):ℝ)+1) = conj (den x (2*(i:ℝ)+1)) := by
  apply Complex.ext <;> simp [den,Complex.add_re,Complex.add_im]
  ring

private theorem radius_pole_sum (x : ℝ) (q : ℕ) (R : ℝ)
    (sf : Summable (fun i : ℕ ↦ ((R:ℂ)/den x (2*(i:ℝ)+1))^q)) :
    ((R:ℂ)^q*oddPoleSum q x).re =
      2*(∑' i : ℕ, ((R:ℂ)/den x (2*(i:ℝ)+1))^q).re := by
  let F (i : ℤ) := ((R:ℂ)/den x (2*(i:ℝ)+1))^q
  have same (i : ℕ) : F (-(i+1:ℤ)) = conj (F i) := by
    simp only [F,conjugate_odd_den,map_pow,map_div₀,Complex.conj_ofReal,Int.cast_natCast]
  have sn : Summable (fun i : ℕ ↦ F (-(i+1:ℤ))) := by
    simp only [same]
    exact Complex.summable_conj.mpr sf
  have both := Summable.of_nat_of_neg_add_one (show Summable (fun i : ℕ ↦ F i) from sf) sn
  have identity : (R:ℂ)^q*oddPoleSum q x = ∑' i : ℤ, F i := by
    unfold oddPoleSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro i
    unfold F den
    push_cast
    rw [div_pow]
    ring
  rw [identity,←tsum_nat_add_neg_add_one both]
  simp only [same]
  change (∑' i : ℕ, (((R:ℂ)/den x (2*(i:ℝ)+1))^q+
    conj (((R:ℂ)/den x (2*(i:ℝ)+1))^q))).re = _
  rw [Summable.tsum_add sf (Complex.summable_conj.mpr sf),←Complex.conj_tsum]
  simp only [Complex.add_re,Complex.conj_re]
  ring

/-- The part beyond the nearest conjugate pair has bounded coefficients on
the larger radius. This includes the actual constant coefficient. -/
theorem compact_logistic_tail_bound {x : ℝ} (hx : 0≤x) (h16 : x≤16) (j : ℕ) :
    |scaledCoeff (compactLogisticTail x) (compactRadius x) j| ≤ 30 := by
  let R := compactRadius x
  let t := -exp (-x)
  have rp : 0<R := compactRadius_pos x
  obtain ⟨rho3,_,R18,_⟩ := compact_geometry hx h16
  by_cases hj : j=0
  · subst j
    have l0 : 0 ≤ 1/(1-t) ∧ 1/(1-t) ≤ 1 := by
      have tneg : t≤0 := (neg_nonpos.mpr (exp_pos _).le)
      constructor
      · exact div_nonneg (by norm_num) (by linarith)
      · apply (div_le_one₀ (by linarith : 0<1-t)).mpr
        linarith
    have nr : |((nearestPole x)⁻¹).re| ≤ 1/3 := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_inv,nearestPole_norm,←one_div]
        exact one_div_le_one_div_of_le (by norm_num) rho3.le
    simp only [scaledCoeff,compactLogisticTail,map_sub,logistic,nearestLogistic,coeff_mk,
      logisticMoment,if_true,Nat.factorial_zero,Nat.cast_one,div_one,zero_add,pow_one]
    change |R*(1/(1-t)-2*((nearestPole x)⁻¹).re)| ≤ 30
    rw [abs_mul,abs_of_pos rp]
    have z := abs_sub (1/(1-t)) (2*((nearestPole x)⁻¹).re)
    rw [abs_of_nonneg l0.1,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at z
    exact mul_le_mul R18.le (by linarith only [z,l0.2,nr] : |1/(1-t)-2*((nearestPole x)⁻¹).re|≤5/3)
      (abs_nonneg _) (by norm_num) |>.trans (by norm_num)
  · let q := j+1
    let f (i : ℕ) := ((R:ℂ)/den x (2*(i:ℝ)+1))^q
    let F (i : ℕ) := ((R:ℂ)/den x (2*(i:ℝ)+3))^q
    have cmp (i : ℕ) : ‖F i‖ ≤ tailEnvelope i := tail_term hx h16 (by dsimp [q];omega) i
    have sf : Summable (fun i ↦ ‖F i‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) cmp tailEnvelope_mass.1
    have eq (i : ℕ) : f (i+1)=F i := by
      unfold f F
      push_cast
      ring_nf
    have full : Summable f := (summable_nat_add_iff (f:=f) 1).1
      (sf.of_norm.congr fun i ↦ (eq i).symm)
    have sum := radius_pole_sum x q R full
    change ((R:ℂ)^q*oddPoleSum q x).re = 2*(∑' i, f i).re at sum
    rw [full.tsum_eq_zero_add] at sum
    simp only [eq,Complex.add_re] at sum
    have a : R^q*coeff j (logistic t) = ((R:ℂ)^q*oddPoleSum q x).re := by
      rw [←logistic_pos_coeff x hx (by omega : 1≤j)]
      rw [←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
    have b : R^q*coeff j (nearestLogistic x) = 2*(f 0).re := by
      simp only [nearestLogistic,coeff_mk,f,Nat.cast_zero,mul_zero,zero_add,q]
      change R^(j+1)*(2*((nearestPole x)⁻¹^(j+1)).re) = _
      rw [show den x 1 = nearestPole x from rfl,div_eq_mul_inv,mul_pow]
      rw [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      ring
    unfold scaledCoeff compactLogisticTail
    rw [map_sub,mul_sub]
    change |R^q*coeff j (logistic t)-R^q*coeff j (nearestLogistic x)| ≤ _
    rw [a,b,sum]
    have mass : ‖∑' i, F i‖ ≤ 9 :=
      (norm_tsum_le_tsum_norm sf).trans ((sf.tsum_le_tsum cmp tailEnvelope_mass.1).trans tailEnvelope_mass.2)
    have := (Complex.abs_re_le_norm (∑' i, F i)).trans mass
    ring_nf
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith only [this]

#print axioms compact_geometry
#print axioms compact_logistic_tail_bound

end LongCycleBounds.MarkedTwo
