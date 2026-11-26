import LongCycleBounds.MarkedOuterLabels
import LongCycleBounds.OuterMoments

/-! Perturbations of the ordinary alternating moments; a linear head cutoff
suffices since the individual perturbation is O(n^(-4)). -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset Real Outer

private theorem power_compare {p j : ℕ} (hj : j≤p+1) (x : ℝ) (i : ℕ) :
    weight j x i ≤ ((i:ℝ)+1)*weight p x i := by
  unfold weight
  rw [←mul_assoc,←pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i]) hj) (by positivity)

/-- All four needed positive masses are controlled by a single peak from the
lower row. The deliberately crude cutoff has no finite numerical cases. -/
theorem outer_mass {p j : ℕ} (hj : j≤p+1) {x : ℝ} (hx : 2≤x) :
    ∑' i, weight j x i ≤ ((p:ℝ)+3)*((p:ℝ)+2)*weight p x (mode p x (by linarith)) := by
  have hx' : 0<x := by linarith
  let W := weight p x (mode p x hx')
  let K := ((p:ℝ)+2)*W
  have wk : 0≤K := by dsimp [K,W]; exact mul_nonneg (by positivity) (weight_pos ..).le
  have head (i : ℕ) (hi : i≤p+1) : weight j x i≤K := by
    apply (power_compare hj x i).trans
    apply mul_le_mul _ (weight_le_mode p x hx' i) (weight_pos ..).le (by positivity)
    exact_mod_cast (show i+1≤p+2 by omega)
  have half (i : ℕ) (hi : p+1 ≤ i) : ratio j x i ≤ 1/2 := by
    have ji : (j:ℝ) ≤ (i:ℝ)+1 := by exact_mod_cast (show j ≤ i+1 by omega)
    have e := (div_le_one (by positivity : 0<(i:ℝ)+1)).2 ji
    have h := (ratio_le_exp j x i).trans (exp_le_exp.mpr (show (j:ℝ)/((i:ℝ)+1)-x≤ -1 by linarith))
    apply h.trans
    rw [exp_neg,inv_le_comm₀ (exp_pos _) (by norm_num : (0:ℝ)<1/2)]
    norm_num
    linarith [Real.add_one_le_exp (1:ℝ)]
  have tail (l : ℕ) : weight j x (l+(p+1)) ≤ (1/2:ℝ)^l*K := by
    induction l with
    | zero => simpa using head (p+1) le_rfl
    | succ l ih =>
      rw [show l+1+(p+1)=(l+(p+1))+1 by omega,weight_succ,pow_succ']
      exact (mul_le_mul (half _ (by omega)) ih (weight_pos ..).le (by norm_num)).trans_eq (by ring)
  have geo := (hasSum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/2:ℝ)‖<1)).mul_right K
  have s := summable_weight j x hx'
  rw [←s.sum_add_tsum_nat_add (p+1)]
  have ht := ((summable_nat_add_iff (p+1)).mpr s).tsum_le_tsum tail geo.summable
  rw [geo.tsum_eq] at ht
  have hd := sum_le_sum (s:=range (p+1)) (g:=fun _ ↦ K)
    (fun i hi ↦ head i (by have := mem_range.mp hi;omega))
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_succ] at hd
  norm_num at ht
  change _ ≤ ((p:ℝ)+3)*((p:ℝ)+2)*W
  dsimp [K] at hd ht
  linarith

def rawRow (u : ℝ) (j : ℕ) (x : ℝ) := normalizedRow u j x/(1-time x)

/-- Positive labels use the zero-based indexing of Outer.moment, so the
ordinary signed moment *adds* to the raw row in the discrepancy. -/
theorem raw_outer_error {n j : ℕ} (hn : 1024≤n) (hj : 5≤j) (hjn : j≤n)
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

#print axioms raw_outer_error
#print axioms outer_mass
end LongCycleBounds.MarkedTwo
