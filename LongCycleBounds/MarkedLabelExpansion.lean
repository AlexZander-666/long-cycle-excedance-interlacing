import LongCycleBounds.MarkedLogistic

/-! Absolutely summable label representation of the genuine transposition-marked row. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset PowerSeries Real
open scoped Classical

theorem logistic_labels {t : ℝ} (ht : ‖t‖ < 1) (i : ℕ) :
    HasSum (fun h : ℕ ↦ t^h * coeff i (linearExp (h:ℝ))) (coeff i (logistic t)) := by
  have ev : logisticMoment t i = ∑' h : ℕ, (h:ℝ)^i*t^h := by
    by_cases z : i=0
    · subst i
      simp [logisticMoment,tsum_geometric_of_norm_lt_one ht,one_div]
    · simpa [logisticMoment,z] using eulerian_eq_powerSeries i (by omega) t ht
  simp only [linearExp,logistic,coeff_mk,ev]
  rw [div_eq_mul_inv]
  apply ((summable_pow_mul_geometric_of_norm_lt_one i ht).hasSum.mul_right
    (i.factorial:ℝ)⁻¹).congr_fun
  intro h
  ring

/-- Every formal coefficient takes a finite convolution, so no topology
on the ambient formal series is needed to exchange the label sum. -/
theorem mul_logistic_labels {t : ℝ} (ht : ‖t‖<1) (W : PowerSeries ℝ) (j : ℕ) :
    HasSum (fun h : ℕ ↦ t^h * coeff j (W * linearExp (h:ℝ))) (coeff j (W * logistic t)) := by
  simp only [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
  have hs := hasSum_sum (s:=range (j+1)) (fun i _ ↦
    (logistic_labels ht (j-i)).mul_left (coeff i W))
  apply hs.congr_fun
  intro h
  apply sum_congr rfl
  intro i _
  ring

/-- Includes the zero label. Its contribution can be controlled separately
by `coeff_bias_zero_label`, while `label_bounds` controls each positive label. -/
theorem markedRow_label_expansion (u t : ℝ) (ht : ‖t‖<1) (hi : t≤0) (j : ℕ) :
    HasSum (fun h : ℕ ↦ t^h * labelCoefficient (-t/(1-t))
      ((u-1)*t/(2*(1-t)^2)) (h:ℝ) j) ((row j u).eval t/(1-t)^(j+1)) := by
  have lt : -1<t := (abs_lt.mp ((Real.norm_eq_abs _).symm ▸ ht)).1
  have z : 1-t≠0 := by linarith
  let a := -t/(1-t)
  let b := (u-1)*t/(2*(1-t)^2)
  have s := (mul_logistic_labels ht (linearExp a*quadraticExp b) j).mul_left (j.factorial:ℝ)
  have val := scaledRow_exact u t 1 lt.le hi j
  simp only [scaledRow,scaledCoeff,one_pow,one_mul] at val
  change (row j u).eval t / ((1-t)^(j+1)*j.factorial) =
    coeff j (linearExp a*(quadraticExp b*logistic t)) at val
  have fix : (row j u).eval t/(1-t)^(j+1) =
      (j.factorial:ℝ)*coeff j (linearExp a*quadraticExp b*logistic t) := by
    rw [mul_assoc,←val]
    field_simp
  rw [fix]
  apply s.congr_fun
  intro h
  change t^h * ((j.factorial:ℝ)*coeff j (linearExp a*(quadraticExp b*linearExp (h:ℝ)))) = _
  rw [mul_assoc (linearExp a)]
  ring

#print axioms markedRow_label_expansion
end LongCycleBounds.MarkedTwo
