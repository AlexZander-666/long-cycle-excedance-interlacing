import LongCycleBounds.MarkedExponentialBias
import Mathlib.RingTheory.PowerSeries.Expand

/-! A signed, finite-degree exponential tilt of an arbitrary input power series. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open MarkedTwo Finset PowerSeries Real
open scoped Classical

/-- The formal exponential of b_a z^a, intrinsic in the mathlib power series ring. -/
def factor (a : ℕ) (ha : 0<a) (b : ℝ) := expand a ha.ne' (linearExp b)

def tilt (b : ℕ → ℝ) : ℕ → PowerSeries ℝ
  | 0 => 1
  | d+1 => factor (d+1) (by omega) (b (d+1)) * tilt b d

/-- Absolute cost at a real radius, including the numerator degree d. -/
def cost (b : ℕ → ℝ) (R : ℝ) (d : ℕ) :=
  ∑ i∈range d, |b (i+1)| * R^(i+1)

theorem factor_scaled {a : ℕ} (ha : 0<a) (b R : ℝ) (F : PowerSeries ℝ) (j : ℕ) :
    scaledCoeff (factor a ha b*F) R j = shiftExp a (b*R^a) (scaledCoeff F R) j := by
  unfold scaledCoeff shiftExp factor
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum]
  let fn (i : ℕ) := R^(j+1) * ((b^(i/a)/(i/a).factorial)*coeff (j-i) F)
  have filt : (∑ i∈range (j+1), R^(j+1)*(coeff i (expand a ha.ne' (linearExp b))*coeff (j-i) F)) =
      ∑ i∈(range (j+1)).filter (a ∣ ·), fn i := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    rw [coeff_expand]
    split_ifs <;> simp [linearExp,coeff_mk,fn]
  rw [filt]
  apply sum_bij' (fun i _ ↦ i/a) (fun l _ ↦ a*l)
  · intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hi).1))))
  · intro l hl
    have le := (Nat.le_div_iff_mul_le ha).mp (Nat.le_of_lt_succ (mem_range.mp hl))
    exact mem_filter.mpr ⟨mem_range.mpr (by rw [mul_comm];omega),dvd_mul_right _ _⟩
  · intro i hi
    exact Nat.mul_div_cancel' (mem_filter.mp hi).2
  · intro l _
    exact Nat.mul_div_cancel_left _ ha
  · intro i hi
    have h := Nat.mul_div_cancel' (mem_filter.mp hi).2
    have le : i≤j := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hi).1)
    simp only [fn,mul_pow,←pow_mul,h]
    rw [show j+1=i+(j-i+1) by omega,pow_add]
    ring

private theorem one_bias {a j : ℕ} (v : ℝ) (M : ℝ) (F : ℕ → ℝ) (hm : 0≤M)
    (h : ∀ i≤j, |F i|≤M) :
    |shiftExp a v F j-F j| ≤ M*(exp |v|-1) := by
  rw [shiftExp,sum_range_succ']
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.mul_zero,Nat.sub_zero,
    one_mul,add_sub_cancel_right]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ i ∈ range (j/a), (|v|^(i+1)/(i+1).factorial)*M := by
          apply sum_le_sum
          intro i _
          rw [abs_mul,abs_div,abs_pow,abs_of_nonneg (by positivity : (0:ℝ)≤(i+1).factorial)]
          exact mul_le_mul_of_nonneg_left (h _ (Nat.sub_le ..)) (by positivity)
    _ ≤ _ := by
      rw [←sum_mul,mul_comm M]
      apply mul_le_mul_of_nonneg_right _ hm
      have s := sum_le_exp_of_nonneg (abs_nonneg v) (j/a+1)
      rw [sum_range_succ'] at s
      simpa using (le_sub_iff_add_le.mpr (by simpa using s) :
        (∑ i∈range (j/a), |v|^(i+1)/(i+1).factorial) ≤ exp |v|-1)

/-- Uniform signed perturbation for all real coefficients b, with no
nonnegativity condition on the input series or the tilt. -/
theorem signed_tilt_bias (b : ℕ → ℝ) {R M : ℝ} (hr : 0≤R) (hm : 0≤M)
    (F : PowerSeries ℝ) (d j : ℕ) (h : ∀ i≤j, |scaledCoeff F R i|≤M) :
    |scaledCoeff (tilt b d*F) R j-scaledCoeff F R j| ≤ M*(exp (cost b R d)-1) := by
  induction d generalizing j with
  | zero => simp [tilt,cost]
  | succ d ih =>
    let old := tilt b d*F
    have cap (i : ℕ) (hi : i≤j) : |scaledCoeff old R i| ≤ M*exp (cost b R d) := by
      have e := ih i (fun l le ↦ h l (le.trans hi))
      have tri := abs_sub_le (scaledCoeff old R i) (scaledCoeff F R i) 0
      simp only [sub_zero] at tri
      change |scaledCoeff old R i-scaledCoeff F R i| ≤ _ at e
      linarith only [tri,e,h i hi]
    have fresh := one_bias (a:=d+1) (j:=j) (b (d+1)*R^(d+1)) _ (scaledCoeff old R)
      (mul_nonneg hm (exp_pos _).le) cap
    rw [←factor_scaled (by omega),abs_mul,abs_of_nonneg (pow_nonneg hr _)] at fresh
    have mid := ih j h
    change |scaledCoeff old R j-scaledCoeff F R j|≤_ at mid
    rw [tilt,mul_assoc]
    apply (abs_sub_le _ (scaledCoeff old R j) _).trans ((add_le_add fresh mid).trans_eq ?_)
    simp only [cost, sum_range_succ,exp_add]
    ring

#print axioms factor_scaled
#print axioms signed_tilt_bias
end LongCycleBounds.FixedCutoff
