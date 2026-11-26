import LongCycleBounds.QuadraticCutoffPoleTails
import LongCycleBounds.FixedCutoffCompactTilt

/-! Absolute coefficient mass for a finite signed exponential tilt. The tail
can be tested beyond the next logistic poles since it involves only the tilt. -/
noncomputable section
namespace LongCycleBounds.QuadraticCutoff
open Real Finset PowerSeries MarkedTwo FixedCutoff

def weighted (P : PowerSeries ℝ) (R : ℝ) (i : ℕ) := R^i*coeff i P

theorem scaled_convolution (P Q : PowerSeries ℝ) (R : ℝ) (j : ℕ) :
    scaledCoeff (P*Q) R j = ∑ i∈range (j+1),weighted P R i*scaledCoeff Q R (j-i) := by
  rw [scaledCoeff,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum]
  apply sum_congr rfl
  intro i hi
  have e : j+1=i+(j-i+1) := by have h := mem_range.mp hi;omega
  unfold weighted scaledCoeff
  rw [e,pow_add]
  ring

/-- Exact ℓ¹ norm upper bound, independent of the length of the coefficient
prefix. A reflected sign choice realizes the prefix as one bounded convolution. -/
theorem tilt_prefix_mass (b : ℕ→ℝ) (d j : ℕ) {R : ℝ} (hR : 0<R) :
    ∑ i∈range (j+1), |weighted (tilt b d) R i| ≤ exp (cost b R d) := by
  let α := weighted (tilt b d) R
  let G := mk fun i : ℕ ↦ (if 0≤α (j-i) then (1:ℝ) else -1)/R^(i+1)
  have val (i : ℕ) : scaledCoeff G R i = if 0≤α (j-i) then 1 else -1 := by
    simp only [scaledCoeff,G,coeff_mk]
    field_simp
  have bound (i : ℕ) (_ : i≤j) : |scaledCoeff G R i|≤1 := by rw [val];split_ifs <;> norm_num
  have exactValue : scaledCoeff (tilt b d*G) R j=∑ i∈range (j+1),|α i| := by
    rw [scaled_convolution]
    apply sum_congr rfl
    intro i hi
    rw [val,show j-(j-i)=i by have h:=mem_range.mp hi;omega]
    change α i*(if 0≤α i then 1 else -1)=_
    split_ifs with h
    · rw [abs_of_nonneg h,mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)];ring
  have hi := tilted_bound b hR.le (by norm_num : (0:ℝ)≤1) G d j bound
  rw [exactValue,abs_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _),one_mul] at hi
  exact hi

theorem tilt_tail_mass (b : ℕ→ℝ) (d j L : ℕ) {ρ R : ℝ} (hr : 0≤ρ) (hR : 0<R) (le : ρ≤R) :
    ∑ i∈(range (j+1)).filter (L≤·), |weighted (tilt b d) ρ i| ≤
      (ρ/R)^L*exp (cost b R d) := by
  have q0 : 0≤ρ/R := by positivity
  have q1 : ρ/R≤1 := (div_le_one₀ hR).mpr le
  calc _ ≤ ∑ i∈(range (j+1)).filter (L≤·), (ρ/R)^L*|weighted (tilt b d) R i| := by
          apply sum_le_sum
          intro i hi
          have eq : weighted (tilt b d) ρ i=(ρ/R)^i*weighted (tilt b d) R i := by
            unfold weighted
            rw [div_pow]
            field_simp
          rw [eq,abs_mul,abs_of_nonneg (pow_nonneg q0 _)]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one q0 q1 (mem_filter.mp hi).2) (abs_nonneg _)
    _ ≤ (ρ/R)^L*∑ i∈range (j+1), |weighted (tilt b d) R i| := by
      rw [Finset.mul_sum]
      apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      exact fun _ _ _ ↦ mul_nonneg (pow_nonneg q0 _) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (tilt_prefix_mass b d j hR) (pow_nonneg q0 _)

/-- Generic split estimate for a signed convolution. The constants in the
small- and large-index regions are independent. -/
theorem weighted_error_split (b : ℕ→ℝ) (d j L : ℕ) {ρ R A D : ℝ} (hp : 0<ρ) (hR : ρ≤R)
    (hA : 0≤A) (hD : 0≤D) (f : ℕ→ℝ) (hf : ∀ i≤j, |f i|≤ if i<L then A else D) :
    |∑ i∈range (j+1), weighted (tilt b d) ρ i*f i| ≤
      A*exp (cost b ρ d)+D*(ρ/R)^L*exp (cost b R d) := by
  let α := weighted (tilt b d) ρ
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ i∈range (j+1), (A*|α i| + if L≤ i then D*|α i| else 0) := by
          apply sum_le_sum
          intro i hi
          have cap := hf i (by have h:=mem_range.mp hi;omega)
          rw [abs_mul,mul_comm]
          by_cases h : i<L
          · simp only [if_pos h] at cap
            simp only [if_neg (by omega : ¬L≤ i),add_zero]
            exact mul_le_mul_of_nonneg_right cap (abs_nonneg _)
          · simp only [if_neg h] at cap
            simp only [if_pos (le_of_not_gt h)]
            exact (mul_le_mul_of_nonneg_right cap (abs_nonneg _)).trans (le_add_of_nonneg_left (mul_nonneg hA (abs_nonneg _)))
    _ = A*(∑ i∈range (j+1),|α i|)+D*(∑ i∈(range (j+1)).filter (L≤·),|α i|) := by
      rw [sum_add_distrib,mul_sum,mul_sum,sum_filter]
    _ ≤ _ := by
      have t := mul_le_mul_of_nonneg_left (tilt_tail_mass b d j L hp.le (hp.trans_le hR) hR) hD
      rw [←mul_assoc] at t
      exact add_le_add (mul_le_mul_of_nonneg_left (tilt_prefix_mass b d j hp) hA) t

#print axioms tilt_prefix_mass
#print axioms tilt_tail_mass
#print axioms weighted_error_split
end LongCycleBounds.QuadraticCutoff
