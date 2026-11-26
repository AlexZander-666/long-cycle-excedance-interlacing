import LongCycleBounds.CycleProfileEGF
import LongCycleBounds.MarkedLogistic

noncomputable section
namespace LongCycleBounds.CycleProfile
open PowerSeries LongCycles

/-- The exponential of a formal series, used below at zero constant term. -/
def expOf (f : PowerSeries ℝ) : PowerSeries ℝ := (PowerSeries.exp ℝ).subst f

private theorem expOf_const {f : PowerSeries ℝ} (h : f.constantCoeff=0) :
    coeff 0 (expOf f)=1 := by
  have hs := HasSubst.of_constantCoeff_zero' h
  rw [expOf,coeff_subst' hs,finsum_eq_single _ 0]
  · simp [coeff_exp]
  · intro j hj
    rw [coeff_zero_eq_constantCoeff_apply,map_pow,h,zero_pow hj]
    simp

private theorem expOf_deriv {f : PowerSeries ℝ} (h : f.constantCoeff=0) :
    derivative ℝ (expOf f)=derivative ℝ f*expOf f := by
  rw [expOf,derivative_subst (.of_constantCoeff_zero' h),derivative_exp,mul_comm]

theorem expOf_add {f g : PowerSeries ℝ} (hf : f.constantCoeff=0) (hg : g.constantCoeff=0) :
    expOf (f+g)=expOf f*expOf g := by
  have h : (f+g).constantCoeff=0 := by simp [hf,hg]
  refine MarkedTwo.driver_unique (A:=derivative ℝ (f+g)) ?_ (expOf_deriv h) ?_
  · simp only [coeff_zero_eq_constantCoeff_apply, map_mul]
    simpa only [coeff_zero_eq_constantCoeff_apply] using
      (expOf_const h).trans (by rw [expOf_const hf,expOf_const hg,mul_one] : (1:ℝ)=coeff 0 (expOf f)*coeff 0 (expOf g))
  · rw [Derivation.leibniz,expOf_deriv hf,expOf_deriv hg,map_add]
    simp only [smul_eq_mul]
    ring

private theorem deriv_rescale (q : ℝ) (f : PowerSeries ℝ) :
    derivative ℝ (rescale q f)=C q*rescale q (derivative ℝ f) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative,coeff_rescale,coeff_C_mul,coeff_rescale,coeff_derivative,pow_succ]
  ring

theorem rescale_expOf (q : ℝ) {f : PowerSeries ℝ} (hf : f.constantCoeff=0) :
    rescale q (expOf f)=expOf (rescale q f) := by
  have h : (rescale q f).constantCoeff=0 := by
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_rescale,pow_zero,one_mul,coeff_zero_eq_constantCoeff_apply,hf]
  refine MarkedTwo.driver_unique (A:=derivative ℝ (rescale q f)) ?_ ?_ (expOf_deriv h)
  · rw [coeff_rescale,pow_zero,one_mul,expOf_const hf,expOf_const h]
  · rw [deriv_rescale,expOf_deriv hf,map_mul,deriv_rescale,mul_assoc]

private theorem baseline (t : ℝ) : egf (fun _ ↦ 1) t=MarkedTwo.egf 1 t := by
  apply PowerSeries.ext
  intro n
  simp only [egf,MarkedTwo.egf,coeff_mk,MarkedTwo.row_one]
  have base := row_one n 2
  have one : profile 2 1=(fun _ ↦ 1) := by funext j;simp [profile]
  rw [one] at base
  rw [base]

private theorem quadratic_zero : MarkedTwo.quadraticExp 0=1 := by
  apply PowerSeries.ext
  intro n
  by_cases h : n=0
  · subst n
    simp [MarkedTwo.quadraticExp,coeff_mk]
  rw [MarkedTwo.quadraticExp,coeff_mk,coeff_one]
  by_cases even : n%2=0
  · have d : n/2≠0 := by omega
    simp [h,even,zero_pow d]
  · simp [h,even]

/-- Coefficients are the original marked permutations divided by j!(1-t)^j.
The base term is the true derangement logistic expression for all -1 ≤ t ≤ 0. -/
theorem normalized_logistic (w : ℕ → ℝ) (t : ℝ) (lo : -1≤t) (hi : t≤0) :
    rescale (1/(1-t)) (egf w t) =
      C (1-t)*(MarkedTwo.linearExp (-t/(1-t))*
        (expOf (rescale (1/(1-t)) (logTilt w t))*MarkedTwo.logistic t)) := by
  rw [egf_tilt,map_mul,baseline]
  change MarkedTwo.normalizedEGF 1 t*rescale (1/(1-t)) (expOf (logTilt w t))=_
  rw [MarkedTwo.normalizedEGF_logistic 1 t lo hi, rescale_expOf _ (logTilt_zero w t)]
  simp only [sub_self,zero_mul,zero_div,quadratic_zero,one_mul]
  ring

theorem normalized_coefficient (w : ℕ → ℝ) (t : ℝ) (j : ℕ) :
    coeff j (rescale (1/(1-t)) (egf w t)) =
      (row j w).eval t / ((1-t)^j*j.factorial) := by
  rw [coeff_rescale,egf,coeff_mk,div_pow,one_pow]
  ring

#print axioms normalized_logistic
#print axioms normalized_coefficient
#print axioms expOf_add
#print axioms rescale_expOf
end LongCycleBounds.CycleProfile
