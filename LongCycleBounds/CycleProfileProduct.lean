import LongCycleBounds.CycleProfileLogistic
import LongCycleBounds.FixedCutoffCoefficients
import LongCycleBounds.FixedCutoffSignedTilt
import LongCycleBounds.MarkedInsertion

noncomputable section
namespace LongCycleBounds.CycleProfile
open PowerSeries LongCycles MarkedTwo FixedCutoff Band
open scoped Classical

private theorem linear_as_exp (b : ℝ) : linearExp b=rescale b (exp ℝ) := by
  apply PowerSeries.ext
  intro n
  simp [linearExp,coeff_mk,coeff_rescale,coeff_exp,div_eq_mul_inv]

theorem expOf_monomial {a : ℕ} (ha : 0<a) (b : ℝ) :
    expOf (C b * X^a)=factor a ha b := by
  rw [factor,linear_as_exp,expand_apply,rescale_eq_subst,subst_comp_subst_apply (HasSubst.smul_X' b) (HasSubst.X_pow ha.ne')]
  congr 1
  rw [smul_eq_C_mul,subst_mul (.X_pow ha.ne'), subst_C,subst_X (.X_pow ha.ne')]
  rfl

def finiteLog (b : ℕ → ℝ) : ℕ → PowerSeries ℝ
  | 0 => 0
  | d+1 => C (b (d+1))*X^(d+1)+finiteLog b d

theorem coeff_finiteLog (b : ℕ → ℝ) (d j : ℕ) :
    coeff j (finiteLog b d)=if 1≤j ∧ j≤d then b j else 0 := by
  induction d with
  | zero => simp [finiteLog]; omega
  | succ d ih =>
    rw [finiteLog,map_add,coeff_C_mul_X_pow,ih]
    by_cases eq : j=d+1
    · subst j
      simp
    · by_cases h : 1≤j ∧ j≤d
      · simp [eq,h,show 1≤j ∧ j≤d+1 by omega]
      · simp [eq,h,show ¬(1≤j ∧ j≤d+1) by omega]

theorem expOf_finiteLog (b : ℕ → ℝ) (d : ℕ) : expOf (finiteLog b d)=tilt b d := by
  induction d with
  | zero =>
    have r := (rescale_eq_subst (0:ℝ) (exp ℝ)).symm
    simpa [finiteLog,tilt,expOf,rescale_zero,constantCoeff_exp] using r
  | succ d ih =>
    rw [finiteLog,tilt,expOf_add,expOf_monomial (by omega),ih]
    · simp
    · rw [←coeff_zero_eq_constantCoeff_apply,coeff_finiteLog]
      simp

/-- A finite reward profile is exactly a finite product of exponential factors
on the original normalized EGF, including the factor from deleting fixed points. -/
theorem bounded_logistic {k : ℕ} (hk : 2≤k) (w : ℕ → ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x) :
    rescale (1/(1-time x)) (egf w (time x)) =
      C (1-time x)*(tilt (fun a ↦ tiltCoefficient w a x) (k-1)*logistic (time x)) := by
  let t := time x
  let q := 1/(1-t)
  let b := fun a ↦ tiltCoefficient w a x
  have lo : -1≤t := neg_le_neg (Real.exp_le_one_iff.mpr (by linarith))
  have hi : t≤0 := neg_nonpos.mpr (Real.exp_pos _).le
  have hlin : linearExp (-t/(1-t))=expOf (C (-t/(1-t))*X) := by
    rw [linear_as_exp,rescale_eq_subst,smul_eq_C_mul,expOf]
  have term_eq : C (-t/(1-t))*X + rescale q (logTilt w t)=finiteLog b (k-1) := by
    apply PowerSeries.ext
    intro a
    rw [map_add,coeff_C_mul,coeff_X,coeff_rescale,logTilt,coeff_mk,coeff_finiteLog]
    by_cases zero : a=0
    · subst a;simp
    by_cases one : a=1
    · subst a
      have kk : 1≤k-1 := by omega
      simp [kk,b,tiltCoefficient,w1,cycleMoment,moment,t,time,longEulerian_zero]
      ring
    have two : ¬a<2 := by omega
    by_cases cut : a<k
    · simp only [one,ite_false,mul_zero,zero_add,two,
        show 1≤a ∧ a≤k-1 by omega]
      dsimp [b,tiltCoefficient,cycleMoment,moment,q,t,time]
      rw [div_pow,one_pow]
      ring
    · simp [one,two,tail a (by omega),show ¬(1≤a ∧ a≤k-1) by omega]
  have z1 : (C (-t/(1-t))*X : PowerSeries ℝ).constantCoeff=0 := by simp
  have z2 : (rescale q (logTilt w t)).constantCoeff=0 := by
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_rescale,pow_zero,one_mul,coeff_zero_eq_constantCoeff_apply,logTilt_zero]
  change rescale q (egf w t)=C (1-t)*(tilt b (k-1)*logistic t)
  rw [normalized_logistic w t lo hi,hlin,←expOf_finiteLog,←term_eq,expOf_add z1 z2]
  ring

#print axioms expOf_finiteLog
#print axioms bounded_logistic
end LongCycleBounds.CycleProfile
