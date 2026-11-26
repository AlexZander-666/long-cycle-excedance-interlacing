import LongCycleBounds.CycleProfileProduct
import LongCycleBounds.CycleProfileNormalization

noncomputable section
namespace LongCycleBounds.CycleProfile
open PowerSeries LongCycles FixedCutoff Band
open MarkedTwo (time)

/-- The actual normalized EGF, defined at every real x. -/
def flow (w : ℕ → ℝ) (x : ℝ) := rescale (1/(1-time x)) (egf w (time x))

theorem coeff_flow (w : ℕ → ℝ) (x : ℝ) (j : ℕ) :
    coeff j (flow w x)=normalizedRow w j x/j.factorial := by
  rw [flow,normalized_coefficient,normalizedRow]
  ring

/-- Derangements have no fixed points before the short-cycle correction is applied. -/
def correction (w : ℕ → ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  if a<2 then 0 else tiltCoefficient w a x

theorem global_tilt {k : ℕ} (w : ℕ → ℝ) (tail : ∀ a≥k,w a=1) (x : ℝ) :
    flow w x=flow (fun _ ↦ 1) x*tilt (fun a ↦ correction w a x) (k-1) := by
  let t:=time x
  let q:=1/(1-t)
  have ident : rescale q (logTilt w t)=finiteLog (fun a ↦ correction w a x) (k-1) := by
    apply PowerSeries.ext
    intro a
    rw [coeff_rescale,logTilt,coeff_mk,coeff_finiteLog]
    by_cases small : a<2
    · simp [small,correction]
    by_cases cut : a<k
    · simp only [small,ite_false,show 1≤a ∧ a≤k-1 by omega,correction]
      dsimp [tiltCoefficient,cycleMoment,moment,q,t,time]
      rw [div_pow,one_pow]
      ring
    · simp [tail a (by omega),small,show ¬(1≤a ∧ a≤k-1) by omega]
  change rescale q (egf w t)=rescale q (egf (fun _ ↦ 1) t)*_
  rw [egf_tilt,map_mul]
  change _*rescale q (expOf (logTilt w t))=_
  rw [rescale_expOf q (logTilt_zero w t),ident,expOf_finiteLog]

#print axioms global_tilt
end LongCycleBounds.CycleProfile
