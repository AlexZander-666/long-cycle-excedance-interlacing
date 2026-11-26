import LongCycleBounds.CycleProfileCalculus
import LongCycleBounds.FixedCutoffReadout

noncomputable section
namespace LongCycleBounds.CycleProfile
open LongCycles Finset PowerSeries FixedCutoff Band
open MarkedTwo (time)
open scoped Classical

private theorem baseTransport (x : ℝ) : CoeffDeriv (flow (fun _ ↦ 1))
    (C (time x/(1-time x)^2)*(flow (fun _ ↦ 1) x*X) - PowerSeries.derivative ℝ (flow (fun _ ↦ 1) x)) x := by
  intro j
  simp only [coeff_flow,map_sub,coeff_C_mul,coeff_derivative]
  have origin (y : ℝ) : normalizedRow (fun _ ↦ 1) 0 y = 1 := by
    simpa [egf,normalizedRow,coeff_mk] using egf_constant (fun _ ↦ 1) (time y)
  have one (y : ℝ) : normalizedRow (fun _ ↦ 1) 1 y = 0 := by
    have r := row_succ_eval 0 (fun _ ↦ 1) (time y)
    simp [cycleDerivativeCoeff] at r
    simp [normalizedRow,r]
  cases j with
  | zero =>
    simp only [origin,coeff_zero_mul_X,mul_zero,one,Nat.factorial_zero,
      Nat.cast_one,div_one,zero_div,zero_mul,sub_zero]
    exact hasDerivAt_const x 1
  | succ m =>
    rw [coeff_succ_mul_X,coeff_flow]
    have hc := (Insertion.universal_hasDerivAt (n:=m+1) (k:=2) (by decide) (by omega) x).div_const
      ((m+1).factorial:ℝ)
    have actual (q : ℕ) : normalizedRow (fun _ ↦ 1) q = Band.normalizedEnumerator q 2 := by
      funext y
      have one : (fun _ : ℕ ↦ (1:ℝ))=profile 2 1 := by funext a;simp [profile]
      rw [one,normalizedRow_one]
    simp only [actual]
    apply hc.congr_deriv
    rw [show m+1+1-2=m by omega]
    simp only [Nat.reduceSubDiff,Nat.choose_one_right,Band.cycleMoment,Band.moment,
      longEulerian_one,Polynomial.eval_one,mul_one]
    rw [Nat.factorial_succ (m+1),Nat.cast_mul,Nat.cast_succ]
    simp only [Nat.cast_succ]
    rw [Nat.factorial_succ m,Nat.cast_mul,Nat.cast_succ]
    unfold time
    field_simp


theorem correction_hasDerivAt (w : ℕ → ℝ) (a : ℕ) (x : ℝ) :
    HasDerivAt (correction w a) (deriv (correction w a) x) x := by
  by_cases h : a<2
  · have e : correction w a=fun _ ↦ 0 := by funext;simp [correction,h]
    rw [e,deriv_const]
    exact hasDerivAt_const x 0
  · have e : correction w a=tiltCoefficient w a := by funext;simp [correction,h]
    rw [e]
    exact (((cycleMoment_hasDerivAt (by omega : 1≤a) x).const_mul (w a-1)).div_const (a.factorial:ℝ)).differentiableAt.hasDerivAt

theorem profile_transport {k : ℕ} (w : ℕ→ℝ) (tail : ∀ a≥k,w a=1) (x : ℝ) :
    CoeffDeriv (flow w)
      ((C (time x/(1-time x)^2)*X +
         finiteLog (fun a ↦ deriv (correction w a) x) (k-1) +
         derivative ℝ (finiteLog (fun a ↦ correction w a x) (k-1))) * flow w x -
       derivative ℝ (flow w x)) x := by
  have h := coeffDeriv_product (baseTransport x) (tilt_x (correction w)
    (fun a ↦ deriv (correction w a) x) (k-1) x (fun a _ _ ↦ correction_hasDerivAt w a x))
  intro i
  simp_rw [global_tilt w tail]
  apply (h i).congr_deriv
  congr 1
  rw [Derivation.leibniz,tilt_z]
  simp only [smul_eq_mul]
  ring

#print axioms profile_transport
end LongCycleBounds.CycleProfile
