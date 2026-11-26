import LongCycleBounds.CycleProfileTransport

noncomputable section
namespace LongCycleBounds.CycleProfile
open Finset PowerSeries FixedCutoff Band
open MarkedTwo (time)
open scoped Classical

theorem transport_driver {k : ℕ} (hk : 3≤k) (w : ℕ→ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) (x : ℝ) :
    C (time x/(1-time x)^2)*X + finiteLog (fun a ↦ deriv (correction w a) x) (k-1) +
       derivative ℝ (finiteLog (fun a ↦ correction w a x) (k-1)) =
         finiteLog (fun a ↦ drift w a x) (k-1) := by
  apply PowerSeries.ext
  intro j
  have next : coeff (j+1) (finiteLog (fun a ↦ correction w a x) (k-1))=correction w (j+1) x := by
    rw [coeff_finiteLog]
    by_cases h : j+1≤k-1
    · simp [h]
    · simp [h,correction,tiltCoefficient,tail (j+1) (by omega)]
  rw [map_add,map_add,coeff_C_mul,coeff_X,coeff_derivative,next,coeff_finiteLog,coeff_finiteLog]
  by_cases z : j=0
  · subst j
    simp [correction]
  by_cases on : j=1
  · subst j
    have co : correction w 1=fun _ ↦ 0 := by funext;simp [correction]
    simp [co,show 1≤k-1 by omega,correction,tiltCoefficient,drift,w1,cycleMoment,moment,time,longEulerian_one]
    ring
  have two : ¬ j<2 := by omega
  have nextTwo : ¬j+1<2 := by omega
  have c : correction w j=tiltCoefficient w j := by funext;simp [correction,two]
  by_cases le : j≤k-1
  · simp only [on,ite_false,mul_zero,zero_add,show 1≤j ∧ j≤k-1 by omega,c,correction,nextTwo]
    rw [mul_comm (tiltCoefficient _ _ _)]
    exact adjacent_mark_difference w (by omega) x
  · simp [on,le,correction,nextTwo,tiltCoefficient,tail (j+1) (by omega)]

theorem convolution_finiteLog (b : ℕ→ℝ) (F : PowerSeries ℝ) {p d : ℕ} (hd : d≤p) :
    coeff p (finiteLog b d*F)=∑ i∈range d,b (i+1)*coeff (p-(i+1)) F := by
  induction d with
  | zero => simp [finiteLog]
  | succ d ih =>
    rw [finiteLog,add_mul,map_add,ih (by omega),sum_range_succ]
    rw [show (C (b (d+1))*X^(d+1))*F=C (b (d+1))*(F*X^(d+1)) by ring,
      coeff_C_mul,coeff_mul_X_pow',if_pos hd,add_comm]

theorem normalizedRow_insertion {k p : ℕ} (hk : 3≤k) (hp : k-1≤p) (w : ℕ→ℝ)
    (w1 : w 1=0) (tail : ∀ a≥k,w a=1) (x : ℝ) :
    normalizedRow w (p+1) x + deriv (normalizedRow w p) x =
      ∑ i∈range (k-1),(p.descFactorial (i+1):ℝ)*drift w (i+1) x*normalizedRow w (p-(i+1)) x := by
  have h := profile_transport w tail x p
  rw [transport_driver hk w w1 tail, map_sub,convolution_finiteLog _ _ hp,coeff_derivative] at h
  simp only [coeff_flow] at h
  have pf : (p.factorial:ℝ)≠0 := by positivity
  have e (y : ℝ) : normalizedRow w p y/p.factorial*(p.factorial:ℝ)=normalizedRow w p y := div_mul_cancel₀ _ pf
  have mult := h.mul_const (p.factorial:ℝ)
  change HasDerivAt (fun y ↦ normalizedRow w p y/p.factorial*(p.factorial:ℝ)) _ x at mult
  simp only [e] at mult
  rw [mult.deriv,sub_mul,Finset.sum_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  have pp : (p:ℝ)+1≠0 := by positivity
  have cancel : normalizedRow w (p+1) x/(((p:ℝ)+1)*p.factorial)*((p:ℝ)+1)*p.factorial =
      normalizedRow w (p+1) x := by field_simp
  rw [cancel,add_sub_cancel]
  apply sum_congr rfl
  intro i hi
  have le : i+1≤p := (Finset.mem_range.mp hi).trans_le hp
  have fac : ((p-(i+1)).factorial:ℝ)*p.descFactorial (i+1)=p.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial le
  have nz : ((p-(i+1)).factorial:ℝ)≠0 := by positivity
  field_simp
  linear_combination (drift w (i+1) x*normalizedRow w (p-(i+1)) x)*fac.symm

#print axioms normalizedRow_insertion
end LongCycleBounds.CycleProfile
