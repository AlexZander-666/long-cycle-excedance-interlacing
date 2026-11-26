import LongCycleBounds.CycleProfile
import LongCycleBounds.MarkedTwoEGF

/-! Formal cycle series attached to an arbitrary real profile on cycle lengths. -/
noncomputable section
namespace LongCycleBounds.CycleProfile
open LongCycles Finset Polynomial
open scoped Classical

private theorem row_empty (w : ℕ → ℝ) : row 0 w = 1 := by
  unfold row
  rw [Fintype.sum_unique]
  have e : (default : Equiv.Perm (Fin 0))=1 := Subsingleton.elim _ _
  simp [e,term,cycleWeight,excedances,Allowed]

/-- The derivative of the single-cycle EGF, before factorial normalization. -/
def cycleDerivativeCoeff (w : ℕ → ℝ) (t : ℝ) (d : ℕ) : ℝ :=
  if d=0 then 0 else (w (d+1))*t*(eulerian d).eval t

theorem row_succ_eval (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    (row (n+1) w).eval t = ∑ d ∈ range (n+1),
      ((n.choose d : ℕ):ℝ)*cycleDerivativeCoeff w t d*(row (n-d) w).eval t := by
  rw [row_anchored (Fin.last n) w, eval_finsetSum]
  simp only [eval_mul,eval_C,eval_X,Nat.add_sub_cancel]
  let w (d : ℕ) := ((n.choose d : ℕ):ℝ)*cycleDerivativeCoeff w t d*(row (n-d) w).eval t
  change _ = ∑ d ∈ range (n+1), w d
  have skip : ∑ d ∈ Icc 1 n, w d = ∑ d ∈ range (n+1), w d := by
    apply sum_subset
    · intro d h
      exact mem_range.mpr (by have := (mem_Icc.mp h).2;omega)
    · intro d h miss
      have eq : d=0 := by
        have := mem_range.mp h
        by_contra! ne
        exact miss (mem_Icc.mpr ⟨by omega,by omega⟩)
      simp [w,eq,cycleDerivativeCoeff]
  rw [←skip]
  refine sum_bij' (fun a _ ↦ a-1) (fun d _ ↦ d+1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro d hd
    have := mem_Icc.mp hd
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a ha
    have := mem_Icc.mp ha
    omega
  · intro d _
    omega
  · intro a ha
    have := mem_Icc.mp ha
    have pos : a-1 ≠ 0 := by omega
    have sw : a-1+1=a := by omega
    have tail : n+1-a = n-(a-1) := by omega
    simp [w,cycleDerivativeCoeff,pos,sw,tail,mul_assoc]

def egf (w : ℕ → ℝ) (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ (row n w).eval t / n.factorial

def cycleDriver (w : ℕ → ℝ) (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ cycleDerivativeCoeff w t n / n.factorial

theorem egf_constant (w : ℕ → ℝ) (t : ℝ) : PowerSeries.coeff 0 (egf w t) = 1 := by
  simp [egf,PowerSeries.coeff_mk,row_empty]

theorem egf_derivative (w : ℕ → ℝ) (t : ℝ) :
    PowerSeries.derivative ℝ (egf w t) = cycleDriver w t * egf w t := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [egf,cycleDriver,PowerSeries.coeff_mk]
  rw [row_succ_eval,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have nz : (n:ℝ)+1≠0 := by positivity
  have fac : (n.factorial:ℝ)≠0 := by positivity
  rw [show ∀ a : ℝ, a/(((n:ℝ)+1)*n.factorial)*((n:ℝ)+1)=a/n.factorial by intro a;field_simp]
  rw [sum_div]
  apply sum_congr rfl
  intro d hd
  have le : d≤n := by have := mem_range.mp hd;omega
  have comb : (n.choose d:ℝ)*d.factorial*(n-d).factorial=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial le
  have nf : (d.factorial:ℝ)≠0 := by positivity
  have mf : ((n-d).factorial:ℝ)≠0 := by positivity
  field_simp
  linear_combination (cycleDerivativeCoeff w t d * (row (n-d) w).eval t) * comb



/-- Logarithm of the change relative to ordinary derangements. Its jth
coefficient is the signed weight change for a labelled j-cycle, divided by j!. -/
def logTilt (w : ℕ → ℝ) (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun a ↦ if a<2 then 0 else
    (w a-1)*t*(eulerian (a-1)).eval t/(a.factorial:ℝ)

theorem logTilt_zero (w : ℕ → ℝ) (t : ℝ) : (logTilt w t).constantCoeff=0 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logTilt,PowerSeries.coeff_mk]

theorem finite_tilt_support (k : ℕ) (u t : ℝ) {a : ℕ} (ha : k≤a) :
    PowerSeries.coeff a (logTilt (profile k u) t)=0 := by
  simp [logTilt,PowerSeries.coeff_mk,profile,not_lt.mpr ha]

theorem driver_tilt (w : ℕ → ℝ) (t : ℝ) :
    cycleDriver w t = cycleDriver (fun _ ↦ 1) t + PowerSeries.derivative ℝ (logTilt w t) := by
  apply PowerSeries.ext
  intro d
  rw [map_add,PowerSeries.coeff_derivative]
  by_cases h : d=0
  · subst d
    simp [cycleDriver,cycleDerivativeCoeff,logTilt,PowerSeries.coeff_mk]
  · have ha : ¬ d+1<2 := by omega
    simp only [cycleDriver,cycleDerivativeCoeff,logTilt,PowerSeries.coeff_mk,if_neg h,if_neg ha,
      Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,one_mul]
    have h1 : (d:ℝ)+1≠0 := by positivity
    have h2 : (d.factorial:ℝ)≠0 := by positivity
    field_simp
    ring

theorem expTilt_constant (w : ℕ → ℝ) (t : ℝ) :
    PowerSeries.coeff 0 ((PowerSeries.exp ℝ).subst (logTilt w t))=1 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (logTilt_zero w t)
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,logTilt_zero,zero_pow hj]
    simp

/-- The exact EGF equals the ordinary derangement EGF times the exponential
of the signed cycle corrections, including at nonpositive weights. -/
theorem egf_tilt (w : ℕ → ℝ) (t : ℝ) :
    egf w t = egf (fun _ ↦ 1) t * (PowerSeries.exp ℝ).subst (logTilt w t) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (logTilt_zero w t)
  refine MarkedTwo.driver_unique (A:=cycleDriver w t) ?_ (egf_derivative w t) ?_
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul]
    have z := egf_constant w t
    have b := egf_constant (fun _ ↦ 1) t
    have c := expTilt_constant w t
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at z b c
    rw [z,b,c,mul_one]
  · rw [Derivation.leibniz,egf_derivative,PowerSeries.derivative_subst hs,PowerSeries.derivative_exp,driver_tilt w t]
    simp only [smul_eq_mul]
    ring

#print axioms finite_tilt_support
#print axioms driver_tilt
#print axioms egf_tilt
end LongCycleBounds.CycleProfile
