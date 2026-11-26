import LongCycleBounds.InsertionBoundary

/-! Exact drift cancellation for arbitrary real short-cycle marks. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Band Real LongCycles Polynomial Finset

/-- The term of degree one is correct with w 1=0 after deleting all fixed points. -/
def tiltCoefficient (w : ℕ → ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  (w a-1)*cycleMoment a x/a.factorial

/-- The common mark for all short nonsingleton cycles, extended by 1 above the cutoff. -/
def commonMark (k : ℕ) (u : ℝ) (a : ℕ) : ℝ := if a=1 then 0 else if a<k then u else 1

theorem adjacent_mark_difference (w : ℕ → ℝ) {a : ℕ} (ha : 1≤a) (x : ℝ) :
    deriv (tiltCoefficient w a) x + ((a:ℝ)+1)*tiltCoefficient w (a+1) x =
      (w (a+1)-w a)*cycleMoment (a+1) x/a.factorial := by
  have h := ((cycleMoment_hasDerivAt ha x).const_mul (w a-1)).div_const (a.factorial:ℝ)
  have dt : deriv (tiltCoefficient w a) x=(w a-1)*(-cycleMoment (a+1) x)/a.factorial := h.deriv
  rw [dt,tiltCoefficient,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  field_simp
  ring

/-- Only the transposition and the cutoff-size insertion survive. -/
theorem common_mark_drift {k a : ℕ} (hk : 3≤k) (ha : 1≤a) (u x : ℝ) :
    deriv (tiltCoefficient (commonMark k u) a) x +
      ((a:ℝ)+1)*tiltCoefficient (commonMark k u) (a+1) x =
      (if a=1 then u*cycleMoment 2 x else 0) +
      (if a+1=k then (1-u)*cycleMoment k x/a.factorial else 0) := by
  rw [adjacent_mark_difference _ ha]
  by_cases one : a=1
  · subst a
    simp [commonMark,show 2<k by omega,show 2≠k by omega]
  by_cases endpt : a+1=k
  · subst k
    simp [commonMark,one,show a≠0 by omega]
  by_cases before : a<k
  · simp [commonMark,one,before,endpt,show a+1<k by omega,show a≠0 by omega]
  · simp [commonMark,one,before,endpt,show ¬a+1<k by omega,show a≠0 by omega]

theorem cycleMoment_abs {x : ℝ} (hx : 0≤x) (a : ℕ) :
    |cycleMoment a x| ≤ ((a-1).factorial:ℝ)*exp (-x) := by
  let r := exp (-x)
  have hr : 0<r := exp_pos _
  have r1 : r≤1 := exp_le_one_iff.mpr (by linarith)
  have hEuler (m : ℕ) : |(eulerian m).eval (-r)| ≤ m.factorial := by
    simp only [eulerian,eval_finsetSum,eval_pow,eval_X]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ _ : Equiv.Perm (Fin m), (1:ℝ) := by
          apply sum_le_sum
          intro i _
          rw [abs_pow,abs_neg,abs_of_pos hr]
          exact pow_le_one₀ hr.le r1
      _ = _ := by simp [Fintype.card_perm]
  change |(-r)*(eulerian (a-1)).eval (-r)/(1-(-r))^a| ≤ _
  rw [sub_neg_eq_add,abs_div,abs_mul,abs_neg,abs_of_pos hr,abs_of_pos (by positivity : 0<(1+r)^a)]
  apply (div_le_iff₀ (by positivity)).2
  have den : 1≤(1+r)^a := one_le_pow₀ (by linarith)
  change _ ≤ ((a-1).factorial:ℝ)*r*(1+r)^a
  nlinarith only [mul_le_mul_of_nonneg_left (hEuler (a-1)) hr.le,
    mul_le_mul_of_nonneg_left den (by positivity : 0≤((a-1).factorial:ℝ)*r)]

/-- Uniform input to a signed exponential majorant: at a nonzero order this
is at most exp(-x)/a for all marks in the unit interval. -/
theorem tiltCoefficient_abs {w : ℕ → ℝ} {x : ℝ} (hx : 0≤x) {a : ℕ} (ha : 1≤a)
    (hw : w a ∈ Set.Icc (0:ℝ) 1) :
    |tiltCoefficient w a x| ≤ exp (-x)/(a:ℝ) := by
  have cap : |w a-1|≤1 := by rw [abs_of_nonpos (by linarith [hw.2])];linarith [hw.1]
  rw [tiltCoefficient,abs_div,abs_mul,abs_of_nonneg (by positivity : 0≤(a.factorial:ℝ))]
  have fac : (a:ℝ)*((a-1).factorial:ℝ)=a.factorial := by exact_mod_cast Nat.mul_factorial_pred (by omega : a≠0)
  have ap : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  rw [div_le_div_iff₀ (by positivity) ap]
  have hh := mul_le_mul cap (cycleMoment_abs hx a) (abs_nonneg _) zero_le_one
  rw [←fac]
  nlinarith only [mul_le_mul_of_nonneg_right hh ap.le]

#print axioms adjacent_mark_difference
#print axioms common_mark_drift
#print axioms tiltCoefficient_abs
end LongCycleBounds.FixedCutoff
