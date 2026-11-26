import LongCycleBounds.CycleProfileGlobalTilt
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace LongCycleBounds.CycleProfile
open PowerSeries FixedCutoff Finset
open MarkedTwo (linearExp)
open scoped Classical

/-- Differentiation of a size-generating series coefficient by coefficient in a real parameter. -/
def CoeffDeriv (F : ℝ → PowerSeries ℝ) (G : PowerSeries ℝ) (x : ℝ) :=
  ∀ i, HasDerivAt (fun y ↦ coeff i (F y)) (coeff i G) x

theorem coeffDeriv_product {F H : ℝ → PowerSeries ℝ} {G L : PowerSeries ℝ} {x : ℝ}
    (df : CoeffDeriv F G x) (dh : CoeffDeriv H L x) :
    CoeffDeriv (fun y ↦ F y*H y) (G*H x+F x*L) x := by
  intro j
  simp only [map_add,coeff_mul,←Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun ij _ ↦ (df ij.1).mul (dh ij.2)

theorem factor_x {a : ℕ} (ha : 0<a) {b : ℝ → ℝ} {x v : ℝ} (db : HasDerivAt b v x) :
    CoeffDeriv (fun y ↦ factor a ha (b y)) (C v*(factor a ha (b x)*X^a)) x := by
  intro j
  rw [coeff_C_mul,coeff_mul_X_pow']
  by_cases divides : a∣j
  · obtain ⟨q,rfl⟩ := divides
    cases q with
    | zero =>
      simp only [mul_zero,show ¬a≤0 by omega,if_false,mul_zero]
      simpa [factor,coeff_expand,linearExp,coeff_mk] using hasDerivAt_const x (1:ℝ)
    | succ q =>
      have le : a≤a*(q+1) := by rw [Nat.mul_succ];omega
      have sub : a*(q+1)-a=a*q := by rw [Nat.mul_succ];omega
      simp only [le,if_true,sub,factor,coeff_expand_mul,linearExp,coeff_mk]
      apply ((db.pow (q+1)).div_const (((q+1).factorial:ℕ):ℝ)).congr_deriv
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
      simp only [Nat.add_sub_cancel]
      have pos : (q:ℝ)+1≠0 := by positivity
      field_simp
  · have z (y : ℝ) : coeff j (factor a ha (b y))=0 := by simp [factor,coeff_expand,divides]
    simp only [z]
    by_cases le : a≤j
    · have no : ¬a∣j-a := by
        intro h
        exact divides (by simpa [Nat.sub_add_cancel le] using dvd_add h (dvd_refl a))
      simpa [le,factor,coeff_expand,no] using hasDerivAt_const x (0:ℝ)
    · simpa [le] using hasDerivAt_const x (0:ℝ)

theorem tilt_x (b : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (d : ℕ) (x : ℝ)
    (db : ∀ a, 1≤a → a≤d → HasDerivAt (b a) (v a) x) :
    CoeffDeriv (fun y ↦ tilt (fun a ↦ b a y) d)
      (finiteLog v d * tilt (fun a ↦ b a x) d) x := by
  induction d with
  | zero =>
    intro j
    simpa [finiteLog,tilt] using hasDerivAt_const x (coeff j (1 : PowerSeries ℝ))
  | succ d ih =>
    have h := coeffDeriv_product (factor_x (a:=d+1) (by omega) (db (d+1) (by omega) le_rfl))
      (ih (fun a lo hi ↦ db a lo (by omega)))
    intro j
    apply (h j).congr_deriv
    congr 1
    rw [finiteLog,tilt]
    ring

theorem tilt_z (b : ℕ → ℝ) (d : ℕ) :
    derivative ℝ (tilt b d)=derivative ℝ (finiteLog b d)*tilt b d := by
  have hs : HasSubst (finiteLog b d) := by
    apply HasSubst.of_constantCoeff_zero'
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_finiteLog]
    simp
  rw [←expOf_finiteLog,expOf,derivative_subst hs,derivative_exp,mul_comm]

#print axioms tilt_x
#print axioms tilt_z
end LongCycleBounds.CycleProfile
