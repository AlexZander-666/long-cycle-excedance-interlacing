import LongCycleBounds.DerangementAnchor
import LongCycleBounds.MarkedInsertion

noncomputable section
namespace LongCycleBounds.MarkedTwo
open Polynomial LongCycles LongCycleFinite Band Finset Real
open scoped Classical

theorem row_reciprocal (n : ℕ) (u : ℝ) {t : ℝ} (ht : t≠0) :
    t^n*(row n u).eval t⁻¹=(row n u).eval t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases z : n=0
    · subst n
      simp only [pow_zero,one_mul]
      unfold row
      rw [Fintype.sum_unique]
      have e : (default : Equiv.Perm (Fin 0))=1 := Subsingleton.elim _ _
      simp [e,term,twos,excedances,Allowed]
    have formula := row_anchored (n:=n) ⟨0,by omega⟩ u
    rw [formula]
    simp only [eval_finsetSum,mul_sum]
    apply sum_congr rfl
    intro a ha
    obtain ⟨lo,hi⟩ := mem_Icc.mp ha
    have er : t^(a-2)*(eulerian (a-1)).eval t⁻¹=(eulerian (a-1)).eval t := by
      simpa only [show a-2+1=a-1 by omega] using eulerian_reciprocity (a-2) ht
    have shorter := ih (n-a) (by omega)
    simp only [eval_mul,eval_C,eval_X]
    conv_lhs => arg 1; rw [show n=(a-2)+2+(n-a) by omega,pow_add,pow_add]
    rw [←er,←shorter]
    field_simp

theorem markedQuotient_reciprocal {n : ℕ} (hn : 3≤n) {u : ℝ} (hu : u∈Set.Icc 0 1)
    {t : ℝ} (ht : t≠0) :
    t^(n-2)*(markedQuotient n u).eval t⁻¹=(markedQuotient n u).eval t := by
  have h := row_reciprocal n u ht
  rw [(markedQuotient_shape hn hu).2.2.2] at h
  simp only [eval_mul,eval_X] at h
  conv_lhs at h => arg 1; rw [show n=n-2+2 by omega,pow_add]
  have e : t^2*t⁻¹=t := by field_simp
  apply mul_left_cancel₀ ht
  calc _ = (t^(n-2)*t^2)*(t⁻¹*(markedQuotient n u).eval t⁻¹) := by
           linear_combination -(t^(n-2)*(markedQuotient n u).eval t⁻¹)*e
       _ = _ := h

private theorem normalized_deriv_at_zero {p : ℕ} (u x : ℝ)
    (hz : (row p u).eval (time x)=0) :
    deriv (normalizedRow u p) x = -time x*(row p u).derivative.eval (time x)/(1-time x)^p := by
  have dt : HasDerivAt time (-time x) x := (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp [time])
  have den : (1-time x)^p≠0 := by unfold time;rw [sub_neg_eq_add];positivity
  have h := (((row p u).hasDerivAt (time x)).comp x dt).div (((hasDerivAt_const x (1:ℝ)).sub dt).pow p) den
  apply HasDerivAt.deriv
  apply h.congr_deriv
  change (_ * (-time x) * (1-time x)^p-(row p u).eval (time x)*_)/((1-time x)^p)^2=_
  rw [hz,zero_mul,sub_zero]
  field_simp

/-- Half-axis sign test for the true marked rows at all real zeros of the lower quotient. -/
theorem marked_quotient_root_sign {n : ℕ} (hn : 4≤n) {u : ℝ} (hu : u∈Set.Icc 0 1)
    (sign : ∀ x : ℝ,0≤x → normalizedRow u (n-1) x=0 →
      0<normalizedRow u n x*(-deriv (normalizedRow u (n-1)) x))
    {t : ℝ} (ht : t<0) (rt : (markedQuotient (n-1) u).eval t=0) :
    (markedQuotient n u).eval t*(markedQuotient (n-1) u).derivative.eval t<0 := by
  let P := markedQuotient (n-1) u
  let Q := markedQuotient n u
  let D := n-1-2
  have pR {v : ℝ} (hv : v≠0) := markedQuotient_reciprocal (n:=n-1) (by omega) hu hv
  have qR {v : ℝ} (hv : v≠0) := markedQuotient_reciprocal (n:=n) (by omega) hu hv
  have unit (v : ℝ) (hv : v<0) (left : -1≤v) (z : P.eval v=0) : Q.eval v*P.derivative.eval v<0 := by
    let x := -log (-v)
    have hx : 0≤x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have coord : time x=v := by simp only [time,x,neg_neg,exp_log (show 0 < -v by linarith)]
    have hP : row (n-1) u=X*P := (markedQuotient_shape (by omega) hu).2.2.2
    have hQ : row n u=X*Q := (markedQuotient_shape (by omega) hu).2.2.2
    have root : (row (n-1) u).eval (time x)=0 := by rw [coord,hP,eval_mul,z,mul_zero]
    have out := sign x hx (by simp [normalizedRow,root])
    rw [normalized_deriv_at_zero u x root] at out
    unfold normalizedRow at out
    rw [coord,hQ,hP,derivative_mul,derivative_X,one_mul] at out
    simp only [eval_add,eval_mul,eval_X,z,zero_add] at out
    have vp : 0<1-v := by linarith
    by_contra! bad
    have scale : v^3/((1-v)^n*(1-v)^(n-1))≤0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hv.le (sq_nonneg v)]
    have nonpos := mul_nonpos_of_nonpos_of_nonneg scale bad
    apply (not_lt_of_ge nonpos)
    exact out.trans_eq (by field_simp)
  by_cases l : -1≤t
  · exact unit t ht l rt
  have qr : t^(D+1)*Q.eval t⁻¹=Q.eval t := by
    rw [show D+1=n-2 by dsimp [D];omega]
    exact qR ht.ne
  have ri : P.eval t⁻¹=0 := (mul_eq_zero.mp ((pR ht.ne).trans rt)).resolve_left (pow_ne_zero _ ht.ne)
  have inside := unit t⁻¹ (inv_lt_zero.mpr ht) (by rw [inv_eq_one_div,le_div_iff_of_neg ht];linarith) ri
  have pd := reciprocal_derivative_at_root P D (fun v hv ↦ pR hv) ht.ne rt
  have e : t^2*(Q.eval t*P.derivative.eval t)=((-t)*(t^D)^2)*(Q.eval t⁻¹*P.derivative.eval t⁻¹) := by
    rw [←qr,pow_succ]
    linear_combination (t^D*t*Q.eval t⁻¹)*pd
  exact neg_of_mul_neg_right (e.trans_lt (mul_neg_of_pos_of_neg
    (mul_pos (neg_pos.mpr ht) (sq_pos_of_ne_zero (pow_ne_zero _ ht.ne))) inside)) (sq_nonneg t)

/-- A single half-axis sign estimate implies strict and weak interlacing at all marks. -/
theorem marked_original_of_normalized_sign {n : ℕ} (hn : 4≤n)
    (sign : ∀ u∈Set.Icc (0:ℝ) 1, ∀ x : ℝ,0≤x → normalizedRow u (n-1) x=0 →
      0<normalizedRow u n x*(-deriv (normalizedRow u (n-1)) x)) :
    ∀ u∈Set.Icc (0:ℝ) 1,
      StrictNegativeInterlacing (markedQuotient (n-1) u) (markedQuotient n u) (n-3) ∧
        WeakRealInterlacing (row (n-1) u) (row n u) := by
  have anchor := derangement_strict (n-4)
  obtain ⟨_,r,_,_,_,fac,_,_,_,_,_⟩ := anchor
  have seed : (generalCycleQuotient (n-1) 2).Splits := by
    rw [show n-4+3=n-1 by omega] at fac
    rw [fac]
    exact Splits.mul (Splits.C _) (Splits.prod (fun _ _ ↦ Splits.X_sub_C _))
  exact marked_interlacing_of_sign hn seed (fun u hu t ht hz ↦ marked_quotient_root_sign hn hu (sign u hu) ht hz)

#print axioms marked_original_of_normalized_sign
end LongCycleBounds.MarkedTwo
