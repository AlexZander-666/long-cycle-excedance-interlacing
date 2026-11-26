import LongCycleBounds.CycleProfileCounterexample
import LongCycleFinite.Assembly

namespace LongCycleFinite.K5Prefix

open Polynomial LongCycles LongCycleBounds.CycleProfile
open LongCycleBounds.CycleProfile.Counterexample

def weights (j : ℕ) : ℤ := if j < 5 then 0 else 1

theorem weights_cast : (fun j => (weights j : ℝ)) = profile 5 0 := by
  funext j
  by_cases h : j < 5 <;> simp [weights, profile, h]

theorem row_from_table {n : ℕ} {p : List ℤ} {past : List (List ℤ)}
    (h : coefficientTable weights n = (0 :: p) :: past) :
    enumerator n 5 = X * ofCoeffs p := by
  rw [← row_zero n (by decide : 2 ≤ 5), ← weights_cast, ← coefficients_correct]
  simp [coefficients, h, ofCoeffs]

theorem table_step {n : ℕ} {t : List (List ℤ)} {v : List ℤ}
    (h : coefficientTable weights n = t) (next : advance weights n t = v) :
    coefficientTable weights (n + 1) = v :: t :=
  (congrArg (fun b => advance weights n b :: b) h).trans (congrArg (fun a => a :: t) next)

def OriginalPair (n : ℕ) : Prop :=
  (∃ p q : ℝ[X], enumerator (n-1) 5 = X*p ∧ enumerator n 5 = X*q ∧
    StrictNegativeInterlacing p q (n-3)) ∧
    WeakRealInterlacing (enumerator (n-1) 5) (enumerator n 5)

theorem original_of_window {n : ℕ} {p q : List ℤ} {w : List Window} {x : Dyadic}
    (hp : enumerator (n-1) 5 = X * ofCoeffs p) (hq : enumerator n 5 = X * ofCoeffs q)
    (hw : 0 < w.length) (hd : w.length = n-3) (h : caseOK p q x w = true) :
    OriginalPair n := by
  have hs := caseOK_sound hw h
  exact ⟨⟨_, _, hp, hq, hd ▸ hs⟩, hp ▸ hq ▸ weak_mul_X_of_strict hs⟩

end LongCycleFinite.K5Prefix
