import LongCycleFinite.GammaRows
import LongCycleBounds.UniversalRecurrence
import LongCycleBounds.InitialRows

/-! The four-cycle cutoff in the gamma basis, derived from maximum-letter insertion. -/

namespace LongCycleFinite
open Polynomial LongCycles

theorem expandGamma_raise (d r : ℕ) (cs : List ℤ)
    (h : 2 * (cs.length - 1) ≤ d) :
    expandGamma (d+r) cs = (1 + X)^r * expandGamma d cs := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (-1 : ℝ)).mono ?_
  intro t (ht : -1 < t)
  change (expandGamma (d+r) cs).eval t = ((1 + X)^r * expandGamma d cs).eval t
  rw [eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_expandGamma _ _ (by omega) ht.ne',
    eval_expandGamma _ _ h ht.ne', pow_add]
  ring

theorem gammaAdvance_length (d j : ℕ) (as : List ℤ)
    (h : 2 * (as.length - 1) ≤ d) :
    2 * ((gammaAdvance d j as).length - 1) ≤ d+1 := by
  induction as generalizing d j with
  | nil => simp [gammaAdvance]
  | cons a as ih =>
    by_cases he : 2 ≤ d
    · have hc : 2 * (as.length - 1) ≤ d-2 := by simp only [List.length_cons] at h; omega
      have ht := ih (d-2) (j+1) hc
      simp only [gammaAdvance, if_neg (by omega : d ≠ 0), List.length_cons, List.length_nil,
        Nat.add_one_sub_one, length_addCoeffs]
      omega
    · have hz : as.length = 0 := by simp only [List.length_cons] at h; omega
      rw [List.length_eq_zero_iff.mp hz]
      by_cases hd : d=0
      · simp [hd, gammaAdvance, addCoeffs]
      · simp [hd, gammaAdvance, addCoeffs]
        omega

namespace K4

/-- Multiplication of a gamma generating polynomial by 1+2y. -/
def gammaLag (b : List ℤ) : List ℤ := addCoeffs b (0 :: scaleCoeffs 2 b)

def gammaNext (n : ℕ) (a b : List ℤ) : List ℤ :=
  addCoeffs (gammaAdvance (n-2) 0 a) (0 :: scaleCoeffs (Nat.fast_choose n 3 : ℤ) (gammaLag b))

theorem expandLag (d : ℕ) (b : List ℤ) (h : 2 * (b.length - 1) ≤ d) :
    expandGamma (d+2) (gammaLag b) = ((1+X)^2+2*X) * expandGamma d b := by
  rw [gammaLag, expandGamma_addCoeffs, expandGamma_raise d 2 b h, expandGamma]
  simp only [Int.cast_zero, map_zero, zero_mul, zero_add, Nat.add_sub_cancel,
    expandGamma_scaleCoeffs, Int.cast_ofNat, map_ofNat]
  ring

private theorem eulerian_three : eulerian 3 = (1+X)^2+2*X := by
  rw [← ofCoeffs_descentCoeffs, show descentCoeffs 3=[1,4,1] by decide +kernel]
  norm_num [ofCoeffs, map_ofNat]
  ring

theorem original_4 : enumerator 4 4 = X * expandGamma 2 [1,2] := by
  rw [LongCycleBounds.beforeSplitRow (by decide : 2 ≤ 4) (by decide : 4 ≤ 4)
    (by decide : 4 < 2*4), ← ofCoeffs_descentCoeffs,
    show descentCoeffs 3 = [1,4,1] by decide +kernel]
  norm_num [ofCoeffs, expandGamma, map_ofNat]
  ring

theorem original_5 : enumerator 5 4 = X * expandGamma 3 [1,8] := by
  rw [LongCycleBounds.beforeSplitRow (by decide : 2 ≤ 4) (by decide : 4 ≤ 5)
    (by decide : 5 < 2*4), ← ofCoeffs_descentCoeffs,
    show descentCoeffs 4 = [1,11,11,1] by decide +kernel]
  norm_num [ofCoeffs, expandGamma, map_ofNat]
  ring

theorem original_6 : enumerator 6 4 = X * expandGamma 4 [1,22,16] := by
  rw [LongCycleBounds.beforeSplitRow (by decide : 2 ≤ 4) (by decide : 4 ≤ 6)
    (by decide : 6 < 2*4), ← ofCoeffs_descentCoeffs,
    show descentCoeffs 5 = [1,26,66,26,1] by decide +kernel]
  norm_num [ofCoeffs, expandGamma, map_ofNat]
  ring

theorem original_7 : enumerator 7 4 = X * expandGamma 5 [1,52,136] := by
  rw [LongCycleBounds.beforeSplitRow (by decide : 2 ≤ 4) (by decide : 4 ≤ 7)
    (by decide : 7 < 2*4), ← ofCoeffs_descentCoeffs,
    show descentCoeffs 6 = [1,57,302,302,57,1] by decide +kernel]
  norm_num [ofCoeffs, expandGamma, map_ofNat]
  ring

/-- Original row preservation, including the two 4-cycles when n+1=8. -/
theorem original_succ {n : ℕ} (hn : 7 ≤ n) {a b c : List ℤ}
    (ha : 2 * (a.length - 1) ≤ n-2) (hb : 2 * (b.length - 1) ≤ n-5)
    (old : enumerator n 4 = X * expandGamma (n-2) a)
    (short : enumerator (n-3) 4 = X * expandGamma (n-5) b)
    (step : gammaNext n a b = c) :
    enumerator (n+1) 4 = X * expandGamma (n-1) c := by
  have advance := expandGamma_gammaAdvance (n-2) 0 a ha
  simp only [pow_zero, mul_one, Nat.mul_zero, zero_add] at advance
  rw [LongCycleBounds.Insertion.enumerator_succ (by decide : 2 ≤ 4), old,
    show n+1-4=n-3 by omega, short, eulerian_three, ← step, gammaNext,
    expandGamma_addCoeffs, expandGamma, Int.cast_zero, map_zero, zero_mul, zero_add,
    expandGamma_scaleCoeffs, Int.cast_natCast, Nat.fast_choose,
    ← Nat.choose_eq_descFactorial_div_factorial]
  rw [show n-1=n-2+1 by omega, advance, insertionStep, derivative_mul,
    derivative_X, one_mul, show n-2+1-2=(n-5)+2 by omega, expandLag _ _ hb]
  have hcast : ((n-2+1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [show n-2+1=n-1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast, map_sub, map_one]
  ring

theorem gammaNext_length {n : ℕ} (hn : 7 ≤ n) (a b : List ℤ)
    (ha : 2 * (a.length - 1) ≤ n-2) (hb : 2 * (b.length - 1) ≤ n-5) :
    2 * ((gammaNext n a b).length - 1) ≤ n-1 := by
  have h := gammaAdvance_length (n-2) 0 a ha
  simp only [gammaNext, gammaLag, length_addCoeffs, List.length_cons, scaleCoeffs, List.length_map]
  omega

structure GammaState where
  current : List ℤ
  previous : List ℤ
  earlier : List ℤ
  oldest : List ℤ
  deriving Inhabited

def gammaState : ℕ → GammaState
  | 0 => ⟨[1,52,136], [1,22,16], [1,8], [1,2]⟩
  | n+1 =>
    let s := gammaState n
    ⟨gammaNext (n+7) s.current s.oldest, s.current, s.previous, s.earlier⟩

def gammaRow (n : ℕ) : List ℤ :=
  if 7 ≤ n then (gammaState (n-7)).current else
    match n with
    | 4 => [1,2]
    | 5 => [1,8]
    | 6 => [1,22,16]
    | _ => []

private def RowRepresents (n : ℕ) (as : List ℤ) : Prop :=
  2 * (as.length - 1) ≤ n-2 ∧ enumerator n 4 = X * expandGamma (n-2) as

private theorem gammaState_represents (n : ℕ) :
    RowRepresents (n+7) (gammaState n).current ∧
      RowRepresents (n+6) (gammaState n).previous ∧
      RowRepresents (n+5) (gammaState n).earlier ∧
      RowRepresents (n+4) (gammaState n).oldest := by
  induction n with
  | zero =>
    exact ⟨⟨by decide, original_7⟩, ⟨by decide, original_6⟩,
      ⟨by decide, original_5⟩, ⟨by decide, original_4⟩⟩
  | succ n ih =>
    obtain ⟨cur, prev, earlier, old⟩ := ih
    have holdlen : 2 * ((gammaState n).oldest.length - 1) ≤ n+7-5 := by
      simpa only [show n+4-2=n+7-5 by omega] using old.1
    have hold : enumerator (n+7-3) 4 = X * expandGamma (n+7-5) (gammaState n).oldest := by
      simpa only [show n+7-3=n+4 by omega, show n+7-5=n+4-2 by omega] using old.2
    have exactLen := gammaNext_length (by omega : 7 ≤ n+7) _ _ cur.1 holdlen
    have exactRow := original_succ (by omega : 7 ≤ n+7) cur.1 holdlen cur.2 hold rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [gammaState, show n+1+7-2=n+7-1 by omega] using exactLen
    · simpa only [gammaState, show n+1+7=n+7+1 by omega,
        show n+7+1-2=n+7-1 by omega] using exactRow
    · exact cur
    · exact prev
    · exact earlier

theorem gammaRow_original {n : ℕ} (h : 4 ≤ n) :
    enumerator n 4 = X * expandGamma (n-2) (gammaRow n) := by
  by_cases h7 : 7 ≤ n
  · have rep := (gammaState_represents (n-7)).1
    rw [show n-7+7=n by omega] at rep
    simpa only [gammaRow, if_pos h7] using rep.2
  · obtain h4 | h5 | h6 : n=4 ∨ n=5 ∨ n=6 := by omega
    · subst n; exact original_4
    · subst n; exact original_5
    · subst n; exact original_6

#print axioms gammaRow_original

end K4
end LongCycleFinite


