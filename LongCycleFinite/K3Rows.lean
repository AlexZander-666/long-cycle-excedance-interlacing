import LongCycleFinite.GammaRows
import LongCycleBounds.UniversalRecurrence
import LongCycleBounds.InitialRows

/-! The executable gamma recurrence for permutations with minimum cycle length three. -/

namespace LongCycleFinite.K3

open Polynomial LongCycles

/-- One gamma step, with index `n` for the old row and `n-2` for the shorter row. -/
def gammaNext (n : ℕ) (a b : List ℤ) : List ℤ :=
  addCoeffs (gammaAdvance (n-2) 0 a) (0 :: scaleCoeffs (Nat.fast_choose n 2 : ℤ) b)

noncomputable section

private theorem expandGamma_increment (d : ℕ) (cs : List ℤ)
    (h : 2 * (cs.length - 1) ≤ d) :
    expandGamma (d+1) cs = (1 + X) * expandGamma d cs := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (-1 : ℝ)).mono ?_
  intro t (ht : -1 < t)
  change (expandGamma (d+1) cs).eval t = ((1 + X) * expandGamma d cs).eval t
  rw [eval_mul, eval_add, eval_one, eval_X, eval_expandGamma _ _ (by omega) ht.ne',
    eval_expandGamma _ _ h ht.ne', pow_succ]
  ring

private theorem eulerian_two : eulerian 2 = 1 + X := by
  have row : descentCoeffs 2 = [1, 1] := by decide +kernel
  rw [← ofCoeffs_descentCoeffs, row]
  norm_num [ofCoeffs]

private theorem enumerator_below_three {n : ℕ} (hn : 0 < n) (hlt : n < 3) :
    enumerator n 3 = 0 := by
  classical
  unfold enumerator
  apply Finset.sum_eq_zero
  intro σ _
  apply if_neg
  intro h
  have hsum : σ.cycleType.toList.sum = n := by
    simp [Equiv.Perm.sum_cycleType, support_univ_of_allowed h (by decide)]
  cases hs : σ.cycleType.toList with
  | nil => simp [hs] at hsum; omega
  | cons m ms =>
    have hm : m ∈ σ.cycleType := by
      have : m ∈ σ.cycleType.toList := by simp [hs]
      simpa using this
    have hl := le_of_mem_cycleType h hm
    simp [hs] at hsum
    omega

/-- The seed gamma row gives the original enumerator at three letters. -/
theorem original_three : enumerator 3 3 = X * expandGamma 1 [1] := by
  rw [LongCycleBounds.beforeSplitRow (by decide : 2 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 3 < 2*3), eulerian_two]
  simp [expandGamma]

theorem original_one : enumerator 1 3 = X * expandGamma 0 [] := by
  simp [expandGamma, enumerator_below_three (by decide : 0 < 1) (by decide : 1 < 3)]

theorem original_two : enumerator 2 3 = X * expandGamma 0 [] := by
  simp [expandGamma, enumerator_below_three (by decide : 0 < 2) (by decide : 2 < 3)]

/-- The gamma recurrence, including the contribution of a newly created 3-cycle,
preserves the identity with the original permutation row. -/
theorem original_succ {n : ℕ} (hn : 3 ≤ n) {a b c : List ℤ}
    (ha : 2 * (a.length - 1) ≤ n-2) (hb : 2 * (b.length - 1) ≤ n-4)
    (old : enumerator n 3 = X * expandGamma (n-2) a)
    (short : enumerator (n-2) 3 = X * expandGamma (n-4) b)
    (step : gammaNext n a b = c) :
    enumerator (n+1) 3 = X * expandGamma (n-1) c := by
  have advance := expandGamma_gammaAdvance (n-2) 0 a ha
  simp only [pow_zero, mul_one, Nat.mul_zero, zero_add] at advance
  rw [LongCycleBounds.Insertion.enumerator_succ (by decide : 2 ≤ 3),
    old, show n+1-3=n-2 by omega, short, eulerian_two, ← step,
    gammaNext, expandGamma_addCoeffs, expandGamma, Int.cast_zero, map_zero, zero_mul, zero_add,
    expandGamma_scaleCoeffs, Int.cast_natCast, Nat.fast_choose,
    ← Nat.choose_eq_descFactorial_div_factorial]
  rw [show n-1=n-2+1 by omega, advance, insertionStep, derivative_mul,
    derivative_X, one_mul, show n-2+1-2=n-1-2 by omega]
  have hcast : ((n-2+1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [show n-2+1=n-1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast, map_sub, map_one]
  by_cases h : 4 ≤ n
  · rw [show n-1-2=n-4+1 by omega, expandGamma_increment _ _ hb]
    ring
  · have h4 : n=3 := by omega
    subst n
    simp only [Nat.reduceSub]
    have hz : expandGamma 0 b = 0 :=
      mul_left_cancel₀ X_ne_zero (short.symm.trans (by simpa [expandGamma] using original_one))
    rw [hz]
    norm_num
    ring

end

private theorem gammaAdvance_length (d j : ℕ) (as : List ℤ)
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

theorem gammaNext_length {n : ℕ} (hn : 3 ≤ n) (a b : List ℤ)
    (ha : 2 * (a.length - 1) ≤ n-2) (hb : 2 * (b.length - 1) ≤ n-4) :
    2 * ((gammaNext n a b).length - 1) ≤ n-1 := by
  have h := gammaAdvance_length (n-2) 0 a ha
  simp only [gammaNext, length_addCoeffs, List.length_cons, scaleCoeffs, List.length_map]
  omega

/-- The three consecutive rows needed by the insertion recurrence. -/
structure GammaState where
  current : List ℤ
  previous : List ℤ
  earlier : List ℤ
  deriving Inhabited

/-- At index zero the state contains the rows of sizes three, two and one. -/
def gammaState : ℕ → GammaState
  | 0 => ⟨[1], [], []⟩
  | n+1 =>
    let s := gammaState n
    ⟨gammaNext (n+3) s.current s.earlier, s.current, s.previous⟩

def gammaRow (n : ℕ) : List ℤ := (gammaState (n-3)).current

private def RowRepresents (n : ℕ) (as : List ℤ) : Prop :=
  2 * (as.length - 1) ≤ n-2 ∧ enumerator n 3 = X * expandGamma (n-2) as

private theorem gammaState_represents (n : ℕ) :
    RowRepresents (n+3) (gammaState n).current ∧
      RowRepresents (n+2) (gammaState n).previous ∧
      RowRepresents (n+1) (gammaState n).earlier := by
  induction n with
  | zero =>
    exact ⟨⟨by decide, original_three⟩, ⟨by decide, original_two⟩, ⟨by decide, original_one⟩⟩
  | succ n ih =>
    obtain ⟨cur, prev, old⟩ := ih
    have holdlen : 2 * ((gammaState n).earlier.length - 1) ≤ n+3-4 := by
      simpa only [show n+1-2=n+3-4 by omega] using old.1
    have hold : enumerator (n+3-2) 3 = X * expandGamma (n+3-4) (gammaState n).earlier := by
      simpa only [show n+3-2=n+1 by omega, show n+3-4=n+1-2 by omega] using old.2
    have exactLen := gammaNext_length (by omega : 3 ≤ n+3)
      _ _ cur.1 holdlen
    have exactRow := original_succ (by omega : 3 ≤ n+3) cur.1 holdlen cur.2 hold rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simpa only [gammaState, show n+1+3-2=n+3-1 by omega] using exactLen
    · simpa only [gammaState, show n+1+3=n+3+1 by omega,
        show n+3+1-2=n+3-1 by omega] using exactRow
    · simpa only [gammaState, show n+1+2=n+3 by omega] using cur
    · simpa only [gammaState, show n+1+1=n+2 by omega] using prev

/-- The executable gamma row represents the actual long-cycle permutations. -/
theorem gammaRow_original {n : ℕ} (h : 3 ≤ n) :
    enumerator n 3 = X * expandGamma (n-2) (gammaRow n) := by
  have rep := (gammaState_represents (n-3)).1
  rw [show n-3+3=n by omega] at rep
  exact rep.2

#print axioms original_succ
#print axioms gammaRow_original

end LongCycleFinite.K3
