import LongCycleFinite.K4Rows

namespace LongCycleFinite.K4

/-- Advance from any previously certified coefficient pair, without unfolding
the state back to the first row. The right-hand lag is the row at n−3. -/
theorem gammaRow_next {n : ℕ} (hn : 7 ≤ n) :
    gammaRow (n+1) = gammaNext n (gammaRow n) (gammaRow (n-3)) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        have h₁ : 7+i.succ.succ.succ+1-7=i+4 := by omega
        have h₂ : 7+i.succ.succ.succ-7=i+3 := by omega
        have h₃ : 7+i.succ.succ.succ-3-7=i := by omega
        simp only [gammaRow, if_pos (by omega : 7 ≤ 7+i.succ.succ.succ+1),
          if_pos (by omega : 7 ≤ 7+i.succ.succ.succ),
          if_pos (by omega : 7 ≤ 7+i.succ.succ.succ-3), h₁,h₂,h₃]
        change gammaNext (i+3+7) _ _ = gammaNext (7+i.succ.succ.succ) _ _
        rw [show i+3+7=7+i.succ.succ.succ by omega]
        rfl

theorem gammaRow_next_of_eq {n : ℕ} (hn : 7 ≤ n) {a b c : List ℤ}
    (old : gammaRow n = a) (lag : gammaRow (n-3) = b) (step : gammaNext n a b = c) :
    gammaRow (n+1) = c := by
  rw [gammaRow_next hn, old, lag, step]

#print axioms gammaRow_next_of_eq

end LongCycleFinite.K4
