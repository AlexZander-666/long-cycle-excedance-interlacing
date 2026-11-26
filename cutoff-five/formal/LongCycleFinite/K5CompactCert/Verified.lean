import LongCycleFinite.K5CompactCert.Data
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! # Kernel-checked table and real interval coverage -/

namespace LongCycleFinite.K5CompactCert

private def validRows (rows : List Cell) : Bool := rows.all (fun c ↦ decide c.Valid)

private theorem validRows_append (a b : List Cell) :
    validRows (a ++ b) = (validRows a && validRows b) := List.all_append

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem checked0 : validRows chunk0 = true := by decide +kernel
private theorem checked1 : validRows chunk1 = true := by decide +kernel
private theorem checked2 : validRows chunk2 = true := by decide +kernel
private theorem checked3 : validRows chunk3 = true := by decide +kernel
private theorem checked4 : validRows chunk4 = true := by decide +kernel
private theorem checked5 : validRows chunk5 = true := by decide +kernel
private theorem checked6 : validRows chunk6 = true := by decide +kernel
private theorem checked7 : validRows chunk7 = true := by decide +kernel
private theorem checked8 : validRows chunk8 = true := by decide +kernel
private theorem checked9 : validRows chunk9 = true := by decide +kernel
private theorem checked10 : validRows chunk10 = true := by decide +kernel

/-- All the checked rational premises of every listed compact cell. -/
theorem cell_valid {c : Cell} (hc : c ∈ cells) : c.Valid := by
  have hall : validRows cells = true := by
    simp only [cells, validRows_append, checked0, checked1, checked2, checked3, checked4,
      checked5, checked6, checked7, checked8, checked9, checked10, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp hall c hc)

/-- Each of the intended 88 indices occurs exactly once and the list is ordered. -/
theorem cell_indices : cells.map Cell.index = List.range 88 := by decide +kernel

/-- The intended strict global caps follow from the sharper rational maxima. -/
theorem budget_caps {c : Cell} (hc : c ∈ cells) :
    c.error44 < 3 / 1000 ∧ c.drift < 48 / 5 ∧ c.phase49 < 1 / 5 := by
  obtain ⟨_, _, _, he, hd, hp⟩ := (cell_valid hc).2.2
  exact ⟨lt_of_le_of_lt he (by decide +kernel), lt_of_le_of_lt hd (by decide +kernel),
    lt_of_le_of_lt hp (by decide +kernel)⟩

private theorem eighths_cover (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hupper : x ≤ ((n + 1 : ℕ) : ℝ) / 8) :
    ∃ i : ℕ, i < n + 1 ∧ (i : ℝ) / 8 ≤ x ∧ x ≤ ((i + 1 : ℕ) : ℝ) / 8 := by
  induction n with
  | zero =>
    exact ⟨0, Nat.zero_lt_succ 0, by simpa using hx, hupper⟩
  | succ n ih =>
    by_cases hmid : x ≤ ((n + 1 : ℕ) : ℝ) / 8
    · obtain ⟨i, hi, hlo, hhi⟩ := ih hmid
      exact ⟨i, Nat.lt_succ_of_lt hi, hlo, hhi⟩
    · exact ⟨n + 1, Nat.lt_succ_self _, le_of_lt (lt_of_not_ge hmid), hupper⟩

/-- The checked rational endpoints cover the entire closed real interval from 0 to 11. -/
theorem covers {x : ℝ} (hx : 0 ≤ x) (hupper : x ≤ 11) :
    ∃ c ∈ cells, c.Valid ∧ (c.a : ℝ) ≤ x ∧ x ≤ (c.b : ℝ) := by
  have bound : x ≤ ((87 + 1 : ℕ) : ℝ) / 8 := by norm_num; exact hupper
  obtain ⟨i, hi, hlo, hhi⟩ := eighths_cover 87 x hx bound
  have himem : i ∈ cells.map Cell.index := by
    rw [cell_indices]
    exact List.mem_range.mpr hi
  obtain ⟨c, hc, hindex⟩ := List.mem_map.mp himem
  have hv := cell_valid hc
  refine ⟨c, hc, hv, ?_, ?_⟩
  · rw [hv.1.2.1, hindex]
    simpa using hlo
  · rw [hv.1.2.2.1, hindex]
    simpa using hhi

end LongCycleFinite.K5CompactCert
