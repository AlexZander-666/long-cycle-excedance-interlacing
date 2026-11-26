import LongCycleBounds.MarkedHalfCompact
import LongCycleBounds.MarkedHalfOuter
import LongCycleBounds.MarkedHalfMiddle
import LongCycleBounds.MarkedAnalyticReadout

/-! The full transposition-marked tail at upper size 512. -/
namespace LongCycleBounds.MarkedTwo.Half
open LongCycles LongCycleFinite Real Band

/-- A common real transposition weight is allowed throughout the analytic tail. -/
theorem marked_interlacing {n : ℕ} (hn : 512 ≤ n) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      StrictNegativeInterlacing (markedQuotient (n-1) u) (markedQuotient n u) (n-3) ∧
        WeakRealInterlacing (row (n-1) u) (row n u) := by
  apply marked_original_of_normalized_sign (by omega)
  intro u hu x hx hz
  by_cases small : x≤16
  · exact marked_compact_sign hu.1 hu.2 hx small hn hz
  by_cases large : 3*sqrt ((n-1:ℕ):ℝ)≤x
  · have r : n-3+2=n-1 := by omega
    have s : n-3+3=n := by omega
    simpa only [r,s] using marked_outer_sign u x (n-3) (by omega)
      hu.1 hu.2 (by simpa only [r] using large) (by simpa only [r] using hz)
  exact marked_middle_sign hu.1 hu.2 (le_of_not_ge small) hn (le_of_not_ge large) hz

/-- Setting the mark equal to zero excludes every transposition. -/
theorem original_interlacing {n : ℕ} (hn : 512 ≤ n) :
    StrictNegativeInterlacing (generalCycleQuotient (n-1) 3) (generalCycleQuotient n 3) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) 3) (enumerator n 3) := by
  have h := marked_interlacing hn 0 (by constructor <;> norm_num)
  rwa [(markedQuotient_endpoints (n:=n-1) (by omega)).1,
    (markedQuotient_endpoints (n:=n) (by omega)).1, row_zero, row_zero] at h

#print axioms marked_interlacing
#print axioms original_interlacing
end LongCycleBounds.MarkedTwo.Half
