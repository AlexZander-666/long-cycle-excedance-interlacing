import LongCycleBounds.FixedFourVerified
import LongCycleFinite.K4FiniteOriginal0511

/-! Consecutive interlacing at all nondegenerate sizes and minimum cycle length four. -/

namespace LongCycleBounds

open LongCycles LongCycleFinite Band

/-- For every upper index at least five, the original adjacent permutation rows
at cutoff four weakly interlace and have strictly interlacing negative quotient roots. -/
theorem fixed_four_all_sizes {n : ℕ} (hn : 5 ≤ n) :
    StrictNegativeInterlacing (generalCycleQuotient (n-1) 4) (generalCycleQuotient n 4) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) 4) (enumerator n 4) := by
  by_cases ht : 512 ≤ n
  · exact FixedFour.original ht
  · exact K4.finite_original_5_511 hn (by omega)

#print axioms fixed_four_all_sizes

end LongCycleBounds
