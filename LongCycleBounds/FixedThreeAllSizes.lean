import LongCycleBounds.MarkedHalfVerified
import LongCycleFinite.K3FiniteOriginal0511

/-! Consecutive interlacing in every nondegenerate size at minimum cycle length three. -/

namespace LongCycleBounds
open LongCycles LongCycleFinite Band

/-- For every size n ≥ 4 the genuine minimum-cycle-three permutation enumerators
weakly interlace. Their quotients by the common zero strictly interlace at simple negative roots. -/
theorem fixed_three_all_sizes {n : ℕ} (hn : 4 ≤ n) :
    StrictNegativeInterlacing (generalCycleQuotient (n-1) 3) (generalCycleQuotient n 3) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) 3) (enumerator n 3) := by
  by_cases ht : 512 ≤ n
  · exact MarkedTwo.Half.original_interlacing ht
  · exact K3.finite_original_4_511 hn (by omega)

#print axioms fixed_three_all_sizes
end LongCycleBounds
