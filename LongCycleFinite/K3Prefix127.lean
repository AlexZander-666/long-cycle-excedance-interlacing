import LongCycleFinite.K3DataExplicit.Rows0127

/-! The contiguous (k=3) range verified by recurrence checkpoints. -/

namespace LongCycleFinite.K3

theorem finite_original_4_127 {n : ℕ} (lo : 4 ≤ n) (hi : n ≤ 127) : OriginalPair n := by
  by_cases h11 : n ≤ 11
  · exact DataExplicit.range0004_0011 lo h11
  by_cases h27 : n ≤ 27
  · exact DataExplicit.range0012_0027 (by omega) h27
  by_cases h43 : n ≤ 43
  · exact DataExplicit.range0028_0043 (by omega) h43
  by_cases h59 : n ≤ 59
  · exact DataExplicit.range0044_0059 (by omega) h59
  by_cases h75 : n ≤ 75
  · exact DataExplicit.range0060_0075 (by omega) h75
  by_cases h91 : n ≤ 91
  · exact DataExplicit.range0076_0091 (by omega) h91
  by_cases h107 : n ≤ 107
  · exact DataExplicit.range0092_0107 (by omega) h107
  by_cases h123 : n ≤ 123
  · exact DataExplicit.range0108_0123 (by omega) h123
  exact DataExplicit.range0124_0127 (by omega) hi

#print axioms finite_original_4_127

end LongCycleFinite.K3
