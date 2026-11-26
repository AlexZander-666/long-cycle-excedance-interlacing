import LongCycleFinite.K3Prefix127
import LongCycleFinite.K3DataExplicit.Rows0255

/-! The contiguous (k=3) range verified by direct endpoint checks. -/

namespace LongCycleFinite.K3

theorem finite_original_4_255 {n : ℕ} (lo : 4 ≤ n) (hi : n ≤ 255) : OriginalPair n := by
  by_cases h127 : n ≤ 127
  · exact finite_original_4_127 lo h127
  by_cases h135 : n ≤ 135
  · exact DataExplicit.range0128_0135 (by omega) h135
  by_cases h143 : n ≤ 143
  · exact DataExplicit.range0136_0143 (by omega) h143
  by_cases h151 : n ≤ 151
  · exact DataExplicit.range0144_0151 (by omega) h151
  by_cases h159 : n ≤ 159
  · exact DataExplicit.range0152_0159 (by omega) h159
  by_cases h167 : n ≤ 167
  · exact DataExplicit.range0160_0167 (by omega) h167
  by_cases h175 : n ≤ 175
  · exact DataExplicit.range0168_0175 (by omega) h175
  by_cases h183 : n ≤ 183
  · exact DataExplicit.range0176_0183 (by omega) h183
  by_cases h191 : n ≤ 191
  · exact DataExplicit.range0184_0191 (by omega) h191
  by_cases h199 : n ≤ 199
  · exact DataExplicit.range0192_0199 (by omega) h199
  by_cases h207 : n ≤ 207
  · exact DataExplicit.range0200_0207 (by omega) h207
  by_cases h215 : n ≤ 215
  · exact DataExplicit.range0208_0215 (by omega) h215
  by_cases h223 : n ≤ 223
  · exact DataExplicit.range0216_0223 (by omega) h223
  by_cases h231 : n ≤ 231
  · exact DataExplicit.range0224_0231 (by omega) h231
  by_cases h239 : n ≤ 239
  · exact DataExplicit.range0232_0239 (by omega) h239
  by_cases h247 : n ≤ 247
  · exact DataExplicit.range0240_0247 (by omega) h247
  exact DataExplicit.range0248_0255 (by omega) hi

#print axioms finite_original_4_255

end LongCycleFinite.K3
