import LongCycleFinite.K5Prefix.Rows48

namespace LongCycleFinite.K5Prefix
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem finite_original {n : ℕ} (lo : 6 ≤ n) (hi : n ≤ 48) : OriginalPair n := by
  interval_cases n
  · exact pair6
  · exact pair7
  · exact pair8
  · exact pair9
  · exact pair10
  · exact pair11
  · exact pair12
  · exact pair13
  · exact pair14
  · exact pair15
  · exact pair16
  · exact pair17
  · exact pair18
  · exact pair19
  · exact pair20
  · exact pair21
  · exact pair22
  · exact pair23
  · exact pair24
  · exact pair25
  · exact pair26
  · exact pair27
  · exact pair28
  · exact pair29
  · exact pair30
  · exact pair31
  · exact pair32
  · exact pair33
  · exact pair34
  · exact pair35
  · exact pair36
  · exact pair37
  · exact pair38
  · exact pair39
  · exact pair40
  · exact pair41
  · exact pair42
  · exact pair43
  · exact pair44
  · exact pair45
  · exact pair46
  · exact pair47
  · exact pair48
#print axioms finite_original
end LongCycleFinite.K5Prefix
