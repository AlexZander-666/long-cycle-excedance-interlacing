import LongCycleFinite.K4Signed.Rows0143
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0139

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0140 : orderAtOK 140 cert0139 cert0140 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0140 : OriginalPair 140 :=
  original_of_certificates (by decide) row0139 row0140 order0140

theorem order0141 : orderAtOK 141 cert0140 cert0141 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0141 : OriginalPair 141 :=
  original_of_certificates (by decide) row0140 row0141 order0141

theorem order0142 : orderAtOK 142 cert0141 cert0142 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0142 : OriginalPair 142 :=
  original_of_certificates (by decide) row0141 row0142 order0142

theorem order0143 : orderAtOK 143 cert0142 cert0143 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0143 : OriginalPair 143 :=
  original_of_certificates (by decide) row0142 row0143 order0143

theorem range0140_0143 {n : ℕ} (lo : 140 ≤ n) (hi : n ≤ 143) : OriginalPair n := by
  interval_cases n
  · exact pair0140
  · exact pair0141
  · exact pair0142
  · exact pair0143

#print axioms range0140_0143

end LongCycleFinite.K4.Data
