import LongCycleFinite.K4Signed.Rows0127
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0123

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0124 : orderAtOK 124 cert0123 cert0124 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0124 : OriginalPair 124 :=
  original_of_certificates (by decide) row0123 row0124 order0124

theorem order0125 : orderAtOK 125 cert0124 cert0125 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0125 : OriginalPair 125 :=
  original_of_certificates (by decide) row0124 row0125 order0125

theorem order0126 : orderAtOK 126 cert0125 cert0126 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0126 : OriginalPair 126 :=
  original_of_certificates (by decide) row0125 row0126 order0126

theorem order0127 : orderAtOK 127 cert0126 cert0127 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0127 : OriginalPair 127 :=
  original_of_certificates (by decide) row0126 row0127 order0127

theorem range0124_0127 {n : ℕ} (lo : 124 ≤ n) (hi : n ≤ 127) : OriginalPair n := by
  interval_cases n
  · exact pair0124
  · exact pair0125
  · exact pair0126
  · exact pair0127

#print axioms range0124_0127

end LongCycleFinite.K4.Data
