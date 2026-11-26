import LongCycleFinite.K4Signed.Rows0131
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0127

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0128 : orderAtOK 128 cert0127 cert0128 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0128 : OriginalPair 128 :=
  original_of_certificates (by decide) row0127 row0128 order0128

theorem order0129 : orderAtOK 129 cert0128 cert0129 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0129 : OriginalPair 129 :=
  original_of_certificates (by decide) row0128 row0129 order0129

theorem order0130 : orderAtOK 130 cert0129 cert0130 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0130 : OriginalPair 130 :=
  original_of_certificates (by decide) row0129 row0130 order0130

theorem order0131 : orderAtOK 131 cert0130 cert0131 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0131 : OriginalPair 131 :=
  original_of_certificates (by decide) row0130 row0131 order0131

theorem range0128_0131 {n : ℕ} (lo : 128 ≤ n) (hi : n ≤ 131) : OriginalPair n := by
  interval_cases n
  · exact pair0128
  · exact pair0129
  · exact pair0130
  · exact pair0131

#print axioms range0128_0131

end LongCycleFinite.K4.Data
