import LongCycleFinite.K4Signed.Rows0119
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0115

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0116 : orderAtOK 116 cert0115 cert0116 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0116 : OriginalPair 116 :=
  original_of_certificates (by decide) row0115 row0116 order0116

theorem order0117 : orderAtOK 117 cert0116 cert0117 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0117 : OriginalPair 117 :=
  original_of_certificates (by decide) row0116 row0117 order0117

theorem order0118 : orderAtOK 118 cert0117 cert0118 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0118 : OriginalPair 118 :=
  original_of_certificates (by decide) row0117 row0118 order0118

theorem order0119 : orderAtOK 119 cert0118 cert0119 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0119 : OriginalPair 119 :=
  original_of_certificates (by decide) row0118 row0119 order0119

theorem range0116_0119 {n : ℕ} (lo : 116 ≤ n) (hi : n ≤ 119) : OriginalPair n := by
  interval_cases n
  · exact pair0116
  · exact pair0117
  · exact pair0118
  · exact pair0119

#print axioms range0116_0119

end LongCycleFinite.K4.Data
