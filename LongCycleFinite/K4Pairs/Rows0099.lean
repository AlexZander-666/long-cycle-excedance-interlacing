import LongCycleFinite.K4Signed.Rows0099
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0095

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0096 : orderAtOK 96 cert0095 cert0096 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0096 : OriginalPair 96 :=
  original_of_certificates (by decide) row0095 row0096 order0096

theorem order0097 : orderAtOK 97 cert0096 cert0097 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0097 : OriginalPair 97 :=
  original_of_certificates (by decide) row0096 row0097 order0097

theorem order0098 : orderAtOK 98 cert0097 cert0098 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0098 : OriginalPair 98 :=
  original_of_certificates (by decide) row0097 row0098 order0098

theorem order0099 : orderAtOK 99 cert0098 cert0099 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0099 : OriginalPair 99 :=
  original_of_certificates (by decide) row0098 row0099 order0099

theorem range0096_0099 {n : ℕ} (lo : 96 ≤ n) (hi : n ≤ 99) : OriginalPair n := by
  interval_cases n
  · exact pair0096
  · exact pair0097
  · exact pair0098
  · exact pair0099

#print axioms range0096_0099

end LongCycleFinite.K4.Data
