import LongCycleFinite.K4Signed.Rows0091
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0087

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0088 : orderAtOK 88 cert0087 cert0088 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0088 : OriginalPair 88 :=
  original_of_certificates (by decide) row0087 row0088 order0088

theorem order0089 : orderAtOK 89 cert0088 cert0089 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0089 : OriginalPair 89 :=
  original_of_certificates (by decide) row0088 row0089 order0089

theorem order0090 : orderAtOK 90 cert0089 cert0090 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0090 : OriginalPair 90 :=
  original_of_certificates (by decide) row0089 row0090 order0090

theorem order0091 : orderAtOK 91 cert0090 cert0091 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0091 : OriginalPair 91 :=
  original_of_certificates (by decide) row0090 row0091 order0091

theorem range0088_0091 {n : ℕ} (lo : 88 ≤ n) (hi : n ≤ 91) : OriginalPair n := by
  interval_cases n
  · exact pair0088
  · exact pair0089
  · exact pair0090
  · exact pair0091

#print axioms range0088_0091

end LongCycleFinite.K4.Data
