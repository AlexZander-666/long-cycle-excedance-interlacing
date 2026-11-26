import LongCycleFinite.K4Signed.Rows0095
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0091

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0092 : orderAtOK 92 cert0091 cert0092 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0092 : OriginalPair 92 :=
  original_of_certificates (by decide) row0091 row0092 order0092

theorem order0093 : orderAtOK 93 cert0092 cert0093 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0093 : OriginalPair 93 :=
  original_of_certificates (by decide) row0092 row0093 order0093

theorem order0094 : orderAtOK 94 cert0093 cert0094 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0094 : OriginalPair 94 :=
  original_of_certificates (by decide) row0093 row0094 order0094

theorem order0095 : orderAtOK 95 cert0094 cert0095 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0095 : OriginalPair 95 :=
  original_of_certificates (by decide) row0094 row0095 order0095

theorem range0092_0095 {n : ℕ} (lo : 92 ≤ n) (hi : n ≤ 95) : OriginalPair n := by
  interval_cases n
  · exact pair0092
  · exact pair0093
  · exact pair0094
  · exact pair0095

#print axioms range0092_0095

end LongCycleFinite.K4.Data
