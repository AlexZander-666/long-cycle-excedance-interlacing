import LongCycleFinite.K4Signed.Rows0059
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0055

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0056 : orderAtOK 56 cert0055 cert0056 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0056 : OriginalPair 56 :=
  original_of_certificates (by decide) row0055 row0056 order0056

theorem order0057 : orderAtOK 57 cert0056 cert0057 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0057 : OriginalPair 57 :=
  original_of_certificates (by decide) row0056 row0057 order0057

theorem order0058 : orderAtOK 58 cert0057 cert0058 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0058 : OriginalPair 58 :=
  original_of_certificates (by decide) row0057 row0058 order0058

theorem order0059 : orderAtOK 59 cert0058 cert0059 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0059 : OriginalPair 59 :=
  original_of_certificates (by decide) row0058 row0059 order0059

theorem range0056_0059 {n : ℕ} (lo : 56 ≤ n) (hi : n ≤ 59) : OriginalPair n := by
  interval_cases n
  · exact pair0056
  · exact pair0057
  · exact pair0058
  · exact pair0059

#print axioms range0056_0059

end LongCycleFinite.K4.Data
