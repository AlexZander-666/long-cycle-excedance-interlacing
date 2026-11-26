import LongCycleFinite.K4Signed.Rows0079
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0075

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0076 : orderAtOK 76 cert0075 cert0076 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0076 : OriginalPair 76 :=
  original_of_certificates (by decide) row0075 row0076 order0076

theorem order0077 : orderAtOK 77 cert0076 cert0077 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0077 : OriginalPair 77 :=
  original_of_certificates (by decide) row0076 row0077 order0077

theorem order0078 : orderAtOK 78 cert0077 cert0078 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0078 : OriginalPair 78 :=
  original_of_certificates (by decide) row0077 row0078 order0078

theorem order0079 : orderAtOK 79 cert0078 cert0079 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0079 : OriginalPair 79 :=
  original_of_certificates (by decide) row0078 row0079 order0079

theorem range0076_0079 {n : ℕ} (lo : 76 ≤ n) (hi : n ≤ 79) : OriginalPair n := by
  interval_cases n
  · exact pair0076
  · exact pair0077
  · exact pair0078
  · exact pair0079

#print axioms range0076_0079

end LongCycleFinite.K4.Data
