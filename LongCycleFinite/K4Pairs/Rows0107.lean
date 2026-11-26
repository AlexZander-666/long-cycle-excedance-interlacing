import LongCycleFinite.K4Signed.Rows0107
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0103

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0104 : orderAtOK 104 cert0103 cert0104 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0104 : OriginalPair 104 :=
  original_of_certificates (by decide) row0103 row0104 order0104

theorem order0105 : orderAtOK 105 cert0104 cert0105 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0105 : OriginalPair 105 :=
  original_of_certificates (by decide) row0104 row0105 order0105

theorem order0106 : orderAtOK 106 cert0105 cert0106 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0106 : OriginalPair 106 :=
  original_of_certificates (by decide) row0105 row0106 order0106

theorem order0107 : orderAtOK 107 cert0106 cert0107 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0107 : OriginalPair 107 :=
  original_of_certificates (by decide) row0106 row0107 order0107

theorem range0104_0107 {n : ℕ} (lo : 104 ≤ n) (hi : n ≤ 107) : OriginalPair n := by
  interval_cases n
  · exact pair0104
  · exact pair0105
  · exact pair0106
  · exact pair0107

#print axioms range0104_0107

end LongCycleFinite.K4.Data
