import LongCycleFinite.K4Signed.Rows0115
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0111

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0112 : orderAtOK 112 cert0111 cert0112 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0112 : OriginalPair 112 :=
  original_of_certificates (by decide) row0111 row0112 order0112

theorem order0113 : orderAtOK 113 cert0112 cert0113 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0113 : OriginalPair 113 :=
  original_of_certificates (by decide) row0112 row0113 order0113

theorem order0114 : orderAtOK 114 cert0113 cert0114 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0114 : OriginalPair 114 :=
  original_of_certificates (by decide) row0113 row0114 order0114

theorem order0115 : orderAtOK 115 cert0114 cert0115 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0115 : OriginalPair 115 :=
  original_of_certificates (by decide) row0114 row0115 order0115

theorem range0112_0115 {n : ℕ} (lo : 112 ≤ n) (hi : n ≤ 115) : OriginalPair n := by
  interval_cases n
  · exact pair0112
  · exact pair0113
  · exact pair0114
  · exact pair0115

#print axioms range0112_0115

end LongCycleFinite.K4.Data
