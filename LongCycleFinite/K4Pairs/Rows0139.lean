import LongCycleFinite.K4Signed.Rows0139
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0135

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0136 : orderAtOK 136 cert0135 cert0136 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0136 : OriginalPair 136 :=
  original_of_certificates (by decide) row0135 row0136 order0136

theorem order0137 : orderAtOK 137 cert0136 cert0137 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0137 : OriginalPair 137 :=
  original_of_certificates (by decide) row0136 row0137 order0137

theorem order0138 : orderAtOK 138 cert0137 cert0138 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0138 : OriginalPair 138 :=
  original_of_certificates (by decide) row0137 row0138 order0138

theorem order0139 : orderAtOK 139 cert0138 cert0139 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0139 : OriginalPair 139 :=
  original_of_certificates (by decide) row0138 row0139 order0139

theorem range0136_0139 {n : ℕ} (lo : 136 ≤ n) (hi : n ≤ 139) : OriginalPair n := by
  interval_cases n
  · exact pair0136
  · exact pair0137
  · exact pair0138
  · exact pair0139

#print axioms range0136_0139

end LongCycleFinite.K4.Data
