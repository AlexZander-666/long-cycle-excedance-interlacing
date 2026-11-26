import LongCycleFinite.K4Signed.Rows0159
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0155

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0156 : orderAtOK 156 cert0155 cert0156 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0156 : OriginalPair 156 :=
  original_of_certificates (by decide) row0155 row0156 order0156

theorem order0157 : orderAtOK 157 cert0156 cert0157 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0157 : OriginalPair 157 :=
  original_of_certificates (by decide) row0156 row0157 order0157

theorem order0158 : orderAtOK 158 cert0157 cert0158 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0158 : OriginalPair 158 :=
  original_of_certificates (by decide) row0157 row0158 order0158

theorem order0159 : orderAtOK 159 cert0158 cert0159 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0159 : OriginalPair 159 :=
  original_of_certificates (by decide) row0158 row0159 order0159

theorem range0156_0159 {n : ℕ} (lo : 156 ≤ n) (hi : n ≤ 159) : OriginalPair n := by
  interval_cases n
  · exact pair0156
  · exact pair0157
  · exact pair0158
  · exact pair0159

#print axioms range0156_0159

end LongCycleFinite.K4.Data
