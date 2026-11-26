import LongCycleFinite.K4Signed.Rows0087
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0083

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0084 : orderAtOK 84 cert0083 cert0084 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0084 : OriginalPair 84 :=
  original_of_certificates (by decide) row0083 row0084 order0084

theorem order0085 : orderAtOK 85 cert0084 cert0085 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0085 : OriginalPair 85 :=
  original_of_certificates (by decide) row0084 row0085 order0085

theorem order0086 : orderAtOK 86 cert0085 cert0086 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0086 : OriginalPair 86 :=
  original_of_certificates (by decide) row0085 row0086 order0086

theorem order0087 : orderAtOK 87 cert0086 cert0087 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0087 : OriginalPair 87 :=
  original_of_certificates (by decide) row0086 row0087 order0087

theorem range0084_0087 {n : ℕ} (lo : 84 ≤ n) (hi : n ≤ 87) : OriginalPair n := by
  interval_cases n
  · exact pair0084
  · exact pair0085
  · exact pair0086
  · exact pair0087

#print axioms range0084_0087

end LongCycleFinite.K4.Data
