import LongCycleFinite.K4Signed.Rows0123
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0119

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0120 : orderAtOK 120 cert0119 cert0120 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0120 : OriginalPair 120 :=
  original_of_certificates (by decide) row0119 row0120 order0120

theorem order0121 : orderAtOK 121 cert0120 cert0121 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0121 : OriginalPair 121 :=
  original_of_certificates (by decide) row0120 row0121 order0121

theorem order0122 : orderAtOK 122 cert0121 cert0122 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0122 : OriginalPair 122 :=
  original_of_certificates (by decide) row0121 row0122 order0122

theorem order0123 : orderAtOK 123 cert0122 cert0123 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0123 : OriginalPair 123 :=
  original_of_certificates (by decide) row0122 row0123 order0123

theorem range0120_0123 {n : ℕ} (lo : 120 ≤ n) (hi : n ≤ 123) : OriginalPair n := by
  interval_cases n
  · exact pair0120
  · exact pair0121
  · exact pair0122
  · exact pair0123

#print axioms range0120_0123

end LongCycleFinite.K4.Data
