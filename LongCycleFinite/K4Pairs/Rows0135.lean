import LongCycleFinite.K4Signed.Rows0135
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0131

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0132 : orderAtOK 132 cert0131 cert0132 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0132 : OriginalPair 132 :=
  original_of_certificates (by decide) row0131 row0132 order0132

theorem order0133 : orderAtOK 133 cert0132 cert0133 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0133 : OriginalPair 133 :=
  original_of_certificates (by decide) row0132 row0133 order0133

theorem order0134 : orderAtOK 134 cert0133 cert0134 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0134 : OriginalPair 134 :=
  original_of_certificates (by decide) row0133 row0134 order0134

theorem order0135 : orderAtOK 135 cert0134 cert0135 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0135 : OriginalPair 135 :=
  original_of_certificates (by decide) row0134 row0135 order0135

theorem range0132_0135 {n : ℕ} (lo : 132 ≤ n) (hi : n ≤ 135) : OriginalPair n := by
  interval_cases n
  · exact pair0132
  · exact pair0133
  · exact pair0134
  · exact pair0135

#print axioms range0132_0135

end LongCycleFinite.K4.Data
