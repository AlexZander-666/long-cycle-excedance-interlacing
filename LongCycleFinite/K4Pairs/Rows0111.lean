import LongCycleFinite.K4Signed.Rows0111
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0107

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0108 : orderAtOK 108 cert0107 cert0108 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0108 : OriginalPair 108 :=
  original_of_certificates (by decide) row0107 row0108 order0108

theorem order0109 : orderAtOK 109 cert0108 cert0109 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0109 : OriginalPair 109 :=
  original_of_certificates (by decide) row0108 row0109 order0109

theorem order0110 : orderAtOK 110 cert0109 cert0110 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0110 : OriginalPair 110 :=
  original_of_certificates (by decide) row0109 row0110 order0110

theorem order0111 : orderAtOK 111 cert0110 cert0111 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0111 : OriginalPair 111 :=
  original_of_certificates (by decide) row0110 row0111 order0111

theorem range0108_0111 {n : ℕ} (lo : 108 ≤ n) (hi : n ≤ 111) : OriginalPair n := by
  interval_cases n
  · exact pair0108
  · exact pair0109
  · exact pair0110
  · exact pair0111

#print axioms range0108_0111

end LongCycleFinite.K4.Data
