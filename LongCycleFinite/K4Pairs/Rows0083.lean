import LongCycleFinite.K4Signed.Rows0083
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0079

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0080 : orderAtOK 80 cert0079 cert0080 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0080 : OriginalPair 80 :=
  original_of_certificates (by decide) row0079 row0080 order0080

theorem order0081 : orderAtOK 81 cert0080 cert0081 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0081 : OriginalPair 81 :=
  original_of_certificates (by decide) row0080 row0081 order0081

theorem order0082 : orderAtOK 82 cert0081 cert0082 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0082 : OriginalPair 82 :=
  original_of_certificates (by decide) row0081 row0082 order0082

theorem order0083 : orderAtOK 83 cert0082 cert0083 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0083 : OriginalPair 83 :=
  original_of_certificates (by decide) row0082 row0083 order0083

theorem range0080_0083 {n : ℕ} (lo : 80 ≤ n) (hi : n ≤ 83) : OriginalPair n := by
  interval_cases n
  · exact pair0080
  · exact pair0081
  · exact pair0082
  · exact pair0083

#print axioms range0080_0083

end LongCycleFinite.K4.Data
