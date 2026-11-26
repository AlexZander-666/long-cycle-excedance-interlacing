import LongCycleFinite.K4Signed.Rows0103
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0099

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0100 : orderAtOK 100 cert0099 cert0100 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0100 : OriginalPair 100 :=
  original_of_certificates (by decide) row0099 row0100 order0100

theorem order0101 : orderAtOK 101 cert0100 cert0101 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0101 : OriginalPair 101 :=
  original_of_certificates (by decide) row0100 row0101 order0101

theorem order0102 : orderAtOK 102 cert0101 cert0102 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0102 : OriginalPair 102 :=
  original_of_certificates (by decide) row0101 row0102 order0102

theorem order0103 : orderAtOK 103 cert0102 cert0103 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0103 : OriginalPair 103 :=
  original_of_certificates (by decide) row0102 row0103 order0103

theorem range0100_0103 {n : ℕ} (lo : 100 ≤ n) (hi : n ≤ 103) : OriginalPair n := by
  interval_cases n
  · exact pair0100
  · exact pair0101
  · exact pair0102
  · exact pair0103

#print axioms range0100_0103

end LongCycleFinite.K4.Data
