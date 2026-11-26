import LongCycleFinite.K4Signed.Rows0047
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0043

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0044 : orderAtOK 44 cert0043 cert0044 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0044 : OriginalPair 44 :=
  original_of_certificates (by decide) row0043 row0044 order0044

theorem order0045 : orderAtOK 45 cert0044 cert0045 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0045 : OriginalPair 45 :=
  original_of_certificates (by decide) row0044 row0045 order0045

theorem order0046 : orderAtOK 46 cert0045 cert0046 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0046 : OriginalPair 46 :=
  original_of_certificates (by decide) row0045 row0046 order0046

theorem order0047 : orderAtOK 47 cert0046 cert0047 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0047 : OriginalPair 47 :=
  original_of_certificates (by decide) row0046 row0047 order0047

theorem range0044_0047 {n : ℕ} (lo : 44 ≤ n) (hi : n ≤ 47) : OriginalPair n := by
  interval_cases n
  · exact pair0044
  · exact pair0045
  · exact pair0046
  · exact pair0047

#print axioms range0044_0047

end LongCycleFinite.K4.Data
