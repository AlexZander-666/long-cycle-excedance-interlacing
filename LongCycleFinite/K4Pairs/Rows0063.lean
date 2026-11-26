import LongCycleFinite.K4Signed.Rows0063
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0059

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0060 : orderAtOK 60 cert0059 cert0060 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0060 : OriginalPair 60 :=
  original_of_certificates (by decide) row0059 row0060 order0060

theorem order0061 : orderAtOK 61 cert0060 cert0061 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0061 : OriginalPair 61 :=
  original_of_certificates (by decide) row0060 row0061 order0061

theorem order0062 : orderAtOK 62 cert0061 cert0062 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0062 : OriginalPair 62 :=
  original_of_certificates (by decide) row0061 row0062 order0062

theorem order0063 : orderAtOK 63 cert0062 cert0063 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0063 : OriginalPair 63 :=
  original_of_certificates (by decide) row0062 row0063 order0063

theorem range0060_0063 {n : ℕ} (lo : 60 ≤ n) (hi : n ≤ 63) : OriginalPair n := by
  interval_cases n
  · exact pair0060
  · exact pair0061
  · exact pair0062
  · exact pair0063

#print axioms range0060_0063

end LongCycleFinite.K4.Data
