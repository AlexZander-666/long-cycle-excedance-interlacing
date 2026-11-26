import LongCycleFinite.K4Signed.Rows0051
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0047

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0048 : orderAtOK 48 cert0047 cert0048 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0048 : OriginalPair 48 :=
  original_of_certificates (by decide) row0047 row0048 order0048

theorem order0049 : orderAtOK 49 cert0048 cert0049 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0049 : OriginalPair 49 :=
  original_of_certificates (by decide) row0048 row0049 order0049

theorem order0050 : orderAtOK 50 cert0049 cert0050 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0050 : OriginalPair 50 :=
  original_of_certificates (by decide) row0049 row0050 order0050

theorem order0051 : orderAtOK 51 cert0050 cert0051 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0051 : OriginalPair 51 :=
  original_of_certificates (by decide) row0050 row0051 order0051

theorem range0048_0051 {n : ℕ} (lo : 48 ≤ n) (hi : n ≤ 51) : OriginalPair n := by
  interval_cases n
  · exact pair0048
  · exact pair0049
  · exact pair0050
  · exact pair0051

#print axioms range0048_0051

end LongCycleFinite.K4.Data
