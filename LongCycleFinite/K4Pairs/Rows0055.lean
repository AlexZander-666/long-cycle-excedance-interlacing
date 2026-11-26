import LongCycleFinite.K4Signed.Rows0055
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0051

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0052 : orderAtOK 52 cert0051 cert0052 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0052 : OriginalPair 52 :=
  original_of_certificates (by decide) row0051 row0052 order0052

theorem order0053 : orderAtOK 53 cert0052 cert0053 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0053 : OriginalPair 53 :=
  original_of_certificates (by decide) row0052 row0053 order0053

theorem order0054 : orderAtOK 54 cert0053 cert0054 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0054 : OriginalPair 54 :=
  original_of_certificates (by decide) row0053 row0054 order0054

theorem order0055 : orderAtOK 55 cert0054 cert0055 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0055 : OriginalPair 55 :=
  original_of_certificates (by decide) row0054 row0055 order0055

theorem range0052_0055 {n : ℕ} (lo : 52 ≤ n) (hi : n ≤ 55) : OriginalPair n := by
  interval_cases n
  · exact pair0052
  · exact pair0053
  · exact pair0054
  · exact pair0055

#print axioms range0052_0055

end LongCycleFinite.K4.Data
