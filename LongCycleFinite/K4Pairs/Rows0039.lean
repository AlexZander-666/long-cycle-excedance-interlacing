import LongCycleFinite.K4Signed.Rows0039
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0035

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0036 : orderAtOK 36 cert0035 cert0036 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0036 : OriginalPair 36 :=
  original_of_certificates (by decide) row0035 row0036 order0036

theorem order0037 : orderAtOK 37 cert0036 cert0037 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0037 : OriginalPair 37 :=
  original_of_certificates (by decide) row0036 row0037 order0037

theorem order0038 : orderAtOK 38 cert0037 cert0038 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0038 : OriginalPair 38 :=
  original_of_certificates (by decide) row0037 row0038 order0038

theorem order0039 : orderAtOK 39 cert0038 cert0039 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0039 : OriginalPair 39 :=
  original_of_certificates (by decide) row0038 row0039 order0039

theorem range0036_0039 {n : ℕ} (lo : 36 ≤ n) (hi : n ≤ 39) : OriginalPair n := by
  interval_cases n
  · exact pair0036
  · exact pair0037
  · exact pair0038
  · exact pair0039

#print axioms range0036_0039

end LongCycleFinite.K4.Data
