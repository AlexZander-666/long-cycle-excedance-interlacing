import LongCycleFinite.K4Signed.Rows0075
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0071

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0072 : orderAtOK 72 cert0071 cert0072 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0072 : OriginalPair 72 :=
  original_of_certificates (by decide) row0071 row0072 order0072

theorem order0073 : orderAtOK 73 cert0072 cert0073 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0073 : OriginalPair 73 :=
  original_of_certificates (by decide) row0072 row0073 order0073

theorem order0074 : orderAtOK 74 cert0073 cert0074 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0074 : OriginalPair 74 :=
  original_of_certificates (by decide) row0073 row0074 order0074

theorem order0075 : orderAtOK 75 cert0074 cert0075 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0075 : OriginalPair 75 :=
  original_of_certificates (by decide) row0074 row0075 order0075

theorem range0072_0075 {n : ℕ} (lo : 72 ≤ n) (hi : n ≤ 75) : OriginalPair n := by
  interval_cases n
  · exact pair0072
  · exact pair0073
  · exact pair0074
  · exact pair0075

#print axioms range0072_0075

end LongCycleFinite.K4.Data
