import LongCycleFinite.K4Signed.Rows0435
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0431

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0432 : orderAtOK 432 cert0431 cert0432 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0432 : OriginalPair 432 :=
  original_of_certificates (by decide) row0431 row0432 order0432

theorem order0433 : orderAtOK 433 cert0432 cert0433 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0433 : OriginalPair 433 :=
  original_of_certificates (by decide) row0432 row0433 order0433

theorem order0434 : orderAtOK 434 cert0433 cert0434 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0434 : OriginalPair 434 :=
  original_of_certificates (by decide) row0433 row0434 order0434

theorem order0435 : orderAtOK 435 cert0434 cert0435 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0435 : OriginalPair 435 :=
  original_of_certificates (by decide) row0434 row0435 order0435

theorem range0432_0435 {n : ℕ} (lo : 432 ≤ n) (hi : n ≤ 435) : OriginalPair n := by
  interval_cases n
  · exact pair0432
  · exact pair0433
  · exact pair0434
  · exact pair0435

#print axioms range0432_0435

end LongCycleFinite.K4.Data
