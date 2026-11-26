import LongCycleFinite.K4Signed.Rows0499
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0495

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0496 : orderAtOK 496 cert0495 cert0496 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0496 : OriginalPair 496 :=
  original_of_certificates (by decide) row0495 row0496 order0496

theorem order0497 : orderAtOK 497 cert0496 cert0497 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0497 : OriginalPair 497 :=
  original_of_certificates (by decide) row0496 row0497 order0497

theorem order0498 : orderAtOK 498 cert0497 cert0498 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0498 : OriginalPair 498 :=
  original_of_certificates (by decide) row0497 row0498 order0498

theorem order0499 : orderAtOK 499 cert0498 cert0499 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0499 : OriginalPair 499 :=
  original_of_certificates (by decide) row0498 row0499 order0499

theorem range0496_0499 {n : ℕ} (lo : 496 ≤ n) (hi : n ≤ 499) : OriginalPair n := by
  interval_cases n
  · exact pair0496
  · exact pair0497
  · exact pair0498
  · exact pair0499

#print axioms range0496_0499

end LongCycleFinite.K4.Data
