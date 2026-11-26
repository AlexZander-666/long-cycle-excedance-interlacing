import LongCycleFinite.K4Signed.Rows0483
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0479

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0480 : orderAtOK 480 cert0479 cert0480 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0480 : OriginalPair 480 :=
  original_of_certificates (by decide) row0479 row0480 order0480

theorem order0481 : orderAtOK 481 cert0480 cert0481 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0481 : OriginalPair 481 :=
  original_of_certificates (by decide) row0480 row0481 order0481

theorem order0482 : orderAtOK 482 cert0481 cert0482 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0482 : OriginalPair 482 :=
  original_of_certificates (by decide) row0481 row0482 order0482

theorem order0483 : orderAtOK 483 cert0482 cert0483 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0483 : OriginalPair 483 :=
  original_of_certificates (by decide) row0482 row0483 order0483

theorem range0480_0483 {n : ℕ} (lo : 480 ≤ n) (hi : n ≤ 483) : OriginalPair n := by
  interval_cases n
  · exact pair0480
  · exact pair0481
  · exact pair0482
  · exact pair0483

#print axioms range0480_0483

end LongCycleFinite.K4.Data
