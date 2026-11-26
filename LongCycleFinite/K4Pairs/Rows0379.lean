import LongCycleFinite.K4Signed.Rows0379
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0375

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0376 : orderAtOK 376 cert0375 cert0376 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0376 : OriginalPair 376 :=
  original_of_certificates (by decide) row0375 row0376 order0376

theorem order0377 : orderAtOK 377 cert0376 cert0377 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0377 : OriginalPair 377 :=
  original_of_certificates (by decide) row0376 row0377 order0377

theorem order0378 : orderAtOK 378 cert0377 cert0378 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0378 : OriginalPair 378 :=
  original_of_certificates (by decide) row0377 row0378 order0378

theorem order0379 : orderAtOK 379 cert0378 cert0379 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0379 : OriginalPair 379 :=
  original_of_certificates (by decide) row0378 row0379 order0379

theorem range0376_0379 {n : ℕ} (lo : 376 ≤ n) (hi : n ≤ 379) : OriginalPair n := by
  interval_cases n
  · exact pair0376
  · exact pair0377
  · exact pair0378
  · exact pair0379

#print axioms range0376_0379

end LongCycleFinite.K4.Data
