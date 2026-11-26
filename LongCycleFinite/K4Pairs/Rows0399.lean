import LongCycleFinite.K4Signed.Rows0399
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0395

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0396 : orderAtOK 396 cert0395 cert0396 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0396 : OriginalPair 396 :=
  original_of_certificates (by decide) row0395 row0396 order0396

theorem order0397 : orderAtOK 397 cert0396 cert0397 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0397 : OriginalPair 397 :=
  original_of_certificates (by decide) row0396 row0397 order0397

theorem order0398 : orderAtOK 398 cert0397 cert0398 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0398 : OriginalPair 398 :=
  original_of_certificates (by decide) row0397 row0398 order0398

theorem order0399 : orderAtOK 399 cert0398 cert0399 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0399 : OriginalPair 399 :=
  original_of_certificates (by decide) row0398 row0399 order0399

theorem range0396_0399 {n : ℕ} (lo : 396 ≤ n) (hi : n ≤ 399) : OriginalPair n := by
  interval_cases n
  · exact pair0396
  · exact pair0397
  · exact pair0398
  · exact pair0399

#print axioms range0396_0399

end LongCycleFinite.K4.Data
