import LongCycleFinite.K4Signed.Rows0415
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0411

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0412 : orderAtOK 412 cert0411 cert0412 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0412 : OriginalPair 412 :=
  original_of_certificates (by decide) row0411 row0412 order0412

theorem order0413 : orderAtOK 413 cert0412 cert0413 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0413 : OriginalPair 413 :=
  original_of_certificates (by decide) row0412 row0413 order0413

theorem order0414 : orderAtOK 414 cert0413 cert0414 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0414 : OriginalPair 414 :=
  original_of_certificates (by decide) row0413 row0414 order0414

theorem order0415 : orderAtOK 415 cert0414 cert0415 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0415 : OriginalPair 415 :=
  original_of_certificates (by decide) row0414 row0415 order0415

theorem range0412_0415 {n : ℕ} (lo : 412 ≤ n) (hi : n ≤ 415) : OriginalPair n := by
  interval_cases n
  · exact pair0412
  · exact pair0413
  · exact pair0414
  · exact pair0415

#print axioms range0412_0415

end LongCycleFinite.K4.Data
