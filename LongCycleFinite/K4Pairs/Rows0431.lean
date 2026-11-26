import LongCycleFinite.K4Signed.Rows0431
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0427

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0428 : orderAtOK 428 cert0427 cert0428 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0428 : OriginalPair 428 :=
  original_of_certificates (by decide) row0427 row0428 order0428

theorem order0429 : orderAtOK 429 cert0428 cert0429 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0429 : OriginalPair 429 :=
  original_of_certificates (by decide) row0428 row0429 order0429

theorem order0430 : orderAtOK 430 cert0429 cert0430 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0430 : OriginalPair 430 :=
  original_of_certificates (by decide) row0429 row0430 order0430

theorem order0431 : orderAtOK 431 cert0430 cert0431 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0431 : OriginalPair 431 :=
  original_of_certificates (by decide) row0430 row0431 order0431

theorem range0428_0431 {n : ℕ} (lo : 428 ≤ n) (hi : n ≤ 431) : OriginalPair n := by
  interval_cases n
  · exact pair0428
  · exact pair0429
  · exact pair0430
  · exact pair0431

#print axioms range0428_0431

end LongCycleFinite.K4.Data
