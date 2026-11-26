import LongCycleFinite.K4Signed.Rows0491
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0487

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0488 : orderAtOK 488 cert0487 cert0488 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0488 : OriginalPair 488 :=
  original_of_certificates (by decide) row0487 row0488 order0488

theorem order0489 : orderAtOK 489 cert0488 cert0489 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0489 : OriginalPair 489 :=
  original_of_certificates (by decide) row0488 row0489 order0489

theorem order0490 : orderAtOK 490 cert0489 cert0490 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0490 : OriginalPair 490 :=
  original_of_certificates (by decide) row0489 row0490 order0490

theorem order0491 : orderAtOK 491 cert0490 cert0491 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0491 : OriginalPair 491 :=
  original_of_certificates (by decide) row0490 row0491 order0491

theorem range0488_0491 {n : ℕ} (lo : 488 ≤ n) (hi : n ≤ 491) : OriginalPair n := by
  interval_cases n
  · exact pair0488
  · exact pair0489
  · exact pair0490
  · exact pair0491

#print axioms range0488_0491

end LongCycleFinite.K4.Data
