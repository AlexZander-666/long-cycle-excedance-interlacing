import LongCycleFinite.K4Signed.Rows0371
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0367

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0368 : orderAtOK 368 cert0367 cert0368 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0368 : OriginalPair 368 :=
  original_of_certificates (by decide) row0367 row0368 order0368

theorem order0369 : orderAtOK 369 cert0368 cert0369 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0369 : OriginalPair 369 :=
  original_of_certificates (by decide) row0368 row0369 order0369

theorem order0370 : orderAtOK 370 cert0369 cert0370 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0370 : OriginalPair 370 :=
  original_of_certificates (by decide) row0369 row0370 order0370

theorem order0371 : orderAtOK 371 cert0370 cert0371 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0371 : OriginalPair 371 :=
  original_of_certificates (by decide) row0370 row0371 order0371

theorem range0368_0371 {n : ℕ} (lo : 368 ≤ n) (hi : n ≤ 371) : OriginalPair n := by
  interval_cases n
  · exact pair0368
  · exact pair0369
  · exact pair0370
  · exact pair0371

#print axioms range0368_0371

end LongCycleFinite.K4.Data
