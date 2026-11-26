import LongCycleFinite.K4Signed.Rows0439
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0435

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0436 : orderAtOK 436 cert0435 cert0436 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0436 : OriginalPair 436 :=
  original_of_certificates (by decide) row0435 row0436 order0436

theorem order0437 : orderAtOK 437 cert0436 cert0437 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0437 : OriginalPair 437 :=
  original_of_certificates (by decide) row0436 row0437 order0437

theorem order0438 : orderAtOK 438 cert0437 cert0438 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0438 : OriginalPair 438 :=
  original_of_certificates (by decide) row0437 row0438 order0438

theorem order0439 : orderAtOK 439 cert0438 cert0439 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0439 : OriginalPair 439 :=
  original_of_certificates (by decide) row0438 row0439 order0439

theorem range0436_0439 {n : ℕ} (lo : 436 ≤ n) (hi : n ≤ 439) : OriginalPair n := by
  interval_cases n
  · exact pair0436
  · exact pair0437
  · exact pair0438
  · exact pair0439

#print axioms range0436_0439

end LongCycleFinite.K4.Data
