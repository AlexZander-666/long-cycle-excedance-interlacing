import LongCycleFinite.K4Signed.Rows0387
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0383

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0384 : orderAtOK 384 cert0383 cert0384 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0384 : OriginalPair 384 :=
  original_of_certificates (by decide) row0383 row0384 order0384

theorem order0385 : orderAtOK 385 cert0384 cert0385 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0385 : OriginalPair 385 :=
  original_of_certificates (by decide) row0384 row0385 order0385

theorem order0386 : orderAtOK 386 cert0385 cert0386 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0386 : OriginalPair 386 :=
  original_of_certificates (by decide) row0385 row0386 order0386

theorem order0387 : orderAtOK 387 cert0386 cert0387 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0387 : OriginalPair 387 :=
  original_of_certificates (by decide) row0386 row0387 order0387

theorem range0384_0387 {n : ℕ} (lo : 384 ≤ n) (hi : n ≤ 387) : OriginalPair n := by
  interval_cases n
  · exact pair0384
  · exact pair0385
  · exact pair0386
  · exact pair0387

#print axioms range0384_0387

end LongCycleFinite.K4.Data
