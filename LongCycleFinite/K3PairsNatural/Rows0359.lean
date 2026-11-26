import LongCycleFinite.K3SignedNatural.Rows0359
import LongCycleFinite.K3SignedNatural.Rows0355
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0356 :
    orderAtOK 356 cert0355 cert0356 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0356 : OriginalPair 356 :=
  original_of_certificates (by decide) row0355 row0356 order0356

theorem order0357 :
    orderAtOK 357 cert0356 cert0357 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0357 : OriginalPair 357 :=
  original_of_certificates (by decide) row0356 row0357 order0357

theorem order0358 :
    orderAtOK 358 cert0357 cert0358 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0358 : OriginalPair 358 :=
  original_of_certificates (by decide) row0357 row0358 order0358

theorem order0359 :
    orderAtOK 359 cert0358 cert0359 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0359 : OriginalPair 359 :=
  original_of_certificates (by decide) row0358 row0359 order0359

theorem range0356_0359 {n : ℕ} (lo : 356 ≤ n) (hi : n ≤ 359) : OriginalPair n := by
  interval_cases n
  · exact pair0356
  · exact pair0357
  · exact pair0358
  · exact pair0359

#print axioms range0356_0359

end LongCycleFinite.K3.DataExplicit
