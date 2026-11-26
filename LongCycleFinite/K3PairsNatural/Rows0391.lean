import LongCycleFinite.K3SignedNatural.Rows0391
import LongCycleFinite.K3SignedNatural.Rows0387
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0388 :
    orderAtOK 388 cert0387 cert0388 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0388 : OriginalPair 388 :=
  original_of_certificates (by decide) row0387 row0388 order0388

theorem order0389 :
    orderAtOK 389 cert0388 cert0389 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0389 : OriginalPair 389 :=
  original_of_certificates (by decide) row0388 row0389 order0389

theorem order0390 :
    orderAtOK 390 cert0389 cert0390 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0390 : OriginalPair 390 :=
  original_of_certificates (by decide) row0389 row0390 order0390

theorem order0391 :
    orderAtOK 391 cert0390 cert0391 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0391 : OriginalPair 391 :=
  original_of_certificates (by decide) row0390 row0391 order0391

theorem range0388_0391 {n : ℕ} (lo : 388 ≤ n) (hi : n ≤ 391) : OriginalPair n := by
  interval_cases n
  · exact pair0388
  · exact pair0389
  · exact pair0390
  · exact pair0391

#print axioms range0388_0391

end LongCycleFinite.K3.DataExplicit
