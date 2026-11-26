import LongCycleFinite.K3SignedNatural.Rows0479
import LongCycleFinite.K3SignedNatural.Rows0475
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0476 :
    orderAtOK 476 cert0475 cert0476 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0476 : OriginalPair 476 :=
  original_of_certificates (by decide) row0475 row0476 order0476

theorem order0477 :
    orderAtOK 477 cert0476 cert0477 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0477 : OriginalPair 477 :=
  original_of_certificates (by decide) row0476 row0477 order0477

theorem order0478 :
    orderAtOK 478 cert0477 cert0478 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0478 : OriginalPair 478 :=
  original_of_certificates (by decide) row0477 row0478 order0478

theorem order0479 :
    orderAtOK 479 cert0478 cert0479 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0479 : OriginalPair 479 :=
  original_of_certificates (by decide) row0478 row0479 order0479

theorem range0476_0479 {n : ℕ} (lo : 476 ≤ n) (hi : n ≤ 479) : OriginalPair n := by
  interval_cases n
  · exact pair0476
  · exact pair0477
  · exact pair0478
  · exact pair0479

#print axioms range0476_0479

end LongCycleFinite.K3.DataExplicit
