import LongCycleFinite.K3SignedNatural.Rows0451
import LongCycleFinite.K3SignedNatural.Rows0447
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0448 :
    orderAtOK 448 cert0447 cert0448 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0448 : OriginalPair 448 :=
  original_of_certificates (by decide) row0447 row0448 order0448

theorem order0449 :
    orderAtOK 449 cert0448 cert0449 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0449 : OriginalPair 449 :=
  original_of_certificates (by decide) row0448 row0449 order0449

theorem order0450 :
    orderAtOK 450 cert0449 cert0450 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0450 : OriginalPair 450 :=
  original_of_certificates (by decide) row0449 row0450 order0450

theorem order0451 :
    orderAtOK 451 cert0450 cert0451 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0451 : OriginalPair 451 :=
  original_of_certificates (by decide) row0450 row0451 order0451

theorem range0448_0451 {n : ℕ} (lo : 448 ≤ n) (hi : n ≤ 451) : OriginalPair n := by
  interval_cases n
  · exact pair0448
  · exact pair0449
  · exact pair0450
  · exact pair0451

#print axioms range0448_0451

end LongCycleFinite.K3.DataExplicit
