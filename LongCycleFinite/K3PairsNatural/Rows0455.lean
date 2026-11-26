import LongCycleFinite.K3SignedNatural.Rows0455
import LongCycleFinite.K3SignedNatural.Rows0451
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0452 :
    orderAtOK 452 cert0451 cert0452 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0452 : OriginalPair 452 :=
  original_of_certificates (by decide) row0451 row0452 order0452

theorem order0453 :
    orderAtOK 453 cert0452 cert0453 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0453 : OriginalPair 453 :=
  original_of_certificates (by decide) row0452 row0453 order0453

theorem order0454 :
    orderAtOK 454 cert0453 cert0454 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0454 : OriginalPair 454 :=
  original_of_certificates (by decide) row0453 row0454 order0454

theorem order0455 :
    orderAtOK 455 cert0454 cert0455 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0455 : OriginalPair 455 :=
  original_of_certificates (by decide) row0454 row0455 order0455

theorem range0452_0455 {n : ℕ} (lo : 452 ≤ n) (hi : n ≤ 455) : OriginalPair n := by
  interval_cases n
  · exact pair0452
  · exact pair0453
  · exact pair0454
  · exact pair0455

#print axioms range0452_0455

end LongCycleFinite.K3.DataExplicit
