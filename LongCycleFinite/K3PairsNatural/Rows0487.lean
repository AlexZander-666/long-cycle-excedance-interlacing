import LongCycleFinite.K3SignedNatural.Rows0487
import LongCycleFinite.K3SignedNatural.Rows0483
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0484 :
    orderAtOK 484 cert0483 cert0484 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0484 : OriginalPair 484 :=
  original_of_certificates (by decide) row0483 row0484 order0484

theorem order0485 :
    orderAtOK 485 cert0484 cert0485 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0485 : OriginalPair 485 :=
  original_of_certificates (by decide) row0484 row0485 order0485

theorem order0486 :
    orderAtOK 486 cert0485 cert0486 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0486 : OriginalPair 486 :=
  original_of_certificates (by decide) row0485 row0486 order0486

theorem order0487 :
    orderAtOK 487 cert0486 cert0487 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0487 : OriginalPair 487 :=
  original_of_certificates (by decide) row0486 row0487 order0487

theorem range0484_0487 {n : ℕ} (lo : 484 ≤ n) (hi : n ≤ 487) : OriginalPair n := by
  interval_cases n
  · exact pair0484
  · exact pair0485
  · exact pair0486
  · exact pair0487

#print axioms range0484_0487

end LongCycleFinite.K3.DataExplicit
