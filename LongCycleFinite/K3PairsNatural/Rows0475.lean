import LongCycleFinite.K3SignedNatural.Rows0475
import LongCycleFinite.K3SignedNatural.Rows0471
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0472 :
    orderAtOK 472 cert0471 cert0472 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0472 : OriginalPair 472 :=
  original_of_certificates (by decide) row0471 row0472 order0472

theorem order0473 :
    orderAtOK 473 cert0472 cert0473 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0473 : OriginalPair 473 :=
  original_of_certificates (by decide) row0472 row0473 order0473

theorem order0474 :
    orderAtOK 474 cert0473 cert0474 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0474 : OriginalPair 474 :=
  original_of_certificates (by decide) row0473 row0474 order0474

theorem order0475 :
    orderAtOK 475 cert0474 cert0475 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0475 : OriginalPair 475 :=
  original_of_certificates (by decide) row0474 row0475 order0475

theorem range0472_0475 {n : ℕ} (lo : 472 ≤ n) (hi : n ≤ 475) : OriginalPair n := by
  interval_cases n
  · exact pair0472
  · exact pair0473
  · exact pair0474
  · exact pair0475

#print axioms range0472_0475

end LongCycleFinite.K3.DataExplicit
