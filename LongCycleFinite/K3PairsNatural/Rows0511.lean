import LongCycleFinite.K3SignedNatural.Rows0511
import LongCycleFinite.K3SignedNatural.Rows0507
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0508 :
    orderAtOK 508 cert0507 cert0508 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0508 : OriginalPair 508 :=
  original_of_certificates (by decide) row0507 row0508 order0508

theorem order0509 :
    orderAtOK 509 cert0508 cert0509 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0509 : OriginalPair 509 :=
  original_of_certificates (by decide) row0508 row0509 order0509

theorem order0510 :
    orderAtOK 510 cert0509 cert0510 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0510 : OriginalPair 510 :=
  original_of_certificates (by decide) row0509 row0510 order0510

theorem order0511 :
    orderAtOK 511 cert0510 cert0511 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0511 : OriginalPair 511 :=
  original_of_certificates (by decide) row0510 row0511 order0511

theorem range0508_0511 {n : ℕ} (lo : 508 ≤ n) (hi : n ≤ 511) : OriginalPair n := by
  interval_cases n
  · exact pair0508
  · exact pair0509
  · exact pair0510
  · exact pair0511

#print axioms range0508_0511

end LongCycleFinite.K3.DataExplicit
