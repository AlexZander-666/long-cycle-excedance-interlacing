import LongCycleFinite.K3SignedNatural.Rows0507
import LongCycleFinite.K3SignedNatural.Rows0503
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0504 :
    orderAtOK 504 cert0503 cert0504 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0504 : OriginalPair 504 :=
  original_of_certificates (by decide) row0503 row0504 order0504

theorem order0505 :
    orderAtOK 505 cert0504 cert0505 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0505 : OriginalPair 505 :=
  original_of_certificates (by decide) row0504 row0505 order0505

theorem order0506 :
    orderAtOK 506 cert0505 cert0506 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0506 : OriginalPair 506 :=
  original_of_certificates (by decide) row0505 row0506 order0506

theorem order0507 :
    orderAtOK 507 cert0506 cert0507 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0507 : OriginalPair 507 :=
  original_of_certificates (by decide) row0506 row0507 order0507

theorem range0504_0507 {n : ℕ} (lo : 504 ≤ n) (hi : n ≤ 507) : OriginalPair n := by
  interval_cases n
  · exact pair0504
  · exact pair0505
  · exact pair0506
  · exact pair0507

#print axioms range0504_0507

end LongCycleFinite.K3.DataExplicit
