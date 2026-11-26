import LongCycleFinite.K3SignedNatural.Rows0459
import LongCycleFinite.K3SignedNatural.Rows0455
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0456 :
    orderAtOK 456 cert0455 cert0456 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0456 : OriginalPair 456 :=
  original_of_certificates (by decide) row0455 row0456 order0456

theorem order0457 :
    orderAtOK 457 cert0456 cert0457 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0457 : OriginalPair 457 :=
  original_of_certificates (by decide) row0456 row0457 order0457

theorem order0458 :
    orderAtOK 458 cert0457 cert0458 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0458 : OriginalPair 458 :=
  original_of_certificates (by decide) row0457 row0458 order0458

theorem order0459 :
    orderAtOK 459 cert0458 cert0459 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0459 : OriginalPair 459 :=
  original_of_certificates (by decide) row0458 row0459 order0459

theorem range0456_0459 {n : ℕ} (lo : 456 ≤ n) (hi : n ≤ 459) : OriginalPair n := by
  interval_cases n
  · exact pair0456
  · exact pair0457
  · exact pair0458
  · exact pair0459

#print axioms range0456_0459

end LongCycleFinite.K3.DataExplicit
