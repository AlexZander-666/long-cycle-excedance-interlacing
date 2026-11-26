import LongCycleFinite.K3SignedNatural.Rows0423
import LongCycleFinite.K3SignedNatural.Rows0419
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0420 :
    orderAtOK 420 cert0419 cert0420 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0420 : OriginalPair 420 :=
  original_of_certificates (by decide) row0419 row0420 order0420

theorem order0421 :
    orderAtOK 421 cert0420 cert0421 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0421 : OriginalPair 421 :=
  original_of_certificates (by decide) row0420 row0421 order0421

theorem order0422 :
    orderAtOK 422 cert0421 cert0422 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0422 : OriginalPair 422 :=
  original_of_certificates (by decide) row0421 row0422 order0422

theorem order0423 :
    orderAtOK 423 cert0422 cert0423 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0423 : OriginalPair 423 :=
  original_of_certificates (by decide) row0422 row0423 order0423

theorem range0420_0423 {n : ℕ} (lo : 420 ≤ n) (hi : n ≤ 423) : OriginalPair n := by
  interval_cases n
  · exact pair0420
  · exact pair0421
  · exact pair0422
  · exact pair0423

#print axioms range0420_0423

end LongCycleFinite.K3.DataExplicit
