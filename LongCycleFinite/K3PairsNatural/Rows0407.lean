import LongCycleFinite.K3SignedNatural.Rows0407
import LongCycleFinite.K3SignedNatural.Rows0403
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0404 :
    orderAtOK 404 cert0403 cert0404 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0404 : OriginalPair 404 :=
  original_of_certificates (by decide) row0403 row0404 order0404

theorem order0405 :
    orderAtOK 405 cert0404 cert0405 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0405 : OriginalPair 405 :=
  original_of_certificates (by decide) row0404 row0405 order0405

theorem order0406 :
    orderAtOK 406 cert0405 cert0406 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0406 : OriginalPair 406 :=
  original_of_certificates (by decide) row0405 row0406 order0406

theorem order0407 :
    orderAtOK 407 cert0406 cert0407 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0407 : OriginalPair 407 :=
  original_of_certificates (by decide) row0406 row0407 order0407

theorem range0404_0407 {n : ℕ} (lo : 404 ≤ n) (hi : n ≤ 407) : OriginalPair n := by
  interval_cases n
  · exact pair0404
  · exact pair0405
  · exact pair0406
  · exact pair0407

#print axioms range0404_0407

end LongCycleFinite.K3.DataExplicit
