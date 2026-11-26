import LongCycleFinite.K3SignedNatural.Rows0443
import LongCycleFinite.K3SignedNatural.Rows0439
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0440 :
    orderAtOK 440 cert0439 cert0440 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0440 : OriginalPair 440 :=
  original_of_certificates (by decide) row0439 row0440 order0440

theorem order0441 :
    orderAtOK 441 cert0440 cert0441 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0441 : OriginalPair 441 :=
  original_of_certificates (by decide) row0440 row0441 order0441

theorem order0442 :
    orderAtOK 442 cert0441 cert0442 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0442 : OriginalPair 442 :=
  original_of_certificates (by decide) row0441 row0442 order0442

theorem order0443 :
    orderAtOK 443 cert0442 cert0443 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0443 : OriginalPair 443 :=
  original_of_certificates (by decide) row0442 row0443 order0443

theorem range0440_0443 {n : ℕ} (lo : 440 ≤ n) (hi : n ≤ 443) : OriginalPair n := by
  interval_cases n
  · exact pair0440
  · exact pair0441
  · exact pair0442
  · exact pair0443

#print axioms range0440_0443

end LongCycleFinite.K3.DataExplicit
