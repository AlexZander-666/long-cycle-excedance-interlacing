import LongCycleFinite.K3SignedNatural.Rows0411
import LongCycleFinite.K3SignedNatural.Rows0407
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0408 :
    orderAtOK 408 cert0407 cert0408 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0408 : OriginalPair 408 :=
  original_of_certificates (by decide) row0407 row0408 order0408

theorem order0409 :
    orderAtOK 409 cert0408 cert0409 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0409 : OriginalPair 409 :=
  original_of_certificates (by decide) row0408 row0409 order0409

theorem order0410 :
    orderAtOK 410 cert0409 cert0410 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0410 : OriginalPair 410 :=
  original_of_certificates (by decide) row0409 row0410 order0410

theorem order0411 :
    orderAtOK 411 cert0410 cert0411 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0411 : OriginalPair 411 :=
  original_of_certificates (by decide) row0410 row0411 order0411

theorem range0408_0411 {n : ℕ} (lo : 408 ≤ n) (hi : n ≤ 411) : OriginalPair n := by
  interval_cases n
  · exact pair0408
  · exact pair0409
  · exact pair0410
  · exact pair0411

#print axioms range0408_0411

end LongCycleFinite.K3.DataExplicit
