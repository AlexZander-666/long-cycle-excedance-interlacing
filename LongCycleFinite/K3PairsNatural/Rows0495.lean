import LongCycleFinite.K3SignedNatural.Rows0495
import LongCycleFinite.K3SignedNatural.Rows0491
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0492 :
    orderAtOK 492 cert0491 cert0492 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0492 : OriginalPair 492 :=
  original_of_certificates (by decide) row0491 row0492 order0492

theorem order0493 :
    orderAtOK 493 cert0492 cert0493 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0493 : OriginalPair 493 :=
  original_of_certificates (by decide) row0492 row0493 order0493

theorem order0494 :
    orderAtOK 494 cert0493 cert0494 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0494 : OriginalPair 494 :=
  original_of_certificates (by decide) row0493 row0494 order0494

theorem order0495 :
    orderAtOK 495 cert0494 cert0495 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0495 : OriginalPair 495 :=
  original_of_certificates (by decide) row0494 row0495 order0495

theorem range0492_0495 {n : ℕ} (lo : 492 ≤ n) (hi : n ≤ 495) : OriginalPair n := by
  interval_cases n
  · exact pair0492
  · exact pair0493
  · exact pair0494
  · exact pair0495

#print axioms range0492_0495

end LongCycleFinite.K3.DataExplicit
