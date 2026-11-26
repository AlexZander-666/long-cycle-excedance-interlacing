import LongCycleFinite.K3SignedNatural.Rows0467
import LongCycleFinite.K3SignedNatural.Rows0463
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0464 :
    orderAtOK 464 cert0463 cert0464 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0464 : OriginalPair 464 :=
  original_of_certificates (by decide) row0463 row0464 order0464

theorem order0465 :
    orderAtOK 465 cert0464 cert0465 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0465 : OriginalPair 465 :=
  original_of_certificates (by decide) row0464 row0465 order0465

theorem order0466 :
    orderAtOK 466 cert0465 cert0466 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0466 : OriginalPair 466 :=
  original_of_certificates (by decide) row0465 row0466 order0466

theorem order0467 :
    orderAtOK 467 cert0466 cert0467 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0467 : OriginalPair 467 :=
  original_of_certificates (by decide) row0466 row0467 order0467

theorem range0464_0467 {n : ℕ} (lo : 464 ≤ n) (hi : n ≤ 467) : OriginalPair n := by
  interval_cases n
  · exact pair0464
  · exact pair0465
  · exact pair0466
  · exact pair0467

#print axioms range0464_0467

end LongCycleFinite.K3.DataExplicit
