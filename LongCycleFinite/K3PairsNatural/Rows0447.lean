import LongCycleFinite.K3SignedNatural.Rows0447
import LongCycleFinite.K3SignedNatural.Rows0443
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0444 :
    orderAtOK 444 cert0443 cert0444 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0444 : OriginalPair 444 :=
  original_of_certificates (by decide) row0443 row0444 order0444

theorem order0445 :
    orderAtOK 445 cert0444 cert0445 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0445 : OriginalPair 445 :=
  original_of_certificates (by decide) row0444 row0445 order0445

theorem order0446 :
    orderAtOK 446 cert0445 cert0446 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0446 : OriginalPair 446 :=
  original_of_certificates (by decide) row0445 row0446 order0446

theorem order0447 :
    orderAtOK 447 cert0446 cert0447 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0447 : OriginalPair 447 :=
  original_of_certificates (by decide) row0446 row0447 order0447

theorem range0444_0447 {n : ℕ} (lo : 444 ≤ n) (hi : n ≤ 447) : OriginalPair n := by
  interval_cases n
  · exact pair0444
  · exact pair0445
  · exact pair0446
  · exact pair0447

#print axioms range0444_0447

end LongCycleFinite.K3.DataExplicit
