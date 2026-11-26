import LongCycleFinite.K3SignedNatural.Rows0383
import LongCycleFinite.K3SignedNatural.Rows0379
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0380 :
    orderAtOK 380 cert0379 cert0380 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0380 : OriginalPair 380 :=
  original_of_certificates (by decide) row0379 row0380 order0380

theorem order0381 :
    orderAtOK 381 cert0380 cert0381 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0381 : OriginalPair 381 :=
  original_of_certificates (by decide) row0380 row0381 order0381

theorem order0382 :
    orderAtOK 382 cert0381 cert0382 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0382 : OriginalPair 382 :=
  original_of_certificates (by decide) row0381 row0382 order0382

theorem order0383 :
    orderAtOK 383 cert0382 cert0383 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0383 : OriginalPair 383 :=
  original_of_certificates (by decide) row0382 row0383 order0383

theorem range0380_0383 {n : ℕ} (lo : 380 ≤ n) (hi : n ≤ 383) : OriginalPair n := by
  interval_cases n
  · exact pair0380
  · exact pair0381
  · exact pair0382
  · exact pair0383

#print axioms range0380_0383

end LongCycleFinite.K3.DataExplicit
