import LongCycleFinite.K3SignedNatural.Rows0367
import LongCycleFinite.K3SignedNatural.Rows0363
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0364 :
    orderAtOK 364 cert0363 cert0364 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0364 : OriginalPair 364 :=
  original_of_certificates (by decide) row0363 row0364 order0364

theorem order0365 :
    orderAtOK 365 cert0364 cert0365 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0365 : OriginalPair 365 :=
  original_of_certificates (by decide) row0364 row0365 order0365

theorem order0366 :
    orderAtOK 366 cert0365 cert0366 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0366 : OriginalPair 366 :=
  original_of_certificates (by decide) row0365 row0366 order0366

theorem order0367 :
    orderAtOK 367 cert0366 cert0367 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0367 : OriginalPair 367 :=
  original_of_certificates (by decide) row0366 row0367 order0367

theorem range0364_0367 {n : ℕ} (lo : 364 ≤ n) (hi : n ≤ 367) : OriginalPair n := by
  interval_cases n
  · exact pair0364
  · exact pair0365
  · exact pair0366
  · exact pair0367

#print axioms range0364_0367

end LongCycleFinite.K3.DataExplicit
