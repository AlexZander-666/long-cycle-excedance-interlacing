import LongCycleFinite.K3SignedNatural.Rows0375
import LongCycleFinite.K3SignedNatural.Rows0371
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0372 :
    orderAtOK 372 cert0371 cert0372 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0372 : OriginalPair 372 :=
  original_of_certificates (by decide) row0371 row0372 order0372

theorem order0373 :
    orderAtOK 373 cert0372 cert0373 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0373 : OriginalPair 373 :=
  original_of_certificates (by decide) row0372 row0373 order0373

theorem order0374 :
    orderAtOK 374 cert0373 cert0374 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0374 : OriginalPair 374 :=
  original_of_certificates (by decide) row0373 row0374 order0374

theorem order0375 :
    orderAtOK 375 cert0374 cert0375 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0375 : OriginalPair 375 :=
  original_of_certificates (by decide) row0374 row0375 order0375

theorem range0372_0375 {n : ℕ} (lo : 372 ≤ n) (hi : n ≤ 375) : OriginalPair n := by
  interval_cases n
  · exact pair0372
  · exact pair0373
  · exact pair0374
  · exact pair0375

#print axioms range0372_0375

end LongCycleFinite.K3.DataExplicit
