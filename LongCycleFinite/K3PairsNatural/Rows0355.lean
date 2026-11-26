import LongCycleFinite.K3SignedNatural.Rows0355
import LongCycleFinite.K3SignedNatural.Rows0351
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0352 :
    orderAtOK 352 cert0351 cert0352 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0352 : OriginalPair 352 :=
  original_of_certificates (by decide) row0351 row0352 order0352

theorem order0353 :
    orderAtOK 353 cert0352 cert0353 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0353 : OriginalPair 353 :=
  original_of_certificates (by decide) row0352 row0353 order0353

theorem order0354 :
    orderAtOK 354 cert0353 cert0354 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0354 : OriginalPair 354 :=
  original_of_certificates (by decide) row0353 row0354 order0354

theorem order0355 :
    orderAtOK 355 cert0354 cert0355 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0355 : OriginalPair 355 :=
  original_of_certificates (by decide) row0354 row0355 order0355

theorem range0352_0355 {n : ℕ} (lo : 352 ≤ n) (hi : n ≤ 355) : OriginalPair n := by
  interval_cases n
  · exact pair0352
  · exact pair0353
  · exact pair0354
  · exact pair0355

#print axioms range0352_0355

end LongCycleFinite.K3.DataExplicit
