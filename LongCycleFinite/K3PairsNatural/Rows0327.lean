import LongCycleFinite.K3SignedNatural.Rows0327
import LongCycleFinite.K3SignedNatural.Rows0323
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0324 :
    orderAtOK 324 cert0323 cert0324 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0324 : OriginalPair 324 :=
  original_of_certificates (by decide) row0323 row0324 order0324

theorem order0325 :
    orderAtOK 325 cert0324 cert0325 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0325 : OriginalPair 325 :=
  original_of_certificates (by decide) row0324 row0325 order0325

theorem order0326 :
    orderAtOK 326 cert0325 cert0326 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0326 : OriginalPair 326 :=
  original_of_certificates (by decide) row0325 row0326 order0326

theorem order0327 :
    orderAtOK 327 cert0326 cert0327 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0327 : OriginalPair 327 :=
  original_of_certificates (by decide) row0326 row0327 order0327

theorem range0324_0327 {n : ℕ} (lo : 324 ≤ n) (hi : n ≤ 327) : OriginalPair n := by
  interval_cases n
  · exact pair0324
  · exact pair0325
  · exact pair0326
  · exact pair0327

#print axioms range0324_0327

end LongCycleFinite.K3.DataExplicit
