import LongCycleFinite.K4Signed.Rows0343
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0339

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0340 : orderAtOK 340 cert0339 cert0340 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0340 : OriginalPair 340 :=
  original_of_certificates (by decide) row0339 row0340 order0340

theorem order0341 : orderAtOK 341 cert0340 cert0341 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0341 : OriginalPair 341 :=
  original_of_certificates (by decide) row0340 row0341 order0341

theorem order0342 : orderAtOK 342 cert0341 cert0342 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0342 : OriginalPair 342 :=
  original_of_certificates (by decide) row0341 row0342 order0342

theorem order0343 : orderAtOK 343 cert0342 cert0343 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0343 : OriginalPair 343 :=
  original_of_certificates (by decide) row0342 row0343 order0343

theorem range0340_0343 {n : ℕ} (lo : 340 ≤ n) (hi : n ≤ 343) : OriginalPair n := by
  interval_cases n
  · exact pair0340
  · exact pair0341
  · exact pair0342
  · exact pair0343

#print axioms range0340_0343

end LongCycleFinite.K4.Data
