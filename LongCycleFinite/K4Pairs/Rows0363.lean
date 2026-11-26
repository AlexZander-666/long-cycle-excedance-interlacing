import LongCycleFinite.K4Signed.Rows0363
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0359

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0360 : orderAtOK 360 cert0359 cert0360 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0360 : OriginalPair 360 :=
  original_of_certificates (by decide) row0359 row0360 order0360

theorem order0361 : orderAtOK 361 cert0360 cert0361 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0361 : OriginalPair 361 :=
  original_of_certificates (by decide) row0360 row0361 order0361

theorem order0362 : orderAtOK 362 cert0361 cert0362 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0362 : OriginalPair 362 :=
  original_of_certificates (by decide) row0361 row0362 order0362

theorem order0363 : orderAtOK 363 cert0362 cert0363 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0363 : OriginalPair 363 :=
  original_of_certificates (by decide) row0362 row0363 order0363

theorem range0360_0363 {n : ℕ} (lo : 360 ≤ n) (hi : n ≤ 363) : OriginalPair n := by
  interval_cases n
  · exact pair0360
  · exact pair0361
  · exact pair0362
  · exact pair0363

#print axioms range0360_0363

end LongCycleFinite.K4.Data
