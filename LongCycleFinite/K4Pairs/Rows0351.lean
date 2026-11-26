import LongCycleFinite.K4Signed.Rows0351
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0347

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0348 : orderAtOK 348 cert0347 cert0348 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0348 : OriginalPair 348 :=
  original_of_certificates (by decide) row0347 row0348 order0348

theorem order0349 : orderAtOK 349 cert0348 cert0349 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0349 : OriginalPair 349 :=
  original_of_certificates (by decide) row0348 row0349 order0349

theorem order0350 : orderAtOK 350 cert0349 cert0350 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0350 : OriginalPair 350 :=
  original_of_certificates (by decide) row0349 row0350 order0350

theorem order0351 : orderAtOK 351 cert0350 cert0351 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0351 : OriginalPair 351 :=
  original_of_certificates (by decide) row0350 row0351 order0351

theorem range0348_0351 {n : ℕ} (lo : 348 ≤ n) (hi : n ≤ 351) : OriginalPair n := by
  interval_cases n
  · exact pair0348
  · exact pair0349
  · exact pair0350
  · exact pair0351

#print axioms range0348_0351

end LongCycleFinite.K4.Data
