import LongCycleFinite.K4Signed.Rows0335
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0331

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0332 : orderAtOK 332 cert0331 cert0332 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0332 : OriginalPair 332 :=
  original_of_certificates (by decide) row0331 row0332 order0332

theorem order0333 : orderAtOK 333 cert0332 cert0333 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0333 : OriginalPair 333 :=
  original_of_certificates (by decide) row0332 row0333 order0333

theorem order0334 : orderAtOK 334 cert0333 cert0334 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0334 : OriginalPair 334 :=
  original_of_certificates (by decide) row0333 row0334 order0334

theorem order0335 : orderAtOK 335 cert0334 cert0335 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0335 : OriginalPair 335 :=
  original_of_certificates (by decide) row0334 row0335 order0335

theorem range0332_0335 {n : ℕ} (lo : 332 ≤ n) (hi : n ≤ 335) : OriginalPair n := by
  interval_cases n
  · exact pair0332
  · exact pair0333
  · exact pair0334
  · exact pair0335

#print axioms range0332_0335

end LongCycleFinite.K4.Data
