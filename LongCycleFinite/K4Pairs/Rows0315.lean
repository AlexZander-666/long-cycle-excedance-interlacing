import LongCycleFinite.K4Signed.Rows0315
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0311

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0312 : orderAtOK 312 cert0311 cert0312 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0312 : OriginalPair 312 :=
  original_of_certificates (by decide) row0311 row0312 order0312

theorem order0313 : orderAtOK 313 cert0312 cert0313 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0313 : OriginalPair 313 :=
  original_of_certificates (by decide) row0312 row0313 order0313

theorem order0314 : orderAtOK 314 cert0313 cert0314 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0314 : OriginalPair 314 :=
  original_of_certificates (by decide) row0313 row0314 order0314

theorem order0315 : orderAtOK 315 cert0314 cert0315 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0315 : OriginalPair 315 :=
  original_of_certificates (by decide) row0314 row0315 order0315

theorem range0312_0315 {n : ℕ} (lo : 312 ≤ n) (hi : n ≤ 315) : OriginalPair n := by
  interval_cases n
  · exact pair0312
  · exact pair0313
  · exact pair0314
  · exact pair0315

#print axioms range0312_0315

end LongCycleFinite.K4.Data
