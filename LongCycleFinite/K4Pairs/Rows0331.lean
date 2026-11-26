import LongCycleFinite.K4Signed.Rows0331
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0327

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0328 : orderAtOK 328 cert0327 cert0328 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0328 : OriginalPair 328 :=
  original_of_certificates (by decide) row0327 row0328 order0328

theorem order0329 : orderAtOK 329 cert0328 cert0329 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0329 : OriginalPair 329 :=
  original_of_certificates (by decide) row0328 row0329 order0329

theorem order0330 : orderAtOK 330 cert0329 cert0330 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0330 : OriginalPair 330 :=
  original_of_certificates (by decide) row0329 row0330 order0330

theorem order0331 : orderAtOK 331 cert0330 cert0331 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0331 : OriginalPair 331 :=
  original_of_certificates (by decide) row0330 row0331 order0331

theorem range0328_0331 {n : ℕ} (lo : 328 ≤ n) (hi : n ≤ 331) : OriginalPair n := by
  interval_cases n
  · exact pair0328
  · exact pair0329
  · exact pair0330
  · exact pair0331

#print axioms range0328_0331

end LongCycleFinite.K4.Data
