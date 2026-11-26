import LongCycleFinite.K4Signed.Rows0427
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0423

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0424 : orderAtOK 424 cert0423 cert0424 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0424 : OriginalPair 424 :=
  original_of_certificates (by decide) row0423 row0424 order0424

theorem order0425 : orderAtOK 425 cert0424 cert0425 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0425 : OriginalPair 425 :=
  original_of_certificates (by decide) row0424 row0425 order0425

theorem order0426 : orderAtOK 426 cert0425 cert0426 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0426 : OriginalPair 426 :=
  original_of_certificates (by decide) row0425 row0426 order0426

theorem order0427 : orderAtOK 427 cert0426 cert0427 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0427 : OriginalPair 427 :=
  original_of_certificates (by decide) row0426 row0427 order0427

theorem range0424_0427 {n : ℕ} (lo : 424 ≤ n) (hi : n ≤ 427) : OriginalPair n := by
  interval_cases n
  · exact pair0424
  · exact pair0425
  · exact pair0426
  · exact pair0427

#print axioms range0424_0427

end LongCycleFinite.K4.Data
