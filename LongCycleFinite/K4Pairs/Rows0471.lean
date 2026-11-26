import LongCycleFinite.K4Signed.Rows0471
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0467

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0468 : orderAtOK 468 cert0467 cert0468 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0468 : OriginalPair 468 :=
  original_of_certificates (by decide) row0467 row0468 order0468

theorem order0469 : orderAtOK 469 cert0468 cert0469 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0469 : OriginalPair 469 :=
  original_of_certificates (by decide) row0468 row0469 order0469

theorem order0470 : orderAtOK 470 cert0469 cert0470 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0470 : OriginalPair 470 :=
  original_of_certificates (by decide) row0469 row0470 order0470

theorem order0471 : orderAtOK 471 cert0470 cert0471 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0471 : OriginalPair 471 :=
  original_of_certificates (by decide) row0470 row0471 order0471

theorem range0468_0471 {n : ℕ} (lo : 468 ≤ n) (hi : n ≤ 471) : OriginalPair n := by
  interval_cases n
  · exact pair0468
  · exact pair0469
  · exact pair0470
  · exact pair0471

#print axioms range0468_0471

end LongCycleFinite.K4.Data
