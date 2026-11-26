import LongCycleFinite.K4Signed.Rows0323
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0319

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0320 : orderAtOK 320 cert0319 cert0320 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0320 : OriginalPair 320 :=
  original_of_certificates (by decide) row0319 row0320 order0320

theorem order0321 : orderAtOK 321 cert0320 cert0321 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0321 : OriginalPair 321 :=
  original_of_certificates (by decide) row0320 row0321 order0321

theorem order0322 : orderAtOK 322 cert0321 cert0322 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0322 : OriginalPair 322 :=
  original_of_certificates (by decide) row0321 row0322 order0322

theorem order0323 : orderAtOK 323 cert0322 cert0323 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0323 : OriginalPair 323 :=
  original_of_certificates (by decide) row0322 row0323 order0323

theorem range0320_0323 {n : ℕ} (lo : 320 ≤ n) (hi : n ≤ 323) : OriginalPair n := by
  interval_cases n
  · exact pair0320
  · exact pair0321
  · exact pair0322
  · exact pair0323

#print axioms range0320_0323

end LongCycleFinite.K4.Data
