import LongCycleFinite.K4Signed.Rows0283
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0279

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0280 : orderAtOK 280 cert0279 cert0280 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0280 : OriginalPair 280 :=
  original_of_certificates (by decide) row0279 row0280 order0280

theorem order0281 : orderAtOK 281 cert0280 cert0281 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0281 : OriginalPair 281 :=
  original_of_certificates (by decide) row0280 row0281 order0281

theorem order0282 : orderAtOK 282 cert0281 cert0282 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0282 : OriginalPair 282 :=
  original_of_certificates (by decide) row0281 row0282 order0282

theorem order0283 : orderAtOK 283 cert0282 cert0283 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0283 : OriginalPair 283 :=
  original_of_certificates (by decide) row0282 row0283 order0283

theorem range0280_0283 {n : ℕ} (lo : 280 ≤ n) (hi : n ≤ 283) : OriginalPair n := by
  interval_cases n
  · exact pair0280
  · exact pair0281
  · exact pair0282
  · exact pair0283

#print axioms range0280_0283

end LongCycleFinite.K4.Data
