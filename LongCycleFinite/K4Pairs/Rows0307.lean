import LongCycleFinite.K4Signed.Rows0307
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0303

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0304 : orderAtOK 304 cert0303 cert0304 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0304 : OriginalPair 304 :=
  original_of_certificates (by decide) row0303 row0304 order0304

theorem order0305 : orderAtOK 305 cert0304 cert0305 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0305 : OriginalPair 305 :=
  original_of_certificates (by decide) row0304 row0305 order0305

theorem order0306 : orderAtOK 306 cert0305 cert0306 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0306 : OriginalPair 306 :=
  original_of_certificates (by decide) row0305 row0306 order0306

theorem order0307 : orderAtOK 307 cert0306 cert0307 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0307 : OriginalPair 307 :=
  original_of_certificates (by decide) row0306 row0307 order0307

theorem range0304_0307 {n : ℕ} (lo : 304 ≤ n) (hi : n ≤ 307) : OriginalPair n := by
  interval_cases n
  · exact pair0304
  · exact pair0305
  · exact pair0306
  · exact pair0307

#print axioms range0304_0307

end LongCycleFinite.K4.Data
