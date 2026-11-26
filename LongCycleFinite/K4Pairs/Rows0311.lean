import LongCycleFinite.K4Signed.Rows0311
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0307

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0308 : orderAtOK 308 cert0307 cert0308 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0308 : OriginalPair 308 :=
  original_of_certificates (by decide) row0307 row0308 order0308

theorem order0309 : orderAtOK 309 cert0308 cert0309 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0309 : OriginalPair 309 :=
  original_of_certificates (by decide) row0308 row0309 order0309

theorem order0310 : orderAtOK 310 cert0309 cert0310 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0310 : OriginalPair 310 :=
  original_of_certificates (by decide) row0309 row0310 order0310

theorem order0311 : orderAtOK 311 cert0310 cert0311 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0311 : OriginalPair 311 :=
  original_of_certificates (by decide) row0310 row0311 order0311

theorem range0308_0311 {n : ℕ} (lo : 308 ≤ n) (hi : n ≤ 311) : OriginalPair n := by
  interval_cases n
  · exact pair0308
  · exact pair0309
  · exact pair0310
  · exact pair0311

#print axioms range0308_0311

end LongCycleFinite.K4.Data
