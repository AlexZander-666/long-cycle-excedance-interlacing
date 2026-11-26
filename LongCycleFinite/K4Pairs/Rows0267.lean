import LongCycleFinite.K4Signed.Rows0267
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0263

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0264 : orderAtOK 264 cert0263 cert0264 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0264 : OriginalPair 264 :=
  original_of_certificates (by decide) row0263 row0264 order0264

theorem order0265 : orderAtOK 265 cert0264 cert0265 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0265 : OriginalPair 265 :=
  original_of_certificates (by decide) row0264 row0265 order0265

theorem order0266 : orderAtOK 266 cert0265 cert0266 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0266 : OriginalPair 266 :=
  original_of_certificates (by decide) row0265 row0266 order0266

theorem order0267 : orderAtOK 267 cert0266 cert0267 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0267 : OriginalPair 267 :=
  original_of_certificates (by decide) row0266 row0267 order0267

theorem range0264_0267 {n : ℕ} (lo : 264 ≤ n) (hi : n ≤ 267) : OriginalPair n := by
  interval_cases n
  · exact pair0264
  · exact pair0265
  · exact pair0266
  · exact pair0267

#print axioms range0264_0267

end LongCycleFinite.K4.Data
