import LongCycleFinite.K4Signed.Rows0247
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0243

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0244 : orderAtOK 244 cert0243 cert0244 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0244 : OriginalPair 244 :=
  original_of_certificates (by decide) row0243 row0244 order0244

theorem order0245 : orderAtOK 245 cert0244 cert0245 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0245 : OriginalPair 245 :=
  original_of_certificates (by decide) row0244 row0245 order0245

theorem order0246 : orderAtOK 246 cert0245 cert0246 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0246 : OriginalPair 246 :=
  original_of_certificates (by decide) row0245 row0246 order0246

theorem order0247 : orderAtOK 247 cert0246 cert0247 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0247 : OriginalPair 247 :=
  original_of_certificates (by decide) row0246 row0247 order0247

theorem range0244_0247 {n : ℕ} (lo : 244 ≤ n) (hi : n ≤ 247) : OriginalPair n := by
  interval_cases n
  · exact pair0244
  · exact pair0245
  · exact pair0246
  · exact pair0247

#print axioms range0244_0247

end LongCycleFinite.K4.Data
