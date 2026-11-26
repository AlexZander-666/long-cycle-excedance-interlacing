import LongCycleFinite.K4Signed.Rows0215
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0211

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0212 : orderAtOK 212 cert0211 cert0212 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0212 : OriginalPair 212 :=
  original_of_certificates (by decide) row0211 row0212 order0212

theorem order0213 : orderAtOK 213 cert0212 cert0213 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0213 : OriginalPair 213 :=
  original_of_certificates (by decide) row0212 row0213 order0213

theorem order0214 : orderAtOK 214 cert0213 cert0214 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0214 : OriginalPair 214 :=
  original_of_certificates (by decide) row0213 row0214 order0214

theorem order0215 : orderAtOK 215 cert0214 cert0215 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0215 : OriginalPair 215 :=
  original_of_certificates (by decide) row0214 row0215 order0215

theorem range0212_0215 {n : ℕ} (lo : 212 ≤ n) (hi : n ≤ 215) : OriginalPair n := by
  interval_cases n
  · exact pair0212
  · exact pair0213
  · exact pair0214
  · exact pair0215

#print axioms range0212_0215

end LongCycleFinite.K4.Data
