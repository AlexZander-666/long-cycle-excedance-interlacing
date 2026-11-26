import LongCycleFinite.K4Signed.Rows0251
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0247

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0248 : orderAtOK 248 cert0247 cert0248 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0248 : OriginalPair 248 :=
  original_of_certificates (by decide) row0247 row0248 order0248

theorem order0249 : orderAtOK 249 cert0248 cert0249 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0249 : OriginalPair 249 :=
  original_of_certificates (by decide) row0248 row0249 order0249

theorem order0250 : orderAtOK 250 cert0249 cert0250 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0250 : OriginalPair 250 :=
  original_of_certificates (by decide) row0249 row0250 order0250

theorem order0251 : orderAtOK 251 cert0250 cert0251 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0251 : OriginalPair 251 :=
  original_of_certificates (by decide) row0250 row0251 order0251

theorem range0248_0251 {n : ℕ} (lo : 248 ≤ n) (hi : n ≤ 251) : OriginalPair n := by
  interval_cases n
  · exact pair0248
  · exact pair0249
  · exact pair0250
  · exact pair0251

#print axioms range0248_0251

end LongCycleFinite.K4.Data
