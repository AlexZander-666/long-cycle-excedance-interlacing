import LongCycleFinite.K4Signed.Rows0219
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0215

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0216 : orderAtOK 216 cert0215 cert0216 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0216 : OriginalPair 216 :=
  original_of_certificates (by decide) row0215 row0216 order0216

theorem order0217 : orderAtOK 217 cert0216 cert0217 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0217 : OriginalPair 217 :=
  original_of_certificates (by decide) row0216 row0217 order0217

theorem order0218 : orderAtOK 218 cert0217 cert0218 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0218 : OriginalPair 218 :=
  original_of_certificates (by decide) row0217 row0218 order0218

theorem order0219 : orderAtOK 219 cert0218 cert0219 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0219 : OriginalPair 219 :=
  original_of_certificates (by decide) row0218 row0219 order0219

theorem range0216_0219 {n : ℕ} (lo : 216 ≤ n) (hi : n ≤ 219) : OriginalPair n := by
  interval_cases n
  · exact pair0216
  · exact pair0217
  · exact pair0218
  · exact pair0219

#print axioms range0216_0219

end LongCycleFinite.K4.Data
