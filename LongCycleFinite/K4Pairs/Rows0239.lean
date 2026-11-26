import LongCycleFinite.K4Signed.Rows0239
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0235

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0236 : orderAtOK 236 cert0235 cert0236 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0236 : OriginalPair 236 :=
  original_of_certificates (by decide) row0235 row0236 order0236

theorem order0237 : orderAtOK 237 cert0236 cert0237 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0237 : OriginalPair 237 :=
  original_of_certificates (by decide) row0236 row0237 order0237

theorem order0238 : orderAtOK 238 cert0237 cert0238 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0238 : OriginalPair 238 :=
  original_of_certificates (by decide) row0237 row0238 order0238

theorem order0239 : orderAtOK 239 cert0238 cert0239 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0239 : OriginalPair 239 :=
  original_of_certificates (by decide) row0238 row0239 order0239

theorem range0236_0239 {n : ℕ} (lo : 236 ≤ n) (hi : n ≤ 239) : OriginalPair n := by
  interval_cases n
  · exact pair0236
  · exact pair0237
  · exact pair0238
  · exact pair0239

#print axioms range0236_0239

end LongCycleFinite.K4.Data
