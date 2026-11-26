import LongCycleFinite.K4Signed.Rows0243
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0239

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0240 : orderAtOK 240 cert0239 cert0240 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0240 : OriginalPair 240 :=
  original_of_certificates (by decide) row0239 row0240 order0240

theorem order0241 : orderAtOK 241 cert0240 cert0241 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0241 : OriginalPair 241 :=
  original_of_certificates (by decide) row0240 row0241 order0241

theorem order0242 : orderAtOK 242 cert0241 cert0242 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0242 : OriginalPair 242 :=
  original_of_certificates (by decide) row0241 row0242 order0242

theorem order0243 : orderAtOK 243 cert0242 cert0243 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0243 : OriginalPair 243 :=
  original_of_certificates (by decide) row0242 row0243 order0243

theorem range0240_0243 {n : ℕ} (lo : 240 ≤ n) (hi : n ≤ 243) : OriginalPair n := by
  interval_cases n
  · exact pair0240
  · exact pair0241
  · exact pair0242
  · exact pair0243

#print axioms range0240_0243

end LongCycleFinite.K4.Data
