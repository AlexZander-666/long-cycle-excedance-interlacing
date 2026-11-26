import LongCycleFinite.K4Signed.Rows0207
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0203

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0204 : orderAtOK 204 cert0203 cert0204 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0204 : OriginalPair 204 :=
  original_of_certificates (by decide) row0203 row0204 order0204

theorem order0205 : orderAtOK 205 cert0204 cert0205 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0205 : OriginalPair 205 :=
  original_of_certificates (by decide) row0204 row0205 order0205

theorem order0206 : orderAtOK 206 cert0205 cert0206 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0206 : OriginalPair 206 :=
  original_of_certificates (by decide) row0205 row0206 order0206

theorem order0207 : orderAtOK 207 cert0206 cert0207 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0207 : OriginalPair 207 :=
  original_of_certificates (by decide) row0206 row0207 order0207

theorem range0204_0207 {n : ℕ} (lo : 204 ≤ n) (hi : n ≤ 207) : OriginalPair n := by
  interval_cases n
  · exact pair0204
  · exact pair0205
  · exact pair0206
  · exact pair0207

#print axioms range0204_0207

end LongCycleFinite.K4.Data
