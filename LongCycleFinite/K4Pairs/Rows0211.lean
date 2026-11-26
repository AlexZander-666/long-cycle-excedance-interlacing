import LongCycleFinite.K4Signed.Rows0211
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0207

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0208 : orderAtOK 208 cert0207 cert0208 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0208 : OriginalPair 208 :=
  original_of_certificates (by decide) row0207 row0208 order0208

theorem order0209 : orderAtOK 209 cert0208 cert0209 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0209 : OriginalPair 209 :=
  original_of_certificates (by decide) row0208 row0209 order0209

theorem order0210 : orderAtOK 210 cert0209 cert0210 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0210 : OriginalPair 210 :=
  original_of_certificates (by decide) row0209 row0210 order0210

theorem order0211 : orderAtOK 211 cert0210 cert0211 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0211 : OriginalPair 211 :=
  original_of_certificates (by decide) row0210 row0211 order0211

theorem range0208_0211 {n : ℕ} (lo : 208 ≤ n) (hi : n ≤ 211) : OriginalPair n := by
  interval_cases n
  · exact pair0208
  · exact pair0209
  · exact pair0210
  · exact pair0211

#print axioms range0208_0211

end LongCycleFinite.K4.Data
