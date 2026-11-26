import LongCycleFinite.K4Signed.Rows0199
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0195

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0196 : orderAtOK 196 cert0195 cert0196 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0196 : OriginalPair 196 :=
  original_of_certificates (by decide) row0195 row0196 order0196

theorem order0197 : orderAtOK 197 cert0196 cert0197 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0197 : OriginalPair 197 :=
  original_of_certificates (by decide) row0196 row0197 order0197

theorem order0198 : orderAtOK 198 cert0197 cert0198 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0198 : OriginalPair 198 :=
  original_of_certificates (by decide) row0197 row0198 order0198

theorem order0199 : orderAtOK 199 cert0198 cert0199 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0199 : OriginalPair 199 :=
  original_of_certificates (by decide) row0198 row0199 order0199

theorem range0196_0199 {n : ℕ} (lo : 196 ≤ n) (hi : n ≤ 199) : OriginalPair n := by
  interval_cases n
  · exact pair0196
  · exact pair0197
  · exact pair0198
  · exact pair0199

#print axioms range0196_0199

end LongCycleFinite.K4.Data
