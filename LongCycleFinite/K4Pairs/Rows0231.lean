import LongCycleFinite.K4Signed.Rows0231
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0227

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0228 : orderAtOK 228 cert0227 cert0228 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0228 : OriginalPair 228 :=
  original_of_certificates (by decide) row0227 row0228 order0228

theorem order0229 : orderAtOK 229 cert0228 cert0229 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0229 : OriginalPair 229 :=
  original_of_certificates (by decide) row0228 row0229 order0229

theorem order0230 : orderAtOK 230 cert0229 cert0230 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0230 : OriginalPair 230 :=
  original_of_certificates (by decide) row0229 row0230 order0230

theorem order0231 : orderAtOK 231 cert0230 cert0231 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0231 : OriginalPair 231 :=
  original_of_certificates (by decide) row0230 row0231 order0231

theorem range0228_0231 {n : ℕ} (lo : 228 ≤ n) (hi : n ≤ 231) : OriginalPair n := by
  interval_cases n
  · exact pair0228
  · exact pair0229
  · exact pair0230
  · exact pair0231

#print axioms range0228_0231

end LongCycleFinite.K4.Data
