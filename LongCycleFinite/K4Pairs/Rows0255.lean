import LongCycleFinite.K4Signed.Rows0255
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0251

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0252 : orderAtOK 252 cert0251 cert0252 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0252 : OriginalPair 252 :=
  original_of_certificates (by decide) row0251 row0252 order0252

theorem order0253 : orderAtOK 253 cert0252 cert0253 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0253 : OriginalPair 253 :=
  original_of_certificates (by decide) row0252 row0253 order0253

theorem order0254 : orderAtOK 254 cert0253 cert0254 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0254 : OriginalPair 254 :=
  original_of_certificates (by decide) row0253 row0254 order0254

theorem order0255 : orderAtOK 255 cert0254 cert0255 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0255 : OriginalPair 255 :=
  original_of_certificates (by decide) row0254 row0255 order0255

theorem range0252_0255 {n : ℕ} (lo : 252 ≤ n) (hi : n ≤ 255) : OriginalPair n := by
  interval_cases n
  · exact pair0252
  · exact pair0253
  · exact pair0254
  · exact pair0255

#print axioms range0252_0255

end LongCycleFinite.K4.Data
