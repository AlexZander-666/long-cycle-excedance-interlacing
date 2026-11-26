import LongCycleFinite.K4Signed.Rows0227
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0223

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0224 : orderAtOK 224 cert0223 cert0224 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0224 : OriginalPair 224 :=
  original_of_certificates (by decide) row0223 row0224 order0224

theorem order0225 : orderAtOK 225 cert0224 cert0225 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0225 : OriginalPair 225 :=
  original_of_certificates (by decide) row0224 row0225 order0225

theorem order0226 : orderAtOK 226 cert0225 cert0226 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0226 : OriginalPair 226 :=
  original_of_certificates (by decide) row0225 row0226 order0226

theorem order0227 : orderAtOK 227 cert0226 cert0227 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0227 : OriginalPair 227 :=
  original_of_certificates (by decide) row0226 row0227 order0227

theorem range0224_0227 {n : ℕ} (lo : 224 ≤ n) (hi : n ≤ 227) : OriginalPair n := by
  interval_cases n
  · exact pair0224
  · exact pair0225
  · exact pair0226
  · exact pair0227

#print axioms range0224_0227

end LongCycleFinite.K4.Data
