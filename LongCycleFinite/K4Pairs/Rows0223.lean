import LongCycleFinite.K4Signed.Rows0223
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0219

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0220 : orderAtOK 220 cert0219 cert0220 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0220 : OriginalPair 220 :=
  original_of_certificates (by decide) row0219 row0220 order0220

theorem order0221 : orderAtOK 221 cert0220 cert0221 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0221 : OriginalPair 221 :=
  original_of_certificates (by decide) row0220 row0221 order0221

theorem order0222 : orderAtOK 222 cert0221 cert0222 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0222 : OriginalPair 222 :=
  original_of_certificates (by decide) row0221 row0222 order0222

theorem order0223 : orderAtOK 223 cert0222 cert0223 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0223 : OriginalPair 223 :=
  original_of_certificates (by decide) row0222 row0223 order0223

theorem range0220_0223 {n : ℕ} (lo : 220 ≤ n) (hi : n ≤ 223) : OriginalPair n := by
  interval_cases n
  · exact pair0220
  · exact pair0221
  · exact pair0222
  · exact pair0223

#print axioms range0220_0223

end LongCycleFinite.K4.Data
