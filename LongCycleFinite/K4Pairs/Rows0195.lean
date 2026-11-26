import LongCycleFinite.K4Signed.Rows0195
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0191

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0192 : orderAtOK 192 cert0191 cert0192 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0192 : OriginalPair 192 :=
  original_of_certificates (by decide) row0191 row0192 order0192

theorem order0193 : orderAtOK 193 cert0192 cert0193 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0193 : OriginalPair 193 :=
  original_of_certificates (by decide) row0192 row0193 order0193

theorem order0194 : orderAtOK 194 cert0193 cert0194 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0194 : OriginalPair 194 :=
  original_of_certificates (by decide) row0193 row0194 order0194

theorem order0195 : orderAtOK 195 cert0194 cert0195 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0195 : OriginalPair 195 :=
  original_of_certificates (by decide) row0194 row0195 order0195

theorem range0192_0195 {n : ℕ} (lo : 192 ≤ n) (hi : n ≤ 195) : OriginalPair n := by
  interval_cases n
  · exact pair0192
  · exact pair0193
  · exact pair0194
  · exact pair0195

#print axioms range0192_0195

end LongCycleFinite.K4.Data
