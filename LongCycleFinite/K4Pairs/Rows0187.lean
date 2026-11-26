import LongCycleFinite.K4Signed.Rows0187
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0183

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0184 : orderAtOK 184 cert0183 cert0184 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0184 : OriginalPair 184 :=
  original_of_certificates (by decide) row0183 row0184 order0184

theorem order0185 : orderAtOK 185 cert0184 cert0185 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0185 : OriginalPair 185 :=
  original_of_certificates (by decide) row0184 row0185 order0185

theorem order0186 : orderAtOK 186 cert0185 cert0186 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0186 : OriginalPair 186 :=
  original_of_certificates (by decide) row0185 row0186 order0186

theorem order0187 : orderAtOK 187 cert0186 cert0187 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0187 : OriginalPair 187 :=
  original_of_certificates (by decide) row0186 row0187 order0187

theorem range0184_0187 {n : ℕ} (lo : 184 ≤ n) (hi : n ≤ 187) : OriginalPair n := by
  interval_cases n
  · exact pair0184
  · exact pair0185
  · exact pair0186
  · exact pair0187

#print axioms range0184_0187

end LongCycleFinite.K4.Data
