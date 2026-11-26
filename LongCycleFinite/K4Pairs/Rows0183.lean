import LongCycleFinite.K4Signed.Rows0183
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0179

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0180 : orderAtOK 180 cert0179 cert0180 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0180 : OriginalPair 180 :=
  original_of_certificates (by decide) row0179 row0180 order0180

theorem order0181 : orderAtOK 181 cert0180 cert0181 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0181 : OriginalPair 181 :=
  original_of_certificates (by decide) row0180 row0181 order0181

theorem order0182 : orderAtOK 182 cert0181 cert0182 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0182 : OriginalPair 182 :=
  original_of_certificates (by decide) row0181 row0182 order0182

theorem order0183 : orderAtOK 183 cert0182 cert0183 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0183 : OriginalPair 183 :=
  original_of_certificates (by decide) row0182 row0183 order0183

theorem range0180_0183 {n : ℕ} (lo : 180 ≤ n) (hi : n ≤ 183) : OriginalPair n := by
  interval_cases n
  · exact pair0180
  · exact pair0181
  · exact pair0182
  · exact pair0183

#print axioms range0180_0183

end LongCycleFinite.K4.Data
