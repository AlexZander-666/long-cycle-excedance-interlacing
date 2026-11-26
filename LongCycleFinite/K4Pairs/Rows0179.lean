import LongCycleFinite.K4Signed.Rows0179
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0175

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0176 : orderAtOK 176 cert0175 cert0176 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0176 : OriginalPair 176 :=
  original_of_certificates (by decide) row0175 row0176 order0176

theorem order0177 : orderAtOK 177 cert0176 cert0177 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0177 : OriginalPair 177 :=
  original_of_certificates (by decide) row0176 row0177 order0177

theorem order0178 : orderAtOK 178 cert0177 cert0178 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0178 : OriginalPair 178 :=
  original_of_certificates (by decide) row0177 row0178 order0178

theorem order0179 : orderAtOK 179 cert0178 cert0179 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0179 : OriginalPair 179 :=
  original_of_certificates (by decide) row0178 row0179 order0179

theorem range0176_0179 {n : ℕ} (lo : 176 ≤ n) (hi : n ≤ 179) : OriginalPair n := by
  interval_cases n
  · exact pair0176
  · exact pair0177
  · exact pair0178
  · exact pair0179

#print axioms range0176_0179

end LongCycleFinite.K4.Data
