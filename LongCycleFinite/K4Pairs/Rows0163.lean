import LongCycleFinite.K4Signed.Rows0163
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0159

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0160 : orderAtOK 160 cert0159 cert0160 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0160 : OriginalPair 160 :=
  original_of_certificates (by decide) row0159 row0160 order0160

theorem order0161 : orderAtOK 161 cert0160 cert0161 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0161 : OriginalPair 161 :=
  original_of_certificates (by decide) row0160 row0161 order0161

theorem order0162 : orderAtOK 162 cert0161 cert0162 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0162 : OriginalPair 162 :=
  original_of_certificates (by decide) row0161 row0162 order0162

theorem order0163 : orderAtOK 163 cert0162 cert0163 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0163 : OriginalPair 163 :=
  original_of_certificates (by decide) row0162 row0163 order0163

theorem range0160_0163 {n : ℕ} (lo : 160 ≤ n) (hi : n ≤ 163) : OriginalPair n := by
  interval_cases n
  · exact pair0160
  · exact pair0161
  · exact pair0162
  · exact pair0163

#print axioms range0160_0163

end LongCycleFinite.K4.Data
