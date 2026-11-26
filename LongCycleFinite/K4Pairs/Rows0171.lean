import LongCycleFinite.K4Signed.Rows0171
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0167

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0168 : orderAtOK 168 cert0167 cert0168 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0168 : OriginalPair 168 :=
  original_of_certificates (by decide) row0167 row0168 order0168

theorem order0169 : orderAtOK 169 cert0168 cert0169 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0169 : OriginalPair 169 :=
  original_of_certificates (by decide) row0168 row0169 order0169

theorem order0170 : orderAtOK 170 cert0169 cert0170 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0170 : OriginalPair 170 :=
  original_of_certificates (by decide) row0169 row0170 order0170

theorem order0171 : orderAtOK 171 cert0170 cert0171 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0171 : OriginalPair 171 :=
  original_of_certificates (by decide) row0170 row0171 order0171

theorem range0168_0171 {n : ℕ} (lo : 168 ≤ n) (hi : n ≤ 171) : OriginalPair n := by
  interval_cases n
  · exact pair0168
  · exact pair0169
  · exact pair0170
  · exact pair0171

#print axioms range0168_0171

end LongCycleFinite.K4.Data
