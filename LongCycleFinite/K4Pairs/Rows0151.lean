import LongCycleFinite.K4Signed.Rows0151
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0147

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0148 : orderAtOK 148 cert0147 cert0148 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0148 : OriginalPair 148 :=
  original_of_certificates (by decide) row0147 row0148 order0148

theorem order0149 : orderAtOK 149 cert0148 cert0149 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0149 : OriginalPair 149 :=
  original_of_certificates (by decide) row0148 row0149 order0149

theorem order0150 : orderAtOK 150 cert0149 cert0150 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0150 : OriginalPair 150 :=
  original_of_certificates (by decide) row0149 row0150 order0150

theorem order0151 : orderAtOK 151 cert0150 cert0151 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0151 : OriginalPair 151 :=
  original_of_certificates (by decide) row0150 row0151 order0151

theorem range0148_0151 {n : ℕ} (lo : 148 ≤ n) (hi : n ≤ 151) : OriginalPair n := by
  interval_cases n
  · exact pair0148
  · exact pair0149
  · exact pair0150
  · exact pair0151

#print axioms range0148_0151

end LongCycleFinite.K4.Data
