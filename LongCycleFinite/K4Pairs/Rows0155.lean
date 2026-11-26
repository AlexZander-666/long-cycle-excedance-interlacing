import LongCycleFinite.K4Signed.Rows0155
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0151

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0152 : orderAtOK 152 cert0151 cert0152 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0152 : OriginalPair 152 :=
  original_of_certificates (by decide) row0151 row0152 order0152

theorem order0153 : orderAtOK 153 cert0152 cert0153 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0153 : OriginalPair 153 :=
  original_of_certificates (by decide) row0152 row0153 order0153

theorem order0154 : orderAtOK 154 cert0153 cert0154 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0154 : OriginalPair 154 :=
  original_of_certificates (by decide) row0153 row0154 order0154

theorem order0155 : orderAtOK 155 cert0154 cert0155 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0155 : OriginalPair 155 :=
  original_of_certificates (by decide) row0154 row0155 order0155

theorem range0152_0155 {n : ℕ} (lo : 152 ≤ n) (hi : n ≤ 155) : OriginalPair n := by
  interval_cases n
  · exact pair0152
  · exact pair0153
  · exact pair0154
  · exact pair0155

#print axioms range0152_0155

end LongCycleFinite.K4.Data
