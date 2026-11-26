import LongCycleFinite.K4Signed.Rows0175
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0171

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0172 : orderAtOK 172 cert0171 cert0172 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0172 : OriginalPair 172 :=
  original_of_certificates (by decide) row0171 row0172 order0172

theorem order0173 : orderAtOK 173 cert0172 cert0173 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0173 : OriginalPair 173 :=
  original_of_certificates (by decide) row0172 row0173 order0173

theorem order0174 : orderAtOK 174 cert0173 cert0174 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0174 : OriginalPair 174 :=
  original_of_certificates (by decide) row0173 row0174 order0174

theorem order0175 : orderAtOK 175 cert0174 cert0175 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0175 : OriginalPair 175 :=
  original_of_certificates (by decide) row0174 row0175 order0175

theorem range0172_0175 {n : ℕ} (lo : 172 ≤ n) (hi : n ≤ 175) : OriginalPair n := by
  interval_cases n
  · exact pair0172
  · exact pair0173
  · exact pair0174
  · exact pair0175

#print axioms range0172_0175

end LongCycleFinite.K4.Data
