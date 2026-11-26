import LongCycleFinite.K4Signed.Rows0167
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0163

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0164 : orderAtOK 164 cert0163 cert0164 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0164 : OriginalPair 164 :=
  original_of_certificates (by decide) row0163 row0164 order0164

theorem order0165 : orderAtOK 165 cert0164 cert0165 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0165 : OriginalPair 165 :=
  original_of_certificates (by decide) row0164 row0165 order0165

theorem order0166 : orderAtOK 166 cert0165 cert0166 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0166 : OriginalPair 166 :=
  original_of_certificates (by decide) row0165 row0166 order0166

theorem order0167 : orderAtOK 167 cert0166 cert0167 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0167 : OriginalPair 167 :=
  original_of_certificates (by decide) row0166 row0167 order0167

theorem range0164_0167 {n : ℕ} (lo : 164 ≤ n) (hi : n ≤ 167) : OriginalPair n := by
  interval_cases n
  · exact pair0164
  · exact pair0165
  · exact pair0166
  · exact pair0167

#print axioms range0164_0167

end LongCycleFinite.K4.Data
