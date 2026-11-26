import LongCycleFinite.K4Signed.Rows0235
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0231

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0232 : orderAtOK 232 cert0231 cert0232 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0232 : OriginalPair 232 :=
  original_of_certificates (by decide) row0231 row0232 order0232

theorem order0233 : orderAtOK 233 cert0232 cert0233 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0233 : OriginalPair 233 :=
  original_of_certificates (by decide) row0232 row0233 order0233

theorem order0234 : orderAtOK 234 cert0233 cert0234 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0234 : OriginalPair 234 :=
  original_of_certificates (by decide) row0233 row0234 order0234

theorem order0235 : orderAtOK 235 cert0234 cert0235 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0235 : OriginalPair 235 :=
  original_of_certificates (by decide) row0234 row0235 order0235

theorem range0232_0235 {n : ℕ} (lo : 232 ≤ n) (hi : n ≤ 235) : OriginalPair n := by
  interval_cases n
  · exact pair0232
  · exact pair0233
  · exact pair0234
  · exact pair0235

#print axioms range0232_0235

end LongCycleFinite.K4.Data
