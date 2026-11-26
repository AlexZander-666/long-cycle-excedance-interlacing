import LongCycleFinite.K4Signed.Rows0275
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0271

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0272 : orderAtOK 272 cert0271 cert0272 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0272 : OriginalPair 272 :=
  original_of_certificates (by decide) row0271 row0272 order0272

theorem order0273 : orderAtOK 273 cert0272 cert0273 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0273 : OriginalPair 273 :=
  original_of_certificates (by decide) row0272 row0273 order0273

theorem order0274 : orderAtOK 274 cert0273 cert0274 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0274 : OriginalPair 274 :=
  original_of_certificates (by decide) row0273 row0274 order0274

theorem order0275 : orderAtOK 275 cert0274 cert0275 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0275 : OriginalPair 275 :=
  original_of_certificates (by decide) row0274 row0275 order0275

theorem range0272_0275 {n : ℕ} (lo : 272 ≤ n) (hi : n ≤ 275) : OriginalPair n := by
  interval_cases n
  · exact pair0272
  · exact pair0273
  · exact pair0274
  · exact pair0275

#print axioms range0272_0275

end LongCycleFinite.K4.Data
