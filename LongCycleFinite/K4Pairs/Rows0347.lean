import LongCycleFinite.K4Signed.Rows0347
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0343

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0344 : orderAtOK 344 cert0343 cert0344 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0344 : OriginalPair 344 :=
  original_of_certificates (by decide) row0343 row0344 order0344

theorem order0345 : orderAtOK 345 cert0344 cert0345 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0345 : OriginalPair 345 :=
  original_of_certificates (by decide) row0344 row0345 order0345

theorem order0346 : orderAtOK 346 cert0345 cert0346 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0346 : OriginalPair 346 :=
  original_of_certificates (by decide) row0345 row0346 order0346

theorem order0347 : orderAtOK 347 cert0346 cert0347 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0347 : OriginalPair 347 :=
  original_of_certificates (by decide) row0346 row0347 order0347

theorem range0344_0347 {n : ℕ} (lo : 344 ≤ n) (hi : n ≤ 347) : OriginalPair n := by
  interval_cases n
  · exact pair0344
  · exact pair0345
  · exact pair0346
  · exact pair0347

#print axioms range0344_0347

end LongCycleFinite.K4.Data
