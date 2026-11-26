import LongCycleFinite.K4Signed.Rows0339
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0335

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0336 : orderAtOK 336 cert0335 cert0336 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0336 : OriginalPair 336 :=
  original_of_certificates (by decide) row0335 row0336 order0336

theorem order0337 : orderAtOK 337 cert0336 cert0337 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0337 : OriginalPair 337 :=
  original_of_certificates (by decide) row0336 row0337 order0337

theorem order0338 : orderAtOK 338 cert0337 cert0338 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0338 : OriginalPair 338 :=
  original_of_certificates (by decide) row0337 row0338 order0338

theorem order0339 : orderAtOK 339 cert0338 cert0339 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0339 : OriginalPair 339 :=
  original_of_certificates (by decide) row0338 row0339 order0339

theorem range0336_0339 {n : ℕ} (lo : 336 ≤ n) (hi : n ≤ 339) : OriginalPair n := by
  interval_cases n
  · exact pair0336
  · exact pair0337
  · exact pair0338
  · exact pair0339

#print axioms range0336_0339

end LongCycleFinite.K4.Data
