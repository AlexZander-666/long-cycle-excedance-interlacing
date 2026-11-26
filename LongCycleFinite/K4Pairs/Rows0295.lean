import LongCycleFinite.K4Signed.Rows0295
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0291

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0292 : orderAtOK 292 cert0291 cert0292 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0292 : OriginalPair 292 :=
  original_of_certificates (by decide) row0291 row0292 order0292

theorem order0293 : orderAtOK 293 cert0292 cert0293 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0293 : OriginalPair 293 :=
  original_of_certificates (by decide) row0292 row0293 order0293

theorem order0294 : orderAtOK 294 cert0293 cert0294 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0294 : OriginalPair 294 :=
  original_of_certificates (by decide) row0293 row0294 order0294

theorem order0295 : orderAtOK 295 cert0294 cert0295 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0295 : OriginalPair 295 :=
  original_of_certificates (by decide) row0294 row0295 order0295

theorem range0292_0295 {n : ℕ} (lo : 292 ≤ n) (hi : n ≤ 295) : OriginalPair n := by
  interval_cases n
  · exact pair0292
  · exact pair0293
  · exact pair0294
  · exact pair0295

#print axioms range0292_0295

end LongCycleFinite.K4.Data
