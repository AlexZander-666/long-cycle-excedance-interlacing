import LongCycleFinite.K4Signed.Rows0463
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0459

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0460 : orderAtOK 460 cert0459 cert0460 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0460 : OriginalPair 460 :=
  original_of_certificates (by decide) row0459 row0460 order0460

theorem order0461 : orderAtOK 461 cert0460 cert0461 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0461 : OriginalPair 461 :=
  original_of_certificates (by decide) row0460 row0461 order0461

theorem order0462 : orderAtOK 462 cert0461 cert0462 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0462 : OriginalPair 462 :=
  original_of_certificates (by decide) row0461 row0462 order0462

theorem order0463 : orderAtOK 463 cert0462 cert0463 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0463 : OriginalPair 463 :=
  original_of_certificates (by decide) row0462 row0463 order0463

theorem range0460_0463 {n : ℕ} (lo : 460 ≤ n) (hi : n ≤ 463) : OriginalPair n := by
  interval_cases n
  · exact pair0460
  · exact pair0461
  · exact pair0462
  · exact pair0463

#print axioms range0460_0463

end LongCycleFinite.K4.Data
