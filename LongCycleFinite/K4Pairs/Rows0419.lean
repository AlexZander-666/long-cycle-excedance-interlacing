import LongCycleFinite.K4Signed.Rows0419
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0415

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0416 : orderAtOK 416 cert0415 cert0416 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0416 : OriginalPair 416 :=
  original_of_certificates (by decide) row0415 row0416 order0416

theorem order0417 : orderAtOK 417 cert0416 cert0417 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0417 : OriginalPair 417 :=
  original_of_certificates (by decide) row0416 row0417 order0417

theorem order0418 : orderAtOK 418 cert0417 cert0418 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0418 : OriginalPair 418 :=
  original_of_certificates (by decide) row0417 row0418 order0418

theorem order0419 : orderAtOK 419 cert0418 cert0419 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0419 : OriginalPair 419 :=
  original_of_certificates (by decide) row0418 row0419 order0419

theorem range0416_0419 {n : ℕ} (lo : 416 ≤ n) (hi : n ≤ 419) : OriginalPair n := by
  interval_cases n
  · exact pair0416
  · exact pair0417
  · exact pair0418
  · exact pair0419

#print axioms range0416_0419

end LongCycleFinite.K4.Data
