import LongCycleFinite.K4Signed.Rows0403
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0399

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0400 : orderAtOK 400 cert0399 cert0400 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0400 : OriginalPair 400 :=
  original_of_certificates (by decide) row0399 row0400 order0400

theorem order0401 : orderAtOK 401 cert0400 cert0401 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0401 : OriginalPair 401 :=
  original_of_certificates (by decide) row0400 row0401 order0401

theorem order0402 : orderAtOK 402 cert0401 cert0402 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0402 : OriginalPair 402 :=
  original_of_certificates (by decide) row0401 row0402 order0402

theorem order0403 : orderAtOK 403 cert0402 cert0403 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0403 : OriginalPair 403 :=
  original_of_certificates (by decide) row0402 row0403 order0403

theorem range0400_0403 {n : ℕ} (lo : 400 ≤ n) (hi : n ≤ 403) : OriginalPair n := by
  interval_cases n
  · exact pair0400
  · exact pair0401
  · exact pair0402
  · exact pair0403

#print axioms range0400_0403

end LongCycleFinite.K4.Data
