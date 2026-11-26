import LongCycleFinite.K4Signed.Rows0395
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0391

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0392 : orderAtOK 392 cert0391 cert0392 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0392 : OriginalPair 392 :=
  original_of_certificates (by decide) row0391 row0392 order0392

theorem order0393 : orderAtOK 393 cert0392 cert0393 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0393 : OriginalPair 393 :=
  original_of_certificates (by decide) row0392 row0393 order0393

theorem order0394 : orderAtOK 394 cert0393 cert0394 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0394 : OriginalPair 394 :=
  original_of_certificates (by decide) row0393 row0394 order0394

theorem order0395 : orderAtOK 395 cert0394 cert0395 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0395 : OriginalPair 395 :=
  original_of_certificates (by decide) row0394 row0395 order0395

theorem range0392_0395 {n : ℕ} (lo : 392 ≤ n) (hi : n ≤ 395) : OriginalPair n := by
  interval_cases n
  · exact pair0392
  · exact pair0393
  · exact pair0394
  · exact pair0395

#print axioms range0392_0395

end LongCycleFinite.K4.Data
