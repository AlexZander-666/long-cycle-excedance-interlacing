import LongCycleFinite.K4Signed.Rows0035
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0031

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0032 : orderAtOK 32 cert0031 cert0032 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0032 : OriginalPair 32 :=
  original_of_certificates (by decide) row0031 row0032 order0032

theorem order0033 : orderAtOK 33 cert0032 cert0033 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0033 : OriginalPair 33 :=
  original_of_certificates (by decide) row0032 row0033 order0033

theorem order0034 : orderAtOK 34 cert0033 cert0034 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0034 : OriginalPair 34 :=
  original_of_certificates (by decide) row0033 row0034 order0034

theorem order0035 : orderAtOK 35 cert0034 cert0035 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0035 : OriginalPair 35 :=
  original_of_certificates (by decide) row0034 row0035 order0035

theorem range0032_0035 {n : ℕ} (lo : 32 ≤ n) (hi : n ≤ 35) : OriginalPair n := by
  interval_cases n
  · exact pair0032
  · exact pair0033
  · exact pair0034
  · exact pair0035

#print axioms range0032_0035

end LongCycleFinite.K4.Data
