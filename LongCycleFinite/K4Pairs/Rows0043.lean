import LongCycleFinite.K4Signed.Rows0043
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0039

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0040 : orderAtOK 40 cert0039 cert0040 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0040 : OriginalPair 40 :=
  original_of_certificates (by decide) row0039 row0040 order0040

theorem order0041 : orderAtOK 41 cert0040 cert0041 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0041 : OriginalPair 41 :=
  original_of_certificates (by decide) row0040 row0041 order0041

theorem order0042 : orderAtOK 42 cert0041 cert0042 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0042 : OriginalPair 42 :=
  original_of_certificates (by decide) row0041 row0042 order0042

theorem order0043 : orderAtOK 43 cert0042 cert0043 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0043 : OriginalPair 43 :=
  original_of_certificates (by decide) row0042 row0043 order0043

theorem range0040_0043 {n : ℕ} (lo : 40 ≤ n) (hi : n ≤ 43) : OriginalPair n := by
  interval_cases n
  · exact pair0040
  · exact pair0041
  · exact pair0042
  · exact pair0043

#print axioms range0040_0043

end LongCycleFinite.K4.Data
