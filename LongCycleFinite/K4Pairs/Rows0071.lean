import LongCycleFinite.K4Signed.Rows0071
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0067

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0068 : orderAtOK 68 cert0067 cert0068 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0068 : OriginalPair 68 :=
  original_of_certificates (by decide) row0067 row0068 order0068

theorem order0069 : orderAtOK 69 cert0068 cert0069 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0069 : OriginalPair 69 :=
  original_of_certificates (by decide) row0068 row0069 order0069

theorem order0070 : orderAtOK 70 cert0069 cert0070 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0070 : OriginalPair 70 :=
  original_of_certificates (by decide) row0069 row0070 order0070

theorem order0071 : orderAtOK 71 cert0070 cert0071 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0071 : OriginalPair 71 :=
  original_of_certificates (by decide) row0070 row0071 order0071

theorem range0068_0071 {n : ℕ} (lo : 68 ≤ n) (hi : n ≤ 71) : OriginalPair n := by
  interval_cases n
  · exact pair0068
  · exact pair0069
  · exact pair0070
  · exact pair0071

#print axioms range0068_0071

end LongCycleFinite.K4.Data
