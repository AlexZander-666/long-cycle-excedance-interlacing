import LongCycleFinite.K4Signed.Rows0031
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0027

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0028 : orderAtOK 28 cert0027 cert0028 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0028 : OriginalPair 28 :=
  original_of_certificates (by decide) row0027 row0028 order0028

theorem order0029 : orderAtOK 29 cert0028 cert0029 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0029 : OriginalPair 29 :=
  original_of_certificates (by decide) row0028 row0029 order0029

theorem order0030 : orderAtOK 30 cert0029 cert0030 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0030 : OriginalPair 30 :=
  original_of_certificates (by decide) row0029 row0030 order0030

theorem order0031 : orderAtOK 31 cert0030 cert0031 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0031 : OriginalPair 31 :=
  original_of_certificates (by decide) row0030 row0031 order0031

theorem range0028_0031 {n : ℕ} (lo : 28 ≤ n) (hi : n ≤ 31) : OriginalPair n := by
  interval_cases n
  · exact pair0028
  · exact pair0029
  · exact pair0030
  · exact pair0031

#print axioms range0028_0031

end LongCycleFinite.K4.Data
