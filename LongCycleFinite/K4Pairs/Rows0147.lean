import LongCycleFinite.K4Signed.Rows0147
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0143

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0144 : orderAtOK 144 cert0143 cert0144 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0144 : OriginalPair 144 :=
  original_of_certificates (by decide) row0143 row0144 order0144

theorem order0145 : orderAtOK 145 cert0144 cert0145 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0145 : OriginalPair 145 :=
  original_of_certificates (by decide) row0144 row0145 order0145

theorem order0146 : orderAtOK 146 cert0145 cert0146 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0146 : OriginalPair 146 :=
  original_of_certificates (by decide) row0145 row0146 order0146

theorem order0147 : orderAtOK 147 cert0146 cert0147 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0147 : OriginalPair 147 :=
  original_of_certificates (by decide) row0146 row0147 order0147

theorem range0144_0147 {n : ℕ} (lo : 144 ≤ n) (hi : n ≤ 147) : OriginalPair n := by
  interval_cases n
  · exact pair0144
  · exact pair0145
  · exact pair0146
  · exact pair0147

#print axioms range0144_0147

end LongCycleFinite.K4.Data
