import LongCycleFinite.K4Signed.Rows0067
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0063

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0064 : orderAtOK 64 cert0063 cert0064 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0064 : OriginalPair 64 :=
  original_of_certificates (by decide) row0063 row0064 order0064

theorem order0065 : orderAtOK 65 cert0064 cert0065 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0065 : OriginalPair 65 :=
  original_of_certificates (by decide) row0064 row0065 order0065

theorem order0066 : orderAtOK 66 cert0065 cert0066 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0066 : OriginalPair 66 :=
  original_of_certificates (by decide) row0065 row0066 order0066

theorem order0067 : orderAtOK 67 cert0066 cert0067 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0067 : OriginalPair 67 :=
  original_of_certificates (by decide) row0066 row0067 order0067

theorem range0064_0067 {n : ℕ} (lo : 64 ≤ n) (hi : n ≤ 67) : OriginalPair n := by
  interval_cases n
  · exact pair0064
  · exact pair0065
  · exact pair0066
  · exact pair0067

#print axioms range0064_0067

end LongCycleFinite.K4.Data
