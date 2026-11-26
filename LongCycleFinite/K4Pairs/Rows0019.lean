import LongCycleFinite.K4Signed.Rows0019
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0016 : orderAtOK 16 cert0015 cert0016 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0016 : OriginalPair 16 :=
  original_of_certificates (by decide) row0015 row0016 order0016

theorem order0017 : orderAtOK 17 cert0016 cert0017 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0017 : OriginalPair 17 :=
  original_of_certificates (by decide) row0016 row0017 order0017

theorem order0018 : orderAtOK 18 cert0017 cert0018 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0018 : OriginalPair 18 :=
  original_of_certificates (by decide) row0017 row0018 order0018

theorem order0019 : orderAtOK 19 cert0018 cert0019 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0019 : OriginalPair 19 :=
  original_of_certificates (by decide) row0018 row0019 order0019

theorem range0016_0019 {n : ℕ} (lo : 16 ≤ n) (hi : n ≤ 19) : OriginalPair n := by
  interval_cases n
  · exact pair0016
  · exact pair0017
  · exact pair0018
  · exact pair0019

#print axioms range0016_0019

end LongCycleFinite.K4.Data
