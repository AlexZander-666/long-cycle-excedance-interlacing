import LongCycleFinite.K4Signed.Rows0023
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0019

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0020 : orderAtOK 20 cert0019 cert0020 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0020 : OriginalPair 20 :=
  original_of_certificates (by decide) row0019 row0020 order0020

theorem order0021 : orderAtOK 21 cert0020 cert0021 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0021 : OriginalPair 21 :=
  original_of_certificates (by decide) row0020 row0021 order0021

theorem order0022 : orderAtOK 22 cert0021 cert0022 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0022 : OriginalPair 22 :=
  original_of_certificates (by decide) row0021 row0022 order0022

theorem order0023 : orderAtOK 23 cert0022 cert0023 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0023 : OriginalPair 23 :=
  original_of_certificates (by decide) row0022 row0023 order0023

theorem range0020_0023 {n : ℕ} (lo : 20 ≤ n) (hi : n ≤ 23) : OriginalPair n := by
  interval_cases n
  · exact pair0020
  · exact pair0021
  · exact pair0022
  · exact pair0023

#print axioms range0020_0023

end LongCycleFinite.K4.Data
