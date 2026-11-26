import LongCycleFinite.K4Signed.Rows0027
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0023

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0024 : orderAtOK 24 cert0023 cert0024 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0024 : OriginalPair 24 :=
  original_of_certificates (by decide) row0023 row0024 order0024

theorem order0025 : orderAtOK 25 cert0024 cert0025 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0025 : OriginalPair 25 :=
  original_of_certificates (by decide) row0024 row0025 order0025

theorem order0026 : orderAtOK 26 cert0025 cert0026 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0026 : OriginalPair 26 :=
  original_of_certificates (by decide) row0025 row0026 order0026

theorem order0027 : orderAtOK 27 cert0026 cert0027 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0027 : OriginalPair 27 :=
  original_of_certificates (by decide) row0026 row0027 order0027

theorem range0024_0027 {n : ℕ} (lo : 24 ≤ n) (hi : n ≤ 27) : OriginalPair n := by
  interval_cases n
  · exact pair0024
  · exact pair0025
  · exact pair0026
  · exact pair0027

#print axioms range0024_0027

end LongCycleFinite.K4.Data
