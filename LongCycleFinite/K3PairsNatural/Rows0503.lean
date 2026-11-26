import LongCycleFinite.K3SignedNatural.Rows0503
import LongCycleFinite.K3SignedNatural.Rows0499
import LongCycleFinite.K3AdjacentOrder

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0500 :
    orderAtOK 500 cert0499 cert0500 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0500 : OriginalPair 500 :=
  original_of_certificates (by decide) row0499 row0500 order0500

theorem order0501 :
    orderAtOK 501 cert0500 cert0501 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0501 : OriginalPair 501 :=
  original_of_certificates (by decide) row0500 row0501 order0501

theorem order0502 :
    orderAtOK 502 cert0501 cert0502 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0502 : OriginalPair 502 :=
  original_of_certificates (by decide) row0501 row0502 order0502

theorem order0503 :
    orderAtOK 503 cert0502 cert0503 = true := orderAtOK_of_linear (by decide +kernel)

theorem pair0503 : OriginalPair 503 :=
  original_of_certificates (by decide) row0502 row0503 order0503

theorem range0500_0503 {n : ℕ} (lo : 500 ≤ n) (hi : n ≤ 503) : OriginalPair n := by
  interval_cases n
  · exact pair0500
  · exact pair0501
  · exact pair0502
  · exact pair0503

#print axioms range0500_0503

end LongCycleFinite.K3.DataExplicit
