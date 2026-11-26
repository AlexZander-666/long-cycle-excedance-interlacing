import LongCycleFinite.K3SignedNatural.Rows0299
import LongCycleFinite.K3SignedNatural.Rows0295

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0296 :
    orderAtOK 296 cert0295 cert0296 = true := by decide +kernel

theorem pair0296 : OriginalPair 296 :=
  original_of_certificates (by decide) row0295 row0296 order0296

theorem order0297 :
    orderAtOK 297 cert0296 cert0297 = true := by decide +kernel

theorem pair0297 : OriginalPair 297 :=
  original_of_certificates (by decide) row0296 row0297 order0297

theorem order0298 :
    orderAtOK 298 cert0297 cert0298 = true := by decide +kernel

theorem pair0298 : OriginalPair 298 :=
  original_of_certificates (by decide) row0297 row0298 order0298

theorem order0299 :
    orderAtOK 299 cert0298 cert0299 = true := by decide +kernel

theorem pair0299 : OriginalPair 299 :=
  original_of_certificates (by decide) row0298 row0299 order0299

theorem range0296_0299 {n : ℕ} (lo : 296 ≤ n) (hi : n ≤ 299) : OriginalPair n := by
  interval_cases n
  · exact pair0296
  · exact pair0297
  · exact pair0298
  · exact pair0299

#print axioms range0296_0299

end LongCycleFinite.K3.DataExplicit
