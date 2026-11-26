import LongCycleFinite.K3SignedNatural.Rows0303
import LongCycleFinite.K3SignedNatural.Rows0299

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0300 :
    orderAtOK 300 cert0299 cert0300 = true := by decide +kernel

theorem pair0300 : OriginalPair 300 :=
  original_of_certificates (by decide) row0299 row0300 order0300

theorem order0301 :
    orderAtOK 301 cert0300 cert0301 = true := by decide +kernel

theorem pair0301 : OriginalPair 301 :=
  original_of_certificates (by decide) row0300 row0301 order0301

theorem order0302 :
    orderAtOK 302 cert0301 cert0302 = true := by decide +kernel

theorem pair0302 : OriginalPair 302 :=
  original_of_certificates (by decide) row0301 row0302 order0302

theorem order0303 :
    orderAtOK 303 cert0302 cert0303 = true := by decide +kernel

theorem pair0303 : OriginalPair 303 :=
  original_of_certificates (by decide) row0302 row0303 order0303

theorem range0300_0303 {n : ℕ} (lo : 300 ≤ n) (hi : n ≤ 303) : OriginalPair n := by
  interval_cases n
  · exact pair0300
  · exact pair0301
  · exact pair0302
  · exact pair0303

#print axioms range0300_0303

end LongCycleFinite.K3.DataExplicit
