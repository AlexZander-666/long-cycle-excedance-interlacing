import LongCycleFinite.K3SignedNatural.Rows0287
import LongCycleFinite.K3SignedNatural.Rows0283

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0284 :
    orderAtOK 284 cert0283 cert0284 = true := by decide +kernel

theorem pair0284 : OriginalPair 284 :=
  original_of_certificates (by decide) row0283 row0284 order0284

theorem order0285 :
    orderAtOK 285 cert0284 cert0285 = true := by decide +kernel

theorem pair0285 : OriginalPair 285 :=
  original_of_certificates (by decide) row0284 row0285 order0285

theorem order0286 :
    orderAtOK 286 cert0285 cert0286 = true := by decide +kernel

theorem pair0286 : OriginalPair 286 :=
  original_of_certificates (by decide) row0285 row0286 order0286

theorem order0287 :
    orderAtOK 287 cert0286 cert0287 = true := by decide +kernel

theorem pair0287 : OriginalPair 287 :=
  original_of_certificates (by decide) row0286 row0287 order0287

theorem range0284_0287 {n : ℕ} (lo : 284 ≤ n) (hi : n ≤ 287) : OriginalPair n := by
  interval_cases n
  · exact pair0284
  · exact pair0285
  · exact pair0286
  · exact pair0287

#print axioms range0284_0287

end LongCycleFinite.K3.DataExplicit
