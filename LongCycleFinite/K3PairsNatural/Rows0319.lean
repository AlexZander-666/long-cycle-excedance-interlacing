import LongCycleFinite.K3SignedNatural.Rows0319
import LongCycleFinite.K3SignedNatural.Rows0315

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0316 :
    orderAtOK 316 cert0315 cert0316 = true := by decide +kernel

theorem pair0316 : OriginalPair 316 :=
  original_of_certificates (by decide) row0315 row0316 order0316

theorem order0317 :
    orderAtOK 317 cert0316 cert0317 = true := by decide +kernel

theorem pair0317 : OriginalPair 317 :=
  original_of_certificates (by decide) row0316 row0317 order0317

theorem order0318 :
    orderAtOK 318 cert0317 cert0318 = true := by decide +kernel

theorem pair0318 : OriginalPair 318 :=
  original_of_certificates (by decide) row0317 row0318 order0318

theorem order0319 :
    orderAtOK 319 cert0318 cert0319 = true := by decide +kernel

theorem pair0319 : OriginalPair 319 :=
  original_of_certificates (by decide) row0318 row0319 order0319

theorem range0316_0319 {n : ℕ} (lo : 316 ≤ n) (hi : n ≤ 319) : OriginalPair n := by
  interval_cases n
  · exact pair0316
  · exact pair0317
  · exact pair0318
  · exact pair0319

#print axioms range0316_0319

end LongCycleFinite.K3.DataExplicit
