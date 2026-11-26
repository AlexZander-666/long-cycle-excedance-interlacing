import LongCycleFinite.K3SignedNatural.Rows0291
import LongCycleFinite.K3SignedNatural.Rows0287

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0288 :
    orderAtOK 288 cert0287 cert0288 = true := by decide +kernel

theorem pair0288 : OriginalPair 288 :=
  original_of_certificates (by decide) row0287 row0288 order0288

theorem order0289 :
    orderAtOK 289 cert0288 cert0289 = true := by decide +kernel

theorem pair0289 : OriginalPair 289 :=
  original_of_certificates (by decide) row0288 row0289 order0289

theorem order0290 :
    orderAtOK 290 cert0289 cert0290 = true := by decide +kernel

theorem pair0290 : OriginalPair 290 :=
  original_of_certificates (by decide) row0289 row0290 order0290

theorem order0291 :
    orderAtOK 291 cert0290 cert0291 = true := by decide +kernel

theorem pair0291 : OriginalPair 291 :=
  original_of_certificates (by decide) row0290 row0291 order0291

theorem range0288_0291 {n : ℕ} (lo : 288 ≤ n) (hi : n ≤ 291) : OriginalPair n := by
  interval_cases n
  · exact pair0288
  · exact pair0289
  · exact pair0290
  · exact pair0291

#print axioms range0288_0291

end LongCycleFinite.K3.DataExplicit
