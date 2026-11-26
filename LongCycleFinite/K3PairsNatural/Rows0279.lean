import LongCycleFinite.K3SignedNatural.Rows0279
import LongCycleFinite.K3SignedNatural.Rows0275

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0276 :
    orderAtOK 276 cert0275 cert0276 = true := by decide +kernel

theorem pair0276 : OriginalPair 276 :=
  original_of_certificates (by decide) row0275 row0276 order0276

theorem order0277 :
    orderAtOK 277 cert0276 cert0277 = true := by decide +kernel

theorem pair0277 : OriginalPair 277 :=
  original_of_certificates (by decide) row0276 row0277 order0277

theorem order0278 :
    orderAtOK 278 cert0277 cert0278 = true := by decide +kernel

theorem pair0278 : OriginalPair 278 :=
  original_of_certificates (by decide) row0277 row0278 order0278

theorem order0279 :
    orderAtOK 279 cert0278 cert0279 = true := by decide +kernel

theorem pair0279 : OriginalPair 279 :=
  original_of_certificates (by decide) row0278 row0279 order0279

theorem range0276_0279 {n : ℕ} (lo : 276 ≤ n) (hi : n ≤ 279) : OriginalPair n := by
  interval_cases n
  · exact pair0276
  · exact pair0277
  · exact pair0278
  · exact pair0279

#print axioms range0276_0279

end LongCycleFinite.K3.DataExplicit
