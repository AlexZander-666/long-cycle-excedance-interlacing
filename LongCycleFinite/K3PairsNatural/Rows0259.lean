import LongCycleFinite.K3SignedNatural.Rows0259

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0256 :
    orderAtOK 256 cert0255 cert0256 = true := by decide +kernel

theorem pair0256 : OriginalPair 256 :=
  original_of_certificates (by decide) row0255 row0256 order0256

theorem order0257 :
    orderAtOK 257 cert0256 cert0257 = true := by decide +kernel

theorem pair0257 : OriginalPair 257 :=
  original_of_certificates (by decide) row0256 row0257 order0257

theorem order0258 :
    orderAtOK 258 cert0257 cert0258 = true := by decide +kernel

theorem pair0258 : OriginalPair 258 :=
  original_of_certificates (by decide) row0257 row0258 order0258

theorem order0259 :
    orderAtOK 259 cert0258 cert0259 = true := by decide +kernel

theorem pair0259 : OriginalPair 259 :=
  original_of_certificates (by decide) row0258 row0259 order0259

theorem range0256_0259 {n : ℕ} (lo : 256 ≤ n) (hi : n ≤ 259) : OriginalPair n := by
  interval_cases n
  · exact pair0256
  · exact pair0257
  · exact pair0258
  · exact pair0259

#print axioms range0256_0259

end LongCycleFinite.K3.DataExplicit
