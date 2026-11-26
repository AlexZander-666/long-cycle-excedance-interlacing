import LongCycleFinite.K3SignedNatural.Rows0263
import LongCycleFinite.K3SignedNatural.Rows0259

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0260 :
    orderAtOK 260 cert0259 cert0260 = true := by decide +kernel

theorem pair0260 : OriginalPair 260 :=
  original_of_certificates (by decide) row0259 row0260 order0260

theorem order0261 :
    orderAtOK 261 cert0260 cert0261 = true := by decide +kernel

theorem pair0261 : OriginalPair 261 :=
  original_of_certificates (by decide) row0260 row0261 order0261

theorem order0262 :
    orderAtOK 262 cert0261 cert0262 = true := by decide +kernel

theorem pair0262 : OriginalPair 262 :=
  original_of_certificates (by decide) row0261 row0262 order0262

theorem order0263 :
    orderAtOK 263 cert0262 cert0263 = true := by decide +kernel

theorem pair0263 : OriginalPair 263 :=
  original_of_certificates (by decide) row0262 row0263 order0263

theorem range0260_0263 {n : ℕ} (lo : 260 ≤ n) (hi : n ≤ 263) : OriginalPair n := by
  interval_cases n
  · exact pair0260
  · exact pair0261
  · exact pair0262
  · exact pair0263

#print axioms range0260_0263

end LongCycleFinite.K3.DataExplicit
