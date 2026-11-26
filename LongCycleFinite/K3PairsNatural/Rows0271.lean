import LongCycleFinite.K3SignedNatural.Rows0271
import LongCycleFinite.K3SignedNatural.Rows0267

namespace LongCycleFinite.K3.DataExplicit

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0268 :
    orderAtOK 268 cert0267 cert0268 = true := by decide +kernel

theorem pair0268 : OriginalPair 268 :=
  original_of_certificates (by decide) row0267 row0268 order0268

theorem order0269 :
    orderAtOK 269 cert0268 cert0269 = true := by decide +kernel

theorem pair0269 : OriginalPair 269 :=
  original_of_certificates (by decide) row0268 row0269 order0269

theorem order0270 :
    orderAtOK 270 cert0269 cert0270 = true := by decide +kernel

theorem pair0270 : OriginalPair 270 :=
  original_of_certificates (by decide) row0269 row0270 order0270

theorem order0271 :
    orderAtOK 271 cert0270 cert0271 = true := by decide +kernel

theorem pair0271 : OriginalPair 271 :=
  original_of_certificates (by decide) row0270 row0271 order0271

theorem range0268_0271 {n : ℕ} (lo : 268 ≤ n) (hi : n ≤ 271) : OriginalPair n := by
  interval_cases n
  · exact pair0268
  · exact pair0269
  · exact pair0270
  · exact pair0271

#print axioms range0268_0271

end LongCycleFinite.K3.DataExplicit
