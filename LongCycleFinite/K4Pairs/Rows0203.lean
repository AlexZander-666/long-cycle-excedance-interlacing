import LongCycleFinite.K4Signed.Rows0203
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0199

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0200 : orderAtOK 200 cert0199 cert0200 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0200 : OriginalPair 200 :=
  original_of_certificates (by decide) row0199 row0200 order0200

theorem order0201 : orderAtOK 201 cert0200 cert0201 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0201 : OriginalPair 201 :=
  original_of_certificates (by decide) row0200 row0201 order0201

theorem order0202 : orderAtOK 202 cert0201 cert0202 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0202 : OriginalPair 202 :=
  original_of_certificates (by decide) row0201 row0202 order0202

theorem order0203 : orderAtOK 203 cert0202 cert0203 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0203 : OriginalPair 203 :=
  original_of_certificates (by decide) row0202 row0203 order0203

theorem range0200_0203 {n : ℕ} (lo : 200 ≤ n) (hi : n ≤ 203) : OriginalPair n := by
  interval_cases n
  · exact pair0200
  · exact pair0201
  · exact pair0202
  · exact pair0203

#print axioms range0200_0203

end LongCycleFinite.K4.Data
