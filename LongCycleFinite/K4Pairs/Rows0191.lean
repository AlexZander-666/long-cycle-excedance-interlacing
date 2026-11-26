import LongCycleFinite.K4Signed.Rows0191
import LongCycleFinite.K3AdjacentOrder
import LongCycleFinite.K4Signed.Rows0187

namespace LongCycleFinite.K4.Data

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem order0188 : orderAtOK 188 cert0187 cert0188 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0188 : OriginalPair 188 :=
  original_of_certificates (by decide) row0187 row0188 order0188

theorem order0189 : orderAtOK 189 cert0188 cert0189 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0189 : OriginalPair 189 :=
  original_of_certificates (by decide) row0188 row0189 order0189

theorem order0190 : orderAtOK 190 cert0189 cert0190 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0190 : OriginalPair 190 :=
  original_of_certificates (by decide) row0189 row0190 order0190

theorem order0191 : orderAtOK 191 cert0190 cert0191 = true :=
  K3.orderAtOK_of_linear (by decide +kernel)

theorem pair0191 : OriginalPair 191 :=
  original_of_certificates (by decide) row0190 row0191 order0191

theorem range0188_0191 {n : ℕ} (lo : 188 ≤ n) (hi : n ≤ 191) : OriginalPair n := by
  interval_cases n
  · exact pair0188
  · exact pair0189
  · exact pair0190
  · exact pair0191

#print axioms range0188_0191

end LongCycleFinite.K4.Data
