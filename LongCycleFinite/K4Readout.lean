import LongCycleFinite.K4Rows
import LongCycleFinite.K3Readout

namespace LongCycleFinite
open LongCycles LongCycleBounds.Band Polynomial

/-- A checked pair of gamma rows gives strict quotient interlacing for any cutoff. -/
theorem original_pair_of_gamma_checks {n k : ℕ} (hk : 2 ≤ k) (hn : 4 ≤ n)
    {a b : List ℤ} {old new : K3.RowCertificate}
    (prev : enumerator (n-1) k = X * expandGamma (n-1-2) a)
    (next : enumerator n k = X * expandGamma (n-2) b)
    (hp : K3.rowOK ((n-1-2)/2) a old.outer old.brackets = true)
    (hq : K3.rowOK ((n-2)/2) b new.outer new.brackets = true)
    (ho : K3.orderAtOK n old new = true) :
    StrictNegativeInterlacing (generalCycleQuotient (n-1) k) (generalCycleQuotient n k) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  let d := (n-3)/2
  have hp' : K3.rowOK d a old.outer old.brackets = true := by
    simpa only [show n-1-2=n-3 by omega] using hp
  have s : StrictNegativeInterlacing
      (expandGamma (n-3) a) (expandGamma (n-2) b) (n-3) := by
    by_cases parity : n % 2 = 0
    · have hq' : K3.rowOK (d+1) b new.outer new.brackets = true := by
        simpa only [show (n-2)/2=d+1 by dsimp [d]; omega] using hq
      have ho' : K3.extraOrder old.brackets new.brackets = true := by
        simpa only [K3.orderAtOK, if_pos parity] using ho
      simpa only [show d+d+1=n-3 by dsimp [d]; omega,
        show n-3+1=n-2 by omega] using K3.checked_even hp' hq' ho'
    · have hq' : K3.rowOK d b new.outer new.brackets = true := by
        simpa only [show (n-2)/2=d by dsimp [d]; omega] using hq
      have ho' : K3.equalOrder old.brackets new.brackets = true := by
        simpa only [K3.orderAtOK, if_neg parity] using ho
      simpa only [show d+d=n-3 by dsimp [d]; omega,
        show n-3+1=n-2 by omega] using K3.checked_odd hp' hq' ho'
  have hprev : generalCycleQuotient (n-1) k = expandGamma (n-3) a := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
    rw [← actual_general_cycle_row hk (by omega : 0 < n-1), prev,
      show n-1-2=n-3 by omega]
  have hnext : generalCycleQuotient n k = expandGamma (n-2) b := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
    rw [← actual_general_cycle_row hk (by omega : 0 < n), next]
  constructor
  · rwa [hprev, hnext]
  · rw [prev, next, show n-1-2=n-3 by omega]
    exact weak_mul_X_of_strict s


namespace K4

abbrev RowCertificate := K3.RowCertificate
abbrev orderAtOK := K3.orderAtOK

def rowAtOK (n : ℕ) (cert : RowCertificate) : Bool :=
  K3.rowOK ((n-2)/2) (gammaRow n) cert.outer cert.brackets

def OriginalPair (n : ℕ) : Prop :=
  StrictNegativeInterlacing (generalCycleQuotient (n-1) 4) (generalCycleQuotient n 4) (n-3) ∧
    WeakRealInterlacing (enumerator (n-1) 4) (enumerator n 4)

theorem original_of_certificates {n : ℕ} (hn : 5 ≤ n) {old new : RowCertificate}
    (hp : rowAtOK (n-1) old = true) (hq : rowAtOK n new = true)
    (ho : orderAtOK n old new = true) : OriginalPair n :=
  original_pair_of_gamma_checks (by decide : 2 ≤ 4) (by omega)
    (gammaRow_original (by omega)) (gammaRow_original (by omega)) hp hq ho

#print axioms original_of_certificates

end K4
end LongCycleFinite
