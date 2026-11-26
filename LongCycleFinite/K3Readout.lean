import LongCycleFinite.K3Rows
import LongCycleFinite.K3Brackets
import LongCycleBounds.GeneralCycleQuotient

/-! Checked gamma intervals give interlacing for the original permutation rows. -/

namespace LongCycleFinite.K3

open LongCycles LongCycleBounds.Band Polynomial

structure RowCertificate where
  outer : Dyadic
  brackets : List Window

def rowAtOK (n : ℕ) (cert : RowCertificate) : Bool :=
  rowOK ((n-2)/2) (gammaRow n) cert.outer cert.brackets

def orderAtOK (n : ℕ) (old new : RowCertificate) : Bool :=
  if n % 2 = 0 then extraOrder old.brackets new.brackets
  else equalOrder old.brackets new.brackets

noncomputable section

/-- The adjacent rows ending at `n` have strictly interlacing quotients
and weakly interlacing original permutation enumerators. -/
def OriginalPair (n : ℕ) : Prop :=
  StrictNegativeInterlacing (generalCycleQuotient (n-1) 3) (generalCycleQuotient n 3) (n-3) ∧
    WeakRealInterlacing (enumerator (n-1) 3) (enumerator n 3)

theorem original_of_certificates {n : ℕ} (hn : 4 ≤ n) {old new : RowCertificate}
    (hp : rowAtOK (n-1) old = true) (hq : rowAtOK n new = true)
    (ho : orderAtOK n old new = true) : OriginalPair n := by
  have prev := gammaRow_original (n := n-1) (by omega)
  have next := gammaRow_original (n := n) (by omega)
  let d := (n-3)/2
  have hp' : rowOK d (gammaRow (n-1)) old.outer old.brackets = true := by
    simpa only [rowAtOK, show n-1-2=n-3 by omega] using hp
  have s : StrictNegativeInterlacing
      (expandGamma (n-3) (gammaRow (n-1))) (expandGamma (n-2) (gammaRow n)) (n-3) := by
    by_cases parity : n % 2 = 0
    · have hq' : rowOK (d+1) (gammaRow n) new.outer new.brackets = true := by
        simpa only [rowAtOK, show (n-2)/2=d+1 by dsimp [d]; omega] using hq
      have ho' : extraOrder old.brackets new.brackets = true := by
        simpa only [orderAtOK, if_pos parity] using ho
      simpa only [show d+d+1=n-3 by dsimp [d]; omega,
        show n-3+1=n-2 by omega] using checked_even hp' hq' ho'
    · have hq' : rowOK d (gammaRow n) new.outer new.brackets = true := by
        simpa only [rowAtOK, show (n-2)/2=d by dsimp [d]; omega] using hq
      have ho' : equalOrder old.brackets new.brackets = true := by
        simpa only [orderAtOK, if_neg parity] using ho
      simpa only [show d+d=n-3 by dsimp [d]; omega,
        show n-3+1=n-2 by omega] using checked_odd hp' hq' ho'
  have hprev : generalCycleQuotient (n-1) 3 = expandGamma (n-3) (gammaRow (n-1)) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
    rw [← actual_general_cycle_row (by decide : 2 ≤ 3) (by omega : 0 < n-1), prev,
      show n-1-2=n-3 by omega]
  have hnext : generalCycleQuotient n 3 = expandGamma (n-2) (gammaRow n) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
    rw [← actual_general_cycle_row (by decide : 2 ≤ 3) (by omega : 0 < n), next]
  constructor
  · rwa [hprev, hnext]
  · rw [prev, next, show n-1-2=n-3 by omega]
    exact weak_mul_X_of_strict s

#print axioms locatedRoots_of_rowOK
#print axioms checked_even
#print axioms checked_odd
#print axioms original_of_certificates

end

end LongCycleFinite.K3
