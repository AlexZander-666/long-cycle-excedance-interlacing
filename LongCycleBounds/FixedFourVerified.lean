import LongCycleBounds.FixedFourCompact
import LongCycleBounds.FixedFourMiddle
import LongCycleBounds.FixedFourExterior
import LongCycleBounds.CycleProfileIndependentReadout

/-! Explicit upper-index cutoff for independent two- and three-cycle weights. -/

namespace LongCycleBounds.FixedFour
open Real LongCycles LongCycleFinite FixedCutoff PoleBridge CycleProfile

/-- The sign on the entire x half-axis, including x=0, for a zero of the
genuine lower permutation row. The sign is uniform on the closed weight square. -/
theorem normalized_sign {p : ℕ} (hp : 511 ≤ p) (w : ℕ → ℝ)
    (one : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (tail : ∀ a ≥ 4, w a = 1) {x : ℝ} (hx : 0 ≤ x)
    (zero : normalizedRow w p x = 0) :
    0 < normalizedRow w (p+1) x * (-deriv (normalizedRow w p) x) := by
  by_cases inside : x ≤ 3 * sqrt (p : ℝ)
  · have gap : ScaledGapAt w 4 p x := by
      by_cases compact : x ≤ 16
      · exact compact_gap one tail unit hx compact hp zero
      · exact middle_gap one tail unit (le_of_not_ge compact) hp inside zero
    exact scaled_gap_to_normalized_sign (by decide : 2 ≤ 4) (by omega : 4-1 ≤ p)
      w one tail hx (radius_pos x)
      (normalizedRow_insertion (by decide : 3 ≤ 4) (by omega) w one tail x) gap
  · exact exterior_sign (by omega) w one tail unit (le_of_not_ge inside) zero

/-- From upper size 512, every pair of independent short-cycle weights in
the closed square yields strict quotient and weak original interlacing. -/
theorem independent_weights {n : ℕ} (hn : 512 ≤ n)
    (w : ℕ → ℝ) (one : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (tail : ∀ a ≥ 4, w a = 1) :
    StrictNegativeInterlacing (weightedQuotient (n-1) w) (weightedQuotient n w) (n-3) ∧
      WeakRealInterlacing (row (n-1) w) (row n w) := by
  apply independent_interlacing_of_normalized_sign (by decide : 3 ≤ 4) (by omega)
    (w := w) <;> try assumption
  intro v v1 vu vt x hx hz
  simpa only [show n-1+1=n by omega] using normalized_sign (by omega : 511 ≤ n-1) v v1 vu vt hx hz

/-- Setting both short-cycle weights to zero restores the original
permutation enumerators with minimum cycle length four. -/
theorem original {n : ℕ} (hn : 512 ≤ n) :
    StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) 4)
        (Band.generalCycleQuotient n 4) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) 4) (enumerator n 4) := by
  have unit (a : ℕ) : profile 4 0 a ∈ Set.Icc (0:ℝ) 1 := by
    by_cases h : a<4 <;> simp [profile,h]
  have tail (a : ℕ) (ha : 4 ≤ a) : profile 4 0 a = 1 := by simp [profile,not_lt.mpr ha]
  simpa only [(weightedQuotient_endpoints (by decide : 2 ≤ 4) (by omega : 0<n-1)).1,
    (weightedQuotient_endpoints (by decide : 2 ≤ 4) (by omega : 0<n)).1,
    row_zero _ (by decide : 2 ≤ 4)] using independent_weights hn (profile 4 0) (by rfl) unit tail

#print axioms normalized_sign
#print axioms independent_weights
#print axioms original

end LongCycleBounds.FixedFour
