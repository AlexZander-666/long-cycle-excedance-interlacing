import LongCycleBounds.FiveCompactVerified
import LongCycleBounds.FiveMiddleSign
import LongCycleBounds.FiveExteriorVerified
import LongCycleBounds.CycleProfileIndependentReadout
import LongCycleFinite.K5Prefix.All

/-! Minimum cycle length five at every nondegenerate pair, with independent weights from size 49. -/
namespace LongCycleBounds.FiveCutoff
open Real LongCycles LongCycleFinite FixedCutoff PoleBridge CycleProfile

theorem normalized_sign {p : ℕ} (hp : 48 ≤ p) (w : ℕ → ℝ)
    (one : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1) (tail : ∀ a ≥ 5, w a = 1)
    {x : ℝ} (hx : 0 ≤ x) (zero : normalizedRow w p x = 0) :
    0 < normalizedRow w (p+1) x * (-deriv (normalizedRow w p) x) := by
  by_cases compact : x ≤ 11
  · exact compact_sign one tail unit hx compact hp zero
  by_cases inside : x ≤ 3*sqrt (p:ℝ)
  · exact middle_sign one tail unit (le_of_not_ge compact) hp inside zero
  exact exterior_sign (by omega) w one tail unit (le_of_not_ge inside) zero

/-- From upper size 49, every choice of independent short-cycle weights in
the closed cube yields strict quotient and weak original interlacing. -/
theorem independent_weights {n : ℕ} (hn : 49 ≤ n)
    (w : ℕ → ℝ) (one : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (tail : ∀ a ≥ 5, w a = 1) :
    StrictNegativeInterlacing (weightedQuotient (n-1) w) (weightedQuotient n w) (n-3) ∧
      WeakRealInterlacing (row (n-1) w) (row n w) := by
  apply independent_interlacing_of_normalized_sign (by decide : 3 ≤ 5) (by omega)
    (w := w) <;> try assumption
  intro v v1 vu vt x hx hz
  simpa only [show n-1+1=n by omega] using normalized_sign (by omega : 48 ≤ n-1) v v1 vu vt hx hz

/-- Setting all three short-cycle weights to zero restores the original
permutation enumerators with minimum cycle length five. -/
theorem original {n : ℕ} (hn : 49 ≤ n) :
    StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) 5)
        (Band.generalCycleQuotient n 5) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) 5) (enumerator n 5) := by
  have unit (a : ℕ) : profile 5 0 a ∈ Set.Icc (0:ℝ) 1 := by
    by_cases h : a<5 <;> simp [profile,h]
  have tail (a : ℕ) (ha : 5 ≤ a) : profile 5 0 a = 1 := by simp [profile,not_lt.mpr ha]
  simpa only [(weightedQuotient_endpoints (by decide : 2 ≤ 5) (by omega : 0<n-1)).1,
    (weightedQuotient_endpoints (by decide : 2 ≤ 5) (by omega : 0<n)).1,
    row_zero _ (by decide : 2 ≤ 5)] using independent_weights hn (profile 5 0) (by rfl) unit tail


theorem all_sizes {n : ℕ} (hn : 6 ≤ n) : K5Prefix.OriginalPair n := by
  by_cases small : n ≤ 48
  · exact K5Prefix.finite_original hn small
  obtain ⟨strict,weak⟩ := original (show 49 ≤ n by omega)
  exact ⟨⟨_, _, Band.actual_general_cycle_row (by decide : 2 ≤ 5) (by omega),
    Band.actual_general_cycle_row (by decide : 2 ≤ 5) (by omega), strict⟩, weak⟩

#print axioms normalized_sign
#print axioms independent_weights
#print axioms original
#print axioms all_sizes
end LongCycleBounds.FiveCutoff
