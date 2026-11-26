import LongCycleBounds.FixedCutoffCubeSign
import LongCycleBounds.CycleProfileIndependentReadout

/-! Eventual consecutive interlacing, uniformly over independent short-cycle weights. -/

noncomputable section

namespace LongCycleBounds.FixedCutoff

open LongCycles LongCycleFinite

/-- One threshold works on the entire cube of short-cycle weights. -/
theorem fixed_cutoff_independent_weights (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, k < N ∧ ∀ n ≥ N, ∀ w : ℕ → ℝ,
      w 1 = 0 → (∀ a, w a ∈ Set.Icc (0 : ℝ) 1) → (∀ a ≥ k, w a = 1) →
      StrictNegativeInterlacing (CycleProfile.weightedQuotient (n - 1) w)
        (CycleProfile.weightedQuotient n w) (n - 3) ∧
      WeakRealInterlacing (CycleProfile.row (n - 1) w) (CycleProfile.row n w) := by
  obtain ⟨N, hN, hsign⟩ := eventual_profile_sign hk
  exact ⟨N, hN, fun n hn ↦ CycleProfile.independent_interlacing_of_normalized_sign hk
    (by omega) (fun w one unit tail ↦ hsign n hn w one tail unit)⟩

#print axioms fixed_cutoff_independent_weights

end LongCycleBounds.FixedCutoff
