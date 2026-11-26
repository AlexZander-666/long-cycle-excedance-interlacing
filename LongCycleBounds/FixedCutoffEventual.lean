import LongCycleBounds.FixedCutoffCompactPhase
import LongCycleBounds.CycleProfileInsertion
noncomputable section
namespace LongCycleBounds.FixedCutoff
open LongCycles LongCycleFinite

theorem original_insert {k : ℕ} (hk : 3≤k) (p : ℕ) (hp : k≤p) (u x : ℝ) :
    InsertionAt (commonMark k u) k p x := by
  apply CycleProfile.normalizedRow_insertion hk (by omega) (commonMark k u) (by simp [commonMark])
  intro a ha
  simp [commonMark,show a≠1 by omega,not_lt.mpr ha]

/-- On the full complement of a compact interval the strict sign for actual rows
holds unconditionally for arbitrary independently marked short cycles in [0,1]. -/
theorem fixed_cutoff_noncompact {k : ℕ} (hk : 3≤k) :
    ∃ X : ℝ, 16≤X ∧ ∃ P : ℕ, ∀ p≥P, ∀ (w : ℕ→ℝ), w 1=0 → (∀ a≥k, w a=1) →
      (∀ a, w a∈Set.Icc (0:ℝ) 1) → ∀ x≥X, CycleProfile.normalizedRow w p x=0 →
      0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
  obtain ⟨X,hX,P,out⟩ := eventual_noncompact_sign k (by omega)
  refine ⟨X,hX,P+k,?_⟩
  intro p hp w w1 tail unit x hx hz
  exact out p (by omega) w w1 tail unit x hx (CycleProfile.normalizedRow_insertion hk (by omega) w w1 tail x) hz

theorem marked_and_original_of_poles {k : ℕ} (hk : 3≤k)
    (compact : ∀ X : ℝ, 16≤X → CompactPoleEstimate (k-1) X) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N,
      (∀ u∈Set.Icc (0:ℝ) 1,
        StrictNegativeInterlacing (CycleProfile.quotient (n-1) k u) (CycleProfile.quotient n k u) (n-3) ∧
        WeakRealInterlacing (CycleProfile.row (n-1) (CycleProfile.profile k u)) (CycleProfile.row n (CycleProfile.profile k u))) ∧
      StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) k) (Band.generalCycleQuotient n k) (n-3) ∧
        WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  apply eventual_interlacing_of_compact hk (fun p hp u _ x _ ↦ original_insert hk p hp u x)
  exact fun X hX ↦ compact_profile_gap_of_estimate (by omega) (by linarith) (compact X hX)

#print axioms fixed_cutoff_noncompact
#print axioms marked_and_original_of_poles
end LongCycleBounds.FixedCutoff
