import LongCycleBounds.FixedCutoffEventual
import LongCycleBounds.FixedCutoffCompactApprox

/-! Eventual original consecutive interlacing at every fixed minimum cycle length. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open LongCycles LongCycleFinite MarkedTwo

theorem actual_compact_poles (d : ℕ) {X : ℝ} (hX : 0≤X) : CompactPoleEstimate d X := by
  obtain ⟨q,M,m,U,q0,q1,hM,hm,hU,est⟩ := compact_scaled_row_uniform d hX
  refine ⟨q,M,m,U,q0,q1,hM,hm,hU,?_⟩
  intro x hx b hb
  exact ⟨tiltValue b d (nearestPole x),est hx.1 hx.2 b hb⟩

/-- The threshold depends only on k, uniformly over every larger upper row
index and the complete common short-cycle weight interval. -/
theorem fixed_cutoff_marked_and_original (k : ℕ) (hk : 3≤k) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N,
      (∀ u∈Set.Icc (0:ℝ) 1,
        StrictNegativeInterlacing (CycleProfile.quotient (n-1) k u) (CycleProfile.quotient n k u) (n-3) ∧
        WeakRealInterlacing (CycleProfile.row (n-1) (CycleProfile.profile k u)) (CycleProfile.row n (CycleProfile.profile k u))) ∧
      StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) k) (Band.generalCycleQuotient n k) (n-3) ∧
        WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) :=
  marked_and_original_of_poles hk fun X hX ↦ actual_compact_poles (k-1) (by linarith)

/-- The unmarked specialization, directly in terms of the conjectured
permutation polynomials rather than the analytic coordinates or a recurrence. -/
theorem fixed_cutoff_eventual_original (k : ℕ) (hk : 3≤k) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N,
      StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) k) (Band.generalCycleQuotient n k) (n-3) ∧
        WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  obtain ⟨N,hN,all⟩ := fixed_cutoff_marked_and_original k hk
  exact ⟨N,hN,fun n hn ↦ (all n hn).2⟩

#print axioms actual_compact_poles
#print axioms fixed_cutoff_marked_and_original
#print axioms fixed_cutoff_eventual_original
end LongCycleBounds.FixedCutoff
