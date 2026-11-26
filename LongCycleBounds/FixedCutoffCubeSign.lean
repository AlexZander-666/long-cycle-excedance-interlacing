import LongCycleBounds.FixedCutoffVerified

/-! A single threshold covers all independently chosen short-cycle weights in the unit cube. -/
namespace LongCycleBounds.FixedCutoff
open LongCycles LongCycleFinite MarkedTwo Real PoleBridge

theorem compact_gap_independent {k : ℕ} (hk : 2≤k) {X : ℝ} (hX : 0≤X) :
    ∃ P : ℕ, ∀ p≥P, ∀ w : ℕ→ℝ, w 1=0 → (∀ a≥k,w a=1) →
      (∀ a,w a∈Set.Icc (0:ℝ) 1) → ∀ x∈Set.Icc (0:ℝ) X,
      CycleProfile.normalizedRow w p x=0 → ScaledGapAt w k p x := by
  obtain ⟨q,M,m,U,q0,q1,hM,hm,hU,est⟩ := actual_compact_poles (k-1) hX
  obtain ⟨P,phase⟩ := compact_phase_threshold (k-1) hX q0 q1 hM hm hU
  refine ⟨P,?_⟩
  intro p hp w one tail unit x hx zero
  let b := fun a ↦ tiltCoefficient w a x
  have er : exp (-x)≤1 := exp_le_one_iff.mpr (by linarith [hx.1])
  have hb (i : ℕ) (hi : 1 ≤ i) (_ : i≤k-1) : |b i|≤1 := (tilt_bound unit hx.1 hi).trans er
  obtain ⟨B,lo,hi,app⟩ := est x hx b hb
  have hzero := scaled_eq_gain hk w one tail hx.1 (radius x) p
  rw [zero,mul_zero] at hzero
  exact phase p hp x hx B lo hi _ (fun a ↦ drift w a x) app
    (fun i _ _ ↦ (drift_bound unit hx.1 i).trans er) hzero

/-- Uniform half-line sign for all bounded short-cycle profiles, with k fixed. -/
theorem eventual_profile_sign {k : ℕ} (hk : 3≤k) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N, ∀ w : ℕ→ℝ, w 1=0 → (∀ a≥k,w a=1) →
      (∀ a,w a∈Set.Icc (0:ℝ) 1) → ∀ x≥(0:ℝ),
      CycleProfile.normalizedRow w (n-1) x=0 →
      0<CycleProfile.normalizedRow w n x*(-deriv (CycleProfile.normalizedRow w (n-1)) x) := by
  obtain ⟨X,h16,P,out⟩ := fixed_cutoff_noncompact hk
  obtain ⟨Q,inside⟩ := compact_gap_independent (k:=k) (by omega) (by linarith : 0≤X)
  let N:=k+P+Q+1
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro n hn w one tail unit x hx zero
  have hp : k≤n-1 := by dsimp [N] at hn;omega
  have e : n-1+1=n := by omega
  by_cases small : x≤X
  · have gap := inside (n-1) (by dsimp [N] at hn;omega) w one tail unit x ⟨hx,small⟩ zero
    have ins := CycleProfile.normalizedRow_insertion hk (p:=n-1) (by omega) w one tail x
    simpa only [e] using scaled_gap_to_normalized_sign (by omega : 2≤k) (by omega : k-1≤n-1)
      w one tail hx (radius_pos x) ins gap
  · simpa only [e] using out (n-1) (by dsimp [N] at hn;omega) w one tail unit x (le_of_not_ge small) zero

#print axioms eventual_profile_sign
end LongCycleBounds.FixedCutoff
