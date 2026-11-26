import LongCycleBounds.FixedCutoffReadout
import LongCycleBounds.CycleProfileReadout

/-! Uniform assembly of the compact, middle-angle and exterior tests. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real Finset PoleBridge MarkedTwo
open LongCycles LongCycleFinite

/-- Finite adjacent-difference insertion identity for the true permutation row. -/
def InsertionAt (w : ℕ→ℝ) (k p : ℕ) (x : ℝ) : Prop :=
  CycleProfile.normalizedRow w (p+1) x + deriv (CycleProfile.normalizedRow w p) x =
    ∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*CycleProfile.normalizedRow w (p-(i+1)) x

/-- Uniform compact-interval test; the same row threshold must work for
the full unit cube, or just for the one-parameter path used in the proof. -/
def ScaledGapAt (w : ℕ→ℝ) (k p : ℕ) (x : ℝ) : Prop :=
  let R := radius x
  let Y := scaledCoeff (profileSeries w k x) R
  |(∑ i∈range (k-1), drift w (i+1) x*R^(i+2)*Y (p+1-(i+2)))/((p:ℝ)+1)| < |Y (p+1)|

/-- A single choice of X and row threshold handles all x beyond X, all unit
profiles at the cutoff, and every size thereafter. -/
theorem eventual_noncompact_sign (k : ℕ) (hk : 2≤k) :
    ∃ X : ℝ, 16≤X ∧ ∃ P : ℕ, ∀ p≥P, ∀ (w : ℕ→ℝ), w 1=0 → (∀ a≥k, w a=1) →
      (∀ a, w a∈Set.Icc (0:ℝ) 1) → ∀ x≥X, InsertionAt w k p x →
      CycleProfile.normalizedRow w p x=0 →
      0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
  let d := k-1
  have hd : 1≤d := by dsimp [d];omega
  obtain ⟨X,hX,Xbud⟩ := eventual_middle_budget d
  obtain ⟨E,hE⟩ := exists_nat_ge (exp (d:ℝ))
  let P := 1024 + (3*d+6) + (2*(d+5+1)).factorial + (2*(4*d+1)).factorial + E
  refine ⟨X,hX,P,?_⟩
  intro p hp w one tail unit x high ins zero
  have hn : 1024≤p+1 := by dsimp [P] at hp;omega
  have room : 3*d+6≤p := by dsimp [P] at hp;omega
  have dense : (2*(d+5+1)).factorial≤p+1 := by dsimp [P] at hp;omega
  have dense0 : (2*(4*d+1)).factorial≤p+1 := by dsimp [P] at hp;omega
  have eN : exp (d:ℝ)≤(p+1:ℕ) := hE.trans (by exact_mod_cast (show E≤p+1 by dsimp [P] at hp;omega))
  let b := fun a ↦ tiltCoefficient w a x
  let C := fun a ↦ drift w a x
  have hx : 0≤x := by linarith
  have h16 : 16≤x := hX.trans high
  have hb (i : ℕ) (hi : 1≤ i) (_ : i≤d) : |b i|≤exp (-x) := tilt_bound unit hx hi
  have hC (i : ℕ) (_ : 1≤ i) (_ : i≤d) : |C i|≤exp (-x) := drift_bound unit hx i
  by_cases phase : x≤3*sqrt (p:ℝ)
  · apply scaled_gap_to_normalized_sign hk (by change d≤p;omega) w one tail hx (radius_pos x) ins
    have yz := scaled_eq_gain hk w one tail hx (radius x) p
    rw [zero,mul_zero] at yz
    have st := middle_insertion_gap hn h16 hd (by simpa using phase) b C hb hC (Xbud x high)
      (by simpa only [Nat.add_sub_cancel,profileSeries,b,d] using yz)
    simpa only [Nat.cast_succ,profileSeries,b,C,d] using st
  · have rz : raw b d p x=0 := by
      have a := raw_eq_profile hk w one tail hx p
      rw [zero] at a
      exact (mul_eq_zero.mp a).resolve_left (by unfold time;linarith [exp_pos (-x)])
    exact raw_gap_to_normalized_sign hk w one tail hx ins
      (outer_insertion_gap hn hd room dense dense0 eN b C hb hC (le_of_not_ge phase) rz)

/-- The marked proof reduces to compact-interval coefficient analysis and the
original enumeration insertion. All upper and lower row indices are explicit. -/
theorem eventual_sign_of_compact {k : ℕ} (hk : 2≤k)
    (insert : ∀ p≥k, ∀ u∈Set.Icc (0:ℝ) 1, ∀ x≥(0:ℝ), InsertionAt (commonMark k u) k p x)
    (compact : ∀ X : ℝ, 16≤X → ∃ P : ℕ, ∀ p≥P, ∀ u∈Set.Icc (0:ℝ) 1,
      ∀ x∈Set.Icc (0:ℝ) X, CycleProfile.normalizedRow (commonMark k u) p x=0 →
        ScaledGapAt (commonMark k u) k p x) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N, ∀ u∈Set.Icc (0:ℝ) 1, ∀ x≥(0:ℝ),
      CycleProfile.normalizedRow (CycleProfile.profile k u) (n-1) x=0 →
      0<CycleProfile.normalizedRow (CycleProfile.profile k u) n x*
        (-deriv (CycleProfile.normalizedRow (CycleProfile.profile k u) (n-1)) x) := by
  obtain ⟨X,h16,P,outer⟩ := eventual_noncompact_sign k hk
  obtain ⟨Q,inner⟩ := compact X h16
  let N := k+P+Q+1
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro n hn u hu x hx hzero
  let p := n-1
  have kp : k≤p := by dsimp [p,N] at *;omega
  have pp : P≤p := by dsimp [p,N] at *;omega
  have qq : Q≤p := by dsimp [p,N] at *;omega
  have next : p+1=n := by dsimp [p,N] at *;omega
  let w := commonMark k u
  have w1 : w 1=0 := by simp [w,commonMark]
  have tail (a : ℕ) (ha : k≤a) : w a=1 := by simp [w,commonMark,show a≠1 by omega,not_lt.mpr ha]
  have unit (a : ℕ) : w a∈Set.Icc (0:ℝ) 1 := by
    dsimp [w,commonMark]
    split_ifs <;> first | exact hu | norm_num
  have zero : CycleProfile.normalizedRow w p x=0 := by simpa only [w,normalized_commonMark,p] using hzero
  have ins := insert p kp u hu x hx
  have ans : 0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
    by_cases lo : x≤X
    · exact scaled_gap_to_normalized_sign hk (by omega) w w1 tail hx (radius_pos x) ins
        (inner p qq u hu x ⟨hx,lo⟩ zero)
    · exact outer p pp w w1 tail unit x (le_of_not_ge lo) ins zero
  simpa only [w,normalized_commonMark,next,p] using ans

/-- Joint marked and unmarked conclusions of the source and compact inputs. -/
theorem eventual_interlacing_of_compact {k : ℕ} (hk : 3≤k)
    (insert : ∀ p≥k, ∀ u∈Set.Icc (0:ℝ) 1, ∀ x≥(0:ℝ), InsertionAt (commonMark k u) k p x)
    (compact : ∀ X : ℝ, 16≤X → ∃ P : ℕ, ∀ p≥P, ∀ u∈Set.Icc (0:ℝ) 1,
      ∀ x∈Set.Icc (0:ℝ) X, CycleProfile.normalizedRow (commonMark k u) p x=0 →
        ScaledGapAt (commonMark k u) k p x) :
    ∃ N : ℕ, k<N ∧ ∀ n≥N,
      (∀ u∈Set.Icc (0:ℝ) 1,
        StrictNegativeInterlacing (CycleProfile.quotient (n-1) k u) (CycleProfile.quotient n k u) (n-3) ∧
        WeakRealInterlacing (CycleProfile.row (n-1) (CycleProfile.profile k u)) (CycleProfile.row n (CycleProfile.profile k u))) ∧
      StrictNegativeInterlacing (Band.generalCycleQuotient (n-1) k) (Band.generalCycleQuotient n k) (n-3) ∧
        WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  obtain ⟨N,kN,sig⟩ := eventual_sign_of_compact (by omega : 2≤k) insert compact
  exact ⟨N,kN,fun n hn ↦ ⟨CycleProfile.interlacing_of_normalized_sign hk (by omega) (sig n hn),
    CycleProfile.original_of_normalized_sign hk (by omega) (sig n hn)⟩⟩

#print axioms eventual_interlacing_of_compact
#print axioms eventual_noncompact_sign
#print axioms eventual_sign_of_compact
end LongCycleBounds.FixedCutoff
