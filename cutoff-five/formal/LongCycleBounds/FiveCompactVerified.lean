import LongCycleBounds.FiveCellLoss
import LongCycleBounds.FiveCellResidue

/-! Original normalized permutation rows at all predecessor roots in [0,11].
Weights on 2-, 3-, and 4-cycles range independently over the closed cube. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real FixedCutoff PoleBridge LongCycleFinite.K5CompactCert

theorem compact_sign {w : ℕ → ℝ} (w1 : w 1=0) (tail : ∀ a ≥ 5, w a=1)
    (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) {x : ℝ} (hx : 0 ≤ x) (xmax : x ≤ 11)
    {p : ℕ} (hp : 48 ≤ p) (zero : CycleProfile.normalizedRow w p x=0) :
    0 < CycleProfile.normalizedRow w (p+1) x * (-deriv (CycleProfile.normalizedRow w p) x) := by
  obtain ⟨c,mem,hc,xa,xb⟩ := covers hx xmax
  obtain ⟨_,_,hr,hthird⟩ := cell_radii hc.1 xa xb
  obtain ⟨rLo,rHi⟩ := Cell.r_bounds hc xa xb
  have inv := cell_inverse_amplitude hc xa xb w1 unit
  have error := residue_of_inverse_amplitude hc xa xb w1 unit inv
  have cap := cell_drift hc xa xb rLo rHi unit
  have rational := (budget_caps mem).2.1
  have raw : (c.drift:ℝ) < ((48/5:ℚ):ℝ) := Rat.cast_lt.mpr rational
  have d : (c.drift:ℝ) ≤ 48/5 := by simpa only [Rat.cast_div,Rat.cast_ofNat] using raw.le
  exact compact_sign_of_cell w1 tail hx hr hthird hp zero error
    (cap.trans (mul_le_mul_of_nonneg_right d (div_pos pi_pos (radius_pos x)).le))

#print axioms compact_sign
end LongCycleBounds.FiveCutoff
