import LongCycleBounds.FiveCutoffDrift
import LongCycleBounds.FiveCellGeometry

/-! Real monotonicity and sign ranges for converting the cell certificate into
a bound for the four actual insertion moments. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real FixedCutoff Band LongCycleFinite.K5CompactCert

theorem height_mono {r t : ℝ} (r0 : 0 ≤ r) (rt : r ≤ t) (t1 : t ≤ 1) :
    height r ≤ height t := by
  have t0 := r0.trans rt
  have prod : r*t ≤ 1 := (mul_le_of_le_one_right r0 t1).trans (rt.trans t1)
  unfold height
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_nonneg (sub_nonneg.mpr rt) (sub_nonneg.mpr prod)]

theorem imbalance_anti {r t : ℝ} (r0 : 0 ≤ r) (rt : r ≤ t) :
    imbalance t ≤ imbalance r := by
  have t0 := r0.trans rt
  unfold imbalance
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

private theorem bound_affine_abs {a x l h : ℝ} (a0 : 0 ≤ a) (lo : l ≤ x) (hi : x ≤ h) :
    |1-a*x| ≤ max |1-a*l| |1-a*h| := by
  have L := (le_abs_self (1-a*l)).trans (le_max_left |1-a*l| |1-a*h|)
  have H := (neg_le_abs (1-a*h)).trans (le_max_right |1-a*l| |1-a*h|)
  exact abs_le.mpr ⟨by linarith only [H,mul_le_mul_of_nonneg_left hi a0],
    by linarith only [L,mul_le_mul_of_nonneg_left lo a0]⟩

theorem roundUp_ge (r : ℚ) : r ≤ roundUp r := by
  unfold roundUp
  apply (le_div_iff₀ (by norm_num [LongCycleFinite.K5CompactCert.den])).mpr
  exact Rat.le_ceil

theorem cell_moment_caps {c : Cell} (hc : c.Geometry) {x : ℝ} (hx : 0 ≤ x)
    (rLo : (c.rLo : ℝ) ≤ exp (-x)) (rHi : exp (-x) ≤ (c.rHi : ℝ)) :
    |cycleMoment 2 x| ≤ (c.m2 : ℝ) ∧ |cycleMoment 3 x| ≤ (c.m3 : ℝ) ∧
      |cycleMoment 4 x| ≤ (c.m4 : ℝ) ∧ |cycleMoment 5 x| ≤ (c.m5 : ℝ) := by
  let r := exp (-x)
  have r0 : 0 ≤ r := (exp_pos _).le
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  obtain ⟨_,_,_,lo0,_,hi1,_⟩ := hc
  have L0 : (0:ℝ) ≤ (c.rLo:ℝ) := by exact_mod_cast lo0.le
  have H1 : (c.rHi:ℝ) ≤ 1 := by exact_mod_cast hi1
  have L : (c.hLo:ℝ) ≤ height r := by
    simpa [Cell.hLo,height] using height_mono L0 rLo r1
  have H : height r ≤ (c.hHi:ℝ) := by
    simpa [Cell.hHi,height] using height_mono r0 rHi H1
  have V : imbalance r ≤ (c.vHi:ℝ) := by
    simpa [Cell.vHi,imbalance] using imbalance_anti L0 rLo
  obtain ⟨h0,_,_,v0,_,_⟩ := shape_bounds r0 r1
  have HV := mul_le_mul H V v0 (h0.trans H)
  have f4 := bound_affine_abs (a:=6) (by norm_num) L H
  have f5 := bound_affine_abs (a:=12) (by norm_num) L H
  obtain ⟨m2,m3,m4,m5⟩ := moment_forms x
  rw [m2,m3,m4,m5]
  change |-(height r)| ≤ _ ∧ |-(height r)*imbalance r| ≤ _ ∧
    |-(height r)*(1-6*height r)| ≤ _ ∧ |-(height r)*imbalance r*(1-12*height r)| ≤ _
  simp only [abs_mul,abs_neg,abs_of_nonneg h0,abs_of_nonneg v0]
  refine ⟨H.trans (by exact_mod_cast roundUp_ge c.hHi),
    HV.trans (by exact_mod_cast roundUp_ge (c.hHi*c.vHi)), ?_, ?_⟩
  · apply (mul_le_mul H f4 (abs_nonneg _) (h0.trans H)).trans
    exact_mod_cast roundUp_ge (c.hHi * max |1-6*c.hLo| |1-6*c.hHi|)
  · apply (mul_le_mul HV f5 (abs_nonneg _) ((mul_nonneg h0 v0).trans HV)).trans
    exact_mod_cast roundUp_ge (c.hHi*c.vHi * max |1-12*c.hLo| |1-12*c.hHi|)

#print axioms cell_moment_caps
end LongCycleBounds.FiveCutoff
