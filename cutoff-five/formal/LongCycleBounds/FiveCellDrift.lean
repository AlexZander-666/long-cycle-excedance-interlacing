import LongCycleBounds.FiveCellMoments

/-! The rational insertion budget bounds the true four-term drift, uniformly
in the independent cycle marks. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Finset FixedCutoff PoleBridge Band LongCycleFinite.K5CompactCert

theorem cell_drift {c : Cell} (hc : c.Valid) {x : ℝ} (xa : (c.a : ℝ) ≤ x)
    (xb : x ≤ (c.b : ℝ)) (rLo : (c.rLo:ℝ) ≤ exp (-x)) (rHi : exp (-x) ≤ (c.rHi:ℝ))
    {w : ℕ → ℝ} (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) :
    (∑ i ∈ range 4, |drift w (i+1) x| * (radius x)^(i+2)) ≤ (c.drift:ℝ)*s x := by
  obtain ⟨hx,rhoCap,_,_⟩ := cell_radii hc.1 xa xb
  obtain ⟨m2,m3,m4,m5⟩ := cell_moment_caps hc.1 hx rLo rHi
  let ρ := radius x
  have rp : 0 < ρ := radius_pos x
  have term (a : ℕ) (M : ℝ) (hm : |cycleMoment (a+1) x| ≤ M) :
      |drift w a x| * ρ^(a+1) * ρ ≤ M*(c.rho:ℝ)^(a+2)/a.factorial := by
    have f : (0:ℝ) < a.factorial := by positivity
    have diff : |w (a+1)-w a| ≤ 1 := abs_le.mpr
      ⟨by linarith [(unit (a+1)).1,(unit a).2],by linarith [(unit (a+1)).2,(unit a).1]⟩
    have cap : |w (a+1)-w a| * |cycleMoment (a+1) x| ≤ M :=
      (mul_le_of_le_one_left (abs_nonneg _) diff).trans hm
    have prod := mul_le_mul cap (pow_le_pow_left₀ rp.le rhoCap (a+2))
      (pow_nonneg rp.le _) ((abs_nonneg _).trans hm)
    rw [drift,abs_div,abs_mul,abs_of_pos f,div_mul_eq_mul_div,div_mul_eq_mul_div,
      mul_assoc (_*_) _ _,←pow_succ]
    exact div_le_div_of_nonneg_right prod f.le
  have d2 := term 1 _ m2
  have d3 := term 2 _ m3
  have d4 := term 3 _ m4
  have d5 := term 4 _ m5
  norm_num [Nat.factorial] at d2 d3 d4 d5
  have PL : (0:ℝ) < (piLo:ℝ) := by norm_num [piLo]
  have raw := hc.2.2.2.1
  change c.computedDrift ≤ c.drift at raw
  have cast : ((c.m2:ℝ)*c.rho^3+(c.m3:ℝ)*c.rho^4/2+(c.m4:ℝ)*c.rho^5/6+
      (c.m5:ℝ)*c.rho^6/24)/(piLo:ℝ) ≤ (c.drift:ℝ) := by exact_mod_cast raw
  have dnon : 0 ≤ (c.drift:ℝ) := by
    apply le_trans _ cast
    apply div_nonneg _ PL.le
    have h2 := (abs_nonneg _).trans m2
    have h3 := (abs_nonneg _).trans m3
    have h4 := (abs_nonneg _).trans m4
    have h5 := (abs_nonneg _).trans m5
    have hρ := rp.le.trans rhoCap
    positivity
  rw [s,← mul_div_assoc]
  apply (le_div_iff₀ rp).mpr
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd, add_mul]
  apply le_trans _ (mul_le_mul_of_nonneg_left pi_enclosure.1 dnon)
  linarith only [d2,d3,d4,d5,(div_le_iff₀ PL).mp cast]

#print axioms cell_drift
end LongCycleBounds.FiveCutoff
