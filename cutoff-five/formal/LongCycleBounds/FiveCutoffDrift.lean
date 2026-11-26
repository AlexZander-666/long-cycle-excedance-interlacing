import LongCycleBounds.FiveCutoffMoments

/-! Rational envelopes for the true quartic tilt coefficients and insertion drift. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real FixedCutoff Band

theorem quartic_tilt (w : ℕ → ℝ) (x : ℝ) :
    let h := height (exp (-x))
    tiltCoefficient w 4 x = (1-w 4)*h*(1-6*h)/24 := by
  dsimp only
  rw [tiltCoefficient,(moment_forms x).2.2.1]
  norm_num
  ring

theorem four_absolute_moments {x : ℝ} (hx : 0 ≤ x) :
    let r := exp (-x)
    |cycleMoment 2 x| ≤ r ∧ |cycleMoment 3 x| ≤ r ∧
    |cycleMoment 4 x| ≤ r ∧ |cycleMoment 5 x| ≤ r := by
  let r := exp (-x)
  have r0 : 0 ≤ r := (exp_pos _).le
  have r1 : r ≤ 1 := exp_le_one_iff.mpr (by linarith)
  obtain ⟨h0,hr,h4,v0,v1,_⟩ := shape_bounds r0 r1
  obtain ⟨m2,m3,m4,m5⟩ := moment_forms x
  have vabs : |imbalance r| ≤ 1 := by rwa [abs_of_nonneg v0]
  have habs : |1-6*height r| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have tailbound (a : ℝ) (ha : |a| ≤ 1) : |-(height r)*a| ≤ r := by
    rw [abs_mul,abs_neg,abs_of_nonneg h0]
    exact (mul_le_of_le_one_right h0 ha).trans hr
  change |cycleMoment 2 x| ≤ r ∧ _
  rw [m2,m3,m4,m5]
  refine ⟨by change |-(height r)| ≤ r; rwa [abs_neg,abs_of_nonneg h0], tailbound _ vabs,
    tailbound _ habs, ?_⟩
  rw [mul_assoc]
  exact tailbound _ (fifth_shape_bound r0 r1)

/-- Common exponential majorant with the factorial retained at all four orders. -/
theorem drift_factorial {w : ℕ → ℝ} (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 0 ≤ x) {a : ℕ} (lo : 1 ≤ a) (hi : a ≤ 4) :
    |drift w a x| ≤ exp (-x) / a.factorial := by
  have diff : |w (a+1)-w a| ≤ 1 := abs_le.mpr
    ⟨by linarith [(unit (a+1)).1, (unit a).2],by linarith [(unit (a+1)).2,(unit a).1]⟩
  obtain ⟨m2,m3,m4,m5⟩ := four_absolute_moments hx
  have bound : |cycleMoment (a+1) x| ≤ exp (-x) := by
    interval_cases a <;> assumption
  rw [drift,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℝ)<a.factorial)]
  exact div_le_div_of_nonneg_right
    ((mul_le_of_le_one_left (abs_nonneg _) diff).trans bound) (by positivity)

#print axioms quartic_tilt
#print axioms four_absolute_moments
#print axioms drift_factorial
end LongCycleBounds.FiveCutoff
