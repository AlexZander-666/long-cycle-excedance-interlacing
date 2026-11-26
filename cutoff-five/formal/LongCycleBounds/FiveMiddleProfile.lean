import LongCycleBounds.FiveCutoffDrift
import LongCycleBounds.FixedCutoffSignedTilt

/-! Factorial majorants for the actual cycle-profile tilt on the middle interval. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Finset FixedCutoff Band

theorem tilt_factorial {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 0 ≤ x) {a : ℕ} (lo : 1 ≤ a) (hi : a ≤ 4) :
    |tiltCoefficient w a x| ≤ exp (-x) / a.factorial := by
  by_cases ha : a = 1
  · subst a
    rw [(FixedFour.tilt_forms w w1 x).1, abs_of_pos (by positivity)]
    simp only [Nat.factorial_one, Nat.cast_one, div_one]
    exact div_le_self (exp_pos _).le (by linarith [exp_pos (-x)])
  obtain ⟨m2,m3,m4,_⟩ := four_absolute_moments hx
  have m : |cycleMoment a x| ≤ exp (-x) := by
    have : 2 ≤ a := by omega
    interval_cases a <;> assumption
  have diff : |w a-1| ≤ 1 := abs_le.mpr
    ⟨by linarith [(unit a).1], by linarith [(unit a).2]⟩
  rw [tiltCoefficient, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ)<a.factorial)]
  exact div_le_div_of_nonneg_right ((mul_le_of_le_one_left (abs_nonneg _) diff).trans m)
    (by positivity)

/-- At radius at least eleven the four factorial terms have a uniform quartic envelope. -/
theorem quartic_majorant {R : ℝ} (hr : 11 ≤ R) :
    R+R^2/2+R^3/6+R^4/24 ≤ (657/10648:ℝ)*R^4 := by
  have h1 : 11*R ≤ R^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ R by linarith)]
  have h2 : 11*R^2 ≤ R^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg R)]
  have h3 : 11*R^3 ≤ R^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (pow_nonneg (show 0 ≤ R by linarith) 3)]
  linarith only [h1,h2,h3]

theorem factorial_budget (b : ℕ → ℝ) {r R : ℝ} (hr : 0 ≤ r) (hR : 11 ≤ R)
    (bounds : ∀ i, 1 ≤ i → i ≤ 4 → |b i| ≤ r/i.factorial) :
    cost b R 4 ≤ (657/10648:ℝ)*r*R^4 := by
  have rr : 0 ≤ R := by linarith
  have term (i : ℕ) (lo : 1 ≤ i) (hi : i ≤ 4) :=
    mul_le_mul_of_nonneg_right (bounds i lo hi) (pow_nonneg rr i)
  have a := term 1 (by decide) (by decide)
  have b2 := term 2 (by decide) (by decide)
  have c := term 3 (by decide) (by decide)
  have d := term 4 (by decide) (by decide)
  norm_num [Nat.factorial] at a b2 c d
  simp only [cost,sum_range_succ,sum_range_zero,zero_add,Nat.reduceAdd,pow_one]
  linarith only [a,b2,c,d,mul_le_mul_of_nonneg_left (quartic_majorant hR) hr]

theorem middle_profile_cost {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 11 ≤ R) :
    cost (fun a ↦ tiltCoefficient w a x) R 4 ≤ (657/10648:ℝ)*exp (-x)*R^4 :=
  factorial_budget _ (exp_pos _).le hR (fun _ ↦ tilt_factorial w1 unit hx)

theorem middle_drift_cost {w : ℕ → ℝ} (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 11 ≤ R) :
    cost (fun a ↦ drift w a x) R 4 ≤ (657/10648:ℝ)*exp (-x)*R^4 :=
  factorial_budget _ (exp_pos _).le hR (fun _ ↦ drift_factorial unit hx)

#print axioms middle_profile_cost
#print axioms middle_drift_cost
end LongCycleBounds.FiveCutoff
