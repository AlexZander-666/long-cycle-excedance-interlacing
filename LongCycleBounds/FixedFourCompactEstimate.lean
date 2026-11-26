import LongCycleBounds.FixedFourCoefficients
import LongCycleBounds.FixedCutoffCompactApprox
import LongCycleBounds.MarkedCompactSign

/-! Numerical coefficient estimates for the three compact intervals at cutoff four. -/

noncomputable section

namespace LongCycleBounds.FixedFour

open Real Finset PoleBridge FixedCutoff MarkedTwo

/-- The scaled coefficients of the genuine cutoff-four profile. -/
def compactRow (w : ℕ → ℝ) (x : ℝ) :=
  scaledCoeff (profileSeries w 4 x) (radius x)

/-- Contribution of a single nearest-pole residue. -/
def compactAmplitude (w : ℕ → ℝ) (x : ℝ) :=
  FixedCutoff.tiltValue (fun a ↦ tiltCoefficient w a x) 3 (nearestPole x)

private theorem pi_upper : π < (16 / 5 : ℝ) :=
  pi_lt_d2.trans (by norm_num)

private theorem pi_sq_lower : (9 : ℝ) ≤ π ^ 2 :=
  (by norm_num : (9 : ℝ) = 3 ^ 2).le.trans
    (pow_le_pow_left₀ (by norm_num) pi_gt_three.le 2)

private theorem pi_sq_upper : π ^ 2 ≤ (16 / 5 : ℝ) ^ 2 :=
  pow_le_pow_left₀ pi_pos.le pi_upper.le 2

private theorem compact_geometry {x X R Q : ℝ} (hx : 0 ≤ x) (hX : x ≤ X)
    (R0 : 0 ≤ R) (Q0 : 0 ≤ Q)
    (hR : X^2 + 4*(16/5)^2 ≤ R^2) (hQ : X^2+9 ≤ Q^2*(X^2+36)) :
    compactRadius x ≤ R ∧ compactRadius X ≤ R ∧ radius x / compactRadius x ≤ Q := by
  have rX : compactRadius X ≤ R := by
    apply (sq_le_sq₀ (compactRadius_pos X).le R0).mp
    have hm : compactRadius X ^ 2 = X ^ 2 + 4 * π ^ 2 := sq_sqrt (by positivity)
    nlinarith only [hm, pi_sq_upper, hR]
  refine ⟨(compactRadius_mono hx hX).trans rX, rX, (compact_ratio_bound hx hX).trans ?_⟩
  apply (div_le_iff₀ (compactRadius_pos X)).2
  apply (sq_le_sq₀ (radius_pos X).le (mul_nonneg Q0 (compactRadius_pos X).le)).mp
  have sqR : compactRadius X ^ 2 = X^2 + 4*π^2 := sq_sqrt (by positivity)
  have sqρ : radius X ^ 2 = X^2 + π^2 := sq_sqrt (by positivity)
  rw [mul_pow, sqR, sqρ]
  have l : (1:ℝ) ≤ 4 * Q^2 := by
    by_contra! bad
    have e := mul_lt_mul_of_pos_right bad (show 0 < X^2+36 by positivity)
    nlinarith only [hQ,e,sq_nonneg X]
  have m := mul_nonneg (sub_nonneg.mpr l) (sub_nonneg.mpr pi_sq_lower)
  nlinarith only [hQ,m]

private theorem prefactor {x X R Q : ℝ} (R0 : 0 ≤ R) (Q1 : Q < 1)
    (hR : compactRadius X ≤ R) (hq : radius x / compactRadius x ≤ Q) :
    compactTailBound X + 2 / (1 - radius x / compactRadius x) ≤
      2*(R/3)^2 + 2*R + 2/(1-Q) := by
  have rat : compactRadius X / π ≤ R / 3 := by
    apply (div_le_div_iff₀ pi_pos (by norm_num)).2
    nlinarith only [hR,mul_nonneg R0 (sub_nonneg.mpr pi_gt_three.le)]
  have rat2 := pow_le_pow_left₀ (div_nonneg (compactRadius_pos X).le pi_pos.le) rat 2
  have frac : 2 / (1 - radius x / compactRadius x) ≤ 2/(1-Q) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  unfold compactTailBound
  linarith only [rat2, hR, frac]

private theorem exp_lower : (8/3 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
private theorem exp_upper : exp 1 < (11/4 : ℝ) := by linarith [exp_one_lt_d9]

private theorem exp_neg_cap (a : ℕ) {x : ℝ} (ha : (a : ℝ) ≤ x) :
    exp (-x) ≤ ((8/3 : ℝ)^a)⁻¹ := by
  calc
    exp (-x) ≤ exp (-(a : ℝ)) := exp_le_exp.mpr (neg_le_neg ha)
    _ = ((exp 1)^a)⁻¹ := by rw [exp_neg, ← exp_nat_mul, mul_one]
    _ ≤ _ := inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) exp_lower.le _)

set_option maxRecDepth 8192 in
private theorem coefficient_budget {w : ℕ → ℝ}
    {x X R Q : ℝ} {d j : ℕ} (hx : 0 ≤ x) (hX : x ≤ X) (hj : 508 ≤ j)
    (R0 : 0 ≤ R) (Q0 : 0 ≤ Q) (Q1 : Q < 1)
    (hR : X^2 + 4*(16/5)^2 ≤ R^2) (hQ : X^2+9 ≤ Q^2*(X^2+36))
    (hC : cost (fun a ↦ tiltCoefficient w a x) (compactRadius x) 3 ≤ d)
    (hF : 2*(R/3)^2 + 2*R + 2/(1-Q) ≤ 170)
    (num : 170*(11/4 : ℝ)^d*Q^508 < 1/1000000) :
    |compactRow w x j - 2*(compactAmplitude w x * compactRotation x^(j+1)).re| <
      1/1000000 := by
  obtain ⟨_, hRX, hq⟩ := compact_geometry hx hX R0 Q0 hR hQ
  have r0 := (radius_pos x).le
  have q0 : 0 ≤ radius x / compactRadius x := div_nonneg r0 (compactRadius_pos x).le
  have fp := (prefactor R0 Q1 hRX hq).trans hF
  have fe : exp (cost (fun a ↦ tiltCoefficient w a x) (compactRadius x) 3) ≤ (11/4)^d := by
    apply (exp_le_exp.mpr hC).trans
    rw [← mul_one (d : ℝ), exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos 1).le exp_upper.le _
  have fq : (radius x / compactRadius x)^(j+1) ≤ Q^508 :=
    (pow_le_pow_left₀ q0 hq _).trans (pow_le_pow_of_le_one Q0 Q1.le (by omega))
  have p := compact_scaled_row_bound hx hX (fun a ↦ tiltCoefficient w a x) 3 j
  change |compactRow w x j - 2*(compactAmplitude w x * compactRotation x^(j+1)).re| ≤ _ at p
  apply p.trans_lt (_ : _ < _)
  apply lt_of_le_of_lt _ num
  apply mul_le_mul _ fq (pow_nonneg q0 _) (by positivity)
  exact mul_le_mul fp fe (exp_pos _).le (by norm_num)

private theorem cost_four {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    {x : ℝ} (hx : 0 ≤ x) (hR : compactRadius x ≤ 8) :
    cost (fun a ↦ tiltCoefficient w a x) (compactRadius x) 3 ≤ (34 : ℕ) := by
  have R0 := (compactRadius_pos x).le
  have e := (tilt_cost_caps w w1 unit hx R0).1
  have p2 := pow_le_pow_left₀ R0 hR 2
  have p3 := pow_le_pow_left₀ R0 hR 3
  norm_num
  linarith only [e, hR, p2, p3]

private theorem cost_decay {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    {x R : ℝ} {a d : ℕ} (hx : 0 ≤ x) (ha : (a : ℝ) ≤ x)
    (hR : compactRadius x ≤ R)
    (H : ((8/3 : ℝ)^a)⁻¹ * (R+R^2/2+R^3/6) ≤ d) :
    cost (fun a ↦ tiltCoefficient w a x) (compactRadius x) 3 ≤ d := by
  have R'0 := (compactRadius_pos x).le
  apply (tilt_cost_caps w w1 unit hx R'0).2.trans
  refine (mul_le_mul (exp_neg_cap a ha) ?_ (by positivity) (by positivity)).trans H
  linarith only [hR, pow_le_pow_left₀ R'0 hR 2, pow_le_pow_left₀ R'0 hR 3]

set_option maxRecDepth 8192 in
/-- Starting at auxiliary order 508, each of the three compact intervals has
an absolute error less than one millionth. -/
theorem compact_error {w : ℕ → ℝ} (w1 : w 1 = 0)
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : 0 ≤ x) (h16 : x ≤ 16)
    {j : ℕ} (hj : 508 ≤ j) :
    |compactRow w x j - 2*(compactAmplitude w x*compactRotation x^(j+1)).re| <
      1/1000000 := by
  by_cases h4 : x ≤ 4
  · have geom := compact_geometry hx h4 (R := 8) (Q := 7/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact coefficient_budget (w := w) hx h4 hj (R := 8) (Q := 7/10) (d := 34)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cost_four w1 unit hx geom.1) (by norm_num) (by
        rw [show 508 = 16*31+4*3 by decide, pow_add, pow_mul, pow_mul]
        norm_num)
  by_cases h8 : x ≤ 8
  · have geom := compact_geometry hx h8 (R := 11) (Q := 9/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact coefficient_budget (w := w) hx h8 hj (R := 11) (Q := 9/10) (d := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cost_decay w1 unit hx (a := 4) (by push_cast; linarith) geom.1
        (by norm_num)) (by norm_num) (by
        rw [show 508 = 16*31+4*3 by decide, pow_add, pow_mul, pow_mul]
        norm_num)
  · have geom := compact_geometry hx h16 (R := 18) (Q := 24/25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact coefficient_budget (w := w) hx h16 hj (R := 18) (Q := 24/25) (d := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cost_decay w1 unit hx (a := 8) (by push_cast; linarith) geom.1
        (by norm_num)) (by norm_num) (by
        rw [show 508 = 16*31+4*3 by decide, pow_add, pow_mul, pow_mul]
        norm_num)

#print axioms compact_error

end LongCycleBounds.FixedFour
