import LongCycleBounds.FiveCellCost

/-! # Lower bound on the principal amplitude at cutoff five

The quartic term uses the sign of the actual coefficient on the cell. When the height interval
straddles the sign boundary, the bound uses both endpoints of the interval of real parts.
-/

noncomputable section

namespace LongCycleBounds.FiveCutoff

open Real FixedCutoff MarkedTwo LongCycleFinite.K5CompactCert

private theorem pole_powers (x : ℝ) :
    (nearestPole x).re = x ∧
      (nearestPole x ^ 2).re = x ^ 2 - π ^ 2 ∧
      (nearestPole x ^ 3).re = x ^ 3 - 3 * π ^ 2 * x ∧
      (nearestPole x ^ 4).re = x ^ 4 - 6 * π ^ 2 * x ^ 2 + π ^ 4 := by
  have hre : (nearestPole x).re = x := by
    simp [nearestPole, PoleBridge.den, Complex.add_re, Complex.mul_re]
  have him : (nearestPole x).im = π := by
    simp [nearestPole, PoleBridge.den, Complex.add_im, Complex.mul_im]
  have hre2 : (nearestPole x ^ 2).re = x ^ 2 - π ^ 2 := by
    rw [pow_two, Complex.mul_re, hre, him]
    ring
  have him2 : (nearestPole x ^ 2).im = 2 * x * π := by
    rw [pow_two, Complex.mul_im, hre, him]
    ring
  refine ⟨hre, hre2, ?_, ?_⟩
  · rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, Complex.mul_re, hre2, him2, hre, him]
    ring
  · have hpow : nearestPole x ^ 4 = nearestPole x ^ 2 * nearestPole x ^ 2 :=
      pow_add (nearestPole x) 2 2
    rw [hpow, Complex.mul_re, hre2, him2]
    ring

private theorem cell_real_parts {c : Cell} {x : ℝ} (ha0 : 0 ≤ (c.a : ℝ))
    (ha : (c.a : ℝ) ≤ x) (hb : x ≤ (c.b : ℝ)) :
    (c.re2Lo : ℝ) ≤ (nearestPole x ^ 2).re ∧
      (c.re3Lo : ℝ) ≤ (nearestPole x ^ 3).re ∧
      (c.re4Lo : ℝ) ≤ (nearestPole x ^ 4).re ∧ (nearestPole x ^ 4).re ≤ (c.re4Hi : ℝ) := by
  obtain ⟨_, h2, h3, h4⟩ := pole_powers x
  have hx := ha0.trans ha
  have hlo0 : 0 ≤ (piLo : ℝ) := by norm_num [piLo]
  have hlo2 := pow_le_pow_left₀ hlo0 pi_enclosure.1 2
  have hhi2 := pow_le_pow_left₀ pi_pos.le pi_enclosure.2 2
  rw [h2, h3, h4]
  unfold Cell.re2Lo Cell.re3Lo Cell.re4Lo Cell.re4Hi
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [pow_le_pow_left₀ ha0 ha 2, hhi2]
  · linarith only [pow_le_pow_left₀ ha0 ha 3,
      mul_le_mul hhi2 hb hx (sq_nonneg (piHi : ℝ))]
  · linarith only [pow_le_pow_left₀ ha0 ha 4, pow_le_pow_left₀ hlo0 pi_enclosure.1 4,
      mul_le_mul hhi2 (pow_le_pow_left₀ hx hb 2) (sq_nonneg x) (sq_nonneg (piHi : ℝ))]
  · linarith only [pow_le_pow_left₀ hx hb 4, pow_le_pow_left₀ pi_pos.le pi_enclosure.2 4,
      mul_le_mul hlo2 (pow_le_pow_left₀ ha0 ha 2) (sq_nonneg (c.a : ℝ)) (sq_nonneg π)]

private theorem lower_term {b cap low u : ℝ} (hb : 0 ≤ b) (hcap : b ≤ cap) (hu : low ≤ u) :
    -(max 0 (-low) * cap) ≤ b * u := by
  have hu' : -(max 0 (-low)) ≤ u := by linarith only [hu, le_max_right 0 (-low)]
  calc
    -(max 0 (-low) * cap) = -(max 0 (-low)) * cap := by rw [neg_mul]
    _ ≤ -(max 0 (-low)) * b := mul_le_mul_of_nonpos_left hcap (neg_nonpos.mpr (le_max_left ..))
    _ ≤ u * b := mul_le_mul_of_nonneg_right hu' hb
    _ = b * u := mul_comm _ _

private theorem cell_fourth_term {c : Cell} {u b : ℝ}
    (hlo : (c.re4Lo : ℝ) ≤ u) (hhi : u ≤ (c.re4Hi : ℝ)) (habs : |b| ≤ (c.b4 : ℝ))
    (hnonpos : 1 ≤ 6 * c.hLo → b ≤ 0) (hnonneg : 6 * c.hHi ≤ 1 → 0 ≤ b) :
    -((c.fourthLoss : ℝ) * (c.b4 : ℝ)) ≤ b * u := by
  unfold Cell.fourthLoss
  split
  · rename_i h
    have hb := hnonpos h
    have hcap : -b ≤ (c.b4 : ℝ) := by simpa [abs_of_nonpos hb] using habs
    have lower := lower_term (neg_nonneg.mpr hb) hcap (neg_le_neg hhi)
    simpa using lower
  · split
    · rename_i h
      have hb := hnonneg h
      have hcap : b ≤ (c.b4 : ℝ) := by simpa [abs_of_nonneg hb] using habs
      simpa using lower_term hb hcap hlo
    · push_cast
      have hleft : -(c.re4Lo : ℝ) ≤ max |(c.re4Lo : ℝ)| |(c.re4Hi : ℝ)| :=
        (neg_le_abs _).trans (le_max_left ..)
      have hu : |u| ≤ max |(c.re4Lo : ℝ)| |(c.re4Hi : ℝ)| := abs_le.mpr
        ⟨by linarith only [hlo, hleft],
        hhi.trans ((le_abs_self (c.re4Hi : ℝ)).trans (le_max_right ..))⟩
      have hprod := mul_le_mul hu habs (abs_nonneg _) ((abs_nonneg _).trans hu)
      rw [← abs_mul, mul_comm u b] at hprod
      exact neg_le.mp ((neg_le_abs (b * u)).trans hprod)

private theorem exponent_real (x : ℝ) (b : ℕ → ℝ) :
    (∑ i ∈ Finset.range 4, (b (i + 1) : ℂ) * nearestPole x ^ (i + 1)).re =
      b 1 * x + b 2 * (nearestPole x ^ 2).re + b 3 * (nearestPole x ^ 3).re +
        b 4 * (nearestPole x ^ 4).re := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reduceAdd, pow_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, (pole_powers x).1]

/-- The inverse principal amplitude is bounded by the original cell certificate. -/
theorem cell_inverse_amplitude {c : Cell} (hv : c.Valid) {x : ℝ} (xa : (c.a : ℝ) ≤ x)
    (xb : x ≤ (c.b : ℝ)) {w : ℕ → ℝ} (w1 : w 1 = 0)
    (unit : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ ‖tiltValue (fun a ↦ tiltCoefficient w a x) 4 (nearestPole x)‖ * (c.invD : ℝ) := by
  obtain ⟨_, cap2, cap3, cap4⟩ := cell_tilt_caps hv xa xb w1 unit
  obtain ⟨_, ae, _, rlo0, _, rhi1, _⟩ := hv.1
  have ha0 : 0 ≤ (c.a : ℝ) := by rw [ae]; positivity
  have hx := ha0.trans xa
  obtain ⟨rlo, rhi⟩ := Cell.r_bounds hv xa xb
  have hr0 := (exp_pos (-x)).le
  have hr1 : exp (-x) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hLo : (c.hLo : ℝ) ≤ height (exp (-x)) := by
    simpa [Cell.hLo, height] using height_mono (by exact_mod_cast rlo0.le) rlo hr1
  have hHi : height (exp (-x)) ≤ (c.hHi : ℝ) := by
    simpa [Cell.hHi, height] using height_mono hr0 rhi (by exact_mod_cast rhi1)
  have hn : 0 ≤ (1 - w 4) * height (exp (-x)) :=
    mul_nonneg (sub_nonneg.mpr (unit 4).2) (shape_bounds hr0 hr1).1
  have fourth_nonpos (h : 1 ≤ 6 * c.hLo) : tiltCoefficient w 4 x ≤ 0 := by
    have h' : (1 : ℝ) ≤ 6 * (c.hLo : ℝ) := by exact_mod_cast h
    rw [quartic_tilt]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hn (by linarith only [h', hLo])) (by norm_num)
  have fourth_nonneg (h : 6 * c.hHi ≤ 1) : 0 ≤ tiltCoefficient w 4 x := by
    have h' : 6 * (c.hHi : ℝ) ≤ 1 := by exact_mod_cast h
    rw [quartic_tilt]
    exact div_nonneg (mul_nonneg hn (by linarith only [h', hHi])) (by norm_num)
  obtain ⟨lo2, lo3, lo4, hi4⟩ := cell_real_parts ha0 xa xb
  obtain ⟨⟨p1, _, _⟩, ⟨p2, _, _⟩, ⟨p3, _, _⟩⟩ := FixedFour.tilt_caps w w1 unit hx
  have h1 := mul_nonneg p1 hx
  have h2 := lower_term p2 ((le_abs_self _).trans cap2) lo2
  have h3 := lower_term p3 ((le_abs_self _).trans cap3) lo3
  have h4 := cell_fourth_term lo4 hi4 cap4 fourth_nonpos fourth_nonneg
  have majorant : (c.computedLoss : ℝ) ≤ (c.loss : ℝ) := by
    exact_mod_cast hv.2.1.2.2.2.2.1
  let z := ∑ i ∈ Finset.range 4,
    (tiltCoefficient w (i + 1) x : ℂ) * nearestPole x ^ (i + 1)
  have real_bound : -(c.loss : ℝ) ≤ z.re := by
    dsimp only [z]
    rw [exponent_real x (fun a ↦ tiltCoefficient w a x)]
    unfold Cell.computedLoss at majorant
    push_cast at majorant
    linarith only [majorant, h1, h2, h3, h4]
  change 1 ≤ ‖Complex.exp z‖ * (c.invD : ℝ)
  rw [Complex.norm_exp]
  calc
    1 = exp (-(c.loss : ℝ)) * exp (c.loss : ℝ) := by rw [← exp_add, neg_add_cancel, exp_zero]
    _ ≤ exp z.re * (c.invD : ℝ) := by
      exact mul_le_mul (exp_le_exp.mpr real_bound) (Cell.exponent_bounds hv).2
        (exp_nonneg _) (exp_nonneg _)

#print axioms cell_inverse_amplitude

end LongCycleBounds.FiveCutoff
