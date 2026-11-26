import LongCycleBounds.CycleProfileIndependentWeights

/-! Interlacing readout along an affine line of independently weighted short cycles. -/

noncomputable section

namespace LongCycleBounds.CycleProfile

open Polynomial LongCycles LongCycleFinite Band Finset Real
open MarkedTwo (time)
open scoped Classical

private theorem continuous_line_eval {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {w : ℕ → ℝ}
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) (tail : ∀ a ≥ k, w a = 1) (x : ℝ) :
    Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ (weightedQuotient n (anchorLine w u)).eval x := by
  have eq (u : Set.Icc (0 : ℝ) 1) :=
    eval_eq_sum_range' (p := weightedQuotient n (anchorLine w u)) (n := n)
      (by rw [(weightedQuotient_shape hk hn (anchorLine_unit unit u.2)
        (fun _ ↦ anchorLine_tail hk tail u)).1]; omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦
    ((continuous_line_quotient_coeff n i w).comp continuous_subtype_val).mul continuous_const)

private theorem continuous_line_aeval {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {w : ℕ → ℝ}
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) (tail : ∀ a ≥ k, w a = 1) (x : ℂ) :
    Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ (weightedQuotient n (anchorLine w u)).aeval x := by
  have eq (u : Set.Icc (0 : ℝ) 1) :
      (weightedQuotient n (anchorLine w u)).aeval x =
        ∑ i ∈ range n, ((weightedQuotient n (anchorLine w u)).coeff i : ℂ) * x ^ i := by
    exact eval₂_eq_sum_range' (algebraMap ℝ ℂ)
      (by rw [(weightedQuotient_shape hk hn (anchorLine_unit unit u.2)
        (fun _ ↦ anchorLine_tail hk tail u)).1]; omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦
    (Complex.continuous_ofReal.comp
      ((continuous_line_quotient_coeff n i w).comp continuous_subtype_val)).mul continuous_const)

/-- The sign transfer on the original polynomials uses only their orders of reciprocity. -/
theorem weighted_row_sign {n : ℕ} (hn : 0 < n) (w : ℕ → ℝ)
    (sign : ∀ x : ℝ, 0 ≤ x → normalizedRow w (n - 1) x = 0 →
      0 < normalizedRow w n x * (-deriv (normalizedRow w (n - 1)) x))
    {t : ℝ} (ht : t < 0) (root : (row (n - 1) w).eval t = 0) :
    (row n w).eval t * (row (n - 1) w).derivative.eval t < 0 := by
  let P := row (n - 1) w
  let Q := row n w
  have at_unit (v : ℝ) (hv : v < 0) (left : -1 ≤ v) (hz : P.eval v = 0) :
      Q.eval v * P.derivative.eval v < 0 := by
    let x := -log (-v)
    have hx : 0 ≤ x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have coord : time x = v := by
      simp only [time, x, neg_neg, exp_log (show 0 < -v by linarith)]
    have r : (row (n - 1) w).eval (time x) = 0 := coord.symm ▸ hz
    have out := sign x hx (by simp [normalizedRow, r])
    rw [normalized_deriv_at_zero w x r] at out
    unfold normalizedRow at out
    rw [coord] at out
    have vp : 0 < 1 - v := by linarith
    by_contra! bad
    have hneg : v / ((1 - v) ^ n * (1 - v) ^ (n - 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hv.le (by positivity)
    have nonpos := mul_nonpos_of_nonpos_of_nonneg hneg bad
    exact (not_lt_of_ge nonpos) (out.trans_eq (by dsimp [P, Q]; field_simp))
  by_cases left : -1 ≤ t
  · exact at_unit t ht left root
  have pr (v : ℝ) (hv : v ≠ 0) := row_reciprocal (n - 1) w hv
  have qr := row_reciprocal n w ht.ne
  have ri : P.eval t⁻¹ = 0 :=
    (mul_eq_zero.mp ((pr t ht.ne).trans root)).resolve_left (pow_ne_zero _ ht.ne)
  have inside := at_unit t⁻¹ (inv_lt_zero.mpr ht)
    (by rw [inv_eq_one_div, le_div_iff_of_neg ht]; linarith) ri
  have pd := reciprocal_derivative_at_root P (n - 1) pr ht.ne root
  have e : t ^ 2 * (Q.eval t * P.derivative.eval t) =
      ((-t) * (t ^ (n - 1)) ^ 2) * (Q.eval t⁻¹ * P.derivative.eval t⁻¹) := by
    change t ^ n * Q.eval t⁻¹ = Q.eval t at qr
    rw [← qr, show t ^ n = t ^ (n - 1) * t by conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]]
    linear_combination (t ^ (n - 1) * t * Q.eval t⁻¹) * pd
  exact neg_of_mul_neg_right (e.trans_lt (mul_neg_of_pos_of_neg
    (mul_pos (neg_pos.mpr ht) (sq_pos_of_ne_zero (pow_ne_zero _ ht.ne))) inside)) (sq_nonneg t)

private theorem weighted_quotient_sign {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n) {w : ℕ → ℝ}
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) (tail : ∀ a ≥ k, w a = 1)
    (sign : ∀ x : ℝ, 0 ≤ x → normalizedRow w (n - 1) x = 0 →
      0 < normalizedRow w n x * (-deriv (normalizedRow w (n - 1)) x))
    {t : ℝ} (ht : t < 0) (root : (weightedQuotient (n - 1) w).eval t = 0) :
    (weightedQuotient n w).eval t * (weightedQuotient (n - 1) w).derivative.eval t < 0 := by
  have pf := (weightedQuotient_shape (n := n - 1) hk (by omega) unit tail).2.2.2
  have qf := (weightedQuotient_shape (n := n) hk hkn.le unit tail).2.2.2
  have r : (row (n - 1) w).eval t = 0 := by rw [pf, eval_mul, root, mul_zero]
  have raw := weighted_row_sign (by omega) w sign ht r
  rw [pf, qf, derivative_mul, derivative_X, one_mul] at raw
  simp only [eval_add, eval_mul, eval_X, root, zero_add] at raw
  have alg : (t * (weightedQuotient n w).eval t) *
        (t * (weightedQuotient (n - 1) w).derivative.eval t) =
      t ^ 2 * ((weightedQuotient n w).eval t * (weightedQuotient (n - 1) w).derivative.eval t) :=
    by ring
  rw [alg] at raw
  exact neg_of_mul_neg_right raw (sq_nonneg t)

/-- At any fixed pair, a common sign criterion for all independent short-cycle weights
implies strict quotient interlacing and weak interlacing of the original rows for all those weights. -/
theorem independent_interlacing_of_normalized_sign {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n)
    (sign : ∀ w : ℕ → ℝ, w 1 = 0 → (∀ a, w a ∈ Set.Icc (0 : ℝ) 1) →
      (∀ a ≥ k, w a = 1) → ∀ x : ℝ, 0 ≤ x → normalizedRow w (n - 1) x = 0 →
      0 < normalizedRow w n x * (-deriv (normalizedRow w (n - 1)) x)) :
    ∀ w : ℕ → ℝ, w 1 = 0 → (∀ a, w a ∈ Set.Icc (0 : ℝ) 1) → (∀ a ≥ k, w a = 1) →
      StrictNegativeInterlacing (weightedQuotient (n - 1) w) (weightedQuotient n w) (n - 3) ∧
        WeakRealInterlacing (row (n - 1) w) (row n w) := by
  intro w w1 unit tail
  have hk2 : 2 ≤ k := by omega
  let P (u : Set.Icc (0 : ℝ) 1) := weightedQuotient (n - 1) (anchorLine w u)
  let Q (u : Set.Icc (0 : ℝ) 1) := weightedQuotient n (anchorLine w u)
  have lineUnit (u : Set.Icc (0 : ℝ) 1) := anchorLine_unit unit u.2
  have lineTail (u : Set.Icc (0 : ℝ) 1) (a : ℕ) (ha : k ≤ a) :=
    anchorLine_tail hk2 tail u ha
  have hp (u : Set.Icc (0 : ℝ) 1) :=
    weightedQuotient_shape (n := n - 1) hk2 (by omega) (lineUnit u) (lineTail u)
  have hq (u : Set.Icc (0 : ℝ) 1) :=
    weightedQuotient_shape (n := n) hk2 hkn.le (lineUnit u) (lineTail u)
  have seed : (generalCycleQuotient (n - 1) 2).Splits := by
    obtain ⟨_, _, _, _, _, fac, _, _, _, _, _⟩ := MarkedTwo.derangement_strict (n - 4)
    rw [show n - 4 + 3 = n - 1 by omega] at fac
    rw [fac]
    exact Splits.mul (Splits.C _) (Splits.prod (fun _ _ ↦ Splits.X_sub_C _))
  have all := RootHomotopy.interlacing_of_connected_sign (d := n - 3) P Q
    (fun u ↦ (hp u).2.1) (fun u ↦ (hp u).1.trans (by omega))
    (continuous_line_aeval hk2 (by omega) unit tail)
    (continuous_line_eval hk2 (by omega) unit tail)
    (fun u _ ↦ weightedQuotient_neg_roots hk2 (by omega) (lineUnit u) (lineTail u))
    (fun u ↦ (hq u).2.1) (fun u ↦ (hq u).1.trans (by omega))
    (fun u ↦ by change 0 < (weightedQuotient n (anchorLine w u)).eval 0
                rw [(hq u).2.2.1]
                norm_num)
    (fun u _ ht hz ↦ weighted_quotient_sign hk2 hkn (lineUnit u) (lineTail u)
      (sign _ (anchorLine_singleton w1 u) (lineUnit u) (lineTail u)) ht hz)
    (by
      refine ⟨⟨1, by norm_num⟩, ?_⟩
      change (weightedQuotient (n - 1) (anchorLine w 1)).Splits
      rw [weightedQuotient, row_anchorLine_one, ← row_one (n - 1) 2]
      change (weightedQuotient (n - 1) (profile 2 1)).Splits
      rwa [(weightedQuotient_endpoints (by decide : 2 ≤ 2) (by omega : 0 < n - 1)).2])
  have st : StrictNegativeInterlacing (weightedQuotient (n - 1) w) (weightedQuotient n w)
      (n - 3) := by
    simpa only [P, Q, anchorLine_zero] using all ⟨0, by norm_num⟩
  refine ⟨st, ?_⟩
  rw [(weightedQuotient_shape (n := n - 1) hk2 (by omega) unit tail).2.2.2,
    (weightedQuotient_shape (n := n) hk2 hkn.le unit tail).2.2.2]
  exact weak_mul_X_of_strict st

#print axioms weighted_row_sign
#print axioms independent_interlacing_of_normalized_sign

end LongCycleBounds.CycleProfile
