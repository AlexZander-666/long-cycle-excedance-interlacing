import LongCycleBounds.PoleBridge
import LongCycleBounds.BandMoments

namespace LongCycleBounds.Band
open PoleTails Bulk
noncomputable section

private def odd (i : ℕ) : ℝ := 2*(i:ℝ)+5

private theorem odd_ge (i : ℕ) : 1 ≤ odd i := by
  unfold odd
  have h : 0 ≤ (i:ℝ) := by positivity
  linarith

private theorem tail_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, envelope (odd i)) ≤ 1-2/((n:ℝ)+2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have step : envelope (odd n) ≤ 2/((n:ℝ)+2)-2/((n:ℝ)+1+2) := by
      unfold envelope odd
      have hp : 0 < (2*(n:ℝ)+5)^2+7 := by positivity
      have hr : 0 < (n:ℝ)+2 := by positivity
      have ht : 0 < (n:ℝ)+1+2 := by positivity
      field_simp
      nlinarith
    linarith

private theorem env_nonneg (l : ℝ) : 0 ≤ envelope l := by unfold envelope; positivity

/-- A single envelope suffices for every exponent at least one quarter of p. -/
theorem norm_quarter (c s l : ℝ) (p q : ℕ) (hc : c^2+s^2=1)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) (hl : 1 ≤ l) (hq : (p:ℝ) ≤ 4*(q:ℝ)) :
    ‖pole c s l^q‖ ≤ envelope l := by
  rw [norm_pole_pow _ _ _ hc hl]
  apply le_trans _ (attenuation l s p hl hp ha)
  apply Real.rpow_le_rpow_of_exponent_le
  · have h : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
    linarith [mul_nonneg h (sq_nonneg s)]
  · linarith

theorem quarter_sum (c s : ℝ) (p q : ℕ) (hc : c^2+s^2=1) (hp : 8 ≤ (p:ℝ))
    (ha : 1 ≤ (p:ℝ)*s^2) (hq : (p:ℝ) ≤ 4*(q:ℝ)) :
    Summable (fun i : ℕ ↦ pole c s (odd i)^q) ∧ ‖total c s q‖ ≤ 5/2 := by
  have bound (n : ℕ) : (∑ i ∈ Finset.range n, envelope (odd i)) ≤ 1 :=
    (tail_sum n).trans (sub_le_self _ (by positivity))
  have ss := summable_of_sum_range_le (fun i ↦ env_nonneg (odd i)) bound
  have mass := Real.tsum_le_of_sum_range_le (fun i ↦ env_nonneg (odd i)) bound
  have cmp (i : ℕ) := norm_quarter c s (odd i) p q hc hp ha (odd_ge i) hq
  have normsum := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) cmp ss
  have ts := (norm_tsum_le_tsum_norm normsum).trans ((Summable.tsum_le_tsum cmp normsum ss).trans mass)
  refine ⟨normsum.of_norm,?_⟩
  have b1 := norm_quarter c s 1 p q hc hp ha (by norm_num) hq
  have b3 := norm_quarter c s 3 p q hc hp ha (by norm_num) hq
  rw [show envelope 1=1 by norm_num [envelope]] at b1
  rw [show envelope 3=1/2 by norm_num [envelope]] at b3
  change ‖pole c s 1^q + (pole c s 3^q + ∑' i, pole c s (odd i)^q)‖ ≤ _
  linarith [norm_add_le (pole c s 1^q) (pole c s 3^q + ∑' i, pole c s (odd i)^q),
    norm_add_le (pole c s 3^q) (∑' i, pole c s (odd i)^q)]

#print axioms norm_quarter
#print axioms quarter_sum
end
end LongCycleBounds.Band
