import Mathlib

/-! Finite two-cycle interactions under a centered bound on consecutive moments. -/

namespace LongCycleBounds.Band

open Finset
open scoped BigOperators

noncomputable section

/-- Weight of an ordered two-cycle term in the normalized row of length `j`. -/
def interactionWeight (j a : ℕ) : ℝ := (j : ℝ) / ((a : ℝ) * ((j - a : ℕ) : ℝ))

/-- The normalized two-cycle contribution of a real sequence of moments. -/
def centeredInteraction (U : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∑ a ∈ Icc k (j - k), interactionWeight j a * U a * U (j - a)

theorem interactionWeight_eq_add {j a : ℕ} (ha : 0 < a) (hb : a < j) :
    interactionWeight j a = 1 / (a : ℝ) + 1 / ((j - a : ℕ) : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hb0 : ((j - a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hb).ne'
  have hab : (a : ℝ) + ((j - a : ℕ) : ℝ) = j := by
    exact_mod_cast (by omega : a + (j - a) = j)
  unfold interactionWeight
  field_simp
  linarith only [hab]

private theorem reciprocal_le {n a : ℕ} (hn : 0 < n) (ha : 0 < a) (h : n ≤ 3 * a) :
    1 / (a : ℝ) ≤ 3 / (n : ℝ) := by
  apply (div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hn)).2
  simpa only [one_mul] using (show (n : ℝ) ≤ 3 * (a : ℝ) by exact_mod_cast h)

theorem interactionWeight_le {k j n a : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hnear : n ≤ 3 * k) (ha : a ∈ Icc k (j - k)) :
    interactionWeight j a ≤ 6 / (n : ℝ) := by
  obtain ⟨ha, hb⟩ := mem_Icc.mp ha
  rw [interactionWeight_eq_add (by omega : 0 < a) (by omega : a < j)]
  have h₁ := reciprocal_le hn (by omega : 0 < a) (by omega : n ≤ 3 * a)
  have h₂ := reciprocal_le hn (by omega : 0 < j - a) (by omega : n ≤ 3 * (j - a))
  exact (add_le_add h₁ h₂).trans_eq (by ring)

theorem interactionWeight_sub_abs {k n a : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hnear : n ≤ 3 * k) (ha : a ∈ Icc k (n - 1 - k)) :
    |interactionWeight n a - interactionWeight (n - 1) a| ≤ 9 / (n : ℝ)^2 := by
  obtain ⟨ha, hb⟩ := mem_Icc.mp ha
  rw [interactionWeight_eq_add (by omega : 0 < a) (by omega : a < n),
      interactionWeight_eq_add (by omega : 0 < a) (by omega : a < n - 1)]
  let x : ℝ := ((n - a : ℕ) : ℝ)
  let y : ℝ := ((n - 1 - a : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast (by omega : 0 < n - a)
  have hy : 0 < y := by
    dsimp only [y]
    exact_mod_cast (by omega : 0 < n - 1 - a)
  have hxy : x = y + 1 := by
    dsimp only [x, y]
    exact_mod_cast (by omega : n - a = n - 1 - a + 1)
  have hdif : 1 / x - 1 / y = -(1 / (x * y)) := by
    rw [hxy]
    field_simp
    ring
  change |1 / (a : ℝ) + 1 / x - (1 / (a : ℝ) + 1 / y)| ≤ _
  rw [show 1 / (a : ℝ) + 1 / x - (1 / (a : ℝ) + 1 / y) = 1 / x - 1 / y by ring, hdif, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (x * y))]
  have hx' := reciprocal_le hn (by omega : 0 < n - a) (by omega : n ≤ 3 * (n - a))
  have hy' := reciprocal_le hn (by omega : 0 < n - 1 - a)
    (by omega : n ≤ 3 * (n - 1 - a))
  change 1 / x ≤ 3 / (n : ℝ) at hx'
  change 1 / y ≤ 3 / (n : ℝ) at hy'
  calc
    1 / (x * y) = (1 / x) * (1 / y) := by ring
    _ ≤ (3 / (n : ℝ)) * (3 / (n : ℝ)) :=
      mul_le_mul hx' hy' (by positivity) (by positivity)
    _ = 9 / (n : ℝ)^2 := by ring

private theorem interactionTerm_abs_le (U : ℕ → ℝ) {k j n a : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hnear : n ≤ 3 * k) (hU : ∀ q ≥ k, |U q| ≤ 3) (ha : a ∈ Icc k (j - k)) :
    |interactionWeight j a * U a * U (j - a)| ≤ 54 / (n : ℝ) := by
  obtain ⟨hal, hau⟩ := mem_Icc.mp ha
  have hU₁ := hU a hal
  have hU₂ := hU (j - a) (by omega)
  have hw := interactionWeight_le hk hn hnear ha
  have hw₀ : 0 ≤ interactionWeight j a := by unfold interactionWeight; positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hw₀]
  calc
    _ ≤ (6 / (n : ℝ)) * 3 * 3 := by gcongr
    _ = _ := by ring

/-- Absolute mass of one interaction, bounded by its actual number of terms. -/
theorem centeredInteraction_abs_le (U : ℕ → ℝ) {k j n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hnear : n ≤ 3 * k) (hU : ∀ q ≥ k, |U q| ≤ 3) :
    |centeredInteraction U k j| ≤ ((Icc k (j - k)).card : ℝ) * (54 / (n : ℝ)) := by
  unfold centeredInteraction
  exact (abs_sum_le_sum_abs _ _).trans
    ((sum_le_sum fun _ ha ↦ interactionTerm_abs_le U hk hn hnear hU ha).trans_eq (by simp))

/-- The lower row at the first split has an empty two-cycle interval. -/
theorem centeredInteraction_before_split (U : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    centeredInteraction U k (2*k-1) = 0 := by
  unfold centeredInteraction
  apply sum_eq_zero
  intro a ha
  obtain ⟨_, _⟩ := mem_Icc.mp ha
  omega

theorem centeredInteraction_preceding_abs_le (U : ℕ → ℝ) {n k d : ℕ} (hn : n = 2*k+d)
    (hk : 0 < k) (hnear : n ≤ 3*k) (hU : ∀ q ≥ k, |U q| ≤ 3) :
    |centeredInteraction U k (n-1)| ≤ 54 * ((d : ℝ) / (n : ℝ)) := by
  have hcard : (Icc k (n-1-k)).card = d := by rw [Nat.card_Icc]; omega
  have hmass := centeredInteraction_abs_le (j := n-1) U hk (by omega : 0 < n) hnear hU
  rw [hcard] at hmass
  exact hmass.trans_eq (by ring)

private theorem centeredTerm_abs_le (U : ℕ → ℝ) (c s : ℝ) {k n a : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hnear : n ≤ 3*k) (hc : |c| ≤ 1)
    (hU : ∀ q ≥ k, |U q| ≤ 3) (hstep : ∀ q ≥ k, |U (q+1) - c * U q| ≤ 6*s)
    (ha : a ∈ Icc k (n-1-k)) :
    |interactionWeight n a * U a * U (n-a) -
      c * (interactionWeight (n-1) a * U a * U (n-1-a))| ≤
      (108 / (n : ℝ)) * s + 81 / (n : ℝ)^2 := by
  obtain ⟨hal, hau⟩ := mem_Icc.mp ha
  have hU₁ := hU a hal
  have hU₂ := hU (n-1-a) (by omega)
  have hidx : n-a = (n-1-a)+1 := by omega
  have hstep' : |U (n-a) - c * U (n-1-a)| ≤ 6*s := by
    rw [hidx]
    exact hstep _ (by omega)
  have hw₀ : 0 ≤ interactionWeight n a := by unfold interactionWeight; positivity
  have hw := interactionWeight_le hk hn hnear (mem_Icc.mpr ⟨hal, by omega⟩ : a ∈ Icc k (n-k))
  have hw' := interactionWeight_sub_abs hk hn hnear ha
  let v := interactionWeight n a * U a * (U (n-a) - c * U (n-1-a))
  let w := c * (interactionWeight n a - interactionWeight (n-1) a) * U a * U (n-1-a)
  have hv : |v| ≤ (108 / (n : ℝ)) * s := by
    dsimp only [v]
    rw [abs_mul, abs_mul, abs_of_nonneg hw₀]
    calc
      _ ≤ (6 / (n : ℝ)) * 3 * (6*s) := by gcongr
      _ = _ := by ring
  have hw'' : |w| ≤ 81 / (n : ℝ)^2 := by
    dsimp only [w]
    simp only [abs_mul]
    calc
      _ ≤ 1 * (9 / (n : ℝ)^2) * 3 * 3 := by gcongr
      _ = _ := by ring
  have hre : interactionWeight n a * U a * U (n-a) -
      c * (interactionWeight (n-1) a * U a * U (n-1-a)) = v + w := by
    dsimp only [v, w]
    ring
  rw [hre]
  exact (abs_add_le v w).trans (add_le_add hv hw'')

/-- The common interval has exactly `d` summands. The upper row adds the
single endpoint `n-k`, including when `d=0`. -/
theorem centeredInteraction_sub_abs_le (U : ℕ → ℝ) (c s : ℝ) {n k d : ℕ} (hn : n = 2*k+d)
    (hk : 0 < k) (hnear : n ≤ 3*k) (hc : |c| ≤ 1)
    (hU : ∀ q ≥ k, |U q| ≤ 3) (hstep : ∀ q ≥ k, |U (q+1) - c * U q| ≤ 6*s) :
    |centeredInteraction U k n - c * centeredInteraction U k (n-1)| ≤
      108 * ((d : ℝ) / (n : ℝ)) * s + 81 * (d : ℝ) / (n : ℝ)^2 + 54 / (n : ℝ) := by
  have hn₀ : 0 < n := by omega
  let term (j a : ℕ) := interactionWeight j a * U a * U (j-a)
  let lower := Icc k (n-1-k)
  have hsplit : Icc k (n-k) = insert (n-k) lower := by
    ext a
    dsimp only [lower]
    simp only [mem_Icc, mem_insert]
    omega
  have hnew : n-k ∉ lower := by
    dsimp only [lower]
    rw [mem_Icc]
    omega
  have hlower : lower.card = d := by
    dsimp only [lower]
    rw [Nat.card_Icc]
    omega
  have hmem : n-k ∈ Icc k (n-k) := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hend : |term n (n-k)| ≤ 54 / (n : ℝ) :=
    interactionTerm_abs_le U hk hn₀ hnear hU hmem
  have hsum : |∑ a ∈ lower, (term n a - c * term (n-1) a)| ≤
      (d : ℝ) * ((108 / (n : ℝ)) * s + 81 / (n : ℝ)^2) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _a ∈ lower, ((108 / (n : ℝ)) * s + 81 / (n : ℝ)^2) :=
        sum_le_sum fun _ ha ↦ centeredTerm_abs_le U c s hk hn₀ hnear hc hU hstep ha
      _ = _ := by rw [sum_const, nsmul_eq_mul, hlower]
  change |(∑ a ∈ Icc k (n-k), term n a) - c * ∑ a ∈ lower, term (n-1) a| ≤ _
  rw [hsplit, sum_insert hnew, mul_sum, add_sub_assoc, ← sum_sub_distrib]
  exact ((abs_add_le _ _).trans (add_le_add hend hsum)).trans_eq (by ring)

/-- The strict interaction estimate in the linear band. The moment
bounds are needed only at exponents at least `k`. -/
theorem centeredInteraction_lt (U : ℕ → ℝ) (c s : ℝ) {n k d : ℕ} (hn : n = 2*k+d)
    (hN : 1000000 ≤ n) (hband : 10000*d ≤ n) (hc : |c| ≤ 1)
    (hs : 0 ≤ s) (hangle : 1 ≤ (n : ℝ) * s^2)
    (hU : ∀ q ≥ k, |U q| ≤ 3) (hstep : ∀ q ≥ k, |U (q+1) - c * U q| ≤ 6*s) :
    |centeredInteraction U k n - c * centeredInteraction U k (n-1)| < (13/200 : ℝ)*s := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlarge : (1000 : ℝ)^2 ≤ n := by
    norm_num
    exact_mod_cast hN
  have hsq : (1000 : ℝ)^2 ≤ ((n : ℝ)*s)^2 := by
    calc
      _ ≤ (n : ℝ) := hlarge
      _ ≤ (n : ℝ) * ((n : ℝ) * s^2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hangle hn₀.le
      _ = _ := by ring
  have hbound : (1000 : ℝ) ≤ (n : ℝ)*s :=
    (sq_le_sq₀ (by norm_num) (mul_nonneg hn₀.le hs)).mp hsq
  have hrec : 1 / (n : ℝ) ≤ s / 1000 := by
    apply (div_le_div_iff₀ hn₀ (by norm_num)).2
    simpa only [one_mul, mul_comm] using hbound
  have hs₀ : 0 < s := by
    by_contra! he
    have bad := mul_nonpos_of_nonneg_of_nonpos hn₀.le he
    linarith only [hbound, bad]
  have hd : (d : ℝ) / (n : ℝ) ≤ 1 / 10000 := by
    apply (div_le_iff₀ hn₀).2
    have hcast : (10000 : ℝ) * (d : ℝ) ≤ n := by exact_mod_cast hband
    calc
      (d : ℝ) ≤ (n : ℝ) / 10000 := (le_div_iff₀ (by norm_num)).2 (by simpa [mul_comm] using hcast)
      _ = (1 / 10000 : ℝ) * n := by ring
  refine (centeredInteraction_sub_abs_le U c s hn (by omega) (by omega) hc hU hstep).trans_lt ?_
  calc
    _ = 108 * ((d : ℝ) / n) * s + 81 * (((d : ℝ) / n) * (1 / n)) + 54 * (1 / (n : ℝ)) := by ring
    _ ≤ 108 * (1 / 10000 : ℝ) * s + 81 * ((1 / 10000 : ℝ) * (s / 1000)) + 54 * (s / 1000) := by
      gcongr
    _ < (13/200 : ℝ)*s := by linarith only [hs₀]

end
end LongCycleBounds.Band
