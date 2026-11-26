import LongCycleBounds.BandMoments
import LongCycleBounds.FullStripMixedTerms
import LongCycleBounds.PoleBridge

/-! Absolute convergence and diagonal extraction for the complete two-cycle pole row. -/

namespace LongCycleBounds.Band

open ComplexConjugate Finset PoleBridge PoleTails
open scoped Real

noncomputable section

private theorem odd_abs_ge_one (i : ℤ) : 1 ≤ |2*(i:ℝ)+1| := by
  rcases le_or_gt 0 i with hi | hi
  · have : (0:ℝ) ≤ i := by exact_mod_cast hi
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (i:ℝ) ≤ -1 := by exact_mod_cast (show i ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]
    linarith

private theorem signed_pole_den (x l : ℝ) (hl : 1 ≤ |l|) :
    pole (c x) (s x) l = (radius x : ℂ) / den x l := by
  rcases le_or_gt 0 l with hp | hn
  · exact pole_den x l (by rwa [abs_of_nonneg hp] at hl)
  · have h := pole_den x (-l) (by rwa [abs_of_neg hn] at hl)
    have hleft : pole (c x) (s x) l = conj (pole (c x) (s x) (-l)) := by
      apply Complex.ext <;> simp [pole]
      ring
    have hright : conj (den x (-l)) = den x l := by
      apply Complex.ext <;> simp [den, Complex.add_re, Complex.add_im]
    rw [hleft, h, map_div₀, Complex.conj_ofReal, hright]

/-- Absolute convergence for every moment of order at least two, at any real x. -/
theorem summable_norm_signed_odd_pole (x : ℝ) {q : ℕ} (hq : 2 ≤ q) :
    Summable (fun i : ℤ ↦ ‖signedOddPole (c x) (s x) i ^ q‖) := by
  let g (i : ℤ) : ℝ := 1 / |(i:ℝ)+1/2|^q
  have sg : Summable g := by
    simpa [g] using (Real.summable_one_div_int_add_rpow (1/2) (q:ℝ)).mpr
      (by exact_mod_cast (show 1 < q by omega))
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    (sg.mul_left (radius x ^ q))
  intro i
  have hnorm : |(i:ℝ)+1/2| ≤ ‖den x (2*(i:ℝ)+1)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [den, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_I_im,
      Complex.ofReal_re, show (2*(i:ℝ)+1)*π = ((i:ℝ)+1/2)*(2*π) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2*π)]
    exact le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.pi_gt_three])
  have hpos : 0 < |(i:ℝ)+1/2| := by
    linarith [odd_abs_ge_one i, show |2*(i:ℝ)+1| = 2*|(i:ℝ)+1/2| by
      rw [show 2*(i:ℝ)+1 = 2*((i:ℝ)+1/2) by ring, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
  rw [signedOddPole, signed_pole_den x _ (odd_abs_ge_one i), norm_pow, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (radius_pos x).le, div_pow, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (pow_pos hpos _) (pow_le_pow_left₀ (abs_nonneg _) hnorm q))
    (pow_nonneg (radius_pos x).le q)

/-- The complete signed pole series is exactly twice the scaled moment, as a complex identity. -/
theorem signed_odd_pole_tsum (x : ℝ) (hx : 0 ≤ x) {q : ℕ} (hq : 2 ≤ q) :
    (∑' i : ℤ, signedOddPole (c x) (s x) i ^ q) =
      (2:ℂ) * (scaledMoment (radius x) (-Real.exp (-x)) q : ℂ) := by
  calc
    _ = (radius x : ℂ)^q * oddPoleSum q x := by
      rw [oddPoleSum, ← tsum_mul_left]
      apply tsum_congr
      intro i
      rw [signedOddPole, signed_pole_den x _ (odd_abs_ge_one i), den, div_pow]
      push_cast
      ring
    _ = _ := by
      rw [scaledMoment]
      push_cast
      rw [moment_poles _ hq _ hx]
      have hf : ((q-1).factorial : ℂ) ≠ 0 := by exact_mod_cast (q-1).factorial_ne_zero
      field_simp

private def mixedTerm (x : ℝ) (j a : ℕ) (v : ℤ × ℤ) : ℂ :=
  (interactionWeight j a : ℂ) *
    (signedOddPole (c x) (s x) v.1 ^ a * signedOddPole (c x) (s x) v.2 ^ (j-a))

private theorem mixedTerm_summable_norm (x : ℝ) {j a : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ j-a) :
    Summable (fun v ↦ ‖mixedTerm x j a v‖) := by
  simpa only [mixedTerm, norm_mul (interactionWeight j a : ℂ)] using
    ((summable_norm_signed_odd_pole x ha).mul_norm (summable_norm_signed_odd_pole x hb)).mul_left
      ‖(interactionWeight j a : ℂ)‖

private theorem sum_mixedTerm (x : ℝ) (hx : 0 ≤ x) {j a : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ j-a) :
    (∑' v, mixedTerm x j a v) =
      ((4 * interactionWeight j a * scaledMoment (radius x) (-Real.exp (-x)) a *
        scaledMoment (radius x) (-Real.exp (-x)) (j-a) : ℝ) : ℂ) := by
  unfold mixedTerm
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm
    (summable_norm_signed_odd_pole x ha) (summable_norm_signed_odd_pole x hb),
    signed_odd_pole_tsum x hx ha, signed_odd_pole_tsum x hx hb]
  push_cast
  ring

private theorem full_kernel_summable_norm (x : ℝ) {j k : ℕ} (hk : 2 ≤ k) :
    Summable (fun v : ℤ × ℤ ↦
      ‖mixedPair j k (signedOddPole (c x) (s x) v.1) (signedOddPole (c x) (s x) v.2)‖) := by
  have hs : Summable (fun v ↦ ∑ a ∈ Icc k (j-k), ‖mixedTerm x j a v‖) :=
    summable_sum fun a ha ↦ by
      obtain ⟨hal, hau⟩ := mem_Icc.mp ha
      exact mixedTerm_summable_norm x (by omega) (by omega)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun v ↦ ?_) hs
  simpa only [mixedPair, mixedTerm, mul_assoc] using
    norm_sum_le (Icc k (j-k)) (fun a ↦ mixedTerm x j a v)

/-- Removing the diagonal preserves absolute convergence of the mixed kernel. -/
theorem summable_norm_offDiagonal (x : ℝ) {j k : ℕ} (hk : 2 ≤ k) :
    Summable (fun v : ℤ × ℤ ↦ ‖offDiagonal j k (c x) (s x) v‖) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun v ↦ ?_)
    (full_kernel_summable_norm x (j := j) hk)
  by_cases hv : v.1 = v.2
  · simp [offDiagonal, hv]
  · simp [offDiagonal, hv]

private theorem sum_full_kernel (x : ℝ) (hx : 0 ≤ x) {j k : ℕ} (hk : 2 ≤ k) :
    (∑' v : ℤ × ℤ, mixedPair j k (signedOddPole (c x) (s x) v.1)
      (signedOddPole (c x) (s x) v.2)) =
      ((4 * centeredInteraction (scaledMoment (radius x) (-Real.exp (-x))) k j : ℝ) : ℂ) := by
  have hsum (a : ℕ) (ha : a ∈ Icc k (j-k)) : Summable (mixedTerm x j a) := by
    obtain ⟨hal, hau⟩ := mem_Icc.mp ha
    exact (mixedTerm_summable_norm x (by omega) (by omega)).of_norm
  rw [show (∑' v : ℤ × ℤ, mixedPair j k (signedOddPole (c x) (s x) v.1)
      (signedOddPole (c x) (s x) v.2)) = ∑' v, ∑ a ∈ Icc k (j-k), mixedTerm x j a v by
    simp only [mixedPair, mixedTerm, mul_assoc]]
  rw [Summable.tsum_finsetSum hsum]
  simp only [centeredInteraction, mul_sum, Complex.ofReal_sum]
  apply sum_congr rfl
  intro a ha
  obtain ⟨hal, hau⟩ := mem_Icc.mp ha
  rw [sum_mixedTerm x hx (by omega : 2 ≤ a) (by omega : 2 ≤ j-a)]
  push_cast
  ring

private theorem reciprocal_reflection (j k : ℕ) :
    (∑ a ∈ Icc k (j-k), (1:ℝ)/(j-a:ℕ)) = ∑ a ∈ Icc k (j-k), (1:ℝ)/a := by
  apply sum_nbij (fun a ↦ j-a)
  · intro a ha
    obtain ⟨hal, hau⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb hab
    have h₁ := (mem_Icc.mp ha).2
    have h₂ := (mem_Icc.mp hb).2
    change j-a = j-b at hab
    omega
  · intro b hb
    obtain ⟨hbl, hbu⟩ := mem_Icc.mp hb
    exact ⟨j-b, mem_Icc.mpr ⟨by omega, by omega⟩, by change j-(j-b)=b; omega⟩
  · exact fun _ _ ↦ rfl

private theorem mixedPair_diagonal {j k : ℕ} (hk : 1 ≤ k) (z : ℂ) :
    mixedPair j k z z = (2 * (∑ a ∈ Icc k (j-k), (1:ℝ)/a) : ℝ) * z^j := by
  unfold mixedPair
  calc
    _ = ((∑ a ∈ Icc k (j-k), interactionWeight j a : ℝ):ℂ)*z^j := by
      rw [Complex.ofReal_sum, sum_mul]
      apply sum_congr rfl
      intro a ha
      have hau := (mem_Icc.mp ha).2
      rw [mul_assoc, ← pow_add, show a+(j-a)=j by omega]
    _ = _ := by
      congr 2
      have weight : (∑ a ∈ Icc k (j-k), interactionWeight j a) =
          ∑ a ∈ Icc k (j-k), ((1:ℝ)/a + (1:ℝ)/(j-a:ℕ)) := by
        apply sum_congr rfl
        intro a ha
        obtain ⟨hal, hau⟩ := mem_Icc.mp ha
        exact interactionWeight_eq_add (by omega) (by omega)
      rw [weight, sum_add_distrib, reciprocal_reflection, two_mul]

private theorem split_full_kernel (x : ℝ) {j k : ℕ} (hk : 2 ≤ k) :
    let z := signedOddPole (c x) (s x)
    (∑' v : ℤ × ℤ, mixedPair j k (z v.1) (z v.2)) =
      (∑' i : ℤ, mixedPair j k (z i) (z i)) + ∑' v, offDiagonal j k (c x) (s x) v := by
  dsimp only
  let z := signedOddPole (c x) (s x)
  let kernel (v : ℤ × ℤ) := mixedPair j k (z v.1) (z v.2)
  let D : Set (ℤ × ℤ) := {v | v.1 = v.2}
  let diag (i : ℤ) : ℤ × ℤ := (i, i)
  have hdiag : Function.Injective diag := fun _ _ eq ↦ congrArg Prod.fst eq
  have hs : Summable kernel := (full_kernel_summable_norm x (j := j) hk).of_norm
  have split := hs.tsum_subtype_add_tsum_subtype_compl D
  rw [_root_.tsum_subtype, _root_.tsum_subtype] at split
  change (∑' v, kernel v) = (∑' i, kernel (diag i)) + _
  rw [← split]
  congr 1
  · have supp : Function.support (D.indicator kernel) ⊆ Set.range diag := by
      intro v hv
      have hmem : v ∈ D := by
        by_contra hn
        exact hv (Set.indicator_of_notMem hn kernel)
      exact ⟨v.1, Prod.ext rfl hmem⟩
    rw [← hdiag.tsum_eq supp]
    apply tsum_congr
    intro i
    exact Set.indicator_of_mem (show diag i ∈ D from rfl) _
  · apply tsum_congr
    intro v
    by_cases hv : v.1 = v.2 <;> simp [D, hv, offDiagonal, kernel, z]

/-- The actual two-cycle row is its diagonal multiple plus the absolutely convergent
off-diagonal remainder. The formula includes an empty interaction interval. -/
theorem full_strip_pole_row {k j : ℕ} (hk : 2 ≤ k) (hj : 2 ≤ j) (x : ℝ) (hx : 0 ≤ x) :
    let U := scaledMoment (radius x) (-Real.exp (-x))
    U j + centeredInteraction U k j =
      poleDiagonalFactor j k * U j + poleRemainder j k (c x) (s x) := by
  let U := scaledMoment (radius x) (-Real.exp (-x))
  let z := signedOddPole (c x) (s x)
  let b := ∑ a ∈ Icc k (j-k), (1:ℝ)/a
  have diag : (∑' i : ℤ, mixedPair j k (z i) (z i)) = ((4*b*U j : ℝ):ℂ) := by
    simp only [mixedPair_diagonal (by omega : 1 ≤ k)]
    change (∑' i : ℤ, ((2*b:ℝ):ℂ) * z i ^ j) = _
    rw [tsum_mul_left, signed_odd_pole_tsum x hx hj]
    push_cast
    ring
  have complex_sum : ((4*centeredInteraction U k j : ℝ):ℂ) =
      ((4*b*U j : ℝ):ℂ) + ∑' v, offDiagonal j k (c x) (s x) v := by
    rw [← sum_full_kernel x hx hk, split_full_kernel x hk, diag]
  have real_sum := congrArg Complex.re complex_sum
  simp only [Complex.add_re, Complex.ofReal_re] at real_sum
  change U j + centeredInteraction U k j =
    (1+b)*U j + (∑' v, offDiagonal j k (c x) (s x) v).re/4
  linarith only [real_sum]

theorem poleDiagonalFactor_ge_one (j k : ℕ) : 1 ≤ poleDiagonalFactor j k := by
  unfold poleDiagonalFactor
  exact le_add_of_nonneg_right (sum_nonneg fun a _ ↦ by positivity)

/-- At the first split the preceding row has no mixed terms, even on the signed lattice. -/
theorem pole_split_preceding {k : ℕ} (hk : 1 ≤ k) (c s : ℝ) :
    poleDiagonalFactor (2*k-1) k = 1 ∧ poleRemainder (2*k-1) k c s = 0 := by
  have empty : Icc k (2*k-1-k) = ∅ := Icc_eq_empty_of_lt (by omega)
  constructor
  · simp [poleDiagonalFactor, empty]
  · have zero (v : ℤ × ℤ) : offDiagonal (2*k-1) k c s v = 0 := by
      simp [offDiagonal, mixedPair, empty]
    simp [poleRemainder, zero]

/-- The diagonal multiplier gains one reciprocal at each new two-cycle row. -/
theorem poleDiagonalFactor_next {p k : ℕ} (hk : 1 ≤ k) (h : 2*k ≤ p+1) :
    poleDiagonalFactor (p+1) k = poleDiagonalFactor p k + 1/((p+1-k:ℕ):ℝ) := by
  unfold poleDiagonalFactor
  rw [show p+1-k=p-k+1 by omega, sum_Icc_succ_top (by omega : k ≤ p-k+1)]
  ring

#print axioms summable_norm_signed_odd_pole
#print axioms signed_odd_pole_tsum
#print axioms summable_norm_offDiagonal
#print axioms full_strip_pole_row
#print axioms poleDiagonalFactor_ge_one
#print axioms pole_split_preceding
#print axioms poleDiagonalFactor_next

end
end LongCycleBounds.Band
