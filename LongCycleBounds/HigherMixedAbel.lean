import LongCycleBounds.TripleMixedAbel

/-! Finite Abel slices with an arbitrary number of frozen weighted axes. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset PoleTails

private theorem odd_label_lower (i : ℤ) : 1 ≤ |2*(i:ℝ)+1| := by
  rcases le_or_gt 0 i with hi|hi
  · have : (0:ℝ) ≤ i := by exact_mod_cast hi
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (i:ℝ) ≤ -1 := by exact_mod_cast (show i ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]; linarith

private theorem pair_empty {j k : ℕ} (_hk : 1≤k) (hj : j<2*k) (w u : ℂ) :
    orientedPair j k w u = 0 := by
  simp [orientedPair, Icc_eq_empty_of_lt (by omega : j-k<k)]

/-- One boundary point per frozen slice; natural subtraction also covers rows before birth. -/
theorem shiftedPair_next (p L : ℕ) {k : ℕ} (hk : 1≤k) (w u : ℂ) :
    orientedPair (p+1-L) k w u = u*orientedPair (p-L) k w u +
      if L+2*k ≤ p+1 then weightedPower w (p+1-L-k)*u^k else 0 := by
  split_ifs with h
  · rw [show p+1-L=p-L+1 by omega,orientedPair_next hk (by omega)]
    rfl
  · rw [pair_empty hk (by omega),pair_empty hk (by omega),mul_zero,add_zero]

private theorem pair_all {j k : ℕ} (hk : 1≤k) {c s : ℝ} (hc : c^2+s^2=1)
    (hs : 0 ≤ s) {i m : ℤ} (hi : i≠m) :
    let z := signedOddPole c s
    s*‖orientedPair j k (z i) (z m)‖ ≤ 1/(k:ℝ)*‖z i‖^(k-1)*‖z m‖^(k-1) := by
  dsimp only
  obtain ⟨hz₀,hz,_⟩ := signed_pole_norms hc hs (odd_label_lower i)
  obtain ⟨hw₀,hw,_⟩ := signed_pole_norms hc hs (odd_label_lower m)
  by_cases hj : k≤j
  · exact orientedPair_separated hk hj hz hw hz₀ hw₀ (signed_odd_gap hc hs hi)
  · rw [pair_empty hk (by omega),norm_zero,mul_zero]
    positivity

private theorem weightedPower_bound {a k : ℕ} (_hk : 1≤k) (ha : k≤a) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : ‖weightedPower z a‖ ≤ (1/(a:ℝ))*‖z‖^(k-1) := by
  rw [weightedPower,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (norm_nonneg _) hz (by omega)) (by positivity)

private theorem shiftedPair_centered (p L : ℕ) {k : ℕ} (hk : 1≤k) {c s : ℝ}
    (hc : c^2+s^2=1) (hs : 0 ≤ s) {i m : ℤ} (hi : i≠m) :
    let z := signedOddPole c s
    ‖orientedPair (p+1-L) k (z i) (z m) - (c:ℂ)*orientedPair (p-L) k (z i) (z m)‖ ≤
      ((|2*(m:ℝ)+1|+1)/(k:ℝ))*(‖z i‖^(k-1)*‖z m‖^(k-1)) := by
  dsimp only
  let z := signedOddPole c s
  let K := orientedPair (p-L) k (z i) (z m)
  let v := ‖z i‖^(k-1)*‖z m‖^(k-1)
  have hv : 0≤v := by dsimp [v]; positivity
  have main : s*‖K‖ ≤ 1/(k:ℝ)*v := by
    simpa only [K,v,mul_assoc,z] using pair_all (j:=p-L) hk hc hs hi
  obtain ⟨_,hzi,_⟩ := signed_pole_norms hc hs (odd_label_lower i)
  obtain ⟨_,hzm,hcₘ⟩ := signed_pole_norms hc hs (odd_label_lower m)
  have edge : ‖if L+2*k ≤ p+1 then weightedPower (z i) (p+1-L-k)*(z m)^k else 0‖ ≤
      1/(k:ℝ)*v := by
    split_ifs with h
    · have ha : k≤p+1-L-k := by omega
      have small : 1/((p+1-L-k:ℕ):ℝ) ≤ 1/(k:ℝ) := one_div_le_one_div_of_le
        (by exact_mod_cast (show 0<k by omega) : (0:ℝ)<k) (by exact_mod_cast ha)
      rw [norm_mul,norm_pow]
      calc _ ≤ ((1/((p+1-L-k:ℕ):ℝ))*‖z i‖^(k-1))*‖z m‖^(k-1) :=
                 mul_le_mul (weightedPower_bound hk ha hzi)
                   (pow_le_pow_of_le_one (norm_nonneg _) hzm (by omega)) (by positivity) (by positivity)
           _ ≤ _ := by dsimp [v]; rw [←mul_assoc]; gcongr
    · rw [norm_zero]; positivity
  change ‖orientedPair (p+1-L) k (z i) (z m)-(c:ℂ)*K‖ ≤ _
  rw [shiftedPair_next p L hk]
  change ‖z m*K+_-(c:ℂ)*K‖ ≤ _
  rw [show ∀ e : ℂ, z m*K+e-(c:ℂ)*K = (z m-(c:ℂ))*K+e by intro e; ring]
  apply (norm_add_le ..).trans
  rw [norm_mul]
  calc
    _ ≤ (|2*(m:ℝ)+1| *s)*‖K‖ + 1/(k:ℝ)*v :=
      add_le_add (mul_le_mul_of_nonneg_right hcₘ (norm_nonneg _)) edge
    _ ≤ |2*(m:ℝ)+1| *(1/(k:ℝ)*v) + 1/(k:ℝ)*v := by
      rw [mul_assoc]; exact add_le_add (mul_le_mul_of_nonneg_left main (abs_nonneg _)) le_rfl
    _ = _ := by dsimp [v]; ring

/-- Sum over the frozen axes. The varying pair is retained in its exact support interval. -/
def higherAbelSlice {r : ℕ} (j k b : ℕ) (z : Fin r → ℂ) (w u : ℂ) : ℂ :=
  ∑ a ∈ Fintype.piFinset (fun _ : Fin r ↦ Icc k b),
    (∏ d, weightedPower (z d) (a d))*orientedPair (j-∑ d, a d) k w u

/-- Exact adjacent shell of the higher kernel, on a common finite box. -/
theorem higherAbelSlice_next {r k : ℕ} (hk : 1≤k) (p b : ℕ)
    (z : Fin r → ℂ) (w u : ℂ) :
    higherAbelSlice (p+1) k b z w u = u*higherAbelSlice p k b z w u +
      ∑ a ∈ Fintype.piFinset (fun _ : Fin r ↦ Icc k b),
        (∏ d, weightedPower (z d) (a d)) *
          (if (∑ d, a d)+2*k ≤ p+1 then weightedPower w (p+1-(∑ d, a d)-k)*u^k else 0) := by
  unfold higherAbelSlice
  rw [mul_sum, ←sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [shiftedPair_next p (∑ d, a d) hk, mul_add, mul_left_comm _ u]

private theorem sum_frozen_bound {r k b : ℕ} (hk : 1≤k) (z : Fin r → ℂ)
    (hz : ∀ d, ‖z d‖≤1) (F : (Fin r → ℕ) → ℂ)
    {s C : ℝ} (hs : 0 ≤ s) (hF : ∀ a, s*‖F a‖ ≤ C) :
    s*‖∑ a ∈ Fintype.piFinset (fun _ : Fin r ↦ Icc k b),
       (∏ d, weightedPower (z d) (a d))*F a‖ ≤
      (∑ a ∈ Icc k b, 1/(a:ℝ))^r * (∏ d, ‖z d‖^(k-1))*C := by
  classical
  let S := Fintype.piFinset (fun _ : Fin r ↦ Icc k b)
  let V := ∏ d, ‖z d‖^(k-1)
  have hv : 0≤V := by dsimp [V]; positivity
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) hs).trans
  rw [mul_sum]
  calc
    _ ≤ ∑ a ∈ S, (∏ d, 1/(a d:ℝ))*V*C := by
      apply sum_le_sum
      intro a ha
      have ha' := Fintype.mem_piFinset.mp ha
      have pref : ‖∏ d, weightedPower (z d) (a d)‖ ≤ (∏ d, 1/(a d:ℝ))*V := by
        rw [norm_prod, ←prod_mul_distrib]
        exact prod_le_prod (fun _ _ ↦ norm_nonneg _)
          (fun d _ ↦ weightedPower_bound hk (mem_Icc.mp (ha' d)).1 (hz d))
      rw [norm_mul,mul_left_comm]
      exact mul_le_mul pref (hF a) (by positivity) (by positivity)
    _ = _ := by
      rw [←sum_mul, ←sum_mul]
      congr 2
      exact (sum_pow' (s := Icc k b) (f := fun a : ℕ ↦ 1/(a:ℝ)) (n := r)).symm

/-- Harmonic majorant for any number of frozen axes, without a row-width hypothesis. -/
theorem higherAbelSlice_size {r k b : ℕ} (hk : 1≤k) (j : ℕ) {c s : ℝ}
    (hc : c^2+s^2=1) (hs : 0 ≤ s) (labels : Fin r → ℤ) {i m : ℤ} (hi : i≠m) :
    let z := signedOddPole c s
    s*‖higherAbelSlice j k b (fun d ↦ z (labels d)) (z i) (z m)‖ ≤
      (∑ a ∈ Icc k b, 1/(a:ℝ))^r * (∏ d, ‖z (labels d)‖^(k-1)) *
        (1/(k:ℝ)*‖z i‖^(k-1)*‖z m‖^(k-1)) := by
  dsimp only
  apply sum_frozen_bound hk _ _ _ hs
  · intro a
    exact pair_all hk hc hs hi
  · intro d
    exact (signed_pole_norms hc hs (odd_label_lower (labels d))).2.1

/-- Centered adjacent-row estimate on the same frozen box, including newly born slices. -/
theorem higherAbelSlice_centered {r k b : ℕ} (hk : 1≤k) (p : ℕ) {c s : ℝ}
    (hc : c^2+s^2=1) (hs : 0 ≤ s) (labels : Fin r → ℤ) {i m : ℤ} (hi : i≠m) :
    let z := signedOddPole c s
    let K := fun j ↦ higherAbelSlice j k b (fun d ↦ z (labels d)) (z i) (z m)
    ‖K (p+1)-(c:ℂ)*K p‖ ≤
      (∑ a ∈ Icc k b, 1/(a:ℝ))^r * (∏ d, ‖z (labels d)‖^(k-1)) *
        (((|2*(m:ℝ)+1|+1)/(k:ℝ))*(‖z i‖^(k-1)*‖z m‖^(k-1))) := by
  dsimp only
  let z := signedOddPole c s
  let F (a : Fin r → ℕ) := orientedPair (p+1-∑ d, a d) k (z i) (z m) -
    (c:ℂ)*orientedPair (p-∑ d, a d) k (z i) (z m)
  have eqn : higherAbelSlice (p+1) k b (fun d ↦ z (labels d)) (z i) (z m) -
      (c:ℂ)*higherAbelSlice p k b (fun d ↦ z (labels d)) (z i) (z m) =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin r ↦ Icc k b),
        (∏ d, weightedPower (z (labels d)) (a d))*F a := by
    unfold higherAbelSlice
    rw [mul_sum, ←sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    dsimp [F]
    ring
  rw [eqn, ←one_mul ‖_‖]
  apply sum_frozen_bound hk _ _ _ (by norm_num)
  · intro a
    rw [one_mul]
    exact shiftedPair_centered p (∑ d, a d) hk hc hs hi
  · intro d
    exact (signed_pole_norms hc hs (odd_label_lower (labels d))).2.1

#print axioms shiftedPair_next
#print axioms higherAbelSlice_next
#print axioms higherAbelSlice_size
#print axioms higherAbelSlice_centered

end LongCycleBounds.Band
