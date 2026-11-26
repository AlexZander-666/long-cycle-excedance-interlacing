import LongCycleBounds.MarkedMiddleMass

/-! Order-sensitive pole mass for the middle interval at cutoff four. -/

noncomputable section
namespace LongCycleBounds.FixedFour49
open Real PoleBridge PoleTails Band MarkedTwo Finset

private theorem pole_tail {c s : ℝ} (hu : c^2+s^2=1) (hs : 0 < s)
    {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    ‖pole c s (2*((i:ℝ)+1)+1)^q‖ ≤
      (1/(2*(q:ℝ)*s^2)) * (1/((i:ℝ)+1)-1/((i:ℝ)+2)) := by
  let u : ℝ := (i:ℝ)+1
  let t : ℝ := 4*u*(u+1)*s^2
  have up : 0 < u := by dsimp [u]; positivity
  have t0 : 0 ≤ t := by dsimp [t]; positivity
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have v := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ t)
    (by linarith : 1 ≤ (q:ℝ)/2)
  have exact_den : 1+((2*u+1)^2-1)*s^2 = 1+t := by dsimp [t]; ring
  have b : 2*(q:ℝ)*s^2*u*(u+1) ≤ (1+t)^((q:ℝ)/2) := by
    calc
      _ ≤ 1 + (q:ℝ)/2*t := by dsimp [t]; linarith only [show (0:ℝ) ≤ 1 by norm_num]
      _ ≤ _ := v
  rw [show (i:ℝ)+2 = u+1 by dsimp [u]; ring]
  change ‖pole c s (2*u+1)^q‖ ≤ (1/(2*(q:ℝ)*s^2)) * (1/u-1/(u+1))
  rw [norm_pole_pow _ _ _ hu (by linarith)]
  unfold amplitude
  rw [exact_den, Real.rpow_neg (by positivity)]
  calc
    _ ≤ 1/(2*(q:ℝ)*s^2*u*(u+1)) := by
      rw [← one_div]
      exact one_div_le_one_div_of_le (by positivity) b
    _ = _ := by field_simp; ring

/-- The two nearest poles contribute at most two. The remaining terms
are bounded by a reciprocal quadratic telescope with its order retained. -/
theorem ordered_pole_mass (x : ℝ) {q : ℕ} (hq : 2 ≤ q) :
    (∑' i : ℤ, ‖signedOddPole (c x) (s x) i ^q‖) ≤
      2 + 1/((q:ℝ)*(s x)^2) := by
  let f (i : ℤ) := ‖signedOddPole (c x) (s x) i ^q‖
  let g (i : ℕ) : ℝ := 1/((i:ℝ)+1)
  let D : ℝ := 1/(2*(q:ℝ)*(s x)^2)
  have hs : 0 < s x := div_pos pi_pos (radius_pos x)
  have qp : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have D0 : 0 ≤ D := by dsimp [D]; positivity
  have step (i : ℕ) : f (i+1) ≤ D*(g i-g (i+1)) := by
    simpa only [f,signedOddPole,g,D,Int.cast_add,Int.cast_natCast,Int.cast_one,Nat.cast_succ,
      show ∀ a : ℝ, a+1+1=a+2 by intro a; ring]
      using pole_tail (circle x) hs hq i
  have fin (m : ℕ) : (∑ i∈range m, f (i+1)) ≤ D*(g 0-g m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      linarith only [ih,step m]
  have bounded (m : ℕ) : (∑ i∈range m, f (i+1)) ≤ D := by
    have g0 : g 0=1 := by simp [g]
    exact (fin m).trans (by rw [g0]; nlinarith only [mul_nonneg D0 (show 0 ≤ g m by positivity)])
  have positive (i : ℕ) : 0 ≤ f (i+1) := norm_nonneg _
  have after := Real.tsum_le_of_sum_range_le positive bounded
  have first : f 0 ≤ 1 := by
    simp only [f,signedOddPole,Int.cast_zero,mul_zero,zero_add]
    rw [norm_pole_pow _ _ _ (circle x) (by norm_num)]
    norm_num [amplitude]
  have htail := summable_of_sum_range_le positive bounded
  have sf : Summable (fun i : ℕ ↦ f (i : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add,Nat.cast_one] using htail
  have reflected (i : ℕ) : f (-(i+1:ℤ)) = f i := by
    have conj (l : ℝ) : pole (c x) (s x) (-l) = star (pole (c x) (s x) l) := by
      apply Complex.ext <;> simp [pole]
      ring
    simp only [f,signedOddPole,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one]
    rw [show 2*(-((i:ℝ)+1))+1= -(2*i+1) by ring,conj,←star_pow,norm_star]
  change ∑' i : ℤ, f i ≤ _
  have sa : Summable f := summable_norm_signed_odd_pole x hq
  rw [←tsum_nat_add_neg_add_one sa]
  simp only [reflected,sf.tsum_add sf]
  have sum := sf.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,Nat.cast_add,Nat.cast_one] at sum
  rw [← sum]
  have doubled : 2*D = 1/((q:ℝ)*(s x)^2) := by dsimp [D]; field_simp
  linarith only [after,first,doubled]

theorem logistic_ordered_bound (x : ℝ) (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    |scaledCoeff (logistic (time x)) (radius x) j| ≤
      2 + 1/((↑(j+1):ℝ)*(s x)^2) := by
  rw [logistic_scaled_moment x hj]
  have sm := summable_norm_signed_odd_pole x (q:=j+1) (by omega)
  have bound := (norm_tsum_le_tsum_norm sm).trans (ordered_pole_mass x (q:=j+1) (by omega))
  rw [signed_odd_pole_tsum x hx (by omega),norm_mul,Complex.norm_real,Complex.norm_ofNat,
    Real.norm_eq_abs] at bound
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  simpa [time, mul_comm] using bound

/-- Even for the shortest row of order n-4, the half-convolution uses
pole exponents with twice their value at least n-2. -/
theorem logistic_half_order_bound (x : ℝ) (hx : 0 ≤ x) {n j i : ℕ}
    (hn : 5 ≤ n) (hj : n - 4 ≤ j) (hi : i ≤ j / 2) :
    |scaledCoeff (logistic (time x)) (radius x) (j-i)| ≤
      2 + 2 * (radius x)^2 / (((n-2:ℕ):ℝ)*π^2) := by
  have order : 1 ≤ j-i := by omega
  have idx : ((n-2:ℕ):ℝ) ≤ 2*((j-i+1:ℕ):ℝ) := by
    exact_mod_cast (show n-2 ≤ 2*(j-i+1) by omega)
  have NN : (0:ℝ) < ((n-2:ℕ):ℝ) := by
    exact_mod_cast (show 0 < n-2 by omega)
  have ss : 0 < (s x)^2 := sq_pos_of_pos (div_pos pi_pos (radius_pos x))
  have qpos : (0:ℝ) < ((j-i+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos (j-i))
  have compare :
      1/(((j-i+1:ℕ):ℝ)*(s x)^2) ≤ 2/(((n-2:ℕ):ℝ)*(s x)^2) := by
    rw [div_le_div_iff₀ (mul_pos qpos ss) (mul_pos NN ss), one_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right idx ss.le
  have scale :
      2/(((n-2:ℕ):ℝ)*(s x)^2) = 2*(radius x)^2/(((n-2:ℕ):ℝ)*π^2) := by
    rw [s, div_pow]
    field_simp [ne_of_gt NN, ne_of_gt (radius_pos x), ne_of_gt pi_pos]
  rw [← scale]
  exact (logistic_ordered_bound x hx order).trans (add_le_add (le_refl 2) compare)

#print axioms ordered_pole_mass
#print axioms logistic_ordered_bound
#print axioms logistic_half_order_bound
end LongCycleBounds.FixedFour49
