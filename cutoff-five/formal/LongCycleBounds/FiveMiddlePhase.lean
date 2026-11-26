import LongCycleBounds.FiveMiddleBudgets
import LongCycleBounds.FixedCutoffAnalyticAssembly

/-! Phase comparison at an adjacent zero and a uniform logistic envelope. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real PoleBridge Band Bulk MarkedTwo FixedCutoff Finset

theorem middle_uniform {x : ℝ} (hx : 9 ≤ x) (j : ℕ) :
    |scaledCoeff (logistic (time x)) (radius x) j| ≤ 2*(radius x)^2/x := by
  have xp : 0 < x := by linarith
  have rp := radius_pos x
  obtain ⟨xl,_⟩ := FixedFour49.radius_bounds hx
  by_cases z : j=0
  · subst j
    simp only [scaledCoeff,logistic,PowerSeries.coeff_mk,logisticMoment,if_true,
      Nat.factorial_zero,Nat.cast_one,div_one,zero_add,pow_one]
    have h : 0<1-time x := by dsimp [time];linarith [exp_pos (-x)]
    rw [abs_of_nonneg (by positivity)]
    have f : 1/(1-time x)≤1 := (div_le_one h).2 (by dsimp [time];linarith [exp_pos (-x)])
    apply (le_div_iff₀ xp).mpr
    have u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left f rp.le) xp.le
    nlinarith only [u,mul_le_mul_of_nonneg_left xl rp.le,sq_nonneg (radius x)]
  · rw [logistic_scaled_moment x (by omega)]
    have sm := summable_norm_signed_odd_pole x (q:=j+1) (by omega)
    have est := (norm_tsum_le_tsum_norm sm).trans (all_pole_mass x xp (q:=j+1) (by omega))
    rw [signed_odd_pole_tsum x xp.le (by omega),norm_mul,Complex.norm_real,Complex.norm_ofNat,
      Real.norm_eq_abs] at est
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact est


private theorem logistic_total {n j : ℕ} (hn : 8≤(n:ℝ)) (hj : 1≤j)
    (hi : (n:ℝ)≤2*((j+1:ℕ):ℝ)) (x : ℝ) (hx : 0≤x) (ang : 1≤(n:ℝ)*(s x)^2) :
    scaledCoeff (logistic (time x)) (radius x) j=2*(total (c x) (s x) (j+1)).re := by
  rw [logistic_scaled_moment x hj]
  congr 1
  rw [time,scaledMoment_poles _ (by omega) _ _ hx]
  have he := congrArg Complex.re (complete_normalization x n (j+1) hn ang hi)
  have eq : radius x^(j+1)*(oddPoleSum (j+1) x).re=2*(total (c x) (s x) (j+1)).re := by
    simpa [Complex.mul_re,←Complex.ofReal_pow] using he
  linarith only [eq]

theorem middle_phase {n : ℕ} (hn : 8 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (angle : 1 ≤ (n:ℝ)*(s x)^2) (Y : ℕ → ℝ)
    (bias : ∀ j, n-4≤j → |Y j-scaledCoeff (logistic (time x)) (radius x) j| < s x/4)
    (zero : Y (n-1) = 0) : s x/2 < |Y n| := by
  let V := scaledCoeff (logistic (time x)) (radius x)
  have nc : (8:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<s x := div_pos pi_pos (radius_pos x)
  have su : s x≤1 := (sq_le_sq₀ hs.le (by norm_num)).mp (by
    nlinarith only [circle x,sq_nonneg (c x)])
  have cu : |c x|≤1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
    rw [sq_abs]
    nlinarith only [circle x,sq_nonneg (s x)]
  have prev := logistic_total nc (by omega : 1≤n-1)
    (by rw [Nat.sub_add_cancel (by omega : 1≤n)];linarith) x hx angle
  rw [Nat.sub_add_cancel (by omega : 1≤n)] at prev
  change V (n-1)=2*(total (c x) (s x) n).re at prev
  have after := logistic_total nc (by omega : 1≤n) (by push_cast;linarith) x hx angle
  change V n=2*(total (c x) (s x) (n+1)).re at after
  have bv (j : ℕ) (h : n-4≤j) : |Y j-V j|<s x/4 := bias j h
  have vz := bv (n-1) (by omega)
  rw [zero,zero_sub,abs_neg] at vz
  have pt : |(total (c x) (s x) n).re| ≤ 1/8 := by
    rw [prev,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at vz
    linarith only [vz,su]
  have phase := central_pole_gap (c x) (s x) n (circle x) hs (by linarith) angle pt
  have dbl : s x < |V n-c x*V (n-1)| := by
    rw [after,prev,show ∀ z w : ℝ, 2*z-c x*(2*w)=2*(z-c x*w) by intro z w;ring,
      abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith only [phase]
  have u := abs_sub (V n) (c x*V (n-1))
  rw [abs_mul] at u
  have w := abs_sub (Y n) (Y n-V n)
  rw [sub_sub_cancel] at w
  nlinarith only [dbl,u,w,bv n (by omega),vz,mul_le_mul_of_nonneg_right cu (abs_nonneg (V (n-1)))]


theorem middle_short_row {n j : ℕ} (hn : 49 ≤ n) (hj : n-5 ≤ j) {x : ℝ} (hx : 0 ≤ x)
    (angle : 1 ≤ (n:ℝ)*(s x)^2) :
    |scaledCoeff (logistic (time x)) (radius x) j| ≤ 2+(n:ℝ)/((n-4:ℕ):ℝ) := by
  have sp : 0 < s x := div_pos pi_pos (radius_pos x)
  have orders : ((n-4:ℕ):ℝ) ≤ (j+1:ℕ) := by exact_mod_cast (show n-4 ≤ j+1 by omega)
  have dest := mul_le_mul_of_nonneg_right orders (sq_nonneg (s x))
  have nn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have d : (0:ℝ) < ((n-4:ℕ):ℝ) := by exact_mod_cast (show 0<n-4 by omega)
  have den : 0 < ((j+1:ℕ):ℝ)*(s x)^2 := by positivity
  apply (FixedFour49.logistic_ordered_bound x hx (by omega : 1≤j)).trans
  apply add_le_add (le_refl 2)
  rw [div_le_div_iff₀ den d,one_mul]
  have t := mul_le_mul_of_nonneg_right angle d.le
  nlinarith only [t,mul_le_mul_of_nonneg_left dest nn]

#print axioms middle_uniform
#print axioms middle_phase
#print axioms middle_short_row
end LongCycleBounds.FiveCutoff
