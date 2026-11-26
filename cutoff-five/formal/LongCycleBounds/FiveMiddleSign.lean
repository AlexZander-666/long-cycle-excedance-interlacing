import LongCycleBounds.FiveMiddlePhase
import LongCycleBounds.FixedFour49Tilt
import LongCycleBounds.CycleProfileInsertion
import LongCycleFinite.K5MiddleCert.HeadPrefactor

/-! The four-mark insertion gap on the middle interval of the logarithmic root coordinate. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real PoleBridge Band Bulk MarkedTwo FixedCutoff Finset LongCycleFinite.K5MiddleCert

theorem middle_bias {w : ℕ → ℝ} (w1 : w 1 = 0) (wt : ∀ a ≥ 5, w a = 1)
    (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) {x : ℝ} (hx : 11 ≤ x)
    {p j : ℕ} (hp : 48 ≤ p) (hj : p+1-5 ≤ j) (outer : x ≤ 3*sqrt (p:ℝ)) :
    |scaledCoeff (profileSeries w 5 x) (radius x) j -
      scaledCoeff (logistic (time x)) (radius x) j| < s x/4 := by
  let n := p+1
  let R := radius x
  let b := fun a ↦ tiltCoefficient w a x
  let M : ℝ := 2+2*R^2/(((n-3:ℕ):ℝ)*π^2)
  let L : ℝ := 2*R^2/x
  have xp : 0 < x := by linarith
  have rp : 0 < R := radius_pos x
  have sr : 0 < s x := div_pos pi_pos rp
  have hn : 49≤n := by dsimp [n]; omega
  have ra : R ≤ (alpha:ℝ)*x := radius_le_alpha hx
  have est := FixedFour49.split_tilt_bias b (middle_b_nonneg w1 wt unit hx) 4 j rp
    (show 0 ≤ M by dsimp [M]; positivity) (show 0 ≤ L by dsimp [L]; positivity)
    (logistic (time x)) (fun i hi ↦ middle_half_order x xp.le hn hj hi)
    (fun i _ ↦ middle_uniform (by linarith : 9≤x) i)
  obtain ⟨small,wide⟩ := middle_costs w1 unit hx
  have v0' : 0 ≤ cost b R 4 :=
    sum_nonneg (fun i _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg rp.le _))
  have raw := middle_profile_cost w1 unit xp.le (hx.trans (FixedFour49.radius_bounds
    (by linarith : 9 ≤ x)).1)
  have cc : (C:ℝ) = 657/10648 := by norm_num [C]
  have hh : M*(exp (cost b R 4)-1) ≤ (head:ℝ)*s x :=
    head_prefactor hn hx rp ra v0' (by simpa only [cc] using raw) small
  have pre := (div_lt_iff₀ (mul_pos pi_pos xp)).mp (tail_prefactor hp hx outer rp.le ra)
  have lbound : L ≤ 7*(n:ℝ)*s x := by
    change 2*R^2/x ≤ 7*(n:ℝ)*(π/R)
    rw [←mul_div_assoc,div_le_div_iff₀ xp rp]
    dsimp only [n]
    nlinarith only [pre]
  have t0 : 0 ≤ (1/2:ℝ)^(j/2) := by positivity
  have tbound : L*(1/2:ℝ)^(j/2)*exp (cost b (2*R) 4) ≤ (tail:ℝ)*s x := by
    calc
      _ ≤ (7*(n:ℝ)*s x)*(1/2:ℝ)^(j/2)*2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right lbound t0) wide.le (exp_pos _).le (by positivity)
      _ = (14*(n:ℝ)/2^(j/2))*s x := by rw [div_pow]; simp only [one_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (tail_bound hn hj) sr.le
  have both := mul_lt_mul_of_pos_right head_add_tail_lt sr
  change |scaledCoeff (tilt b 4*logistic (time x)) R j - _| < _
  linarith only [est,hh,tbound,both]

theorem middle_sign {w : ℕ → ℝ} (w1 : w 1 = 0) (wt : ∀ a ≥ 5, w a = 1)
    (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) {x : ℝ} (hx : 11 ≤ x)
    {p : ℕ} (hp : 48 ≤ p) (outer : x ≤ 3*sqrt (p:ℝ))
    (zero : CycleProfile.normalizedRow w p x=0) :
    0 < CycleProfile.normalizedRow w (p+1) x * (-deriv (CycleProfile.normalizedRow w p) x) := by
  let n := p+1
  let R := radius x
  let Y := scaledCoeff (profileSeries w 5 x) R
  let V := scaledCoeff (logistic (time x)) R
  have hn : 49 ≤ n := by dsimp [n]; omega
  have h0 : 0 ≤ x := by linarith
  have rp : 0 < R := radius_pos x
  have sr : 0 < s x := div_pos pi_pos rp
  have su : s x ≤ 1 := by nlinarith [circle x,sq_nonneg (c x),sq_nonneg (s x-1)]
  have ang : 1 ≤ (n:ℝ)*(s x)^2 := by
    have v := fixed_central_angle (n:=p+2) (by omega) x h0
      (by simpa only [Nat.add_sub_cancel] using outer)
    simpa [n,Nat.cast_add] using v
  have yz : Y (n-1)=0 := by
    change scaledCoeff (profileSeries w 5 x) (radius x) p=0
    rw [scaled_eq_gain (by decide : 2≤5) w w1 wt h0,zero,mul_zero]
  have bias (j : ℕ) (hj : n-5 ≤ j) : |Y j-V j| < s x/4 := middle_bias w1 wt unit hx hp hj outer
  have beyond := middle_phase (by omega : 8≤n) h0 ang Y (fun j hj ↦ bias j (by omega)) yz
  have sh (j : ℕ) (hj : n-5 ≤ j) : |Y j| ≤ 4 := by
    have tri := abs_sub_le (Y j) (V j) 0
    simp only [sub_zero] at tri
    have vv : |V j| ≤ _ := middle_short_row hn hj h0 ang
    linarith only [tri,vv,bias j hj,bare_mass_reserve hn,su]
  have driftBound := middle_drift_sum unit hx
  have cap : |∑ i∈range 4, drift w (i+1) x*R^(i+2)*Y (n-(i+2))| ≤ 4*((J:ℝ)*s x) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ i∈range 4, (|drift w (i+1) x| * R^(i+2))*4 := by
        apply sum_le_sum
        intro i hi
        rw [abs_mul,abs_mul,abs_of_pos (pow_pos rp _)]
        have ib := mem_range.mp hi
        exact mul_le_mul_of_nonneg_left (sh _ (by omega))
          (mul_nonneg (abs_nonneg _) (pow_nonneg rp.le _))
      _ ≤ _ := by rw [←sum_mul,mul_comm 4]; exact mul_le_mul_of_nonneg_right driftBound (by norm_num)
  apply scaled_gap_to_normalized_sign (by decide : 2≤5) (by omega : 5-1≤p)
    w w1 wt h0 rp (CycleProfile.normalizedRow_insertion (by decide : 3≤5) (by omega) w w1 wt x)
  change |(∑ i∈range 4, drift w (i+1) x*R^(i+2)*Y (n-(i+2)))/((p:ℝ)+1)| < |Y n|
  apply lt_trans _ beyond
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  rw [← show (n:ℝ)=(p:ℝ)+1 by simp [n], abs_div,abs_of_pos np,div_lt_iff₀ np]
  have h := (div_lt_iff₀ np).mp (insertion_reserve hn)
  nlinarith only [mul_lt_mul_of_pos_right h sr,cap]

#print axioms middle_bias
#print axioms middle_sign
end LongCycleBounds.FiveCutoff
