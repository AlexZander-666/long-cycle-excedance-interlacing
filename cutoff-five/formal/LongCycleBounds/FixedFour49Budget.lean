import LongCycleBounds.FixedFourCoefficients

/-! Explicit middle-region budgets at the closed interface x = 9. -/

noncomputable section
namespace LongCycleBounds.FixedFour49
open Real PoleBridge Band Bulk MarkedTwo FixedCutoff Finset

private theorem endpoint_exp : (8000:ℝ) < exp 9 := by
  calc
    _ < (2718/1000:ℝ)^9 := by norm_num
    _ ≤ (exp 1)^9 := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
    _ = exp 9 := by rw [← exp_nat_mul]; norm_num

private theorem decay {x : ℝ} (hx : 9 ≤ x) {m : ℕ} (hm : m ≤ 6) :
    exp (-x)*x^m ≤ (9:ℝ)^m/8000 := by
  let h := (x-9)/6
  have hp : 0 ≤ h := by dsimp [h]; linarith
  have x0 : 0 ≤ x := by linarith
  have t := add_one_le_exp h
  have bound : x ≤ 9*exp h := by dsimp [h] at t; linarith only [hx,t]
  have b := pow_le_pow_left₀ x0 bound m
  rw [mul_pow,← exp_nat_mul] at b
  have mc : (m:ℝ) ≤ 6 := by exact_mod_cast hm
  have e : exp (-x)*exp ((m:ℝ)*h) ≤ exp (-9) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have mh := mul_le_mul_of_nonneg_right mc hp
    dsimp [h] at mh ⊢
    linarith only [mh]
  calc
    _ ≤ exp (-x)*(9^m*exp ((m:ℝ)*h)) := mul_le_mul_of_nonneg_left b (exp_pos _).le
    _ = 9^m*(exp (-x)*exp ((m:ℝ)*h)) := by ring
    _ ≤ 9^m*exp (-9) := mul_le_mul_of_nonneg_left e (by positivity)
    _ ≤ _ := by
      rw [exp_neg, ← div_eq_mul_inv]
      exact (div_lt_div_of_pos_left (by positivity) (by norm_num) endpoint_exp).le

theorem radius_bounds {x : ℝ} (hx : 9 ≤ x) :
    x ≤ radius x ∧ radius x ≤ (53/50)*x := by
  have rp := radius_pos x
  have x0 : 0 ≤ x := by linarith
  have rs : (radius x)^2 = x^2+π^2 := sq_sqrt (by positivity)
  refine ⟨(sq_le_sq₀ x0 rp.le).mp (by nlinarith only [rs,sq_nonneg π]), ?_⟩
  apply (sq_le_sq₀ rp.le (by positivity)).mp
  have hp : π ≤ 63/20 := by linarith only [pi_lt_d2]
  nlinarith only [rs,pow_le_pow_left₀ pi_pos.le hp 2,
    pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9) hx 2]

private theorem radius_decay {x : ℝ} (hx : 9 ≤ x) {m : ℕ} (hm : m≤6) :
    exp (-x)*(radius x)^m ≤ (53/50:ℝ)^m*9^m/8000 := by
  have p := pow_le_pow_left₀ (radius_pos x).le (radius_bounds hx).2 m
  calc
    _ ≤ exp (-x)*(((53/50)*x)^m) := mul_le_mul_of_nonneg_left p (exp_pos _).le
    _ = (53/50:ℝ)^m*(exp (-x)*x^m) := by rw [mul_pow]; ring
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (decay hx hm) (by positivity)

private theorem cubic_budget {R : ℝ} (hR : 9 ≤ R) :
    R+R^2/2+R^3/6 ≤ (19/81)*R^3 := by
  have hz : 0 ≤ R := by linarith
  nlinarith only [mul_le_mul_of_nonneg_right hR (sq_nonneg R),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9) hR 2) hz]

theorem cost_le {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 9 ≤ x) :
    cost (fun a ↦ tiltCoefficient w a x) (radius x) 3
      ≤ (19/81)*(exp (-x)*(radius x)^3) := by
  have base := (FixedFour.tilt_cost_caps w w1 unit (show 0≤x by linarith) (radius_pos x).le).2
  calc
    _ ≤ _ := base
    _ ≤ exp (-x)*((19/81)*(radius x)^3) :=
      mul_le_mul_of_nonneg_left (cubic_budget (hx.trans (radius_bounds hx).1)) (exp_pos _).le
    _ = _ := by ring

private theorem cost_nonneg (b : ℕ → ℝ) {R : ℝ} (hR : 0≤R) :
    0 ≤ cost b R 3 :=
  sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR _)

theorem cost_small {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 9 ≤ x) :
    cost (fun a ↦ tiltCoefficient w a x) (radius x) 3 ≤ 13/500 := by
  have h := radius_decay hx (m:=3) (by decide)
  norm_num at h
  nlinarith only [cost_le w1 unit hx,h]

private theorem double_cost (b : ℕ → ℝ) {R : ℝ} (hR : 0≤R) :
    cost b (2*R) 3 ≤ 8*cost b R 3 := by
  simp only [cost, mul_sum]
  apply sum_le_sum
  intro i hi
  rw [mul_pow]
  have e : (2:ℝ)^(i+1) ≤ 8 := by
    have hle := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (show i+1≤3 by have := mem_range.mp hi; omega)
    norm_num at hle ⊢
    exact hle
  nlinarith only [mul_le_mul_of_nonneg_right e
    (mul_nonneg (abs_nonneg (b (i+1))) (pow_nonneg hR (i+1)))]

theorem exp_double_bound {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 9 ≤ x) :
    exp (cost (fun a ↦ tiltCoefficient w a x) (2*radius x) 3) ≤ 2 := by
  let b := fun a ↦ tiltCoefficient w a x
  let v := cost b (2*radius x) 3
  have p : 0≤v := cost_nonneg b (mul_nonneg (by norm_num) (radius_pos x).le)
  have h : v ≤ 1/2 := by
    have le := double_cost b (radius_pos x).le
    change v ≤ _ at le
    linarith only [le,cost_small w1 unit hx]
  apply (exp_bound_div_one_sub_of_interval p (by linarith)).trans
  apply (div_le_iff₀ (by linarith)).mpr
  linarith only [h]

theorem head_bound {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 9 ≤ x) {n : ℕ} (hn : 49 ≤ n) :
    (2+2*(radius x)^2/(((n-2:ℕ):ℝ)*π^2))*
      (exp (cost (fun a ↦ tiltCoefficient w a x) (radius x) 3)-1) < s x/5 := by
  let R := radius x
  let v := cost (fun a ↦ tiltCoefficient w a x) R 3
  let D : ℝ := ((n-2:ℕ):ℝ)*π^2
  let Q : ℝ := 47*(157/50)^2
  have rp : 0<R := radius_pos x
  have p : 0≤v := cost_nonneg _ rp.le
  have vs : v≤13/500 := cost_small w1 unit hx
  have vp : v<1 := by linarith
  have e : exp v-1 ≤ (103/100)*v := by
    have h := exp_bound_div_one_sub_of_interval p vp
    have a : 1/(1-v)-1 = v/(1-v) := by
      field_simp [ne_of_gt (show 0 < 1-v by linarith)]
      ring
    have cap : v/(1-v) ≤ (103/100)*v := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith only [mul_nonneg p (show 0≤13/500-v by linarith)]
    linarith only [h,a,cap]
  have pp : (157/50:ℝ)≤π := by linarith only [pi_gt_d2]
  have nc : (47:ℝ) ≤ ((n-2:ℕ):ℝ) := by exact_mod_cast (show 47≤n-2 by omega)
  have qd : Q≤D := mul_le_mul nc (pow_le_pow_left₀ (by norm_num) pp 2) (sq_nonneg _) (by norm_num)
  have qp : 0<Q := by norm_num [Q]
  have dp : 0<D := qp.trans_le qd
  have ratio : 2*R^2/D ≤ 2*R^2/Q :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg R)) qp qd
  have mass : 2+2*R^2/D ≤ 2+2*R^2/Q := add_le_add le_rfl ratio
  have m0 : 0≤2+2*R^2/D :=
    add_nonneg (by norm_num) (div_nonneg (by positivity) dp.le)
  have upper : v≤(19/81)*(exp (-x)*R^3) := cost_le w1 unit hx
  have w4 := radius_decay hx (m:=4) (by decide)
  have w6 := radius_decay hx (m:=6) (by decide)
  change (2+2*R^2/D)*(exp v-1) < s x/5
  apply lt_of_mul_lt_mul_right (a:=R) _ rp.le
  have target : s x/5*R=π/5 := by
    unfold s
    change π/R/5*R=π/5
    field_simp
  rw [target]
  calc
    _ ≤ (2+2*R^2/D)*((103/100)*v)*R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e m0) rp.le
    _ ≤ (2+2*R^2/Q)*((103/100)*((19/81)*(exp (-x)*R^3)))*R := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul mass
        (mul_le_mul_of_nonneg_left upper (by norm_num)) (by positivity) (by positivity)) rp.le
    _ = (103/100)*(19/81)*(2*(exp (-x)*R^4)+2*(exp (-x)*R^6)/Q) := by ring
    _ < _ := by
      dsimp [R,Q]
      norm_num at w4 w6 ⊢
      linarith only [w4,w6,pp]

theorem drift_budget {w : ℕ → ℝ} (unit : ∀ a, w a ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 9 ≤ x) :
    (∑ i∈range 3, |drift w (i+1) x| * (radius x)^(i+2)) ≤ s x := by
  let R := radius x
  have rp : 0<R := radius_pos x
  have cub := mul_le_mul_of_nonneg_left (cubic_budget (hx.trans (radius_bounds hx).1)) rp.le
  have hc : R^2+R^3/2+R^4/6 ≤ (19/81)*R^4 := by
    change R*(R+R^2/2+R^3/6) ≤ R*((19/81)*R^3) at cub
    nlinarith only [cub]
  have b := FixedFour.drift_cost_cap w unit (show 0≤x by linarith) rp.le
  apply b.trans
  rw [s]
  apply (le_div_iff₀ rp).mpr
  calc
    _ ≤ exp (-x)*((19/81)*R^4)*R := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (exp_pos _).le) rp.le
    _ = (19/81)*(exp (-x)*R^5) := by ring
    _ ≤ _ := by
      have h := radius_decay hx (m:=5) (by decide)
      dsimp [R]
      norm_num at h ⊢
      linarith only [h,pi_gt_d2]

#print axioms head_bound
#print axioms drift_budget
end LongCycleBounds.FixedFour49
