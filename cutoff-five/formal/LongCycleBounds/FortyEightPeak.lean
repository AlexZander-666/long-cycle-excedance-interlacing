import LongCycleBounds.OuterLow

/-! Sharp peak localization in the steep region, including the successor row. -/
noncomputable section
namespace LongCycleBounds.Outer.FortyEight
open Real Finset

theorem mode_one_bound (N : ℕ) (hN : 48 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : (29/10:ℝ)*sqrt N ≤ x) : (mode N x hx : ℝ)+1 ≤ Real.sqrt N/2 := by
  have pr : (48:ℝ)≤N := by exact_mod_cast hN
  have hs := sq_sqrt (show 0≤(N:ℝ) by positivity)
  have hr : (27/4:ℝ) ≤ sqrt N := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    linarith only [pr,hs]
  have pos : 0<sqrt (N:ℝ) := by linarith
  have hi := mode_index_mul_le N x hx
  have bound := mul_le_mul_of_nonneg_left hregion (Nat.cast_nonneg (mode N x hx))
  have mm : (29/10:ℝ)*(mode N x hx:ℝ) ≤ sqrt N := by
    apply le_of_mul_le_mul_right (a:=sqrt (N:ℝ)) _ pos
    nlinarith only [hi,bound,hs]
  linarith

private theorem exp_small : exp (-4) < 1/50 := by
  rw [exp_neg,inv_lt_comm₀ (exp_pos _) (by norm_num)]
  have hh : (27/10 : ℝ)<exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 27/10) (by decide : 4 ≠ 0)
  rw [← exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem right_succ_decay (N : ℕ) (hN : 48≤N) (x : ℝ) (hx : 0<x)
    (hregion : (29/10:ℝ)*sqrt N≤x) {j : ℕ} (hj : mode N x hx<j) :
    weight N x (j+1) ≤ (1/50 : ℝ)*weight N x j := by
  let m := mode N x hx
  have hb : ratio N x (m+1) ≤ (1/50:ℝ) := by
    by_cases hh : (m:ℝ)+2 ≤ sqrt N/2
    · have hr := ratio_contracts N x m hh
      exact hr.trans (by linarith [ratio_mode_le N x hx])
    · have hs : 6 ≤ sqrt (N:ℝ) := by
        rw [le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast (show 6^2≤N by omega)
      have hsq := sq_sqrt (show 0≤(N:ℝ) by positivity)
      have hdiv : (N:ℝ)/((m:ℝ)+2) ≤ 2*sqrt N := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_nonneg (show 0≤(m:ℝ)+2-sqrt N/2 by linarith) (sqrt_nonneg (N:ℝ))]
      have he := ratio_le_exp N x (m+1)
      push_cast at he
      have hindex : (m:ℝ)+1+1=m+2 := by ring
      rw [hindex] at he
      exact he.trans ((exp_le_exp.mpr (show (N:ℝ)/((m:ℝ)+2)-x≤ -4 by linarith)).trans exp_small.le)
  rw [weight_succ]
  exact mul_le_mul_of_nonneg_right ((ratio_antitone N x (show m+1≤j from hj)).trans hb) (weight_pos ..).le

theorem left_succ_decay (N : ℕ) (hN : 48 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : (29/10:ℝ)*sqrt N ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    leftAt (weight N x) (mode N x hx) (d+1) ≤ (1/50 : ℝ)*leftAt (weight N x) (mode N x hx) d := by
  let m := mode N x hx
  by_cases he : d+1 ≤ m
  · let j := m-(d+1)
    have hj : j+1 = m-d := by dsimp [j]; omega
    have hbf : j+1 < mode N x hx := by change j+1 < m; omega
    have hcast : (j : ℝ)+1 ≤ (mode N x hx : ℝ) := by exact_mod_cast (show j+1 ≤ mode N x hx by omega)
    have he' := ratio_contracts N x j (by linarith [mode_one_bound N hN x hx hregion])
    have hr := (one_lt_ratio_before N x hx hbf).le.trans he'
    change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_pos he, leftAt, if_pos (by omega : d ≤ m), ← hj]
    change weight N x j ≤ _ * weight N x (j+1)
    rw [weight_succ, ← mul_assoc]
    exact le_mul_of_one_le_left (weight_pos ..).le hr
  · change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_neg he]
    exact mul_nonneg (by norm_num) (leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..)

theorem neighbors_product (N : ℕ) (hN : 48 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : (29/10:ℝ)*sqrt N ≤ x) :
    let m := mode N x hx
    leftAt (weight N x) m 1 * weight N x (m+1) ≤ (1/50 : ℝ)*weight N x m ^ 2 := by
  dsimp only
  generalize hm : mode N x hx = m
  cases m with
  | zero => simp [leftAt]; positivity
  | succ j =>
    have h := mode_one_bound N hN x hx hregion
    rw [hm] at h
    push_cast at h
    have hr := ratio_contracts N x j (by linarith)
    simp only [leftAt, if_pos (show 1 ≤ j+1 by omega), Nat.add_one_sub_one]
    rw [weight_succ N x (j+1), weight_succ N x j]
    nlinarith [mul_le_mul_of_nonneg_right hr
      (mul_nonneg (ratio_pos N x j).le (sq_nonneg (weight N x j)))]

theorem neighbors_min_le (N : ℕ) (hN : 48 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : (29/10:ℝ)*sqrt N ≤ x) :
    let m := mode N x hx
    min (leftAt (weight N x) m 1) (weight N x (m+1)) ≤ weight N x m/7 := by
  dsimp only
  have hp := neighbors_product N hN x hx hregion
  dsimp only at hp
  by_contra! bad
  rw [lt_min_iff] at bad
  have hh := mul_lt_mul_of_pos_left bad.2 (weight_pos N x (mode N x hx))
  have hmp := mul_lt_mul_of_pos_right bad.1 (weight_pos N x (mode N x hx+1))
  nlinarith [sq_pos_of_pos (weight_pos N x (mode N x hx))]

theorem both_geometric (N : ℕ) (hN : 48 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : (29/10:ℝ)*sqrt N ≤ x) (l : ℕ) :
    let m := mode N x hx
    leftAt (weight N x) m (l+1) ≤ (1/50 : ℝ)^l*weight N x m ∧
      weight N x (m+(l+1)) ≤ (1/50 : ℝ)^l*weight N x m := by
  let m := mode N x hx
  change leftAt (weight N x) m (l+1) ≤ _ ∧ weight N x (m+(l+1)) ≤ _
  induction l with
  | zero =>
    simp only [zero_add, pow_zero, one_mul]
    constructor
    · unfold leftAt
      split
      · exact weight_le_mode ..
      · exact (weight_pos ..).le
    · exact weight_le_mode ..
  | succ l ih =>
    have hl := left_succ_decay N hN x hx hregion (l+1) (by omega)
    have hr := right_succ_decay N hN x hx hregion (j := m+(l+1)) (by change m < _; omega)
    constructor
    · exact hl.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.1 (by norm_num))
    · exact hr.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.2 (by norm_num))



private theorem sum_left (f : ℕ → ℝ) (m : ℕ) :
    ∑' j : ℕ, leftAt f m (j+1) = ∑ j ∈ range m, f j := by
  rw [tsum_eq_sum (s := range m) (fun j hj ↦ by
    have h : ¬ j+1 ≤ m := by simpa [Finset.mem_range] using hj
    simp [leftAt, h])]
  rw [← sum_range_reflect f m]
  apply sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  simp [leftAt, show j+1 ≤ m by omega, show m-(j+1) = m-1-j by omega]

theorem mass_at_peak (n : ℕ) (hn : 48 ≤ n) (x : ℝ) (hx : 0 < x)
    (region : (29/10:ℝ)*sqrt n ≤ x) :
    ∑' j, weight n x j ≤ 4*weight n x (mode n x hx) := by
  let m := mode n x hx
  let w := weight n x
  let W := w m
  let g (j : ℕ) : ℝ := (1/50:ℝ)^j*W
  have wp : 0 < W := weight_pos ..
  have geo : HasSum g ((1-(1/50:ℝ))⁻¹*W) :=
    (hasSum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/50:ℝ)‖<1)).mul_right W
  have left (j : ℕ) : leftAt w m (j+1)≤g j := (both_geometric n hn x hx region j).1
  have right (j : ℕ) : w (j+(m+1))≤g j := by
    simpa only [show j+(m+1)=m+(j+1) by omega] using (both_geometric n hn x hx region j).2
  have ls : Summable (fun j : ℕ ↦ leftAt w m (j+1)) :=
    geo.summable.of_nonneg_of_le (fun j ↦ leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..) left
  have rs : Summable (fun j : ℕ ↦ w (j+(m+1))) := (summable_nat_add_iff _).mpr (summable_weight n x hx)
  have lb := ls.tsum_le_tsum left geo.summable
  have rb := rs.tsum_le_tsum right geo.summable
  rw [sum_left] at lb
  rw [geo.tsum_eq] at lb rb
  have split := (summable_weight n x hx).sum_add_tsum_nat_add (m+1)
  change ∑ i ∈ range (m+1), w i + ∑' j, w (j+(m+1)) = ∑' j, w j at split
  rw [sum_range_succ] at split
  change ∑' j, w j ≤ 4*W
  change 0 < w m at wp
  dsimp [W] at lb rb ⊢
  linarith

theorem region_next {p : ℕ} (hp : 48 ≤ p) {x : ℝ} (h : 3*sqrt p ≤ x) :
    (29/10:ℝ)*sqrt ((p+1:ℕ):ℝ) ≤ x := by
  apply le_trans _ h
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt (by positivity),Nat.cast_succ]
  have pr : (48:ℝ)≤p := by exact_mod_cast hp
  linarith

#print axioms mass_at_peak
#print axioms both_geometric
#print axioms region_next
end LongCycleBounds.Outer.FortyEight
