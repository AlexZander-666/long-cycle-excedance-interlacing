import LongCycleBounds.BandCentral

namespace LongCycleBounds.Band
open PoleTails PoleBridge Bulk
open scoped Real
noncomputable section

/-- A telescoping bound for all positive odd poles, including the leading pole. -/
private theorem weighted_step (i : ℕ) :
    (2*(i:ℝ)+1) * envelope (2*i+1)^2  ≤  6/((i:ℝ)+1)-6/((i:ℝ)+2) := by
  cases i with
  | zero => norm_num [envelope]
  | succ i =>
    push_cast
    unfold envelope
    have hi : 0  ≤  (i:ℝ) := by positivity
    field_simp
    rw [← sub_nonneg]
    ring_nf
    positivity

private def major (i : ℕ) : ℝ := (2*(i:ℝ)+1)*envelope (2*i+1)^2

private theorem major_bound (n : ℕ) :
    ∑ i ∈ Finset.range n, major i  ≤  6-6/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (n:ℝ)+1+1 = n+2 by ring]
    linarith [show major n  ≤  6/((n:ℝ)+1)-6/((n:ℝ)+2) from weighted_step n]

/-- A centered difference of the *entire* normalized odd-pole sum. -/
theorem half_centered_difference (c s : ℝ) (p q : ℕ) (hc : c^2+s^2=1)
    (hs : 0 ≤ s) (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) (hq : (p:ℝ) ≤ 2*(q:ℝ)) :
    ‖total c s (q+1)-(c:ℂ)*total c s q‖  ≤  6*s := by
  have hn (i : ℕ) : 0 ≤ major i := by dsimp [major]; positivity
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, major i  ≤  6 :=
    (major_bound n).trans (sub_le_self _ (by positivity))
  have sm := summable_of_sum_range_le hn hsum
  have tm := Real.tsum_le_of_sum_range_le hn hsum
  let z (i : ℕ) := pole c s (2*(i:ℝ)+1)
  have localEst (i : ℕ) : ‖z i^(q+1)-(c:ℂ)*z i^q‖  ≤  major i*s := by
    let l := 2*(i:ℝ)+1
    have hl : 1 ≤ l := by dsimp [l]; linarith [show (0:ℝ) ≤ i by positivity]
    have hz : ‖z i^q‖  ≤  envelope l^2 := by
      change ‖pole c s l ^q‖  ≤  _
      rw [norm_pole_pow _ _ _ hc hl]
      exact decay_half _ _ p q hl hp ha hq
    rw [show z i^(q+1)-(c:ℂ)*z i^q = z i^q*(z i-(c:ℂ)) by ring, norm_mul]
    calc _  ≤  envelope l^2*(l*s) :=
          mul_le_mul hz (norm_centered _ _ _ hc hl hs) (norm_nonneg _) (sq_nonneg _)
         _ = _ := by dsimp [major,l]; ring
  have normSum := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) localEst (sm.mul_right s)
  have hh := (norm_tsum_le_tsum_norm normSum).trans
    (Summable.tsum_le_tsum localEst normSum (sm.mul_right s))
  obtain ⟨u,eu⟩ := positive_half c s p q hc hp ha hq
  obtain ⟨v,ev⟩ := positive_half c s p (q+1) hc hp ha (by push_cast; linarith)
  rw [← eu, ← ev, ← tsum_mul_left, ← v.tsum_sub (u.mul_left (c:ℂ))]
  rw [tsum_mul_right] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right tm hs)

/-- The angular condition needed for every q≥k, over a band wider than the target. -/
theorem centered_angle {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) (hwidth : 2*n ≤ 5*k)
    (x : ℝ) (hx : 0 ≤ x) (upper : x ≤ 5/2*Real.sqrt (n-2 : ℕ)) :
    1 ≤ ((2*k:ℕ):ℝ)*s x^2 := by
  have sq := mul_self_le_mul_self hx upper
  have hr : radius x^2=x^2+π^2 := Real.sq_sqrt (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ ((n-2:ℕ):ℝ) by positivity)
  rw [Nat.cast_sub hn] at sq hs
  norm_num at sq hs
  have xBound : x^2 ≤ 25/4*((n:ℝ)-2) := by nlinarith only [sq,hs]
  have piconst : 9 ≤ π^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (π-3)]
  have width : 2*(n:ℝ) ≤ 5*k := by exact_mod_cast hwidth
  have kr : 4 ≤ (k:ℝ) := by exact_mod_cast hk
  have pk : 0 ≤ 2*(k:ℝ)-1 := by linarith
  unfold s
  rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos (radius_pos x)),one_mul,hr]
  push_cast
  nlinarith only [xBound,mul_nonneg pk (sub_nonneg.mpr piconst),width,kr]

private theorem scaled_eq_half {k q : ℕ} (hk : 4 ≤ k) (hq : k ≤ q)
    (x : ℝ) (hx : 0 ≤ x) (ha : 1 ≤ ((2*k:ℕ):ℝ)*s x^2) :
    scaledMoment (radius x) (-Real.exp (-x)) q = (total (c x) (s x) q).re := by
  rw [scaledMoment_poles _ (by omega : 2 ≤ q) _ _ hx]
  have hp : 8 ≤ ((2*k:ℕ):ℝ) := by exact_mod_cast (show 8 ≤ 2*k by omega)
  have hq' : ((2*k:ℕ):ℝ) ≤ 2*(q:ℝ) := by exact_mod_cast (show 2*k ≤ 2*q by omega)
  have he := congrArg Complex.re (complete_normalization x (2*k) q hp ha hq')
  have eq : radius x^q*(oddPoleSum q x).re=2*(total (c x) (s x) q).re := by
    simpa [Complex.mul_re,← Complex.ofReal_pow] using he
  linarith

/-- Uniform mass and centered step for the actual scaled Eulerian moments. -/
theorem linear_scaled_moments {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) (hwidth : 2*n ≤ 5*k)
    (x : ℝ) (hx : 0 ≤ x) (upper : x ≤ 5/2*Real.sqrt (n-2 : ℕ)) (q : ℕ) (hq : k ≤ q) :
    let U := scaledMoment (radius x) (-Real.exp (-x))
    |U q| ≤ 3/2 ∧ |U (q+1) - c x * U q| ≤ 6*s x := by
  dsimp only
  have ha := centered_angle hk hn hwidth x hx upper
  have hp : 8 ≤ ((2*k:ℕ):ℝ) := by exact_mod_cast (show 8 ≤ 2*k by omega)
  have hq' : ((2*k:ℕ):ℝ) ≤ 2*(q:ℝ) := by exact_mod_cast (show 2*k ≤ 2*q by omega)
  rw [scaled_eq_half hk hq x hx ha,scaled_eq_half hk (show k ≤ q+1 by omega) x hx ha]
  refine ⟨(Complex.abs_re_le_norm _).trans (numerator_bound _ _ _ _ (circle x) hp ha hq').le, ?_⟩
  have diff := (Complex.abs_re_le_norm _).trans
    (half_centered_difference _ _ _ _ (circle x) (div_pos Real.pi_pos (radius_pos x)).le hp ha hq')
  simpa [Complex.mul_re] using diff

#print axioms half_centered_difference
#print axioms linear_scaled_moments

end
end LongCycleBounds.Band
