import LongCycleBounds.FiveOuterScalars
import LongCycleBounds.FixedFour101Labels

/-! Strict-excedance label errors for a four-term tilt in the exterior region. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff.Exterior
open Real Finset FixedCutoff MarkedTwo
theorem positive_label {n j d : ℕ} (hn : 49 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    {x h : ℝ} (hh : 1 ≤ h) (outer : 3*sqrt ((n-1 : ℕ) : ℝ) ≤ x)
    (b : ℕ → ℝ) (cost_bound : ∀ R, 0 ≤ R → cost b R d ≤ exp (-x)*(R+R^2/2+R^3/6+R^4/24)) :
    |label b d h j-h^j| ≤ h^j/(60*(n:ℝ)) := by
  let R : ℝ := j/h
  let N : ℝ := n
  have N49 : 49 ≤ N := by dsimp [N]; exact_mod_cast hn
  have R0 : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have RN : R ≤ N := by
    apply (div_le_iff₀ (by linarith : 0<h)).mpr
    exact (by dsimp [N]; exact_mod_cast hjn : (j:ℝ) ≤ N).trans
      (le_mul_of_one_le_right (by linarith) hh)
  have v0 : 0 ≤ cost b R d := sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (by positivity)
  have poly : R+R^2/2+R^3/6+R^4/24 ≤ N^4/21 := by
    have h1 : 49*N ≤ N^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr N49) (show 0≤N by linarith)]
    have h2 : 49*N^2 ≤ N^3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr N49) (sq_nonneg N)]
    have h3 : 49*N^3 ≤ N^4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr N49) (pow_nonneg (show 0≤N by linarith) 3)]
    linarith only [RN,pow_le_pow_left₀ R0 RN 2,pow_le_pow_left₀ R0 RN 3,
      pow_le_pow_left₀ R0 RN 4,h1,h2,h3,N49]
  have cap := (cost_bound R R0).trans (mul_le_mul_of_nonneg_left poly (exp_pos _).le)
  have bud : 3*(exp (-x)*N^5)<1 := fifth_power hn outer
  have cp : cost b R d * (63*N) ≤ 1 := by
    linarith only [bud,mul_le_mul_of_nonneg_right cap (show 0 ≤ 63*N by positivity)]
  have slack : cost b R d * (60*N+1) ≤ 1 := le_trans
    (mul_le_mul_of_nonneg_left (by linarith only [N49]) v0) cp
  have lt1 : cost b R d < 1 := by
    nlinarith only [cp,mul_nonneg (show 0 ≤ 63*N-2 by linarith) v0]
  have expcap := exp_bound_div_one_sub_of_interval v0 lt1
  have rel : exp (cost b R d)-1 ≤ 1/(60*N) := by
    apply (sub_le_sub_right expcap 1).trans
    rw [sub_le_iff_le_add,div_le_iff₀ (sub_pos.mpr lt1)]
    have np : 0 < 60*N := by positivity
    apply le_of_mul_le_mul_left (a:=60*N) _ np
    field_simp [np.ne']
    nlinarith only [slack]
  apply (positive_label_error b d (by linarith : 0<h) hj).trans
  simpa [R,N,div_eq_mul_inv] using mul_le_mul_of_nonneg_left rel (pow_nonneg (by linarith : 0≤h) j)

theorem zero_label {n j d : ℕ} (hn : 49 ≤ n) (hd : 1≤d) (hd3 : d≤4)
    (hj : n-5≤j) (hjn : j≤n) {x : ℝ}
    (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) :
    |label b d 0 j|≤exp (-x)/(60*(n:ℝ)) := by
  let ρ := exp (x/d)
  have rp : 0<ρ := exp_pos _
  have xp : 0≤x := le_trans (by positivity) outer
  have dp : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by omega)
  have prod : exp (-x)*ρ^d=1 := by
    dsimp [ρ]
    rw [←exp_nat_mul,←exp_add]
    field_simp
    simp
  have ex := fifth_power hn outer
  have n49 : (49:ℝ)≤n := by exact_mod_cast hn
  have hp : (1:ℝ)≤n := by linarith
  have npos : (0:ℝ)<n := by linarith
  have hexp : exp (d:ℝ) ≤ 60 := by
    have hh : (d:ℝ)≤4 := by exact_mod_cast hd3
    calc
      exp (d:ℝ) ≤ exp 4 := exp_le_exp.mpr hh
      _ = (exp 1)^4 := by rw [←exp_nat_mul]; norm_num
      _ ≤ (11/4:ℝ)^4 := pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) _
      _ ≤ _ := by norm_num
  have powle : 2*(n:ℝ)≤ρ := by
    apply le_of_pow_le_pow_left₀ (n:=d) (by omega) rp.le
    apply le_of_mul_le_mul_left (a:=exp (-x)) _ (exp_pos _)
    rw [prod]
    have cmp := pow_le_pow_right₀ (by linarith : 1 ≤ 2*(n:ℝ)) hd3
    have fourth : (2*(n:ℝ))^4 ≤ 3*(n:ℝ)^5 := by
      nlinarith only [mul_nonneg (pow_nonneg npos.le 4) (show 0≤3*(n:ℝ)-16 by linarith)]
    nlinarith only [ex,mul_le_mul_of_nonneg_left (cmp.trans fourth) (exp_pos (-x)).le]
  have f : (j.factorial:ℝ)≤(n:ℝ)^j := by exact_mod_cast j.factorial_le_pow.trans (Nat.pow_le_pow_left hjn j)
  have absorb : 3600*(n:ℝ)^(d+1) ≤ (2:ℝ)^(j-d) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega : d+1≤5)) (by norm_num : (0:ℝ)≤3600)).trans
      ((reserve hn).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega)))
  have numer : (j.factorial:ℝ)*exp d*(60*(n:ℝ)) ≤ ρ^(j-d) := calc
    _ ≤ ((n:ℝ)^j*60)*(60*n) := mul_le_mul_of_nonneg_right (mul_le_mul f hexp (exp_pos _).le (by positivity)) (by positivity)
    _ = (3600*(n:ℝ)^(d+1))*(n:ℝ)^(j-d) := by
      rw [mul_assoc (3600:ℝ) ((n:ℝ)^(d+1)),←pow_add,show d+1+(j-d)=j+1 by omega,pow_add]
      ring
    _ ≤ (2:ℝ)^(j-d)*(n:ℝ)^(j-d) := mul_le_mul_of_nonneg_right absorb (by positivity)
    _ ≤ ρ^(j-d) := by rw [←mul_pow]; exact pow_le_pow_left₀ (by positivity) powle _
  apply (zero_label_decay hd xp b hb j).trans
  rw [div_le_div_iff₀ (pow_pos rp _) (by positivity : 0<60*(n:ℝ))]
  have split : ρ^j=ρ^d*ρ^(j-d) := by rw [←pow_add]; congr 1; omega
  change _ ≤ exp (-x)*ρ^j
  rw [split,←mul_assoc (exp (-x)) (ρ^d),prod,one_mul]
  simpa only [mul_assoc] using numer


#print axioms positive_label
#print axioms zero_label
end LongCycleBounds.FiveCutoff.Exterior
