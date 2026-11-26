import LongCycleBounds.FixedFourOuterLabels
import LongCycleBounds.FixedFourCoefficients
import LongCycleBounds.OuterDecayEnvelope
import LongCycleBounds.OuterLow

/-! Finite exterior bounds using the genuine cutoff-four tilt at upper size 101. -/

noncomputable section
namespace LongCycleBounds.FixedFour101.Exterior
open Real Finset FixedCutoff MarkedTwo

theorem budget_six {n m : ℕ} (hn : 101 ≤ n) (hm : m ≤ 6) {x : ℝ}
    (outer : 3*sqrt ((n-1 : ℕ) : ℝ) ≤ x) : exp (-x)*(n:ℝ)^m ≤ 1 := by
  have h := OuterDecayEnvelope.sixth_power hn outer
  have pos : 0 ≤ exp (-x)*(n:ℝ)^6 := by positivity
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast (show 1≤n by omega)) hm) (exp_pos _).le).trans
    (by linarith only [h,pos])

/-- Relative error at a positive integer label, uniformly down to upper size 101. -/
theorem positive_label {n j d : ℕ} (hn : 101 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    {x h : ℝ} (hh : 1 ≤ h) (outer : 3*sqrt ((n-1 : ℕ) : ℝ) ≤ x)
    (b : ℕ → ℝ) (cost_bound : ∀ R, 0 ≤ R → cost b R d ≤ exp (-x)*(R+R^2/2+R^3/6)) :
    |label b d h j-h^j| ≤ h^j/(10*(n:ℝ)^3) := by
  let R : ℝ := j/h
  let N : ℝ := n
  have N101 : 101 ≤ N := by dsimp [N]; exact_mod_cast hn
  have R0 : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have RN : R ≤ N := by
    apply (div_le_iff₀ (by linarith : 0<h)).mpr
    exact (by dsimp [N]; exact_mod_cast hjn : (j:ℝ) ≤ N).trans
      (le_mul_of_one_le_right (by linarith) hh)
  have v0 : 0 ≤ cost b R d := sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (by positivity)
  have poly : R+R^2/2+R^3/6 ≤ N^3/5 := by
    have e : N+N^2/2+N^3/6 ≤ N^3/5 := by
      nlinarith only [mul_nonneg (sq_nonneg N) (show 0 ≤ N-101 by linarith),
        mul_nonneg (show 0≤N by linarith) (show 0≤N-1 by linarith)]
    nlinarith only [e,RN,pow_le_pow_left₀ R0 RN 2,pow_le_pow_left₀ R0 RN 3]
  have cap := (cost_bound R R0).trans (mul_le_mul_of_nonneg_left poly (exp_pos _).le)
  have bud : 4*(exp (-x)*N^6)<1 := OuterDecayEnvelope.sixth_power hn outer
  have cp : 2*cost b R d * (10*N^3) ≤ 1 := by
    nlinarith only [bud,mul_le_mul_of_nonneg_right cap (by positivity : 0 ≤ 20*N^3)]
  have vhalf : cost b R d ≤ 1/2 := by
    have scale : 1 ≤ 10*N^3 := by nlinarith only [one_le_pow₀ (show 1 ≤ N by linarith) (n:=3)]
    nlinarith only [cp,mul_nonneg v0 (sub_nonneg.mpr scale)]
  have expcap := exp_bound_div_one_sub_of_interval v0 (by linarith : cost b R d<1)
  have frac : 1/(1-cost b R d) ≤ 1+2*cost b R d := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [mul_nonneg v0 (show 0 ≤ 1-2*cost b R d by linarith)]
  have rel : exp (cost b R d)-1 ≤ 1/(10*N^3) := by
    apply (show exp (cost b R d)-1 ≤ 2*cost b R d by linarith only [expcap,frac]).trans
    exact (le_div_iff₀ (by positivity)).mpr cp
  apply (positive_label_error b d (by linarith : 0<h) hj).trans
  simpa [R,N,div_eq_mul_inv] using mul_le_mul_of_nonneg_left rel (pow_nonneg (by linarith : 0≤h) j)

theorem zero_label {n j d : ℕ} (hn : 101≤n) (hd : 1≤d) (hd3 : d≤3)
    (hj : 2*d+5≤j) (hjn : j≤n) {x : ℝ}
    (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) :
    |label b d 0 j|≤exp (-x)/(n:ℝ)^4 := by
  let ρ := exp (x/d)
  have rp : 0<ρ := exp_pos _
  have xp : 0≤x := le_trans (by positivity) outer
  have dp : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by omega)
  have prod : exp (-x)*ρ^d=1 := by
    dsimp [ρ]
    rw [←exp_nat_mul,←exp_add]
    field_simp
    simp
  have ex := budget_six hn (show 2*d≤6 by omega) outer
  have hexp : exp (d:ℝ)≤n := by
    have hh : (d:ℝ)≤3 := by exact_mod_cast hd3
    calc
      exp (d:ℝ) ≤ exp 3 := exp_le_exp.mpr hh
      _ = (exp 1)^3 := by rw [←exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^3 := pow_le_pow_left₀ (exp_pos _).le exp_one_lt_three.le _
      _ ≤ _ := by exact_mod_cast (show 3^3≤n by omega)
  have hp : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have npos : (0:ℝ)<n := by linarith
  have powle : (n:ℝ)^2≤ρ := by
    apply le_of_pow_le_pow_left₀ (n:=d) (by omega) rp.le
    apply le_of_mul_le_mul_left (a:=exp (-x)) _ (exp_pos _)
    rw [prod,←pow_mul]
    exact ex
  have f : (j.factorial:ℝ)≤(n:ℝ)^j := by exact_mod_cast j.factorial_le_pow.trans (Nat.pow_le_pow_left hjn j)
  have numer : (j.factorial:ℝ)*exp d*(n:ℝ)^4 ≤ ρ^(j-d) := calc
    _ ≤ ((n:ℝ)^j*n)*(n:ℝ)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul f hexp (exp_pos _).le (by positivity)) (by positivity)
    _ = (n:ℝ)^(j+5) := by rw [pow_add];ring
    _ ≤ (n:ℝ)^(2*(j-d)) := pow_le_pow_right₀ hp (by omega)
    _ = ((n:ℝ)^2)^(j-d) := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) powle _
  apply (zero_label_decay hd xp b hb j).trans
  rw [div_le_div_iff₀ (pow_pos rp _) (pow_pos npos _)]
  have split : ρ^j=ρ^d*ρ^(j-d) := by rw [←pow_add];congr 1;omega
  change _ ≤ exp (-x)*ρ^j
  rw [split,←mul_assoc,prod,one_mul]
  exact numer

#print axioms budget_six
#print axioms positive_label
#print axioms zero_label
end LongCycleBounds.FixedFour101.Exterior
