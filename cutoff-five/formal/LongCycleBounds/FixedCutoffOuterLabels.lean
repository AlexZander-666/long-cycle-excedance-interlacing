import LongCycleBounds.FixedCutoffLabels
import LongCycleBounds.FixedCutoffMiddle

/-! Fixed-degree regularity at all exterior sites, with an explicit (coarse)
threshold in the size and a zero-label bound retaining exp(-x). -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real Finset MarkedTwo

theorem outer_power_budget (m n : ℕ) (hn : 2≤n) (large : (2*(m+1)).factorial≤n)
    {x : ℝ} (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) : exp (-x)*(n:ℝ)^m≤1 := by
  have nr : (2:ℝ)≤n := by exact_mod_cast hn
  have sn : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  rw [sn] at outer
  have xp : 0≤x := le_trans (by positivity) outer
  have sq := sq_le_sq' (by linarith [sqrt_nonneg ((n:ℝ)-1)]) outer
  have nl : (n:ℝ)≤x^2 := by nlinarith only [sq,sq_sqrt (by linarith : 0≤(n:ℝ)-1),nr]
  have pow := pow_le_pow_left₀ (by positivity) nl (m+1)
  rw [←pow_mul] at pow
  have fac : ((2*(m+1)).factorial:ℝ)≤n := by exact_mod_cast large
  rw [exp_neg,inv_mul_le_iff₀ (exp_pos x),mul_one]
  apply le_trans _ (pow_div_factorial_le_exp x xp (2*(m+1)))
  rw [le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left fac (by positivity)).trans ((pow_succ (n:ℝ) m) ▸ pow)

theorem outer_positive_error {n j d : ℕ} (hn : 2≤n) (hd : 2*d≤n)
    (large : (2*((d+5)+1)).factorial≤n) (hj : 1≤j) (hjn : j≤n)
    {x h : ℝ} (hh : 1≤h) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) :
    |label b d h j-h^j|≤h^j/(n:ℝ)^4 := by
  let R : ℝ := j/h
  have nr : (2:ℝ)≤n := by exact_mod_cast hn
  have dn : 2*(d:ℝ)≤n := by exact_mod_cast hd
  have jp : (j:ℝ)≤n := by exact_mod_cast hjn
  have Rp : 0≤R := by dsimp [R];positivity
  have Rn : R≤n := by
    dsimp [R];rw [div_le_iff₀ (by linarith)]
    exact jp.trans (le_mul_of_one_le_right (by positivity) hh)
  have v0 : 0≤cost b R d := sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg Rp _)
  have cap : cost b R d ≤ d*exp (-x)*(n:ℝ)^d := by
    apply le_trans _ (coarse_cost (exp_pos _).le (by linarith : (1:ℝ)≤n) b hb)
    exact sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Rp Rn (i+1)) (abs_nonneg _)
  have bud := outer_power_budget (d+5) n hn large outer
  have hmul : 2*cost b R d*(n:ℝ)^4 ≤ 1 := by
    have q := mul_le_mul_of_nonneg_right dn (show 0≤exp (-x)*(n:ℝ)^d*(n:ℝ)^4 by positivity)
    rw [pow_add] at bud
    nlinarith only [bud,q,mul_le_mul_of_nonneg_right cap (by positivity : 0≤2*(n:ℝ)^4)]
  have hsmall : cost b R d≤1/2 := by
    have a := le_mul_of_one_le_right (show 0≤2*cost b R d by linarith) (one_le_pow₀ (by linarith : (1:ℝ)≤n) (n:=4))
    linarith only [a,hmul]
  have e := exp_bound_div_one_sub_of_interval v0 (by linarith : cost b R d<1)
  have e' : 1/(1-cost b R d)≤1+2*cost b R d := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [mul_nonneg v0 (show 0≤1-2*cost b R d by linarith)]
  have sm : exp (cost b R d)-1≤1/(n:ℝ)^4 := by
    apply le_trans (show exp (cost b R d)-1≤2*cost b R d by linarith only [e,e']) _
    exact (le_div_iff₀ (by positivity)).2 hmul
  apply (positive_label_error b d (by linarith : 0<h) hj).trans
  simpa [R,div_eq_mul_inv] using mul_le_mul_of_nonneg_left sm (pow_nonneg (by linarith : 0≤h) j)

theorem outer_zero_error {n j d : ℕ} (hn : 2≤n) (hd : 1≤d)
    (large : (2*(4*d+1)).factorial≤n) (hexp : exp (d:ℝ)≤n)
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
  have ex := outer_power_budget (4*d) n hn large outer
  have hp : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have npos : (0:ℝ)<n := by linarith
  have powle : (n:ℝ)^4≤ρ := by
    apply le_of_pow_le_pow_left₀ (n:=d) (by omega) rp.le
    apply le_of_mul_le_mul_left (a:=exp (-x)) _ (exp_pos _)
    rw [prod,←pow_mul]
    exact ex
  have f : (j.factorial:ℝ)≤(n:ℝ)^j := by exact_mod_cast j.factorial_le_pow.trans (Nat.pow_le_pow_left hjn j)
  have numer : (j.factorial:ℝ)*exp d*(n:ℝ)^4 ≤ ρ^(j-d) := calc
    _ ≤ ((n:ℝ)^j*n)*(n:ℝ)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul f hexp (exp_pos _).le (by positivity)) (by positivity)
    _ = (n:ℝ)^(j+5) := by rw [pow_add];ring
    _ ≤ (n:ℝ)^(4*(j-d)) := pow_le_pow_right₀ hp (by omega)
    _ = ((n:ℝ)^4)^(j-d) := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) powle _
  apply (zero_label_decay hd xp b hb j).trans
  rw [div_le_div_iff₀ (pow_pos rp _) (pow_pos npos _)]
  have split : ρ^j=ρ^d*ρ^(j-d) := by rw [←pow_add];congr 1;omega
  change _ ≤ exp (-x)*ρ^j
  rw [split,←mul_assoc,prod,one_mul]
  exact numer

#print axioms outer_power_budget
#print axioms outer_positive_error
#print axioms outer_zero_error
end LongCycleBounds.FixedCutoff
