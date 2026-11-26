import LongCycleBounds.FixedCutoffOuterLabels
import LongCycleBounds.MarkedOuterMoments
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real Finset Outer MarkedTwo PowerSeries

def raw (b : ℕ→ℝ) (d j : ℕ) (x : ℝ) : ℝ :=
  j.factorial * coeff j (tilt b d*logistic (time x))

private theorem arithmetic {N : ℝ} (h : 1024 ≤ N) :
    8*N*(1+(N+2)*(N+1)) ≤ N^4 ∧ 8*(N+N^2) < N^8 := by
  let a := N-1024
  have ha : 0≤a := sub_nonneg.mpr h
  have he : N=1024+a := by dsimp [a];ring
  constructor
  · rw [he,←sub_nonneg];ring_nf;positivity
  · rw [he,←sub_pos];ring_nf;positivity

private theorem outer_x {p : ℕ} (hp : 1024≤p+1) {x : ℝ} (outer : 3*sqrt (p:ℝ)≤x) :
    2≤x := by
  have pn : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have h := sqrt_le_sqrt pn
  rw [sqrt_one] at h
  linarith


private theorem raw_outer_error {n j d : ℕ} (hn : 1024≤n) (hd0 : 1≤d) (hd : 2*d≤n)
    (dense : (2*((d+5)+1)).factorial≤n) (dense0 : (2*(4*d+1)).factorial≤n)
    (expo : exp (d:ℝ)≤n) (hj : 2*d+5≤j) (hjn : j≤n) {x : ℝ} (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) :
    |raw b d j x+Outer.moment j x| ≤ (exp (-x)+∑' i, weight j x i)/(n:ℝ)^4 := by
  have hp0 : (0:ℝ)<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0<n-1 by omega)
  have hx : 0<x := lt_of_lt_of_le (by positivity) outer
  let t := time x
  let T (i : ℕ) := label b d i j
  have hnorm : ‖t‖ < 1 := by simp [t,time,Real.norm_eq_abs,exp_lt_one_iff,hx]
  have hs := logistic_label_sum b d hnorm j
  have sh := hs.summable.tsum_eq_zero_add
  rw [hs.tsum_eq] at sh
  have original : raw b d j x = T 0 + ∑' i : ℕ, t^(i+1)*T (i+1) := by
    simpa [raw,T,t] using sh
  let E (i : ℕ) := t^(i+1)*T (i+1)+(-1:ℝ)^i*weight j x i
  have bound (i : ℕ) : ‖E i‖ ≤ weight j x i/(n:ℝ)^4 := by
    have bound := outer_positive_error (by omega : 2≤n) hd dense (by omega : 1≤j) hjn
      (h:=(i+1:ℕ)) (by exact_mod_cast (show 1≤ i+1 by omega)) outer b hb
    change |T (i+1)-((i+1:ℕ):ℝ)^j|≤_/ _ at bound
    have e : E i = -((-1:ℝ)^i)*(exp (-x))^(i+1)*(T (i+1)-((i+1:ℕ):ℝ)^j) := by
      have tv : t=(-1)*exp (-x) := by simp [t,time]
      simp only [E,tv,mul_pow,weight,Nat.cast_succ,pow_succ (-1:ℝ) i]
      ring
    rw [e,Real.norm_eq_abs,abs_mul,abs_mul]
    simp only [abs_neg,abs_pow,abs_one,one_pow,one_mul,abs_of_pos (exp_pos _)]
    unfold weight
    rw [Nat.cast_succ] at bound ⊢
    calc
      _ ≤ (exp (-x))^(i+1)*((((i:ℝ)+1)^j)/(n:ℝ)^4) := mul_le_mul_of_nonneg_left bound (by positivity)
      _ = _ := by ring
  have hrs : Summable (fun i : ℕ ↦ weight j x i/(n:ℝ)^4) := (summable_weight j x hx).div_const _
  have herr := (norm_tsum_le_tsum_norm (hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound)).trans
    ((hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound).tsum_le_tsum bound hrs)
  have hraw : raw b d j x+Outer.moment j x=T 0+∑' i, E i := by
    rw [original,add_assoc,Outer.moment]
    congr 1
    exact (((summable_nat_add_iff 1).mpr hs.summable).tsum_add (summable_signed_weight j x hx)).symm
  rw [hraw]
  rw [Real.norm_eq_abs] at herr
  have zero : |T 0| ≤ exp (-x)/(n:ℝ)^4 := by
    simpa only [T,Nat.cast_zero] using outer_zero_error (by omega) hd0 dense0 expo hj hjn outer b hb
  rw [tsum_div_const] at herr
  rw [add_div]
  exact (abs_add_le ..).trans (add_le_add zero herr)


theorem raw_peak_error {p j d : ℕ} (hn : 1024≤p+1) (hd0 : 1≤d) (hd : 2*d≤p+1)
    (dense : (2*((d+5)+1)).factorial≤p+1) (dense0 : (2*(4*d+1)).factorial≤p+1)
    (expo : exp (d:ℝ)≤(p+1:ℕ)) (hj : 2*d+5≤j) (hjn : j≤p+1) {x : ℝ} (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) (outer : 3*sqrt (p:ℝ)≤x) :
    8*((p:ℝ)+1)*|raw b d j x+Outer.moment j x| ≤ weight p x (mode p x (by linarith [outer_x hn outer])) := by
  have hx := outer_x hn outer
  let W := weight p x (mode p x (by linarith))
  have hW : 0≤W := (weight_pos ..).le
  have r0 : exp (-x)≤W := by
    have he : weight p x 0=exp (-x) := by simp [weight]
    rw [←he]
    exact weight_le_mode p x _ 0
  have err := raw_outer_error hn hd0 hd dense dense0 expo hj hjn b hb (by simpa using outer)
  have mass := outer_mass hjn hx
  have pn : 1024≤(p:ℝ)+1 := by exact_mod_cast hn
  let N := (p:ℝ)+1
  have ar := (arithmetic pn).1
  change _ ≤ ((p:ℝ)+3)*((p:ℝ)+2)*W at mass
  rw [Nat.cast_succ] at err
  have main := (le_div_iff₀ (by positivity)).mp err
  change 8*N*_ ≤ W
  have pN : 0<N^4 := by dsimp [N];positivity
  apply le_of_mul_le_mul_right (a:=N^4) _ pN
  change _ ≤ W*N^4
  dsimp [N] at *
  nlinarith only [mul_le_mul_of_nonneg_right ar hW,
    mul_le_mul_of_nonneg_left (main.trans (add_le_add r0 mass)) (by positivity : 0≤8*((p:ℝ)+1))]


/-- Entire exterior insertion bound for an arbitrary signed finite profile. -/
theorem outer_insertion_gap {p d : ℕ} (hn : 1024≤p+1) (hd0 : 1≤d) (room : 3*d+6≤p)
    (dense : (2*((d+5)+1)).factorial≤p+1) (dense0 : (2*(4*d+1)).factorial≤p+1)
    (expo : exp (d:ℝ)≤(p+1:ℕ)) {x : ℝ} (b C : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x))
    (hC : ∀ i, 1 ≤ i → i ≤ d → |C i|≤exp (-x))
    (outer : 3*sqrt (p:ℝ)≤x) (zero : raw b d p x=0) :
    |∑ i ∈ range d, (p.descFactorial (i+1):ℝ)*C (i+1)*raw b d (p-(i+1)) x| <
      |raw b d (p+1) x| := by
  let N := (p:ℝ)+1
  have hn' : 1024≤p+1 := hn
  have nr : 1024≤N := by dsimp [N];exact_mod_cast hn'
  have cut : 3*sqrt (p:ℝ)≤x := outer
  have x2 := outer_x hn' cut
  have hx : 0<x := by linarith
  let M := mode p x hx
  let W := weight p x M
  have wp : 0<W := weight_pos ..
  have prev : raw b d p x=0 := zero
  have small (j : ℕ) (hj : 2*d+5≤j) (le : j≤p+1) :
      8*N*|raw b d j x+Outer.moment j x| ≤ W := raw_peak_error hn' hd0 (by omega) dense dense0 expo hj le b hb cut
  have eps (j : ℕ) (hj : 2*d+5≤j) (le : j≤p+1) :
      |raw b d j x+Outer.moment j x| ≤ W/8 := by
    nlinarith only [small j hj le,mul_nonneg (show 0≤N-1 by linarith)
      (abs_nonneg (raw b d j x+Outer.moment j x))]
  have ps : 2*d+5≤p := by omega
  have next := small p ps (by omega)
  rw [prev,zero_add] at next
  have q := mode_index_mul_le p x hx
  change (M:ℝ)*x ≤ p at q
  have pm : (M:ℝ)+2 ≤ N := by
    dsimp [N]
    have hp1 : (2:ℝ)≤p := by exact_mod_cast (show 2≤p by omega)
    nlinarith only [q,hp1,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (sub_nonneg.mpr x2)]
  have split : 5*sqrt (p:ℝ)/2≤x := by linarith [sqrt_nonneg (p:ℝ)]
  have rob := robust_derivative_moment p (by omega) x hx split
  change W/2 < |Outer.moment (p+1) x|+((M:ℝ)+2)*|Outer.moment p x| at rob
  have big : W/4 < |raw b d (p+1) x| := by
    have diff := abs_sub (raw b d (p+1) x+Outer.moment (p+1) x) (raw b d (p+1) x)
    rw [add_sub_cancel_left] at diff
    nlinarith only [diff,rob,next,mul_le_mul_of_nonneg_right pm (abs_nonneg (Outer.moment p x)),
      eps (p+1) (by omega) le_rfl]
  have short (j : ℕ) (hj : 2*d+5≤j) (le : j≤p) : |raw b d j x| ≤ 2*W := by
    have plain := signed_weight_bound j x hx
    change |Outer.moment j x| ≤ weight j x (mode j x hx) at plain
    let i := mode j x hx
    have weight_le : weight j x i≤weight p x i := by
      unfold weight
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i]) le)
        (by positivity)
    have bound := plain.trans (weight_le.trans (weight_le_mode p x hx i))
    have diff := abs_sub (raw b d j x+Outer.moment j x) (Outer.moment j x)
    rw [add_sub_cancel_right] at diff
    linarith only [diff,eps j hj (by omega),bound,wp]
  have mass : |∑ i ∈ range d, (p.descFactorial (i+1):ℝ)*C (i+1)*raw b d (p-(i+1)) x| ≤
      (d:ℝ)*N^d*exp (-x)*(2*W) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _i ∈ range d, (N^d*exp (-x))*(2*W) := by
        apply sum_le_sum
        intro i hi
        have h : i+1≤d := mem_range.mp hi
        have df : (p.descFactorial (i+1):ℝ)≤N^d := by
          apply le_trans (by exact_mod_cast Nat.descFactorial_le_pow p (i+1) : (p.descFactorial (i+1):ℝ) ≤ (p:ℝ)^(i+1))
          exact (pow_le_pow_left₀ (by positivity) (show (p:ℝ)≤N by dsimp [N];linarith) _).trans
            (pow_le_pow_right₀ (by linarith) h)
        rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(p.descFactorial (i+1):ℝ))]
        exact mul_le_mul (mul_le_mul df (hC _ (by omega) h) (abs_nonneg _) (by positivity))
          (short _ (by omega) (Nat.sub_le ..)) (abs_nonneg _) (by positivity)
      _ = _ := by simp;ring
  have bud := outer_power_budget (d+5) (p+1) (by omega) dense (by simpa using outer)
  rw [Nat.cast_succ,pow_add] at bud
  change exp (-x)*(N^d*N^5)≤1 at bud
  have dx : (d:ℝ)≤N := by dsimp [N];exact_mod_cast (show d≤p+1 by omega)
  have cmp : 8*(d:ℝ)<N^5 := by
    have nn := pow_le_pow_right₀ (by linarith : 1≤N) (by decide : 2≤5)
    nlinarith only [nn,mul_pos (show 0<N by linarith) (show 0<N-8 by linarith),dx]
  have strict := mul_lt_mul_of_pos_right cmp (mul_pos (exp_pos (-x)) (pow_pos (by linarith : 0<N) d))
  apply mass.trans_lt
  apply lt_trans _ big
  nlinarith only [mul_lt_mul_of_pos_right (show 8*d*N^d*exp (-x)<1 by nlinarith only [strict,bud]) wp]

#print axioms raw_peak_error
#print axioms outer_insertion_gap
end LongCycleBounds.FixedCutoff
