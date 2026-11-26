import LongCycleBounds.FortyEightPeak
import LongCycleBounds.FiveOuterLabels
import LongCycleBounds.FiveMiddleProfile
import LongCycleBounds.FixedCutoffAnalyticAssembly
import LongCycleBounds.CycleProfileInsertion

/-! Exterior sign for the genuine short-cycle weights at size 49 and beyond. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff.Exterior
open Real Finset Outer FixedCutoff MarkedTwo PowerSeries

private theorem outer_x {p : ℕ} (hp : 49≤p+1) {x : ℝ} (outer : 3*sqrt (p:ℝ)≤x) :
    2≤x := by
  have pn : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have h := sqrt_le_sqrt pn
  rw [sqrt_one] at h
  linarith


private theorem raw_outer_error {n j d : ℕ} (hn : 49≤n) (hd0 : 1≤d) (hd : d≤4) (hj : n-5≤j) (hjn : j≤n) {x : ℝ} (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) (cost_bound : ∀ R, 0 ≤ R → cost b R d ≤ exp (-x)*(R+R^2/2+R^3/6+R^4/24)) (outer : 3*sqrt ((n-1:ℕ):ℝ)≤x) :
    |raw b d j x+Outer.moment j x| ≤ (exp (-x)+∑' i, weight j x i)/(60*(n:ℝ)) := by
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
  have bound (i : ℕ) : ‖E i‖ ≤ weight j x i/(60*(n:ℝ)) := by
    have bound := positive_label hn (by omega : 1≤j) hjn
      (h:=(i+1:ℕ)) (by exact_mod_cast (show 1≤ i+1 by omega)) outer b cost_bound
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
      _ ≤ (exp (-x))^(i+1)*((((i:ℝ)+1)^j)/(60*(n:ℝ))) := mul_le_mul_of_nonneg_left bound (by positivity)
      _ = _ := by ring
  have hrs : Summable (fun i : ℕ ↦ weight j x i/(60*(n:ℝ))) := (summable_weight j x hx).div_const _
  have herr := (norm_tsum_le_tsum_norm (hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound)).trans
    ((hrs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) bound).tsum_le_tsum bound hrs)
  have hraw : raw b d j x+Outer.moment j x=T 0+∑' i, E i := by
    rw [original,add_assoc,Outer.moment]
    congr 1
    exact (((summable_nat_add_iff 1).mpr hs.summable).tsum_add (summable_signed_weight j x hx)).symm
  rw [hraw]
  rw [Real.norm_eq_abs] at herr
  have zero : |T 0| ≤ exp (-x)/(60*(n:ℝ)) := by
    simpa only [T, Nat.cast_zero] using zero_label hn hd0 hd hj hjn outer b hb
  rw [tsum_div_const] at herr
  rw [add_div]
  exact (abs_add_le ..).trans (add_le_add zero herr)


private theorem smaller_mass (p j : ℕ) (hp : 48≤p) (hj : j≤p) (x : ℝ) (hx : 0<x)
    (region : 3*sqrt p≤x) : ∑' i, weight j x i ≤ 4*weight p x (mode p x hx) := by
  apply le_trans ((summable_weight j x hx).tsum_le_tsum _ (summable_weight p x hx))
    (FortyEight.mass_at_peak p hp x hx (by linarith [sqrt_nonneg (p:ℝ)]))
  intro i
  unfold weight
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i]) hj) (by positivity)

private theorem successor_mass (p : ℕ) (hp : 48≤p) (x : ℝ) (hx : 0<x)
    (region : 3*sqrt p≤x) : ∑' i, weight (p+1) x i ≤ 4*((p:ℝ)+1)*weight p x (mode p x hx) := by
  let m := mode (p+1) x hx
  have mass := FortyEight.mass_at_peak (p+1) (by omega) x hx (FortyEight.region_next hp region)
  have idx := mode_index_mul_le (p+1) x hx
  change (m:ℝ)*x≤((p+1:ℕ):ℝ) at idx
  rw [Nat.cast_succ] at idx
  have x2 : 2≤x := outer_x (by omega : 49≤p+1) region
  have pr : (48:ℝ)≤p := by exact_mod_cast hp
  have ml : (m:ℝ)+1 ≤ (p:ℝ)+1 := by
    nlinarith only [idx,pr,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sub_nonneg.mpr x2)]
  have eq : weight (p+1) x m = ((m:ℝ)+1)*weight p x m := by unfold weight; rw [pow_succ]; ring
  change _ ≤ 4*weight (p+1) x m at mass
  rw [eq] at mass
  rw [mul_assoc]
  exact mass.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul ml (weight_le_mode p x hx m) (weight_pos ..).le (by positivity)) (by norm_num))

private theorem peak_small {p j d : ℕ} (hn : 49≤p+1) (hd0 : 1≤d) (hd : d≤4)
    (hj : p+1-5≤j) (hjn : j≤p) {x : ℝ} (b : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x)) (cost_bound : ∀ R, 0 ≤ R → cost b R d≤exp (-x)*(R+R^2/2+R^3/6+R^4/24))
    (outer : 3*sqrt (p:ℝ)≤x) :
    8*((p:ℝ)+1)*|raw b d j x+Outer.moment j x| ≤ weight p x (mode p x (by linarith [outer_x hn outer])) := by
  have hx : 0<x := by linarith [outer_x hn outer]
  have err := raw_outer_error hn hd0 hd hj (by omega : j≤p+1) b hb cost_bound (by simpa using outer)
  have mass := smaller_mass p j (by omega) hjn x hx outer
  have rr := weight_le_mode p x hx 0
  simp only [weight, Nat.cast_zero, zero_add,one_pow,one_mul,pow_one] at rr
  change exp (-x)≤weight p x (mode p x hx) at rr
  rw [Nat.cast_succ] at err
  have main := (le_div_iff₀ (by positivity)).mp err
  nlinarith only [main,mass,rr,(weight_pos p x (mode p x hx)).le]

private theorem peak_successor {p d : ℕ} (hn : 49≤p+1) (hd0 : 1≤d) (hd : d≤4)
    {x : ℝ} (b : ℕ→ℝ) (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x))
    (cost_bound : ∀ R, 0 ≤ R → cost b R d≤exp (-x)*(R+R^2/2+R^3/6+R^4/24))
    (outer : 3*sqrt (p:ℝ)≤x) :
    |raw b d (p+1) x+Outer.moment (p+1) x| ≤ weight p x (mode p x (by linarith [outer_x hn outer]))/8 := by
  have hx : 0<x := by linarith [outer_x hn outer]
  have err := raw_outer_error hn hd0 hd (by omega : p+1-5≤p+1) le_rfl b hb cost_bound (by simpa using outer)
  have mass := successor_mass p (by omega) x hx outer
  have rr := weight_le_mode p x hx 0
  have eq : weight p x 0=exp (-x) := by simp [weight]
  rw [eq] at rr
  rw [Nat.cast_succ] at err
  have main := (le_div_iff₀ (by positivity)).mp err
  apply (le_div_iff₀ (by norm_num)).mpr
  apply le_of_mul_le_mul_right (a:=60*((p:ℝ)+1)) _ (by positivity)
  nlinarith only [main,mass,rr,(weight_pos p x (mode p x hx)).le,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) p) (weight_pos p x (mode p x hx)).le]

theorem insertion_gap {p d : ℕ} (hn : 49≤p+1) (hd0 : 1≤d) (hd : d≤4) {x : ℝ} (b C : ℕ→ℝ)
    (hb : ∀ i, 1 ≤ i → i ≤ d → |b i|≤exp (-x))
    (cost_bound : ∀ R, 0 ≤ R → cost b R d ≤ exp (-x)*(R+R^2/2+R^3/6+R^4/24)) 
    (hC : ∀ i, 1 ≤ i → i ≤ d → |C i|≤exp (-x))
    (outer : 3*sqrt (p:ℝ)≤x) (zero : raw b d p x=0) :
    |∑ i ∈ range d, (p.descFactorial (i+1):ℝ)*C (i+1)*raw b d (p-(i+1)) x| <
      |raw b d (p+1) x| := by
  let N := (p:ℝ)+1
  have hn' : 49≤p+1 := hn
  have nr : 49≤N := by dsimp [N];exact_mod_cast hn'
  have cut : 3*sqrt (p:ℝ)≤x := outer
  have x2 := outer_x hn' cut
  have hx : 0<x := by linarith
  let M := mode p x hx
  let W := weight p x M
  have wp : 0<W := weight_pos ..
  have prev : raw b d p x=0 := zero
  have small (j : ℕ) (hj : p+1-5≤j) (le : j≤p) :
      8*N*|raw b d j x+Outer.moment j x| ≤ W := peak_small hn' hd0 hd hj le b hb cost_bound cut
  have eps (j : ℕ) (hj : p+1-5≤j) (le : j≤p+1) :
      |raw b d j x+Outer.moment j x| ≤ W/8 := by
    by_cases h : j≤p
    · nlinarith only [small j hj h,mul_nonneg (show 0≤N-1 by linarith)
        (abs_nonneg (raw b d j x+Outer.moment j x))]
    · have ej : j=p+1 := by omega
      subst j
      exact peak_successor hn' hd0 hd b hb cost_bound cut
  have next := small p (by omega) le_rfl
  rw [prev,zero_add] at next
  have q := mode_index_mul_le p x hx
  change (M:ℝ)*x ≤ p at q
  have pm : (M:ℝ)+2 ≤ N := by
    dsimp [N]
    have hp1 : (2:ℝ)≤p := by exact_mod_cast (show 2≤p by omega)
    nlinarith only [q,hp1,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (sub_nonneg.mpr x2)]
  have split : (29/10:ℝ)*sqrt (p:ℝ)≤x := by linarith [sqrt_nonneg (p:ℝ)]
  have rob := robust_derivative_of_tails p x hx (FortyEight.neighbors_min_le p (by omega) x hx split)
    (FortyEight.both_geometric p (by omega) x hx split)
  change W/2 < |Outer.moment (p+1) x|+((M:ℝ)+2)*|Outer.moment p x| at rob
  have big : W/4 < |raw b d (p+1) x| := by
    have diff := abs_sub (raw b d (p+1) x+Outer.moment (p+1) x) (raw b d (p+1) x)
    rw [add_sub_cancel_left] at diff
    nlinarith only [diff,rob,next,mul_le_mul_of_nonneg_right pm (abs_nonneg (Outer.moment p x)),
      eps (p+1) (by omega) le_rfl]
  have short (j : ℕ) (hj : p+1-5≤j) (le : j≤p) : |raw b d j x| ≤ 2*W := by
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
  have budget := fifth_power hn' (by simpa using outer)
  rw [Nat.cast_succ] at budget
  change 3*(exp (-x)*N^5)<1 at budget
  have d4 : (d:ℝ)≤4 := by exact_mod_cast hd
  have nd := pow_le_pow_right₀ (by linarith : 1≤N) hd
  have cmp : 8*(d:ℝ)*N^d ≤ 3*N^5 := by
    nlinarith only [mul_le_mul_of_nonneg_right d4 (by positivity : 0≤N^d),nd,
      mul_nonneg (pow_nonneg (show 0≤N by linarith) 4) (show 0≤3*N-32 by linarith)]
  have smallsum : 8*(d:ℝ)*N^d*exp (-x)<1 :=
    (mul_le_mul_of_nonneg_right cmp (exp_pos _).le).trans_lt (by linarith only [budget])
  apply mass.trans_lt
  apply lt_trans _ big
  nlinarith only [mul_lt_mul_of_pos_right smallsum wp]

end LongCycleBounds.FiveCutoff.Exterior

namespace LongCycleBounds.FiveCutoff
open Real Finset FixedCutoff MarkedTwo CycleProfile

/-- The three short-cycle marks vary independently over their entire closed cube.
The lower row has index p and the upper row has index p+1. -/
theorem exterior_sign {p : ℕ} (hn : 49≤p+1) (w : ℕ→ℝ) (one : w 1=0)
    (tail : ∀ a≥5, w a=1) (unit : ∀ a,w a∈Set.Icc (0:ℝ) 1) {x : ℝ}
    (outer : 3*sqrt (p:ℝ)≤x) (zero : CycleProfile.normalizedRow w p x=0) :
    0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
  have hx : 0≤x := le_trans (by positivity) outer
  let b := fun a ↦ tiltCoefficient w a x
  let C := fun a ↦ drift w a x
  have hb (i : ℕ) (hi : 1 ≤ i) (_ : i≤4) : |b i|≤exp (-x) := tilt_bound unit hx hi
  have hC (i : ℕ) (_ : 1 ≤ i) (_ : i≤4) : |C i|≤exp (-x) := drift_bound unit hx i
  have rz : raw b 4 p x=0 := by
    have a := raw_eq_profile (by decide : 2≤5) w one tail hx p
    rw [zero] at a
    exact (mul_eq_zero.mp a).resolve_left (by unfold MarkedTwo.time;linarith [exp_pos (-x)])
  apply raw_gap_to_normalized_sign (by decide : 2≤5) w one tail hx
    (CycleProfile.normalizedRow_insertion (by decide : 3≤5) (by omega) w one tail x)
  have coeff (a : ℕ) (lo : 1≤a) (hi : a≤4) : |b a| ≤ exp (-x)/a.factorial :=
    tilt_factorial one unit hx lo hi
  have costBound (R : ℝ) (hR : 0≤R) :
      cost b R 4 ≤ exp (-x)*(R+R^2/2+R^3/6+R^4/24) := by
    have term (a : ℕ) (lo : 1≤a) (hi : a≤4) :=
      mul_le_mul_of_nonneg_right (coeff a lo hi) (pow_nonneg hR a)
    have a := term 1 (by decide) (by decide)
    have b2 := term 2 (by decide) (by decide)
    have c := term 3 (by decide) (by decide)
    have d := term 4 (by decide) (by decide)
    norm_num [Nat.factorial] at a b2 c d
    simp only [cost,sum_range_succ,sum_range_zero,zero_add,Nat.reduceAdd,pow_one]
    linarith only [a,b2,c,d]
  exact Exterior.insertion_gap hn (by decide : 1≤4) (by decide : 4≤4) b C hb costBound hC outer rz

#print axioms exterior_sign
end LongCycleBounds.FiveCutoff
