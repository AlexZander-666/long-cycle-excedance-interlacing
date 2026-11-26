import LongCycleBounds.FullStripMixedTerms

/-! Finite ordered triple kernels away from the common-label diagonal. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset PoleTails

def weightedPower (z : ℂ) (a : ℕ) : ℂ := ((1/(a:ℝ):ℝ):ℂ)*z^a

/-- The denominator pair belongs to the first two axes; the last exponent is free. -/
def orientedTriple (j k : ℕ) (z w u : ℂ) : ℂ :=
  ∑ a ∈ Icc k (j-2*k), weightedPower z a * orientedPair (j-a) k w u

theorem orientedTriple_expand (j k : ℕ) (z w u : ℂ) :
    orientedTriple j k z w u = ∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
      weightedPower z a*weightedPower w b*u^(j-a-b) := by
  simp only [orientedTriple,orientedPair,mul_sum,weightedPower,mul_assoc]

theorem orientedTriple_swap {j k : ℕ} (hk : 1≤k) (z w u : ℂ) :
    orientedTriple j k z w u = orientedTriple j k w z u := by
  rw [orientedTriple_expand,orientedTriple_expand]
  let S := Icc k (j-2*k)
  let T (a : ℕ) := Icc k (j-a-k)
  have cross (a b : ℕ) : a∈S ∧ b∈T a ↔ a∈T b ∧ b∈S := by
    simp only [S,T,mem_Icc]; omega
  rw [sum_comm' cross]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  rw [show j-a-b=j-b-a by omega]
  ring

/-- The new edge where the free exponent is exactly k. -/
def tripleEdge (j k : ℕ) (z w u : ℂ) : ℂ :=
  ∑ a ∈ Icc k (j-2*k), weightedPower z a * weightedPower w (j-a-k) * u^k

theorem orientedTriple_next {p k : ℕ} (hk : 1≤k) (hp : 3*k≤p+1) (z w u : ℂ) :
    orientedTriple (p+1) k z w u =
      u*orientedTriple p k z w u + tripleEdge (p+1) k z w u := by
  let g (a : ℕ) := weightedPower z a * orientedPair (p-a) k w u
  have wide : ∑ a ∈ Icc k (p+1-2*k), g a = ∑ a ∈ Icc k (p-2*k), g a := by
    rw [show p+1-2*k=p-2*k+1 by omega,sum_Icc_succ_top (by omega : k≤p-2*k+1)]
    have empty := Icc_eq_empty_of_lt (by omega : p-(p-2*k+1)-k < k)
    simp [g,orientedPair,empty]
  unfold orientedTriple tripleEdge
  change _ = u*(∑ a ∈ Icc k (p-2*k), g a) + _
  rw [←wide,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have := (mem_Icc.mp ha).2
  rw [show p+1-a=p-a+1 by omega,orientedPair_next hk (by omega)]
  dsimp only [g,weightedPower]
  ring

private theorem norm_weightedPower {k a : ℕ} (hk : 1≤k) (ha : k≤a)
    {z : ℂ} (hz : ‖z‖≤1) :
    ‖weightedPower z a‖ ≤ 1/(k:ℝ)*‖z‖^(k-1) := by
  rw [weightedPower,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul _ _ (pow_nonneg (norm_nonneg _) _) (by positivity)
  · exact one_div_le_one_div_of_le (by exact_mod_cast (show 0<k by omega)) (by exact_mod_cast ha)
  · exact pow_le_pow_of_le_one (norm_nonneg _) hz (by omega)

private theorem window_bound {j k : ℕ} (hk : 1≤k) (hj : j<4*k) {v : ℝ} (hv : 0≤v) :
    (∑ _a ∈ Icc k (j-2*k), (1/(k:ℝ))^2*v) ≤ 1/(k:ℝ)*v := by
  have num : ((Icc k (j-2*k)).card:ℝ) ≤ k := by exact_mod_cast (show (Icc k (j-2*k)).card≤k by rw [Nat.card_Icc];omega)
  rw [sum_const,nsmul_eq_mul]
  calc
    _ ≤ (k:ℝ)*((1/(k:ℝ))^2*v) := mul_le_mul_of_nonneg_right num (by positivity)
    _ = _ := by field_simp [ne_of_gt (by exact_mod_cast (show 0<k by omega) : 0<(k:ℝ))]

private theorem triangle_size_axis {j k : ℕ} (hk : 1≤k) (hj : j<4*k)
    {z w u : ℂ} (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hu : ‖u‖≤1) (hw0 : 0<‖w‖) (hu0 : 0<‖u‖)
    {s : ℝ} (hs : 0 ≤ s) (sep : 2*s*‖w‖*‖u‖ ≤ ‖w-u‖) :
    s*‖orientedTriple j k z w u‖ ≤ (1/(k:ℝ))*(‖z‖^(k-1)*‖w‖^(k-1)*‖u‖^(k-1)) := by
  unfold orientedTriple
  calc
    _ ≤ s*(∑ a ∈ Icc k (j-2*k), ‖weightedPower z a * orientedPair (j-a) k w u‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) hs
    _ ≤ ∑ _a ∈ Icc k (j-2*k), (1/(k:ℝ))^2*(‖z‖^(k-1)*‖w‖^(k-1)*‖u‖^(k-1)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro a ha
      obtain ⟨hal,har⟩ := mem_Icc.mp ha
      have pair := orientedPair_separated (j:=j-a) hk (by omega) hw hu hw0 hu0 sep
      rw [norm_mul, mul_left_comm]
      calc
        _ ≤ (1/(k:ℝ)*‖z‖^(k-1))*(1/(k:ℝ)*‖w‖^(k-1)*‖u‖^(k-1)) :=
          mul_le_mul (norm_weightedPower hk hal hz) pair (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ _ := window_bound hk hj (by positivity)

theorem tripleEdge_bound {j k : ℕ} (hk : 1≤k) (hj : j<4*k)
    {z w u : ℂ} (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hu : ‖u‖≤1) :
    ‖tripleEdge j k z w u‖ ≤ (1/(k:ℝ))*(‖z‖^(k-1)*‖w‖^(k-1)*‖u‖^(k-1)) := by
  unfold tripleEdge
  apply (norm_sum_le ..).trans
  apply le_trans _ (window_bound (k:=k) hk hj (by positivity))
  apply sum_le_sum
  intro a ha
  obtain ⟨hal,har⟩ := mem_Icc.mp ha
  rw [norm_mul,norm_mul,norm_pow]
  have ub := pow_le_pow_of_le_one (norm_nonneg u) hu (show k-1≤k by omega)
  calc
    _ ≤ ((1/(k:ℝ)*‖z‖^(k-1))*(1/(k:ℝ)*‖w‖^(k-1)))*‖u‖^(k-1) := by
      gcongr
      · exact norm_weightedPower hk hal hz
      · exact norm_weightedPower hk (by omega) hw
    _ = _ := by ring

private theorem odd_abs (i : ℤ) : 1 ≤ |2*(i:ℝ)+1| := by
  rcases le_or_gt 0 i with hi|hi
  · have : (0:ℝ) ≤ i := by exact_mod_cast hi
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (i:ℝ) ≤ -1 := by exact_mod_cast (by omega : i ≤ -1)
    rw [abs_of_neg (by linarith)]
    linarith

/-- Every nonconstant ordered triple has an Abel axis meeting the free exponent. -/
theorem signed_odd_triple_size {j k : ℕ} (hk : 1≤k) (hj : j<4*k)
    {c s : ℝ} (hc : c^2+s^2=1) (hs : 0 ≤ s) {i m h : ℤ} (mix : i≠h ∨ m≠h) :
    let z := signedOddPole c s
    let v (l : ℤ) := ‖z l‖^(k-1)
    s*‖orientedTriple j k (z i) (z m) (z h)‖ ≤ (1/(k:ℝ))*(v i*v m*v h) := by
  dsimp only
  obtain ⟨hi₀,hi,_⟩ := signed_pole_norms hc hs (odd_abs i)
  obtain ⟨hm₀,hm,_⟩ := signed_pole_norms hc hs (odd_abs m)
  obtain ⟨hh₀,hh,_⟩ := signed_pole_norms hc hs (odd_abs h)
  rcases mix with ne|ne
  · rw [orientedTriple_swap hk]
    simpa only [signedOddPole,mul_comm (‖pole c s (2*(m:ℝ)+1)‖^(k-1))] using
      triangle_size_axis (j:=j) hk hj hm hi hh hi₀ hh₀ hs (signed_odd_gap hc hs ne)
  · exact triangle_size_axis (j:=j) hk hj hi hm hh hm₀ hh₀ hs (signed_odd_gap hc hs ne)

/-- One new boundary edge also covers the first nonempty triangle at p+1=3k. -/
theorem signed_odd_triple_centered {p k : ℕ} (hk : 1≤k) (hp : 3*k≤p+1) (hn : p+1<4*k)
    {c s : ℝ} (hc : c^2+s^2=1) (hs : 0 ≤ s) {i m h : ℤ} (mix : i≠h ∨ m≠h) :
    let z := signedOddPole c s
    let v (l : ℤ) := ‖z l‖^(k-1)
    ‖orientedTriple (p+1) k (z i) (z m) (z h) - (c:ℂ)*orientedTriple p k (z i) (z m) (z h)‖ ≤
      ((|2*(h:ℝ)+1|+1)/(k:ℝ))*(v i*v m*v h) := by
  dsimp only
  let z := signedOddPole c s
  let v (l : ℤ) := ‖z l‖^(k-1)
  let K := orientedTriple p k (z i) (z m) (z h)
  have size : s*‖K‖ ≤ 1/(k:ℝ)*(v i*v m*v h) :=
    signed_odd_triple_size hk (by omega : p<4*k) hc hs mix
  obtain ⟨_,hi,_⟩ := signed_pole_norms hc hs (odd_abs i)
  obtain ⟨_,hm,_⟩ := signed_pole_norms hc hs (odd_abs m)
  obtain ⟨_,hh,hcenter⟩ := signed_pole_norms hc hs (odd_abs h)
  have edge : ‖tripleEdge (p+1) k (z i) (z m) (z h)‖ ≤ 1/(k:ℝ)*(v i*v m*v h) :=
    tripleEdge_bound hk hn hi hm hh
  change ‖orientedTriple (p+1) k (z i) (z m) (z h) - (c:ℂ)*K‖ ≤ _
  rw [orientedTriple_next hk hp]
  change ‖z h*K + tripleEdge (p+1) k (z i) (z m) (z h) - (c:ℂ)*K‖ ≤ _
  rw [show z h*K+tripleEdge (p+1) k (z i) (z m) (z h)-(c:ℂ)*K =
    (z h-(c:ℂ))*K+tripleEdge (p+1) k (z i) (z m) (z h) by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul]
  calc
    _ ≤ (|2*(h:ℝ)+1| *s)*‖K‖ + (1/(k:ℝ))*(v i*v m*v h) :=
      add_le_add (mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)) edge
    _ ≤ |2*(h:ℝ)+1| *(1/(k:ℝ)*(v i*v m*v h)) + 1/(k:ℝ)*(v i*v m*v h) := by
      rw [mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left size (abs_nonneg _)) le_rfl
    _ = (|2*(h:ℝ)+1|+1)/(k:ℝ)*(v i*v m*v h) := by ring

#print axioms orientedTriple_swap
#print axioms orientedTriple_next
#print axioms signed_odd_triple_size
#print axioms signed_odd_triple_centered
end LongCycleBounds.Band
