import LongCycleBounds.MixedPoleGap

namespace LongCycleBounds.Band
open PoleTails Finset
noncomputable section

def signedOddPole (c s : ℝ) (i : ℤ) : ℂ := pole c s (2*(i:ℝ)+1)

def offDiagonal (j k : ℕ) (c s : ℝ) (v : ℤ × ℤ) : ℂ :=
  if v.1 = v.2 then 0 else mixedPair j k (signedOddPole c s v.1) (signedOddPole c s v.2)

def poleRemainder (j k : ℕ) (c s : ℝ) : ℝ := (∑' v : ℤ × ℤ, offDiagonal j k c s v).re / 4

def poleDiagonalFactor (j k : ℕ) : ℝ := 1 + ∑ a ∈ Icc k (j-k), 1/(a:ℝ)

end
end LongCycleBounds.Band
