import LongCycleFinite.K5Prefix.Rows07

namespace LongCycleFinite.K5Prefix
open LongCycleBounds.CycleProfile.Counterexample
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def p8 : List ℤ := [1, 120, 1191, 2416, 1191, 120, 1]
def t8 : List (List ℤ) := (0 :: p8) :: t7
theorem h8 : coefficientTable weights 8 = t8 :=
  table_step h7 (by decide +kernel)
theorem row8 : LongCycles.enumerator 8 5 = Polynomial.X * ofCoeffs p8 :=
  row_from_table (past := t7) h8
def w8 : List Window := [⟨⟨-103, 1⟩, ⟨-101, 1⟩⟩,
   ⟨⟨-73, 4⟩, ⟨-71, 4⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-113, 9⟩, ⟨-111, 9⟩⟩,
   ⟨⟨-81, 12⟩, ⟨-79, 12⟩⟩]
theorem checked8 : caseOK p7 p8 ⟨-8936830510563328, 0⟩ w8 = true := by decide +kernel
theorem pair8 : OriginalPair 8 :=
  original_of_window row7 row8 (by decide) (by decide) checked8
def p9 : List ℤ := [1, 247, 4293, 15619, 15619, 4293, 247, 1]
def t9 : List (List ℤ) := (0 :: p9) :: t8
theorem h9 : coefficientTable weights 9 = t9 :=
  table_step h8 (by decide +kernel)
theorem row9 : LongCycles.enumerator 9 5 = Polynomial.X * ofCoeffs p9 :=
  row_from_table (past := t8) h9
def w9 : List Window := [⟨⟨-111, 0⟩, ⟨-109, 0⟩⟩,
   ⟨⟨-67, 3⟩, ⟨-65, 3⟩⟩,
   ⟨⟨-121, 6⟩, ⟨-119, 6⟩⟩,
   ⟨⟨-69, 7⟩, ⟨-67, 7⟩⟩,
   ⟨⟨-127, 10⟩, ⟨-125, 10⟩⟩,
   ⟨⟨-75, 13⟩, ⟨-73, 13⟩⟩]
theorem checked9 : caseOK p8 p9 ⟨-8936830510563328, 0⟩ w9 = true := by decide +kernel
theorem pair9 : OriginalPair 9 :=
  original_of_window row8 row9 (by decide) (by decide) checked9
def p10 : List ℤ := [1, 628, 17380, 106252, 186934, 106252, 17380, 628, 1]
def t10 : List (List ℤ) := (0 :: p10) :: t9
theorem h10 : coefficientTable weights 10 = t10 :=
  table_step h9 (by decide +kernel)
theorem row10 : LongCycles.enumerator 10 5 = Polynomial.X * ofCoeffs p10 :=
  row_from_table (past := t9) h10
def w10 : List Window := [⟨⟨-230, 0⟩, ⟨-226, 0⟩⟩,
   ⟨⟨-113, 3⟩, ⟨-111, 3⟩⟩,
   ⟨⟨-101, 5⟩, ⟨-99, 5⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-83, 8⟩, ⟨-81, 8⟩⟩,
   ⟨⟨-75, 10⟩, ⟨-73, 10⟩⟩,
   ⟨⟨-73, 14⟩, ⟨-71, 14⟩⟩]
theorem checked10 : caseOK p9 p10 ⟨-8936830510563328, 0⟩ w10 = true := by decide +kernel
theorem pair10 : OriginalPair 10 :=
  original_of_window row9 row10 (by decide) (by decide) checked10
def p11 : List ℤ := [1, 1475, 64934, 622898, 1790372, 1790372, 622898, 64934, 1475, 1]
def t11 : List (List ℤ) := (0 :: p11) :: t10
theorem h11 : coefficientTable weights 11 = t11 :=
  table_step h10 (by decide +kernel)
theorem row11 : LongCycles.enumerator 11 5 = Polynomial.X * ofCoeffs p11 :=
  row_from_table (past := t10) h11
def w11 : List Window := [⟨⟨-600, 0⟩, ⟨-584, 0⟩⟩,
   ⟨⟨-85, 2⟩, ⟨-83, 2⟩⟩,
   ⟨⟨-85, 4⟩, ⟨-83, 4⟩⟩,
   ⟨⟨-101, 6⟩, ⟨-99, 6⟩⟩,
   ⟨⟨-83, 7⟩, ⟨-81, 7⟩⟩,
   ⟨⟨-97, 9⟩, ⟨-95, 9⟩⟩,
   ⟨⟨-99, 11⟩, ⟨-97, 11⟩⟩,
   ⟨⟨-111, 16⟩, ⟨-109, 16⟩⟩]
theorem checked11 : caseOK p10 p11 ⟨-8936830510563328, 0⟩ w11 = true := by decide +kernel
theorem pair11 : OriginalPair 11 :=
  original_of_window row10 row11 (by decide) (by decide) checked11
end LongCycleFinite.K5Prefix
