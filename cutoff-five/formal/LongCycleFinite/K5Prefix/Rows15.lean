import LongCycleFinite.K5Prefix.Rows11

namespace LongCycleFinite.K5Prefix
open LongCycleBounds.CycleProfile.Counterexample
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def p12 : List ℤ := [1, 3290, 230517, 3321264, 14715306, 23714604, 14715306, 3321264, 230517, 3290, 1]
def t12 : List (List ℤ) := (0 :: p12) :: t11
theorem h12 : coefficientTable weights 12 = t12 :=
  table_step h11 (by decide +kernel)
theorem row12 : LongCycles.enumerator 12 5 = Polynomial.X * ofCoeffs p12 :=
  row_from_table (past := t11) h12
def w12 : List Window := [⟨⟨-1456, 0⟩, ⟨-1424, 0⟩⟩,
   ⟨⟨-67, 1⟩, ⟨-65, 1⟩⟩,
   ⟨⟨-65, 3⟩, ⟨-127, 4⟩⟩,
   ⟨⟨-79, 5⟩, ⟨-77, 5⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-105, 8⟩, ⟨-103, 8⟩⟩,
   ⟨⟨-65, 9⟩, ⟨-127, 10⟩⟩,
   ⟨⟨-125, 12⟩, ⟨-123, 12⟩⟩,
   ⟨⟨-93, 17⟩, ⟨-91, 17⟩⟩]
theorem checked12 : caseOK p11 p12 ⟨-8936830510563328, 0⟩ w12 = true := by decide +kernel
theorem pair12 : OriginalPair 12 :=
  original_of_window row11 row12 (by decide) (by decide) checked12
def p13 : List ℤ := [1, 7086, 789296, 16608099, 108481452, 265583826, 265583826, 108481452, 16608099, 789296, 7086, 1]
def t13 : List (List ℤ) := (0 :: p13) :: t12
theorem h13 : coefficientTable weights 13 = t13 :=
  table_step h12 (by decide +kernel)
theorem row13 : LongCycles.enumerator 13 5 = Polynomial.X * ofCoeffs p13 :=
  row_from_table (past := t12) h13
def w13 : List Window := [⟨⟨-3232, 0⟩, ⟨-3168, 0⟩⟩,
   ⟨⟨-109, 1⟩, ⟨-107, 1⟩⟩,
   ⟨⟨-93, 3⟩, ⟨-91, 3⟩⟩,
   ⟨⟨-121, 5⟩, ⟨-119, 5⟩⟩,
   ⟨⟨-95, 6⟩, ⟨-93, 6⟩⟩,
   ⟨⟨-89, 7⟩, ⟨-87, 7⟩⟩,
   ⟨⟨-69, 8⟩, ⟨-67, 8⟩⟩,
   ⟨⟨-91, 10⟩, ⟨-89, 10⟩⟩,
   ⟨⟨-77, 12⟩, ⟨-75, 12⟩⟩,
   ⟨⟨-83, 18⟩, ⟨-81, 18⟩⟩]
theorem checked13 : caseOK p12 p13 ⟨-8936830510563328, 0⟩ w13 = true := by decide +kernel
theorem pair13 : OriginalPair 13 :=
  original_of_window row12 row13 (by decide) (by decide) checked13
def p14 : List ℤ := [1, 14899, 2630304, 79345371, 738755551, 2629306642, 3969999424, 2629306642, 738755551, 79345371, 2630304, 14899, 1]
def t14 : List (List ℤ) := (0 :: p14) :: t13
theorem h14 : coefficientTable weights 14 = t14 :=
  table_step h13 (by decide +kernel)
theorem row14 : LongCycles.enumerator 14 5 = Polynomial.X * ofCoeffs p14 :=
  row_from_table (past := t13) h14
def w14 : List Window := [⟨⟨-6976, 0⟩, ⟨-6848, 0⟩⟩,
   ⟨⟨-89, 0⟩, ⟨-87, 0⟩⟩,
   ⟨⟨-65, 2⟩, ⟨-127, 3⟩⟩,
   ⟨⟨-87, 4⟩, ⟨-85, 4⟩⟩,
   ⟨⟨-69, 5⟩, ⟨-67, 5⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-121, 8⟩, ⟨-119, 8⟩⟩,
   ⟨⟨-97, 9⟩, ⟨-95, 9⟩⟩,
   ⟨⟨-65, 10⟩, ⟨-127, 11⟩⟩,
   ⟨⟨-95, 13⟩, ⟨-93, 13⟩⟩,
   ⟨⟨-77, 19⟩, ⟨-75, 19⟩⟩]
theorem checked14 : caseOK p13 p14 ⟨-8936830510563328, 0⟩ w14 = true := by decide +kernel
theorem pair14 : OriginalPair 14 :=
  original_of_window row13 row14 (by decide) (by decide) checked14
def p15 : List ℤ := [1, 30812, 8709339, 370638127, 4791876806, 23973701325, 52176475782, 52176475782, 23973701325, 4791876806, 370638127, 8709339, 30812, 1]
def t15 : List (List ℤ) := (0 :: p15) :: t14
theorem h15 : coefficientTable weights 15 = t15 :=
  table_step h14 (by decide +kernel)
theorem row15 : LongCycles.enumerator 15 5 = Polynomial.X * ofCoeffs p15 :=
  row_from_table (past := t14) h15
def w15 : List Window := [⟨⟨-14976, 0⟩, ⟨-14720, 0⟩⟩,
   ⟨⟨-146, 0⟩, ⟨-142, 0⟩⟩,
   ⟨⟨-89, 2⟩, ⟨-87, 2⟩⟩,
   ⟨⟨-121, 4⟩, ⟨-119, 4⟩⟩,
   ⟨⟨-97, 5⟩, ⟨-95, 5⟩⟩,
   ⟨⟨-91, 6⟩, ⟨-89, 6⟩⟩,
   ⟨⟨-93, 7⟩, ⟨-91, 7⟩⟩,
   ⟨⟨-87, 8⟩, ⟨-85, 8⟩⟩,
   ⟨⟨-69, 9⟩, ⟨-67, 9⟩⟩,
   ⟨⟨-93, 11⟩, ⟨-91, 11⟩⟩,
   ⟨⟨-115, 14⟩, ⟨-113, 14⟩⟩,
   ⟨⟨-73, 20⟩, ⟨-71, 20⟩⟩]
theorem checked15 : caseOK p14 p15 ⟨-8936830510563328, 0⟩ w15 = true := by decide +kernel
theorem pair15 : OriginalPair 15 :=
  original_of_window row14 row15 (by decide) (by decide) checked15
end LongCycleFinite.K5Prefix
