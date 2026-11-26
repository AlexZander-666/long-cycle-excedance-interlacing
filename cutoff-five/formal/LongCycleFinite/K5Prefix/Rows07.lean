import LongCycleFinite.K5Prefix.Rows03

namespace LongCycleFinite.K5Prefix
open LongCycleBounds.CycleProfile.Counterexample
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def t4 : List (List ℤ) := [0, 0, 0, 0] :: t3
theorem h4 : coefficientTable weights 4 = t4 :=
  table_step h3 (by decide +kernel)
def p5 : List ℤ := [1, 11, 11, 1]
def t5 : List (List ℤ) := (0 :: p5) :: t4
theorem h5 : coefficientTable weights 5 = t5 :=
  table_step h4 (by decide +kernel)
theorem row5 : LongCycles.enumerator 5 5 = Polynomial.X * ofCoeffs p5 :=
  row_from_table (past := t4) h5
def p6 : List ℤ := [1, 26, 66, 26, 1]
def t6 : List (List ℤ) := (0 :: p6) :: t5
theorem h6 : coefficientTable weights 6 = t6 :=
  table_step h5 (by decide +kernel)
theorem row6 : LongCycles.enumerator 6 5 = Polynomial.X * ofCoeffs p6 :=
  row_from_table (past := t5) h6
def w6 : List Window := [⟨⟨-81, 3⟩, ⟨-79, 3⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-105, 10⟩, ⟨-103, 10⟩⟩]
theorem checked6 : caseOK p5 p6 ⟨-8936830510563328, 0⟩ w6 = true := by decide +kernel
theorem pair6 : OriginalPair 6 :=
  original_of_window row5 row6 (by decide) (by decide) checked6
def p7 : List ℤ := [1, 57, 302, 302, 57, 1]
def t7 : List (List ℤ) := (0 :: p7) :: t6
theorem h7 : coefficientTable weights 7 = t7 :=
  table_step h6 (by decide +kernel)
theorem row7 : LongCycles.enumerator 7 5 = Polynomial.X * ofCoeffs p7 :=
  row_from_table (past := t6) h7
def w7 : List Window := [⟨⟨-93, 2⟩, ⟨-91, 2⟩⟩,
   ⟨⟨-75, 5⟩, ⟨-73, 5⟩⟩,
   ⟨⟨-111, 8⟩, ⟨-109, 8⟩⟩,
   ⟨⟨-89, 11⟩, ⟨-87, 11⟩⟩]
theorem checked7 : caseOK p6 p7 ⟨-8936830510563328, 0⟩ w7 = true := by decide +kernel
theorem pair7 : OriginalPair 7 :=
  original_of_window row6 row7 (by decide) (by decide) checked7
end LongCycleFinite.K5Prefix
