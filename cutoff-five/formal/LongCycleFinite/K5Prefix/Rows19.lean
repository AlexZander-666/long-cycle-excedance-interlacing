import LongCycleFinite.K5Prefix.Rows15

namespace LongCycleFinite.K5Prefix
open LongCycleBounds.CycleProfile.Counterexample
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def p16 : List ℤ := [1, 63003, 28556963, 1697861626, 29883791697, 204534644645, 619766384139, 890288995212, 619766384139, 204534644645, 29883791697, 1697861626, 28556963, 63003, 1]
def t16 : List (List ℤ) := (0 :: p16) :: t15
theorem h16 : coefficientTable weights 16 = t16 :=
  table_step h15 (by decide +kernel)
theorem row16 : LongCycles.enumerator 16 5 = Polynomial.X * ofCoeffs p16 :=
  row_from_table (past := t15) h16
def w16 : List Window := [⟨⟨-30976, 0⟩, ⟨-30464, 0⟩⟩,
   ⟨⟨-238, 0⟩, ⟨-234, 0⟩⟩,
   ⟨⟨-123, 2⟩, ⟨-121, 2⟩⟩,
   ⟨⟨-81, 3⟩, ⟨-79, 3⟩⟩,
   ⟨⟨-67, 4⟩, ⟨-65, 4⟩⟩,
   ⟨⟨-123, 6⟩, ⟨-121, 6⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-69, 7⟩, ⟨-67, 7⟩⟩,
   ⟨⟨-125, 9⟩, ⟨-123, 9⟩⟩,
   ⟨⟨-103, 10⟩, ⟨-101, 10⟩⟩,
   ⟨⟨-67, 11⟩, ⟨-65, 11⟩⟩,
   ⟨⟨-71, 14⟩, ⟨-69, 14⟩⟩,
   ⟨⟨-69, 21⟩, ⟨-67, 21⟩⟩]
theorem checked16 : caseOK p15 p16 ⟨-8936830510563328, 0⟩ w16 = true := by decide +kernel
theorem pair16 : OriginalPair 16 :=
  original_of_window row15 row16 (by decide) (by decide) checked16
def p17 : List ℤ := [1, 127841, 92560751, 7648113783, 180518816437, 1653824076877, 6788383387043, 13502402774547, 13502402774547, 6788383387043, 1653824076877, 180518816437, 7648113783, 92560751, 127841, 1]
def t17 : List (List ℤ) := (0 :: p17) :: t16
theorem h17 : coefficientTable weights 17 = t17 :=
  table_step h16 (by decide +kernel)
theorem row17 : LongCycles.enumerator 17 5 = Polynomial.X * ofCoeffs p17 :=
  row_from_table (past := t16) h17
def w17 : List Window := [⟨⟨-62976, 0⟩, ⟨-61952, 0⟩⟩,
   ⟨⟨-396, 0⟩, ⟨-388, 0⟩⟩,
   ⟨⟨-87, 1⟩, ⟨-85, 1⟩⟩,
   ⟨⟨-107, 3⟩, ⟨-105, 3⟩⟩,
   ⟨⟨-89, 4⟩, ⟨-87, 4⟩⟩,
   ⟨⟨-83, 5⟩, ⟨-81, 5⟩⟩,
   ⟨⟨-87, 6⟩, ⟨-85, 6⟩⟩,
   ⟨⟨-97, 7⟩, ⟨-95, 7⟩⟩,
   ⟨⟨-101, 8⟩, ⟨-99, 8⟩⟩,
   ⟨⟨-93, 9⟩, ⟨-91, 9⟩⟩,
   ⟨⟨-79, 10⟩, ⟨-77, 10⟩⟩,
   ⟨⟨-97, 12⟩, ⟨-95, 12⟩⟩,
   ⟨⟨-85, 15⟩, ⟨-83, 15⟩⟩,
   ⟨⟨-69, 22⟩, ⟨-67, 22⟩⟩]
theorem checked17 : caseOK p16 p17 ⟨-8936830510563328, 0⟩ w17 = true := by decide +kernel
theorem pair17 : OriginalPair 17 :=
  original_of_window row16 row17 (by decide) (by decide) checked17
def p18 : List ℤ := [1, 258078, 296490728, 33952367786, 1062396120124, 12802836780046, 69619561030488, 186367701826346, 257465590782726, 186367701826346, 69619561030488, 12802836780046, 1062396120124, 33952367786, 296490728, 258078, 1]
def t18 : List (List ℤ) := (0 :: p18) :: t17
theorem h18 : coefficientTable weights 18 = t18 :=
  table_step h17 (by decide +kernel)
theorem row18 : LongCycles.enumerator 18 5 = Polynomial.X * ofCoeffs p18 :=
  row_from_table (past := t17) h18
def w18 : List Window := [⟨⟨-128000, 0⟩, ⟨-125952, 0⟩⟩,
   ⟨⟨-648, 0⟩, ⟨-632, 0⟩⟩,
   ⟨⟨-119, 1⟩, ⟨-117, 1⟩⟩,
   ⟨⟨-69, 2⟩, ⟨-67, 2⟩⟩,
   ⟨⟨-117, 4⟩, ⟨-115, 4⟩⟩,
   ⟨⟨-109, 5⟩, ⟨-107, 5⟩⟩,
   ⟨⟨-113, 6⟩, ⟨-111, 6⟩⟩,
   ⟨⟨-65, 6⟩, ⟨-127, 7⟩⟩,
   ⟨⟨-73, 7⟩, ⟨-71, 7⟩⟩,
   ⟨⟨-77, 8⟩, ⟨-75, 8⟩⟩,
   ⟨⟨-71, 9⟩, ⟨-69, 9⟩⟩,
   ⟨⟨-121, 11⟩, ⟨-119, 11⟩⟩,
   ⟨⟨-69, 12⟩, ⟨-67, 12⟩⟩,
   ⟨⟨-103, 16⟩, ⟨-101, 16⟩⟩,
   ⟨⟨-67, 23⟩, ⟨-65, 23⟩⟩]
theorem checked18 : caseOK p17 p18 ⟨-8936830510563328, 0⟩ w18 = true := by decide +kernel
theorem pair18 : OriginalPair 18 :=
  original_of_window row17 row18 (by decide) (by decide) checked18
def p19 : List ℤ := [1, 519233, 939226032, 148807096304, 6119148120924, 95648109039388, 676561972663248, 2382516754435216, 4413306247800134, 4413306247800134, 2382516754435216, 676561972663248, 95648109039388, 6119148120924, 148807096304, 939226032, 519233, 1]
def t19 : List (List ℤ) := (0 :: p19) :: t18
theorem h19 : coefficientTable weights 19 = t19 :=
  table_step h18 (by decide +kernel)
theorem row19 : LongCycles.enumerator 19 5 = Polynomial.X * ofCoeffs p19 :=
  row_from_table (past := t18) h19
def w19 : List Window := [⟨⟨-260096, 0⟩, ⟨-256000, 0⟩⟩,
   ⟨⟨-1040, 0⟩, ⟨-1016, 0⟩⟩,
   ⟨⟨-85, 0⟩, ⟨-83, 0⟩⟩,
   ⟨⟨-91, 2⟩, ⟨-89, 2⟩⟩,
   ⟨⟨-75, 3⟩, ⟨-73, 3⟩⟩,
   ⟨⟨-71, 4⟩, ⟨-69, 4⟩⟩,
   ⟨⟨-75, 5⟩, ⟨-73, 5⟩⟩,
   ⟨⟨-85, 6⟩, ⟨-83, 6⟩⟩,
   ⟨⟨-99, 7⟩, ⟨-97, 7⟩⟩,
   ⟨⟨-113, 8⟩, ⟨-111, 8⟩⟩,
   ⟨⟨-117, 9⟩, ⟨-115, 9⟩⟩,
   ⟨⟨-111, 10⟩, ⟨-109, 10⟩⟩,
   ⟨⟨-93, 11⟩, ⟨-91, 11⟩⟩,
   ⟨⟨-99, 13⟩, ⟨-97, 13⟩⟩,
   ⟨⟨-65, 16⟩, ⟨-127, 17⟩⟩,
   ⟨⟨-67, 24⟩, ⟨-65, 24⟩⟩]
theorem checked19 : caseOK p18 p19 ⟨-8936830510563328, 0⟩ w19 = true := by decide +kernel
theorem pair19 : OriginalPair 19 :=
  original_of_window row18 row19 (by decide) (by decide) checked19
end LongCycleFinite.K5Prefix
