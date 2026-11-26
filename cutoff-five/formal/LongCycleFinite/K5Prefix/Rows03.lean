import LongCycleFinite.K5Prefix.Base

namespace LongCycleFinite.K5Prefix
open LongCycleBounds.CycleProfile.Counterexample
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def t0 : List (List ℤ) := [[1]]
theorem h0 : coefficientTable weights 0 = t0 := rfl
def t1 : List (List ℤ) := [] :: t0
theorem h1 : coefficientTable weights 1 = t1 :=
  table_step h0 (by decide +kernel)
def t2 : List (List ℤ) := [0, 0] :: t1
theorem h2 : coefficientTable weights 2 = t2 :=
  table_step h1 (by decide +kernel)
def t3 : List (List ℤ) := [0, 0, 0] :: t2
theorem h3 : coefficientTable weights 3 = t3 :=
  table_step h2 (by decide +kernel)
end LongCycleFinite.K5Prefix
