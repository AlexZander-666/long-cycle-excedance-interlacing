"""Generate a dyadic interlacing certificate for the 43 hard-cutoff-five pairs."""
from fractions import Fraction
from pathlib import Path
from finite import rows

ROOT = Path(__file__).resolve().parent
DEST = ROOT.parent / "formal/LongCycleFinite/K5Prefix"
LAST = 48

def sign(coeffs, x):
    a, b = x.as_integer_ratio()
    v = coeffs[-1]
    den = 1
    for c in reversed(coeffs[:-1]):
        den *= b
        v = a*v + c*den
    return (v > 0) - (v < 0)

def points(p, q):
    degree = len(p)-1
    grid = sorted(-Fraction(65+2*j,64)*Fraction(2)**i
                  for i in range(-LAST-4,LAST+5) for j in range(32))
    values = [sign(p,t) for t in grid]
    assert 0 not in values
    windows=[]
    for a,b,sa,sb in zip(grid,grid[1:],values,values[1:]):
        if sa==sb:
            continue
        for _ in range(80):
            if sign(q,a)==sign(q,b)==sa:
                break
            mid=(a+b)/2
            sm=sign(p,mid)
            if sm==0:
                a,b=(a+mid)/2,(b+mid)/2
            elif sm==sa:
                a=mid
            else:
                b=mid
        else:
            raise ValueError("Could not separate the adjacent-row roots")
        assert a<b<0 and (not windows or windows[-1][1]<a)
        windows.append((a,b))
    assert len(windows)==degree and sign(q,grid[0])==(-1)**(degree+1)
    return grid[0],windows

def dyad(x):
    assert x.denominator.bit_count()==1
    return f"⟨{x.numerator}, {x.denominator.bit_length()-1}⟩"

def coeffs(xs):
    return "["+", ".join(map(str,xs))+"]"

def emit():
    data=rows(LAST,5)
    previous="Base"
    for start in range(0,LAST+1,4):
        upper=min(start+3,LAST)
        mod=f"Rows{upper:02d}"
        out=[f"import LongCycleFinite.K5Prefix.{previous}",
             "", "namespace LongCycleFinite.K5Prefix",
             "open LongCycleBounds.CycleProfile.Counterexample",
             "set_option maxRecDepth 16384","set_option maxHeartbeats 4000000",""]
        for n in range(start,upper+1):
            if n==0:
                out.extend(["def t0 : List (List ℤ) := [[1]]",
                            "theorem h0 : coefficientTable weights 0 = t0 := rfl"])
                continue
            if n>=5:
                assert data[n][0]==0
                out.append(f"def p{n} : List ℤ := {coeffs(data[n][1:])}")
                head=f"(0 :: p{n})"
            else:
                head=coeffs([0]*n if n>1 else [])
            out += [f"def t{n} : List (List ℤ) := {head} :: t{n-1}",
                    f"theorem h{n} : coefficientTable weights {n} = t{n} :=",
                    f"  table_step h{n-1} (by decide +kernel)"]
            if n>=5:
                out += [f"theorem row{n} : LongCycles.enumerator {n} 5 = Polynomial.X * ofCoeffs p{n} :=",
                        f"  row_from_table (past := t{n-1}) h{n}"]
            if n>=6:
                ext,ws=points(data[n-1][1:],data[n][1:])
                brackets=",\n   ".join(f"⟨{dyad(a)}, {dyad(b)}⟩" for a,b in ws)
                out += [f"def w{n} : List Window := [{brackets}]",
                        f"theorem checked{n} : caseOK p{n-1} p{n} {dyad(ext)} w{n} = true := by decide +kernel",
                        f"theorem pair{n} : OriginalPair {n} :=",
                        f"  original_of_window row{n-1} row{n} (by decide) (by decide) checked{n}"]
        out.append("end LongCycleFinite.K5Prefix")
        (DEST/(mod+".lean")).write_text("\n".join(out)+"\n")
        previous=mod
    cases="\n"+"\n".join(f"  · exact pair{n}" for n in range(6,LAST+1))
    (DEST/"All.lean").write_text(f"import LongCycleFinite.K5Prefix.{previous}\n\nnamespace LongCycleFinite.K5Prefix\nset_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\ntheorem finite_original {{n : ℕ}} (lo : 6 ≤ n) (hi : n ≤ 48) : OriginalPair n := by\n  interval_cases n{cases}\n#print axioms finite_original\nend LongCycleFinite.K5Prefix\n")
    print("Resolved every rational window. 43 adjacent pairs using 1032 lower-row roots.")
if __name__=="__main__":
    emit()
