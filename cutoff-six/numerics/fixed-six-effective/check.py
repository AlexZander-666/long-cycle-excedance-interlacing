"""Cutoff six: outward rational bounds on each closed interval and full hard prefix."""
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from importlib.util import spec_from_file_location, module_from_spec
from math import factorial, gcd
from pathlib import Path
import sys


def load_sibling(name):
    path = Path(__file__).resolve().parents[1] / "fixed-five-effective" / (name + ".py")
    spec = spec_from_file_location("five_" + name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


base = load_sibling("check")
finite = load_sibling("finite")
P,Q = base.P, base.Q
up, sqrt_up, exp_up, exp_neg = base.up, base.sqrt_up, base.exp_up, base.exp_neg
N, A = 49, 13


def compact():
    maxima = []
    cells = []
    for i in range(8*A):
        a, b = F(i,8), F(i+1,8)
        rlo, rhi = exp_neg(b)[0], exp_neg(a)[1]
        hlo, hhi = rlo/(1+rlo)**2, rhi/(1+rhi)**2
        vmax = (1-rlo)/(1+rlo)
        # M6 = -H(1-30H+120H^2) and |the quadratic|<=1 on [0,1/4].
        m = [rhi/(1+rhi), hhi, hhi*vmax,
             hhi*max(abs(1-6*hlo),abs(1-6*hhi)),
             hhi*vmax*max(abs(1-12*hlo),abs(1-12*hhi)), hhi]
        rho = sqrt_up(b*b+Q*Q)
        tilts = [up(m[j-1]/factorial(j)) for j in range(1,6)]
        loss = up(sum(v*rho**j for j,v in enumerate(tilts,1)))
        drift = up(sum(m[j]*rho**(j+2)/factorial(j) for j in range(1,6))/P)
        errors = []
        for q in range(21,61):
            lam = F(q,20)
            if lam**2*(b*b+P*P)>b*b+9*P*P:
                continue
            shell = up(sum(v*(rho*lam)**j for j,v in enumerate(tilts,1)))
            e = up(max(rho,lam*rho*rho/(2*P**2))*rho/P*exp_up(shell+loss)/lam**(N-6))
            errors.append((e,lam))
        e, lam = min(errors)
        budget = up((3*e+(2+e)*drift/N)/2)
        cells.append((i,lam,e,drift,budget))
    for col in [2,3,4]:
        maxima.append(max((c[col],c[0]) for c in cells))
    assert maxima[0][0] < F(7,50) and maxima[1][0] < 15 and maxima[2][0] < F(21,50)
    print("compact (exact upper bound, cell index) for residue/sD, J/s, phase budget:",maxima)
    contents = "cell\tlambda\tresidue_over_sD\tdrift_over_s\tcombined\n"
    contents += "".join("\t".join(map(str,c))+"\n" for c in cells)
    if "--write" in sys.argv:
        Path(__file__).with_name("cells.tsv").write_text(contents)
    else:
        assert Path(__file__).with_name("cells.tsv").read_text()==contents


def middle():
    a = F(A)
    alpha = sqrt_up(1+(Q/a)**2)
    C = sum(1/(factorial(j)*a**(5-j)) for j in range(1,6))
    r = exp_neg(a)[1]
    v = up(C*alpha**5*a**5*r)
    head = up(C*r*(2*alpha**6*a**6+2*alpha**8*a**8/((N-4)*P**2))/(P*(1-v)))
    wide = exp_up(32*v)
    assert v < F(13,1000) and wide<2
    assert 18*alpha**3/P < 7
    tail = up(max(F(14*n,2**((n-6)//2)) for n in (N,N+1)))
    assert head+tail < F(4,25) < F(1,4)
    J = up(C*r*alpha**7*a**7/P)
    assert J< F(3,4) and 2+F(N,N-5)+F(1,4)<4 and 4*J/N<F(1,2)
    print("middle v, doubled cost, head/s, tail/s, drift/s:",v,wide,head,tail,J)


def exterior():
    # sqrt(48)>6.92; verify exp(3sqrt(48))>7*49^5/2 by finite Taylor.
    z=3*F(692,100)
    assert (z/3)**2 < N-1
    assert sum(z**j/factorial(j) for j in range(95)) > F(7*N**5,2)
    assert 9*N>11**2 # ensures n^(11/2) exp(-3sqrt(n-1)) decreases
    assert sum(F(1,factorial(i)*N**(5-i)) for i in range(1,6))<F(1,100)
    assert (1-F(1,50))**-1/50<F(1,40)
    assert 6*N**5*40*7<100*2**(N-6)
    assert F(N+1,N)**6<2
    # m+1 <= sqrt(p)/2 + 1 <= 2sqrt(p)/3 ; n-th mass <= 3sqrt(p)*W.
    assert 36<N-1 and 4*N<9*(N-1)
    assert F(1,2)-F(2,3)*F(5,40)-(3+F(1,6))/40 >F(1,3)
    assert F(2,50)<F(1,3)
    print("exterior positive labels <1/(40 sqrt p); zero label <r/(40 sqrt p); upper >W/3.")


def prefix():
    rows=finite.rows(N-1,6)
    for j in range(6,10):
        assert finite.brute(j,6)==rows[j]
    digest=sha256()
    count=0
    for n in range(7,N):
        a=finite.primitive(rows[n][1:]); b=finite.primitive(rows[n-1][1:])
        assert rows[n][0]==rows[n-1][0]==0
        assert len(a)==n-1 and len(b)==n-2 and all(x>0 for x in a+b)
        while len(b)>1:
            c=finite.primitive(finite.signed_remainder(a,b))
            assert len(b)==len(a)-1 and len(c)==len(b)-1 and c[-1]>0,(n,len(b))
            count+=1
            digest.update((str(c)+"\n").encode())
            a,b=b,c
        assert len(a)==2 and len(b)==1 and b[0]>0
    print("hard six: all 42 pairs 7..48; literal n=6..9; two source recurrences; chains",
          count,digest.hexdigest())


if __name__=="__main__":
    compact();middle();exterior();prefix()
    print("PASS")
