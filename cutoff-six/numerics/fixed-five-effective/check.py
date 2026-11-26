"""Rational majorants for a quartic tilt. Only the final displayed comparisons are rounded."""
from fractions import Fraction as F
from math import factorial, isqrt
P, Q = F(314159,100000), F(314160,100000)
S = 10**7

def up(x):
    return F(-(-x.numerator*S//x.denominator),S)

def down(x):
    return F(x.numerator*S//x.denominator,S)

def sqrt_up(x):
    x=F(x); a=isqrt(x.numerator*S*S//x.denominator)
    return F(a+(F(a,S)**2<x),S)

def exp_up(x):
    x=F(x)
    # Repeated squaring, with outward rounding at each operation.
    assert x>=0
    e=0
    while x>F(1,4):
        x/=2; e+=1
    poly=sum((x**i/factorial(i) for i in range(13)),F(0))
    out=up(poly + x**13/factorial(13)/(1-x/14))
    for i in range(e):out=up(out*out)
    return out

def exp_neg(x):
    x=F(x)
    if x==0:return F(1),F(1)
    lower=sum((x**i/factorial(i) for i in range(65)),F(0))
    return down(1/exp_up(x)),up(1/lower)

def compact(N,A,step=F(1,8)):
    j=N-5
    worst=(0,None)
    Kmax=(0,None)
    budget=(0,None)
    cuts=int(F(A)/step)
    for i in range(cuts):
        a,b=i*step,(i+1)*step
        rlo,rhi=exp_neg(b)[0],exp_neg(a)[1]
        yhi=rhi/(1+rhi); Hhi=rhi/(1+rhi)**2; Hlo=rlo/(1+rlo)**2
        # For t=-exp(-x), q=(1-r)/(1+r), H=r/(1+r)^2.
        zl,zh=(1-rhi)/(1+rhi),(1-rlo)/(1+rlo)
        m2=up(Hhi)
        m3=up(Hhi*zh)
        m4=up(Hhi*max(abs(1-6*Hlo),abs(1-6*Hhi)))
        m5=up(Hhi*zh*max(abs(1-12*Hlo),abs(1-12*Hhi)))
        B=(up(yhi),up(m2/2),up(m3/6),up(m4/24))
        rho=sqrt_up(b*b+Q*Q)
        # Lower bound for log |B(zeta)| using the signed real powers.
        re=([a,b],[a*a-Q*Q,b*b-P*P],
            [a**3-3*Q**2*b,b**3-3*P**2*a],
            [a**4-6*Q**2*b*b+P**4,b**4-6*P**2*a*a+Q**4])
        # b1,b2,b3 nonnegative; sign of b4 follows 1-6H.
        loss=max(F(0),-re[1][0])*B[1]+max(F(0),-re[2][0])*B[2]
        if 6*Hlo>=1: loss+=max(F(0),re[3][1])*B[3]
        elif 6*Hhi<=1: loss+=max(F(0),-re[3][0])*B[3]
        else:loss+=max(abs(v) for v in re[3])*B[3]
        invD=exp_up(up(loss))
        s_inv=up(rho/P)
        drift=up((m2*rho**3+m3*rho**4/2+m4*rho**5/6+m5*rho**6/24)/P)
        # Any one of the rational radii is a rigorous certificate for the full cell.
        cand=[]
        for q in range(21,61):
            lam=F(q,20)
            if lam**2*(b*b+P*P)>b*b+9*P*P:continue
            R=rho*lam
            coeff=max(rho,lam*rho*rho/(2*P**2))
            cost=up(sum(v*R**i for i,v in enumerate(B,1)))
            err=up(coeff*exp_up(cost)*invD*s_inv/lam**j)
            cand.append((err,lam))
        error,lam=min(cand)
        # sufficient positive gap 2-3 epsilon > (2+epsilon)*drift/N
        ratio=up((3*error+(2+error)*drift/N)/2)
        worst=max(worst,(error,(a,b,lam)))
        Kmax=max(Kmax,(drift,(a,b,lam)))
        budget=max(budget,(ratio,(a,b,lam)))
    return worst,Kmax,budget


def middle(N,A):
    alpha=sqrt_up(1+(Q/A)**2)
    r=exp_neg(A)[1]
    A=F(A)
    C=1/A**3+1/(2*A**2)+1/(6*A)+F(1,24)
    v=up(C*alpha**4*A**4*r)
    assert 0<v<1 and exp_up(16*v)<2
    head=up(C*r*(2*alpha**5*A**5+2*alpha**7*A**7/((N-3)*P**2))/(P*(1-v)))
    assert 18*alpha**3/P<7
    tail=up(max(F(14*n,2**((n-5)//2)) for n in (N,N+1)))
    assert head+tail<F(1,4)
    J=up(C*r*alpha**6*A**6/P)
    assert J<1
    V=2+F(N,N-4)
    assert V+F(1,4)<4
    assert 4*J/N<F(1,2)
    return v,head,tail,J

def exterior(N):
    floor=F(isqrt((N-1)*10**8),10**4)
    assert floor**2<=N-1
    def lower_exp(x):return sum((x**i/factorial(i) for i in range(90)),F(0))
    assert lower_exp(3*floor)>3*N**5
    # derivative of 5 log n - 3sqrt(n-1) < 0; 3n>10sqrt(n-1) for n>=49.
    assert N>=49 and 9*N>100
    assert F(1,N**3)+F(1,2*N**2)+F(1,6*N)+F(1,24)<F(1,21)
    assert 1/(1-F(1,63*N))/63<F(1,60)
    assert lower_exp(3*floor/4)>2*N and 9*N>64
    assert exp_up(F(41,24))<6
    assert 360*N**5<=2**(N-9) and F(N+1,N)**5<2
    assert F(4*N+1,60*N)<F(1,12)
    print("Exterior: 3 r n^5 < 1, quarter-exponential radius > 2n, both label errors <= 1/(60n).")

def full():
    N,A=49,11
    worst,drift,budget=compact(N,A)
    assert worst[0]<F(3,1000) and drift[0]<F(48,5) and budget[0]<F(1,5)
    print('Compact maxima (relative residue, drift/s, normalized phase+insertion):',worst,drift,budget)
    print('Middle (v, head/s, tail/s, drift/s):',middle(N,A))
    exterior(N)
    print('PASS all budgets for n>=49, weights in [0,1]^3.')

if __name__=='__main__':full()
