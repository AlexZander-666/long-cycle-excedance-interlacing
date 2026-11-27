"""Exactly check the 43 remaining hard-cutoff adjacent pairs using primitive Sturm chains."""
from functools import reduce
from hashlib import sha256
from itertools import permutations
from math import comb,gcd

def trim(p):
    while p and p[-1]==0:p.pop()
    return p

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return trim(c)

def mul(a,b):
    c=[0]*(len(a)+len(b))
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)

def scale(a,s):
    return trim([x*s for x in a])

def primitive(p):
    trim(p)
    if not p:return p
    d=reduce(gcd,p,0)
    return [x//d for x in p]

def signed_remainder(a,b):
    a=a[:]
    assert b and b[-1]>0
    while len(a)>=len(b):
        d=len(a)-len(b)
        # Positive multiplication by leading coefficient preserves the remainder's sign.
        a=primitive(add(scale(a,b[-1]),[0]*d+scale(b,-a[-1])))
    return [-v for v in a]

def euler(j):
    rows=[[1]]
    for i in range(j):
        a=rows[-1]
        b=[0]*(i+1)
        for l,v in enumerate(a):
            b[l]+=(l+1)*v
            if l<i:b[l+1]+=(i-l)*v
        rows.append(trim(b))
    return rows

def rows(N,k):
    A=euler(N); out=[[1]]
    for j in range(1,N+1):
        direct=[]
        for h in range(k,j+1):
            direct=add(direct,scale(mul([0]+A[h-1],out[j-h]),comb(j-1,h-1)))
        ins=[]
        for e,x in enumerate(out[j-1]):
            ins=add(ins,[0]*e+[e*x,(j-1-e)*x])
        if j>=k:
            ins=add(ins,scale(mul([0]+A[k-1],out[j-k]),comb(j-1,k-1)))
        assert trim(ins)==direct
        out.append(direct)
    return out

def brute(n,k):
    coef=[0]*n
    for p in permutations(range(n)):
        seen=set()
        good=True
        for i in range(n):
            if i in seen:continue
            j=i;d=0
            while j not in seen:
                seen.add(j); d+=1; j=p[j]
            if d<k:good=False;break
        if good:coef[sum(i<v for i,v in enumerate(p))]+=1
    return trim(coef)

def main():
    k=5
    E=rows(48,k)
    for n in range(5,9):
        assert brute(n,k)==E[n]
    total=0
    dig=sha256()
    for n in range(k+1,49):
        assert E[n][0]==0 and E[n-1][0]==0
        a=primitive(E[n][1:]); b=primitive(E[n-1][1:])
        assert len(a)==n-1 and len(b)==n-2 and all(x>0 for x in a+b)
        while len(b)>1:
            c=primitive(signed_remainder(a,b))
            assert len(b)==len(a)-1 and len(c)==len(b)-1 and c[-1]>0,(n,len(b))
            total+=1
            dig.update((str(c)+'\n').encode())
            a,b=b,c
        assert len(a)==2 and len(b)==1 and b[0]>0
    print('PASS k=5 all 43 hard adjacent pairs n=6..48; literal permutations 5..8; both exact recurrences agree.')
    print('Positive strict primitive remainder-chain checks:',total,'SHA-256',dig.hexdigest())

if __name__=='__main__':main()
