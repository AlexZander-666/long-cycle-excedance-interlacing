# Cutoff seven: the middle and exterior sign estimates

Independent derivation, 27 November 2026. Let the upper size be \(n\ge96\) and put \(p=n-1\). The analytic estimates below hold for every fixed choice of the five independent weights \(w_2,\ldots,w_6\in[0,1]\), with \(w_1=0\) and \(w_a=1\) for \(a\ge7\). Together with the compact estimate on \([0,16]\), they give the strict sign at every lower-row negative root, including at \(t=-1\) via the compact estimate. The separate integer prefix covers all hard-cutoff pairs at upper sizes \(8,\ldots,95\). Here the original statistic is the number of indices \(i\) for which \(i<\pi(i)\). [Alexandersson's problem, SymCat](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles).

## The six offsets from the original rows

Define the actual weighted polynomial
\[
 F_j(t)=\sum_{\pi\in S_j}t^{\operatorname{exc}(\pi)}
                \prod_{C\text{ cycle of }\pi}w_{|C|}.
\]
Write \(r=e^{-x}\), \(t=-r\), \(\rho=\sqrt{x^2+\pi^2}\), \(s=\pi/\rho\), and \(M_a=t A_{a-1}(t)/(1-t)^a\). For cycles of length \(a\ge2\) the numerator is their true strict-excedance polynomial. The \(a=1\) value \(M_1=t/(1-t)\) simply completes the Eulerian generating function identity. It cancels from the coefficient of a one-cycle since \(w_1=0\).

The cycle exponential formula gives \(H_j=F_j(t)/(1-t)^j=(1+r)j![z^j]B(z)L(z)\), where
\[
 L(z)=\frac1{1+r e^z},\qquad
 B(z)=\exp\!\left(\sum_{a=1}^{6}b_a z^a\right),\qquad
 b_a=(w_a-1)M_a/a!.
\]
In detail, all normalized row coefficients have exponential generating function \(\exp(\sum_{a\ge1}w_aM_a z^a/a!)\). Sum the unweighted series using \(M_a=\sum_{h\ge1}(-r)^h h^{a-1}\) for \(x>0\), which gives \(\log((1+r)/(1+r e^z))\). Coefficients extend to \(x=0\) by continuity. The same Eulerian identity gives \(M'_a=-M_{a+1}\) in \(x\). Applying \(\partial_z+\partial_x\) to the weighted exponential series and comparing coefficients gives
\[
 H_n+H'_p=\sum_{a=1}^{6}(p)_a C_a H_{p-a},\qquad
 C_a=(w_{a+1}-w_a)M_{a+1}/a!.
\]
This formula uses \(p-a=n-a-1\), so the needed rows are \(n-2,n-3,n-4,n-5,n-6,n-7\), alongside \(n-1,n\). In particular the last offset uses the seventh moment.

Set \(Y_j=\rho^{j+1}[z^j](BL)\), \(V_j=\rho^{j+1}[z^j]L\), and \(A_j=H_j/(1+r)\). At \(H_p=0\) it is sufficient to have either
\[
 |Y_n|>\frac1n\sum_{a=1}^{6}|C_a|\rho^{a+1}|Y_{n-a-1}|,
 \qquad\text{or}\qquad
 |A_n|>\sum_{a=1}^{6}(p)_a|C_a|\,|A_{n-a-1}|.
\]
The scaled factor \(1/n\) is exactly \((p)_a(p-a)!/n!\). Either bound implies \(H_n(-H'_p)>0\) by the displayed identity. [Original insertion and readout in Lean](../formal/LongCycleBounds/FixedCutoffReadout.lean).

The normalized moments through order six satisfy \(|M_a|\le r\). With \(u=(1-r)/(1+r)\) and \(h=r/(1+r)^2\), the factors of \(-h\) at orders \(2,3,4,5,6\) are respectively \(1,u,1-6h,3u^3-2u,1-30h+120h^2\). The last two have absolute value at most one by their interior critical points and endpoints on \([0,1]\) and \([0,1/4]\). At order seven the factor is \(u(1-60h+360h^2)\), equivalently \((17/2)u-30u^3+(45/2)u^5\). The exact Bernstein check certifies \(|M_7|\le(21/20)r\) on the entire closed logistic interval. Thus \(|b_a|\le r/a!\) for all six tilt terms and \(|C_a|\le r/a!\) for \(a\le5\), with \(|C_6|\le(21/20)r/6!\). [Seventh moment certificate](moment.py).

## Middle region \(16\le x\le3\sqrt{n-1}\)

Use the naked logistic bounds
\[
 |V_j|\le 2+\frac{1}{(j+1)s^2}\quad(j\ge1),\qquad
 |V_j|\le\frac{2\rho^2}{x}\quad(j\ge0,\ x\ge9).
\]
The first follows from the signed odd poles by comparison of the decreasing positive tail with its integral. The second is the all-order envelope, including \(V_0=\rho/(1+r)\). Also \(ns^2\ge1\) here since \(x^2\le9(n-1)\) and \(\pi^2>9\). The existing naked logistic phase bound at \(ns^2\ge1\) implies \(|Y_n|>s/2\) if \(Y_{n-1}=0\) and \(|Y_j-V_j|<s/4\) for \(j=n-1,n\). For that implication one has \(|V_{n-1}|<s/4\), the naked phase gives \(|V_n-(x/\rho)V_{n-1}|>s\), and the two perturbations cost less than \(s/2\). [Ordered pole bound](../formal/LongCycleBounds/FixedFour49PoleMass.lean), [phase bound and all-order envelope](../formal/LongCycleBounds/FiveMiddlePhase.lean).

Let \(D(R)=\sum_{a=1}^{6}R^a/a!\), \(d_A=D(16)/16^6\), \(\alpha=51/50\), and \(v(R)=\sum_{a=1}^{6}|b_a|R^a\). Then \(v(R)\le rD(R)\), \(D(R)\le d_A R^6\) for \(R\ge16\), and \(\rho\le\alpha x\). The absolute coefficient norm of \(B-1\) at radius \(R\) is at most \(e^{v(R)}-1\) by the exponential expansion and the triangle inequality. The inequalities \(157/50<\pi<22/7\) and \(e^{-16}<1/8800000\) give
\[
 v(\rho)\le v_0=\frac{d_A(16\alpha)^6}{8800000}<\frac1{200},
 \qquad e^{v(2\rho)}\le \frac{1}{1-64v_0}<2.
\]
Here and below \(x^b e^{-x}\) decreases for \(x\ge16\) and \(b\le9\). The second estimate uses \(e^y\le(1-y)^{-1}\) for \(0\le y<1\).

Write \(B_i=[z^i]B(z)\). For every \(j\ge n-7\) split \(Y_j-V_j=\sum_{i=1}^j B_i\rho^i V_{j-i}\) at \(i=\lfloor j/2\rfloor\). In the head, \(m=j-i\) satisfies \(m\ge1\) and \(2(m+1)\ge j+2\ge n-5\). Consequently the head divided by \(s\) is bounded by
\[
 \frac{d_A e^{-x}}{\pi(1-v_0)}
       \left(2\rho^7+\frac{2\rho^9}{(n-5)\pi^2}\right)
 <\frac{1}{16}.
\]
Indeed the logistic factor is at most \(2+2\rho^2/((n-5)\pi^2)\) and the tilt factor is at most \(v(\rho)/(1-v_0)\). To check \(1/16\) one substitutes the rational upper bound on \(e^{-16}\), \(\alpha\cdot16\) for the optimized powers of \(\rho\), \(91\) for \(n-5\), and \(157/50\) for the lower factors of \(\pi\).

Use the all-order logistic envelope in the tail, allowing \(m=0\). Its size divided by \(s\) is at most
\[
 \frac{2\rho^3}{\pi x}\;2^{-\lfloor j/2\rfloor}e^{v(2\rho)}
 \ \le\ 14n\,2^{-\lfloor(n-7)/2\rfloor}<\frac1{1000}.
\]
The prefactor follows from \(2\rho^3/(\pi x)\le18\alpha^3(n-1)/\pi<7n\). The displayed bound is decreasing by increments of two, so only \(n=96,97\) are checked. This proves \(|Y_j-V_j|<s/4\) at every needed index. In the insertion terms \(j\ge n-7\), the individual bounds imply
\[
 |Y_j|\le 2+\frac{n}{n-6}+\frac14<4.
\]
Finally,
\[
 J:=\sum_{a=1}^{6}\frac{|C_a|\rho^{a+1}}s
 \le\frac{r}{\pi}\left(
           \sum_{a=1}^{5}\frac{\rho^{a+2}}{a!}
                   +\frac{21\rho^8}{20\cdot6!}\right)<\frac25.
\]
The same decreasing functions give the same rational substitutions. Then the scaled insertion cost is at most \(4Js/n<s/2<|Y_n|\). Both endpoints of the middle interval are included.

## Exterior region \(x\ge3\sqrt{n-1}\)

For every \(n\ge96\) one has
\[
 n^7 r < 16,\qquad D(n)<n^6/600,\qquad 6n^7<2^{n-7}.
\]
For the first bound, \(\sqrt{95}>487/50\) and the degree-96 Taylor lower bound at \(3(487/50)\) is greater than \(96^7/16\). The logarithmic derivative of \(y^7e^{-3\sqrt{y-1}}\) is negative on \(y\ge96\) since \(9y>14^2\). The second inequality follows from termwise decrease in \(D(n)/n^6\). For the third one check \(96\), then use \((97/96)^7<2\) to pass to each successor. These are the only numerical base checks involving large integers.

Expand \(\displaystyle A_j=\sum_{h\ge0}(-r)^h T_j(h)\) with \(T_j(h)=j![z^j](B(z)e^{hz})\). The series can be extracted from a circle of radius \(<x\) by uniform geometric convergence. For \(h\ge1\) and \(1\le j\le n\), one has
\[
 \left|\frac{T_j(h)}{h^j}-1\right|
   \le \sum_{i=1}^{j}|B_i|\frac{(j)_i}{h^i}
   \le e^{v(n)}-1<\frac1{6n}.
\]
Indeed \(v(n)(6n+1)\le[16/(600n)](6n+1)<1\) and \(e^u-1\le u/(1-u)\) for \(0\le u<1\).

For the zero label in the needed range \(n-7\le j\le n\), use the nonconstant coefficient norm at radius \(2n\), together with \(j!\le n^j\). Here \(v(2n)\le64rn^6/600<1/2\), so
\[
 |T_j(0)|\le \frac{j!}{(2n)^j}(e^{v(2n)}-1)
 \le 2^{-j}\cdot\frac{128rn^6}{600}
 <\frac{r}{6n}.
\]
The radius is fixed at \(2n\) for the tilt \(B\) only. The previous geometric coefficient identity uses the smaller circle for \(L\).

Let \(S_j=\sum_{h\ge1}(-1)^h h^jr^h\), let \(h_j\) be an integer maximizing \(h^jr^h\) for \(h\ge1\), and put \(W=h_p^p r^{h_p}\). The established peak inequalities for \(p\ge48,\ x\ge(29/10)\sqrt p\) give mass \(\sum_{h\ge1}h^pr^h\le4W\), \(h_p\le\sqrt p/2\), and
\[
 W/2<|S_n|+(h_p+1)|S_p|.
\]
The last inequality is the adjacent signed-moment comparison from the two geometric tails and the smaller neighboring peak. The theorem with zero-based label index uses \(h_p-1\) for the mode and adds two to that index, giving the displayed \(h_p+1\). Since \(x\ge3\sqrt p\ge(29/10)\sqrt n\) here, the size-\(n\) mass is at most \(4h_n^n r^{h_n}\le4h_n W\le2\sqrt n\,W\le nW/2\). Also \(h_p+1\le n/8\) because \(\sqrt p\ge6\) gives \(\sqrt p/2+1\le p/12+1\le(p+1)/8\). [Mass and modes](../formal/LongCycleBounds/FortyEightPeak.lean), [adjacent signed moments](../formal/LongCycleBounds/OuterMoments.lean).

The positive and zero label error estimates now give
\[
 |A_j-S_j|<W/n\quad(n-7\le j\le p),\qquad
 |A_n-S_n|<W/8.
\]
For the first inequality, the positive-label mass is at most \(4W\) by \(j\le p\), and \(r\le W\), giving \((4W+r)/(6n)\le5W/(6n)\). For the second use \((1+n/2)W/(6n)<W/8\). At \(A_p=0\), the first bound controls the term \((h_p+1)|S_p|<W/8\) in the adjacent comparison, so \(|A_n|>W/4\). For each lagged row \(j\le p\), unimodality gives \(|S_j|\le\max_h h^jr^h\le W\). Therefore \(|A_j|<2W\) at each of the six insertion indices. Using \((p)_a\le n^a\), their total raw cost is at most
\[
 2W\frac{21}{20}rD(n)
  < 2W\frac{21}{20}\frac{16}{600n}<W/4 .
\]
This proves the exterior strict sign through arbitrarily large \(x\), including its left endpoint.

## Coverage and finite certificates

The separately computed compact budget for \(0\le x\le16\), \(n\ge96\), uses the error relative to \(s |B(x+i\pi)|\) for every row down to \(n-7\). At a lower zero a rotation of the first-pole term gives the upper amplitude \(>(2-3\epsilon)s|B(x+i\pi)|\) with compact error \(\epsilon\), while a shorter row has size at most \((2+\epsilon)|B(x+i\pi)|\). The cell check controls \((3\epsilon+(2+\epsilon)J/n)/2<1\), exactly the scaled insertion requirement. Endpoints are closed. [Compact check and transcript](compact.log).

Inversion of a permutation preserves cycle lengths and exchanges excedances and deficiencies. With singleton weight zero this makes \(F_j/t\) reciprocal of degree \(j-2\). The exact single-cycle contributions give constant and leading coefficients both one for \(j\ge7\). At a negative root of the lower quotient, \(H_n(-H'_p)>0\) gives that the upper quotient times the derivative of the lower quotient is negative. This sign transports from \(t\in[-1,0)\) to \(t<-1\): the reciprocal polynomial identity differentiates at the root, and the product transforms by \(-t^{2n-7}>0\).

For fixed \(n\ge96\) deform the short weights simultaneously on the straight segment from all ones (ordinary derangements) to the specified profile. The lower quotient starts with simple negative zeros by the derangement result. It cannot acquire a multiple negative zero because the proved product is strict at every negative lower zero throughout the segment. The fixed leading and constant coefficients and continuous intermediate coefficients prevent escape to infinity or passage through zero. Hence all lower quotient roots remain simple and negative. At these roots the upper quotient values have alternating signs opposite to the derivatives of the lower quotient. Its leading and constant coefficients give the two exterior signs. The degree difference of one accounts for every upper root in a separate interval. This proves simple negative strict interlacing for all five independent weights at every upper size \(n\ge96\). The original rows share a simple zero at zero and satisfy ordinary weak interlacing. [Derangement anchor](../formal/LongCycleBounds/DerangementAnchor.lean), [independent profile readout](../formal/LongCycleBounds/CycleProfileIndependentReadout.lean).

The hard cutoff takes \(w_2=\cdots=w_6=0\). The exact finite certificate covers upper sizes \(8,\ldots,95\), so the paper proof and the separate finite computation together cover every consecutive pair of nonzero hard-cutoff rows. The first nonzero row \(F_7=t A_6\) is also covered by the first pair. The finite certificate concerns this hard profile. Below 96 the continuous five-dimensional weight range is outside this result. [Finite source and transcript](prefix.log).

Run **python3 -IB middle_outer.py** from this directory to replay the exact rational bounds of the two new sections. The mathematics above is an independently checked derivation using prior Lean results for the logistic and modal inequalities. Its degree-six insertion estimates have their own rational replay. Full cutoff-seven kernel acceptance and the ongoing independent web review are tracked separately.
