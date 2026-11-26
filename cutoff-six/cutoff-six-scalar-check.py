"""Exact rational checks for the cutoff-six proof in the manuscript."""

from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from math import factorial
from pathlib import Path


root = Path(__file__).resolve().parent
if not (root / "numerics").is_dir():
    root = root.parents[1] / "research" / "long-cycles"
else:
    root = root / "numerics"
spec = spec_from_file_location("cutoff_six_check", root / "fixed-six-effective" / "check.py")
module = module_from_spec(spec)
spec.loader.exec_module(module)


def check_middle():
    base = Q(13)
    alpha = module.sqrt_up(1 + (module.Q / base) ** 2)
    cost = sum(1 / (factorial(j) * base ** (5 - j)) for j in range(1, 6))
    exp_minus_base = module.exp_neg(base)[1]
    v_bound = Q(13, 1000)
    assert cost * alpha**5 * base**5 * exp_minus_base < v_bound
    assert module.exp_up(32 * v_bound) < 2
    head = cost * exp_minus_base / (module.P * (1 - v_bound))
    head *= 2 * alpha**6 * base**6 + 2 * alpha**8 * base**8 / (45 * module.P**2)
    assert head < Q(153, 1000)
    assert 18 * alpha**3 / module.P < 7
    assert max(Q(14*n, 2**((n-6)//2)) for n in (49, 50)) < Q(409, 1250000)
    assert Q(51, 49) < 2
    drift = cost * exp_minus_base * alpha**7 * base**7 / module.P
    assert drift < Q(3, 4)
    assert 4 * drift / 49 < Q(1, 2)
    assert 2 + Q(49, 44) + Q(1, 4) < 4
    print("middle printed budgets passed with v_* = 13/1000")


def check_exterior():
    n = 49
    y = Q(69, 10)
    assert y**2 < n - 1
    assert y > 4  # Then 12u/(1+u²)<12/u<3 for u≥y.
    assert (1 + y*y)**6 / 14 < sum((3*y)**j / factorial(j) for j in range(64))
    assert sum(Q(1, factorial(j) * n**(5-j)) for j in range(1, 6)) < Q(1, 100)
    assert 14 * (6 + Q(1, n)) / 100 < 1
    assert Q(32*14, 100*n) < Q(1, 2)
    assert 12 * n**6 <= 2**(n-6) and Q(n+1, n)**6 < 2
    assert 9 * (n-1) > Q(29, 10)**2 * n
    assert 48 * (Q(1, 2) - Q(10, 29))**2 > 1
    assert sum(Q(4)**j / factorial(j) for j in range(16)) > 50
    assert 48 * Q(9, 10)**2 > 4**2
    assert Q(1, 50) < Q(1, 7)**2
    # These are the squared base cases for the two mode bounds at n=49.
    assert 16 * 48 <= (49 - 8)**2
    assert 16 * 49 <= 49**2
    # Sum (b+1)a^(b-1), b>=2.
    a = Q(1, 50)
    assert Q(2, 7) + 2 * (a / (1-a)**2 + 2*a / (1-a)) < Q(1, 2)
    assert (1 + Q(n, 2))/(6*n) <= Q(1, 8)
    assert Q(2, 6*n+1) < Q(1, 4)
    print("exterior scalar checks passed for 1/(6n), r/(6n), and W/4")


check_middle()
check_exterior()
