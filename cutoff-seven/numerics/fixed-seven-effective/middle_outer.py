"""Exact scalar certificates for the cutoff-seven middle and exterior proof."""

from fractions import Fraction as Q
from math import factorial


N = 96
A = 16
ALPHA = Q(51, 50)
PI_LOW = Q(157, 50)
PI_HIGH = Q(22, 7)
R_HIGH = Q(1, 8_800_000)
DRIFT_FACTOR = Q(21, 20)


def exp_lower(x, degree):
    assert x >= 0
    term = total = Q(1)
    for j in range(1, degree + 1):
        term *= x / j
        total += term
    return total


def polynomial_ratio(at):
    return sum(Q(1, factorial(i) * at ** (6 - i)) for i in range(1, 7))


def ceiling_decimal(value, places=9):
    unit = 10**places
    integer = -(-value.numerator * unit // value.denominator)
    return f"{integer // unit}.{integer % unit:0{places}d}"


def middle():
    assert N - 7 == 89
    assert A * A + PI_HIGH**2 < (ALPHA * A)**2
    assert 9 < PI_LOW**2
    assert exp_lower(Q(A), 64) > 8_800_000
    assert A > 9  # decreasing x^m exp(-x) for all powers used
    radius = ALPHA * A
    constant = polynomial_ratio(A)
    cost = constant * R_HIGH * radius**6
    assert cost < Q(1, 200)
    wide = 1 / (1 - 64 * cost)
    assert wide < 2
    head_numerator = constant * R_HIGH * (
        2 * radius**7 + 2 * radius**9 / ((N - 5) * PI_LOW**2))
    head = head_numerator / (PI_LOW * (1 - cost))
    paper_head = head_numerator / (PI_LOW * (1 - Q(1, 200)))
    assert head <= paper_head < Q(1, 16)
    print(f"middle literal paper head / s: {paper_head} < {ceiling_decimal(paper_head)}")
    assert 18 * ALPHA**3 < 7 * PI_LOW
    # Going up by two multiplies these tails by (n+2)/(2*n), less than one.
    assert N + 2 < 2 * N
    tail = max(Q(14 * n, 2 ** ((n - 7) // 2)) for n in (N, N + 1))
    assert tail < Q(1, 1000)
    assert paper_head + tail < Q(1, 4)
    baseline = R_HIGH * sum(radius ** (i + 2) / factorial(i) for i in range(1, 6))
    sixth = DRIFT_FACTOR * R_HIGH * radius**8 / factorial(6)
    drift = (baseline + sixth) / PI_LOW
    assert drift < Q(2, 5)
    assert 2 + Q(N, N - 6) + Q(1, 4) < 4
    assert 4 * drift / N < Q(1, 2)
    for name, computed, abstract in (
        ("tilt cost", cost, Q(1, 200)),
        ("doubled-radius exponential", wide, Q(2)),
        ("head / s", head, Q(1, 16)),
        ("tail / s", tail, Q(1, 1000)),
        ("drift / s", drift, Q(2, 5)),
        ("full shorter-row insertion / s", 4 * drift / N, Q(1, 2)),
    ):
        print(f"middle {name}: outward {ceiling_decimal(computed)}, strict bound {abstract}")


def exterior():
    p = N - 1
    sqrt_lower = Q(487, 50)
    assert sqrt_lower**2 < p
    assert exp_lower(3 * sqrt_lower, 96) > Q(N**7, 16)
    assert 9 * N > 14**2  # makes n^7 exp(-3 sqrt(n-1)) decreasing from 96
    assert polynomial_ratio(N) < Q(1, 600)
    assert 16 * (6 + Q(1, N)) < 600
    assert 64 * Q(16, 600 * N) < Q(1, 2)
    assert Q(128, 600) < 1
    assert 6 * N**7 < 2 ** (N - 7)
    assert Q(N + 1, N)**7 < 2
    assert 9 * p > Q(29, 10)**2 * N
    assert p > 36 and p >= 21 and N >= 16
    assert Q(5, 6) < 1
    assert (1 + Q(N, 2)) / (6 * N) < Q(1, 8)
    assert 1 - Q(6, 8) == Q(1, 4)
    assert 2 * DRIFT_FACTOR * Q(16, 600 * N) < Q(1, 4)
    print("exterior n^7 exp(-3 sqrt(n-1)) < 16 for n >= 96")
    print("exterior positive-label relative error < 1/(6n), zero-label < r/(6n)")
    print("exterior positive peak gap > W/4, six-term drift insertion < W/4")


if __name__ == "__main__":
    middle()
    exterior()
    print("PASS: middle and exterior scalar certificates")
