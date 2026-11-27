"""Certify the seventh signed cycle moment on the full closed logistic interval."""
from fractions import Fraction as F
from math import comb


def eulerian(n):
    row = [1]
    for size in range(2, n + 1):
        row = [(k + 1) * (row[k] if k < len(row) else 0)
               + (size - k) * (row[k - 1] if k else 0) for k in range(size)]
    return row


def bernstein_coefficients(coeff, left, width):
    degree = len(coeff) - 1
    power = [sum(coeff[j] * comb(j, k) * left**(j-k) * width**k
                 for j in range(k, degree + 1)) for k in range(degree + 1)]
    return [sum(power[k] * F(comb(i, k), comb(degree, k)) for k in range(i + 1))
            for i in range(degree + 1)]


def main():
    # v=(1-r)/(1+r), H=r/(1+r)^2. This is -M7/H in the v coordinate.
    p = [F(0), F(17, 2), F(0), F(-30), F(0), F(45, 2)]
    scaled = [sum(p[j] * F(comb(2, i-j), 4)
                  for j in range(len(p)) if 0 <= i-j <= 2) for i in range(8)]
    coeff = eulerian(6)
    assert coeff == [1, 57, 302, 302, 57, 1]

    def eval_at(poly, x):
        return sum(c * x**i for i, c in enumerate(poly))

    # After multiplication by (1+r)^7, both sides of the identity between
    # the direct Eulerian expression and the transformed polynomial have degree ≤7.
    for r in map(F, range(1, 9)):
        v = (1-r)/(1+r)
        assert eval_at(scaled, v) * (1+r)**7 == eval_at(coeff, -r)
    for poly, limit, name in [(p, F(11, 6), 'height'), (scaled, F(21, 20), 'exp(-x)')]:
        pieces = 32
        bounds = [abs(c) for i in range(pieces)
                  for c in bernstein_coefficients(poly, F(i, pieces), F(1, pieces))]
        assert max(bounds) < limit
        print(f'full interval |M7|/{name} <= {max(bounds)} < {limit}')
    for r in (F(1, 2), F(1, 11)):
        v = (1-r)/(1+r)
        print(f'r={r}: |M7|/height={abs(eval_at(p,v))}, |M7|/r={abs(eval_at(scaled,v))}')
    assert abs(eval_at(p, F(1, 3))) == F(49, 27)
    assert abs(eval_at(scaled, F(5, 6))) > 1


if __name__ == '__main__':
    main()
