#!/usr/bin/env python3
"""Verify the dyadic certificate by independently reconstructing the original t-rows."""

import argparse
import gzip
from itertools import permutations
from math import comb
from pathlib import Path


FIRST = 4
LAST = 1023
HEADER = "long-cycle-k3-gamma-dyadic-v1"


def check(condition, message):
    if not condition:
        raise ValueError(message)


def permutation_row(n):
    """Directly tabulate E_(n,3) from cycle lengths and excedances."""
    coeffs = [0] * n
    for perm in permutations(range(n)):
        visited = set()
        valid = True
        for a in range(n):
            if a in visited:
                continue
            length = 0
            while a not in visited:
                visited.add(a)
                a = perm[a]
                length += 1
            if length < 3:
                valid = False
                break
        if valid:
            coeffs[sum(a < b for a, b in enumerate(perm))] += 1
    return coeffs


def original_rows(last):
    rows = [[1], [0], [0, 0]]
    for n in range(3, last + 1):
        previous, boundary = rows[-1], rows[-3]
        multiplicity = comb(n - 1, 2)
        row = [0] * n
        for j, c in enumerate(previous):
            row[j] += j * c
            row[j + 1] += (n - 1 - j) * c
        for j, c in enumerate(boundary):
            row[j + 1] += multiplicity * c
            row[j + 2] += multiplicity * c
        rows = [rows[-2], previous, row]
        if n <= 8:
            check(row == permutation_row(n), f"permutation enumeration differs at n={n}")
        yield n, row


def extract_gamma(row):
    quotient = row[1:]
    n = len(row)
    degree = n - 2
    check(row[0] == 0 and quotient == quotient[::-1], f"invalid reciprocal quotient at n={n}")
    check(quotient[0] == 1, f"constant coefficient differs from 1 at n={n}")
    remainder = quotient[: degree // 2 + 1]
    for i in range(len(remainder)):
        coefficient = remainder[i]
        binomial = 1
        for j in range(i + 1, len(remainder)):
            binomial = (binomial * (degree - i - j + 1)) // (j - i)
            remainder[j] -= coefficient * binomial
    check(remainder[-1] > 0, f"gamma degree differs at n={n}")
    return remainder


def dyadic(mantissa, exponent):
    check(0 < mantissa < 2**47 and mantissa % 2 == 1 and -16000 < exponent < 16000,
          "invalid dyadic endpoint")
    return (mantissa, exponent)


def negative_less(left, right):
    """Compare -m * 2**e with -m' * 2**e' using integer shifts."""
    m, e = left
    other, shift = right
    if e >= shift:
        return m << (e - shift) > other
    return m > other << (shift - e)


def endpoint_sign(coeffs, point):
    mantissa, exponent = point
    value = coeffs[-1]
    if exponent >= 0:
        x = -(mantissa << exponent)
        for coefficient in reversed(coeffs[:-1]):
            value = coefficient + x * value
    else:
        step = -exponent
        shift = step
        for coefficient in reversed(coeffs[:-1]):
            value = (coefficient << shift) - mantissa * value
            shift += step
    return (value > 0) - (value < 0)


def verify(last, lines):
    check(next(lines, "").strip() == HEADER, "invalid certificate header")
    previous = []
    roots = 0
    for n, row in original_rows(last):
        gamma = extract_gamma(row)
        if n < FIRST:
            continue
        values = [int(value) for value in next(lines, "").split()]
        degree = len(gamma) - 1
        check(len(values) == 2 + 4 * degree and values[:2] == [n, degree],
              f"invalid row header at n={n}")
        current = []
        for i in range(degree):
            offset = 2 + 4 * i
            left = dyadic(*values[offset:offset + 2])
            right = dyadic(*values[offset + 2:offset + 4])
            check(negative_less(left, right), f"invalid bracket {i} at n={n}")
            if current:
                check(negative_less(current[-1][1], left), f"within-row overlap at n={n}")
            expected_sign = -1 if (degree - i) % 2 else 1
            check(endpoint_sign(gamma, left) == expected_sign
                  and endpoint_sign(gamma, right) == -expected_sign,
                  f"bad endpoint signs in bracket {i} at n={n}")
            current.append((left, right))
        grows = n % 2 == 0
        check(len(current) == len(previous) + grows, f"unexpected adjacent degrees at n={n}")
        interleaved = current[:grows]
        for past, present in zip(previous, current[grows:]):
            interleaved.extend((past, present))
        check(all(negative_less(a[1], b[0]) for a, b in zip(interleaved, interleaved[1:])),
              f"overlapping adjacent-row brackets at n={n}")
        roots += degree
        previous = current
    if last == LAST:
        check(all(not line.strip() for line in lines), "trailing certificate rows")
    print(f"PASS: n={FIRST}..{last}, {last - FIRST + 1} adjacent pairs, "
          f"{roots} gamma roots, {2 * roots} integer endpoint signs, "
          f"original t-row recurrence and gamma extraction, permutations through n={min(last, 8)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, default=Path("certificate.txt.gz"))
    parser.add_argument("--last", type=int, choices=range(FIRST, LAST + 1), metavar="N", default=LAST)
    args = parser.parse_args()
    opener = gzip.open if args.certificate.suffix == ".gz" else open
    with opener(args.certificate, "rt", encoding="ascii") as stream:
        verify(args.last, stream)


if __name__ == "__main__":
    main()
