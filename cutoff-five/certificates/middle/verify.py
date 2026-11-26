#!/usr/bin/env python3
"""Reproduce the cutoff-five middle-region scalar bounds in exact rationals."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json

SCALE = 10_000_000
PI_LO = Q(314159, 100000)
PI_HI = Q(314160, 100000)


def round_up(value):
    return Q(-((-value.numerator * SCALE) // value.denominator), SCALE)


def taylor(value, order):
    term = total = Q(1)
    for i in range(1, order + 1):
        term *= value / i
        total += term
    return total, term


def verify_arithmetic():
    a, n = 11, 49
    square = 1 + (PI_HI / a)**2
    lower = Q(isqrt(square.numerator * SCALE**2 // square.denominator), SCALE)
    alpha = lower + Q(lower**2 < square, SCALE)
    assert 0 < alpha and square <= alpha**2
    endpoint_lower, _ = taylor(Q(a), 64)
    r0 = round_up(1 / endpoint_lower)
    assert 1 <= r0 * endpoint_lower
    quartic_cap = 1 / Q(a**3) + 1 / Q(2*a**2) + 1 / Q(6*a) + Q(1, 24)
    v_raw = quartic_cap * alpha**4 * a**4 * r0
    v0 = round_up(v_raw)
    head_raw = quartic_cap*r0*(2*alpha**5*a**5 + 2*alpha**7*a**7/((n-3)*PI_LO**2)) / (PI_LO*(1-v0))
    head = round_up(head_raw)
    tail49, tail50 = (Q(14*j, 2**((j-5)//2)) for j in (n, n+1))
    tail = round_up(max(tail49, tail50))
    j_raw = quartic_cap*r0*alpha**6*a**6/PI_LO
    drift = round_up(j_raw)
    assert 0 < v0 < Q(8877, 500000)
    assert head < Q(17, 100) and head + tail < Q(1, 4)
    assert 0 < drift < 1 and 4*drift/n < Q(1, 2)
    assert 18*alpha**3/PI_LO < 7
    assert 2 + Q(n, n-4) + Q(1, 4) < 4
    # Compare the Lean range-reduced certificate with a direct, unscaled tail.
    x = 16*v0
    direct, last_term = taylor(x, 64)
    direct_upper = direct + (last_term*x/65) / (1-x/66)
    x_half = x / 2
    assert 0 <= x_half <= Q(1, 4)
    reduced, reduced_last = taylor(x_half, 12)
    reduced_upper = round_up(reduced + (reduced_last*x_half/13)/(1-x_half/14))
    exp_upper = round_up(reduced_upper**2)
    assert direct_upper <= exp_upper < 2
    return {
        "alpha": alpha, "r0": r0, "C": quartic_cap, "vFormula": v_raw, "v0": v0,
        "expUpper16v0": exp_upper, "headFormula": head_raw, "head": head,
        "tailAt49": tail49, "tailAt50": tail50, "tail": tail, "JFormula": j_raw, "J": drift,
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the canonical constants")
    args = parser.parse_args()
    path = Path(__file__).with_name("constants.json")
    values = {name: str(value) for name, value in verify_arithmetic().items()}
    text = json.dumps(values, indent=2) + "\n"
    if args.write:
        path.write_text(text)
    if path.read_text() != text:
        raise SystemExit("Frozen constants differ from the exact recomputation")
    for name in ("alpha", "r0", "C", "v0", "expUpper16v0", "head", "tail", "J"):
        print(f"{name} = {values[name]}")
    print("PASS exact middle-region endpoint constants and reserves.")


if __name__ == "__main__":
    main()
