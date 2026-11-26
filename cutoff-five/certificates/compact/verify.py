#!/usr/bin/env python3
"""Check the frozen TSV using exact fractions and unscaled exponential series."""
import csv
from fractions import Fraction as F
from pathlib import Path

PI_MIN, PI_MAX = F(314159, 100000), F(314160, 100000)
ROUND_DENOM = 10_000_000


def rounded(x):
    return F(-((-x.numerator * ROUND_DENOM) // x.denominator), ROUND_DENOM)


def taylor_bounds(x):
    """Bound exp(x) directly using 161 terms, without scaling or squaring."""
    if not 0 <= x < 162:
        raise ValueError(f"Taylor bound out of range: {x}")
    term = total = F(1)
    for degree in range(1, 161):
        term = term * x / degree
        total += term
    return total, total + (term * x / 161) / (1 - x / 162)


def verify_cell(i, row):
    a, b = row["a"], row["b"]
    low, high = row["rLo"], row["rHi"]
    rho, lam = row["rho"], row["lambda"]
    assert row["index"] == i and (a, b) == (F(i, 8), F(i + 1, 8))
    assert 0 < low <= high <= 1
    assert low * taylor_bounds(b)[1] <= 1
    assert high * taylor_bounds(a)[0] >= 1
    assert rho > 0 and rho**2 >= b*b + PI_MAX**2
    assert F(21, 20) <= lam <= 3 and (20*lam).denominator == 1
    assert lam**2 * (b*b + PI_MIN**2) <= b*b + 9*PI_MIN**2
    for field, value in (
        ("rightHalves", b), ("costHalves", row["cost"]), ("lossHalves", row["loss"])
    ):
        h = row[field]
        assert h == int(h) and h >= 0
        assert 0 <= value / (2**int(h)) <= F(1, 4)
        assert not h or value / (2**(int(h) - 1)) > F(1, 4)

    hlo, hhi = [r / (1+r)**2 for r in (low, high)]
    vmax = (1-low) / (1+low)
    moments = (
        rounded(hhi), rounded(hhi*vmax),
        rounded(hhi * max(abs(1 - 6*h) for h in (hlo, hhi))),
        rounded(hhi * vmax * max(abs(1 - 12*h) for h in (hlo, hhi))),
    )
    m2, m3, m4, m5 = moments
    coeffs = (rounded(high/(1+high)), rounded(m2/2), rounded(m3/6), rounded(m4/24))
    b1, b2, b3, b4 = coeffs
    re4 = (
        a**4 - 6 * PI_MAX**2 * b*b + PI_MIN**4,
        b**4 - 6 * PI_MIN**2 * a*a + PI_MAX**4,
    )
    if 6*hlo >= 1:
        b4_interval = (-b4, F(0))
    elif 6*hhi <= 1:
        b4_interval = (F(0), b4)
    else:
        b4_interval = (-b4, b4)
    loss = b2 * max(0, PI_MAX**2 - a*a) + b3 * max(0, 3 * PI_MAX**2 * b - a**3)
    loss -= min(c * r for c in b4_interval for r in re4)
    cost = sum(coefficient * (rho*lam)**degree for degree, coefficient in enumerate(coeffs, 1))
    assert 0 <= loss <= row["loss"] and taylor_bounds(row["loss"])[1] <= row["invD"]
    assert 0 <= cost <= row["cost"] and taylor_bounds(row["cost"])[1] <= row["expCost"]
    drift = sum(moment*rho**degree/d
                for degree, moment, d in zip(range(3, 7), moments, (1, 2, 6, 24))) / PI_MIN
    assert 0 <= drift <= row["drift"]
    factor = max(rho, lam*rho*rho / (2*PI_MIN**2)) * rounded(rho / PI_MIN) / lam**44
    error = factor * row["invD"] * row["expCost"]
    assert 0 <= error <= row["error44"]
    phase = (3*row["error44"] + (2 + row["error44"]) * row["drift"] / 49) / 2
    assert 0 <= phase <= row["phase49"]


def main():
    with Path(__file__).with_name("cells.tsv").open(newline="") as records:
        rows = [{key: F(value) for key, value in row.items()}
                for row in csv.DictReader(records, delimiter="\t")]
    assert len(rows) == 88
    for i, row in enumerate(rows):
        verify_cell(i, row)
    for key, published, site, strict in (
        ("error44", F(949, 400000), 87, F(3, 1000)),
        ("drift", F(95990813, 10000000), 30, F(48, 5)),
        ("phase49", F(391801, 2000000), 30, F(1, 5)),
    ):
        maximum = max(row[key] for row in rows)
        assert maximum == published < strict
        assert rows[site][key] == maximum
        print(f"{key} maximum = {maximum} < {strict} (cell {site})")
    print("PASS 88 closed cells covering [0,11], with all rational budgets rechecked.")


if __name__ == "__main__":
    main()
