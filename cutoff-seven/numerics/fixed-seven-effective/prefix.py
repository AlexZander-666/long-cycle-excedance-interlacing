"""Build and independently check negative dyadic brackets for old sizes 7 through 94."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / 'fixed-five-effective'))
import finite
import generate_prefix_lean as candidates


def sign_at(coeffs, dyadic):
    num, den = dyadic
    assert den > 0 and den.bit_count() == 1
    # Homogeneous Horner evaluation with positive denominator.
    value = coeffs[-1]
    scale = 1
    for term in reversed(coeffs[:-1]):
        scale *= den
        value = value * num + term * scale
    return (value > 0) - (value < 0)


def main():
    last = 95
    candidates.LAST = last
    rows = finite.rows(last, 7)
    for n in range(7, 10):
        assert finite.brute(n, 7) == rows[n]
    path = ROOT / 'dyadic-prefix.json'
    if not path.exists():
        data = {}
        for n in range(8, last + 1):
            outer, windows = candidates.points(rows[n-1][1:], rows[n][1:])
            data[n] = [outer.as_integer_ratio(),
                       [[a.as_integer_ratio(), b.as_integer_ratio()] for a, b in windows]]
        tmp = path.with_suffix('.tmp')
        tmp.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        tmp.replace(path)
    data = json.loads(path.read_bytes())
    assert sorted(map(int, data)) == list(range(8, last+1))
    count = 0
    for n in range(8, last+1):
        outer, windows = data[str(n)]
        p, q = rows[n-1][1:], rows[n][1:]
        d = len(p)-1
        assert rows[n-1][0] == rows[n][0] == 0
        assert len(windows) == d == n-3 and len(q) == d+2
        assert all(c > 0 for c in p+q)
        left = Fraction(*outer)
        assert sign_at(q, outer) == (-1)**(d+1)
        for j, (a, b) in enumerate(windows):
            assert left < Fraction(*a) < Fraction(*b) < 0
            left = Fraction(*b)
            s = (-1)**(d-j)
            assert sign_at(p, a) == sign_at(q, a) == sign_at(q, b) == s
            assert sign_at(p, b) == -s
        count += d
    print(f'PASS {len(data)} hard-cutoff-seven adjacent pairs at upper size 8..95; '
          f'{count} strictly ordered lower-root intervals; two row recurrences, '
          'literal permutation enumeration at sizes 7, 8, 9.')
    print(sha256(path.read_bytes()).hexdigest(), path.name)


if __name__ == '__main__':
    main()
