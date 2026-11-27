"""Outward rational two-pole budgets for the seventh cutoff on 0 <= x <= 16."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import runpy


def main():
    base = runpy.run_path(str(Path(__file__).resolve().parents[1] / 'fixed-five-effective/check.py'))
    lower_pi, upper_pi = base['P'], base['Q']
    up, exp_neg, exp_up = base['up'], base['exp_neg'], base['exp_up']
    size = 96
    cells = []
    for i in range(128):
        left, right = F(i, 8), F(i+1, 8)
        rlo, rhi = exp_neg(right)[0], exp_neg(left)[1]
        hlo, hhi = rlo/(1+rlo)**2, rhi/(1+rhi)**2
        vmax = (1-rlo)/(1+rlo)
        moments = [rhi/(1+rhi), hhi, hhi*vmax, hhi*max(abs(1-6*hlo), abs(1-6*hhi)),
                   hhi*vmax*max(abs(1-12*hlo), abs(1-12*hhi)), hhi,
                   min(F(11, 6)*hhi, F(21, 20)*rhi)]
        rho = base['sqrt_up'](right**2 + upper_pi**2)
        tilts = [moments[m-1]/factorial(m) for m in range(1, 7)]
        loss = up(sum(t*rho**m for m, t in enumerate(tilts, 1)))
        drift = up(sum(moments[m]*rho**(m+2)/factorial(m) for m in range(1, 7))/lower_pi)
        candidates = []
        for index in range(21, 61):
            lam = F(index, 20)
            if lam**2*(right**2 + lower_pi**2) > right**2 + 9*lower_pi**2:
                continue
            shell = up(sum(t*(rho*lam)**m for m, t in enumerate(tilts, 1)))
            error = up(max(rho, lam*rho**2/(2*lower_pi**2))*rho*exp_up(shell+loss)
                       / (lower_pi*lam**(size-7)))
            candidates.append((error, lam))
        error, lam = min(candidates)
        budget = up((3*error+(2+error)*drift/size)/2)
        cells.append((i, lam, error, drift, budget))
    maximal = {key: max((cell[col], cell[0]) for cell in cells)
               for key, col in [('error', 2), ('drift', 3), ('phase budget', 4)]}
    for key, (value, index) in maximal.items():
        print(f'{key}: {value} on [{index}/8,{index+1}/8]')
    assert maximal['phase budget'][0] < 1
    print(f'PASS {len(cells)} closed cells, all upper ranks n >= {size}')
    return cells


if __name__ == '__main__':
    main()
