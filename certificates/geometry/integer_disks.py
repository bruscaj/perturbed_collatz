"""Rational complex capture disks around three exactly replayed integer cycles."""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from fractions import Fraction as Q
from math import prod
from discrete import CYCLES, cycle
from rational import certified_pi, require


def certify():
    outer, radius = Q(1,4096), Q(1,10**6)
    pi = certified_pi()[1]
    # |1-cos u| <= |u|^2 exp(|u|)/2 and exp(t) <= 1/(1-t).
    remainder_coefficient = (Q(25,4)+outer/2)*pi**2/(2*(1-pi*outer))
    require(pi*outer < 1 and remainder_coefficient < 64, 'integer remainder bound')
    rows = []
    for seed,length,name in CYCLES:
        data = cycle(seed,length,name)
        centers = [n for n,_ in data['states']]
        require(max(map(abs,centers)) <= 12, 'center outside uniform bound')
        factors = [Q(3 if n % 2 else 1,2)+64*outer for n in centers]
        odds = sum(n % 2 for n in centers)
        require(2**odds*radius < outer, 'partial traversal leaves certified disk')
        require(prod(factors) < 1, 'full cycle is not contractive')
        rows.append({'cycle_id':name,'states':data['states'],'physical_period':length,
                     'capture_radius':str(radius),'outer_radius':str(outer),
                     'multiplier':str(Q(3**odds,2**length)),
                     'step_error_factors':[str(x) for x in factors],
                     'full_cycle_error_factor':str(prod(factors)),
                     'partial_error_bound':str(2**odds*radius)})
    return {'nonlinear_remainder_coefficient_upper':str(remainder_coefficient),
            'used_remainder_coefficient':64,'cycles':rows}


if __name__ == '__main__':
    import json
    print(json.dumps(certify(),indent=2))
