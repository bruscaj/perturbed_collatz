"""Exact rational enclosures shared by the geometry certificates.

No floating-point value is used to certify an inequality. The analytic
Taylor and disk bounds are proved in the accompanying manuscript.
"""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from fractions import Fraction as Q
from math import factorial


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def point(x):
    return (Q(x), Q(x))


def plus(a, b):
    return (a[0] + b[0], a[1] + b[1])


def times(a, b):
    ends = [x*y for x in a for y in b]
    return (min(ends), max(ends))


def scale(a, factor):
    return times(a, point(factor))


def upper_abs(a):
    return max(abs(a[0]), abs(a[1]))


def round_up(x, denominator):
    return Q(-(-x.numerator*denominator//x.denominator), denominator)


def round_down(x, denominator):
    return -round_up(-x, denominator)


def outward(a, denominator=10**15):
    return (round_down(a[0], denominator), round_up(a[1], denominator))


def interval_strings(a):
    return [str(a[0]), str(a[1])]


def atan_unit_fraction(q):
    x = Q(1, q)
    s = sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(24))
    return (s, s + x**49/49)


def certified_pi():
    # tan(4 atan(1/5) - atan(1/239)) = 1; the angles give pi/4.
    require((Q(120,119)-Q(1,239))/(1+Q(120,119)*Q(1,239)) == 1,
            'Machin rational identity')
    bounds = plus(scale(atan_unit_fraction(5), 16),
                  scale(atan_unit_fraction(239), -4))
    pi = (Q('3.14159265358979323846'), Q('3.14159265358979323847'))
    require(pi[0] < bounds[0] < bounds[1] < pi[1], 'pi enclosure')
    return pi


def trig_at(c, pi, sine):
    integer = round(c)
    offset = c-integer
    low, high = scale(pi, abs(offset))
    require(0 <= low <= high < 2, 'reduced real angle outside Taylor range')
    total = point(0)
    for j in range(8):
        degree = 2*j + int(sine)
        term = (low**degree/factorial(degree), high**degree/factorial(degree))
        total = plus(total, scale(term, (-1)**j))
    remainder = high**(degree+1)/factorial(degree+1)
    sign = -1 if integer % 2 else 1
    if sine and offset < 0:
        sign = -sign
    return scale(plus(total, (-remainder, remainder)), sign)


if __name__ == '__main__':
    import json
    print(json.dumps({'pi': interval_strings(certified_pi())}, indent=2))
