"""Exhaustive rational interval cover of the real return on [0, 9/50]."""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from fractions import Fraction as Q
from functools import lru_cache
from rational import (certified_pi, plus, point, scale, times, trig_at, upper_abs,
                      outward, interval_strings, require)

PI = certified_pi()


def step(box, impulse):
    center,radius = (box[0]+box[1])/2,(box[1]-box[0])/2
    factor = center/2+Q(1,4)
    cosine,sine = outward(trig_at(center,PI,False)),outward(trig_at(center,PI,True))
    image = plus(point(center+Q(1,4)+impulse),scale(cosine,-factor))
    derivative = plus(plus(point(1),scale(cosine,Q(-1,2))),scale(times(PI,sine),factor))
    variation = (4+16*(abs(factor)+radius/2))*radius
    derivative = outward(plus(derivative,(-variation,variation)))
    return outward(plus(image,times(derivative,(-radius,radius)))),derivative


@lru_cache(maxsize=None)
def lap(box):
    derivative = point(1)
    for impulse in (1,0,-1):
        box,local = step(box,impulse)
        derivative = outward(times(derivative,local))
    return box,derivative


def displacement(x):
    image,_ = lap(point(x))
    return plus(image,point(-x))


def check_interval(left,right,mode,depth=0):
    center,radius = (left+right)/2,(right-left)/2
    _,derivative = lap((left,right))
    dg = plus(derivative,point(-1))
    g = plus(displacement(center),times(dg,(-radius,radius)))
    margins = {'g<0':-g[1],'g>0':g[0],'dg<0':-dg[1],'dg>0':dg[0]}
    if derivative[0] > 0 and margins[mode] > 0:
        return [{'interval':interval_strings((left,right)),'condition':mode,
                 'derivative':interval_strings(derivative),'positive_margin':str(margins[mode])}]
    require(depth < 20, 'interval certificate exhausted bisection budget')
    return (check_interval(left,center,mode,depth+1)
            +check_interval(center,right,mode,depth+1))


def certify():
    zones = (('0','.06','dg<0'),('.06','.15','g<0'),('.15','.17','dg>0'),
             ('.17','.173','g>0'),('.173','.18','dg<0'))
    covers = []
    for a,b,mode in zones:
        leaves = check_interval(Q(a),Q(b),mode)
        require(Q(leaves[0]['interval'][0]) == Q(a) and Q(leaves[-1]['interval'][1]) == Q(b),
                'cover endpoints')
        require(all(leaves[i]['interval'][1] == leaves[i+1]['interval'][0] for i in range(len(leaves)-1)),
                'gap in interval cover')
        covers.append({'interval':[str(Q(a)),str(Q(b))],'condition':mode,'leaves':leaves})
    brackets = [(Q('.16503724'),Q('.16503725')),(Q('.17752760'),Q('.17752761'))]
    roots = []
    for name,(a,b),direction in zip(('repeller','attractor'),brackets,(1,-1)):
        ga,gb = displacement(a),displacement(b)
        require(scale(ga,direction)[1] < 0 < scale(gb,direction)[0], 'root bracket signs')
        roots.append({'kind':name,'bracket':interval_strings((a,b)),
                      'left_displacement':interval_strings(ga),'right_displacement':interval_strings(gb),
                      'derivative_interval':interval_strings(lap((a,b))[1])})
    repelling = lap(brackets[0])[1]
    require(Q('1.096') < repelling[0] and repelling[1] < Q('1.097'), 'repeller multiplier')
    from attracting_disks import SLOW_CENTERS
    require(upper_abs(plus(brackets[1],point(-Q(SLOW_CENTERS[0])))) < Q(1,10**6),
            'attracting root outside independent capture disk')
    end = displacement(Q('.18'))
    require(end[1] < 0, 'right endpoint not mapped inward')
    return {'domain':['0','9/50'],'zones':covers,'leaf_counts':[len(c['leaves']) for c in covers],
            'nonzero_fixed_returns':roots,'right_endpoint_displacement':interval_strings(end),
            'zero_fixed_return':'verified by the exact integer three-cycle'}


if __name__ == '__main__':
    import json
    print(json.dumps(certify(),indent=2))
