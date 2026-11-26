"""Two noninteger real attracting cycles, certified by rational complex disks."""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from fractions import Fraction as Q
from rational import (certified_pi, plus, point, scale, times, trig_at,
                      upper_abs, round_up, round_down, require, interval_strings)

FAST_CENTERS = ('1.045673204662','3.060567710576','5.058720096962',
                '7.040922064888','12.030267292222','6.043435831841',
                '2.052131519289','2.043141227448','1.033231466989')
SLOW_CENTERS = ('0.177527602643','1.140098603174','2.131993200359')
WORD = (1,0,-1)


def check(name, center_strings, radius_units):
    pi = certified_pi()
    centers = tuple(map(Q,center_strings))
    radii = tuple(Q(x)/10**6 for x in radius_units)
    require(len(centers) == len(radii) and len(centers) % 3 == 0, 'disk clock')
    product, signed = Q(1), point(1)
    rows = []
    for i,(c,radius) in enumerate(zip(centers,radii)):
        j = (i+1) % len(centers)
        sine,cosine = trig_at(c,pi,True),trig_at(c,pi,False)
        factor = c/2+Q(1,4)
        image = plus(point(c+Q(1,4)+WORD[i % 3]),scale(cosine,-factor))
        residual = upper_abs(plus(image,point(-centers[j])))
        derivative = plus(plus(point(1),scale(cosine,Q(-1,2))),scale(times(pi,sine),factor))
        require(pi[1]*radius < 1, 'complex exponential majorant domain')
        second = (pi[1]+(abs(factor)+radius/2)*pi[1]**2)/(1-pi[1]*radius)
        variation = second*radius
        signed = times(signed,plus(derivative,(-variation,variation)))
        bound = round_up(upper_abs(derivative)+variation,10**5)
        error = round_up(residual,10**12)
        slack = radii[j]-(error+bound*radius)
        require(slack > 0, f'{name}: disk {i} does not enter next disk')
        product *= bound
        require(c-radius > 0 and abs(c-round(c)) > radius, 'disk meets nonpositive real axis or an integer')
        for k in range(i+3,len(centers),3):
            require(abs(c-centers[k]) > radius+radii[k], 'same-phase disks overlap')
        rows.append({'step':i,'phase':i % 3,'center_decimal':center_strings[i],
                     'center':str(c),'radius':str(radius),'residual_upper':str(error),
                     'derivative_upper':str(bound),'inclusion_slack':str(slack)})
    require(product < 1, 'cycle product is not below one')
    require(min(radii) >= Q(11,10**7), 'uniform small capture disk not contained')
    return {'cycle_id':name,'physical_period':len(centers),'disks':rows,
            'lipschitz_product':str(product),
            'lipschitz_upper_1e6':str(round_up(product,10**6)),
            'signed_multiplier_interval':interval_strings((round_down(signed[0],10**6),round_up(signed[1],10**6))),
            'uniform_center_capture_radius':str(Q(1,10**6)),
            'minimum_inclusion_slack':str(min(Q(row['inclusion_slack']) for row in rows))}


def certify():
    fast = check('noninteger_nine',FAST_CENTERS,('100','130','60','10','1.1','3','6','8','10'))
    slow = check('noninteger_three',SLOW_CENTERS,('10','11.8','4.4'))
    require(Q(fast['lipschitz_upper_1e6']) < Q('.012'), 'fast product')
    require(Q(slow['lipschitz_upper_1e6']) < Q('.894'), 'slow product')
    # Distinctness at phase zero follows from disjoint trapping intervals.
    require(abs(Q(FAST_CENTERS[0])-Q(SLOW_CENTERS[0])) > Q('.001'), 'two traps overlap')
    return {'cycles':[fast,slow]}


if __name__ == '__main__':
    import json
    print(json.dumps(certify(),indent=2))
