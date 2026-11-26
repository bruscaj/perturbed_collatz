"""Deterministic rational complex-ball replay of one point at all three phases.

Candidate centers are rounded rational Taylor polynomials, not floating-point
trajectories. Every resulting error is bounded independently of that rounding.
"""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from fractions import Fraction as Q
from math import factorial
from rational import certified_pi, round_up, require, interval_strings

WORD = (1,0,-1)
SOURCE = (Q(71,100),Q(1,50))
RADIUS = Q(1,10**6)
PI_INTERVAL = certified_pi()
PI = sum(PI_INTERVAL)/2
PI_ERROR = (PI_INTERVAL[1]-PI_INTERVAL[0])/2
TRIG_ERROR = 2*Q(3**40,factorial(40))+8*PI_ERROR


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def scale(a,s):
    return a[0]*s,a[1]*s


def norm_bound(a):
    return abs(a[0])+abs(a[1])


def trig(center):
    x,y = center
    integer = round(x)
    offset = (x-integer,y)
    w = scale(offset,PI)
    require(norm_bound(offset) <= 1 and norm_bound(w) <= 3 and abs(y) <= Q(1,2),
            'complex Taylor assumptions')
    term = (Q(1),Q(0))
    sine,cosine = (Q(0),Q(0)),term
    for j in range(1,40):
        term = scale(mul(term,w),Q(1,j))
        signed = scale(term,(-1)**(j//2))
        if j % 2:
            sine = add(sine,signed)
        else:
            cosine = add(cosine,signed)
    sign = -1 if integer % 2 else 1
    return scale(sine,sign),scale(cosine,sign)


def advance_ball(center,error,impulse):
    require(abs(center[1])+error < Q(1,2) and norm_bound(center)+error <= 15,
            'second derivative disk assumptions')
    sine,cosine = trig(center)
    factor = add(scale(center,Q(1,2)),(Q(1,4),Q(0)))
    image = add(add(center,(Q(1,4)+impulse,Q(0))),scale(mul(factor,cosine),-1))
    candidate = tuple(Q(round(v*10**18),10**18) for v in image)
    residual = norm_bound(add(image,scale(candidate,-1)))+norm_bound(factor)*TRIG_ERROR
    derivative = add(add((Q(1),Q(0)),scale(cosine,Q(-1,2))),scale(mul(factor,sine),PI))
    derivative_bound = (norm_bound(derivative)+(Q(1,2)+4*norm_bound(factor))*TRIG_ERROR
                        +8*norm_bound(factor)*PI_ERROR)
    new_error = round_up(residual+derivative_bound*error+1000*error**2,10**24)
    return candidate,new_error


def check_trace(phase,expected,centers,cycle_id):
    center,error = SOURCE,Q(0)
    rows,earlier_margins = [],[]
    for k in range(expected+1):
        ph = (phase+k) % 3
        distances = [(center[0]-target)**2+center[1]**2 for target in centers[ph]]
        rows.append({'time':k,'phase':ph,'real':str(center[0]),'imaginary':str(center[1]),
                     'radius':str(error)})
        if k < expected:
            margin = min(distances)-(RADIUS+error)**2
            require(margin > 0, 'earlier target-disk entry not excluded')
            earlier_margins.append(margin)
        else:
            require(error < RADIUS and min(distances) < (RADIUS-error)**2,
                    'last ball not inside target disk')
            target = centers[ph][distances.index(min(distances))]
            return {'launch_phase':phase,'cycle_id':cycle_id,'first_target_disk_entry':expected,
                    'target_phase':ph,'target_center':target,'capture_radius':str(RADIUS),
                    'final_error':str(error),'minimum_earlier_squared_margin':str(min(earlier_margins)),
                    'trajectory_balls':rows}
        center,error = advance_ball(center,error,WORD[ph])
    raise ArithmeticError('missing terminal ball')


def certify():
    exponential = sum(Q(2**j,factorial(j)) for j in range(8))+Q(2**8,factorial(8))/(1-Q(2,9))
    require(exponential < 8, 'exp(2) majorant')
    require(4*8+(Q(15,2)+Q(1,4))*16*8 < 2000, 'uniform second derivative majorant')
    small,large = ((0,),(1,),(2,)),((1,7,2),(3,12,2),(5,6,1))
    for group in (small,large):
        for ph,values in enumerate(group):
            images = {((3*n+1)//2 if n % 2 else n//2)+WORD[ph] for n in values}
            require(images == set(group[(ph+1) % 3]), 'phase-tagged target cycle')
    rows = [check_trace(phase,time,group,name) for phase,(time,group,name) in enumerate(
            ((43,small,'integer_three'),(91,large,'integer_nine'),(38,small,'integer_three')))]
    require(all(Q(row['final_error']) < Q(4,10**18) for row in rows),
            'published final-error upper bound')
    return {'source_real':str(SOURCE[0]),'source_imaginary':str(SOURCE[1]),
            'pi_interval':interval_strings(PI_INTERVAL),'trigonometric_error_bound':str(TRIG_ERROR),
            'candidate_center_grid':10**18,'error_grid':10**24,'launches':rows}


if __name__ == '__main__':
    import json
    print(json.dumps(certify(),indent=2))
