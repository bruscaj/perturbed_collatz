"""Exact signed cycles, complete affine return table, and zoom examples."""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

from rational import require

WORD = (1, 0, -1)
CYCLES = ((0, 3, 'integer_three'), (1, 9, 'integer_nine'),
          (-1, 3, 'negative_integer_three'))


def step(n, phase):
    return (n//2 if n % 2 == 0 else (3*n+1)//2) + WORD[phase], (phase+1) % 3


def lap(n):
    phase = 0
    for _ in range(3):
        n, phase = step(n, phase)
    return n


def cycle(seed, length, name):
    n, phase = seed, 0
    states = []
    for _ in range(length):
        require([n, phase] not in states, 'cycle shortened before claimed period')
        states.append([n, phase])
        n, phase = step(n, phase)
    require((n, phase) == (seed, 0), 'cycle does not close')
    return {'id': name, 'physical_period': length, 'states': states,
            'phase_zero_values': [n for n, phase in states if phase == 0],
            'odd_inputs': sum(n % 2 for n, _ in states),
            'safe_nonnegative_cycle': all(n >= (phase != 0) for n, phase in states)}


def return_table():
    rows = []
    expected = [(1,0),(3,7),(1,1),(2,4),(2,7),(2,6),(0,0),(1,2)]
    for residue in range(8):
        coefficient, constant, odd = 8, residue, 0
        parities = []
        for impulse in WORD:
            require(coefficient % 2 == 0, 'free parameter does not fix parity')
            parity = constant % 2
            parities.append(parity)
            odd += parity
            coefficient = (3 if parity else 1)*coefficient//2
            constant = ((3*constant+1)//2 if parity else constant//2) + impulse
        require((odd,constant) == expected[residue], 'incorrect complete return row')
        require(coefficient == 3**odd, 'incorrect affine multiplier')
        rows.append({'residue_mod_8': residue, 'input_parities': parities,
                     'slope_in_quotient': coefficient, 'offset': constant})
    return rows


def return_trace(seed, cap=1000):
    values = []
    n = seed
    while n not in values:
        require(len(values) < cap, 'example did not close within its budget')
        values.append(n)
        n = lap(n)
    start = values.index(n)
    return {'seed': seed, 'phase': 0, 'values': values + [n],
            'cycle_start_index': start, 'return_cycle': values[start:]}


def certify():
    cycles = [cycle(*x) for x in CYCLES]
    require(set(map(tuple,cycles[0]['states'])).isdisjoint(map(tuple,cycles[1]['states'])),
            'the two nonnegative cycles are not disjoint')
    zoom = []
    for root in (0,1):
        seed = root
        for _ in range(3):
            seed = 8*seed+6
        n, phase = seed, 0
        states = [[n,phase]]
        for _ in range(9):
            require(n % 2 == 0, 'zoom example does not have all-even prefix')
            n,phase = step(n,phase)
            states.append([n,phase])
        require((n,phase) == (root,0), 'zoom example misses its root')
        zoom.append({'root':root,'depth':3,'seed':seed,'states':states})
    require(zoom[1]['seed']-zoom[0]['seed'] == 2**9, 'zoom residue mismatch')
    examples = [return_trace(n) for n in (9,25,42,84)]
    require(examples[0]['return_cycle'] == [0], 'seed 9 destination')
    require(set(examples[1]['return_cycle']) == {1,7,2}, 'seed 25 destination')
    require(set(examples[2]['return_cycle']) != set(examples[3]['return_cycle']),
            'modulo-42 examples fail to distinguish basins')
    return {'forcing':list(WORD), 'cycles':cycles, 'return_branches':return_table(),
            'binary_zoom_examples':zoom, 'examples':examples}


if __name__ == '__main__':
    import json
    print(json.dumps(certify(), indent=2))
