#!/usr/bin/env python3
"""Independent physical and arithmetic audit of balanced B1 repayment rules."""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import time

from balanced_repayment import BalancedRepayment, INPUT_SHA256, require, v2


HERE = Path(__file__).resolve().parent
IMPULSES = (0, 0, 1, -1, 0, 1, -1)
HEIGHT = (0, 0, 0, 1, 0, 0, 1)
PREVIOUS_SELECTOR_SHA256 = '1c10f36181385b423eb749b1a56b5e3a8cde0b669908e1bd30e88a39166b66df'


def load_previous_selector():
    """Load the exact pre-extension selector, not whichever version is current."""
    path = HERE / 'selector_inputs/b1_selector_before_extensions.py'
    require(hashlib.sha256(path.read_bytes()).hexdigest() == PREVIOUS_SELECTOR_SHA256,
            'pre-extension selector snapshot differs')
    spec = importlib.util.spec_from_file_location('b1_selector_before_extensions', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.B1Selector(inputs=HERE / 'selector_inputs')


def affine_run(coefficient, constant, phase, steps):
    for _ in range(steps):
        require(coefficient > 0 and coefficient % 2 == 0 and constant >= HEIGHT[phase],
                'physical affine branch is nonuniform or unsafe')
        if constant % 2:
            coefficient, constant = 3 * coefficient // 2, (3 * constant + 1) // 2
        else:
            coefficient, constant = coefficient // 2, constant // 2
        constant += IMPULSES[phase]
        phase = (phase + 1) % 7
    require(constant >= HEIGHT[phase], 'unsafe affine endpoint')
    return coefficient, constant, phase


def replay(source, target, steps):
    value, phase = 6 * source - 1, 1
    for _ in range(steps):
        value = (value // 2 if value % 2 == 0 else (3 * value + 1) // 2) + IMPULSES[phase]
        phase = (phase + 1) % 7
        require(value >= HEIGHT[phase], 'physical point leaves safe domain')
    require((value, phase) == (6 * target - 1, 1), 'physical point replay failed')


def audit_ray(ray):
    coefficient, constant, phase = 6 * ray['M'], 6 * ray['r'] - 1, 1
    for label in ray['path']:
        require(coefficient % 768 == 0 and (constant + 1) % 6 == 0 and phase == 1,
                'whole-ray section coordinates failed')
        require(((constant + 1) // 6 - 1) % 128 + 1 == label,
                'whole-ray primitive label failed')
        coefficient, constant, phase = affine_run(coefficient, constant, phase, 7)
    require((coefficient, constant, phase) == (6 * ray['A'], 6 * ray['B'] - 1, 1),
            'whole-ray physical affine endpoint failed')
    require(0 < ray['A'] < ray['M'] and 0 < ray['B'] < ray['r'] <= ray['M'],
            'whole-ray original-rank decrease failed')


def literal_homogeneous(model, source):
    """Independent guarded-step reference; a derived finite cap prevents looping."""
    residue = (source - 1) % 128 + 1
    primitive = model.growing.get(residue)
    if primitive is None:
        return None
    # Each legal growing step removes seven powers of two from this quantity.
    cap = ((primitive.slope - 128) * source + primitive.numerator_constant).bit_length() // 7 + 1
    value, depth = source, 0
    while primitive.applies(value):
        value = primitive.apply(value)
        depth += 1
        require(depth <= cap, 'literal growing loop exceeded a proved finite cap')
    for _ in range(depth):
        if not model.j.applies(value):
            return None
        value = model.j.apply(value)
    require(depth >= 1 and 0 < value < source, 'literal balanced rank theorem failed')
    return value, depth


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=HERE / 'balanced_repayment_verification.json')
    args = parser.parse_args()
    start = time.time()
    model = BalancedRepayment()

    primitive_records = []
    for primitive in [*model.growing.values(), model.j]:
        actual = affine_run(768, 6 * primitive.residue - 1, 1, 7)
        expected = (6 * primitive.slope, 6 * primitive.image_at_residue - 1, 1)
        require(actual == expected, 'primitive whole-physical identity failed')
        row = {'residue': primitive.residue, 'slope_numerator': primitive.slope,
               'constant_numerator': primitive.numerator_constant,
               'image_at_residue': primitive.image_at_residue}
        if primitive.residue != 123:
            a, b = primitive.slope, primitive.numerator_constant
            require(0 <= b <= a - 128 and a <= 2187, 'shifted growing bound failed')
            delta = v2(abs(123 - primitive.residue))
            require(0 <= delta < 7, 'terminal valuation not below seven')
            # At s=123 modulo128, the exact valuation is delta. An odd
            # (a-128) multiplier preserves it, since no modulus wrap can
            # affect a valuation below7.
            terminal_shift = (a - 128) * 123 + b
            require(v2(terminal_shift) == delta, 'switch-valuation identity failed')
            row['delta'] = delta
            row['shifted_growth_bound_verified'] = True
        primitive_records.append(row)

    g, h, fixed_point = Fraction(2187, 128), Fraction(3, 128), Fraction(3, 25)
    beta = g * h
    margin = 1 - 2 * beta - fixed_point
    require(beta == Fraction(6561, 16384) < 1, 'uniform multiplier budget failed')
    require(margin == Fraction(16199, 204800) > 0, 'all-positive-source rank floor failed')
    require(Fraction(15, 128) == fixed_point * (1 - h), 'J fixed point failed')
    mixed_density = Fraction(21, 16384) / (1 - Fraction(21, 16384))
    homogeneous_density = 21 * Fraction(1, 16384) / (1 - Fraction(1, 16384))
    require(mixed_density == Fraction(21, 16363), 'mixed density sum failed')
    require(homogeneous_density == Fraction(21, 16383), 'homogeneous density sum failed')

    finite_levels = []
    earlier_levels = []
    mixed_examples = []
    for depth in (1, 2, 3):
        residues = set()
        count = 0
        for word in product(model.growing, repeat=depth):
            ray = model.mixed_ray(word)
            audit_ray(ray)
            require(ray['r'] not in residues, 'two words define the same source cylinder')
            residues.add(ray['r'])
            for modulus, previous in earlier_levels:
                require((ray['r'] - 1) % modulus + 1 not in previous,
                        'different first-switch depths overlap')
            witness = model.consume_mixed(ray['r'], list(word))
            require(witness is not None and witness['target_t'] == ray['B'],
                    'mixed finite-word consumer disagrees with whole ray')
            if depth == 3 and len(set(word)) == 3 and len(mixed_examples) < 3:
                mixed_examples.append(witness)
            count += 1
        require(count == len(residues) == 21 ** depth, 'mixed level count failed')
        finite_levels.append({'growing_depth': depth, 'whole_rays_verified': count,
                              'source_modulus': 128 ** (2 * depth),
                              'pairwise_and_cross_level_disjoint': True})
        earlier_levels.append((128 ** (2 * depth), residues))

    counts = Counter()
    first_examples = {}
    for source in range(1, 100001):
        witness = model.select_homogeneous(source)
        literal = literal_homogeneous(model, source)
        require((witness is None) == (literal is None), 'closed decoder/reference acceptance differs')
        if witness is not None:
            require((witness['target_t'], witness['growing_periods']) == literal,
                    'closed decoder/reference witness differs')
            replay(source, witness['target_t'], witness['source_steps'])
            counts[witness['growing_residue']] += 1
            first_examples.setdefault(witness['growing_residue'], witness)

    high_depth = []
    whole_homogeneous = 0
    new_examples = []
    previous_selector = load_previous_selector()
    for depth in (1, 2, 3, 4, 7, 14, 32, 100, 1000):
        for residue in model.growing:
            ray = model.homogeneous_ray(residue, depth)
            audit_ray(ray)
            for v in (0, 1, 243):
                source = ray['M'] * v + ray['r']
                witness = model.select_homogeneous(source)
                require(witness is not None, 'homogeneous source ray rejected')
                require(witness['target_t'] == ray['A'] * v + ray['B'], 'homogeneous endpoint differs')
                require(witness['growing_periods'] == depth and witness['growing_residue'] == residue,
                        'homogeneous unique depth or branch differs')
                literal = literal_homogeneous(model, source)
                require(literal == (witness['target_t'], depth), 'large literal reference differs')
                if depth <= 7 and previous_selector.select(source)['status'] == 'unhandled' and len(new_examples) < 6:
                    new_examples.append(witness)
            replay(ray['r'], ray['B'], 14 * depth)
            whole_homogeneous += 1
        high_depth.append({'depth': depth, 'whole_rays_verified': len(model.growing),
                           'parameters_per_ray': 3})

    source_files = ['balanced_repayment.py', 'verify_balanced_repayment.py',
                    'selector_inputs/period_composition.json',
                    'selector_inputs/b1_selector_before_extensions.py']
    result = {
        'scope': 'General mixed growing-word/J123 balanced repayment theorem; exact finite-word certificate consumer; total exact selector for all21 homogeneous families. No global capture, no whole-unbounded-relation DFA claim.',
        'input_pin_sha256': INPUT_SHA256,
        'primitive_audit': primitive_records,
        'proof_constants': {'max_growing_slope': str(g), 'J_slope': str(h),
                            'J_fixed_point': str(fixed_point), 'beta': str(beta),
                            'rank_margin_at_t1': str(margin)},
        'exact_component_densities': {'mixed_balanced_language': str(mixed_density),
                                      'homogeneous_21_family_union': str(homogeneous_density),
                                      'homogeneous_unreduced_fraction': '21/16383',
                                      'scope': 'These two components only, not their union with another selected library.',
                                      'tail_justification': 'Mixed depth>=K is contained in the21^K growing-prefix cylinders modulo128^K, with density(21/128)^K; homogeneous is a subset.'},
        'mixed_complete_finite_levels': finite_levels,
        'mixed_total_whole_rays_verified': sum(x['whole_rays_verified'] for x in finite_levels),
        'mixed_representative_witnesses': mixed_examples,
        'homogeneous_bounded_diagnostic': {'through_parameter': 100000,
                                          'literal_reference_comparisons': 100000,
                                          'accepted_by_residue': dict(sorted(counts.items())),
                                          'accepted_total': sum(counts.values()),
                                          'all_accepted_physically_replayed': True},
        'homogeneous_large_depth_checks': high_depth,
        'homogeneous_total_whole_rays_verified': whole_homogeneous,
        'first_homogeneous_witness_by_residue': dict(sorted(first_examples.items())),
        'examples_unhandled_by_previous_frozen_combined_selector': new_examples,
        'previous_selector_comparison_scope': 'The frozen selector_inputs/b1_selector_before_extensions.py and its frozen inputs only; not all-current main.',
        'source_hashes': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in source_files},
        'all_passed': True, 'elapsed_seconds': round(time.time() - start, 3),
        'proof_boundary': 'Exact mathematical proof and independent physical checks. The parent formal package supplies GeneralRepaymentBound.lean for the generic envelope inequality; this Python verifier does not run Lean or kernel-formalize the concrete physical adaptation. Mixed consumer requires a supplied finite growing word; only the homogeneous union has a total membership decoder here.',
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'output': str(args.output), 'all_passed': True,
                      'physical_primitives': len(primitive_records),
                      'mixed_whole_rays': result['mixed_total_whole_rays_verified'],
                      'homogeneous_whole_rays': whole_homogeneous,
                      'homogeneous_accepted_through100000': sum(counts.values()),
                      'densities': result['exact_component_densities'],
                      'new_against_previous_frozen_selector_examples': len(new_examples),
                      'elapsed_seconds': result['elapsed_seconds']}))


if __name__ == '__main__':
    main()
