"""Exact balanced repayment certificates for the frozen B1 primitive bank.

The mixed rule checks a supplied finite word of growing primitives followed by
the same number of J123 steps. The homogeneous selector decides the union of
all 21 languages f_i^k J123^k, k >= 1, using an exact valuation-derived depth.
It does not decide unrestricted membership in the mixed-word language.
"""
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import hashlib
import json


DEFAULT_INPUT = Path(__file__).with_name('selector_inputs') / 'period_composition.json'
INPUT_SHA256 = '1d17744f41f576505ee7e46c321457d3f98a49da566c6eb9b6c47ad3c4cdcdce'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def v2(value):
    require(type(value) is int and value > 0, 'valuation requires a positive integer')
    return (value & -value).bit_length() - 1


@dataclass(frozen=True)
class Primitive:
    """f(128*v + residue) = slope*v + image_at_residue, for v >= 0."""
    residue: int
    slope: int
    image_at_residue: int

    @property
    def numerator_constant(self):
        return 128 * self.image_at_residue - self.slope * self.residue

    def applies(self, value):
        return value >= self.residue and (value - self.residue) % 128 == 0

    def apply(self, value):
        require(self.applies(value), 'primitive guard failed')
        return self.slope * ((value - self.residue) // 128) + self.image_at_residue


class BalancedRepayment:
    def __init__(self, source=DEFAULT_INPUT):
        raw = Path(source).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == INPUT_SHA256, 'primitive input pin differs')
        data = json.loads(raw)
        self.bank = {p['r']: Primitive(p['r'], p['a'], p['b'])
                     for p in data['primitive_bank']}
        self.growing = {r: p for r, p in self.bank.items() if p.slope > 128}
        require(len(self.growing) == 21, 'growing bank has changed')
        self.j = self.bank[123]
        require(self.j == Primitive(123, 3, 3), 'J123 primitive has changed')
        for p in self.growing.values():
            require(128 < p.slope <= 2187 and p.slope % 2 == 1,
                    'uniform growing slope bound failed')
            require(0 <= p.numerator_constant <= p.slope - 128,
                    'uniform shifted growth bound failed')
            require(p.image_at_residue > p.residue, 'primitive is not strictly growing')

    def _word(self, word):
        require(isinstance(word, (list, tuple)) and len(word) >= 1,
                'supply a nonempty finite list or tuple of growing residues')
        require(all(type(r) is int and r in self.growing for r in word),
                'word contains a nongrowing primitive')
        return tuple(word)

    @staticmethod
    def _repay(value, periods):
        """J123^periods(value), exactly when every intervening guard holds."""
        require(value >= 1 and periods >= 1, 'positive state and depth required')
        shifted = 25 * value - 3
        if v2(shifted) < 7 * periods:
            return None
        numerator = pow(3, periods) * (shifted >> (7 * periods)) + 3
        require(numerator % 25 == 0, 'J123 conjugacy integrality failed')
        target = numerator // 25
        require(target >= 1, 'J123 endpoint is not positive')
        return target

    @staticmethod
    def _witness(source, target, periods, rule, **metadata):
        require(0 < target < source, 'balanced repayment did not lower original rank')
        return {
            'status': 'reduction', 'source_t': source, 'target_t': target,
            'proof_rule': rule, 'source_steps': 14 * periods, 'target_steps': 0,
            'meeting_phase': 1, 'original_source_W': 8 * source,
            'alternate_W': 8 * target, 'original_W_drop': 8 * (source - target),
            'growing_periods': periods, 'contracting_periods': periods,
            'repayment_residue': 123, **metadata,
        }

    def consume_mixed(self, source, word):
        """Check a supplied word f_i1...f_ik J123^k; return witness or None.

        This finite-certificate consumer is total for the supplied finite word.
        It does not search over arbitrary mixed words or assert that following
        the growing alphabet forever terminates on every positive input.
        """
        require(type(source) is int and source >= 1, 'positive integer B1 source required')
        word = self._word(word)
        value = source
        for residue in word:
            primitive = self.growing[residue]
            if not primitive.applies(value):
                return None
            value = primitive.apply(value)
        target = self._repay(value, len(word))
        if target is None:
            return None
        return self._witness(source, target, len(word), 'mixed_growth_J123_balanced_repayment',
                             growing_word=list(word), switch_t=value,
                             scope='Certificate for the supplied finite mixed word')

    def select_homogeneous(self, source):
        """Decide exactly the union of f_i^k J123^k over 21 i and all k >= 1."""
        require(type(source) is int and source >= 1, 'positive integer B1 source required')
        residue = (source - 1) % 128 + 1
        primitive = self.growing.get(residue)
        if primitive is None:
            return None
        a = primitive.slope
        b = primitive.numerator_constant
        coefficient = a - 128
        shifted = coefficient * source + b
        delta = v2(abs(123 - residue))
        exponent = v2(shifted)
        if exponent < 7 + delta or exponent % 7 != delta:
            return None
        periods = (exponent - delta) // 7
        numerator = pow(a, periods) * (shifted >> (7 * periods)) - b
        require(numerator % coefficient == 0, 'growing conjugacy integrality failed')
        switch = numerator // coefficient
        require(switch >= 1, 'growing endpoint is not positive')
        require(v2(coefficient * switch + b) == delta, 'wrong terminal growing valuation')
        target = self._repay(switch, periods)
        if target is None:
            return None
        require(switch % 128 == 123, 'repayment did not start on J123 guard')
        return self._witness(source, target, periods, 'homogeneous_growth_J123_balanced_repayment',
                             growing_residue=residue, growing_slope=a,
                             growing_numerator_constant=b, switch_t=switch,
                             transformed_source_valuation=exponent,
                             switch_valuation=delta, maximal_growing_run=True,
                             scope='Exact union of 21 homogeneous balanced families')

    def mixed_ray(self, word):
        """The unique whole source ray for the supplied growing word then J^k."""
        word = self._word(word)
        modulus, residue, slope, intercept = 1, 1, 1, 1
        path = list(word) + [123] * len(word)
        for label in path:
            primitive = self.bank[label]
            lift = ((primitive.residue - intercept) * pow(slope, -1, 128)) % 128
            new_modulus = 128 * modulus
            new_residue = modulus * lift + residue
            new_slope = primitive.slope * slope
            new_intercept = (primitive.slope *
                             ((slope * lift + intercept - primitive.residue) // 128)
                             + primitive.image_at_residue)
            modulus, residue, slope, intercept = (new_modulus, new_residue,
                                                  new_slope, new_intercept)
        require(modulus == 128 ** (2 * len(word)), 'whole-word modulus is wrong')
        require(0 < slope < modulus and 0 < intercept < residue <= modulus,
                'whole-word strict descent failed')
        return {'M': modulus, 'r': residue, 'A': slope, 'B': intercept,
                'path': path, 'growing_word': list(word),
                'growing_periods': len(word), 'contracting_periods': len(word),
                'source_steps': 14 * len(word), 'target_steps': 0,
                'parameter_domain': 't=M*v+r, v>=0; target=A*v+B'}

    def homogeneous_ray(self, residue, periods):
        require(type(periods) is int and periods >= 1, 'positive integer depth required')
        return self.mixed_ray([residue] * periods)


@lru_cache(maxsize=1)
def _default():
    return BalancedRepayment()


def select_homogeneous(source):
    return _default().select_homogeneous(source)


def consume_mixed(source, word):
    return _default().consume_mixed(source, word)


def homogeneous_ray(residue, periods):
    return _default().homogeneous_ray(residue, periods)


def mixed_ray(word):
    return _default().mixed_ray(word)
