"""Hostile tests of the public eight-impulse partition consumer.

Uses only the bundled files and Python's standard library. These tests check
rejection of corrupted evidence; they do not replace the full recurrence census.
"""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("eight_partition_checker", HERE / "full_excursions" / "run.py")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class PartitionMutationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = json.loads((HERE / "full_excursions" / "partitions.json").read_text())
        cls.local = next(i for i, r in enumerate(cls.records) if r["shard"] == 1)
        cls.split = [i for i, r in enumerate(cls.records) if r["shard"] == 3]
        # Accept the authentic complete control before testing any rejection.
        cls.control = CHECKER.summarize(deepcopy(cls.records))

    def reject(self, change, message):
        records = deepcopy(self.records)
        change(records)
        with self.assertRaisesRegex((ValueError, ArithmeticError), message):
            CHECKER.summarize(records)

    def test_authentic_control(self):
        expected = json.loads((HERE / "full_excursions" / "results.json").read_text())
        # Normalize JSON object keys, which are strings in the stored file.
        self.assertEqual(json.loads(json.dumps(self.control)), expected)
        self.assertEqual(self.control["words"], 2383451629)

    def test_malformed_local_witness(self):
        for pairs in (None, [], [[1, 0]] * 3,
                      [[1, 0], [0, 0], [0, 0], [-1, 0]],
                      [[1, 0], [0, 0], [0, 0], [True, 0]]):
            with self.subTest(pairs=pairs):
                self.reject(lambda rows: rows[self.local]["peak"].update(pairs=pairs),
                            "four pairs of nonnegative integer gaps")

    def test_wrong_nonwinning_local_peak(self):
        self.reject(lambda rows: rows[self.local]["peak"].update(
            value=rows[self.local]["peak"]["value"] + 1), "invalid shard peak witness")

    def test_wrong_local_recurrent_peak(self):
        self.reject(lambda rows: rows[self.local]["recurrent_peak"].update(
            value=rows[self.local]["recurrent_peak"]["value"] + 1),
            "invalid shard recurrent_peak witness")

    def test_negative_count_with_preserved_total(self):
        def change(rows):
            histogram = rows[self.local]["cycle"]
            previous = histogram["1"]
            histogram["1"] = -1
            histogram["2"] += previous + 1
        self.reject(change, "invalid cycle histogram")

    def test_cross_shard_witness(self):
        self.reject(lambda rows: rows[self.local].update(peak=deepcopy(rows[0]["peak"])),
                    "different first-pair shard")

    def test_cross_subpartition_witness(self):
        left, right = self.split[:2]
        self.reject(lambda rows: rows[left].update(peak=deepcopy(rows[right]["peak"])),
                    "different third-prefix partition")

    def test_ineligible_excursion_pair(self):
        def change(rows):
            rows[self.local]["peak"]["pairs"][1] = [1000, 0]
        self.reject(change, "ineligible excursion pair")

    def test_duplicate_partition(self):
        self.reject(lambda rows: rows.append(deepcopy(rows[0])),
                    "incomplete or duplicate partitions")

    def test_missing_partition(self):
        self.reject(lambda rows: rows.pop(), "incomplete or duplicate partitions")

    def test_duplicate_replacing_missing_partition(self):
        self.reject(lambda rows: rows.__setitem__(1, deepcopy(rows[0])),
                    "incomplete or duplicate partitions")

    def test_wrong_subpartition_populations_with_preserved_aggregates(self):
        def change(rows):
            for index, delta in zip(self.split[:2], (1, -1)):
                record = rows[index]
                record["words"] += delta
                for key, bin_name in (("cycle", "1"), ("transient", "0"),
                                      ("primitive_cycle", "1")):
                    record[key][bin_name] += delta
            self.assertEqual(sum(r["words"] for r in rows), self.control["words"])
            for key in ("cycle", "transient", "primitive_cycle"):
                for bin_name in set().union(*(r[key] for r in rows)):
                    self.assertEqual(sum(r[key].get(bin_name, 0) for r in rows),
                                     sum(r[key].get(bin_name, 0) for r in self.records))
        self.reject(change, "inconsistent shard histogram totals")

    def test_missing_local_primitive_witness(self):
        self.reject(lambda rows: rows[self.local]["primitive_examples"].pop("1"),
                    "missing or extra primitive witness")

    def test_wrong_local_primitive_period(self):
        def change(rows):
            examples = rows[self.local]["primitive_examples"]
            examples["2"] = deepcopy(examples["1"])
        self.reject(change, "invalid shard primitive period witness")

    def test_boolean_partition_identifier(self):
        self.reject(lambda rows: rows[self.local].update(shard=True),
                    "invalid partition identifiers")


if __name__ == "__main__":
    unittest.main(verbosity=2)
