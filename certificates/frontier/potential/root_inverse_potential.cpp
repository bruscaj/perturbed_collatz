// Search a finite type potential, then check every inequality with integers.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;
constexpr Int Scale = 1000000;
constexpr std::array<int, 7> Q = {2619, 2899, 3319, -169, 2835, 3223, -313};

struct Type {
    int shrink;
    int grow_base;
};

void write_binary(std::ofstream& out, Int value) {
    for (int i = 0; i < 8; ++i) {
        out.put(static_cast<char>(value & 255));
        value >>= 8;
    }
}

int main(int argc, char** argv) {
    const int precision = argc > 1 ? std::stoi(argv[1]) : 7;
    const Int shrink_weight = argc > 2 ? std::stoi(argv[2]) : 812129;
    const Int grow_weight = argc > 3 ? std::stoi(argv[3]) : 1129176;
    const int iterations = argc > 4 ? std::stoi(argv[4]) : 2000;
    if (precision < 1 || precision > 14 || shrink_weight <= 0 || grow_weight <= 0
        || shrink_weight > 2 * Scale || grow_weight > 2 * Scale || iterations < 1) {
        throw std::runtime_error("invalid ternary precision, weight or iteration limit");
    }
    int modulus = 1;
    for (int i = 0; i < precision; ++i) {
        modulus *= 3;
    }
    const int reduced = modulus / 3;
    const int count = 7 * modulus;
    std::vector<Type> types;
    types.reserve(count);
    for (int p = 0; p < 7; ++p) {
        const int q = (p + 6) % 7;
        for (int r = 0; r < modulus; ++r) {
            const int shrink = ((2 * r - Q[q]) % modulus + modulus) % modulus;
            const int grow = r % 3 == 0 ? q * modulus + (2 * (r / 3)) % reduced : -1;
            types.push_back({q * modulus + shrink, grow});
        }
    }

    std::vector<double> value(count, 1.0), updated(count);
    for (int t = 0; t < iterations; ++t) {
        double biggest = 0.0;
        for (int i = 0; i < count; ++i) {
            const Type& type = types[i];
            double next = static_cast<double>(shrink_weight) * value[type.shrink];
            if (type.grow_base >= 0) {
                int at = type.grow_base;
                next += static_cast<double>(grow_weight) * std::min({value[at], value[at + reduced],
                                                                    value[at + 2 * reduced]});
            }
            updated[i] = (value[i] + next / Scale) / 2.0;
            biggest = std::max(biggest, updated[i]);
        }
        for (int i = 0; i < count; ++i) {
            value[i] = updated[i] / biggest;
        }
    }

    std::vector<Int> potential(count);
    for (int i = 0; i < count; ++i) {
        potential[i] = 1 + static_cast<Int>(value[i] * 1e12);
    }
    Int smallest_margin = std::numeric_limits<Int>::max();
    Int largest_margin = std::numeric_limits<Int>::min();
    double smallest_ratio = std::numeric_limits<double>::infinity();
    double largest_ratio = 0;
    for (int i = 0; i < count; ++i) {
        const Type& type = types[i];
        Int weighted = shrink_weight * potential[type.shrink];
        if (type.grow_base >= 0) {
            int at = type.grow_base;
            weighted += grow_weight * std::min({potential[at], potential[at + reduced],
                                               potential[at + 2 * reduced]});
        }
        const Int base = Scale * potential[i];
        smallest_margin = std::min(smallest_margin, weighted - base);
        largest_margin = std::max(largest_margin, weighted - base);
        double ratio = static_cast<double>(weighted) / base;
        smallest_ratio = std::min(smallest_ratio, ratio);
        largest_ratio = std::max(largest_ratio, ratio);
    }
    std::cout << "precision=" << precision << " states=" << count
              << " weights=" << shrink_weight << ',' << grow_weight
              << " iterations=" << iterations << " minimum_integer_margin=" << smallest_margin
              << " maximum_integer_margin=" << largest_margin
              << " ratios=" << std::setprecision(10) << smallest_ratio << ',' << largest_ratio << '\n';
    if (argc > 5) {
        if (smallest_margin < 0 && largest_margin >= 0) {
            throw std::runtime_error("cannot export a candidate with mixed margins");
        }
        const std::string name = argv[5];
        std::ofstream out(name, std::ios::binary);
        if (!out) {
            throw std::runtime_error("cannot open potential output");
        }
        if (name.size() >= 4 && name.substr(name.size()-4) == ".bin") {
            for (Int item : {static_cast<Int>(precision), Scale, shrink_weight, grow_weight}) {
                write_binary(out, item);
            }
            for (Int value : potential) write_binary(out, value);
            if (!out) throw std::runtime_error("could not write binary potential");
            return 0;
        }
        out << "{\n  \"precision\": " << precision << ",\n  \"scale\": " << Scale
            << ",\n  \"shrink_weight\": " << shrink_weight << ",\n  \"grow_weight\": " << grow_weight
            << ",\n  \"values\": [\n";
        for (int i = 0; i < count; ++i) {
            if (i % 6 == 0) {
                out << "    ";
            }
            out << potential[i];
            if (i + 1 < count) {
                out << ',';
            }
            if (i % 6 == 5 || i + 1 == count) {
                out << '\n';
            } else {
                out << ' ';
            }
        }
        out << "  ]\n}\n";
    }
}
