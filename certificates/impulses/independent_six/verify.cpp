// Exhaustive verifier for three alternating (+,-) pairs, starting in {0,1,2}.
// Output counts rooted paths, so a cyclic word can be checked more than once.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

using Value = std::uint64_t;
struct Pair { unsigned b, a; };
using Word = std::array<Pair, 3>;

Value ordinary(Value n) {
    if (n % 2 == 0) return n / 2;
    if (n > (std::numeric_limits<Value>::max() - 1) / 3)
        throw std::overflow_error("ordinary step");
    return (3 * n + 1) / 2;
}

Value minus_step(Value n) {
    Value m = ordinary(n);
    if (m == 0) throw std::domain_error("unsafe minus impulse");
    return m - 1;
}

void signed_layers() {
    std::set<Value> previous {0,1,2};
    std::cout << "{\n  \"signed_layers\": [";
    for (unsigned j = 1; j <= 6; ++j) {
        std::set<Value> current;
        for (Value n : previous) {
            Value v = j % 2 ? ordinary(n) + 1 : minus_step(n);
            std::set<Value> trace;
            while (v > 2 && !current.count(v)) {
                if (!trace.insert(v).second || trace.size() > 100000)
                    throw std::runtime_error("uncertified ordinary return");
                v = ordinary(v);
            }
            current.insert(trace.begin(), trace.end());
            if (v == 0) current.insert(0);
            if (v == 1 || v == 2) {
                current.insert(1);
                current.insert(2);
            }
        }
        std::cout << (j == 1 ? "" : ", ") << "[" << current.size() << ", "
                  << *current.rbegin() << "]";
        previous.swap(current);
    }
    std::cout << "],\n";
}

// List every gap pair from n whose endpoint exceeds 2. The verified signed
// closures above establish finite ordinary returns for all three nesting levels.
template <typename Callback>
void escapes(Value n, Callback emit) {
    Value u = ordinary(n) + 1;
    for (unsigned b = 0; u > 2; ++b, u = ordinary(u)) {
        Value v = minus_step(u);
        for (unsigned a = 0; v > 2; ++a, v = ordinary(v)) {
            emit(Pair{b,a}, v);
        }
    }
}

// Literal iteration, skipping only the explicit finite orbits of 0, 1 and 2.
Value coast(Value n, unsigned gap, Value& peak) {
    while (gap && n > 2) {
        n = ordinary(n);
        peak = std::max(peak, n);
        --gap;
    }
    if (gap && n) {
        peak = std::max<Value>(peak, 2);
        if (gap % 2) n = 3 - n;
    }
    return n;
}

Value pair_step(Value n, Pair gap, Value& peak) {
    n = ordinary(n) + 1;
    peak = std::max(peak, n);
    n = coast(n, gap.b, peak);
    n = minus_step(n);
    peak = std::max(peak, n);
    return coast(n, gap.a, peak);
}

struct Reached {
    Value n, edge_peak;
    unsigned walk, depth;
};

struct Witness {
    Value value = 0;
    Word word {};
    unsigned phase = 0, seed = 0;

    void update(Value v, const Word& w, unsigned ph, unsigned s) {
        if (v > value) { value = v; word = w; phase = ph; seed = s; }
    }
    void print() const {
        std::cout << "{\"value\": " << value << ", \"pairs\": [";
        for (unsigned j = 0; j < 3; ++j)
            std::cout << (j ? ", " : "") << "[" << word[j].b << ", " << word[j].a << "]";
        std::cout << "], \"seed\": " << seed << ", \"before_pair\": " << phase << "}";
    }
};

struct Census {
    std::array<std::vector<Reached>,3> reached;
    std::array<Value,3> prefixes {};
    Value transitions = 0;
    unsigned max_states = 0;
    Witness peak, ratio, recurrent_peak;
    std::map<unsigned, Value> cycles_by_ratio, words_by_max_ratio;

    void verify(const Word& word) {
        for (auto& phase : reached) phase.clear();
        unsigned states = 0, max_ratio = 0;
        for (unsigned start = 0; start < 3; ++start) {
            for (unsigned seed = 0; seed < 3; ++seed) {
                Value n = seed, high = seed;
                unsigned phase = start;
                const unsigned walk = 3 * start + seed;
                for (unsigned depth = 0;; ++depth) {
                    auto& here = reached[phase];
                    auto old = std::find_if(here.begin(), here.end(),
                        [n](const Reached& v){ return n == v.n; });
                    if (old != here.end()) {
                        if (old->walk == walk) {
                            unsigned length = depth - old->depth;
                            if (length % 3) throw std::logic_error("cycle phase mismatch");
                            const unsigned r = length / 3;
                            ratio.update(r, word, start, seed);
                            ++cycles_by_ratio[r];
                            max_ratio = std::max(max_ratio, r);
                            for (const auto& layer : reached) {
                                for (const auto& state : layer) {
                                    if (state.walk == walk && state.depth >= old->depth)
                                        recurrent_peak.update(state.edge_peak, word, start, seed);
                                }
                            }
                        }
                        break;
                    }
                    if (++states > 100000) throw std::runtime_error("unclosed word");
                    Value edge_peak = n;
                    Value next = pair_step(n, word[phase], edge_peak);
                    here.push_back({n, edge_peak, walk, depth});
                    high = std::max(high, edge_peak);
                    n = next;
                    phase = (phase + 1) % 3;
                }
                peak.update(high, word, start, seed);
            }
        }
        max_states = std::max(states, max_states);
        transitions += states;
        ++words_by_max_ratio[max_ratio];
    }
};

void print_histogram(const std::map<unsigned, Value>& counts) {
    std::cout << "{";
    bool first = true;
    for (auto [key, value] : counts) {
        std::cout << (first ? "" : ", ") << "\"" << key << "\": " << value;
        first = false;
    }
    std::cout << "}";
}

int main() {
    signed_layers();
    Census census;
    for (Value seed : {0,1,2}) {
        escapes(seed, [&](Pair first, Value n1) {
            ++census.prefixes[0];
            escapes(n1, [&](Pair second, Value n2) {
                ++census.prefixes[1];
                escapes(n2, [&](Pair third, Value) {
                    ++census.prefixes[2];
                    census.verify({first, second, third});
                });
            });
        });
    }
    std::cout << "  \"escaping_prefixes\": [" << census.prefixes[0] << ", "
              << census.prefixes[1] << ", " << census.prefixes[2] << "],\n"
              << "  \"rooted_boundary_transitions\": " << census.transitions << ",\n"
              << "  \"max_states_per_rooted_word\": " << census.max_states << ",\n"
              << "  \"peak\": ";
    census.peak.print();
    std::cout << ",\n  \"response_ratio\": ";
    census.ratio.print();
    std::cout << ",\n  \"recurrent_peak\": ";
    census.recurrent_peak.print();
    std::cout << ",\n  \"rooted_cycles_by_ratio\": ";
    print_histogram(census.cycles_by_ratio);
    std::cout << ",\n  \"rooted_words_by_max_ratio\": ";
    print_histogram(census.words_by_max_ratio);
    std::cout << "\n}\n";
}
