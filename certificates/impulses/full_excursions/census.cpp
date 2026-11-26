// One shard per first escaping pair, in increasing (before, after) order.
// Every counted word is followed on its own seed-1 strobe orbit.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

using V = std::uint64_t;
struct Pair { unsigned b, a; };
using Word = std::array<Pair, 4>;
struct Segment { V end, peak; };

V ordinary(V n) {
    if (!(n & 1)) return n / 2;
    if (n > (std::numeric_limits<V>::max() - 1) / 3) throw std::overflow_error("3n+1");
    return (3 * n + 1) / 2;
}

constexpr unsigned small = 1024, gaps = 256;
std::array<std::array<Segment, gaps + 1>, small> table;
void initialize() {
    for (unsigned n = 0; n < small; ++n) {
        auto &row = table[n];
        row[0] = {n,n};
        for (unsigned i = 1; i <= gaps; ++i) {
            V value = ordinary(row[i-1].end);
            row[i] = {value,std::max(row[i-1].peak,value)};
        }
    }
}

Segment coast(V n, unsigned k) {
    if (n < small && k <= gaps) return table[n][k];
    V peak = n;
    while (k) {
        if (n < small && k <= gaps) {
            auto result = table[n][k];
            return {result.end,std::max(peak,result.peak)};
        }
        n = ordinary(n);
        peak = std::max(peak,n);
        --k;
    }
    return {n,peak};
}

Segment pair_step(V n, Pair pair) {
    Segment early = coast(ordinary(n)+1,pair.b);
    V m = ordinary(early.end);
    if (!m) throw std::logic_error("unsafe negative impulse");
    Segment late = coast(m-1,pair.a);
    return {late.end,std::max({n,early.peak,late.peak})};
}

template<class Emit>
void escapes(V n, Emit emit) {
    V u = ordinary(n)+1, early_peak = std::max(n,u);
    for (unsigned b = 0; u > 2; ++b) {
        if (b == 10000) throw std::runtime_error("pre-minus ordinary tail unresolved");
        V v = ordinary(u)-1, peak = std::max(early_peak,v);
        for (unsigned a = 0; v > 2; ++a) {
            if (a == 10000) throw std::runtime_error("post-minus ordinary tail unresolved");
            emit(Pair{b,a},Segment{v,peak});
            v = ordinary(v);
            peak = std::max(peak,v);
        }
        u = ordinary(u);
        early_peak = std::max(early_peak,u);
    }
}

bool equal(Pair x, Pair y) { return x.b==y.b && x.a==y.a; }
bool primitive(const Word &w) {
    // Every proper period must preserve positive-pulse slots, hence divide four pairs.
    return !equal(w[0],w[2]) || !equal(w[1],w[3]);
}

struct Sample {
    V value = 0;
    Word word {};
    void update(V next, const Word &w) { if (next > value) {value=next;word=w;} }
};

struct Memo { V stamp=0, input=0; Segment result {}; };
struct Run {
    std::array<Memo,2048> prefix_cache {};
    V stamp=0, words=0;
    V prefix_index=0;
    unsigned part=0, parts=1;
    std::vector<V> cycles,transients,primitive_cycles;
    std::map<unsigned,Word> witnesses;
    Sample worst, recurrent;
    struct Visit { V n, peak; };
    std::vector<Visit> trace;
    Word word {};
    Run() { trace.reserve(40); }

    Segment first_three(V n) {
        // Reuse a prefix only on exactly the same input with exactly the same word prefix.
        auto &cell=prefix_cache[n % prefix_cache.size()];
        if (cell.stamp==stamp && cell.input==n) return cell.result;
        Segment total={n,n};
        for (unsigned i=0;i<3;++i) {
            auto next=pair_step(total.end,word[i]);
            total={next.end,std::max(total.peak,next.peak)};
        }
        cell={stamp,n,total};
        return total;
    }
    static void count(std::vector<V> &hist,unsigned index) {
        if (hist.size()<=index) hist.resize(index+1);
        ++hist[index];
    }
    void close(Segment first) {
        // Enumeration supplied this entire first lap, including every intermediate peak.
        trace.clear();
        trace.push_back({1,first.peak});
        V n=first.end;
        V peak=first.peak;
        for (;;) {
            auto old=std::find_if(trace.begin(),trace.end(),[n](const Visit &v){return v.n==n;});
            if(old!=trace.end()) {
                unsigned mu=static_cast<unsigned>(old-trace.begin());
                unsigned period=static_cast<unsigned>(trace.end()-old);
                count(transients,mu);count(cycles,period);
                if (primitive(word)) {
                    count(primitive_cycles,period);
                    if (primitive_cycles[period]==1) witnesses.emplace(period,word);
                }
                worst.update(peak,word);
                if(peak>recurrent.value) {
                    V cycle_peak=0;
                    for (;old!=trace.end();++old) cycle_peak=std::max(cycle_peak,old->peak);
                    recurrent.update(cycle_peak,word);
                }
                ++words;
                return;
            }
            if (trace.size()>=1000) throw std::runtime_error("unclosed strobe trajectory");
            auto head=first_three(n),last=pair_step(head.end,word[3]);
            V lap_peak=std::max(head.peak,last.peak);
            trace.push_back({n,lap_peak});
            peak=std::max(peak,lap_peak);
            n=last.end;
        }
    }

    void descend(unsigned depth, Segment previous) {
        if (depth==3) {
            if (prefix_index++ % parts != part) return;
            ++stamp;
        }
        escapes(previous.end,[&](Pair p,Segment next){
            word[depth]=p;
            next.peak=std::max(next.peak,previous.peak);
            if (depth==3) close(next);
            else descend(depth+1,next);
        });
    }
};

void print_word(const Word &word) {
    std::cout << "[";
    for (unsigned i=0;i<4;++i)
        std::cout << (i?",":"") << "[" << word[i].b << "," << word[i].a << "]";
    std::cout << "]";
}
void print_hist(const std::vector<V> &values) {
    std::cout << "{";
    bool first=true;
    for(unsigned i=0;i<values.size();++i) if(values[i]) {
        std::cout << (first?"":",") << '"' << i << "\":" << values[i];first=false;
    }
    std::cout << "}";
}
void print_peak(const Sample &peak) {
    std::cout << "{\"value\":" << peak.value << ",\"pairs\":";
    print_word(peak.word);std::cout << "}";
}
int main(int argc,char **argv) {
    if(argc!=2 && argc!=4) throw std::invalid_argument("usage: census first_pair [part parts]");
    unsigned shard=std::stoul(argv[1]),index=0;
    initialize();
    Run run;
    if(argc==4) {
        run.part=std::stoul(argv[2]);run.parts=std::stoul(argv[3]);
        if(run.part>=run.parts) throw std::invalid_argument("invalid partition");
    }
    escapes(1,[&](Pair p,Segment next){
        if(index++==shard) {run.word[0]=p;run.descend(1,next);}
    });
    if(index!=15 || !run.words) throw std::invalid_argument("empty shard");
    std::cout << "{\"shard\":"<<shard<<",\"part\":"<<run.part<<",\"parts\":"<<run.parts
              <<",\"words\":"<<run.words<<",\"cycle\":";
    print_hist(run.cycles);std::cout << ",\"transient\":";print_hist(run.transients);
    std::cout << ",\"primitive_cycle\":";print_hist(run.primitive_cycles);
    std::cout << ",\"primitive_examples\":{";
    bool first=true;
    for(const auto &entry:run.witnesses) {
        std::cout << (first?"":",") << '"' << entry.first << "\":";
        print_word(entry.second);first=false;
    }
    std::cout << "},\"peak\":";print_peak(run.worst);
    std::cout << ",\"recurrent_peak\":";print_peak(run.recurrent);std::cout << "}\n";
}
