// Scan seed 1 for every specified rooted escaping four-pair word in a shard.
// Physical maxima include pair interiors. Fixed-word laps continue to exact closure.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using N = std::uint64_t;
struct Pair { unsigned b, a; };
using Word = std::array<Pair,4>;
struct Edge { N end, peak; };

N T(N n) {
    if (!(n & 1)) return n / 2;
    if (n > (std::numeric_limits<N>::max()-1)/3) throw std::overflow_error("ordinary step");
    return (3*n+1)/2;
}

// T^k(2^k*q+r) = m*q+c. For each residue, verify that a single iterate
// dominates both slope and intercept of every prefix, so its affine value
// gives the exact physical maximum for every q >= 0.
constexpr unsigned block = 8, small = 1024, max_gap = 255;
struct Affine { unsigned m, c; };
struct Jump { Affine end, peak; };
std::array<std::array<Jump,1<<block>,block+1> jumps;
struct SmallEdge { unsigned end, peak; };
std::array<std::array<SmallEdge,max_gap+1>,small> quick;

void initialize() {
    for (unsigned k=0;k<=block;++k) for (unsigned r=0;r<(1u<<k);++r) {
        Affine v{1u<<k,r}, high=v;
        std::array<Affine,block+1> path {};
        path[0]=v;
        for(unsigned j=1;j<=k;++j){
            if(v.m%2) throw std::logic_error("residue width");
            v={v.m/2*((v.c%2)?3u:1u),static_cast<unsigned>(T(v.c))};
            path[j]=v;
            if(v.m>high.m) high=v;
        }
        for(unsigned j=0;j<=k;++j) if(path[j].m>high.m||path[j].c>high.c)
            throw std::logic_error("non-dominating block maximum");
        jumps[k][r]={v,high};
    }
    for(unsigned n=0;n<small;++n) {
        N v=n,high=n;
        for(unsigned g=0;g<=max_gap;++g) {
            if(high>std::numeric_limits<unsigned>::max()) throw std::overflow_error("small table");
            quick[n][g]={static_cast<unsigned>(v),static_cast<unsigned>(high)};
            v=T(v);high=std::max(high,v);
        }
    }
}

inline N jump(N n, unsigned k, N& peak) {
    if(n>std::numeric_limits<N>::max()/10000) {
        for(unsigned j=0;j<k;++j){n=T(n);peak=std::max(peak,n);}
        return n;
    }
    const auto &j=jumps[k][n&((1u<<k)-1)];
    const N q=n>>k;
    peak=std::max(peak,j.peak.m*q+j.peak.c);
    return j.end.m*q+j.end.c;
}

inline N coast(N n, unsigned gap, N& peak) {
#ifdef LITERAL_COAST
    // Independent full-run cross-check. Only the known base cycles are skipped.
    while(gap && n>2) {
        n=T(n);peak=std::max(peak,n);--gap;
    }
    if(gap && n) {
        peak=std::max<N>(peak,2);
        if(gap&1) n=3-n;
    }
    return n;
#else
    while (gap) {
        if(n<small && gap<=max_gap) {
            SmallEdge v=quick[n][gap];
            peak=std::max<N>(peak,v.peak);
            return v.end;
        }
        if(gap<=block) return jump(n,gap,peak);
        n=jump(n,block,peak);
        gap-=block;
    }
    return n;
#endif
}

inline N apply_pair(N n, Pair p, N& peak) {
    n=T(n)+1;
    peak=std::max(peak,n);
    n=coast(n,p.b,peak);
    n=T(n);
    if(!n) throw std::logic_error("unsafe minus");
    --n; peak=std::max(peak,n);
    return coast(n,p.a,peak);
}

template<typename Emit>
void escapes(N n, Emit emit) {
    N u=T(n)+1, prepeak=std::max(n,u);
    for(unsigned b=0;u>2;++b) {
        if(b>=10000) throw std::runtime_error("uncertified ordinary tail before minus");
        N v=T(u)-1, high=std::max(prepeak,v);
        for(unsigned a=0;v>2;++a) {
            if(a>=10000) throw std::runtime_error("uncertified ordinary tail after minus");
            emit(Pair{b,a},Edge{v,high});
            v=T(v);high=std::max(high,v);
        }
        u=T(u);prepeak=std::max(prepeak,u);
    }
}

struct Record {
    N value=0;
    Word witness {};
    void see(N v,const Word &w) {
        if(v>value) {value=v;witness=w;}
    }
    void print() const {
        std::cout<<"{\"value\":"<<value<<",\"word\":[";
        for(unsigned i=0;i<4;++i)std::cout<<(i?",":"")<<"["<<witness[i].b<<","<<witness[i].a<<"]";
        std::cout<<"]}";
    }
};

constexpr unsigned cache_size=32768, state_limit=1000;
struct Cache { unsigned version=0; Edge result {}; };
struct Scan {
    unsigned first, shard, partition, middle=0, prefix=0;
    N count=0, total_laps=0;
    std::vector<Cache> two_cache,three_cache;
    std::array<N,state_limit+1> cycle_hist {},transient_hist {};
    Word w {};
    Record peak,recurrent,ratio,transient;
    Scan(unsigned f,unsigned s,unsigned p):first(f),shard(s),partition(p),
        two_cache(cache_size),three_cache(cache_size) {}

    Edge two(N n) {
        if(n<cache_size && two_cache[n].version==middle)return two_cache[n].result;
        N p=n,v=apply_pair(n,w[0],p);v=apply_pair(v,w[1],p);
        if(n<cache_size)two_cache[n]={middle,{v,p}};
        return {v,p};
    }
    Edge three(N n) {
        if(n<cache_size && three_cache[n].version==prefix)return three_cache[n].result;
        Edge e=two(n);e.end=apply_pair(e.end,w[2],e.peak);
        if(n<cache_size)three_cache[n]={prefix,e};
        return e;
    }

    void close(Edge first_lap) {
        // Arrays are initialized on demand. Every read uses an index < length.
        N states[state_limit],peaks[state_limit];
        states[0]=1;peaks[0]=first_lap.peak;
        N n=first_lap.end,high=first_lap.peak;
        unsigned length=1;
        while(true) {
            unsigned old=0;
            while(old<length && states[old]!=n) ++old;
            if(old<length) {
                N on_cycle=0;
                for(unsigned j=old;j<length;++j)on_cycle=std::max(on_cycle,peaks[j]);
                peak.see(high,w);recurrent.see(on_cycle,w);
                ratio.see(length-old,w);transient.see(old,w);
                ++cycle_hist[length-old];++transient_hist[old];
                total_laps+=length;++count;
                return;
            }
            if(length==state_limit)throw std::runtime_error("unclosed word");
            states[length]=n;
            Edge e=three(n);
            n=apply_pair(e.end,w[3],e.peak);
            peaks[length++]=e.peak;high=std::max(high,e.peak);
        }
    }
    void run() {
        unsigned id=0;
        escapes(1,[&](Pair p,Edge e1) {
            if(id++!=first)return;
            w[0]=p;
            escapes(e1.end,[&](Pair q,Edge e2) {
                ++middle;w[1]=q;
                escapes(e2.end,[&](Pair r,Edge e3) {
                    ++prefix;
                    if((prefix-1)%partition!=shard)return;
                    w[2]=r;
                    const N h=std::max({e1.peak,e2.peak,e3.peak});
                    escapes(e3.end,[&](Pair s,Edge e4) {
                        w[3]=s;close({e4.end,std::max(h,e4.peak)});
                    });
                });
            });
        });
        if(id!=15)throw std::logic_error("first-level count");
    }
    void output() const {
        std::cout<<"{\"first\":"<<first<<",\"shard\":"<<shard<<",\"parts\":"<<partition
                 <<",\"words\":"<<count<<",\"laps\":"<<total_laps<<",\"peak\":";
        peak.print();std::cout<<",\"recurrent\":";recurrent.print();
        std::cout<<",\"ratio\":";ratio.print();std::cout<<",\"transient\":";transient.print();
        for(const auto name : {"cycle_hist","transient_hist"}) {
            const auto& hist=name[0]=='c'?cycle_hist:transient_hist;
            std::cout<<",\""<<name<<"\":{";bool initial=true;
            for(unsigned i=0;i<hist.size();++i)if(hist[i]){
                std::cout<<(initial?"":",")<<"\""<<i<<"\":"<<hist[i];initial=false;
            }
            std::cout<<"}";
        }
        std::cout<<"}\n";
    }
};

int main(int argc,char**argv) {
    if(argc!=4)throw std::invalid_argument("usage: scan FIRST SHARD PARTS");
    unsigned f=std::stoul(argv[1]),s=std::stoul(argv[2]),p=std::stoul(argv[3]);
    if(f>=15||!p||s>=p)throw std::invalid_argument("bad shard");
    initialize();Scan scan(f,s,p);scan.run();scan.output();
}
