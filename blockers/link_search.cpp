// Exhaustive check of small triple blockers of partitions of nine points.
// A vertex of maximum degree is the distinguished point 8. Its link is an
// ordinary graph on points 0..7. All graphs on those points are generated.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
#ifdef _MSC_VER
#include <intrin.h>
#endif

using Bits = std::uint64_t;
using Graph = std::uint32_t;

int count(Bits mask) {
#ifdef _MSC_VER
    return static_cast<int>(__popcnt64(mask));
#else
    return __builtin_popcountll(mask);
#endif
}
int first(Bits mask) {
#ifdef _MSC_VER
    unsigned long result;
    _BitScanForward64(&result, mask);
    return result;
#else
    return __builtin_ctzll(mask);
#endif
}
int edge(int a, int b) {
    if (a > b) std::swap(a, b);
    return b * (b - 1) / 2 + a;
}

struct Canonical {
    int size;
    Graph graph;
    Graph best = ~Graph(0);
    std::array<int,8> order{}, degree{};
    std::array<std::uint64_t,8> signature{}, target{};
    Canonical(int n, Graph g) : size(n), graph(g) {
        for (int a = 0; a < n; ++a)
            for (int b = 0; b < n; ++b)
                if (a != b && (g & (1u << edge(a,b)))) ++degree[a];
        for (int a = 0; a < n; ++a) {
            signature[a] = std::uint64_t(degree[a]) << 32;
            for (int b = 0; b < n; ++b)
                if (a != b && (g & (1u << edge(a,b))))
                    signature[a] += Bits(1) << (4 * degree[b]);
        }
        target = signature;
        std::sort(target.begin(), target.begin() + n);
        label(0, (1u << n) - 1, 0);
    }
    void label(int pos, unsigned available, Graph image) {
        if (image >= best) return;
        if (pos == size) { best = image; return; }
        for (int v = 0; v < size; ++v) {
            if (!(available & (1u << v)) || signature[v] != target[pos]) continue;
            Graph next = image;
            for (int j = 0; j < pos; ++j)
                if (graph & (1u << edge(order[j],v))) next |= 1u << edge(j,pos);
            order[pos] = v;
            label(pos+1, available ^ (1u << v), next);
        }
    }
};

std::set<Graph> all_links() {
    std::set<Graph> graphs{0};
    const int known[] = {1,1,2,4,11,34,156,1044,12346};
    for (int n = 2; n <= 8; ++n) {
        std::set<Graph> next;
        for (Graph g : graphs)
            for (unsigned neighbors = 0; neighbors < (1u << (n-1)); ++neighbors) {
                Graph extended = g | (neighbors << ((n-1)*(n-2)/2));
                next.insert(Canonical(n,extended).best);
            }
        graphs.swap(next);
        if (graphs.size() != static_cast<unsigned>(known[n]))
            throw std::runtime_error("Unlabeled graph count mismatch");
    }
    return graphs;
}

struct Search {
    Graph link;
    int maxdeg;
    std::array<unsigned,56> triple{};
    std::array<Bits,56> adj{};
    std::array<int,8> deg{};
    std::uint64_t nodes = 0;
    explicit Search(Graph g) : link(g), maxdeg(count(g)) {
        int t = 0;
        for (unsigned mask = 0; mask < 256; ++mask)
            if (count(mask) == 3) triple[t++] = mask;
        for (int a = 0; a < 8; ++a)
            for (int b = a+1; b < 8; ++b)
                if (link & (1u << edge(a,b))) { ++deg[a]; ++deg[b]; }
        for (int i = 0; i < 56; ++i)
            for (int j = 0; j < i; ++j) {
                if (triple[i] & triple[j]) continue;
                unsigned rest = 255 ^ (triple[i] | triple[j]);
                int a = first(rest), b = first(rest & (rest-1));
                if (!(g & (1u << edge(a,b)))) {
                    adj[i] |= Bits(1) << j;
                    adj[j] |= Bits(1) << i;
                }
            }
    }
    // The chosen triples must cover every edge: on each such edge, the
    // third triple of the partition contains point 8 and is outside Bad.
    bool cover(Bits active, Bits chosen, int left) {
        ++nodes;
        if (left < 0) return false;
        int pivot = -1, maximum = 0;
        Bits matchable = active;
        int matching = 0;
        for (Bits bits = active; bits; bits &= bits-1) {
            int v = first(bits);
            Bits neighbors = adj[v] & active;
            int d = count(neighbors);
            if (d > maximum) { pivot = v; maximum = d; }
            if ((matchable & (Bits(1)<<v)) && (neighbors & matchable)) {
                int w = first(neighbors & matchable);
                matchable &= ~((Bits(1)<<v) | (Bits(1)<<w));
                if (++matching > left) return false;
            }
        }
        if (pivot < 0) {
            auto degrees = deg;
            for (Bits items = chosen; items; items &= items-1)
                for (unsigned points = triple[first(items)]; points; points &= points-1)
                    ++degrees[first(points)];
            // Every named vertex contributes at least two distinct bad triples.
            for (int d : degrees)
                if (d > maxdeg || d + left < 2) return false;
            return true;
        }
        Bits single = Bits(1) << pivot;
        Bits neighbors = adj[pivot] & active;
        return cover(active & ~single, chosen | single, left-1) ||
               cover(active & ~(single | neighbors), chosen | neighbors, left-maximum);
    }
};

int main() {
    auto links = all_links();
    std::uint64_t nodes = 0;
    std::array<int,29> cases{}, survivors{};
    std::set<Graph> possible_links;
    for (auto link : links) {
        int d = count(link);
        if (d < 10 || d > 19) continue;
        Search s(link);
        ++cases[d];
        if (s.cover((Bits(1)<<56)-1, 0, 35-d)) {
            ++survivors[d];
            possible_links.insert(link);
            std::cout << "possible link, degree " << d << ", mask " << link << "\n";
        }
        nodes += s.nodes;
    }
    for (int d = 10; d <= 19; ++d)
        std::cout << "degree " << d << " tested " << cases[d] << " survivors " << survivors[d] << "\n";
    std::cout << "branch nodes " << nodes << "\n";
    // In this labeling the first ten bits are the edges among points 0..4.
    Graph complete = (1u << 28) - 1;
    Graph without_five_clique = complete ^ ((1u << 10) - 1);
    Graph with_one_pair = without_five_clique | (1u << edge(3,4));
    if (possible_links != std::set<Graph>{without_five_clique, with_one_pair})
        throw std::runtime_error("Unexpected survivors");
    std::cout << "PASS: all surviving links have the two reported forms.\n";
}
