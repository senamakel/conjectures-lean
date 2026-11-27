#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <utility>

// Exact 105-edge witness search inside one axis-aligned subcube of Q8.
// Input: dimension and a file with edge count, component count, and vertex labels.

using Occupied = std::array<bool, 256>;
using Mask = std::uint64_t;

std::pair<int, int> measure(const Occupied& used) {
    int vertices = 0, degrees = 0, components = 0;
    Occupied seen{};
    for (int v = 0; v < 256; ++v) {
        if (!used[v]) continue;
        ++vertices;
        int degree = 0;
        for (int bit = 0; bit < 8; ++bit) degree += used[v ^ (1 << bit)];
        if (degree > 2) return {-1, -1};
        degrees += degree;
        if (seen[v]) continue;
        ++components;
        std::array<int, 256> stack{};
        int len = 0;
        stack[len++] = v;
        seen[v] = true;
        while (len) {
            int w = stack[--len];
            for (int bit = 0; bit < 8; ++bit) {
                int u = w ^ (1 << bit);
                if (used[u] && !seen[u]) {
                    seen[u] = true;
                    stack[len++] = u;
                }
            }
        }
    }
    int edges = degrees / 2;
    return edges == vertices - components ? std::pair{edges, components} : std::pair{-1, -1};
}

struct Refill {
    Occupied outside;
    std::array<int, 64> vertices{};
    std::array<Mask, 64> adjacent{};
    std::array<int, 64> degrees{};
    std::uint64_t nodes = 0, high = 0;

    void visit(Mask remaining, Mask selected, int edges) {
        ++nodes;
        // Each additional selected vertex contributes at most two new edges.
        if (edges + 2 * std::popcount(remaining) < 105) return;
        if (edges >= 105) {
            ++high;
            auto full = outside;
            for (Mask bits = selected; bits; bits &= bits - 1)
                full[vertices[std::countr_zero(bits)]] = true;
            auto [e, k] = measure(full);
            if (e >= 105) {
                if (e != edges) std::exit(2);
                std::cout << "WITNESS " << e << " edges " << k << " components:";
                for (int i = 0; i < 256; ++i) if (full[i]) std::cout << ' ' << i;
                std::cout << '\n';
                std::exit(0);
            }
        }
        if (!remaining) return;
        int i = std::countr_zero(remaining);
        Mask item = Mask{1} << i;
        remaining ^= item;
        visit(remaining, selected, edges);
        Mask neighbors = adjacent[i] & selected;
        int degree = degrees[i] + std::popcount(neighbors);
        if (degree > 2) return;
        for (Mask bits = neighbors; bits; bits &= bits - 1)
            if (degrees[std::countr_zero(bits)] == 2) return;
        for (Mask bits = neighbors; bits; bits &= bits - 1)
            ++degrees[std::countr_zero(bits)];
        int cross = degrees[i];
        degrees[i] = degree;
        visit(remaining, selected | item, edges + degree);
        degrees[i] = cross;
        for (Mask bits = neighbors; bits; bits &= bits - 1)
            --degrees[std::countr_zero(bits)];
    }
};

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: refill <dimension 1..6> <seed file>\n";
        return 2;
    }
    int dimension = std::atoi(argv[1]);
    if (dimension < 1 || dimension > 6) return 2;
    unsigned cubeSize = 1u << dimension;
    std::ifstream file(argv[2]);
    int m, k, x;
    if (!(file >> m >> k)) return 2;
    Occupied seed{};
    while (file >> x) {
        if (x < 0 || x >= 256 || seed[x]) return 2;
        seed[x] = true;
    }
    if (measure(seed) != std::pair{m, k}) return 2;
    std::uint64_t nodes = 0, high = 0;
    unsigned cubes = 0;
    for (int moving = 0; moving < 256; ++moving) {
        if (std::popcount(static_cast<unsigned>(moving)) != dimension) continue;
        for (int anchor = 0; anchor < 256; ++anchor) {
            if (anchor & moving) continue;
            ++cubes;
            Refill state{seed};
            unsigned next = 0;
            for (int x = 0; x < 256; ++x) {
                if ((x & ~moving) != anchor) continue;
                state.vertices[next++] = x;
                state.outside[x] = false;
            }
            int outsideEdges = measure(state.outside).first;
            if (outsideEdges < 0) return 2;
            std::array<int, 256> outsideDegree{};
            for (int x = 0; x < 256; ++x)
                if (state.outside[x])
                    for (int bit = 0; bit < 8; ++bit)
                        outsideDegree[x] += state.outside[x ^ (1 << bit)];
            // An exterior vertex has at most one neighbor in this subcube.
            // A saturated exterior neighbor therefore excludes the incident candidate.
            Mask allowed = 0;
            for (unsigned i = 0; i < cubeSize; ++i) {
                bool saturated = false;
                int x = state.vertices[i];
                for (int bit = 0; bit < 8; ++bit) {
                    int y = x ^ (1 << bit);
                    if (state.outside[y]) {
                        ++state.degrees[i];
                        saturated |= outsideDegree[y] >= 2;
                    }
                }
                if (!saturated && state.degrees[i] <= 2) allowed |= Mask{1} << i;
                for (unsigned j = 0; j < cubeSize; ++j)
                    if (std::popcount(static_cast<unsigned>(x ^ state.vertices[j])) == 1)
                        state.adjacent[i] |= Mask{1} << j;
            }
            state.visit(allowed, 0, outsideEdges);
            nodes += state.nodes;
            high += state.high;
        }
    }
    std::cout << "seed " << m << " edges " << k << " components: no witness; "
              << cubes << " cubes, " << nodes << " search nodes, " << high
              << " qualifying-edge checks\n";
}
