#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>

// Independent first-phase census for the Q7-at-53 split argument.
// Normalize a degree-two vertex and its two neighbors to {0,1,2} in Q6.
// Count induced linear-forest layers with 23..26 edges and at least 27 vertices.
// Usage: enumerate_q6_heavy_layers <exact-edge-count 23..26> <mask-output>
// Resource caps are enforced by the caller and the per-slice caps below.

struct Search {
  std::array<std::uint8_t, 64> degree{};
  std::array<std::uint64_t, 64> neighbors{};
  std::uint64_t nodes = 0;
  std::uint64_t labeled = 0;
  std::uint64_t cyclic_leaves = 0;
  bool stopped = false;
  int target_edges;
  std::ofstream masks;
  std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();

  Search(int target, const std::string &output)
      : target_edges(target), masks(output, std::ios::binary | std::ios::trunc) {}

  bool within_limits() {
    if (nodes >= 6'000'000'000ULL ||
        ((nodes & 0xffff) == 0 &&
         std::chrono::steady_clock::now() - start >= std::chrono::seconds(180))) {
      stopped = true;
      return false;
    }
    return true;
  }

  void visit(std::uint64_t remaining, std::uint64_t selected, int vertices,
             int edges) {
    if (!within_limits()) return;
    ++nodes;
    int remaining_count = std::popcount(remaining);
    if (edges > target_edges || edges + 2 * remaining_count < target_edges ||
        vertices + remaining_count < 27)
      return;
    if (remaining == 0) {
      if (edges != target_edges || vertices < 27) return;
      std::array<bool, 64> seen{};
      int components = 0;
      int degree_sum = 0;
      for (int v = 0; v < 64; ++v) {
        if (((selected >> v) & 1U) == 0) continue;
        degree_sum += degree[v];
        if (seen[v]) continue;
        ++components;
        std::array<int, 64> stack{};
        int size = 0;
        stack[size++] = v;
        seen[v] = true;
        while (size > 0) {
          int u = stack[--size];
          std::uint64_t adjacent = neighbors[u] & selected;
          while (adjacent != 0) {
            int w = std::countr_zero(adjacent);
            adjacent &= adjacent - 1;
            if (!seen[w]) {
              seen[w] = true;
              stack[size++] = w;
            }
          }
        }
      }
      if (degree_sum != 2 * edges) {
        std::cerr << "invariant failure: edges=" << edges
                  << " vertices=" << vertices
                  << " components=" << components
                  << " degree_sum=" << degree_sum << '\n';
        stopped = true;
        return;
      }
      if (edges != vertices - components) {
        ++cyclic_leaves;
        return;
      }
      if (!masks) {
        std::cerr << "failed to open mask output\n";
        stopped = true;
        return;
      }
      masks.write(reinterpret_cast<const char *>(&selected), sizeof(selected));
      if (!masks) {
        std::cerr << "failed writing mask output\n";
        stopped = true;
        return;
      }
      ++labeled;
      return;
    }

    // Pick the most constrained undecided vertex, breaking ties by label.
    int next = -1;
    int best_score = -1;
    for (std::uint64_t todo = remaining; todo != 0; todo &= todo - 1) {
      int candidate = std::countr_zero(todo);
      int score = std::popcount(neighbors[candidate] & selected);
      if (score > best_score) {
        next = candidate;
        best_score = score;
      }
    }
    std::uint64_t next_remaining = remaining & ~(std::uint64_t{1} << next);

    // Including it is legal exactly when the new induced degree is at most 2
    // at this vertex and does not push an already-selected neighbor over 2.
    std::uint64_t adjacent_selected = neighbors[next] & selected;
    int new_degree = std::popcount(adjacent_selected);
    bool can_include = new_degree <= 2;
    for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1) {
      int u = std::countr_zero(todo);
      if (degree[u] >= 2) can_include = false;
    }
    if (can_include) {
      for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1)
        ++degree[std::countr_zero(todo)];
      degree[next] = static_cast<std::uint8_t>(new_degree);
      visit(next_remaining, selected | (std::uint64_t{1} << next), vertices + 1,
            edges + new_degree);
      degree[next] = 0;
      for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1)
        --degree[std::countr_zero(todo)];
    }
    if (stopped) return;

    // Excluding the next vertex.
    visit(next_remaining, selected, vertices, edges);
  }

  void run() {
    for (int v = 0; v < 64; ++v)
      for (int bit = 0; bit < 6; ++bit)
        neighbors[v] |= std::uint64_t{1} << (v ^ (1 << bit));
    // Canonical degree-two pattern: origin 0 and neighbors 1 and 2.
    degree[0] = 2;
    degree[1] = degree[2] = 1;
    visit(~std::uint64_t{0} & ~std::uint64_t{0b111}, 0b111, 3, 2);
  }
};

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cerr << "usage: enumerate_q6_heavy_layers <exact-edge-count 23..26> <mask-output>\n";
    return 2;
  }
  int target = std::stoi(argv[1]);
  if (target < 23 || target > 26) return 2;
  Search search(target, argv[2]);
  if (!search.masks) {
    std::cerr << "could not open mask output\n";
    return 2;
  }
  search.run();
  const double seconds = std::chrono::duration<double>(
      std::chrono::steady_clock::now() - search.start).count();
  std::cout << (search.stopped ? "STOPPED" : "COMPLETE")
            << " target_edges=" << target << " nodes=" << search.nodes
            << " labeled=" << search.labeled
            << " cyclic_leaves=" << search.cyclic_leaves
            << " wall_seconds=" << seconds << '\n';
  return search.stopped ? 1 : 0;
}
