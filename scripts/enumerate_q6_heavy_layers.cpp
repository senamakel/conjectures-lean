#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

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
  std::uint64_t forced_exclusions = 0;
  std::uint64_t early_cycle_prunes = 0;
  bool stopped = false;
  bool force_saturated_neighbors;
  bool early_cycle_check;
  bool use_capacity_bound;
  int target_edges;
  std::ofstream masks;
  std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();

  struct RollbackDsu {
    struct Change { int child; int root; int root_size; bool made_set; };
    std::array<int, 64> parent{};
    std::array<int, 64> size{};
    std::vector<Change> history;

    RollbackDsu() { parent.fill(-1); }

    int find(int x) const {
      while (parent[x] != x) x = parent[x];
      return x;
    }

    std::size_t snapshot() const { return history.size(); }

    void make_set(int x) {
      history.push_back({x, -1, 0, true});
      parent[x] = x;
      size[x] = 1;
    }

    void unite(int a, int b) {
      int ra = find(a), rb = find(b);
      if (ra == rb) return;
      if (size[ra] < size[rb]) std::swap(ra, rb);
      history.push_back({rb, ra, size[ra], false});
      parent[rb] = ra;
      size[ra] += size[rb];
    }

    void rollback(std::size_t mark) {
      while (history.size() > mark) {
        Change c = history.back();
        history.pop_back();
        if (c.made_set) {
          parent[c.child] = -1;
          size[c.child] = 0;
        } else {
          parent[c.child] = c.child;
          size[c.root] = c.root_size;
        }
      }
    }
  } dsu;

  Search(int target, const std::string &output, bool force_saturated,
         bool early_cycle, bool capacity_bound)
      : force_saturated_neighbors(force_saturated), early_cycle_check(early_cycle),
        use_capacity_bound(capacity_bound), target_edges(target),
        masks(output, std::ios::binary | std::ios::trunc) {}

  bool within_limits() {
    if (nodes >= 6'000'000'000ULL ||
        ((nodes & 0xffff) == 0 &&
         std::chrono::steady_clock::now() - start >= std::chrono::seconds(140))) {
      stopped = true;
      return false;
    }
    return true;
  }

  void visit(std::uint64_t remaining, std::uint64_t selected, int vertices,
             int edges, int capacity, std::uint64_t blocked) {
    if (!within_limits()) return;
    ++nodes;
    if (force_saturated_neighbors) {
      std::uint64_t before = remaining;
      remaining &= ~blocked;
      forced_exclusions += std::popcount(before) - std::popcount(remaining);
    }
    int remaining_count = std::popcount(remaining);
    int max_vertices = target_edges >= 25 ? 28 : 32;
    int max_additional = use_capacity_bound
        ? (capacity + 2 * remaining_count) / 2
        : 2 * remaining_count;
    if (edges > target_edges ||
        edges + max_additional < target_edges ||
        vertices > max_vertices || vertices + remaining_count < 27)
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
    if (can_include && early_cycle_check && new_degree == 2) {
      int y = std::countr_zero(adjacent_selected);
      std::uint64_t rest = adjacent_selected & (adjacent_selected - 1);
      int z = std::countr_zero(rest);
      if (dsu.find(y) == dsu.find(z)) {
        can_include = false;
        ++early_cycle_prunes;
      }
    }
    if (can_include) {
      std::uint64_t next_blocked = blocked;
      if (force_saturated_neighbors) {
        for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1) {
          int u = std::countr_zero(todo);
          if (degree[u] == 1) next_blocked |= neighbors[u];
        }
        if (new_degree == 2) next_blocked |= neighbors[next];
      }
      std::size_t dsu_mark = dsu.snapshot();
      if (early_cycle_check) {
        dsu.make_set(next);
        for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1)
          dsu.unite(next, std::countr_zero(todo));
      }
      for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1)
        ++degree[std::countr_zero(todo)];
      degree[next] = static_cast<std::uint8_t>(new_degree);
      visit(next_remaining, selected | (std::uint64_t{1} << next), vertices + 1,
            edges + new_degree, capacity + 2 - 2 * new_degree, next_blocked);
      degree[next] = 0;
      for (std::uint64_t todo = adjacent_selected; todo != 0; todo &= todo - 1)
        --degree[std::countr_zero(todo)];
      if (early_cycle_check) dsu.rollback(dsu_mark);
    }
    if (stopped) return;

    // Excluding the next vertex.
    visit(next_remaining, selected, vertices, edges, capacity, blocked);
  }

  void run() {
    for (int v = 0; v < 64; ++v)
      for (int bit = 0; bit < 6; ++bit)
        neighbors[v] |= std::uint64_t{1} << (v ^ (1 << bit));
    // Canonical degree-two pattern: origin 0 and neighbors 1 and 2.
    degree[0] = 2;
    degree[1] = degree[2] = 1;
    std::uint64_t blocked = 0;
    if (force_saturated_neighbors) blocked |= neighbors[0];
    if (early_cycle_check) {
      dsu.make_set(0);
      dsu.make_set(1);
      dsu.make_set(2);
      dsu.unite(0, 1);
      dsu.unite(0, 2);
    }
    visit(~std::uint64_t{0} & ~std::uint64_t{0b111}, 0b111, 3, 2, 2, blocked);
  }
};

int main(int argc, char **argv) {
  if (argc < 3) {
    std::cerr << "usage: enumerate_q6_heavy_layers <exact-edge-count 23..26> <mask-output> [--force-saturated] [--early-cycle] [--capacity-bound]\n";
    return 2;
  }
  int target = std::stoi(argv[1]);
  if (target < 23 || target > 26) return 2;
  bool force_saturated = false, early_cycle = false, capacity_bound = false;
  for (int i = 3; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--force-saturated") force_saturated = true;
    else if (arg == "--early-cycle") early_cycle = true;
    else if (arg == "--capacity-bound") capacity_bound = true;
    else return 2;
  }
  Search search(target, argv[2], force_saturated, early_cycle, capacity_bound);
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
            << " forced_exclusions=" << search.forced_exclusions
            << " early_cycle_prunes=" << search.early_cycle_prunes
            << " wall_seconds=" << seconds << '\n';
  return search.stopped ? 1 : 0;
}
