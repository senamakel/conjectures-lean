#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

// Deterministic DFS enumerator for normalized induced linear forests in Q6.
// Optional checkpointing stores a disjoint frontier of branch-decision paths.
// The defaults reproduce the original Q6 search parameters and output format.
struct Search {
  struct Decision { int vertex; bool include; };
  using Prefix = std::vector<Decision>;
  struct RollbackDsu {
    struct Change { int child; int root; int root_size; bool made_set; };
    std::array<int, 64> parent{};
    std::array<int, 64> size{};
    std::vector<Change> history;
    RollbackDsu() { parent.fill(-1); }
    int find(int x) const { while (parent[x] != x) x = parent[x]; return x; }
    std::size_t snapshot() const { return history.size(); }
    void make_set(int x) { history.push_back({x, -1, 0, true}); parent[x] = x; size[x] = 1; }
    void unite(int a, int b) {
      int ra = find(a), rb = find(b);
      if (ra == rb) return;
      if (size[ra] < size[rb]) std::swap(ra, rb);
      history.push_back({rb, ra, size[ra], false}); parent[rb] = ra; size[ra] += size[rb];
    }
    void rollback(std::size_t mark) {
      while (history.size() > mark) {
        Change c = history.back(); history.pop_back();
        if (c.made_set) { parent[c.child] = -1; size[c.child] = 0; }
        else { parent[c.child] = c.child; size[c.root] = c.root_size; }
      }
    }
  } dsu;

  std::array<std::uint8_t, 64> degree{};
  std::array<std::uint64_t, 64> neighbors{};
  int dimension, target_edges, minimum_vertices;
  std::uint64_t max_nodes;
  std::uint64_t nodes = 0, total_nodes = 0, labeled = 0, cyclic_leaves = 0;
  std::uint64_t forced_exclusions = 0, early_cycle_prunes = 0;
  bool stopped = false, fatal = false, force_saturated_neighbors, early_cycle_check, use_capacity_bound;
  std::ofstream masks;
  std::filesystem::path output_path, checkpoint_path;
  std::vector<Prefix> frontier;
  std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();

  Search(int target, const std::string &output, bool force_saturated,
         bool early_cycle, bool capacity_bound, int dim, int min_vertices,
         std::uint64_t node_cap, const std::string &checkpoint)
      : dimension(dim), target_edges(target), minimum_vertices(min_vertices),
        max_nodes(node_cap), force_saturated_neighbors(force_saturated),
        early_cycle_check(early_cycle), use_capacity_bound(capacity_bound),
        output_path(output), checkpoint_path(checkpoint) {
    for (int v = 0; v < (1 << dimension); ++v)
      for (int bit = 0; bit < dimension; ++bit)
        neighbors[v] |= std::uint64_t{1} << (v ^ (1 << bit));
    degree[0] = 2; degree[1] = degree[2] = 1;
  }

  bool limits_reached() {
    if (nodes >= max_nodes ||
        ((nodes & 0xffff) == 0 && std::chrono::steady_clock::now() - start >= std::chrono::seconds(140))) {
      stopped = true; return true;
    }
    return false;
  }

  void emit(std::uint64_t selected) {
    masks.write(reinterpret_cast<const char *>(&selected), sizeof(selected));
    if (!masks) { std::cerr << "failed writing mask output\n"; stopped = fatal = true; }
    else ++labeled;
  }

  int choose(std::uint64_t remaining, std::uint64_t selected) const {
    int next = -1, best = -1;
    for (std::uint64_t todo = remaining; todo; todo &= todo - 1) {
      int v = std::countr_zero(todo), score = std::popcount(neighbors[v] & selected);
      if (score > best) { next = v; best = score; }
    }
    return next;
  }

  void visit(std::uint64_t remaining, std::uint64_t selected, int vertices,
             int edges, int capacity, std::uint64_t blocked, Prefix &path,
             const Prefix *replay = nullptr, std::size_t replay_depth = 0) {
    if ((!replay || replay_depth == replay->size()) && limits_reached()) {
      frontier.push_back(path); return;
    }
    if (!replay || replay_depth >= replay->size()) {
      ++nodes; ++total_nodes;
    }
    if (force_saturated_neighbors) remaining &= ~blocked;
    int rem = std::popcount(remaining);
    int max_vertices = target_edges >= 25 ? 28 : 32;
    int max_additional = use_capacity_bound ? (capacity + 2 * rem) / 2 : 2 * rem;
    bool pruned = edges > target_edges || edges + max_additional < target_edges ||
        vertices > max_vertices || vertices + rem < minimum_vertices;
    if (pruned) {
      if (replay && replay_depth < replay->size()) {
        std::cerr << "checkpoint prefix continues beyond a pruned state\n";
        stopped = fatal = true;
      }
      return;
    }
    if (remaining == 0) {
      if (replay && replay_depth < replay->size()) {
        std::cerr << "checkpoint prefix continues beyond a terminal state\n";
        stopped = fatal = true;
        return;
      }
      if (edges != target_edges || vertices < minimum_vertices) return;
      bool seen[64]{}; int components = 0;
      for (int v = 0; v < (1 << dimension); ++v) {
        if (((selected >> v) & 1U) == 0 || seen[v]) continue;
        ++components; int stack[64], n = 0; stack[n++] = v; seen[v] = true;
        while (n) { int u = stack[--n]; std::uint64_t adj = neighbors[u] & selected;
          while (adj) { int w = std::countr_zero(adj); adj &= adj - 1;
            if (!seen[w]) { seen[w] = true; stack[n++] = w; }
          }
        }
      }
      int degree_sum = 0;
      for (int v = 0; v < (1 << dimension); ++v) if ((selected >> v) & 1U) degree_sum += degree[v];
      if (degree_sum != 2 * edges) { std::cerr << "degree invariant failure\n"; stopped = fatal = true; return; }
      if (edges != vertices - components) { ++cyclic_leaves; return; }
      emit(selected); return;
    }
    int next = choose(remaining, selected);
    if (next < 0) return;
    if (replay && replay_depth < replay->size()) {
      Decision d = (*replay)[replay_depth];
      if (d.vertex != next || !(remaining & (std::uint64_t{1} << next))) {
        std::cerr << "checkpoint prefix does not match traversal configuration\n"; stopped = fatal = true; return;
      }
      // Replay the saved choice without consuming this invocation's node cap.
      const std::uint64_t rest = remaining & ~(std::uint64_t{1} << next);
      std::uint64_t adj = neighbors[next] & selected;
      int nd = std::popcount(adj); bool can = nd <= 2;
      for (std::uint64_t t = adj; t; t &= t - 1) if (degree[std::countr_zero(t)] >= 2) can = false;
      if (d.include) {
        if (!can || (early_cycle_check && nd == 2 && dsu.find(std::countr_zero(adj)) ==
            dsu.find(std::countr_zero(adj & (adj - 1))))) { std::cerr << "invalid include prefix\n"; stopped = fatal = true; return; }
        auto mark = dsu.snapshot();
        if (early_cycle_check) { dsu.make_set(next); for (std::uint64_t t = adj; t; t &= t - 1) dsu.unite(next, std::countr_zero(t)); }
        for (std::uint64_t t = adj; t; t &= t - 1) ++degree[std::countr_zero(t)];
        degree[next] = static_cast<std::uint8_t>(nd);
        std::uint64_t nb = blocked;
        if (force_saturated_neighbors) {
          for (std::uint64_t t = adj; t; t &= t - 1) { int u = std::countr_zero(t); if (degree[u] == 2) nb |= neighbors[u]; }
          if (nd == 2) nb |= neighbors[next];
        }
        path.push_back(d); visit(rest, selected | (std::uint64_t{1} << next), vertices+1, edges+nd,
            capacity+2-2*nd, nb, path, replay, replay_depth+1); path.pop_back();
        degree[next] = 0; for (std::uint64_t t = adj; t; t &= t - 1) --degree[std::countr_zero(t)];
        if (early_cycle_check) dsu.rollback(mark);
      } else {
        path.push_back(d); visit(rest, selected, vertices, edges, capacity, blocked, path, replay, replay_depth+1); path.pop_back();
      }
      return;
    }
    // Once the checkpoint prefix is replayed, normal DFS is performed.
    const std::uint64_t rest = remaining & ~(std::uint64_t{1} << next);
    std::uint64_t adj = neighbors[next] & selected; int nd = std::popcount(adj);
    bool can = nd <= 2;
    for (std::uint64_t t = adj; t; t &= t - 1) if (degree[std::countr_zero(t)] >= 2) can = false;
    if (can && early_cycle_check && nd == 2 && dsu.find(std::countr_zero(adj)) == dsu.find(std::countr_zero(adj & (adj-1)))) { can = false; ++early_cycle_prunes; }
    if (can) {
      auto mark = dsu.snapshot(); if (early_cycle_check) { dsu.make_set(next); for (std::uint64_t t=adj;t;t&=t-1) dsu.unite(next,std::countr_zero(t)); }
      std::uint64_t nb=blocked; for (std::uint64_t t=adj;t;t&=t-1) { int u=std::countr_zero(t); ++degree[u]; if (force_saturated_neighbors && degree[u]==2) nb|=neighbors[u]; }
      degree[next]=static_cast<std::uint8_t>(nd); if (force_saturated_neighbors && nd==2) nb|=neighbors[next];
      path.push_back({next,true}); visit(rest,selected|(std::uint64_t{1}<<next),vertices+1,edges+nd,capacity+2-2*nd,nb,path); path.pop_back();
      degree[next]=0; for (std::uint64_t t=adj;t;t&=t-1) --degree[std::countr_zero(t)]; if (early_cycle_check) dsu.rollback(mark);
    }
    if (stopped) { Prefix sibling=path; sibling.push_back({next,false}); frontier.push_back(std::move(sibling)); return; }
    path.push_back({next,false}); visit(rest,selected,vertices,edges,capacity,blocked,path); path.pop_back();
  }

  void initialize_dsu() {
    if (early_cycle_check) { dsu.make_set(0); dsu.make_set(1); dsu.make_set(2); dsu.unite(0,1); dsu.unite(0,2); }
  }
  std::uint64_t initial_remaining() const {
    const std::uint64_t all = dimension == 6 ? ~std::uint64_t{0} : ((std::uint64_t{1} << (1 << dimension))-1);
    return all & ~std::uint64_t{0b111};
  }
  void save_checkpoint() {
    if (checkpoint_path.empty()) return;
    masks.flush(); auto offset = masks.tellp();
    if (!masks || offset < 0) { std::cerr << "failed flushing mask output for checkpoint\n"; fatal = true; return; }
    auto temp = checkpoint_path; temp += ".tmp";
    std::ofstream out(temp, std::ios::trunc);
    if (!out) { std::cerr << "failed opening checkpoint temporary\n"; fatal = true; return; }
    out << "SNAKECP1 " << dimension << ' ' << target_edges << ' ' << minimum_vertices << ' '
        << force_saturated_neighbors << ' ' << early_cycle_check << ' ' << use_capacity_bound << ' '
        << static_cast<std::uint64_t>(offset) << ' ' << total_nodes << ' ' << labeled << ' ' << cyclic_leaves << '\n';
    out << frontier.size() << '\n';
    for (const auto &p : frontier) { out << p.size(); for (auto d : p) out << ' ' << d.vertex << ' ' << d.include; out << '\n'; }
    out.flush();
    if (!out) { std::cerr << "failed writing checkpoint temporary\n"; fatal = true; return; }
    out.close();
    if (!out) { std::cerr << "failed closing checkpoint temporary\n"; fatal = true; return; }
    std::error_code ec; std::filesystem::rename(temp, checkpoint_path, ec);
    if (ec) { std::cerr << "failed replacing checkpoint: " << ec.message() << '\n'; fatal = true; }
  }
  bool load_checkpoint(std::uint64_t &offset) {
    std::ifstream in(checkpoint_path);
    std::string magic;
    int dim, target, minv, force, cycle, capacity;
    if (!(in >> magic >> dim >> target >> minv >> force >> cycle >> capacity >> offset
          >> total_nodes >> labeled >> cyclic_leaves)) return false;
    if (magic != "SNAKECP1" || dim != dimension || target != target_edges ||
        minv != minimum_vertices || force != force_saturated_neighbors ||
        cycle != early_cycle_check || capacity != use_capacity_bound) return false;

    std::size_t count;
    if (!(in >> count)) return false;
    frontier.clear();
    for (std::size_t i = 0; i < count; ++i) {
      std::size_t length;
      if (!(in >> length)) return false;
      Prefix prefix;
      for (std::size_t j = 0; j < length; ++j) {
        int vertex, include;
        if (!(in >> vertex >> include) || vertex < 0 || vertex >= (1 << dimension) ||
            (include != 0 && include != 1)) return false;
        prefix.push_back({vertex, include != 0});
      }
      frontier.push_back(std::move(prefix));
    }

    for (std::size_t i = 0; i < frontier.size(); ++i) {
      for (std::size_t j = 0; j < frontier.size(); ++j) {
        if (i == j || frontier[i].size() > frontier[j].size()) continue;
        bool is_prefix = true;
        for (std::size_t k = 0; k < frontier[i].size(); ++k) {
          if (frontier[i][k].vertex != frontier[j][k].vertex ||
              frontier[i][k].include != frontier[j][k].include) {
            is_prefix = false;
            break;
          }
        }
        if (is_prefix) return false;
      }
    }

    if (offset % sizeof(std::uint64_t) != 0 || labeled != offset / sizeof(std::uint64_t)) return false;
    std::error_code error;
    const auto output_size = std::filesystem::file_size(output_path, error);
    return !error && output_size >= offset;
  }
};

bool aliases(const std::filesystem::path &left, const std::filesystem::path &right) {
  std::error_code left_error;
  std::error_code right_error;
  const auto left_absolute = std::filesystem::absolute(left, left_error).lexically_normal();
  const auto right_absolute = std::filesystem::absolute(right, right_error).lexically_normal();
  if (!left_error && !right_error && left_absolute == right_absolute) return true;

  std::error_code equivalent_error;
  if (std::filesystem::equivalent(left, right, equivalent_error) && !equivalent_error) return true;

  left_error.clear();
  right_error.clear();
  const auto left_canonical = std::filesystem::weakly_canonical(left, left_error);
  const auto right_canonical = std::filesystem::weakly_canonical(right, right_error);
  return !left_error && !right_error && left_canonical == right_canonical;
}

int main(int argc, char **argv) {
  if (argc < 3) { std::cerr << "usage: enumerate_q6_heavy_layers <target-edges> <mask-output> [--force-saturated] [--early-cycle] [--capacity-bound] [--dimension N] [--min-vertices N] [--node-cap N] [--checkpoint FILE] [--resume]\n"; return 2; }
  int target=std::stoi(argv[1]), dimension=6, minv=27; std::uint64_t cap=6'000'000'000ULL;
  bool force=false, cycle=false, capacity=false, resume=false; std::string checkpoint;
  for (int i=3;i<argc;++i) { std::string a=argv[i];
    if (a=="--force-saturated") force=true; else if(a=="--early-cycle") cycle=true; else if(a=="--capacity-bound") capacity=true;
    else if(a=="--resume") resume=true;
    else if((a=="--dimension"||a=="--min-vertices"||a=="--node-cap"||a=="--checkpoint")&&i+1<argc) {
      std::string v=argv[++i]; if(a=="--dimension") dimension=std::stoi(v); else if(a=="--min-vertices") minv=std::stoi(v); else if(a=="--node-cap") cap=std::stoull(v); else checkpoint=v;
    } else return 2;
  }
  if (dimension < 2 || dimension > 6 || target < 0 || minv < 3 || cap == 0 ||
      (resume && checkpoint.empty())) return 2;
  if (!checkpoint.empty()) {
    const std::filesystem::path output_path(argv[2]);
    const std::filesystem::path checkpoint_path(checkpoint);
    const std::filesystem::path temporary_path(checkpoint + ".tmp");
    if (aliases(output_path, checkpoint_path) || aliases(output_path, temporary_path)) {
      std::cerr << "mask output aliases checkpoint or checkpoint temporary\n";
      return 2;
    }
  }
  Search s(target,argv[2],force,cycle,capacity,dimension,minv,cap,checkpoint);
  std::uint64_t offset=0;
  if(resume) {
    if(!s.load_checkpoint(offset)) { std::cerr<<"invalid or incompatible checkpoint\n"; return 2; }
    std::error_code ec; std::filesystem::resize_file(argv[2],offset,ec);
    if(ec) { std::cerr<<"failed truncating output to checkpoint offset: "<<ec.message()<<'\n'; return 2; }
    s.masks.open(argv[2],std::ios::binary|std::ios::app);
  } else {
    s.masks.open(argv[2],std::ios::binary|std::ios::trunc);
    if(!checkpoint.empty()) s.frontier.push_back({});
  }
  if(!s.masks) { std::cerr<<"could not open mask output\n"; return 2; }
  s.initialize_dsu();
  std::vector<Search::Prefix> tasks=std::move(s.frontier); s.frontier.clear();
  if(tasks.empty()&&!resume) tasks.push_back({});
  for(std::size_t i=0;i<tasks.size();++i) {
    s.stopped=false; Search::Prefix path;
    s.visit(s.initial_remaining(),0b111,3,2,2,force?(s.neighbors[0]):0,path,&tasks[i],0);
    if(s.stopped) { for(std::size_t j=i+1;j<tasks.size();++j) s.frontier.push_back(tasks[j]); break; }
  }
  if (!s.fatal) s.save_checkpoint();
  s.masks.flush();
  if (!s.masks) { std::cerr<<"failed flushing mask output\n"; s.fatal=true; }
  s.masks.close();
  if (s.fatal) return 2;
  auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-s.start).count();
  std::cout<<(s.frontier.empty()?"COMPLETE":"STOPPED")<<" target_edges="<<target<<" nodes="<<s.nodes
    <<" total_nodes="<<s.total_nodes<<" labeled="<<s.labeled<<" cyclic_leaves="<<s.cyclic_leaves
    <<" frontier="<<s.frontier.size()<<" wall_seconds="<<sec<<'\n';
  return s.frontier.empty()?0:1;
}
