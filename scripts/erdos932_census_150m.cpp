#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

int main(int argc, char** argv) {
  if (argc != 3) {
    std::cerr << "usage: erdos932_census_150m OEIS_BFILE EXTENSION_TSV\n";
    return 2;
  }
  constexpr std::uint32_t endpoint = 150'000'000;
  constexpr std::uint32_t sieve_endpoint = 150'100'000;
  constexpr std::uint32_t published_last_r = 6'386'830;
  constexpr std::uint32_t published_last_prime = 111'551'057;
  const auto wall_start = std::chrono::steady_clock::now();

  // Read the complete 10,000-term A387864 b-file as (offset, term) pairs.
  std::ifstream input(argv[1]);
  if (!input) {
    std::cerr << "cannot open OEIS b-file: " << argv[1] << "\n";
    return 2;
  }
  std::vector<std::uint32_t> expected;
  std::uint32_t offset, value;
  while (input >> offset >> value) {
    if (offset != expected.size() + 1) {
      std::cerr << "nonconsecutive OEIS b-file offset at " << offset << "\n";
      return 2;
    }
    expected.push_back(value);
  }
  if (expected.size() != 10'000 || expected.back() != published_last_r) {
    std::cerr << "unexpected OEIS prefix length or endpoint\n";
    return 2;
  }

  // Byte-array Eratosthenes sieve. The extra 100,000 covers the next prime
  // after the largest left endpoint, and is not used as a smoothness cutoff.
  std::vector<std::uint8_t> is_prime(sieve_endpoint + 1, 1);
  is_prime[0] = is_prime[1] = 0;
  for (std::uint32_t p = 2; std::uint64_t(p) * p <= sieve_endpoint; ++p) {
    if (!is_prime[p]) continue;
    for (std::uint64_t m = std::uint64_t(p) * p; m <= sieve_endpoint; m += p)
      is_prime[static_cast<std::size_t>(m)] = 0;
  }
  std::vector<std::uint32_t> primes;
  for (std::uint32_t n = 2; n <= sieve_endpoint; ++n)
    if (is_prime[n]) primes.push_back(n);
  const std::size_t left_count = static_cast<std::size_t>(
      std::upper_bound(primes.begin(), primes.end(), endpoint) - primes.begin());
  if (left_count >= primes.size()) {
    std::cerr << "sieve did not contain the next prime after endpoint\n";
    return 2;
  }
  if (primes[published_last_r - 1] != published_last_prime) {
    std::cerr << "OEIS endpoint prime does not match generated prime list\n";
    return 2;
  }

  // The maximum gap is computed from the actual scanned range. Iterating this
  // list and breaking at ell >= gap enforces the strict threshold exactly.
  std::uint32_t max_gap = 0;
  for (std::size_t i = 0; i < left_count; ++i)
    max_gap = std::max(max_gap, primes[i + 1] - primes[i]);
  std::vector<std::uint32_t> small_primes;
  for (auto p : primes) {
    if (p >= max_gap) break;
    small_primes.push_back(p);
  }

  std::vector<std::uint32_t> all_hits;
  std::vector<std::string> extension_rows;
  std::size_t terms = 0;
  std::size_t extension_terms = 0;
  std::uint32_t last_term_r = 0, last_term_p = 0, last_term_q = 0, last_gap = 0;
  std::uint32_t last_n1 = 0, last_n2 = 0;

  for (std::size_t i = 0; i < left_count; ++i) {
    const std::uint32_t p = primes[i];
    const std::uint32_t q = primes[i + 1];
    const std::uint32_t gap = q - p;
    std::uint32_t n1 = 0, n2 = 0;
    unsigned count = 0;
    for (std::uint32_t m = p + 1; m < q; ++m) {
      std::uint32_t residual = m;
      for (auto ell : small_primes) {
        if (ell >= gap) break;
        while (residual % ell == 0) residual /= ell;
        if (residual == 1) break;
      }
      if (residual == 1) {
        if (count++ == 0) n1 = m;
        else { n2 = m; break; }
      }
    }
    if (count < 2) continue;
    const std::uint32_t r = static_cast<std::uint32_t>(i + 1);
    all_hits.push_back(r);
    ++terms;
    last_term_r = r; last_term_p = p; last_term_q = q; last_gap = gap;
    last_n1 = n1; last_n2 = n2;
    if (r > published_last_r) {
      ++extension_terms;
      extension_rows.push_back(std::to_string(r) + "\t" + std::to_string(p) +
                               "\t" + std::to_string(q) + "\t" +
                               std::to_string(gap) + "\t" + std::to_string(n1) +
                               "\t" + std::to_string(n2));
    }
  }

  if (all_hits.size() < expected.size() ||
      !std::equal(expected.begin(), expected.end(), all_hits.begin())) {
    std::cerr << "computed sequence disagrees with OEIS A387864 prefix\n";
    return 1;
  }
  if (terms != expected.size() + extension_terms) {
    std::cerr << "term-count consistency check failed\n";
    return 1;
  }
  std::ofstream out(argv[2]);
  if (!out) {
    std::cerr << "cannot open output table: " << argv[2] << "\n";
    return 2;
  }
  out << "r\tp_r\tp_next\tgap\tn1\tn2\n";
  for (const auto& row : extension_rows) out << row << "\n";
  out.close();

  const auto wall_seconds = std::chrono::duration<double>(
      std::chrono::steady_clock::now() - wall_start).count();
  std::cout << "oeis_prefix_terms_verified=" << expected.size() << "\n"
            << "oeis_last_r=" << expected.back() << "\n"
            << "oeis_last_prime=" << primes[published_last_r - 1] << "\n"
            << "prime_gaps_scanned=" << left_count << "\n"
            << "left_prime_endpoint=" << endpoint << "\n"
            << "max_gap_in_range=" << max_gap << "\n"
            << "qualifying_gaps_total=" << terms << "\n"
            << "new_terms=" << extension_terms << "\n"
            << "last_new_r=" << last_term_r << "\n"
            << "last_new_gap=" << last_term_p << " " << last_term_q
            << " gap=" << last_gap << "\n"
            << "last_new_hits=" << last_n1 << " " << last_n2 << "\n"
            << "wall_seconds=" << wall_seconds << "\n";
  return 0;
}
