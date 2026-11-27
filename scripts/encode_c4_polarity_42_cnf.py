#!/usr/bin/env python3
"""Emit DIMACS for the 138-edge order-seven polarity deletion candidate."""

import argparse
from itertools import combinations, product


class Cnf:
    def __init__(self):
        self.variables = 0
        self.clauses = []
        self.true = self.variable()
        self.clauses.append((self.true,))

    def variable(self):
        self.variables += 1
        return self.variables

    def thresholds(self, inputs, limit):
        """Return literals for at least 0, 1, …, limit true inputs."""
        previous = [self.true] + [-self.true] * limit
        for x in inputs:
            current = [self.true]
            for threshold in range(1, limit + 1):
                at_least = self.variable()
                above, below = previous[threshold], previous[threshold - 1]
                # at_least iff above or (x and below).
                self.clauses.extend([
                    (-above, at_least),
                    (-x, -below, at_least),
                    (-at_least, above, x),
                    (-at_least, above, below),
                ])
                current.append(at_least)
            previous = current
        return previous

    def lex_at_least(self, left, right):
        """Require the left Boolean string to be lexicographically at least right."""
        prefix = self.true
        for x, y in zip(left, right, strict=True):
            if x == y:
                continue
            self.clauses.append((-prefix, x, -y))
            same = self.variable()
            self.clauses.extend([
                (-same, prefix),
                (-same, -x, y),
                (-same, x, -y),
                (-prefix, x, y, same),
                (-prefix, -x, -y, same),
            ])
            prefix = same

    def write(self):
        print(f"p cnf {self.variables} {len(self.clauses)}")
        for clause in self.clauses:
            print(*clause, 0)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True)) % 7


def orthogonal_permutations(points):
    units = [v for v in product(range(7), repeat=3) if dot(v, v) == 1]
    point_index = {v: i for i, v in enumerate(points)}
    permutations = set()
    for a in units:
        perpendicular = [v for v in units if dot(a, v) == 0]
        for b in perpendicular:
            for c in perpendicular:
                if dot(b, c) != 0:
                    continue
                image = []
                for x, y, z in points:
                    v = tuple((x * r + y * s + z * t) % 7
                              for r, s, t in zip(a, b, c, strict=True))
                    inverse = pow(next(q for q in v if q), -1, 7)
                    image.append(point_index[tuple(q * inverse % 7 for q in v)])
                permutations.add(tuple(image))
    return sorted(permutations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--symmetry", action="store_true",
                        help="keep lexicographically maximal polarity images")
    args = parser.parse_args()
    points = [(1, a, b) for a in range(7) for b in range(7)]
    points += [(0, 1, a) for a in range(7)] + [(0, 0, 1)]

    def orthogonal(i, j):
        return dot(points[i], points[j]) == 0

    n = len(points)
    cnf = Cnf()
    deleted = [cnf.variable() for _ in points]
    count = cnf.thresholds(deleted, 16)
    cnf.clauses.extend([(count[15],), (-count[16],)])
    score = [deleted[i] for i in range(n) if orthogonal(i, i)]
    assert len(score) == 8
    for i, j in combinations(range(n), 2):
        if orthogonal(i, j):
            x, y = deleted[i], deleted[j]
            edge = cnf.variable()
            cnf.clauses.extend([(-edge, x), (-edge, y), (edge, -x, -y)])
            score.append(edge)
    assert len(score) == 8 + 224
    cnf.clauses.append((cnf.thresholds(score, 34)[34],))

    for i in range(n):
        neighbors = [j for j in range(n) if j != i and orthogonal(i, j)]
        for excess in combinations(neighbors, len(neighbors) - 5):
            cnf.clauses.append((deleted[i], *(-deleted[j] for j in excess)))
    if args.symmetry:
        permutations = orthogonal_permutations(points)
        assert len(permutations) == 336
        for permutation in permutations:
            assert set(permutation) == set(range(n))
            assert all(orthogonal(i, j) == orthogonal(permutation[i], permutation[j])
                       for i in range(n) for j in range(i, n))
            cnf.lex_at_least(deleted, [deleted[i] for i in permutation])
    cnf.write()


if __name__ == "__main__":
    main()
