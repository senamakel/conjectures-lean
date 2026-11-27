#!/usr/bin/env python3
"""Emit DIMACS for the 138-edge order-seven polarity deletion candidate."""

from itertools import combinations


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

    def write(self):
        print(f"p cnf {self.variables} {len(self.clauses)}")
        for clause in self.clauses:
            print(*clause, 0)


def main():
    points = [(1, a, b) for a in range(7) for b in range(7)]
    points += [(0, 1, a) for a in range(7)] + [(0, 0, 1)]

    def orthogonal(i, j):
        return sum(a * b for a, b in zip(points[i], points[j])) % 7 == 0

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
    cnf.write()


if __name__ == "__main__":
    main()
