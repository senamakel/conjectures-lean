#!/usr/bin/env python3
"""Independent arithmetic check of the compact 42-vertex edge counter."""


def main() -> None:
    # For each allowed non-root degree, the number of excess incidences above
    # six is the sum of the two threshold flags used by the CNF.
    for degree in (6, 7, 8):
        flags = int(degree >= 7) + int(degree >= 8)
        assert degree - 6 == flags

    # Exhaust all degree multiplicity triples on 41 non-root vertices. The
    # root has fixed degree six. Verify that 2e=276 exactly when the compact
    # counter has 24 true flags, under the degree window 6..8.
    profiles = 0
    extremal_profiles = []
    for n8 in range(42):
        for n7 in range(42 - n8):
            n6 = 41 - n7 - n8
            degree_sum = 6 + 6 * n6 + 7 * n7 + 8 * n8
            flag_sum = n7 + 2 * n8
            assert (degree_sum == 276) == (flag_sum == 24)
            profiles += 1
            if flag_sum == 24 and n8 <= 4:
                extremal_profiles.append((n6, n7, n8))

    expected = [(17 + k, 24 - 2 * k, k) for k in range(5)]
    assert extremal_profiles == expected
    assert all(sum(p) == 41 for p in extremal_profiles)
    assert all(6 * p[0] + 7 * p[1] + 8 * p[2] + 6 == 276
               for p in extremal_profiles)
    assert all(p[1] + 2 * p[2] == 24 for p in extremal_profiles)

    print(f"checked {profiles} degree profiles; handshake iff 24 flags")
    print(f"with degree-eight cap 4, profiles: {extremal_profiles}")


if __name__ == "__main__":
    main()
