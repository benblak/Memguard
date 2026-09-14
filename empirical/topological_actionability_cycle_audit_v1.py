#!/usr/bin/env python3
from itertools import combinations


def sat_cycle_subset(n: int, chosen_edges: set[int], neg_edge: int = 0) -> bool:
    # Exact parity-consistency check by union-find with XOR potentials.
    parent = list(range(n))
    rank = [0] * n
    parity = [0] * n  # xor from node to parent

    def find(x):
        if parent[x] != x:
            p = parent[x]
            parent[x], up = find(parent[x])
            parity[x] ^= up
        return parent[x], parity[x]

    def union(a, b, w):
        # constraint x_a xor x_b = w ; w=0 positive, w=1 negative
        ra, pa = find(a)
        rb, pb = find(b)
        if ra == rb:
            return (pa ^ pb) == w
        if rank[ra] < rank[rb]:
            ra, rb = rb, ra
            pa, pb = pb, pa
        parent[rb] = ra
        parity[rb] = pa ^ pb ^ w
        if rank[ra] == rank[rb]:
            rank[ra] += 1
        return True

    for e in sorted(chosen_edges):
        a, b = e, (e + 1) % n
        w = 1 if e == neg_edge else 0
        if not union(a, b, w):
            return False
    return True


def exhaustive_depth(n: int) -> tuple[int, int, int]:
    edges = list(range(n))
    first_bad = None
    bad_count = 0
    checked = 0
    for r in range(n + 1):
        for comb in combinations(edges, r):
            checked += 1
            ok = sat_cycle_subset(n, set(comb))
            if not ok:
                bad_count += 1
                if first_bad is None:
                    first_bad = r
    return first_bad if first_bad is not None else -1, bad_count, checked


def theorem_check(n: int):
    full = set(range(n))
    assert not sat_cycle_subset(n, full)
    for e in range(n):
        assert sat_cycle_subset(n, full - {e})
    # Since every proper edge subset of a simple cycle is a forest,
    # checking all n maximal proper subsets suffices mathematically;
    # every smaller subset is contained in one of them and parity constraints
    # remain satisfiable under deletion.
    return n


def main():
    print('INSACERMO TOPOLOGICAL ACTIONABILITY CYCLE AUDIT V1')
    print('One negative edge, all other cycle edges positive.')
    print('Constraint semantics: positive = same bit, negative = opposite bit.')
    print()

    for n in [3, 4, 5, 7, 9, 12]:
        depth, bad, checked = exhaustive_depth(n)
        assert depth == n
        assert bad == 1
        print(f'n={n:2d} exhaustive_subsets={checked:5d} first_unsat_size={depth:2d} unsat_subsets={bad}')

    print()
    for n in [17, 31, 101, 1001]:
        depth = theorem_check(n)
        print(f'n={n:4d} theorem_check: full cycle UNSAT; every single-edge deletion SAT; kappa_top={depth}')

    print()
    print('VERDICT: EXACT_UNBOUNDED_TOPOLOGICAL_DEPTH')
    print('For every k choose n>k: every constraint family of size <=k is satisfiable, while the full n-cycle is not.')


if __name__ == '__main__':
    main()
