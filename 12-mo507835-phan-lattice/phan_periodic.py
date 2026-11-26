#!/usr/bin/python3
"""Search C4-free periodic patterns in Phan's three-layer lattice."""

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import exp, sqrt
from random import Random
from time import perf_counter


def periodic_problem(n, period):
    """Return edge count and the list of all distinct cycle constraints."""
    if n < 2 or period < 3:
        raise ValueError("Require n >= 2 and period >= 3")
    sites = tuple(product(range(period), repeat=n - 1))
    site_id = {site: i for i, site in enumerate(sites)}
    pairs = tuple(combinations(range(n), 2))
    half = n * len(sites)
    cycles = []
    for a_id, a in enumerate(sites):
        for i, j in pairs:
            b = tuple((v + (k == i) + (k == j)) % period for k, v in enumerate(a))
            minus = n * a_id
            plus = half + n * site_id[b]
            cycles.append((minus + i, minus + j, plus + i, plus + j))
    return 2 * half, cycles


def verify_graph(n, period, kept):
    """Independent check by enumerating neighbor pairs in the quotient graph."""
    sites = tuple(product(range(period), repeat=n - 1))
    half = n * len(sites)
    common = set()
    for side in range(2):
        sign = 1 if side == 0 else -1
        for a_id, a in enumerate(sites):
            base = side * half + n * a_id
            neighbors = [
                tuple((v + sign * (k == i)) % period for k, v in enumerate(a))
                for i in range(n) if kept[base + i]
            ]
            for pair in combinations(sorted(neighbors), 2):
                if pair in common:
                    raise RuntimeError(f"Unexpected 4-cycle through middle sites {pair}")
                common.add(pair)


def parity_pattern(period):
    """An exact density-3/4 construction in dimension four for even periods."""
    states = [True] * (8 * period ** 3)
    labels = (1, 2, 3, 0)
    for index, site in enumerate(product(range(period), repeat=3)):
        label = 0
        for coordinate, image in zip(site, (2, 3, 1)):
            if coordinate % 2:
                label ^= image
        direction = labels.index(label)
        states[4 * index + direction] = False
        states[4 * period ** 3 + 4 * index + direction] = False
    return states


def search(n, period, steps, restarts, seed):
    edge_count, cycles = periodic_problem(n, period)
    adjacent = defaultdict(list)
    for cycle in cycles:
        for edge in cycle:
            adjacent[edge].append(tuple(e for e in cycle if e != edge))
    # Incidence counting requires at least ceil(number_of_cycles / (n-1)) deletions.
    upper = edge_count - (len(cycles) + n - 2) // (n - 1)
    if n == 4 and period % 2 == 0:
        best = parity_pattern(period)
        verify_graph(n, period, best)
        kept_count = sum(best)
        if kept_count != upper or any(all(best[e] for e in cycle) for cycle in cycles):
            raise RuntimeError("Invalid parity construction")
        return kept_count, edge_count, upper

    rng = Random(seed)
    best = None
    best_count = 0
    edge_order = list(range(edge_count))
    for _ in range(restarts):
        rng.shuffle(edge_order)
        kept = [False] * edge_count
        for edge in edge_order:
            kept[edge] = not any(all(kept[e] for e in other) for other in adjacent[edge])
        count = sum(kept)
        for step in range(steps + 1):
            if count > best_count:
                best, best_count = kept.copy(), count
                if best_count == upper:
                    break
            if step == steps:
                break
            edge = rng.randrange(edge_count)
            if kept[edge]:
                continue
            removed = set()
            for other in adjacent[edge]:
                if all(kept[e] and e not in removed for e in other):
                    removed.add(rng.choice(other))
            delta = 1 - len(removed)
            temperature = 0.12 + 0.73 * (steps - step) / steps
            if delta >= 0 or rng.random() < exp(delta / temperature):
                kept[edge] = True
                for e in removed:
                    kept[e] = False
                count += delta
        if best_count == upper:
            break
    if best_count != sum(best) or any(all(best[e] for e in cycle) for cycle in cycles):
        raise RuntimeError("Invalid cycle witness")
    verify_graph(n, period, best)
    return best_count, edge_count, upper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[2, 3, 4])
    parser.add_argument("--periods", type=int, nargs="+", default=[3, 4, 5, 6])
    parser.add_argument("--steps", type=int, default=12000)
    parser.add_argument("--restarts", type=int, default=5)
    parser.add_argument("--seed", type=int, default=507835)
    args = parser.parse_args()
    if args.steps < 0 or args.restarts < 1:
        parser.error("Require nonnegative steps and at least one restart")
    started = perf_counter()
    print(" n period   kept/edges  density  counting_upper  conjectured  optimal")
    for n in args.dimensions:
        for period in args.periods:
            best, edges, upper = search(n, period, args.steps, args.restarts, args.seed)
            threshold = (1 + 1 / sqrt(n)) / 2
            ratio = Fraction(best, edges)
            print(f"{n:2} {period:6} {best:5}/{edges:<5} {float(ratio):.6f} "
                  f"{upper/edges:15.6f} {threshold:12.6f} {best == upper}")
    print(f"Elapsed: {perf_counter()-started:.3f}s")


if __name__ == "__main__":
    main()
