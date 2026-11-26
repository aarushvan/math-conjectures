"""Exhaustive checks for the top-to-bottom {132, 213} stack sort."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial


FORBIDDEN = {(1, 3, 2), (2, 1, 3)}


def avoids(word, forbidden=FORBIDDEN):
    for triple in combinations(word, 3):
        x, y, z = triple
        ranks = (1 + (y < x) + (z < x), 1 + (x < y) + (z < y),
                 1 + (x < z) + (y < z))
        if ranks in forbidden:
            return False
    return True


def literal(word, forbidden=FORBIDDEN):
    """Test the entire candidate stack, including triples below the new top."""
    stack = []
    output = []
    for x in word:
        while not avoids((x,) + tuple(reversed(stack)), forbidden):
            output.append(stack.pop())
        stack.append(x)
    return tuple(output + stack[::-1])


def pair_allows(x, stack):
    """Here stack is in top-to-bottom order."""
    return all(not (x < b < a or a < x < b) for a, b in combinations(stack, 2))


def classical(word):
    stack = []
    out = []
    for x in word:
        while stack and stack[-1] < x:
            out.append(stack.pop())
        stack.append(x)
    return tuple(out + stack[::-1])


def decomposed(word):
    if not word:
        return ()
    pivot = word[0]
    low_stack = [pivot]
    gap = []
    out = []
    for x in word[1:]:
        if x > pivot:
            gap.append(x)
            continue
        out.extend(decomposed(gap))
        gap = []
        while low_stack[-1] < x:
            out.append(low_stack.pop())
        low_stack.append(x)
    out.extend(decomposed(gap))
    return tuple(out + low_stack[::-1])


def before(word, e):
    return set(word[:word.index(e)])


def weight(values, n):
    return sum(1 << (n - x) for x in values)


def trace(start, transition):
    """Return the transient length and the cycle in a finite function graph."""
    seen = {}
    path = []
    state = start
    while state not in seen:
        seen[state] = len(path)
        path.append(state)
        state = transition[state]
    split = seen[state]
    return split, tuple(path[split:])


@lru_cache(None)
def classical_images(size):
    """All standardized outputs of West's map, encoded with one byte per letter."""
    if size == 0:
        return {b""}
    largest = bytes([size])
    smaller = bytes(range(1, size))
    outputs = set()
    for left_size in range(size):
        for left in combinations(smaller, left_size):
            right = bytes(x for x in smaller if x not in left)
            left_table = bytes.maketrans(bytes(range(1, left_size + 1)), bytes(left))
            right_table = bytes.maketrans(bytes(range(1, len(right) + 1)), right)
            suffixes = [word.translate(right_table) + largest
                        for word in classical_images(len(right))]
            for word in classical_images(left_size):
                prefix = word.translate(left_table)
                outputs.update(prefix + suffix for suffix in suffixes)
    return outputs


def verify_reduction(n):
    """Verify the entire cycle classification using only states after n starts."""
    images = classical_images(n - 1)
    identity = tuple(range(1, n + 1))
    certified = {bytes(identity[:-1])}
    for image in images:
        if image in certified:
            continue
        state = tuple(image) + (n,)
        path = set()
        marks = []
        while True:
            if state[-1] == n:
                mark = bytes(state[:-1])
                assert mark in images, state
                if mark in certified:
                    break
                marks.append(mark)
            assert state not in path, ("nonmonotone cycle", state)
            path.add(state)
            state = decomposed(state)
        certified.update(marks)
    assert certified == images
    print("n={}  distinct outputs after an n-start={}  all reach identity".format(
        n, len(certified)), flush=True)


def verify(n):
    identity = tuple(range(1, n + 1))
    reverse = identity[::-1]
    target = {identity, reverse}
    graph = {p: literal(p) for p in permutations(identity)}

    # Every legal stack and proposed new top up to this size, up to relabeling.
    for candidate in graph:
        x, stack = candidate[0], candidate[1:]
        if avoids(stack):
            assert pair_allows(x, stack) == avoids(candidate), candidate

    assert classical_images(n) == {bytes(classical(p)) for p in graph}
    returns = {}
    all_cycles = set()
    longest = 0
    for p, q in graph.items():
        assert q == decomposed(p), (p, q)
        complement_p = tuple(n + 1 - x for x in p)
        complement_q = tuple(n + 1 - x for x in q)
        assert literal(complement_p, {(3, 1, 2), (2, 3, 1)}) == complement_q, p
        assert q[-1] == p[0], (p, q)
        assert (q == identity) == (p[0] == n and avoids(p[1:], {(2, 3, 1)})), p
        assert (graph[q] == p) == (p in target), p
        if q[0] == p[-1]:
            assert q == p[::-1] and avoids(q), p
        if p in target:
            assert q == p[::-1], p
        for extreme in {1, n}:
            initial = before(p, extreme)
            final = before(q, extreme)
            if p[0] != extreme:
                assert p[0] in initial - final, p
                assert all(y > p[0] for y in final - initial), p
                assert weight(final, n) < weight(initial, n), p
            state = p
            steps = 0
            while state[0] != extreme:
                state = graph[state]
                steps += 1
                assert steps <= weight(initial, n), p
        if p[0] == n:
            assert q == classical(p[1:]) + (n,), p
            if n >= 2:
                assert q[-2:] == (n - 1, n), p
                second = graph[q]
                assert second.index(n - 1) == second.index(n) + 1, p
                third = graph[second]
                assert third.index(n - 1) < third.index(n), p
            state = q
            while state[0] != n:
                state = graph[state]
            returns[p[1:]] = state[1:]
        distance, cycle = trace(p, graph)
        longest = max(longest, distance)
        all_cycles.add(frozenset(cycle))

    assert len(returns) == factorial(n - 1)
    projected = set()
    for cycle in all_cycles:
        heads = {p[0] for p in cycle}
        assert {1, n} <= heads
        assert len(heads) >= 3 or cycle == target
        marked = frozenset(p[1:] for p in cycle if p[0] == n)
        assert marked and marked not in projected
        projected.add(marked)
    induced = {frozenset(trace(p, returns)[1]) for p in returns}
    assert projected == induced
    assert induced == {frozenset({reverse[1:]})}
    assert all_cycles == {frozenset(target)}
    print("n={}  permutations={}  period={}  maximum transient={}".format(
        n, len(graph), len(target), longest))
    if n == 7:
        witness = (5, 2, 3, 6, 7, 4, 1)
        distance, cycle = trace(witness, graph)
        assert distance == 12 and cycle[0] == identity
    return longest


if __name__ == "__main__":
    assert __debug__, "Run without -O to enable the checks"
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through-12", action="store_true",
                        help="also exhaust the reduced state spaces for sizes 8 to 12")
    options = parser.parse_args()
    maxima = [verify(n) for n in range(1, 8)]
    assert maxima == [0, 0, 3, 4, 7, 7, 12]
    if options.through_12:
        for size in range(8, 13):
            verify_reduction(size)
