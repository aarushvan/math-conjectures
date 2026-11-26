#!/usr/bin/python3
"""Verify Stanley's bivariate monomial positivity with exact integer coefficients."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import accumulate, combinations
from math import factorial, prod
from time import perf_counter


def partitions(total, cap=None):
    if total == 0:
        yield ()
        return
    for part in range(min(total, cap or total), 0, -1):
        for tail in partitions(total - part, part):
            yield (part,) + tail


def dominates(left, right):
    left_sums = tuple(accumulate(left))
    return len(left) <= len(right) and all(
        a >= b for a, b in zip(left_sums, accumulate(right))
    )


def conjugate(shape):
    return tuple(sum(part >= i for part in shape) for i in range(1, shape[0] + 1))


@lru_cache(maxsize=None)
def margin_count(rows, columns):
    """Count binary matrices with ordered row and column sums."""
    if not rows:
        return int(not columns)
    if len(columns) < rows[0] or (columns and columns[0] > len(rows)):
        return 0
    total = 0
    for chosen in combinations(range(len(columns)), rows[0]):
        residual = list(columns)
        for j in chosen:
            residual[j] -= 1
        total += margin_count(rows[1:], tuple(sorted(filter(None, residual), reverse=True)))
    return total


def explicit_coefficient(shape, elementary):
    """Independent small-degree oracle using direct products of squarefree monomials."""
    variables = len(shape)
    states = Counter({(0,) * variables: 1})
    for part in elementary:
        terms = tuple(combinations(range(variables), part))
        result = Counter()
        for exponents, coefficient in states.items():
            for term in terms:
                updated = list(exponents)
                for j in term:
                    updated[j] += 1
                if all(a <= b for a, b in zip(updated, shape)):
                    result[tuple(updated)] += coefficient
        states = result
    return states[shape]


def basis_change(shapes):
    elementary = [conjugate(shape) for shape in shapes]
    columns = [
        {i: count for i, mu in enumerate(shapes) if (count := margin_count(mu, nu))}
        for nu in elementary
    ]
    inverse = []
    for i, column in enumerate(columns):
        if column.get(i) != 1 or any(j < i for j in column):
            raise RuntimeError("Expected unit triangular elementary-to-monomial matrix")
    for target in range(len(shapes)):
        residual = {target: 1}
        expansion = {}
        for j in range(target, len(shapes)):
            coefficient = residual.get(j, 0)
            if coefficient:
                expansion[j] = coefficient
                for row, count in columns[j].items():
                    residual[row] = residual.get(row, 0) - coefficient * count
        if any(residual.values()):
            raise RuntimeError(f"Monomial basis reconstruction failed for {shapes[target]}")
        inverse.append(expansion)
    return elementary, columns, inverse


def verify(degree):
    shapes = list(partitions(degree))
    elementary, columns, inverse = basis_change(shapes)
    if degree <= 5:
        for nu, column in zip(elementary, columns):
            for i, shape in enumerate(shapes):
                if column.get(i, 0) != explicit_coefficient(shape, nu):
                    raise RuntimeError(f"Direct expansion disagrees for {shape}, {nu}")

    histogram = Counter()
    length_zeros = dominance_zeros = 0
    first_extra_zero = None
    twos = []
    dominance = [[dominates(lam, alpha) for alpha in shapes] for lam in shapes]
    minimum_examples = []
    minimum_positive = None
    for i, (lam, expansion) in enumerate(zip(shapes, inverse)):
        coefficients = Counter()
        for j, factor in expansion.items():
            for a, left in columns[j].items():
                for b, right in columns[j].items():
                    coefficients[a, b] += factor * left * right

        for a, alpha in enumerate(shapes):
            for b, beta in enumerate(shapes):
                value = coefficients[a, b]
                if value < 0:
                    raise RuntimeError(f"Negative coefficient {value}: {lam}, {alpha}, {beta}")
                histogram[value] += 1
                if len(lam) > min(len(alpha), len(beta)):
                    length_zeros += 1
                if not (dominance[i][a] and dominance[i][b]):
                    dominance_zeros += 1
                    if value:
                        raise RuntimeError("Dominance-based vanishing failed")
                elif value == 0 and first_extra_zero is None:
                    first_extra_zero = lam, alpha, beta
                if a == i and value != columns[i].get(b, 0):
                    raise RuntimeError("Principal monomial slice failed")
                if value == 2 and a <= b and len(twos) < 3:
                    twos.append((lam, alpha, beta))
                if a == 0:
                    expected = (factorial(degree) // prod(map(factorial, beta))) if len(lam) == 1 else 0
                    if value != expected:
                        raise RuntimeError("One-variable specialization failed")
                if value > 0:
                    if minimum_positive is None or value < minimum_positive:
                        minimum_positive = value
                        minimum_examples = []
                    if value == minimum_positive and len(minimum_examples) < 4:
                        minimum_examples.append((lam, alpha, beta))

    total = sum(histogram.values())
    print(f"d={degree} partitions={len(shapes)} tested={total} zeros={histogram[0]} "
          f"length_zeros={length_zeros} dominance_zeros={dominance_zeros} positives={total-histogram[0]} "
          f"min_positive={minimum_positive} at_min={histogram[minimum_positive]} "
          f"at_2={histogram[2]}")
    print(f"  (lambda, alpha, beta) at min_positive: {minimum_examples}")
    print(f"  examples at 2: {twos}; first zero within dominance: {first_extra_zero}")
    if histogram[1] == len(shapes):
        print("  Coefficient 1 occurs only on the joint diagonal.")
    return total, histogram[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=8)
    args = parser.parse_args()
    if args.degree < 1:
        parser.error("--degree must be positive")
    started = perf_counter()
    total, zeros = 1, 0
    print("d=0: Phi(1)=1")
    for degree in range(1, args.degree + 1):
        count, zero_count = verify(degree)
        total += count
        zeros += zero_count
    print(f"Total: {total} ordered coefficient classes, {zeros} zeros, "
          f"{total-zeros} positives, 0 negatives, {perf_counter()-started:.3f}s.")


if __name__ == "__main__":
    main()
