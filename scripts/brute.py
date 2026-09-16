"""Independent exhaustive check of Kurz's Conjecture 2 (convex hull area of polyhexes).

Usage: python3 brute.py N      (N = 12 takes about 8 minutes)

Cells are centres in axial coordinates (q, r). Neighbour steps: +-(1,0), +-(0,1), +-(1,-1).
In these coordinates one hexagon has area exactly 1, so plain coordinate area is the
normalised area. All coordinates are scaled by 3 to stay in integers.

The hull area is computed directly from all 6n hexagon corners, with no use of the
mixed-area formula from the proof. Polyhexes are enumerated with Redelmeier's algorithm;
the fixed counts match OEIS A001207.

Output per n: number of fixed polyhexes, maximum hull area, the claimed exact maximum
M(n) = ceil(n^2 + 14n/3)/6, Kurz's bound floor(n^2 + 14n/3 + 1)/6, and the number of
maximisers counted as fixed polyhexes and up to the 12 lattice symmetries.
"""
import sys
from fractions import Fraction
from math import ceil

NB = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]
HEX3 = [(1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]


def hull_area_x2(points):
    pts = sorted(set(points))
    if len(pts) < 3:
        return 0

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    h = lower[:-1] + upper[:-1]
    return abs(sum(h[i][0] * h[(i + 1) % len(h)][1] - h[(i + 1) % len(h)][0] * h[i][1]
                   for i in range(len(h))))


def area(cells):
    pts = [(3 * q + dx, 3 * r + dy) for (q, r) in cells for (dx, dy) in HEX3]
    return Fraction(hull_area_x2(pts), 18)


def M(n):
    return Fraction(ceil(Fraction(3 * n * n + 14 * n, 3)), 6)


def kurz(n):
    return Fraction((3 * n * n + 14 * n + 3) // 3, 6)


def rot(c):
    return (-c[1], c[0] + c[1])


def refl(c):
    return (c[1], c[0])


def canon_free(cells):
    best = None
    cur = list(cells)
    for _ in range(2):
        for _ in range(6):
            cur = [rot(c) for c in cur]
            mq = min(c[0] for c in cur)
            mr = min(c[1] for c in cur if c[0] == mq)
            key = tuple(sorted((c[0] - mq, c[1] - mr) for c in cur))
            if best is None or key < best:
                best = key
        cur = [refl(c) for c in cur]
    return best


def redelmeier(N, visit):
    def allowed(c):
        return c[1] > 0 or (c[1] == 0 and c[0] >= 0)

    poly = []

    def rec(untried, seen):
        while untried:
            c = untried.pop()
            poly.append(c)
            visit(poly)
            if len(poly) < N:
                new, newseen = [], set(seen)
                for d in NB:
                    nb = (c[0] + d[0], c[1] + d[1])
                    if allowed(nb) and nb not in newseen:
                        newseen.add(nb)
                        new.append(nb)
                rec(untried + new, newseen)
            poly.pop()

    rec([(0, 0)], {(0, 0)})


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    count = [0] * (N + 1)
    best = [Fraction(0)] * (N + 1)
    extremal = [[] for _ in range(N + 1)]
    violations = 0

    def visit(poly):
        nonlocal violations
        n = len(poly)
        count[n] += 1
        a = area(poly)
        if a > kurz(n):
            violations += 1
        if a > best[n]:
            best[n] = a
            extremal[n] = [tuple(poly)]
        elif a == best[n]:
            extremal[n].append(tuple(poly))

    redelmeier(N, visit)
    print("n  fixed  max_area  M(n)  kurz_bound  #fixed_max  #free_max")
    for n in range(1, N + 1):
        free = {canon_free(p) for p in extremal[n]}
        print(n, count[n], best[n], M(n), kurz(n), len(extremal[n]), len(free),
              "OK" if best[n] == M(n) else "MISMATCH")
    print("violations of Kurz bound:", violations)


if __name__ == "__main__":
    main()
