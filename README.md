# Polyhex-Hull: a Lean proof of Kurz's conjecture on polyhexes

This repository contains a Lean 4 proof, built on Mathlib, of Conjecture 2 in the paper *Convex hulls of polyominoes* by Sascha Kurz (Beiträge zur Algebra und Geometrie 49 (2008), [arXiv:math/0702786](https://arxiv.org/abs/math/0702786)). Kurz states the conjecture as follows.

> The area of the convex hull of any edge-to-edge connected system of n regular hexagons of unit area is at most ⌊n² + 14n/3 + 1⌋ / 6.

We prove the sharper bound ⌈n² + 14n/3⌉ / 6. The two bounds differ by 1/6 when 3 divides n, and they are equal for all other n. A path made of three straight runs of almost equal length reaches the sharper bound for every n. The accompanying paper proves this last fact. The Lean code covers only the upper bound.

## Main statements

```lean
theorem Polyhex.kurz_conjecture_sharp (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6)

theorem Polyhex.kurz_conjecture (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6)

theorem Polyhex.kurz_conjecture_euclid (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (euclid '' region S))
      ≤ ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6)
```

A cell is a point of `ℤ × ℤ` in axial coordinates. The statement `IsPolyhex S` says that `S` is nonempty and that `S` is connected in the graph where two cells are joined when they share an edge. The set `region S` is the union of the translates of `hexagon`, which is the convex hull of the six points `±(1/3, 1/3)`, `±(-1/3, 2/3)` and `±(2/3, -1/3)`. Area is Lebesgue measure on `ℝ × ℝ`.

The following results show that this model matches the words of the conjecture.

* `volume_hexagon` proves that `hexagon` has area 1.
* `euclid_det` proves that the map `euclid` from axial coordinates to Euclidean coordinates has determinant 1.
* `euclid_hexVertex_succ` proves that two neighbouring corners of a Euclidean cell differ by a rotation of sixty degrees about its centre. Every cell is therefore a regular hexagon.
* `volume_euclid_hexagon` proves that a Euclidean cell has area 1.

## Proof outline

Let `s = n - 1`, and let `a`, `b` and `c` count the edges of a spanning tree in the three lattice directions. The hull of the polyhex is the hull of the cell centres plus one hexagon. Its area is at most the area of the centre hull, plus 1, plus a third of the sum of three widths of the centre hull. Two estimates on the spanning tree bound the area and the widths, and a short integer inequality finishes the proof.

| File | What it proves |
| --- | --- |
| `Defs.lean` | This file defines cells, adjacency, the hexagon and polyhexes. |
| `Arith.lean` | This file proves the final integer inequality. |
| `Growth.lean` | This file orders the cells as a rooted spanning tree and proves that the three widths add up to at most `3s + max(a, b, c)`. |
| `Connect.lean` | This file proves that every polyhex has such an order. |
| `Slicing.lean` | This file uses Fubini's theorem to bound the area that a convex set gains when it is stretched along the horizontal axis. |
| `Transport.lean` | This file moves those bounds to every direction with a linear map of determinant 1. |
| `TreeArea.lean` | This file proves that the hull of the centres has area at most `(ab + bc + ca)/2`. |
| `Hexagon.lean` | This file writes the hexagon as a point plus three segments. |
| `Main.lean` | This file puts the pieces together and proves the main theorems. |
| `HexArea.lean` | This file proves that the hexagon has area 1. |
| `Euclidean.lean` | This file proves that the cells are regular and gives the Euclidean statement. |

## Building

```bash
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The last command prints the axioms that the main theorems use. The only axioms are `propext`, `Quot.sound` and `Classical.choice`, and the code contains no `sorry`.

## Computation

The script `scripts/brute.py` lists every polyhex with at most N cells. It computes the area of each hull exactly from the corners of the hexagons. For N = 12 it checks 8,182,213 fixed polyhexes. The largest area always equals ⌈n² + 14n/3⌉ / 6, and for each n only one shape reaches it, up to rotation and reflection.

```bash
python3 scripts/brute.py 12
```

## Credits

The informal proof first appeared on [Principia Math](https://principia-math.com) as the solution to problem MathDB 380445. Pragyaan Gaur wrote the formal proof and the computations.
