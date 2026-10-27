# Polyhex-Hull: a Lean proof of Kurz's conjecture on polyhexes

This repository contains a Lean 4 proof, built on Mathlib, of Conjecture 2 in the paper *Convex hulls of polyominoes* by Sascha Kurz (Beiträge zur Algebra und Geometrie 49 (2008), [arXiv:math/0702786](https://arxiv.org/abs/math/0702786)). Kurz states the conjecture as follows.

> The area of the convex hull of any edge-to-edge connected system of n regular hexagons of unit area is at most ⌊n² + 14n/3 + 1⌋ / 6.

We prove the sharper bound ⌈n² + 14n/3⌉ / 6. The two bounds differ by 1/6 when 3 divides n, and they are equal for all other n. A path made of three straight runs of almost equal length reaches the sharper bound for every n. The accompanying paper proves this last fact. The Lean code covers only the upper bound.

## Paper

The accompanying preprint is *The maximum area of the convex hull of a polyhex*, [arXiv:2609.30310](https://arxiv.org/abs/2609.30310). It proves both the upper bound and the matching construction. The maximum areas, scaled by six, are sequence [A399934](https://oeis.org/A399934) in the OEIS.

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
| `Statement.lean` | This file repeats the definitions of `Challenge.lean`. |
| `Bridge.lean` | This file transfers the main theorems to the regular hexagonal tiling of `Challenge.lean`. |

## Building

```bash
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The project uses Lean `v4.35.0` and the Mathlib tag `v4.35.0`, and every Lean file uses the module system. The paper describes the earlier build on Lean `v4.35.0-rc1`, and apart from the module headers the proofs did not change in the upgrade. The last command prints the axioms that the main theorems use. The only axioms are `propext`, `Quot.sound` and `Classical.choice`, and the code contains no `sorry`.

## Computation

The script `scripts/brute.py` lists every polyhex with at most N cells. It computes the area of each hull exactly from the corners of the hexagons. For N = 12 it checks 8,182,213 fixed polyhexes. The largest area always equals ⌈n² + 14n/3⌉ / 6, and for each n only one shape reaches it, up to rotation and reflection.

```bash
python3 scripts/brute.py 12
```

## Palomar files

The repository is laid out for the [Palomar](https://palomar-registry.org) registry of machine-checked results.

* `Challenge.lean` states the advertised theorems with `sorry` and imports only Mathlib. It describes the regular hexagonal tiling directly in Euclidean coordinates: a cell with axial coordinates `(q, r)` has centre `(q + r/2, (√3/2) r)`, and every cell is a translate of a regular hexagon with opposite edges at distance 1. It states Kurz's bound, the sharper bound, and the area `√3/2` of one cell, which is the unit of area in both bounds.
* `PolyhexHull/Statement.lean` repeats the definitions of `Challenge.lean` character for character, because `lake comparator` needs them to be identical on both sides.
* `PolyhexHull/Bridge.lean` proves that the linear map `(q, r) ↦ (q + r/2, (√3/2) r)` carries the axial model of `Defs.lean` onto the regular tiling and multiplies every area by `√3/2`. The axial theorems therefore give the Euclidean ones.
* `Solution.lean` repeats the statements of `Challenge.lean` and proves them from `Bridge.lean`.
* `comparator.json` names the three theorems, so that `lake comparator` can check that each proof in `Solution.lean` proves exactly the statement in `Challenge.lean` with only the standard axioms.
* `formalization.yaml` records the sources, the scope, the known divergences and how the work was produced.
* `.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical verification on a commit without submitting it.

## How this was made

The first informal proof of the upper bound was produced by the automated proof system of the Principia Math project in September 2026, whose underlying model was not disclosed. Pragyaan Gaur replaced two of its steps, the insertion lemma for the spanning tree and the final arithmetic step, with proofs of the author's own. Claude Opus 5 (Anthropic), used through Claude Code versions 2.1.271 to 2.1.284 between 16 September and 1 October 2026, helped develop the proof strategy and wrote the Lean formalization, the search program and the paper. Claude Opus 5.5 prepared the Palomar files, the bridge to Euclidean coordinates and the upgrade to Lean `v4.35.0` on 26 October 2026. Pragyaan Gaur checked the mathematics and is responsible for the content. No AI system is an author.

## Credits

The problem is Conjecture 2 of Sascha Kurz. The first informal proof of the upper bound was produced by the automated proof system of [Principia Math](https://principia-math.com) as the solution to problem MathDB 380445. Pragyaan Gaur directed the work, proved the insertion lemma and the final arithmetic step, checked all the mathematics and the statements in `Challenge.lean`, and is responsible for the content. The Lean formalization and the search program `scripts/brute.py` were written with Claude under the author's direction, as described in the section above.
