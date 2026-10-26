module

public import Mathlib

@[expose] public section

/-!
# Kurz's conjecture on the convex hull of a polyhex: the statements

This file is the statement surface for Palomar. It imports only Mathlib, and every theorem in it
is left as `sorry`. `Solution.lean` proves each one, and `comparator.json` lists them.

A polyhex is an edge-to-edge connected system of regular hexagons. Kurz (*Convex hulls of
polyominoes*, Beiträge Algebra Geom. 49 (2008), Conjecture 2) conjectured that the convex hull of
a polyhex with `n` cells of unit area has area at most `⌊n² + 14n/3 + 1⌋ / 6`.

The cells here are the cells of the regular hexagonal tiling of the Euclidean plane `ℝ × ℝ`.
A cell is named by its axial coordinates `(q, r) ∈ ℤ × ℤ`, its centre is
`(q + r/2, (√3/2) r)`, and the cell itself is the translate of `hexagon`, the regular hexagon
centred at the origin whose opposite edges are at distance `1`. Neighbouring centres are at
distance `1`, so two cells share an edge exactly when their axial coordinates differ by one of the
six steps in `hexSteps`. Areas are Lebesgue measure on `ℝ × ℝ`. Kurz measures area in units of
one cell, so every bound below is multiplied by `volume hexagon`, which `volume_hexagon` computes
to be `√3/2`.

* `kurz_conjecture` is Kurz's bound as he states it.
* `kurz_conjecture_sharp` is the sharper bound `⌈n² + 14n/3⌉ / 6`, which differs from Kurz's by
  `1/6` when `3 ∣ n` and agrees with it otherwise.
* `volume_hexagon` fixes the unit of area.

That the sharp bound is attained for every `n` is proved in the accompanying paper
(arXiv:2609.30310) and is not part of this formalization.
-/

open MeasureTheory Set
open scoped Pointwise

namespace KurzPolyhex

/-- The six steps between the axial coordinates of neighbouring cells of the hexagonal tiling. -/
def hexSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- The adjacency graph of the hexagonal tiling: two cells are adjacent when their axial
coordinates differ by one of the six steps, that is, when the two hexagons share an edge. -/
def hexGraph : SimpleGraph (ℤ × ℤ) where
  Adj x y := y - x ∈ hexSteps
  symm := ⟨fun x y (h : y - x ∈ hexSteps) => by
    show x - y ∈ hexSteps
    rw [← neg_sub]
    simp only [hexSteps, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h | h | h | h <;> rw [h] <;> decide⟩
  loopless := ⟨fun x (h : x - x ∈ hexSteps) => by
    rw [sub_self] at h
    exact absurd h (by decide)⟩

/-- A polyhex is a finite, nonempty set of cells that is connected in `hexGraph`, so that its
hexagons form an edge-to-edge connected system. -/
def IsPolyhex (S : Finset (ℤ × ℤ)) : Prop :=
  S.Nonempty ∧ (hexGraph.induce (S : Set (ℤ × ℤ))).Connected

/-- The centre of the cell with axial coordinates `c`. Centres of neighbouring cells are at
distance `1`. -/
noncomputable def center (c : ℤ × ℤ) : ℝ × ℝ :=
  ((c.1 : ℝ) + (c.2 : ℝ) / 2, √3 / 2 * c.2)

/-- The regular hexagon centred at the origin with vertices at distance `1/√3` from the origin, so
that opposite edges are at distance `1`. It is the cell of the tiling with centre `0`. -/
noncomputable def hexagon : Set (ℝ × ℝ) :=
  convexHull ℝ {(1 / 2, √3 / 6), (0, √3 / 3), (-1 / 2, √3 / 6),
    (-1 / 2, -√3 / 6), (0, -√3 / 3), (1 / 2, -√3 / 6)}

/-- The union of the cells of `S`, each the translate of `hexagon` by its centre. -/
noncomputable def region (S : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  ⋃ c ∈ S, center c +ᵥ hexagon

/-- The cell has area `√3/2`, the area of a regular hexagon with opposite edges at distance `1`.
This is the unit of area in the two theorems below. -/
theorem volume_hexagon : volume hexagon = ENNReal.ofReal (√3 / 2) := by
  sorry

/-- **Kurz's Conjecture 2.** The convex hull of a polyhex with `n` cells has area at most
`⌊n² + 14n/3 + 1⌋ / 6` times the area of one cell. -/
theorem kurz_conjecture (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6) := by
  sorry

/-- **The sharp bound.** The convex hull of a polyhex with `n` cells has area at most
`⌈n² + 14n/3⌉ / 6` times the area of one cell. -/
theorem kurz_conjecture_sharp (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6) := by
  sorry

end KurzPolyhex
