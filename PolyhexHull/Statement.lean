module

public import Mathlib

@[expose] public section

/-!
# The statement definitions

This file repeats, character for character, the definitions of `Challenge.lean`: the hexagonal
tiling in Euclidean coordinates, its adjacency graph, polyhexes and their regions. Comparator
requires the definitions used by the compared theorems to be identical in `Challenge.lean` and in
the environment of `Solution.lean`, and `Challenge.lean` may import only Mathlib, so the two copies
must be kept in step by hand. `PolyhexHull.Bridge` relates them to the axial model in
`PolyhexHull.Defs`.
-/

open MeasureTheory Set
open scoped Pointwise

namespace KurzPolyhex

/-- The six steps between the axial coordinates of neighbouring cells of the hexagonal tiling. -/
def hexSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- The adjacency graph of the hexagonal tiling: two different cells are adjacent when their axial
coordinates differ by one of the six steps, that is, when the two hexagons share an edge. Since
`hexSteps` is closed under negation and does not contain `0`, this is the same as asking that
`y - x ∈ hexSteps`. -/
def hexGraph : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel fun x y => y - x ∈ hexSteps

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

end KurzPolyhex
