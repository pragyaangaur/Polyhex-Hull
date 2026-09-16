import Mathlib

/-!
# Polyhexes in axial coordinates

Cell centres of the hexagonal tiling are the points of the triangular lattice. We use axial
coordinates `(q, r) ∈ ℤ × ℤ`, in which the six neighbours of a cell are obtained by adding
`±(1,0)`, `±(0,1)` and `±(1,-1)`.

We embed a cell `(q, r)` in the plane `ℝ × ℝ` at the point `(q, r)`, and the cell itself is the
translate of `hexagon`, the convex hull of the six points `±(1/3,1/3)`, `±(-1/3,2/3)`,
`±(2/3,-1/3)`. This is the Voronoi cell of the lattice `ℤ × ℤ` for the quadratic form that makes
the lattice triangular, so it is the image of a regular hexagon under a linear map, and the
translates `c + hexagon` for `c ∈ ℤ × ℤ` are exactly the images of the cells of a regular
hexagonal tiling. Since linear maps multiply all areas by the same constant, ratios of areas are
the same in both pictures. In these coordinates `hexagon` has area `1` (proved in
`PolyhexHull.Hexagon`), so plain Lebesgue measure on `ℝ × ℝ` is the normalisation used by Kurz.
-/

namespace Polyhex

open Set
open scoped Pointwise

/-- A cell of the hexagonal tiling, in axial coordinates. -/
abbrev Cell := ℤ × ℤ

/-- The six unit steps of the triangular lattice. -/
def units : Finset Cell := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

lemma neg_mem_units {e : Cell} (h : e ∈ units) : -e ∈ units := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- Two cells are adjacent when they share an edge. -/
def hexGraph : SimpleGraph Cell where
  Adj x y := y - x ∈ units
  symm := ⟨fun x y (h : y - x ∈ units) => by simpa using neg_mem_units h⟩
  loopless := ⟨fun x (h : x - x ∈ units) => by
    simp only [sub_self, units, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h
    norm_num at h⟩

/-- Real embedding of a lattice point. -/
def toPlane (c : Cell) : ℝ × ℝ := ((c.1 : ℝ), (c.2 : ℝ))

@[simp] lemma toPlane_fst (c : Cell) : (toPlane c).1 = c.1 := rfl
@[simp] lemma toPlane_snd (c : Cell) : (toPlane c).2 = c.2 := rfl

lemma toPlane_add (c d : Cell) : toPlane (c + d) = toPlane c + toPlane d := by
  ext <;> simp [toPlane]

lemma toPlane_sub (c d : Cell) : toPlane (c - d) = toPlane c - toPlane d := by
  ext <;> simp [toPlane]

/-- The six vertices of the central cell. -/
def hexVertices : Set (ℝ × ℝ) :=
  {(1/3, 1/3), (-1/3, 2/3), (-2/3, 1/3), (-1/3, -1/3), (1/3, -2/3), (2/3, -1/3)}

/-- The central cell, a hexagon of area one. -/
def hexagon : Set (ℝ × ℝ) := convexHull ℝ hexVertices

/-- The union of the cells of a polyhex. -/
def region (S : Finset Cell) : Set (ℝ × ℝ) := ⋃ c ∈ S, (toPlane c +ᵥ hexagon)

/-- A finite set of cells is a polyhex when it is nonempty and edge-connected. -/
def IsPolyhex (S : Finset Cell) : Prop :=
  S.Nonempty ∧ (hexGraph.induce (S : Set Cell)).Connected

/-- The planar determinant `det(v, p)`. -/
def det2 (v p : ℝ × ℝ) : ℝ := v.1 * p.2 - v.2 * p.1

/-- The three linear forms whose widths appear in the area formula. -/
def form : Fin 3 → Cell → ℤ
  | 0 => fun c => c.1 + 2 * c.2
  | 1 => fun c => c.1 - c.2
  | 2 => fun c => 2 * c.1 + c.2

lemma form_add (k : Fin 3) (c d : Cell) : form k (c + d) = form k c + form k d := by
  fin_cases k <;> simp [form] <;> ring

lemma form_sub (k : Fin 3) (c d : Cell) : form k (c - d) = form k c - form k d := by
  fin_cases k <;> simp [form] <;> ring

lemma form_sum (k : Fin 3) (s : Finset ℕ) (f : ℕ → Cell) :
    form k (∑ i ∈ s, f i) = ∑ i ∈ s, form k (f i) := by
  induction s using Finset.induction_on with
  | empty => fin_cases k <;> simp [form]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add, ih]

/-- The direction class of a unit step: `±(1,0)`, `±(0,1)` or `±(1,-1)`. -/
def cls (e : Cell) : Fin 3 :=
  if e.2 = 0 then 0 else if e.1 = 0 then 1 else 2

end Polyhex
