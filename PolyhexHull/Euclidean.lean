import PolyhexHull.HexArea

/-!
# The Euclidean picture

The linear map `euclid (q, r) = κ (q + r/2, (√3/2) r)` with `κ² = 2/√3` has determinant one and
carries the axial picture to the usual Euclidean one:

* it intertwines the lattice rotation `rho (q, r) = (-r, q + r)` with the rotation `rot60` by
  sixty degrees, and `rho` cycles the six vertices of `hexagon`, so `euclid '' hexagon` is a
  regular hexagon;
* it preserves area, so `euclid '' hexagon` has area one;
* neighbouring cells share an edge.

Hence `kurz_conjecture_euclid` is Kurz's statement about regular hexagons of unit area in the
Euclidean plane, for cells of the regular hexagonal tiling.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

noncomputable def κ : ℝ := Real.sqrt (2 / Real.sqrt 3)

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma κ_sq : κ ^ 2 = 2 / Real.sqrt 3 := by
  rw [κ, Real.sq_sqrt (by positivity [sqrt3_pos])]

/-- From axial to Euclidean coordinates, scaled so that one cell has area one. -/
noncomputable def euclid : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (κ * (p.1 + p.2 / 2), κ * (Real.sqrt 3 / 2 * p.2))
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

lemma euclid_det : LinearMap.det euclid = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, euclid, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  have h3 : Real.sqrt 3 ≠ 0 := sqrt3_pos.ne'
  have := κ_sq
  field_simp
  rw [this]
  field_simp

/-- Rotation by sixty degrees. -/
noncomputable def rot60 (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / 2 - Real.sqrt 3 / 2 * p.2, Real.sqrt 3 / 2 * p.1 + p.2 / 2)

lemma rot60_normSq (p : ℝ × ℝ) :
    (rot60 p).1 ^ 2 + (rot60 p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [rot60]
  nlinarith [h]

/-- The lattice rotation in axial coordinates. -/
def rho (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, p.1 + p.2)

lemma euclid_rho (p : ℝ × ℝ) : euclid (rho p) = rot60 (euclid p) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [euclid, rho, rot60, LinearMap.coe_mk, AddHom.coe_mk]
  ext
  · have h' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    simp only
    linear_combination (κ * p.2 / 4) * h'
  · simp only; ring

/-- The six vertices, in counterclockwise order. -/
noncomputable def hexVertex : Fin 6 → ℝ × ℝ
  | 0 => (1/3, 1/3)
  | 1 => (-1/3, 2/3)
  | 2 => (-2/3, 1/3)
  | 3 => (-1/3, -1/3)
  | 4 => (1/3, -2/3)
  | 5 => (2/3, -1/3)

lemma hexVertices_eq : hexVertices = range hexVertex := by
  ext p
  simp only [hexVertices, mem_insert_iff, mem_singleton_iff, mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [hexVertex]

lemma rho_hexVertex (k : Fin 6) : rho (hexVertex k) = hexVertex (k + 1) := by
  fin_cases k <;> simp [rho, hexVertex] <;> norm_num

/-- **Regularity.** Consecutive Euclidean vertices differ by a rotation of sixty degrees about
the centre. -/
theorem euclid_hexVertex_succ (k : Fin 6) :
    euclid (hexVertex (k + 1)) = rot60 (euclid (hexVertex k)) := by
  rw [← rho_hexVertex, euclid_rho]

/-- The Euclidean cell has area one. -/
theorem volume_euclid_hexagon : volume (euclid '' hexagon) = 1 := by
  rw [Measure.addHaar_image_linearMap, euclid_det, volume_hexagon]
  simp

/-- The cell at `(1, 0)` shares with the central cell the edge between two of its vertices. -/
lemma neighbour_shares_edge :
    hexVertex 0 ∈ toPlane (1, 0) +ᵥ hexVertices ∧ hexVertex 5 ∈ toPlane (1, 0) +ᵥ hexVertices := by
  refine ⟨⟨(-2/3, 1/3), by simp [hexVertices], ?_⟩, ⟨(-1/3, -1/3), by simp [hexVertices], ?_⟩⟩ <;>
    simp [toPlane, hexVertex] <;> norm_num

/-- **Kurz's Conjecture 2, Euclidean form.** -/
theorem kurz_conjecture_euclid (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (euclid '' region S))
      ≤ ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6) := by
  rw [← LinearMap.image_convexHull, Measure.addHaar_image_linearMap, euclid_det]
  simpa using kurz_conjecture S hS

end Polyhex
