module

public import PolyhexHull.Main
public import PolyhexHull.HexArea
public import PolyhexHull.Statement

@[expose] public section

/-!
# From the axial model to the Euclidean statement

`PolyhexHull.Defs` works with the lattice `ℤ × ℤ` embedded as itself and a skewed hexagon of area
`1`. The linear map `shear (q, r) = (q + r/2, (√3/2) r)` carries that picture onto the regular
hexagonal tiling of `PolyhexHull.Statement`: it sends lattice points to cell centres, the skewed
hexagon to the regular one, and so each region to the corresponding region. It has determinant
`√3/2`, so it multiplies every area by the area of one regular cell. The theorems of
`PolyhexHull.Main` then transfer directly.
-/

open MeasureTheory Set
open scoped Pointwise

namespace KurzPolyhex

/-- The linear map from axial to Euclidean coordinates. -/
noncomputable def shear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 + p.2 / 2, √3 / 2 * p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

lemma shear_apply (p : ℝ × ℝ) : shear p = (p.1 + p.2 / 2, √3 / 2 * p.2) := rfl

lemma shear_det : LinearMap.det shear = √3 / 2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, shear, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]

lemma center_eq (c : ℤ × ℤ) : center c = shear (Polyhex.toPlane c) := by
  simp [center, shear_apply, Polyhex.toPlane]

lemma hexagon_eq : hexagon = shear '' Polyhex.hexagon := by
  rw [Polyhex.hexagon, LinearMap.image_convexHull, hexagon]
  congr 1
  simp only [Polyhex.hexVertices, Set.image_insert_eq, Set.image_singleton, shear_apply]
  norm_num
  ring_nf

lemma region_eq (S : Finset (ℤ × ℤ)) : region S = shear '' Polyhex.region S := by
  simp only [region, Polyhex.region, Set.image_iUnion₂, center_eq, hexagon_eq]
  refine Set.iUnion₂_congr fun c _ => ?_
  ext x
  simp only [Set.mem_vadd_set, Set.mem_image, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨Polyhex.toPlane c + h, ⟨h, hh, rfl⟩, by rw [map_add]⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨shear h, ⟨h, hh, rfl⟩, by rw [map_add]⟩

lemma volume_shear_image (s : Set (ℝ × ℝ)) :
    volume (shear '' s) = ENNReal.ofReal (√3 / 2) * volume s := by
  rw [Measure.addHaar_image_linearMap, shear_det, abs_of_nonneg (by positivity)]

theorem volume_hexagon' : volume hexagon = ENNReal.ofReal (√3 / 2) := by
  rw [hexagon_eq, volume_shear_image, Polyhex.volume_hexagon, mul_one]

lemma volume_convexHull_region (S : Finset (ℤ × ℤ)) :
    volume (convexHull ℝ (region S))
      = volume hexagon * volume (convexHull ℝ (Polyhex.region S)) := by
  rw [region_eq, ← LinearMap.image_convexHull, volume_shear_image, volume_hexagon']

lemma hexGraph_eq : hexGraph = Polyhex.hexGraph := rfl

lemma isPolyhex_iff (S : Finset (ℤ × ℤ)) : IsPolyhex S ↔ Polyhex.IsPolyhex S := Iff.rfl

theorem kurz_conjecture' (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6) := by
  rw [volume_convexHull_region]
  gcongr
  exact Polyhex.kurz_conjecture S ((isPolyhex_iff S).mp hS)

theorem kurz_conjecture_sharp' (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6) := by
  rw [volume_convexHull_region]
  gcongr
  exact Polyhex.kurz_conjecture_sharp S ((isPolyhex_iff S).mp hS)

end KurzPolyhex
