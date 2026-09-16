import PolyhexHull.Slicing

/-!
# Arbitrary directions

For `v ≠ 0` the linear map `align v : p ↦ (⟪v, p⟫ / |v|², det(v, p))` has determinant one, sends
`v` to `(1, 0)`, and turns the functional `det(v, ·)` into the second coordinate. This transports
the horizontal inequalities of `PolyhexHull.Slicing` to every direction.

All convex sets here are convex hulls of finite sets, which keeps compactness trivial.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

variable {v : ℝ × ℝ}

/-- A determinant-one linear map sending `v` to `(1, 0)`. -/
noncomputable def align (v : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ((v.1 * p.1 + v.2 * p.2) / (v.1 ^ 2 + v.2 ^ 2), v.1 * p.2 - v.2 * p.1)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

lemma norm_sq_pos (hv : v ≠ 0) : 0 < v.1 ^ 2 + v.2 ^ 2 := by
  rcases v with ⟨a, b⟩
  have : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; exact hv (by simp [h.1, h.2])
  rcases this with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

lemma align_self (hv : v ≠ 0) : align v v = ((1 : ℝ), (0 : ℝ)) := by
  have := norm_sq_pos hv
  ext
  · simp only [align, LinearMap.coe_mk, AddHom.coe_mk]; field_simp
  · simp only [align, LinearMap.coe_mk, AddHom.coe_mk]; ring

@[simp] lemma align_snd (p : ℝ × ℝ) : (align v p).2 = det2 v p := by
  simp [align, det2]

lemma align_det (hv : v ≠ 0) : LinearMap.det (align v) = 1 := by
  have hpos := norm_sq_pos hv
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr, align, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

lemma volume_image_align (hv : v ≠ 0) (s : Set (ℝ × ℝ)) : volume (align v '' s) = volume s := by
  rw [Measure.addHaar_image_linearMap, align_det hv]
  simp

lemma volume_image_affine (hv : v ≠ 0) (x : ℝ × ℝ) (s : Set (ℝ × ℝ)) :
    volume ((fun p => align v (p - x)) '' s) = volume s := by
  have : (fun p => align v (p - x)) '' s = align v '' ((fun p => p - x) '' s) := by
    rw [image_image]
  rw [this, volume_image_align hv]
  simp only [sub_eq_add_neg, image_add_right, neg_neg]
  exact measure_preimage_add_right _ _ _

lemma isCompact_convexHull_finite {F : Set (ℝ × ℝ)} (hF : F.Finite) :
    IsCompact (convexHull ℝ F) := hF.isCompact_convexHull ℝ

/-- Bounds on a linear functional pass to convex hulls. -/
lemma det_bounds_convexHull {F : Set (ℝ × ℝ)} {lo hi : ℝ}
    (hb : ∀ p ∈ F, lo ≤ det2 v p ∧ det2 v p ≤ hi) :
    ∀ p ∈ convexHull ℝ F, lo ≤ det2 v p ∧ det2 v p ≤ hi := by
  have hconv : Convex ℝ {p : ℝ × ℝ | lo ≤ det2 v p ∧ det2 v p ≤ hi} := by
    have : {p : ℝ × ℝ | lo ≤ det2 v p ∧ det2 v p ≤ hi}
        = {p | lo ≤ (align v p).2} ∩ {p | (align v p).2 ≤ hi} := by
      ext p; simp
    rw [this]
    exact (convex_halfSpace_ge ((LinearMap.snd ℝ ℝ ℝ).comp (align v)).isLinear lo).inter
      (convex_halfSpace_le ((LinearMap.snd ℝ ℝ ℝ).comp (align v)).isLinear hi)
  exact fun p hp => convexHull_min hb hconv hp

/-- `area(conv F + [0, v]) ≤ area(conv F) + (hi - lo)` when `det(v, ·) ∈ [lo, hi]` on `F`. -/
theorem volume_add_segment_le {F : Set (ℝ × ℝ)} (hF : F.Finite) (hv : v ≠ 0) {lo hi : ℝ}
    (hb : ∀ p ∈ F, lo ≤ det2 v p ∧ det2 v p ≤ hi) :
    volume (convexHull ℝ F + segment ℝ 0 v) ≤ volume (convexHull ℝ F) + ENNReal.ofReal (hi - lo) := by
  set K := convexHull ℝ F
  have hKc : IsCompact K := hF.isCompact_convexHull ℝ
  have hseg : IsCompact (segment ℝ (0 : ℝ × ℝ) v) := by
    rw [← convexHull_pair]; exact (toFinite _).isCompact_convexHull ℝ
  have himg : align v '' (K + segment ℝ 0 v) = align v '' K + segment ℝ 0 ((1 : ℝ), (0 : ℝ)) := by
    rw [image_add, ← align_self hv]
    congr 1
    have := image_segment ℝ (align v).toAffineMap 0 v
    simpa using this
  have hcont : Continuous (align v) := LinearMap.continuous_of_finiteDimensional _
  rw [← volume_image_align hv, himg, ← volume_image_align hv K]
  apply volume_add_segment_e1_le
  · exact (convex_convexHull ℝ F).linear_image (align v)
  · exact (hKc.image hcont).isClosed
  · rw [← himg]; exact ((hKc.add hseg).image hcont).isClosed.measurableSet
  · rintro _ ⟨k, hk, rfl⟩
    simpa using det_bounds_convexHull hb k hk

/-- `area(conv (F ∪ {x + v})) ≤ area(conv F) + (hi - lo)/2` for `x ∈ conv F`. -/
theorem volume_convexHull_insert_le {F : Set (ℝ × ℝ)} (hF : F.Finite) (hv : v ≠ 0) {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ F) {lo hi : ℝ} (hb : ∀ p ∈ F, lo ≤ det2 v p ∧ det2 v p ≤ hi) :
    volume (convexHull ℝ (insert (x + v) F))
      ≤ volume (convexHull ℝ F) + ENNReal.ofReal ((hi - lo) / 2) := by
  set T : ℝ × ℝ → ℝ × ℝ := fun p => align v (p - x) with hT
  set TA : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
    (align v).toAffineMap.comp (AffineMap.id ℝ (ℝ × ℝ) - AffineMap.const ℝ (ℝ × ℝ) x)
  have hTA : ⇑TA = T := by
    funext p; simp [TA, hT]
  have hcont : Continuous T := by
    rw [hT]; exact (LinearMap.continuous_of_finiteDimensional _).comp (continuous_sub_right x)
  have hdet : ∀ p, (T p).2 = det2 v p - det2 v x := by
    intro p; simp [hT, det2]
  have hK : T '' convexHull ℝ F = convexHull ℝ (T '' F) := by
    rw [← hTA, AffineMap.image_convexHull]
  have hE : T '' convexHull ℝ (insert (x + v) F)
      = convexHull ℝ (insert ((1 : ℝ), (0 : ℝ)) (convexHull ℝ (T '' F))) := by
    rw [← hTA, AffineMap.image_convexHull, image_insert_eq, hTA]
    have h1 : T (x + v) = ((1 : ℝ), (0 : ℝ)) := by simp [hT, align_self hv]
    rw [h1]
    apply Subset.antisymm
    · exact convexHull_mono (insert_subset_insert (subset_convexHull ℝ _))
    · refine convexHull_min (insert_subset_iff.mpr ⟨subset_convexHull ℝ _ (mem_insert _ _), ?_⟩)
        (convex_convexHull ℝ _)
      exact convexHull_mono (subset_insert _ _)
  have hfin : (T '' F).Finite := hF.image T
  rw [← volume_image_affine hv x, ← volume_image_affine hv x (convexHull ℝ F)]
  change volume (T '' _) ≤ volume (T '' _) + _
  rw [hE, hK]
  have h0 : (0 : ℝ × ℝ) ∈ convexHull ℝ (T '' F) := by
    rw [← hK]; exact ⟨x, hx, by simp [hT]⟩
  have hb' : ∀ k ∈ convexHull ℝ (T '' F), lo - det2 v x ≤ k.2 ∧ k.2 ≤ hi - det2 v x := by
    intro k hk
    rw [← hK] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    rw [hdet]
    have := det_bounds_convexHull hb p hp
    constructor <;> linarith [this.1, this.2]
  have := volume_convexHull_insert_e1_le (convex_convexHull ℝ _)
    ((hfin.isCompact_convexHull ℝ).isClosed) h0 ?_ hb'
  · convert this using 3
    ring
  · have hfin' : (insert ((1 : ℝ), (0 : ℝ)) (T '' F)).Finite := hfin.insert _
    have : convexHull ℝ (insert ((1 : ℝ), (0 : ℝ)) (convexHull ℝ (T '' F)))
        = convexHull ℝ (insert ((1 : ℝ), (0 : ℝ)) (T '' F)) := by
      apply Subset.antisymm
      · refine convexHull_min (insert_subset_iff.mpr ⟨subset_convexHull ℝ _ (mem_insert _ _), ?_⟩)
          (convex_convexHull ℝ _)
        exact convexHull_mono (subset_insert _ _)
      · exact convexHull_mono (insert_subset_insert (subset_convexHull ℝ _))
    rw [this]
    exact (hfin'.isCompact_convexHull ℝ).isClosed.measurableSet

end Polyhex
