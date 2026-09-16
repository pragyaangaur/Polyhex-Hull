import PolyhexHull.Main

/-!
# The cell has area one

The upper bound comes from the zonotope form and the segment inequality. For the lower bound the
hexagon contains three rhombi of area `1/3` each, which overlap only along segments.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

/-- A line `a x + b y = c` with `b ≠ 0` has measure zero. -/
lemma volume_line {a b c : ℝ} (hb : b ≠ 0) :
    volume {p : ℝ × ℝ | a * p.1 + b * p.2 = c} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | a * p.1 + b * p.2 = c} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | a * p.1 + b * p.2 = c}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | a * p.1 + b * p.2 = c} = {(c - a * x) / b} := by
      ext y
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [h]; field_simp; ring
    rw [this, measure_singleton]
  exact (lintegral_congr fun x => this x).trans lintegral_zero

/-- The parallelogram `b + [0,1] u + [0,1] w`. -/
def rhombus (b u w : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun st : ℝ × ℝ => b + st.1 • u + st.2 • w) '' (Icc 0 1 ×ˢ Icc 0 1)

/-- The linear map `(s, t) ↦ s u + t w`. -/
noncomputable def spanMap (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

lemma spanMap_det (u w : ℝ × ℝ) : LinearMap.det (spanMap u w) = u.1 * w.2 - u.2 * w.1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, spanMap, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  ring

lemma volume_rhombus (b u w : ℝ × ℝ) :
    volume (rhombus b u w) = ENNReal.ofReal |u.1 * w.2 - u.2 * w.1| := by
  have : rhombus b u w = (fun p => b + p) '' (spanMap u w '' (Icc 0 1 ×ˢ Icc 0 1)) := by
    rw [rhombus, image_image]
    congr 1
    funext st
    simp [spanMap, add_assoc]
  rw [this, image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, spanMap_det,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

lemma isCompact_rhombus (b u w : ℝ × ℝ) : IsCompact (rhombus b u w) :=
  (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/-- Coordinates with respect to `g₁, g₂` based at `z₀`: `α = x - y`, `β = x + 2y` for
`(x, y) = p - z₀`. -/
lemma rhombus12_coords {p : ℝ × ℝ} (hp : p ∈ rhombus z0 g1 g2) :
    0 ≤ (p.1 + 1/3) - (p.2 + 1/3) ∧ (p.1 + 1/3) + 2 * (p.2 + 1/3) ≤ 1 ∧
      (p.1 + 1/3) - (p.2 + 1/3) ≤ 1 ∧ 0 ≤ (p.1 + 1/3) + 2 * (p.2 + 1/3) := by
  obtain ⟨⟨s, t⟩, ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩, rfl⟩ := hp
  simp only [z0, g1, g2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma rhombus23_coords {p : ℝ × ℝ} (hp : p ∈ rhombus z0 g2 g3) :
    (p.1 + 1/3) - (p.2 + 1/3) ≤ 0 ∧ (p.1 + 1/3) - (p.2 + 1/3) + ((p.1 + 1/3) + 2 * (p.2 + 1/3)) ≤ 1 := by
  obtain ⟨⟨s, t⟩, ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩, rfl⟩ := hp
  simp only [z0, g2, g3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> linarith

lemma rhombus13_coords {p : ℝ × ℝ} (hp : p ∈ rhombus (z0 + g2) g1 g3) :
    1 ≤ (p.1 + 1/3) + 2 * (p.2 + 1/3) ∧
      1 ≤ (p.1 + 1/3) - (p.2 + 1/3) + ((p.1 + 1/3) + 2 * (p.2 + 1/3)) := by
  obtain ⟨⟨s, t⟩, ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩, rfl⟩ := hp
  simp only [z0, g1, g2, g3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> linarith

lemma rhombus_subset_hexagon {b u w : ℝ × ℝ}
    (h : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → b + s • u + t • w ∈ hexagon) :
    rhombus b u w ⊆ hexagon := by
  rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  exact h s t hs ht

lemma smul_mem_segment {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (u : ℝ × ℝ) : s • u ∈ segment ℝ 0 u :=
  ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, by simp⟩

theorem volume_hexagon : volume hexagon = 1 := by
  apply le_antisymm
  · -- upper bound through the zonotope form
    have hb0 : ∀ p ∈ ({z0} : Set (ℝ × ℝ)), -1/3 ≤ det2 g1 p ∧ det2 g1 p ≤ -1/3 := by
      intro p hp; rw [mem_singleton_iff] at hp; subst hp
      simp [det2, g1, z0]; norm_num
    have hb1' : ∀ p ∈ ({z0} : Set (ℝ × ℝ)), 0 ≤ det2 g2 p ∧ det2 g2 p ≤ 0 := by
      intro p hp; rw [mem_singleton_iff] at hp; subst hp
      simp [det2, g2, z0]
    have hb2' : ∀ p ∈ ({z0} : Set (ℝ × ℝ)), 1/3 ≤ det2 g3 p ∧ det2 g3 p ≤ 1/3 := by
      intro p hp; rw [mem_singleton_iff] at hp; subst hp
      simp [det2, g3, z0]; norm_num
    have hb1 := det_bounds_add_pair (u := g1) hb1' (by simp [det2, g1, g2]; norm_num)
    have hb2 := det_bounds_add_pair (u := g2)
      (det_bounds_add_pair (u := g1) hb2' (by simp [det2, g1, g3]; norm_num))
      (by simp [det2, g2, g3]; norm_num)
    have hF0 : ({z0} : Set (ℝ × ℝ)).Finite := finite_singleton _
    have hF1 : ({z0} + {0, g1} : Set (ℝ × ℝ)).Finite := hF0.add (toFinite _)
    have hF2 : ({z0} + {0, g1} + {0, g2} : Set (ℝ × ℝ)).Finite := hF1.add (toFinite _)
    have s1 := volume_add_segment_le hF0 (by simp [g1, Prod.ext_iff]) hb0
    have s2 := volume_add_segment_le hF1 (by simp [g2, Prod.ext_iff]) hb1
    have s3 := volume_add_segment_le hF2 (by simp [g3, Prod.ext_iff]) hb2
    rw [convexHull_add_pair] at s1 s2 s3
    rw [convexHull_singleton, measure_singleton, zero_add] at s1
    have d21 : det2 g2 g1 = -1/3 := by simp [det2, g1, g2]; norm_num
    have d31 : det2 g3 g1 = -1/3 := by simp [det2, g1, g3]; norm_num
    have d32 : det2 g3 g2 = -1/3 := by simp [det2, g2, g3]; norm_num
    rw [d21] at s2
    rw [d31, d32] at s3
    have hhex : hexagon = convexHull ℝ ({z0} + {0, g1} + {0, g2} + {0, g3}) := by
      rw [hexagon_eq_zonotope, convexHull_add, convexHull_add, convexHull_add, convexHull_singleton,
        convexHull_pair, convexHull_pair, convexHull_pair]
    rw [hhex]
    refine ((s3.trans (add_le_add s2 le_rfl)).trans
      (add_le_add (add_le_add s1 le_rfl) le_rfl)).trans_eq ?_
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · -- lower bound through three rhombi
    have hz : ∀ s t u : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 →
        z0 + s • g1 + t • g2 + u • g3 ∈ hexagon := by
      intro s t u hs ht hu
      rw [hexagon_eq_zonotope]
      exact add_mem_add (add_mem_add (add_mem_add (mem_singleton _) (smul_mem_segment hs _))
        (smul_mem_segment ht _)) (smul_mem_segment hu _)
    have I01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have I11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have h12 : rhombus z0 g1 g2 ⊆ hexagon := rhombus_subset_hexagon fun s t hs ht => by
      simpa using hz s t 0 hs ht I01
    have h23 : rhombus z0 g2 g3 ⊆ hexagon := rhombus_subset_hexagon fun s t hs ht => by
      simpa using hz 0 s t I01 hs ht
    have h13 : rhombus (z0 + g2) g1 g3 ⊆ hexagon := rhombus_subset_hexagon fun s t hs ht => by
      have := hz s 1 t hs I11 ht
      convert this using 1; simp; abel
    have n1 : volume (rhombus z0 g1 g2 ∩ rhombus z0 g2 g3) = 0 := by
      refine measure_mono_null (fun p hp => ?_) (volume_line (a := 1) (b := -1) (c := 0)
        (by norm_num))
      have := rhombus12_coords hp.1; have := rhombus23_coords hp.2
      simp only [mem_ofPred_eq]; linarith
    have n2 : volume (rhombus z0 g1 g2 ∩ rhombus (z0 + g2) g1 g3) = 0 := by
      refine measure_mono_null (fun p hp => ?_) (volume_line (a := 1) (b := 2) (c := 0)
        (by norm_num))
      have := rhombus12_coords hp.1; have := rhombus13_coords hp.2
      simp only [mem_ofPred_eq]; linarith
    have n3 : volume (rhombus z0 g2 g3 ∩ rhombus (z0 + g2) g1 g3) = 0 := by
      refine measure_mono_null (fun p hp => ?_) (volume_line (a := 2) (b := 1) (c := 0)
        (by norm_num))
      have := rhombus23_coords hp.1; have := rhombus13_coords hp.2
      simp only [mem_ofPred_eq]; linarith
    have hunion : volume (rhombus z0 g1 g2 ∪ rhombus z0 g2 g3 ∪ rhombus (z0 + g2) g1 g3) = 1 := by
      rw [measure_union₀ (isCompact_rhombus _ _ _).isClosed.measurableSet.nullMeasurableSet,
        measure_union₀ (isCompact_rhombus _ _ _).isClosed.measurableSet.nullMeasurableSet n1,
        volume_rhombus, volume_rhombus, volume_rhombus]
      · rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
        simp [g1, g2, g3]
        norm_num
      · refine measure_mono_null ?_ ((measure_union_null n2 n3))
        rw [union_inter_distrib_right]
    calc (1 : ENNReal) = volume (rhombus z0 g1 g2 ∪ rhombus z0 g2 g3 ∪ rhombus (z0 + g2) g1 g3) :=
          hunion.symm
      _ ≤ volume hexagon := measure_mono (union_subset (union_subset h12 h23) h13)

end Polyhex
