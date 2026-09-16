import PolyhexHull.Defs

/-!
# Area growth by slicing

The two geometric inequalities of the proof are both of the form "a convex set grows by at most
so much area when it is stretched in one direction". We prove them by slicing along horizontal
lines (Fubini) in coordinates where the stretching direction is `(1, 0)`, and then transport them
to an arbitrary direction `v` by a linear map of determinant one.

* `volume_add_segment_le`: `area(K + [0, v]) ≤ area K + width_{det(v,·)} K`.
* `volume_convexHull_insert_le`: for `x ∈ K`,
  `area(conv(K ∪ {x + v})) ≤ area K + ½ width_{det(v,·)} K`.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

/-- Horizontal sections of a convex set are intervals. -/
lemma section_ordConnected {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (y : ℝ) :
    ((fun x : ℝ => (x, y)) ⁻¹' K).OrdConnected := by
  have hc : Convex ℝ ((fun x : ℝ => (x, y)) ⁻¹' K) := by
    intro a ha b hb θ φ hθ hφ hθφ
    simp only [mem_preimage] at ha hb ⊢
    have := hK ha hb hθ hφ hθφ
    convert this using 1
    ext
    · simp [smul_eq_mul]
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rw [← add_mul, hθφ, one_mul]
  exact hc.ordConnected

/-- The slicing lemma: if every point of `E` lies to the right of a point of the convex set `K` on
the same horizontal line, at distance at most `h y`, then `E` has at most `∫ h` more area. -/
theorem volume_le_of_slices {K E : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKc : IsClosed K)
    (hE : MeasurableSet E) (h : ℝ → ℝ)
    (hyp : ∀ p ∈ E, ∃ q ∈ K, q.2 = p.2 ∧ q.1 ≤ p.1 ∧ p.1 ≤ q.1 + h p.2) :
    volume E ≤ volume K + ∫⁻ y, ENNReal.ofReal (h y) := by
  have hmeas : MeasurableSet (E \ K) := hE.diff hKc.measurableSet
  calc volume E ≤ volume (E ∩ K) + volume (E \ K) := by
        conv_lhs => rw [← inter_union_sdiff E K]
        exact measure_union_le _ _
    _ ≤ volume K + volume (E \ K) := by gcongr; exact inter_subset_right
    _ ≤ volume K + ∫⁻ y, ENNReal.ofReal (h y) := by
        gcongr
        rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
        refine lintegral_mono fun y => ?_
        set T := (fun x : ℝ => (x, y)) ⁻¹' (E \ K) with hT
        -- every point of the section lies strictly to the right of the section of `K`
        have right : ∀ x ∈ T, ∃ x₀, (x₀, y) ∈ K ∧ x ≤ x₀ + h y ∧
            ∀ k, (k, y) ∈ K → k < x := by
          intro x hx
          simp only [hT, mem_preimage, mem_sdiff] at hx
          obtain ⟨q, hq, hq2, hq1, hqh⟩ := hyp _ hx.1
          simp only at hq2 hq1 hqh
          have hqK : (q.1, y) ∈ K := by rw [← hq2]; exact hq
          refine ⟨q.1, hqK, hqh, fun k hk => ?_⟩
          by_contra hkx
          push Not at hkx
          have := (section_ordConnected hK y).out hqK hk ⟨hq1, hkx⟩
          exact hx.2 this
        have key : ∀ x ∈ T, ∀ x' ∈ T, x' - x ≤ h y := by
          intro x hx x' hx'
          obtain ⟨x₀, -, -, hlt⟩ := right x hx
          obtain ⟨x₀', hK', hle', -⟩ := right x' hx'
          have := hlt x₀' hK'
          linarith
        calc volume T ≤ Metric.ediam T := Real.volume_le_diam T
          _ ≤ ENNReal.ofReal (h y) := by
            apply Metric.ediam_le
            intro x hx x' hx'
            rw [edist_dist, Real.dist_eq]
            apply ENNReal.ofReal_le_ofReal
            rw [abs_le]
            constructor <;> linarith [key x hx x' hx', key x' hx' x hx]

end Polyhex
