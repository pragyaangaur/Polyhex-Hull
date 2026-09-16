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

/-! ### Stretching along the horizontal axis -/

lemma mem_segment_zero_e1 {u : ℝ × ℝ} (hu : u ∈ segment ℝ 0 ((1 : ℝ), (0 : ℝ))) :
    0 ≤ u.1 ∧ u.1 ≤ 1 ∧ u.2 = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hu
  simp only [smul_zero, zero_add, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
  exact ⟨hb, by linarith, trivial⟩

theorem volume_add_segment_e1_le {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKc : IsClosed K)
    (hE : MeasurableSet (K + segment ℝ 0 ((1 : ℝ), (0 : ℝ)))) {lo hi : ℝ}
    (hb : ∀ k ∈ K, lo ≤ k.2 ∧ k.2 ≤ hi) :
    volume (K + segment ℝ 0 ((1 : ℝ), (0 : ℝ))) ≤ volume K + ENNReal.ofReal (hi - lo) := by
  classical
  let h : ℝ → ℝ := fun y => if y ∈ Icc lo hi then 1 else 0
  refine (volume_le_of_slices hK hKc hE h ?_).trans ?_
  · rintro p ⟨k, hk, u, hu, rfl⟩
    obtain ⟨hu0, hu1, hu2⟩ := mem_segment_zero_e1 hu
    refine ⟨k, hk, by simp [hu2], by simp; linarith, ?_⟩
    have : (k + u).2 ∈ Icc lo hi := by simp [hu2]; exact hb k hk
    simp only [h, this, ite_true]
    simp; linarith
  · gcongr
    have : (fun y => ENNReal.ofReal (h y)) = (Icc lo hi).indicator 1 := by
      funext y
      by_cases hy : y ∈ Icc lo hi
      · simp only [h, ite_eq_left hy, ENNReal.ofReal_one, Set.indicator_of_mem hy, Pi.one_apply]
      · simp only [h, ite_eq_right hy, ENNReal.ofReal_zero, Set.indicator_of_notMem hy]
    rw [this, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]

/-- The tent function used for point insertion. -/
noncomputable def tent (lo hi : ℝ) (y : ℝ) : ℝ :=
  if 0 ≤ y ∧ y ≤ hi then 1 - y / hi else if lo ≤ y ∧ y < 0 then 1 - y / lo else 0

lemma lintegral_tent_le {lo hi : ℝ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    ∫⁻ y, ENNReal.ofReal (tent lo hi y) ≤ ENNReal.ofReal ((hi - lo) / 2) := by
  classical
  have hsplit : (fun y => ENNReal.ofReal (tent lo hi y))
      = fun y => (Icc 0 hi).indicator (fun y => ENNReal.ofReal (1 - y / hi)) y
        + (Ico lo 0).indicator (fun y => ENNReal.ofReal (1 - y / lo)) y := by
    funext y
    simp only [tent, indicator, mem_Icc, mem_Ico]
    by_cases h1 : 0 ≤ y ∧ y ≤ hi
    · have h2 : ¬ (lo ≤ y ∧ y < 0) := fun h => by linarith [h.2, h1.1]
      simp [h1, h2]
    · by_cases h2 : lo ≤ y ∧ y < 0 <;> simp [h1, h2]
  rw [hsplit, lintegral_add_left' ((Measurable.ennreal_ofReal (by fun_prop)).indicator
      measurableSet_Icc).aemeasurable,
    lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ico]
  have I1 : ∫⁻ y in Icc 0 hi, ENNReal.ofReal (1 - y / hi) = ENNReal.ofReal (hi / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hhi]
      rcases hhi.eq_or_lt with h0 | h0
      · subst h0; simp
      · simp only [intervalIntegral.integral_sub intervalIntegrable_const
          (intervalIntegral.intervalIntegrable_id.div_const _), intervalIntegral.integral_const,
          intervalIntegral.integral_div, integral_id]
        field_simp
        ring
    · exact (by fun_prop : Continuous fun y : ℝ => 1 - y / hi).integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rcases hhi.eq_or_lt with h0 | h0
      · subst h0; simp
      · have : y / hi ≤ 1 := (div_le_one h0).mpr hy.2
        simp only [Pi.zero_apply]; linarith
  have I2 : ∫⁻ y in Ico lo 0, ENNReal.ofReal (1 - y / lo) = ENNReal.ofReal (-lo / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hlo]
      rcases hlo.eq_or_lt with h0 | h0
      · subst h0; simp
      · simp only [intervalIntegral.integral_sub intervalIntegrable_const
          (intervalIntegral.intervalIntegrable_id.div_const _), intervalIntegral.integral_const,
          intervalIntegral.integral_div, integral_id]
        have hne : lo ≠ 0 := h0.ne
        field_simp
        ring
    · exact ((by fun_prop : Continuous fun y : ℝ => 1 - y / lo).integrableOn_Icc).mono_set
        Ico_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
      rcases hlo.eq_or_lt with h0 | h0
      · subst h0; simp at hy
      · have : y / lo ≤ 1 := by
          rw [div_le_one_of_neg h0]; exact hy.1
        simp only [Pi.zero_apply]; linarith
  rw [I1, I2, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  apply le_of_eq
  congr 1
  ring

theorem volume_convexHull_insert_e1_le {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKc : IsClosed K)
    (h0 : (0 : ℝ × ℝ) ∈ K) (hE : MeasurableSet (convexHull ℝ (insert ((1 : ℝ), (0 : ℝ)) K)))
    {lo hi : ℝ} (hb : ∀ k ∈ K, lo ≤ k.2 ∧ k.2 ≤ hi) :
    volume (convexHull ℝ (insert ((1 : ℝ), (0 : ℝ)) K))
      ≤ volume K + ENNReal.ofReal ((hi - lo) / 2) := by
  have hlo : lo ≤ 0 := by simpa using (hb 0 h0).1
  have hhi : 0 ≤ hi := by simpa using (hb 0 h0).2
  refine (volume_le_of_slices hK hKc hE (tent lo hi) ?_).trans ?_
  · intro p hp
    rw [convexHull_insert ⟨0, h0⟩, hK.convexHull_eq, mem_convexJoin] at hp
    obtain ⟨v, hv, k, hk, a, b, ha, hb', hab, rfl⟩ := hp
    simp only [mem_singleton_iff] at hv
    subst hv
    -- the point is `b • k` shifted right by `a`
    have hbk : b • k ∈ K := hK.smul_mem_of_zero_mem h0 hk ⟨hb', by linarith⟩
    have hy : (a • ((1 : ℝ), (0 : ℝ)) + b • k).2 = b * k.2 := by simp
    have hx : (a • ((1 : ℝ), (0 : ℝ)) + b • k).1 = b * k.1 + a := by simp; ring
    refine ⟨b • k, hbk, by rw [hy]; simp, by rw [hx]; simp [ha], ?_⟩
    obtain ⟨hlk, hkh⟩ := hb k hk
    rw [hx, hy, Prod.smul_fst, smul_eq_mul, add_le_add_iff_left]
    have ha' : a = 1 - b := by linarith
    unfold tent
    by_cases hpos : 0 ≤ b * k.2
    · have hle : b * k.2 ≤ b * hi := mul_le_mul_of_nonneg_left hkh hb'
      have hle' : b * k.2 ≤ hi := by nlinarith
      rw [ite_eq_left ⟨hpos, hle'⟩]
      rcases hhi.eq_or_lt with h0' | h0'
      · subst h0'; simp only [div_zero, sub_zero]; linarith
      · have : b * k.2 / hi ≤ b := by rw [div_le_iff₀ h0']; linarith
        linarith
    · push Not at hpos
      have hge : b * lo ≤ b * k.2 := mul_le_mul_of_nonneg_left hlk hb'
      have hge' : lo ≤ b * k.2 := by nlinarith
      rw [ite_eq_right (fun h => by linarith [h.1]), ite_eq_left ⟨hge', hpos⟩]
      rcases hlo.eq_or_lt with h0' | h0'
      · subst h0'; linarith
      · have : b * k.2 / lo ≤ b := by rw [div_le_iff_of_neg h0']; linarith
        linarith
  · gcongr
    exact lintegral_tent_le hlo hhi

end Polyhex
