import PolyhexHull.Arith
import PolyhexHull.Connect
import PolyhexHull.Hexagon
import PolyhexHull.TreeArea

/-!
# Kurz's hexagon conjecture

**Conjecture 2 of S. Kurz, *Convex hulls of polyominoes* (Beiträge Algebra Geom. 49 (2008)).**
The area of the convex hull of any edge-to-edge connected system of `n` regular hexagons of unit
area is at most `⌊n² + 14n/3 + 1⌋ / 6`.

We prove the slightly sharper bound `⌈n² + 14n/3⌉ / 6` and deduce Kurz's form.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

/-- The union of translates of the hexagon is the Minkowski sum of centres and hexagon. -/
lemma region_eq (S : Finset Cell) :
    region S = ((fun c => toPlane c) '' (S : Set Cell)) + hexagon := by
  ext p
  simp only [region, mem_iUnion, mem_add, mem_image, Finset.mem_coe, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨c, hc, h, hh, rfl⟩; exact ⟨_, ⟨c, hc, rfl⟩, h, hh, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, h, hh, rfl⟩; exact ⟨c, hc, h, hh, rfl⟩

lemma convexHull_region (S : Finset Cell) :
    convexHull ℝ (region S) = convexHull ℝ ((fun c => toPlane c) '' (S : Set Cell)) + hexagon := by
  rw [region_eq, convexHull_add, convex_hexagon.convexHull_eq]

/-- Bounds on `det(v, ·)` for a set `F + {0, u}` with `det(v, u) ≤ 0`. -/
lemma det_bounds_add_pair {F : Set (ℝ × ℝ)} {v u : ℝ × ℝ} {lo hi : ℝ}
    (hb : ∀ p ∈ F, lo ≤ det2 v p ∧ det2 v p ≤ hi) (hu : det2 v u ≤ 0) :
    ∀ p ∈ F + {0, u}, lo + det2 v u ≤ det2 v p ∧ det2 v p ≤ hi := by
  rintro _ ⟨f, hf, w, hw, rfl⟩
  have hadd : det2 v (f + w) = det2 v f + det2 v w := by simp [det2]; ring
  obtain ⟨h1, h2⟩ := hb f hf
  simp only [mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · have h0 : det2 v 0 = 0 := by simp [det2]
    rw [hadd, h0]; constructor <;> linarith
  · rw [hadd]; constructor <;> linarith

lemma convexHull_add_pair (F : Set (ℝ × ℝ)) (u : ℝ × ℝ) :
    convexHull ℝ F + segment ℝ 0 u = convexHull ℝ (F + {0, u}) := by
  rw [convexHull_add, convexHull_pair]

lemma volume_add_singleton (s : Set (ℝ × ℝ)) (b : ℝ × ℝ) : volume (s + {b}) = volume s := by
  rw [add_singleton, image_add_right]
  exact measure_preimage_add_right _ _ _

/-- The main estimate, in terms of any growth order. -/
theorem volume_hull_le_growth {S : Finset Cell} (g : Growth S) :
    volume (convexHull ℝ (region S)) ≤ ENNReal.ofReal
      ((g.pairs g.s : ℝ) / 2 + 1 + g.s + (max (g.count 0) (max (g.count 1) (g.count 2)) : ℕ) / 3) := by
  classical
  -- extremal cells for the three forms
  have hne : (Finset.range (g.s + 1)).Nonempty := ⟨0, by simp⟩
  have hmax := fun k : Fin 3 => Finset.exists_max_image _ (fun i => form k (g.pt i)) hne
  have hmin := fun k : Fin 3 => Finset.exists_min_image _ (fun i => form k (g.pt i)) hne
  choose M hMr hM using hmax
  choose N hNr hN using hmin
  have hMs : ∀ k, M k ≤ g.s := fun k => by have := hMr k; simp at this; omega
  have hNs : ∀ k, N k ≤ g.s := fun k => by have := hNr k; simp at this; omega
  set A : Fin 3 → ℝ := fun k => form k (g.pt (M k))
  set B : Fin 3 → ℝ := fun k => form k (g.pt (N k))
  set C : Set (ℝ × ℝ) := (fun c => toPlane c) '' (S : Set Cell)
  have hC : C = g.pts g.s := by
    ext p
    simp only [C, Growth.pts, mem_image, Finset.mem_coe, mem_ofPred_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨i, hi, rfl⟩ := g.mem_iff.mp hc
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨g.pt i, g.pt_mem hi, rfl⟩
  have hCfin : C.Finite := (S.finite_toSet).image _
  -- bounds of the three forms on the centres
  have hform : ∀ k, ∀ c ∈ S, (B k : ℝ) ≤ form k c ∧ (form k c : ℝ) ≤ A k := by
    intro k c hc
    obtain ⟨i, hi, rfl⟩ := g.mem_iff.mp hc
    have hi' : i ∈ Finset.range (g.s + 1) := by simp; omega
    simp only [A, B]
    exact ⟨by exact_mod_cast hN k i hi', by exact_mod_cast hM k i hi'⟩
  -- the three stages
  set F0 : Set (ℝ × ℝ) := C + {z0}
  set F1 : Set (ℝ × ℝ) := F0 + {0, g1}
  set F2 : Set (ℝ × ℝ) := F1 + {0, g2}
  have hF0 : F0.Finite := hCfin.add (finite_singleton _)
  have hF1 : F1.Finite := hF0.add (toFinite _)
  have hF2 : F2.Finite := hF1.add (toFinite _)
  have hb0 : ∀ p ∈ F0, B 0 / 3 - 1/3 ≤ det2 g1 p ∧ det2 g1 p ≤ A 0 / 3 - 1/3 := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, w, hw, rfl⟩
    rw [mem_singleton_iff] at hw; subst hw
    have := hform 0 c hc
    simp only [det2, g1, z0, toPlane, form, Prod.fst_add, Prod.snd_add] at this ⊢
    push_cast at this
    constructor <;> linarith
  have hb1' : ∀ p ∈ F0, -A 1 / 3 ≤ det2 g2 p ∧ det2 g2 p ≤ -B 1 / 3 := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, w, hw, rfl⟩
    rw [mem_singleton_iff] at hw; subst hw
    have := hform 1 c hc
    simp only [det2, g2, z0, toPlane, form, Prod.fst_add, Prod.snd_add] at this ⊢
    push_cast at this
    constructor <;> linarith
  have hb1 := det_bounds_add_pair (u := g1) hb1' (by simp [det2, g1, g2]; norm_num)
  have hb2' : ∀ p ∈ F0, -A 2 / 3 + 1/3 ≤ det2 g3 p ∧ det2 g3 p ≤ -B 2 / 3 + 1/3 := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, w, hw, rfl⟩
    rw [mem_singleton_iff] at hw; subst hw
    have := hform 2 c hc
    simp only [det2, g3, z0, toPlane, form, Prod.fst_add, Prod.snd_add] at this ⊢
    push_cast at this
    constructor <;> linarith
  have hb2 := det_bounds_add_pair (u := g2)
    (det_bounds_add_pair (u := g1) hb2' (by simp [det2, g1, g3]; norm_num))
    (by simp [det2, g2, g3]; norm_num)
  have hg1 : g1 ≠ 0 := by simp [g1, Prod.ext_iff]
  have hg2 : g2 ≠ 0 := by simp [g2, Prod.ext_iff]
  have hg3 : g3 ≠ 0 := by simp [g3, Prod.ext_iff]
  -- rewrite the hull as a sum of segments
  have hhull : convexHull ℝ (region S)
      = convexHull ℝ F2 + segment ℝ 0 g3 := by
    rw [convexHull_region, hexagon_eq_zonotope, ← convexHull_add_pair, ← convexHull_add_pair]
    simp only [F0]
    rw [convexHull_add, convexHull_singleton]
    simp only [add_assoc]
    rfl
  have s3 := volume_add_segment_le hF2 hg3 hb2
  have s2 := volume_add_segment_le hF1 hg2 hb1
  have s1 := volume_add_segment_le hF0 hg1 hb0
  have htrans : volume (convexHull ℝ F0) = volume (convexHull ℝ C) := by
    simp only [F0]
    rw [convexHull_add, convexHull_singleton, volume_add_singleton]
  have harea := g.volume_hull_pts_le g.s le_rfl
  rw [← hC] at harea
  -- widths
  have hW := g.width_sum_le M N hMs hNs
  have hWr : A 0 - B 0 + (A 1 - B 1) + (A 2 - B 2)
      ≤ 3 * (g.s : ℝ) + (max (g.count 0) (max (g.count 1) (g.count 2)) : ℕ) := by
    simp only [Fin.sum_univ_three] at hW
    have : ((form 0 (g.pt (M 0)) - form 0 (g.pt (N 0)) + (form 1 (g.pt (M 1)) - form 1 (g.pt (N 1)))
        + (form 2 (g.pt (M 2)) - form 2 (g.pt (N 2))) : ℤ) : ℝ)
        ≤ ((3 * g.s + (max (g.count 0) (max (g.count 1) (g.count 2)) : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hW
    push_cast at this
    simp only [A, B]
    push_cast
    linarith
  have hAB : ∀ k, B k ≤ A k := fun k => by
    have := hform k _ (g.pt_mem (Nat.zero_le g.s))
    exact this.1.trans this.2
  have d21 : det2 g2 g1 = -1/3 := by simp [det2, g1, g2]; norm_num
  have d31 : det2 g3 g1 = -1/3 := by simp [det2, g1, g3]; norm_num
  have d32 : det2 g3 g2 = -1/3 := by simp [det2, g2, g3]; norm_num
  have e1 : convexHull ℝ F1 = convexHull ℝ F0 + segment ℝ 0 g1 := (convexHull_add_pair F0 g1).symm
  have e2 : convexHull ℝ F2 = convexHull ℝ F1 + segment ℝ 0 g2 := (convexHull_add_pair F1 g2).symm
  rw [d21] at s2
  rw [d31, d32] at s3
  have hA0 := hAB 0
  have hA1 := hAB 1
  have hA2 := hAB 2
  have hp0 : (0 : ℝ) ≤ g.pairs g.s := Nat.cast_nonneg _
  rw [hhull]
  calc volume (convexHull ℝ F2 + segment ℝ 0 g3)
      ≤ volume (convexHull ℝ F2)
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := s3
    _ = volume (convexHull ℝ F1 + segment ℝ 0 g2)
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := by rw [e2]
    _ ≤ volume (convexHull ℝ F1) + ENNReal.ofReal ((-B 1 / 3) - (-A 1 / 3 + -1/3))
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := by
        gcongr
    _ = volume (convexHull ℝ F0 + segment ℝ 0 g1)
          + ENNReal.ofReal ((-B 1 / 3) - (-A 1 / 3 + -1/3))
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := by rw [e1]
    _ ≤ volume (convexHull ℝ F0) + ENNReal.ofReal ((A 0 / 3 - 1/3) - (B 0 / 3 - 1/3))
          + ENNReal.ofReal ((-B 1 / 3) - (-A 1 / 3 + -1/3))
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := by
        gcongr
    _ ≤ ENNReal.ofReal ((g.pairs g.s : ℝ) / 2) + ENNReal.ofReal ((A 0 / 3 - 1/3) - (B 0 / 3 - 1/3))
          + ENNReal.ofReal ((-B 1 / 3) - (-A 1 / 3 + -1/3))
          + ENNReal.ofReal ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3)) := by
        rw [htrans]; gcongr
    _ = ENNReal.ofReal ((g.pairs g.s : ℝ) / 2 + ((A 0 / 3 - 1/3) - (B 0 / 3 - 1/3))
          + ((-B 1 / 3) - (-A 1 / 3 + -1/3))
          + ((-B 2 / 3 + 1/3) - (-A 2 / 3 + 1/3 + -1/3 + -1/3))) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;>
          first | positivity | linarith
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        linarith

/-- **Kurz's Conjecture 2, sharp form.** For an edge-connected set of `n` hexagonal cells, the
convex hull of their union has area at most `⌈n² + 14n/3⌉ / 6`. -/
theorem kurz_conjecture_sharp (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6) := by
  obtain ⟨g⟩ := exists_growth hS
  refine (volume_hull_le_growth g).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : S.card = g.count 0 + g.count 1 + g.count 2 + 1 := by
    rw [← g.card_eq, g.count_sum]
  have hs : g.s = g.count 0 + g.count 1 + g.count 2 := g.count_sum.symm
  have key := arith_ceil (g.count 0) (g.count 1) (g.count 2)
  have hp : g.pairs g.s = g.count 0 * g.count 1 + g.count 1 * g.count 2 + g.count 2 * g.count 0 :=
    rfl
  rw [hcard, hp, hs]
  push_cast at key ⊢
  linarith

/-- **Kurz's Conjecture 2.** For an edge-connected set of `n` hexagonal cells, the convex hull of
their union has area at most `⌊n² + 14n/3 + 1⌋ / 6`. -/
theorem kurz_conjecture (S : Finset Cell) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6) := by
  refine (kurz_conjecture_sharp S hS).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : (⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℤ) ≤ ⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ := by
    rw [Int.le_floor]
    have := Int.ceil_lt_add_one ((S.card : ℝ) ^ 2 + 14 / 3 * S.card)
    linarith
  have h2 : ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℤ) : ℝ)
      ≤ ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

end Polyhex
