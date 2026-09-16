import PolyhexHull.Transport

/-!
# The hexagon as a zonotope

The central cell is `z + [0, g₁] + [0, g₂] + [0, g₃]` with `z = (-1/3, -1/3)`, `g₁ = (2/3, -1/3)`,
`g₂ = (1/3, 1/3)` and `g₃ = (-1/3, 2/3)`.
-/

namespace Polyhex

open MeasureTheory Set
open scoped Pointwise

noncomputable def z0 : ℝ × ℝ := (-1/3, -1/3)
noncomputable def g1 : ℝ × ℝ := (2/3, -1/3)
noncomputable def g2 : ℝ × ℝ := (1/3, 1/3)
noncomputable def g3 : ℝ × ℝ := (-1/3, 2/3)

lemma zero_mem_hexagon : (0 : ℝ × ℝ) ∈ hexagon := by
  have h1 : ((1/3 : ℝ), (1/3 : ℝ)) ∈ hexagon := subset_convexHull ℝ _ (by simp [hexVertices])
  have h2 : ((-1/3 : ℝ), (-1/3 : ℝ)) ∈ hexagon := subset_convexHull ℝ _ (by simp [hexVertices])
  have := (convex_convexHull ℝ hexVertices) h1 h2 (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have e : (0 : ℝ × ℝ) = (1/2 : ℝ) • ((1/3 : ℝ), (1/3 : ℝ)) + (1/2 : ℝ) • ((-1/3 : ℝ), (-1/3 : ℝ)) := by
    ext <;> norm_num
  rw [e]; exact this

lemma hexagon_eq_zonotope :
    hexagon = {z0} + segment ℝ 0 g1 + segment ℝ 0 g2 + segment ℝ 0 g3 := by
  apply Subset.antisymm
  · -- the zonotope is convex and contains the six vertices
    have hconv : Convex ℝ ({z0} + segment ℝ 0 g1 + segment ℝ 0 g2 + segment ℝ 0 g3) :=
      (((convex_singleton z0).add (convex_segment 0 g1)).add (convex_segment 0 g2)).add
        (convex_segment 0 g3)
    refine convexHull_min ?_ hconv
    have mem : ∀ a b c : Bool,
        z0 + (if a then g1 else 0) + (if b then g2 else 0) + (if c then g3 else 0)
          ∈ {z0} + segment ℝ 0 g1 + segment ℝ 0 g2 + segment ℝ 0 g3 := by
      intro a b c
      refine add_mem_add (add_mem_add (add_mem_add (mem_singleton _) ?_) ?_) ?_ <;>
        split_ifs <;> first | exact left_mem_segment ℝ _ _ | exact right_mem_segment ℝ _ _
    intro p hp
    simp only [hexVertices, mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · convert mem true true true using 1; norm_num [z0, g1, g2, g3]
    · convert mem false true true using 1; norm_num [z0, g1, g2, g3]
    · convert mem false false true using 1; norm_num [z0, g1, g2, g3]
    · convert mem false false false using 1; norm_num [z0, g1, g2, g3]
    · convert mem true false false using 1; norm_num [z0, g1, g2, g3]
    · convert mem true true false using 1; norm_num [z0, g1, g2, g3]
  · -- the zonotope is the convex hull of eight points, all in the hexagon
    rw [← convexHull_pair (𝕜 := ℝ) 0 g1, ← convexHull_pair (𝕜 := ℝ) 0 g2,
      ← convexHull_pair (𝕜 := ℝ) 0 g3, ← convexHull_singleton (𝕜 := ℝ) z0,
      ← convexHull_add, ← convexHull_add, ← convexHull_add]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro p ⟨q, ⟨r, ⟨t, ht, w1, hw1, rfl⟩, w2, hw2, rfl⟩, w3, hw3, rfl⟩
    simp only [mem_singleton_iff, mem_insert_iff] at ht hw1 hw2 hw3
    subst ht
    have V : ∀ x ∈ hexVertices, x ∈ hexagon := fun x hx => subset_convexHull ℝ _ hx
    rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl <;> rcases hw3 with rfl | rfl
    · convert V _ (by simp [hexVertices] : ((-1/3 : ℝ), (-1/3 : ℝ)) ∈ hexVertices) using 1
      simp [z0]
    · convert V _ (by simp [hexVertices] : ((-2/3 : ℝ), (1/3 : ℝ)) ∈ hexVertices) using 1
      simp [z0, g3]; norm_num
    · convert zero_mem_hexagon using 1; simp [z0, g2]; norm_num
    · convert V _ (by simp [hexVertices] : ((-1/3 : ℝ), (2/3 : ℝ)) ∈ hexVertices) using 1
      simp [z0, g2, g3]; norm_num
    · convert V _ (by simp [hexVertices] : ((1/3 : ℝ), (-2/3 : ℝ)) ∈ hexVertices) using 1
      simp [z0, g1]; norm_num
    · convert zero_mem_hexagon using 1; simp [z0, g1, g3]; norm_num
    · convert V _ (by simp [hexVertices] : ((2/3 : ℝ), (-1/3 : ℝ)) ∈ hexVertices) using 1
      simp [z0, g1, g2]; norm_num
    · convert V _ (by simp [hexVertices] : ((1/3 : ℝ), (1/3 : ℝ)) ∈ hexVertices) using 1
      norm_num [z0, g1, g2, g3]

lemma convex_hexagon : Convex ℝ hexagon := convex_convexHull ℝ _

end Polyhex
