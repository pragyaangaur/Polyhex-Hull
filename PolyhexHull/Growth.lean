import PolyhexHull.Defs

/-!
# Growth orders (rooted spanning trees)

A connected polyhex can be listed as `pt 0, pt 1, …, pt s` so that every `pt j` with `j ≥ 1` is
adjacent to an earlier cell `pt (par j)`. The steps `e j = pt j - pt (par j)` are the edges of a
rooted spanning tree. We use this in place of graph-theoretic spanning trees.

The root chain `chain j` is the set of indices on the tree path from `j` up to the root (the root
itself excluded). Two basic facts drive the width estimate:
* `pt j = pt 0 + ∑ i ∈ chain j, e i`;
* any two indices on a common chain are comparable.
-/

namespace Polyhex

open Finset

structure Growth (S : Finset Cell) where
  s : ℕ
  pt : ℕ → Cell
  par : ℕ → ℕ
  par_lt : ∀ j, 1 ≤ j → j ≤ s → par j < j
  step : ∀ j, 1 ≤ j → j ≤ s → pt j - pt (par j) ∈ units
  image_eq : (range (s + 1)).image pt = S
  injOn : Set.InjOn pt (range (s + 1))

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- The tree edge ending at `j`. -/
def e (j : ℕ) : Cell := g.pt j - g.pt (g.par j)

lemma card_eq : g.s + 1 = S.card := by
  have h := card_image_of_injOn g.injOn
  rw [g.image_eq, card_range] at h
  exact h.symm

lemma pt_mem {i : ℕ} (hi : i ≤ g.s) : g.pt i ∈ S := by
  have h := mem_image_of_mem g.pt (show i ∈ range (g.s + 1) by simp; omega)
  rwa [g.image_eq] at h

lemma mem_iff {c : Cell} : c ∈ S ↔ ∃ i ≤ g.s, g.pt i = c := by
  constructor
  · intro hc
    have h := hc
    rw [← g.image_eq, mem_image] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨i, by simp at hi; omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact g.pt_mem hi

/-- The indices on the path from `j` to the root, excluding the root. -/
def chain (j : ℕ) : Finset ℕ :=
  if _h : 1 ≤ j ∧ j ≤ g.s then insert j (chain (g.par j)) else ∅
termination_by j
decreasing_by exact g.par_lt j _h.1 _h.2

lemma chain_of_good {j : ℕ} (h : 1 ≤ j ∧ j ≤ g.s) : g.chain j = insert j (g.chain (g.par j)) := by
  rw [chain]; simp [h]

lemma chain_of_bad {j : ℕ} (h : ¬ (1 ≤ j ∧ j ≤ g.s)) : g.chain j = ∅ := by
  rw [chain]; simp [h]

lemma mem_chain_bounds {j i : ℕ} (hi : i ∈ g.chain j) : 1 ≤ i ∧ i ≤ j ∧ j ≤ g.s := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h : 1 ≤ j ∧ j ≤ g.s
    · rw [g.chain_of_good h, mem_insert] at hi
      rcases hi with rfl | hi
      · exact ⟨h.1, le_rfl, h.2⟩
      · have hp := g.par_lt j h.1 h.2
        obtain ⟨h1, h2, _⟩ := ih _ hp hi
        exact ⟨h1, by omega, h.2⟩
    · rw [g.chain_of_bad h] at hi; simp at hi

lemma self_mem_chain {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ g.s) : j ∈ g.chain j := by
  rw [g.chain_of_good ⟨h1, h2⟩]; exact mem_insert_self _ _

lemma chain_subset {i j : ℕ} (hi : i ∈ g.chain j) : g.chain i ⊆ g.chain j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h : 1 ≤ j ∧ j ≤ g.s
    · rw [g.chain_of_good h, mem_insert] at hi
      rw [g.chain_of_good h]
      rcases hi with rfl | hi
      · rw [g.chain_of_good h]
      · exact (ih _ (g.par_lt j h.1 h.2) hi).trans (subset_insert _ _)
    · rw [g.chain_of_bad h] at hi; simp at hi

lemma chain_total {i i' j : ℕ} (hi : i ∈ g.chain j) (hi' : i' ∈ g.chain j) :
    i ∈ g.chain i' ∨ i' ∈ g.chain i := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h : 1 ≤ j ∧ j ≤ g.s
    · rw [g.chain_of_good h, mem_insert] at hi hi'
      rcases hi with rfl | hi
      · right; rw [g.chain_of_good h]; exact hi'.elim (fun h' => h' ▸ mem_insert_self _ _)
          (fun h' => mem_insert_of_mem h')
      · rcases hi' with rfl | hi'
        · left; rw [g.chain_of_good h]; exact mem_insert_of_mem hi
        · exact ih _ (g.par_lt j h.1 h.2) hi hi'
    · rw [g.chain_of_bad h] at hi; simp at hi

lemma pt_eq_sum {j : ℕ} (hj : j ≤ g.s) : g.pt j = g.pt 0 + ∑ i ∈ g.chain j, g.e i := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h1 : 1 ≤ j
    · have h : 1 ≤ j ∧ j ≤ g.s := ⟨h1, hj⟩
      have hp := g.par_lt j h1 hj
      have hnot : j ∉ g.chain (g.par j) := fun hm => by
        have := g.mem_chain_bounds hm; omega
      rw [g.chain_of_good h, sum_insert hnot, ← add_assoc, add_comm (g.pt 0), add_assoc,
        ← ih _ hp (by omega), e]
      abel
    · have : j = 0 := by omega
      subst this
      rw [g.chain_of_bad (by omega)]; simp

lemma e_mem_units {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ g.s) : g.e i ∈ units := g.step i h1 h2

end Growth

end Polyhex
