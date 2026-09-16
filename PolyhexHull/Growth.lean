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

/-! ### Widths -/

/-- Sign of the edge `i` on the tree path from `N` to `M`. -/
def sgn (M N i : ℕ) : ℤ := (if i ∈ g.chain M then 1 else 0) - (if i ∈ g.chain N then 1 else 0)

lemma form_diff (k : Fin 3) {M N : ℕ} (hM : M ≤ g.s) (hN : N ≤ g.s) :
    form k (g.pt M) - form k (g.pt N)
      = ∑ i ∈ Icc 1 g.s, g.sgn M N i * form k (g.e i) := by
  have hsub : ∀ J, J ≤ g.s → g.chain J ⊆ Icc 1 g.s := fun J _ i hi => by
    have := g.mem_chain_bounds hi; simp only [mem_Icc]; omega
  rw [g.pt_eq_sum hM, g.pt_eq_sum hN, form_add, form_add, form_sum, form_sum]
  simp only [sgn, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, ← sum_filter, filter_mem_eq_inter, filter_mem_eq_inter,
    inter_eq_right.mpr (hsub M hM), inter_eq_right.mpr (hsub N hN)]
  ring

/-- Per-edge bound: the contribution of one edge to the sum of the three widths. -/
lemma edge_contrib (e : Cell) (he : e ∈ units) (σ : Fin 3 → ℤ)
    (hσ : ∀ k, σ k = 1 ∨ σ k = 0 ∨ σ k = -1) :
    ∑ k, σ k * form k e ≤ 3 + if (∀ k, 0 < σ k * form k e) then 1 else 0 := by
  simp only [units, mem_insert, mem_singleton] at he
  rw [Fin.sum_univ_three]
  split_ifs with hall
  · rcases hσ 0 with h0 | h0 | h0 <;> rcases hσ 1 with h1 | h1 | h1 <;>
      rcases hσ 2 with h2 | h2 | h2 <;>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [h0, h1, h2, form] <;> omega
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    rcases hσ 0 with h0 | h0 | h0 <;> rcases hσ 1 with h1 | h1 | h1 <;>
      rcases hσ 2 with h2 | h2 | h2 <;>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases k <;> simp only [h0, h1, h2, form, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk ⊢ <;>
      omega

/-- Two full edges whose sign patterns agree up to a global sign are parallel. -/
lemma cls_eq_of_full (e e' : Cell) (he : e ∈ units) (he' : e' ∈ units) (σ τ : Fin 3 → ℤ)
    (hf : ∀ k, 0 < σ k * form k e) (hf' : ∀ k, 0 < τ k * form k e')
    (hστ : (∀ k, τ k = σ k) ∨ (∀ k, τ k = -σ k)) : cls e = cls e' := by
  simp only [units, mem_insert, mem_singleton] at he he'
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
  have h0' := hf' 0; have h1' := hf' 1; have h2' := hf' 2
  rcases hστ with h | h <;> rw [h 0] at h0' <;> rw [h 1] at h1' <;> rw [h 2] at h2' <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [form, cls] at h0 h1 h2 h0' h1' h2' ⊢ <;> nlinarith

lemma sgn_cases (M N i : ℕ) : g.sgn M N i = 1 ∨ g.sgn M N i = 0 ∨ g.sgn M N i = -1 := by
  unfold sgn; split_ifs <;> simp

/-- The sign patterns of two edges that are nonzero in every coordinate agree up to sign. -/
lemma sgn_pattern (M N : Fin 3 → ℕ) {i i' : ℕ}
    (hi : ∀ k, g.sgn (M k) (N k) i ≠ 0) (hi' : ∀ k, g.sgn (M k) (N k) i' ≠ 0) :
    (∀ k, g.sgn (M k) (N k) i' = g.sgn (M k) (N k) i)
      ∨ (∀ k, g.sgn (M k) (N k) i' = -g.sgn (M k) (N k) i) := by
  -- each nonzero sign means membership in exactly one of the two chains
  have one : ∀ k j, g.sgn (M k) (N k) j ≠ 0 →
      (j ∈ g.chain (M k) ∧ j ∉ g.chain (N k)) ∨ (j ∉ g.chain (M k) ∧ j ∈ g.chain (N k)) := by
    intro k j hj
    unfold sgn at hj
    by_cases a : j ∈ g.chain (M k) <;> by_cases b : j ∈ g.chain (N k) <;> simp_all
  have val : ∀ k j, g.sgn (M k) (N k) j =
      (if j ∈ g.chain (M k) then 1 else 0) - (if j ∈ g.chain (N k) then 1 else 0) := fun _ _ => rfl
  by_cases hc : i ∈ g.chain i' ∨ i' ∈ g.chain i
  · left
    intro k
    rcases one k i (hi k) with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases one k i' (hi' k) with ⟨c, d⟩ | ⟨c, d⟩
    · rw [val, val]; simp [a, b, c, d]
    · exfalso
      rcases hc with hc | hc
      · exact b (g.chain_subset d hc)
      · exact c (g.chain_subset a hc)
    · exfalso
      rcases hc with hc | hc
      · exact a (g.chain_subset c hc)
      · exact d (g.chain_subset b hc)
    · rw [val, val]; simp [a, b, c, d]
  · right
    intro k
    push Not at hc
    rcases one k i (hi k) with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases one k i' (hi' k) with ⟨c, d⟩ | ⟨c, d⟩
    · exact absurd (g.chain_total a c) (by tauto)
    · rw [val, val]; simp [a, b, c, d]
    · rw [val, val]; simp [a, b, c, d]
    · exact absurd (g.chain_total b d) (by tauto)

/-- Number of tree edges in direction class `d`. -/
def count (d : Fin 3) : ℕ := #{i ∈ Icc 1 g.s | cls (g.e i) = d}

lemma count_sum : g.count 0 + g.count 1 + g.count 2 = g.s := by
  have h := card_eq_sum_card_fiberwise (f := fun i => cls (g.e i)) (s := Icc 1 g.s)
    (t := univ) (fun _ _ => mem_univ _)
  simp only [Fin.sum_univ_three, Nat.card_Icc, add_tsub_cancel_right] at h
  simp only [count]
  omega

/-- The width estimate: `w₀ + w₁ + w₂ ≤ 3s + max(a, b, c)`. -/
theorem width_sum_le (M N : Fin 3 → ℕ) (hM : ∀ k, M k ≤ g.s) (hN : ∀ k, N k ≤ g.s) :
    ∑ k, (form k (g.pt (M k)) - form k (g.pt (N k)))
      ≤ 3 * g.s + max (g.count 0) (max (g.count 1) (g.count 2)) := by
  classical
  simp_rw [g.form_diff _ (hM _) (hN _)]
  rw [sum_comm]
  set σ : ℕ → Fin 3 → ℤ := fun i k => g.sgn (M k) (N k) i with hσ
  let full : ℕ → Prop := fun i => ∀ k, 0 < σ i k * form k (g.e i)
  have hle : ∀ i ∈ Icc 1 g.s,
      ∑ k, g.sgn (M k) (N k) i * form k (g.e i) ≤ 3 + if full i then 1 else 0 := by
    intro i hi
    simp only [mem_Icc] at hi
    exact edge_contrib _ (g.e_mem_units hi.1 hi.2) (σ i) (fun k => g.sgn_cases _ _ _)
  refine (sum_le_sum hle).trans ?_
  rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, sum_boole]
  simp only [nsmul_eq_mul]
  -- all full edges are parallel
  by_cases hex : ∃ i₀ ∈ Icc 1 g.s, full i₀
  · obtain ⟨i₀, hi₀, hf₀⟩ := hex
    have hsub : {i ∈ Icc 1 g.s | full i} ⊆ {i ∈ Icc 1 g.s | cls (g.e i) = cls (g.e i₀)} := by
      intro i hi
      simp only [mem_filter, mem_Icc] at hi hi₀ ⊢
      refine ⟨hi.1, ?_⟩
      have nz : ∀ j, full j → ∀ k, g.sgn (M k) (N k) j ≠ 0 := fun j hj k h0 => by
        have := hj k; simp only [hσ, h0, zero_mul, lt_self_iff_false] at this
      refine (cls_eq_of_full _ _ (g.e_mem_units hi₀.1 hi₀.2) (g.e_mem_units hi.1.1 hi.1.2)
        (σ i₀) (σ i) hf₀ hi.2 ?_).symm
      exact g.sgn_pattern M N (nz _ hf₀) (nz _ hi.2)
    have hc := card_le_card hsub
    have hm : #{i ∈ Icc 1 g.s | cls (g.e i) = cls (g.e i₀)}
        ≤ max (g.count 0) (max (g.count 1) (g.count 2)) := by
      have : #{i ∈ Icc 1 g.s | cls (g.e i) = cls (g.e i₀)} = g.count (cls (g.e i₀)) := rfl
      rw [this]
      generalize cls (g.e i₀) = d
      fin_cases d <;> simp
    have : (#{i ∈ Icc 1 g.s | full i} : ℤ) ≤ max (g.count 0) (max (g.count 1) (g.count 2)) := by
      exact_mod_cast hc.trans hm
    push_cast at this ⊢
    linarith
  · push Not at hex
    have : {i ∈ Icc 1 g.s | full i} = ∅ := filter_eq_empty_iff.mpr (fun i hi => hex i hi)
    rw [this, card_empty]
    push_cast
    have : (0 : ℤ) ≤ max (g.count 0 : ℤ) (max (g.count 1) (g.count 2)) := by positivity
    linarith

end Growth

end Polyhex
