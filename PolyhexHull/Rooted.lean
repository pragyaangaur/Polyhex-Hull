module

public import PolyhexHull.Structure
public import PolyhexHull.Walk

@[expose] public section

/-!
# Growth orders rooted at a minimiser of `form 2`

Suppose `W = 3s + m` and the width of `S` for `form 2` is `s + m`. Root a growth order at a cell
where `form 2` is smallest. Every tree edge then lies on the root chain of a maximiser of
`form 2`, so the tree is a single path `pt 0, pt 1, …, pt s`, and every step is one of
`d₁ = (1, 0)`, `d₂ = (0, 1)`, `d₃ = (1, -1)`. Along this path the tree path of `form k` is an
interval `(N k, M k]`, and the equality case of the width estimate pins down which steps lie in
which interval. When all three direction counts are positive this forces the step sequence
`A^x d₁^(y-x) B^(s-y)` with `{A, B} = {d₂, d₃}`.
-/

namespace Polyhex

open Finset

/-- Signed interval indicator: `1` on `(Y, X]`, `-1` on `(X, Y]`, `0` elsewhere. -/
def isg (i X Y : ℕ) : ℤ := (if i ≤ X then 1 else 0) - (if i ≤ Y then 1 else 0)

lemma root_term_le {e : Cell} (he : e ∈ units) (t : ℤ) (ht : t = 1 ∨ t = 0) :
    t * form 2 e ≤ 1 + if cls e = 0 then 1 else 0 := by
  simp only [units, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> decide

lemma root_term_eq {e : Cell} (he : e ∈ units) (t : ℤ) (ht : t = 1 ∨ t = 0)
    (h : t * form 2 e = 1 + if cls e = 0 then 1 else 0) :
    t = 1 ∧ (e = (1, 0) ∨ e = (0, 1) ∨ e = (1, -1)) := by
  simp only [units, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> revert h <;>
    decide

/-- The equality table for one edge whose step is `d₁`, `d₂` or `d₃` and which lies on the path of
`form 2` with positive increment. `s0`, `s1` are its signs for `form 0` and `form 1`. -/
lemma edge_table (e : Cell) (he : e = (1, 0) ∨ e = (0, 1) ∨ e = (1, -1)) (s0 s1 : ℤ)
    (h0 : s0 = 1 ∨ s0 = 0 ∨ s0 = -1) (h1 : s1 = 1 ∨ s1 = 0 ∨ s1 = -1)
    (hc : s0 * form 0 e + s1 * form 1 e + form 2 e
      = 3 + if 0 < s0 * form 0 e ∧ 0 < s1 * form 1 e then 1 else 0) :
    (e = (1, 0) → (0 < s0 * form 0 e ∧ 0 < s1 * form 1 e) → s0 = 1 ∧ s1 = 1) ∧
    (e = (0, 1) → ((0 < s0 * form 0 e ∧ 0 < s1 * form 1 e) → s0 = 1 ∧ s1 = -1) ∧
      (¬(0 < s0 * form 0 e ∧ 0 < s1 * form 1 e) → s0 = 1 ∧ s1 = 0)) ∧
    (e = (1, -1) → ((0 < s0 * form 0 e ∧ 0 < s1 * form 1 e) → s0 = -1 ∧ s1 = 1) ∧
      (¬(0 < s0 * form 0 e ∧ 0 < s1 * form 1 e) → s0 = 0 ∧ s1 = 1)) := by
  rcases he with rfl | rfl | rfl <;> rcases h0 with rfl | rfl | rfl <;>
    rcases h1 with rfl | rfl | rfl <;> revert hc <;> decide

lemma card_Icc_le (s x : ℕ) (hx : x ≤ s) : #{i ∈ Icc 1 s | i ≤ x} = x := by
  have : {i ∈ Icc 1 s | i ≤ x} = Icc 1 x := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

lemma card_Icc_mid (s x y : ℕ) (hy : y ≤ s) : #{i ∈ Icc 1 s | ¬ i ≤ x ∧ i ≤ y} = y - x := by
  have : {i ∈ Icc 1 s | ¬ i ≤ x ∧ i ≤ y} = Icc (x + 1) y := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

lemma card_Icc_gt (s y : ℕ) : #{i ∈ Icc 1 s | ¬ i ≤ y} = s - y := by
  have : {i ∈ Icc 1 s | ¬ i ≤ y} = Icc (y + 1) s := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

lemma cls_sw_std (b : Bool) (x y i : ℕ) :
    cls (sw b (std x y i)) =
      if i ≤ x then (if b then 2 else 1) else if i ≤ y then 0 else (if b then 1 else 2) := by
  unfold sw std
  cases b <;> split_ifs <;> decide

lemma pat_id {i N0 N1 M0 M1 : ℕ} {e : Cell} (_hi : 1 ≤ i) (hA : N0 ≤ N1) (hB : M0 ≤ M1)
    (key : (e = (1, 0) ∧ isg i M0 N0 = 1 ∧ isg i M1 N1 = 1) ∨
      (e = (0, 1) ∧ isg i M0 N0 = 1 ∧ isg i M1 N1 = 0) ∨
      (e = (1, -1) ∧ isg i M0 N0 = 0 ∧ isg i M1 N1 = 1)) :
    e = sw false (std (max N0 N1) (min M0 M1) i) := by
  simp only [sw, std]
  rcases key with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ <;> simp only [isg] at h0 h1 <;>
    split_ifs at h0 h1 <;> split_ifs <;> first | rfl | (exfalso; omega)

lemma pat_sig {i N0 N1 M0 M1 : ℕ} {e : Cell} (_hi : 1 ≤ i) (hA : N1 < N0) (hB : M1 < M0)
    (key : (e = (1, 0) ∧ isg i M0 N0 = 1 ∧ isg i M1 N1 = 1) ∨
      (e = (0, 1) ∧ isg i M0 N0 = 1 ∧ isg i M1 N1 = 0) ∨
      (e = (1, -1) ∧ isg i M0 N0 = 0 ∧ isg i M1 N1 = 1)) :
    e = sw true (std (max N0 N1) (min M0 M1) i) := by
  simp only [sw, std, ite_true]
  rcases key with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ <;> simp only [isg] at h0 h1 <;>
    split_ifs at h0 h1 <;> split_ifs <;> first | rfl | (exfalso; omega)

namespace Growth

variable {S : Finset Cell} (g : Growth S)

lemma exists_of_count {k : Fin 3} (h : 1 ≤ g.count k) : ∃ i ∈ Icc 1 g.s, cls (g.e i) = k := by
  by_contra hne
  push Not at hne
  have : g.count k = 0 := by
    unfold count; rw [card_eq_zero, filter_eq_empty_iff]; exact hne
  omega

lemma count_eq_zero {k : Fin 3} (h : ∀ i ∈ Icc 1 g.s, cls (g.e i) ≠ k) : g.count k = 0 := by
  unfold count; rw [card_eq_zero, filter_eq_empty_iff]; exact h

/-- **The rooted tree is a path.** Rooted at a minimiser of `form 2`, with width `s + m` for that
form, every edge lies on the root chain of the maximiser `M 2`, every step is `d₁`, `d₂` or `d₃`,
and the root chains are the initial intervals `chain j = {1, …, j}`. -/
theorem rooted_path {M N : Fin 3 → ℕ} (h : g.IsExt M N) (hN : N 2 = 0)
    (hw2 : wd 2 S = g.s + g.mm) :
    g.count 0 = g.mm ∧ (∀ i ∈ Icc 1 g.s, g.e i = (1, 0) ∨ g.e i = (0, 1) ∨ g.e i = (1, -1)) ∧
      (∀ j ≤ g.s, g.chain j = Icc 1 j) ∧ (∀ i ∈ Icc 1 g.s, i ∈ g.chain (M 2)) := by
  have hch0 : g.chain 0 = ∅ := g.chain_of_bad (by omega)
  have hwd : wd 2 S = ∑ i ∈ Icc 1 g.s, g.sgn (M 2) 0 i * form 2 (g.e i) := by
    unfold wd
    rw [← (h 2).2.2.1, ← (h 2).2.2.2, hN]
    exact g.form_diff 2 (h 2).1 (Nat.zero_le _)
  have hsg : ∀ i, g.sgn (M 2) 0 i = if i ∈ g.chain (M 2) then 1 else 0 := by
    intro i; simp [sgn, hch0]
  have ht : ∀ i, g.sgn (M 2) 0 i = 1 ∨ g.sgn (M 2) 0 i = 0 := by
    intro i; rw [hsg]; split_ifs <;> simp
  have hb : ∀ i ∈ Icc 1 g.s,
      g.sgn (M 2) 0 i * form 2 (g.e i) ≤ 1 + if cls (g.e i) = 0 then 1 else 0 := by
    intro i hi
    simp only [mem_Icc] at hi
    exact root_term_le (g.e_mem_units hi.1 hi.2) _ (ht i)
  have hsum : ∑ i ∈ Icc 1 g.s, ((1 : ℤ) + if cls (g.e i) = 0 then 1 else 0)
      = g.s + g.count 0 := by
    rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, sum_boole]
    simp [count]
  have hle := sum_le_sum hb
  have hc0 := g.count_le_mm 0
  have heq : ∑ i ∈ Icc 1 g.s, g.sgn (M 2) 0 i * form 2 (g.e i)
      = ∑ i ∈ Icc 1 g.s, ((1 : ℤ) + if cls (g.e i) = 0 then 1 else 0) := by omega
  have hpt := (sum_eq_sum_iff_of_le hb).mp heq
  have hte : ∀ i ∈ Icc 1 g.s,
      g.sgn (M 2) 0 i = 1 ∧ (g.e i = (1, 0) ∨ g.e i = (0, 1) ∨ g.e i = (1, -1)) := by
    intro i hi
    have hi' := hi
    simp only [mem_Icc] at hi'
    exact root_term_eq (g.e_mem_units hi'.1 hi'.2) _ (ht i) (hpt i hi)
  have hall : ∀ i ∈ Icc 1 g.s, i ∈ g.chain (M 2) := by
    intro i hi
    have := (hte i hi).1
    rw [hsg] at this
    by_contra hn
    simp [hn] at this
  refine ⟨by omega, fun i hi => (hte i hi).2, fun j hj => ?_, hall⟩
  ext i
  constructor
  · intro hi
    have := g.mem_chain_bounds hi
    simp only [mem_Icc]; omega
  · intro hi
    simp only [mem_Icc] at hi
    rcases g.chain_total (hall i (by simp; omega)) (hall j (by simp; omega)) with h1 | h1
    · exact h1
    · have := g.mem_chain_bounds h1
      have hij : i = j := by omega
      subst hij
      exact g.self_mem_chain hi.1 hj

/-- **The step pattern.** Rooted at a minimiser of `form 2`, with `W = 3s + m`, width `s + m` for
`form 2` and all three direction counts positive, the steps are `A^x d₁^(y-x) B^(s-y)` with
`(A, B) = (d₂, d₃)`, or the image of this pattern under `sig`, that is `(A, B) = (d₃, d₂)`. -/
theorem rooted_pattern (hroot : ∀ i ≤ g.s, form 2 (g.pt 0) ≤ form 2 (g.pt i))
    (hW : Wsum S = 3 * g.s + g.mm) (hw2 : wd 2 S = g.s + g.mm) (hm : 1 ≤ g.mm)
    (hc1 : 1 ≤ g.count 1) (hc2 : 1 ≤ g.count 2) :
    ∃ x y : ℕ, ∃ b : Bool, x < y ∧ y ≤ g.s ∧ ∀ i ∈ Icc 1 g.s, g.e i = sw b (std x y i) := by
  obtain ⟨M, N, h, hN⟩ := g.exists_ext 2 0 (Nat.zero_le _) hroot
  obtain ⟨hc0, hD, hch, hall⟩ := g.rooted_path h hN hw2
  obtain ⟨hc, d, hcd, hfd⟩ := g.eq_case h hW hm
  have hsg : ∀ k, ∀ i ∈ Icc 1 g.s, g.sgn (M k) (N k) i = isg i (M k) (N k) := by
    intro k i hi
    simp only [mem_Icc] at hi
    unfold sgn isg
    rw [hch _ (h k).1, hch _ (h k).2.1]
    simp [mem_Icc, hi.1]
  have hs2 : ∀ i ∈ Icc 1 g.s, g.sgn (M 2) (N 2) i = 1 := by
    intro i hi
    have hm2 := hall i hi
    rw [hch _ (h 2).1] at hm2
    simp only [mem_Icc] at hm2 hi
    rw [hsg 2 i (by simp; omega), hN]
    simp [isg, hm2.2, show ¬ i ≤ 0 by omega]
  -- the table, for every edge
  have tab : ∀ i ∈ Icc 1 g.s,
      (g.e i = (1, 0) → g.Full M N i → isg i (M 0) (N 0) = 1 ∧ isg i (M 1) (N 1) = 1) ∧
      (g.e i = (0, 1) → (g.Full M N i → isg i (M 0) (N 0) = 1 ∧ isg i (M 1) (N 1) = -1) ∧
        (¬ g.Full M N i → isg i (M 0) (N 0) = 1 ∧ isg i (M 1) (N 1) = 0)) ∧
      (g.e i = (1, -1) → (g.Full M N i → isg i (M 0) (N 0) = -1 ∧ isg i (M 1) (N 1) = 1) ∧
        (¬ g.Full M N i → isg i (M 0) (N 0) = 0 ∧ isg i (M 1) (N 1) = 1)) := by
    intro i hi
    have hf : g.Full M N i ↔ (0 < g.sgn (M 0) (N 0) i * form 0 (g.e i)
        ∧ 0 < g.sgn (M 1) (N 1) i * form 1 (g.e i)) := by
      constructor
      · intro hf; exact ⟨hf 0, hf 1⟩
      · rintro ⟨a, b⟩ k
        fin_cases k
        · exact a
        · exact b
        · show 0 < g.sgn (M 2) (N 2) i * form 2 (g.e i)
          rw [hs2 i hi]
          rcases hD i hi with he | he | he <;> rw [he] <;> decide
    have hci := hc i hi
    rw [cval, Fin.sum_univ_three, hs2 i hi, one_mul] at hci
    simp only [hf] at hci
    have T := edge_table (g.e i) (hD i hi) _ _ (g.sgn_cases _ _ _) (g.sgn_cases _ _ _) hci
    rw [hsg 0 i hi, hsg 1 i hi] at T
    simp only [hf]
    rw [hsg 0 i hi, hsg 1 i hi]
    exact T
  have hcl : ∀ i ∈ Icc 1 g.s, ∀ k, cls (g.e i) = k →
      (k = 0 → g.e i = (1, 0)) ∧ (k = 1 → g.e i = (0, 1)) ∧ (k = 2 → g.e i = (1, -1)) := by
    intro i hi k hk
    rcases hD i hi with he | he | he <;> rw [he] at hk ⊢ <;> subst hk <;> decide
  fin_cases d
  · -- the full class is the class of `d₁`
    simp only [Fin.zero_eta] at hcd hfd
    have key : ∀ i ∈ Icc 1 g.s,
        (g.e i = (1, 0) ∧ isg i (M 0) (N 0) = 1 ∧ isg i (M 1) (N 1) = 1) ∨
        (g.e i = (0, 1) ∧ isg i (M 0) (N 0) = 1 ∧ isg i (M 1) (N 1) = 0) ∨
        (g.e i = (1, -1) ∧ isg i (M 0) (N 0) = 0 ∧ isg i (M 1) (N 1) = 1) := by
      intro i hi
      obtain ⟨t1, t2, t3⟩ := tab i hi
      rcases hD i hi with he | he | he
      · exact Or.inl ⟨he, t1 he ((hfd i hi).mpr (by rw [he]; decide))⟩
      · refine Or.inr (Or.inl ⟨he, (t2 he).2 fun hf => ?_⟩)
        have := (hfd i hi).mp hf; rw [he] at this; exact absurd this (by decide)
      · refine Or.inr (Or.inr ⟨he, (t3 he).2 fun hf => ?_⟩)
        have := (hfd i hi).mp hf; rw [he] at this; exact absurd this (by decide)
    obtain ⟨i₁, hi₁, hcl₁⟩ := g.exists_of_count (k := 0) (by omega)
    have he₁ := (hcl i₁ hi₁ 0 hcl₁).1 rfl
    have hk₁ := key i₁ hi₁
    rw [he₁] at hk₁
    simp only [Prod.mk.injEq] at hk₁
    have hb₁ : isg i₁ (M 0) (N 0) = 1 ∧ isg i₁ (M 1) (N 1) = 1 := by
      rcases hk₁ with ⟨-, h1⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨-, h⟩, -⟩
      · exact h1
      · omega
      · omega
    simp only [isg] at hb₁
    have hM0 := (h 0).1
    have hM1 := (h 1).1
    simp only [mem_Icc] at hi₁
    refine ⟨max (N 0) (N 1), min (M 0) (M 1), decide (N 1 < N 0), ?_, ?_, ?_⟩
    · split_ifs at hb₁ <;> omega
    · omega
    · -- the two mixed cases contradict a positive count
      have no3 : N 0 ≤ N 1 → M 1 < M 0 → False := by
        intro ha hb
        obtain ⟨i, hi, hci⟩ := g.exists_of_count (k := 2) hc2
        have he := (hcl i hi 2 hci).2.2 rfl
        have hk := key i hi
        rw [he] at hk
        simp only [Prod.mk.injEq] at hk
        rcases hk with ⟨⟨-, h⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨-, h0, h1⟩
        · omega
        · omega
        · simp only [isg] at h0 h1
          simp only [mem_Icc] at hi
          split_ifs at h0 h1 <;> omega
      have no2 : N 1 < N 0 → M 0 ≤ M 1 → False := by
        intro ha hb
        obtain ⟨i, hi, hci⟩ := g.exists_of_count (k := 1) hc1
        have he := (hcl i hi 1 hci).2.1 rfl
        have hk := key i hi
        rw [he] at hk
        simp only [Prod.mk.injEq] at hk
        rcases hk with ⟨⟨h, -⟩, -⟩ | ⟨-, h0, h1⟩ | ⟨⟨h, -⟩, -⟩
        · omega
        · simp only [isg] at h0 h1
          simp only [mem_Icc] at hi
          split_ifs at h0 h1 <;> omega
        · omega
      intro i hi
      have hi' := hi
      simp only [mem_Icc] at hi'
      by_cases hA : N 1 < N 0 <;> by_cases hB : M 1 < M 0
      · rw [decide_eq_true hA]; exact pat_sig hi'.1 hA hB (key i hi)
      · exact absurd (no2 hA (by omega)) id
      · exact absurd (no3 (by omega) hB) id
      · rw [decide_eq_false hA]; exact pat_id hi'.1 (by omega) (by omega) (key i hi)
  · -- the full class is the class of `d₂`: then there is no `d₃` edge
    exfalso
    simp only [Fin.mk_one] at hcd hfd
    obtain ⟨i₀, hi₀, hcl₀⟩ := g.exists_of_count (k := 1) hc1
    have he₀ := (hcl i₀ hi₀ 1 hcl₀).2.1 rfl
    have hA := ((tab i₀ hi₀).2.1 he₀).1 ((hfd i₀ hi₀).mpr hcl₀)
    obtain ⟨i, hi, hci⟩ := g.exists_of_count (k := 2) hc2
    have he := (hcl i hi 2 hci).2.2 rfl
    have hB := ((tab i hi).2.2 he).2 fun hf => by
      have := (hfd i hi).mp hf; rw [hci] at this; exact absurd this (by decide)
    simp only [isg] at hA hB
    simp only [mem_Icc] at hi hi₀
    split_ifs at hA hB <;> omega
  · -- the full class is the class of `d₃`: then there is no `d₂` edge
    exfalso
    simp only [Fin.reduceFinMk] at hcd hfd
    obtain ⟨i₀, hi₀, hcl₀⟩ := g.exists_of_count (k := 2) hc2
    have he₀ := (hcl i₀ hi₀ 2 hcl₀).2.2 rfl
    have hA := ((tab i₀ hi₀).2.2 he₀).1 ((hfd i₀ hi₀).mpr hcl₀)
    obtain ⟨i, hi, hci⟩ := g.exists_of_count (k := 1) hc1
    have he := (hcl i hi 1 hci).2.1 rfl
    have hB := ((tab i hi).2.1 he).2 fun hf => by
      have := (hfd i hi).mp hf; rw [hci] at this; exact absurd this (by decide)
    simp only [isg] at hA hB
    simp only [mem_Icc] at hi hi₀
    split_ifs at hA hB <;> omega

end Growth

end Polyhex
