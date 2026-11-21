module

public import PolyhexHull.Equality

@[expose] public section

/-!
# The structure forced by `W = 3s + m`

For a growth order with extremal indices `M`, `N`, the width sum splits as a sum of edge
contributions `cval i ≤ 3 + [edge i is full]`. If `W = 3s + m` with `m ≥ 1`, every contribution is
exactly `3 + [full]`, and the full edges are exactly the edges of one direction class `d`, which
has `m` edges.

An exclusion argument (the four quadrants of two tree edges cannot all contain tokens) then shows
that every edge lies on the tree path of the form `form (d + 2)`, the form whose increment along
class `d` is `±2`, and is crossed in the positive direction. Hence the width of `S` for that form
is exactly `s + m`.
-/

namespace Polyhex

open Finset

/-- Signed indicator of two booleans. -/
def sgb (a b : Bool) : ℤ := (if a then 1 else 0) - (if b then 1 else 0)

/-- Pick one of three values by an index. -/
def pick {α : Type} : Fin 3 → α → α → α → α
  | 0 => fun a _ _ => a
  | 1 => fun _ b _ => b
  | 2 => fun _ _ c => c

lemma pick_fn {α : Type} (f : Fin 3 → α) (k : Fin 3) : pick k (f 0) (f 1) (f 2) = f k := by
  fin_cases k <;> rfl

set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 4000000 in
/-- The finite core of the exclusion argument. `X, Y` record which root chains contain a full edge
`i₀` (with step `e₀`) and `x, y` the same for another edge `i` (with step `e`). The three
alternatives in the hypothesis say that `i₀` lies below `i`, that `i` lies below `i₀`, or that the
two edges share no root chain. -/
lemma excl_core (e₀ e : Cell) (he₀ : e₀ ∈ units) (he : e ∈ units) :
    ∀ X0 Y0 X1 Y1 X2 Y2 : Bool,
      (0 < sgb X0 Y0 * form 0 e₀ ∧ 0 < sgb X1 Y1 * form 1 e₀ ∧ 0 < sgb X2 Y2 * form 2 e₀) →
    ∀ x0 y0 x1 y1 x2 y2 : Bool,
      3 ≤ sgb x0 y0 * form 0 e + sgb x1 y1 * form 1 e + sgb x2 y2 * form 2 e →
      (((x0 → X0) ∧ (y0 → Y0) ∧ (x1 → X1) ∧ (y1 → Y1) ∧ (x2 → X2) ∧ (y2 → Y2)) ∨
       ((X0 → x0) ∧ (Y0 → y0) ∧ (X1 → x1) ∧ (Y1 → y1) ∧ (X2 → x2) ∧ (Y2 → y2)) ∨
       (¬(X0 ∧ x0) ∧ ¬(Y0 ∧ y0) ∧ ¬(X1 ∧ x1) ∧ ¬(Y1 ∧ y1) ∧ ¬(X2 ∧ x2) ∧ ¬(Y2 ∧ y2))) →
      0 < sgb (pick (cls e₀ + 2) x0 x1 x2) (pick (cls e₀ + 2) y0 y1 y2)
        * form (cls e₀ + 2) e := by
  simp only [units, mem_insert, mem_singleton] at he₀ he
  rcases he₀ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- For a unit step, a positive signed increment of the form `form (d + 2)` equals its absolute
value, which is `2` on the class `d` and `1` otherwise. -/
lemma term_eq {e : Cell} (he : e ∈ units) (d : Fin 3) (t : ℤ) (ht : t = 1 ∨ t = 0 ∨ t = -1)
    (hp : 0 < t * form (d + 2) e) : t * form (d + 2) e = if cls e = d then 2 else 1 := by
  simp only [units, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases d <;>
    rcases ht with rfl | rfl | rfl <;> revert hp <;> decide

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- The contribution of edge `i` to the width sum. -/
def cval (M N : Fin 3 → ℕ) (i : ℕ) : ℤ := ∑ k, g.sgn (M k) (N k) i * form k (g.e i)

/-- An edge is full when it lies on all three paths, each crossing it with positive increment. -/
def Full (M N : Fin 3 → ℕ) (i : ℕ) : Prop := ∀ k, 0 < g.sgn (M k) (N k) i * form k (g.e i)

instance (M N : Fin 3 → ℕ) (i : ℕ) : Decidable (g.Full M N i) :=
  inferInstanceAs (Decidable (∀ k : Fin 3, 0 < g.sgn (M k) (N k) i * form k (g.e i)))

lemma sgn_eq_sgb (M N i : ℕ) :
    g.sgn M N i = sgb (decide (i ∈ g.chain M)) (decide (i ∈ g.chain N)) := by
  unfold sgn sgb; simp

lemma Wsum_eq_sum_cval {M N : Fin 3 → ℕ} (h : g.IsExt M N) :
    Wsum S = ∑ i ∈ Icc 1 g.s, g.cval M N i := by
  rw [g.Wsum_eq h]
  simp_rw [g.form_diff _ (h _).1 (h _).2.1]
  rw [sum_comm]
  rfl

lemma full_cls {M N : Fin 3 → ℕ} {i i' : ℕ} (hi : i ∈ Icc 1 g.s) (hi' : i' ∈ Icc 1 g.s)
    (hf : g.Full M N i) (hf' : g.Full M N i') : cls (g.e i) = cls (g.e i') := by
  simp only [mem_Icc] at hi hi'
  have nz : ∀ j, g.Full M N j → ∀ k, g.sgn (M k) (N k) j ≠ 0 := fun j hj k h0 => by
    have := hj k; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  exact cls_eq_of_full _ _ (g.e_mem_units hi.1 hi.2) (g.e_mem_units hi'.1 hi'.2) _ _ hf hf'
    (g.sgn_pattern M N (nz _ hf) (nz _ hf'))

lemma count_le_mm (d : Fin 3) : g.count d ≤ g.mm := by
  unfold mm; fin_cases d <;> simp

/-- **Equality case of the width estimate.** If `W = 3s + m` with `m ≥ 1`, every edge contributes
exactly `3 + [full]`, and the full edges are exactly the edges of one class `d` with `m` edges. -/
theorem eq_case {M N : Fin 3 → ℕ} (h : g.IsExt M N) (hW : Wsum S = 3 * g.s + g.mm)
    (hm : 1 ≤ g.mm) :
    (∀ i ∈ Icc 1 g.s, g.cval M N i = 3 + if g.Full M N i then 1 else 0) ∧
      ∃ d, g.count d = g.mm ∧ ∀ i ∈ Icc 1 g.s, (g.Full M N i ↔ cls (g.e i) = d) := by
  have hle : ∀ i ∈ Icc 1 g.s, g.cval M N i ≤ 3 + if g.Full M N i then 1 else 0 := by
    intro i hi
    simp only [mem_Icc] at hi
    exact edge_contrib _ (g.e_mem_units hi.1 hi.2) _ (fun k => g.sgn_cases _ _ _)
  have hsum : ∑ i ∈ Icc 1 g.s, ((3 : ℤ) + if g.Full M N i then 1 else 0)
      = 3 * g.s + #{i ∈ Icc 1 g.s | g.Full M N i} := by
    rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, sum_boole]
    simp [mul_comm]
  have hW' := g.Wsum_eq_sum_cval h
  have hcle : ∑ i ∈ Icc 1 g.s, g.cval M N i
      ≤ ∑ i ∈ Icc 1 g.s, ((3 : ℤ) + if g.Full M N i then 1 else 0) := sum_le_sum hle
  obtain ⟨i₀, hi₀, hf₀⟩ : ∃ i₀ ∈ Icc 1 g.s, g.Full M N i₀ := by
    by_contra hne
    push Not at hne
    have : {i ∈ Icc 1 g.s | g.Full M N i} = ∅ := filter_eq_empty_iff.mpr hne
    rw [this, card_empty] at hsum
    omega
  set d := cls (g.e i₀) with hd
  have hsub : {i ∈ Icc 1 g.s | g.Full M N i} ⊆ {i ∈ Icc 1 g.s | cls (g.e i) = d} := by
    intro i hi
    simp only [mem_filter] at hi ⊢
    exact ⟨hi.1, g.full_cls hi.1 hi₀ hi.2 hf₀⟩
  have hcd : #{i ∈ Icc 1 g.s | cls (g.e i) = d} = g.count d := rfl
  have hdm := g.count_le_mm d
  have hc1 := card_le_card hsub
  have hfe : #{i ∈ Icc 1 g.s | g.Full M N i} = g.count d := by omega
  refine ⟨fun i hi => ?_, d, by omega, ?_⟩
  · have heq : ∑ i ∈ Icc 1 g.s, g.cval M N i
        = ∑ i ∈ Icc 1 g.s, ((3 : ℤ) + if g.Full M N i then 1 else 0) := by omega
    exact (sum_eq_sum_iff_of_le hle).mp heq i hi
  · have hset := eq_of_subset_of_card_le hsub (by omega)
    intro i hi
    constructor
    · intro hf
      have : i ∈ {i ∈ Icc 1 g.s | g.Full M N i} := mem_filter.mpr ⟨hi, hf⟩
      rw [hset] at this
      exact (mem_filter.mp this).2
    · intro hc
      have : i ∈ {i ∈ Icc 1 g.s | cls (g.e i) = d} := mem_filter.mpr ⟨hi, hc⟩
      rw [← hset] at this
      exact (mem_filter.mp this).2

/-- **The wide form.** If `W = 3s + m` with `m ≥ 1`, then for the full class `d` every tree edge
lies on the path of `form (d + 2)` and is crossed with positive increment, so the width of `S` for
that form is `s + m`. -/
theorem exists_wide {M N : Fin 3 → ℕ} (h : g.IsExt M N) (hW : Wsum S = 3 * g.s + g.mm)
    (hm : 1 ≤ g.mm) : ∃ k, wd k S = g.s + g.mm := by
  classical
  obtain ⟨hc, d, hcd, hfd⟩ := g.eq_case h hW hm
  obtain ⟨i₀, hi₀, hd₀⟩ : ∃ i₀ ∈ Icc 1 g.s, cls (g.e i₀) = d := by
    by_contra hne
    push Not at hne
    have : g.count d = 0 := by
      unfold count; rw [card_eq_zero, filter_eq_empty_iff]; exact hne
    omega
  have hf₀ := (hfd i₀ hi₀).mpr hd₀
  have hi₀' := hi₀
  simp only [mem_Icc] at hi₀'
  have hpos : ∀ i ∈ Icc 1 g.s, 0 < g.sgn (M (d + 2)) (N (d + 2)) i * form (d + 2) (g.e i) := by
    intro i hi
    have hi' := hi
    simp only [mem_Icc] at hi'
    have rel : (∀ X, i ∈ g.chain X → i₀ ∈ g.chain X) ∨ (∀ X, i₀ ∈ g.chain X → i ∈ g.chain X) ∨
        (∀ X, ¬(i₀ ∈ g.chain X ∧ i ∈ g.chain X)) := by
      by_cases h1 : i₀ ∈ g.chain i
      · exact Or.inl fun X hX => g.chain_subset hX h1
      by_cases h2 : i ∈ g.chain i₀
      · exact Or.inr (Or.inl fun X hX => g.chain_subset hX h2)
      exact Or.inr (Or.inr fun X ⟨a, b⟩ => (g.chain_total a b).elim h1 h2)
    have hc3 : 3 ≤ g.cval M N i := by rw [hc i hi]; split_ifs <;> omega
    have key := excl_core (g.e i₀) (g.e i) (g.e_mem_units hi₀'.1 hi₀'.2)
      (g.e_mem_units hi'.1 hi'.2)
      (decide (i₀ ∈ g.chain (M 0))) (decide (i₀ ∈ g.chain (N 0)))
      (decide (i₀ ∈ g.chain (M 1))) (decide (i₀ ∈ g.chain (N 1)))
      (decide (i₀ ∈ g.chain (M 2))) (decide (i₀ ∈ g.chain (N 2)))
      ⟨by simpa [g.sgn_eq_sgb] using hf₀ 0, by simpa [g.sgn_eq_sgb] using hf₀ 1,
        by simpa [g.sgn_eq_sgb] using hf₀ 2⟩
      (decide (i ∈ g.chain (M 0))) (decide (i ∈ g.chain (N 0)))
      (decide (i ∈ g.chain (M 1))) (decide (i ∈ g.chain (N 1)))
      (decide (i ∈ g.chain (M 2))) (decide (i ∈ g.chain (N 2)))
      (by simpa [cval, Fin.sum_univ_three, g.sgn_eq_sgb] using hc3)
      (by
        rcases rel with r | r | r
        · left; simp only [decide_eq_true_eq]; exact ⟨r _, r _, r _, r _, r _, r _⟩
        · right; left; simp only [decide_eq_true_eq]; exact ⟨r _, r _, r _, r _, r _, r _⟩
        · right; right; simp only [decide_eq_true_eq]; exact ⟨r _, r _, r _, r _, r _, r _⟩)
    rw [hd₀] at key
    have e1 : pick (d + 2) (decide (i ∈ g.chain (M 0))) (decide (i ∈ g.chain (M 1)))
        (decide (i ∈ g.chain (M 2))) = decide (i ∈ g.chain (M (d + 2))) :=
      pick_fn (fun k => decide (i ∈ g.chain (M k))) (d + 2)
    have e2 : pick (d + 2) (decide (i ∈ g.chain (N 0))) (decide (i ∈ g.chain (N 1)))
        (decide (i ∈ g.chain (N 2))) = decide (i ∈ g.chain (N (d + 2))) :=
      pick_fn (fun k => decide (i ∈ g.chain (N k))) (d + 2)
    rw [e1, e2] at key
    rw [g.sgn_eq_sgb]
    exact key
  refine ⟨d + 2, ?_⟩
  have hwd : wd (d + 2) S = form (d + 2) (g.pt (M (d + 2))) - form (d + 2) (g.pt (N (d + 2))) := by
    unfold wd; rw [(h _).2.2.1, (h _).2.2.2]
  rw [hwd, g.form_diff _ (h _).1 (h _).2.1]
  have hterm : ∀ i ∈ Icc 1 g.s, g.sgn (M (d + 2)) (N (d + 2)) i * form (d + 2) (g.e i)
      = 1 + if cls (g.e i) = d then 1 else 0 := by
    intro i hi
    have hi' := hi
    simp only [mem_Icc] at hi'
    rw [term_eq (g.e_mem_units hi'.1 hi'.2) d _ (g.sgn_cases _ _ _) (hpos i hi)]
    split_ifs <;> norm_num
  rw [sum_congr rfl hterm, sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right,
    sum_boole, ← hcd]
  simp [count]

end Growth

end Polyhex
