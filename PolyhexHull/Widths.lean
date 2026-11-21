module

public import PolyhexHull.Growth

@[expose] public section

/-!
# Widths of a set of cells

`wd k S` is the width of the finite set of cells `S` with respect to the linear form `form k`,
that is the largest value of `form k` on `S` minus the smallest. `Wsum S` is the sum of the three
widths. These depend on `S` alone, and for any growth order they are computed from a choice of
extremal cells.
-/

namespace Polyhex

open Finset

/-- The largest value of `form k` on `S` (zero for the empty set). -/
def hiF (k : Fin 3) (S : Finset Cell) : ℤ := if h : S.Nonempty then S.sup' h (form k) else 0

/-- The smallest value of `form k` on `S` (zero for the empty set). -/
def loF (k : Fin 3) (S : Finset Cell) : ℤ := if h : S.Nonempty then S.inf' h (form k) else 0

/-- The width of `S` with respect to `form k`. -/
def wd (k : Fin 3) (S : Finset Cell) : ℤ := hiF k S - loF k S

/-- The sum of the three widths. -/
def Wsum (S : Finset Cell) : ℤ := ∑ k, wd k S

lemma hiF_eq {k : Fin 3} {S : Finset Cell} {c : Cell} (hc : c ∈ S)
    (h : ∀ d ∈ S, form k d ≤ form k c) : hiF k S = form k c := by
  have hne : S.Nonempty := ⟨c, hc⟩
  rw [hiF, dite_eq_left hne]
  exact le_antisymm (sup'_le _ _ h) (le_sup' _ hc)

lemma loF_eq {k : Fin 3} {S : Finset Cell} {c : Cell} (hc : c ∈ S)
    (h : ∀ d ∈ S, form k c ≤ form k d) : loF k S = form k c := by
  have hne : S.Nonempty := ⟨c, hc⟩
  rw [loF, dite_eq_left hne]
  exact le_antisymm (inf'_le _ hc) (le_inf' _ _ h)

lemma le_hiF {k : Fin 3} {S : Finset Cell} {c : Cell} (hc : c ∈ S) : form k c ≤ hiF k S := by
  rw [hiF, dite_eq_left ⟨c, hc⟩]; exact le_sup' _ hc

lemma loF_le {k : Fin 3} {S : Finset Cell} {c : Cell} (hc : c ∈ S) : loF k S ≤ form k c := by
  rw [loF, dite_eq_left ⟨c, hc⟩]; exact inf'_le _ hc

lemma wd_nonneg (k : Fin 3) (S : Finset Cell) : 0 ≤ wd k S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp [wd, hiF, loF]
  · have := (loF_le (k := k) hc).trans (le_hiF hc); simp only [wd]; omega

lemma Wsum_nonneg (S : Finset Cell) : 0 ≤ Wsum S :=
  Finset.sum_nonneg fun k _ => wd_nonneg k S

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- `M` and `N` pick, for each form, a cell of the growth where it is largest and smallest. -/
def IsExt (M N : Fin 3 → ℕ) : Prop :=
  ∀ k, M k ≤ g.s ∧ N k ≤ g.s ∧ form k (g.pt (M k)) = hiF k S ∧ form k (g.pt (N k)) = loF k S

/-- Extremal indices exist, and the minimiser of one chosen form may be prescribed. -/
lemma exists_ext (k₀ : Fin 3) (n₀ : ℕ) (hn₀ : n₀ ≤ g.s)
    (hmin : ∀ i ≤ g.s, form k₀ (g.pt n₀) ≤ form k₀ (g.pt i)) :
    ∃ M N : Fin 3 → ℕ, g.IsExt M N ∧ N k₀ = n₀ := by
  classical
  have hne : (range (g.s + 1)).Nonempty := ⟨0, by simp⟩
  have hmax := fun k : Fin 3 => exists_max_image _ (fun i => form k (g.pt i)) hne
  have hmn := fun k : Fin 3 => exists_min_image _ (fun i => form k (g.pt i)) hne
  choose M hMr hM using hmax
  choose N hNr hN using hmn
  have hall : ∀ k (j : ℕ), j ≤ g.s → (∀ i ≤ g.s, form k (g.pt i) ≤ form k (g.pt j)) →
      form k (g.pt j) = hiF k S := fun k j hj h => by
    refine (hiF_eq (g.pt_mem hj) fun d hd => ?_).symm
    obtain ⟨i, hi, rfl⟩ := g.mem_iff.mp hd
    exact h i hi
  have hall' : ∀ k (j : ℕ), j ≤ g.s → (∀ i ≤ g.s, form k (g.pt j) ≤ form k (g.pt i)) →
      form k (g.pt j) = loF k S := fun k j hj h => by
    refine (loF_eq (g.pt_mem hj) fun d hd => ?_).symm
    obtain ⟨i, hi, rfl⟩ := g.mem_iff.mp hd
    exact h i hi
  refine ⟨M, Function.update N k₀ n₀, fun k => ?_, by simp⟩
  have hMs : M k ≤ g.s := by have := hMr k; simp at this; omega
  have hNs : N k ≤ g.s := by have := hNr k; simp at this; omega
  refine ⟨hMs, ?_, hall k _ hMs fun i hi => hM k i (by simp; omega), ?_⟩
  · by_cases h : k = k₀
    · subst h; simpa using hn₀
    · simpa [h] using hNs
  · by_cases h : k = k₀
    · subst h; simpa using hall' k n₀ hn₀ hmin
    · simpa [h] using hall' k _ hNs fun i hi => hN k i (by simp; omega)

lemma exists_ext' : ∃ M N : Fin 3 → ℕ, g.IsExt M N := by
  have hne : (range (g.s + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨n₀, hn₀r, hn₀⟩ := exists_min_image _ (fun i => form 0 (g.pt i)) hne
  obtain ⟨M, N, h, -⟩ := g.exists_ext 0 n₀ (by simp at hn₀r; omega)
    (fun i hi => hn₀ i (by simp; omega))
  exact ⟨M, N, h⟩

lemma Wsum_eq {M N : Fin 3 → ℕ} (h : g.IsExt M N) :
    Wsum S = ∑ k, (form k (g.pt (M k)) - form k (g.pt (N k))) := by
  unfold Wsum wd
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(h k).2.2.1, (h k).2.2.2]

lemma Wsum_le : Wsum S ≤ 3 * g.s + max (g.count 0) (max (g.count 1) (g.count 2)) := by
  obtain ⟨M, N, h⟩ := g.exists_ext'
  rw [g.Wsum_eq h]
  exact g.width_sum_le M N (fun k => (h k).1) (fun k => (h k).2.1)

end Growth

end Polyhex
