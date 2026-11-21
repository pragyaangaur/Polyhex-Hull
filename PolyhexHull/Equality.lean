module

public import PolyhexHull.Main

@[expose] public section

/-!
# Equality in the bound

If a polyhex attains the bound `⌈n² + 14n/3⌉ / 6`, then every link in the chain of inequalities
behind `kurz_conjecture_sharp` is an equality. For every growth order this gives two facts:

* the sum of the three widths is `W = 3s + m`, where `m` is the largest direction count;
* the three direction counts `a, b, c` differ pairwise by at most one.

The second fact follows from the identity `3n² + 14n + 2 - 3L = Q(x, y)` with
`Q(x, y) = 3(x² - xy + y²) - 2x - 2y + 1`, where `L = 6 + 6s + 2m + 3(ab + bc + ca)`, `c = m`,
`x = c - a` and `y = c - b`. Equality forces `Q(x, y) ≤ 2`, so `x, y ≤ 1`.
-/

namespace Polyhex

open MeasureTheory Set Finset

/-- Three natural numbers that differ pairwise by at most one. -/
def Balanced (a b c : ℕ) : Prop :=
  a ≤ b + 1 ∧ b ≤ a + 1 ∧ b ≤ c + 1 ∧ c ≤ b + 1 ∧ a ≤ c + 1 ∧ c ≤ a + 1

lemma balanced_core (a b c : ℤ) (ha : a ≤ c) (hb : b ≤ c) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (h : 3 * (a + b + c + 1) ^ 2 + 14 * (a + b + c + 1)
      ≤ 3 * (6 + 6 * (a + b + c) + 2 * c + 3 * (a * b + b * c + c * a))) :
    c ≤ a + 1 ∧ c ≤ b + 1 := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = c - x := ⟨c - a, by linarith, by ring⟩
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ b = c - y := ⟨c - b, by linarith, by ring⟩
  have hQ : 3 * (x ^ 2 - x * y + y ^ 2) - 2 * x - 2 * y + 1 ≤ 2 := by linear_combination h
  have gx : 0 ≤ (x - 1) * (3 * x - 1) := by
    rcases (show x = 0 ∨ 1 ≤ x by omega) with h | h
    · subst h; norm_num
    · exact mul_nonneg (by linarith) (by linarith)
  have gy : 0 ≤ (y - 1) * (3 * y - 1) := by
    rcases (show y = 0 ∨ 1 ≤ y by omega) with h | h
    · subst h; norm_num
    · exact mul_nonneg (by linarith) (by linarith)
  constructor
  · by_contra hc
    have h2 : 0 ≤ (x - 2) * (3 * x + 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (x - y)]
  · by_contra hc
    have h2 : 0 ≤ (y - 2) * (3 * y + 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (x - y)]

/-- Equality in the arithmetic step forces balanced counts. -/
lemma balanced_of_le (a b c : ℕ)
    (h : 3 * ((a : ℤ) + b + c + 1) ^ 2 + 14 * ((a : ℤ) + b + c + 1)
      ≤ 3 * (6 + 6 * ((a : ℤ) + b + c) + 2 * (max a (max b c) : ℕ)
        + 3 * (a * b + b * c + c * a))) :
    Balanced a b c := by
  unfold Balanced
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  all_goals first
    | (have hm : max a (max b c) = c := by omega
       rw [hm] at h
       have := balanced_core a b c (by omega) (by omega) (by positivity) (by positivity) h
       omega)
    | (have hm : max a (max b c) = b := by omega
       rw [hm] at h
       have := balanced_core a c b (by omega) (by omega) (by positivity) (by positivity)
         (by linear_combination h)
       omega)
    | (have hm : max a (max b c) = a := by omega
       rw [hm] at h
       have := balanced_core b c a (by omega) (by omega) (by positivity) (by positivity)
         (by linear_combination h)
       omega)

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- The largest of the three direction counts. -/
def mm : ℕ := max (g.count 0) (max (g.count 1) (g.count 2))

end Growth

/-- **Equality in the bound, for every growth order.** If the hull of a polyhex has the largest
possible area, then for every growth order the width sum is `3s + m` and the direction counts are
balanced. -/
theorem extremal_growth {S : Finset Cell}
    (hmax : volume (convexHull ℝ (region S))
      = ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6))
    (g : Growth S) :
    Wsum S = 3 * g.s + g.mm ∧ Balanced (g.count 0) (g.count 1) (g.count 2) := by
  set a := g.count 0
  set b := g.count 1
  set c := g.count 2
  have hcard : S.card = a + b + c + 1 := by rw [← g.card_eq, g.count_sum]
  have hs : g.s = a + b + c := g.count_sum.symm
  have hp : g.pairs g.s = a * b + b * c + c * a := rfl
  have hv := volume_hull_le_widths g
  rw [hmax] at hv
  have hnn : (0 : ℝ) ≤ (g.pairs g.s : ℝ) / 2 + 1 + (Wsum S : ℝ) / 3 := by
    have : (0 : ℝ) ≤ (Wsum S : ℝ) := by exact_mod_cast Wsum_nonneg S
    positivity
  have hC := (ENNReal.ofReal_le_ofReal_iff hnn).mp hv
  have hW : ((Wsum S : ℤ) : ℝ) ≤ ((3 * g.s + g.mm : ℤ) : ℝ) := by exact_mod_cast g.Wsum_le
  have key := arith_ceil a b c
  rw [hcard] at hC
  rw [hp] at hC
  simp only [hs] at hC hW
  have hm : g.mm = max a (max b c) := rfl
  rw [hm] at hW
  push_cast at hC hW key
  set X : ℝ := ((a : ℝ) + b + c + 1) ^ 2 + 14 / 3 * ((a : ℝ) + b + c + 1) with hX
  refine ⟨?_, ?_⟩
  · have : ((Wsum S : ℤ) : ℝ) = ((3 * g.s + g.mm : ℤ) : ℝ) := by
      rw [hs, hm]; push_cast; linarith
    exact_mod_cast this
  · set L : ℤ := 6 + 6 * ((a : ℤ) + b + c) + 2 * (max a (max b c) : ℕ)
      + 3 * (a * b + b * c + c * a) with hL
    have hLr : (L : ℝ) = 6 + 6 * ((a : ℝ) + b + c) + 2 * ((max a (max b c) : ℕ) : ℝ)
        + 3 * ((a : ℝ) * b + b * c + c * a) := by simp [hL]
    have h1 : ((⌈X⌉ : ℤ) : ℝ) ≤ (L : ℝ) := by
      rw [hLr]; push_cast; linarith
    have h2 : ⌈X⌉ ≤ L := by exact_mod_cast h1
    have h3 : X ≤ (L : ℝ) := Int.ceil_le.mp h2
    apply balanced_of_le
    have h4 : (3 * ((a : ℝ) + b + c + 1) ^ 2 + 14 * ((a : ℝ) + b + c + 1)) ≤ 3 * (L : ℝ) := by
      rw [hX] at h3; linarith
    rw [hLr] at h4
    exact_mod_cast h4

end Polyhex
