import Mathlib

/-!
# The arithmetic step

If a spanning tree has `a`, `b`, `c` edges in the three lattice directions, the geometric part of
the argument bounds the hull area by `1 + s + m/3 + (ab + bc + ca)/2`, where `s = a + b + c` and
`m = max a b c`. Here we show that this is at most `⌈n² + 14n/3⌉ / 6` for `n = s + 1`, which is
in turn at most Kurz's bound `⌊n² + 14n/3 + 1⌋ / 6`.

Instead of the balancing argument in the informal proof we use a direct inequality. With `c` the
largest count, `x = c - a` and `y = c - b`, the difference of the two sides is
`3(x² - xy + y²) - 2x - 2y + 1`, which is nonnegative for all integers `x, y ≥ 0`.
-/

namespace Polyhex

lemma arith_of_max_right (a b c : ℤ) (ha : a ≤ c) (hb : b ≤ c) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    3 * (6 + 6 * (a + b + c) + 2 * c + 3 * (a * b + b * c + c * a))
      ≤ 3 * (a + b + c + 1) ^ 2 + 14 * (a + b + c + 1) + 2 := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = c - x := ⟨c - a, by linarith, by ring⟩
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ b = c - y := ⟨c - b, by linarith, by ring⟩
  have hx' : 0 ≤ (x - 1) * (3 * x - 1) := by
    rcases (show x = 0 ∨ 1 ≤ x by omega) with h | h
    · subst h; norm_num
    · exact mul_nonneg (by linarith) (by linarith)
  have hy' : 0 ≤ (y - 1) * (3 * y - 1) := by
    rcases (show y = 0 ∨ 1 ≤ y by omega) with h | h
    · subst h; norm_num
    · exact mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (x - y)]

/-- The key arithmetic inequality, in integer form. -/
lemma arith_main (a b c : ℕ) :
    3 * (6 + 6 * ((a : ℤ) + b + c) + 2 * (max a (max b c) : ℕ) + 3 * (a * b + b * c + c * a))
      ≤ 3 * ((a : ℤ) + b + c + 1) ^ 2 + 14 * ((a : ℤ) + b + c + 1) + 2 := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  all_goals first
    | (have hm : max a (max b c) = c := by omega
       rw [hm]
       exact arith_of_max_right a b c (by omega) (by omega)
         (by positivity) (by positivity))
    | (have hm : max a (max b c) = b := by omega
       rw [hm]
       have := arith_of_max_right a c b (by omega) (by omega)
         (by positivity) (by positivity)
       linarith)
    | (have hm : max a (max b c) = a := by omega
       rw [hm]
       have := arith_of_max_right b c a (by omega) (by omega)
         (by positivity) (by positivity)
       linarith)

/-- The real form of the arithmetic step, with Kurz's floor bound on the right. -/
theorem arith_kurz (a b c : ℕ) :
    ((a * b + b * c + c * a : ℕ) : ℝ) / 2 + 1 + ((a + b + c : ℕ) : ℝ)
        + ((max a (max b c) : ℕ) : ℝ) / 3
      ≤ (⌊((a + b + c + 1 : ℕ) : ℝ) ^ 2 + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ) + 1⌋ : ℝ) / 6 := by
  have key := arith_main a b c
  set L : ℤ := 6 + 6 * ((a : ℤ) + b + c) + 2 * (max a (max b c) : ℕ)
    + 3 * (a * b + b * c + c * a) with hL
  have hfl : L ≤ ⌊((a + b + c + 1 : ℕ) : ℝ) ^ 2 + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ) + 1⌋ := by
    rw [Int.le_floor]
    have : (3 * L : ℝ) ≤ 3 * ((a : ℝ) + b + c + 1) ^ 2 + 14 * ((a : ℝ) + b + c + 1) + 2 := by
      exact_mod_cast key
    push_cast
    linarith
  have hfl' : (L : ℝ) ≤ (⌊((a + b + c + 1 : ℕ) : ℝ) ^ 2
      + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ) + 1⌋ : ℝ) := by exact_mod_cast hfl
  have hLr : (L : ℝ) = 6 + 6 * ((a : ℝ) + b + c) + 2 * ((max a (max b c) : ℕ) : ℝ)
      + 3 * ((a : ℝ) * b + b * c + c * a) := by
    simp [hL]
  rw [hLr] at hfl'
  push_cast at hfl' ⊢
  linarith

/-- The sharper exact form: the bound is at most `⌈n² + 14n/3⌉ / 6`. -/
theorem arith_ceil (a b c : ℕ) :
    ((a * b + b * c + c * a : ℕ) : ℝ) / 2 + 1 + ((a + b + c : ℕ) : ℝ)
        + ((max a (max b c) : ℕ) : ℝ) / 3
      ≤ (⌈((a + b + c + 1 : ℕ) : ℝ) ^ 2 + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ)⌉ : ℝ) / 6 := by
  have key := arith_main a b c
  set L : ℤ := 6 + 6 * ((a : ℤ) + b + c) + 2 * (max a (max b c) : ℕ)
    + 3 * (a * b + b * c + c * a) with hL
  have hcl : L ≤ ⌈((a + b + c + 1 : ℕ) : ℝ) ^ 2 + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ)⌉ := by
    rw [Int.le_ceil_iff]
    have : (3 * L : ℝ) ≤ 3 * ((a : ℝ) + b + c + 1) ^ 2 + 14 * ((a : ℝ) + b + c + 1) + 2 := by
      exact_mod_cast key
    push_cast
    linarith
  have hcl' : (L : ℝ) ≤ (⌈((a + b + c + 1 : ℕ) : ℝ) ^ 2
      + 14 / 3 * ((a + b + c + 1 : ℕ) : ℝ)⌉ : ℝ) := by exact_mod_cast hcl
  have hLr : (L : ℝ) = 6 + 6 * ((a : ℝ) + b + c) + 2 * ((max a (max b c) : ℕ) : ℝ)
      + 3 * ((a : ℝ) * b + b * c + c * a) := by
    simp [hL]
  rw [hLr] at hcl'
  push_cast at hcl' ⊢
  linarith

end Polyhex
