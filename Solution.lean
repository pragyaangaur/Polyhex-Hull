module

public import PolyhexHull

public section

/-!
# Kurz's conjecture on the convex hull of a polyhex: the proofs

Each theorem below has exactly the statement of its namesake in `Challenge.lean`. The definitions
it uses come from `PolyhexHull.Statement`, which repeats those of `Challenge.lean` character for
character. The proofs quote `PolyhexHull.Bridge`, which transfers the axial theorems of
`PolyhexHull.Main` to the regular hexagonal tiling.
-/

open MeasureTheory Set
open scoped Pointwise

namespace KurzPolyhex

theorem volume_hexagon : volume hexagon = ENNReal.ofReal (√3 / 2) :=
  volume_hexagon'

theorem kurz_conjecture (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ : ℝ) / 6) :=
  kurz_conjecture' S hS

theorem kurz_conjecture_sharp (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume (convexHull ℝ (region S))
      ≤ volume hexagon * ENNReal.ofReal ((⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ : ℝ) / 6) :=
  kurz_conjecture_sharp' S hS

end KurzPolyhex
