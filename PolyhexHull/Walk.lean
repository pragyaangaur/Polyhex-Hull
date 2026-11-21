module

public import PolyhexHull.Defs

@[expose] public section

/-!
# Three-run walks

`walk i j t` is the cell reached after `t` steps of the walk from `(0, 0)` that takes `i` steps
`d₂ = (0, 1)`, then `j` steps `d₁ = (1, 0)`, then steps `d₃ = (1, -1)`. The cells of the first
`i + j + k + 1` positions form the polyhex `W(i, j, k)` of the uniqueness theorem.

`sig` is the lattice symmetry `σ(q, r) = (q + r, -r)`, which fixes `d₁` and swaps `d₂` and `d₃`.
-/

namespace Polyhex

/-- The lattice symmetry fixing `(1, 0)` and swapping `(0, 1)` with `(1, -1)`. -/
def sig (c : Cell) : Cell := (c.1 + c.2, -c.2)

lemma sig_add (c d : Cell) : sig (c + d) = sig c + sig d := by
  simp only [sig, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring

lemma sig_sig (c : Cell) : sig (sig c) = c := by
  simp [sig]

/-- Apply `sig` or not. -/
def sw (b : Bool) (c : Cell) : Cell := if b then sig c else c

lemma sw_add (b : Bool) (c d : Cell) : sw b (c + d) = sw b c + sw b d := by
  cases b <;> simp [sw, sig_add]

lemma sw_zero (b : Bool) : sw b 0 = 0 := by
  cases b <;> simp [sw, sig]

/-- The step pattern `d₂^x d₁^(y - x) d₃^(...)`, indexed from `1`. -/
def std (x y i : ℕ) : Cell := if i ≤ x then (0, 1) else if i ≤ y then (1, 0) else (1, -1)

/-- The position after `t` steps of the walk `d₂^i d₁^j d₃^∞`. -/
def walk (i j t : ℕ) : Cell :=
  if t ≤ i then (0, (t : ℤ))
  else if t ≤ i + j then ((t : ℤ) - i, (i : ℤ))
  else ((t : ℤ) - i, 2 * (i : ℤ) + j - t)

lemma walk_zero (i j : ℕ) : walk i j 0 = 0 := by
  simp [walk]

lemma walk_succ (i j t : ℕ) :
    walk i j (t + 1) = walk i j t + std i (i + j) (t + 1) := by
  unfold walk std
  split_ifs <;> simp only [Prod.mk_add_mk, Prod.mk.injEq] <;> push_cast <;> (constructor <;> first | trivial | omega)

/-- The cells of `W(i, j, k)`. -/
def tub (i j k : ℕ) : Finset Cell := (Finset.range (i + j + k + 1)).image (walk i j)

/-- The washtub with `n` cells: `W(i, j, k)` with `i = ⌊n/3⌋`, `j = ⌊(n+1)/3⌋`, `k = ⌊(n-1)/3⌋`.
These three numbers add up to `n - 1`, differ pairwise by at most one, and `j` is the largest. -/
def washtub (n : ℕ) : Finset Cell := tub (n / 3) ((n + 1) / 3) ((n - 1) / 3)

end Polyhex
