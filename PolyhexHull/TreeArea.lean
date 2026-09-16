import PolyhexHull.Growth
import PolyhexHull.Transport

/-!
# Area of the hull of the centres

Inserting the cells of a growth order one at a time, each insertion along a unit step `v` adds at
most half the width of the current hull in the direction `det(v, ·)`. That width is at most the
number of earlier tree edges not parallel to `v`. Summing gives
`area(conv centres) ≤ (ab + bc + ca) / 2`.
-/

namespace Polyhex

open MeasureTheory Set Finset
open scoped Pointwise

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- Integer determinant of two lattice vectors. -/
def idet (e c : Cell) : ℤ := e.1 * c.2 - e.2 * c.1

lemma idet_add (e c d : Cell) : idet e (c + d) = idet e c + idet e d := by
  simp [idet]; ring

lemma det2_toPlane (e c : Cell) : det2 (toPlane e) (toPlane c) = idet e c := by
  simp [det2, idet, toPlane]

lemma abs_idet_units {e e' : Cell} (he : e ∈ units) (he' : e' ∈ units) :
    |idet e e'| = if cls e' = cls e then 0 else 1 := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at he he'
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma toPlane_ne_zero {e : Cell} (he : e ∈ units) : toPlane e ≠ 0 := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [toPlane, Prod.ext_iff]

/-- Prefix count of edges in class `d` among edges `1..j`. -/
def pcount (j : ℕ) (d : Fin 3) : ℕ := #{i ∈ Icc 1 j | cls (g.e i) = d}

/-- Pairs of nonparallel edges among edges `1..j`. -/
def pairs (j : ℕ) : ℕ :=
  g.pcount j 0 * g.pcount j 1 + g.pcount j 1 * g.pcount j 2 + g.pcount j 2 * g.pcount j 0

/-- Number of edges among `1..j` not parallel to direction class `d`. -/
def nonpar (j : ℕ) (d : Fin 3) : ℕ := #{i ∈ Icc 1 j | cls (g.e i) ≠ d}

lemma pcount_succ (j : ℕ) (d : Fin 3) :
    g.pcount (j + 1) d = g.pcount j d + if cls (g.e (j + 1)) = d then 1 else 0 := by
  unfold pcount
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma pcount_sum (j : ℕ) : g.pcount j 0 + g.pcount j 1 + g.pcount j 2 = j := by
  have h := card_eq_sum_card_fiberwise (f := fun i => cls (g.e i)) (s := Icc 1 j)
    (t := univ) (fun _ _ => mem_univ _)
  simp only [Fin.sum_univ_three, Nat.card_Icc, add_tsub_cancel_right] at h
  simp only [pcount]
  omega

lemma nonpar_add (j : ℕ) (d : Fin 3) : g.nonpar j d + g.pcount j d = j := by
  unfold nonpar pcount
  rw [add_comm, card_filter_add_card_filter_not]
  simp

lemma pairs_succ (j : ℕ) :
    g.pairs (j + 1) = g.pairs j + g.nonpar j (cls (g.e (j + 1))) := by
  have hs := g.pcount_sum j
  have hn := g.nonpar_add j (cls (g.e (j + 1)))
  unfold pairs
  simp only [pcount_succ]
  generalize cls (g.e (j + 1)) = d at hn ⊢
  fin_cases d <;> simp at hn ⊢ <;> nlinarith [hn, hs]

/-- The planar point set of the first `j + 1` centres. -/
def pts (j : ℕ) : Set (ℝ × ℝ) := (fun i => toPlane (g.pt i)) '' {i | i ≤ j}

lemma pts_finite (j : ℕ) : (g.pts j).Finite :=
  (Set.finite_le_nat j).image _

lemma pts_succ (j : ℕ) : g.pts (j + 1) = insert (toPlane (g.pt (j + 1))) (g.pts j) := by
  ext p
  simp only [pts, mem_image, mem_ofPred_eq, mem_insert_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · right; exact ⟨i, by omega, rfl⟩
    · left; rw [show i = j + 1 by omega]
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨j + 1, le_rfl, rfl⟩
    · exact ⟨i, by omega, rfl⟩

/-- Range of `idet v` over the first centres grows by at most one per nonparallel edge. -/
lemma idet_range (v : Cell) (hv : v ∈ units) (t : ℕ) (ht : t ≤ g.s) :
    ∃ lo hi : ℤ, hi - lo ≤ #{i ∈ Icc 1 t | cls (g.e i) ≠ cls v} ∧
      ∀ i ≤ t, lo ≤ idet v (g.pt i) ∧ idet v (g.pt i) ≤ hi := by
  induction t with
  | zero =>
    refine ⟨idet v (g.pt 0), idet v (g.pt 0), by simp, fun i hi => ?_⟩
    rw [Nat.le_zero.mp hi]; exact ⟨le_rfl, le_rfl⟩
  | succ t ih =>
    obtain ⟨lo, hi, hw, hb⟩ := ih (by omega)
    have hp := g.par_lt (t + 1) (by omega) ht
    have hpt : g.pt (t + 1) = g.pt (g.par (t + 1)) + g.e (t + 1) := by simp [e]
    have hval : idet v (g.pt (t + 1)) = idet v (g.pt (g.par (t + 1))) + idet v (g.e (t + 1)) := by
      rw [hpt, idet_add]
    have habs := abs_idet_units hv (g.e_mem_units (i := t + 1) (by omega) ht)
    obtain ⟨hlo, hhi⟩ := hb (g.par (t + 1)) (by omega)
    have hcount : #{i ∈ Icc 1 (t + 1) | cls (g.e i) ≠ cls v}
        = #{i ∈ Icc 1 t | cls (g.e i) ≠ cls v} + if cls (g.e (t + 1)) = cls v then 0 else 1 := by
      rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), filter_insert]
      by_cases h1 : cls (g.e (t + 1)) = cls v
      · simp [h1]
      · rw [ite_eq_left h1, ite_eq_right h1, card_insert_of_notMem (by simp)]
    refine ⟨min lo (idet v (g.pt (t + 1))), max hi (idet v (g.pt (t + 1))), ?_, fun i hi' => ?_⟩
    · rw [hcount]
      split_ifs at habs ⊢ with h
      · have : idet v (g.e (t + 1)) = 0 := abs_eq_zero.mp habs
        push_cast
        rw [hval, this, add_zero]
        have := min_le_left lo (idet v (g.pt (g.par (t + 1))))
        have := le_max_left hi (idet v (g.pt (g.par (t + 1))))
        rw [min_eq_left hlo, max_eq_left hhi]
        linarith
      · push_cast
        have h1 := abs_le.mp habs.le
        rcases le_total lo (idet v (g.pt (t + 1))) with hl | hl <;>
          rcases le_total hi (idet v (g.pt (t + 1))) with hh | hh
        all_goals
          simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hl, hh]
          linarith
    · rcases Nat.lt_or_ge i (t + 1) with h | h
      · obtain ⟨a, b⟩ := hb i (by omega)
        exact ⟨(min_le_left _ _).trans a, b.trans (le_max_left _ _)⟩
      · rw [show i = t + 1 by omega]
        exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- The area of the hull of the first `j + 1` centres is at most `pairs j / 2`. -/
theorem volume_hull_pts_le (j : ℕ) (hj : j ≤ g.s) :
    volume (convexHull ℝ (g.pts j)) ≤ ENNReal.ofReal ((g.pairs j : ℝ) / 2) := by
  induction j with
  | zero =>
    have : g.pts 0 = {toPlane (g.pt 0)} := by
      ext p; simp [pts]
    rw [this, convexHull_singleton, measure_singleton]
    exact bot_le
  | succ j ih =>
    have hv := g.e_mem_units (i := j + 1) (by omega) hj
    obtain ⟨lo, hi, hw, hb⟩ := g.idet_range (g.e (j + 1)) hv j (by omega)
    have hp := g.par_lt (j + 1) (by omega) hj
    have hx : toPlane (g.pt (g.par (j + 1))) ∈ convexHull ℝ (g.pts j) :=
      subset_convexHull ℝ _ ⟨_, by show g.par (j + 1) ≤ j; omega, rfl⟩
    have hstep := volume_convexHull_insert_le (g.pts_finite j) (toPlane_ne_zero hv) hx
      (lo := lo) (hi := hi) (by
        rintro _ ⟨i, hi', rfl⟩
        rw [det2_toPlane]
        exact_mod_cast hb i hi')
    have hpt : toPlane (g.pt (g.par (j + 1))) + toPlane (g.e (j + 1)) = toPlane (g.pt (j + 1)) := by
      rw [← toPlane_add]; simp [e]
    rw [hpt, ← g.pts_succ] at hstep
    refine hstep.trans ?_
    refine (add_le_add (ih (by omega)) le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by
      have : (lo : ℝ) ≤ hi := by
        exact_mod_cast (hb 0 (by omega)).1.trans (hb 0 (by omega)).2
      linarith)]
    apply ENNReal.ofReal_le_ofReal
    rw [g.pairs_succ]
    have hw' : ((hi - lo : ℤ) : ℝ) ≤ (g.nonpar j (cls (g.e (j + 1))) : ℝ) := by
      exact_mod_cast hw
    push_cast at hw' ⊢
    linarith

end Growth

end Polyhex
