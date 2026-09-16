import PolyhexHull.Growth

/-!
# Connected polyhexes have growth orders

Starting from one cell, repeatedly add a cell adjacent to the cells chosen so far. Connectivity of
the induced graph guarantees such a cell exists until every cell is used.
-/

namespace Polyhex

open Finset

theorem exists_growth {S : Finset Cell} (hS : IsPolyhex S) : Nonempty (Growth S) := by
  classical
  obtain ⟨x0, hx0⟩ := hS.1
  have claim : ∀ k, k < S.card → ∃ T ⊆ S, T.card = k + 1 ∧ Nonempty (Growth T) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨{x0}, by simpa using hx0, by simp, ⟨?_⟩⟩
      exact
        { s := 0
          pt := fun _ => x0
          par := fun _ => 0
          par_lt := fun j h1 h2 => by omega
          step := fun j h1 h2 => by omega
          image_eq := by ext; simp
          injOn := fun i hi j hj _ => by simp at hi hj; omega }
    | succ k ih =>
      intro hk
      obtain ⟨T, hTS, hTc, ⟨g⟩⟩ := ih (by omega)
      obtain ⟨w, hwS, hwT⟩ : ∃ w ∈ S, w ∉ T := by
        by_contra h
        push Not at h
        have := card_le_card (show S ⊆ T from h)
        omega
      have hT0 : g.pt 0 ∈ T := g.pt_mem (Nat.zero_le _)
      obtain ⟨p⟩ := hS.2.preconnected ⟨g.pt 0, hTS hT0⟩ ⟨w, hwS⟩
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {v | v.1 ∈ T} hT0 hwT
      simp only [Set.mem_ofPred_eq] at hd1 hd2
      have hadj : hexGraph.Adj d.fst.1 d.snd.1 := d.adj
      obtain ⟨i, hi', hipt⟩ := g.mem_iff.mp hd1
      set u := d.snd.1 with hu
      refine ⟨insert u T, insert_subset_iff.mpr ⟨d.snd.2, hTS⟩,
        by rw [card_insert_of_notMem hd2, hTc], ⟨?_⟩⟩
      exact
        { s := g.s + 1
          pt := fun j => if j = g.s + 1 then u else g.pt j
          par := fun j => if j = g.s + 1 then i else g.par j
          par_lt := fun j h1 h2 => by
            by_cases hj : j = g.s + 1
            · simp only [hj, ite_true]; omega
            · simp only [hj, ite_false]; exact g.par_lt j h1 (by omega)
          step := fun j h1 h2 => by
            by_cases hj : j = g.s + 1
            · simp only [hj, ite_true, show i ≠ g.s + 1 by omega, ite_false, hipt]
              exact hadj
            · have hp := g.par_lt j h1 (by omega)
              simp only [hj, ite_false, show g.par j ≠ g.s + 1 by omega]
              exact g.step j h1 (by omega)
          image_eq := by
            rw [range_add_one, image_insert, ite_eq_left rfl]
            congr 1
            refine Eq.trans (image_congr fun j hj => ?_) g.image_eq
            simp at hj
            simp [show j ≠ g.s + 1 by omega]
          injOn := by
            intro a ha b hb hab
            simp only [coe_range, Set.mem_Iio] at ha hb
            by_cases haa : a = g.s + 1 <;> by_cases hbb : b = g.s + 1
            · rw [haa, hbb]
            · simp only [haa, hbb, ite_true, ite_false] at hab
              exfalso; apply hd2
              rw [hab]; exact g.pt_mem (by omega)
            · simp only [haa, hbb, ite_true, ite_false] at hab
              exfalso; apply hd2
              rw [← hab]; exact g.pt_mem (by omega)
            · simp only [haa, hbb, ite_false] at hab
              exact g.injOn (by simp; omega) (by simp; omega) hab }
  obtain ⟨T, hTS, hTc, hg⟩ := claim (S.card - 1) (by have := hS.1.card_pos; omega)
  have : T = S := eq_of_subset_of_card_le hTS (by have := hS.1.card_pos; omega)
  exact this ▸ hg

end Polyhex
