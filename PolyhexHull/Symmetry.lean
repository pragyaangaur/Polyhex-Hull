module

public import PolyhexHull.Widths
public import PolyhexHull.Walk

@[expose] public section

/-!
# Lattice symmetries

`rhoP` is the rotation `ρ(q, r) = (-r, q + r)` by sixty degrees and `sigP` is the reflection
`σ(q, r) = (q + r, -r)`, both as permutations of the cells. Together they generate the twelve
symmetries of the triangular lattice that fix the origin.

We record how these maps act on unit steps, direction classes, widths and growth orders, and
prove that `W(i, j, k)` and `W(k, j, i)` are congruent.
-/

namespace Polyhex

open Finset
open scoped Fin.NatCast

/-- The rotation `ρ(q, r) = (-r, q + r)`. -/
def rhoP : Equiv.Perm Cell where
  toFun c := (-c.2, c.1 + c.2)
  invFun c := (c.1 + c.2, -c.1)
  left_inv c := by ext <;> simp
  right_inv c := by ext <;> simp

/-- The reflection `σ(q, r) = (q + r, -r)`. -/
def sigP : Equiv.Perm Cell where
  toFun := sig
  invFun := sig
  left_inv := sig_sig
  right_inv := sig_sig

lemma rhoP_apply (c : Cell) : rhoP c = (-c.2, c.1 + c.2) := rfl

lemma sigP_apply (c : Cell) : sigP c = sig c := rfl

lemma rhoP_add (a b : Cell) : rhoP (a + b) = rhoP a + rhoP b := by
  simp only [rhoP_apply, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

lemma rhoP_mem_units {e : Cell} (he : e ∈ units) : rhoP e ∈ units := by
  simp only [units, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma cls_rhoP {e : Cell} (he : e ∈ units) : cls (rhoP e) = cls e + 1 := by
  simp only [units, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma rhoP_pow_succ_apply (j : ℕ) (c : Cell) : (rhoP ^ (j + 1)) c = rhoP ((rhoP ^ j) c) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

lemma rhoP_pow_add (j : ℕ) (a b : Cell) :
    (rhoP ^ j) (a + b) = (rhoP ^ j) a + (rhoP ^ j) b := by
  induction j with
  | zero => simp
  | succ j ih => simp only [rhoP_pow_succ_apply, ih, rhoP_add]

lemma rhoP_pow_sub (j : ℕ) (a b : Cell) :
    (rhoP ^ j) (a - b) = (rhoP ^ j) a - (rhoP ^ j) b := by
  have := rhoP_pow_add j (a - b) b
  rw [sub_add_cancel] at this
  rw [this]; abel

lemma rhoP_pow_mem_units (j : ℕ) {e : Cell} (he : e ∈ units) : (rhoP ^ j) e ∈ units := by
  induction j with
  | zero => simpa using he
  | succ j ih => rw [rhoP_pow_succ_apply]; exact rhoP_mem_units ih

lemma cls_rhoP_pow (j : ℕ) {e : Cell} (he : e ∈ units) :
    cls ((rhoP ^ j) e) = cls e + (j : Fin 3) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [rhoP_pow_succ_apply, cls_rhoP (rhoP_pow_mem_units j he), ih, Nat.cast_succ, add_assoc]

/-! ### Widths of images -/

lemma wd_image_pos (φ : Cell → Cell) (k k' : Fin 3) (h : ∀ c, form k (φ c) = form k' c)
    (T : Finset Cell) : wd k (T.image φ) = wd k' T := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [wd, hiF, loF]
  obtain ⟨c₁, hc₁, h₁⟩ := exists_max_image T (form k') hne
  obtain ⟨c₂, hc₂, h₂⟩ := exists_min_image T (form k') hne
  have a1 : hiF k (T.image φ) = form k (φ c₁) := hiF_eq (mem_image_of_mem φ hc₁) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := mem_image.mp hd; rw [h, h]; exact h₁ c hc)
  have a2 : loF k (T.image φ) = form k (φ c₂) := loF_eq (mem_image_of_mem φ hc₂) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := mem_image.mp hd; rw [h, h]; exact h₂ c hc)
  have b1 : hiF k' T = form k' c₁ := hiF_eq hc₁ h₁
  have b2 : loF k' T = form k' c₂ := loF_eq hc₂ h₂
  simp only [wd, a1, a2, b1, b2, h]

lemma wd_image_neg (φ : Cell → Cell) (k k' : Fin 3) (h : ∀ c, form k (φ c) = -form k' c)
    (T : Finset Cell) : wd k (T.image φ) = wd k' T := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [wd, hiF, loF]
  obtain ⟨c₁, hc₁, h₁⟩ := exists_max_image T (form k') hne
  obtain ⟨c₂, hc₂, h₂⟩ := exists_min_image T (form k') hne
  have a1 : hiF k (T.image φ) = form k (φ c₂) := hiF_eq (mem_image_of_mem φ hc₂) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := mem_image.mp hd; rw [h, h]; have := h₂ c hc; omega)
  have a2 : loF k (T.image φ) = form k (φ c₁) := loF_eq (mem_image_of_mem φ hc₁) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := mem_image.mp hd; rw [h, h]; have := h₁ c hc; omega)
  have b1 : hiF k' T = form k' c₁ := hiF_eq hc₁ h₁
  have b2 : loF k' T = form k' c₂ := loF_eq hc₂ h₂
  simp only [wd, a1, a2, b1, b2, h]
  ring

lemma wd_rhoP (k : Fin 3) (T : Finset Cell) : wd k (T.image rhoP) = wd (k - 1) T := by
  fin_cases k
  · exact wd_image_pos _ 0 2 (fun c => by simp [form, rhoP_apply]; ring) T
  · exact wd_image_neg _ 1 0 (fun c => by simp [form, rhoP_apply]; ring) T
  · exact wd_image_pos _ 2 1 (fun c => by simp [form, rhoP_apply]; ring) T

lemma image_rhoP_pow_succ (j : ℕ) (T : Finset Cell) :
    T.image (rhoP ^ (j + 1)) = (T.image (rhoP ^ j)).image rhoP := by
  rw [image_image]
  congr 1
  funext c
  exact rhoP_pow_succ_apply j c

lemma wd_rhoP_pow (j : ℕ) (k : Fin 3) (T : Finset Cell) :
    wd k (T.image (rhoP ^ j)) = wd (k - (j : Fin 3)) T := by
  induction j generalizing k with
  | zero => simp
  | succ j ih => rw [image_rhoP_pow_succ, wd_rhoP, ih, Nat.cast_succ, sub_sub, add_comm (1 : Fin 3)]

lemma Wsum_rhoP (T : Finset Cell) : Wsum (T.image rhoP) = Wsum T := by
  simp only [Wsum, Fin.sum_univ_three, wd_rhoP]
  have h0 : (0 : Fin 3) - 1 = 2 := rfl
  have h1 : (1 : Fin 3) - 1 = 0 := rfl
  have h2 : (2 : Fin 3) - 1 = 1 := rfl
  rw [h0, h1, h2]
  ring

lemma Wsum_rhoP_pow (j : ℕ) (T : Finset Cell) : Wsum (T.image (rhoP ^ j)) = Wsum T := by
  induction j with
  | zero => simp
  | succ j ih => rw [image_rhoP_pow_succ, Wsum_rhoP, ih]

/-! ### Growth orders under a symmetry -/

namespace Growth

variable {S : Finset Cell} (g : Growth S)

/-- Transport a growth order along `ρ^j`. -/
def mapRho (j : ℕ) : Growth (S.image (rhoP ^ j)) where
  s := g.s
  pt i := (rhoP ^ j) (g.pt i)
  par := g.par
  par_lt := g.par_lt
  step i h1 h2 := by rw [← rhoP_pow_sub]; exact rhoP_pow_mem_units j (g.step i h1 h2)
  image_eq := by
    show (range (g.s + 1)).image ((rhoP ^ j) ∘ g.pt) = _
    rw [← image_image, g.image_eq]
  injOn a ha b hb hab := g.injOn ha hb ((rhoP ^ j).injective hab)

lemma mapRho_e (j i : ℕ) : (g.mapRho j).e i = (rhoP ^ j) (g.e i) := by
  show (rhoP ^ j) (g.pt i) - (rhoP ^ j) (g.pt (g.par i)) = _
  rw [← rhoP_pow_sub]; rfl

lemma mapRho_count (j : ℕ) (k : Fin 3) :
    (g.mapRho j).count k = g.count (k - (j : Fin 3)) := by
  unfold count
  have hs : (g.mapRho j).s = g.s := rfl
  rw [hs]
  congr 1
  refine filter_congr fun i hi => ?_
  simp only [mem_Icc] at hi
  rw [mapRho_e, cls_rhoP_pow j (g.e_mem_units hi.1 hi.2)]
  exact eq_sub_iff_add_eq.symm

end Growth

/-! ### Reversing a three-run walk -/

lemma walk_rev (a j b t : ℕ) (ht : t ≤ a + j + b) :
    walk b j (a + j + b - t) = sig (-(walk a j t)) + (((j + a : ℕ) : ℤ), (b : ℤ) - a) := by
  unfold walk sig
  split_ifs <;> simp only [Prod.fst_neg, Prod.snd_neg, Prod.mk_add_mk, Prod.mk.injEq] <;>
    push_cast <;> (constructor <;> omega)

/-- `W(b, j, a)` is the image of `W(a, j, b)` under `c ↦ σ(-c) + E`. -/
lemma tub_rev (a j b : ℕ) :
    tub b j a = (tub a j b).image (fun c => sig (-c) + (((j + a : ℕ) : ℤ), (b : ℤ) - a)) := by
  unfold tub
  rw [image_image]
  ext c
  simp only [mem_image, mem_range, Function.comp]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨a + j + b - u, by omega, ?_⟩
    rw [← walk_rev a j b _ (by omega)]
    congr 1; omega
  · rintro ⟨t, ht, rfl⟩
    exact ⟨a + j + b - t, by omega, walk_rev a j b t (by omega)⟩

end Polyhex
