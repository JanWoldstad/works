import WildNumber.Normalization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace WildNumber

open Finset SimpleGraph

private def wildGraph {n : ℕ} (W : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  fromEdgeSet (W : Set _)

private instance {n : ℕ} (W : Finset (Sym2 (Fin n))) : DecidableRel (wildGraph W).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ W ∧ _ ≠ _))

private theorem stays {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (closed : ∀ x y, P x → G.Adj x y → P y) {x y : V} (hx : P x)
    (hr : G.Reachable x y) : P y := by
  have h := (reachable_iff_reflTransGen x y).mp hr
  clear hr
  induction h with
  | refl => exact hx
  | tail _ hadj ih => exact closed _ _ ih hadj

/-- The edge between two vertices fixes a color. Properness forces every
edge of that color at either vertex to stay in this pair. -/
private theorem pair_escapes {n : ℕ} (hn : 2 < n) (C : Coloring n)
    {W : Finset (Sym2 (Fin n))} (h : Connects C W) {a b : Fin n} (hab : a ≠ b) :
    ∃ x y, (x = a ∨ x = b) ∧ y ≠ a ∧ y ≠ b ∧ (wildGraph W).Adj x y := by
  classical
  by_contra hc
  let P := fun x : Fin n => x = a ∨ x = b
  have closed (x y : Fin n) (hx : P x) (he : (joined C W (C.color a b)).Adj x y) : P y := by
    rcases he with ⟨hxy, hcol | hw⟩
    · rcases hx with hx | hx <;> subst x
      · exact Or.inr (C.proper hxy hab hcol)
      · exact Or.inl (C.proper hxy hab.symm (hcol.trans (C.symm a b)))
    · by_contra hy
      exact hc ⟨x, y, hx, fun ha => hy (Or.inl ha), fun hb => hy (Or.inr hb),
        ⟨hw, hxy⟩⟩
  have allP (y : Fin n) : P y := stays closed (Or.inl (rfl : a = a)) (h (C.color a b) a y)
  have sub : (univ : Finset (Fin n)) ⊆ {a, b} := by
    intro x _; simpa [P] using allP x
  have hc' := card_le_card sub
  simp [hab] at hc'
  omega

private theorem leaf_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (noPair : ∀ x y, G.Adj x y → G.degree x = 1 → G.degree y ≠ 1) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ G.edgeFinset.card := by
  classical
  let L := univ.filter (fun v => G.degree v = 1)
  have one (x : L) : ∃! y, G.Adj x.val y :=
    degree_eq_one_iff_existsUnique_adj.mp (mem_filter.mp x.property).2
  let partner (x : L) := (one x).exists.choose
  have adj (x : L) : G.Adj x.val (partner x) := (one x).exists.choose_spec
  let f (x : L) : G.edgeFinset := ⟨s(x.val, partner x), by simpa using adj x⟩
  have inj : Function.Injective f := by
    intro x y he
    have hh : s(x.val, partner x) = s(y.val, partner y) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hh with h1 | h2
    · exact Subtype.ext h1.1
    · have e : G.Adj x.val y.val := h2.2 ▸ adj x
      exact False.elim (noPair _ _ e (mem_filter.mp x.property).2 (mem_filter.mp y.property).2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj

private theorem edge_bound {n : ℕ} (C : Coloring n) {W : Finset (Sym2 (Fin n))}
    (hn : 2 < n) (hh : Connects C W) :
    2 * n ≤ 3 * W.card + 2 * (univ.filter (fun x => (wildGraph W).degree x = 0)).card := by
  classical
  let G := wildGraph W
  have noPair (x y : Fin n) (he : G.Adj x y) (hx : G.degree x = 1) (hy : G.degree y = 1) : False := by
    obtain ⟨v, w, hxy, hwx, hwy, ha⟩ := pair_escapes hn C hh he.ne
    rcases hxy with rfl | rfl
    · exact hwy ((degree_eq_one_iff_existsUnique_adj.mp hx).unique ha he)
    · exact hwx ((degree_eq_one_iff_existsUnique_adj.mp hy).unique ha he.symm)
  have leaves := leaf_count G noPair
  have ecard : G.edgeFinset.card ≤ W.card := by
    apply card_le_card
    intro e he
    have hmem : e ∈ G.edgeSet := by simpa using he
    rw [show G.edgeSet = (W : Set _) \ Sym2.diagSet by exact edgeSet_fromEdgeSet _] at hmem
    exact hmem.1
  have pt (v : Fin n) : 2 ≤ G.degree v + (if G.degree v = 1 then 1 else 0) +
      2 * (if G.degree v = 0 then 1 else 0) := by
    split_ifs <;> omega
  have hs := sum_le_sum (s := (univ : Finset (Fin n))) (fun v _ => pt v)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_add_distrib,
    ← mul_sum, sum_boole] at hs
  have hd := G.sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_id] at hs
  change 2 * n ≤ 3 * W.card + 2 * (univ.filter (fun x => G.degree x = 0)).card
  omega

theorem lower_thirteen (C : Coloring 13) {W : Finset (Sym2 (Fin 13))}
    (h : Connects C W) : 9 ≤ W.card := by
  classical
  have nonzero (v : Fin 13) : (wildGraph W).degree v ≠ 0 := by
    obtain ⟨w, ha⟩ := (h (missingColor C v)).exists_adj_of_nontrivial v
    rcases ha with ⟨hn, hc | he⟩
    · exact False.elim (missingColor_spec C v w hn hc)
    · exact Nat.ne_of_gt (show (wildGraph W).Adj v w from ⟨he, hn⟩).degree_pos_left
  have z : (univ.filter (fun v => (wildGraph W).degree v = 0)) = ∅ := by
    ext v; simp [nonzero]
  have hh := edge_bound C (by decide) h
  rw [z] at hh
  simp at hh
  omega

theorem lower_fourteen (C : Coloring 14) {W : Finset (Sym2 (Fin 14))}
    (h : Connects C W) : 9 ≤ W.card := by
  classical
  have z : (univ.filter (fun v => (wildGraph W).degree v = 0)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hab
    obtain ⟨x, y, hx, _, _, he⟩ := pair_escapes (by decide) C h hab
    have hp := he.degree_pos_left
    rcases hx with rfl | rfl
    · exact (Nat.ne_of_gt hp) (mem_filter.mp ha).2
    · exact (Nat.ne_of_gt hp) (mem_filter.mp hb).2
  have hh := edge_bound C (by decide) h
  omega

end WildNumber
