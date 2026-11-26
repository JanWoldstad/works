import WildNumber.MatchingKinds
import WildNumber.MatchingTransport
import Mathlib.Logic.Equiv.Basic

namespace WildNumber.Reduction

open Finset

/-- Pairs with the same number of selected endpoints can be aligned by
preserving or exchanging the two endpoint labels. -/
private theorem endpoint_alignment {D F : Finset Pos} {i k : Fin 6}
    (h : kind D i = kind F k) :
    ∃ j : Fin 2 ≃ Fin 2, ∀ a, some (i,a) ∈ D ↔ some (k,j a) ∈ F := by
  refine ⟨if (some (i,0) ∈ D ↔ some (k,0) ∈ F) then Equiv.refl _ else Equiv.swap 0 1, ?_⟩
  intro a
  fin_cases a <;> by_cases hd0 : some (i,0) ∈ D <;> by_cases hd1 : some (i,1) ∈ D <;>
    by_cases hf0 : some (k,0) ∈ F <;> by_cases hf1 : some (k,1) ∈ F <;>
    simp_all [kind]

/-- Biject corresponding pair types, then align their endpoints. -/
theorem relabel_profile {D F : Finset Pos} (h : SameProfile D F) :
    ∃ e : Pos ≃ Pos, e none = none ∧ sixPairs.map e.finsetCongr.toEmbedding = sixPairs ∧
      D.map e.toEmbedding = F := by
  classical
  let eqv (k : Fin 3) : {i // kind D i = k} ≃ {i // kind F i = k} :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_subtype, profile] using h.2 k)
  let ix := Equiv.ofFiberEquiv eqv
  have hk (i : Fin 6) : kind D i = kind F (ix i) := (Equiv.ofFiberEquiv_map eqv i).symm
  let ends (i : Fin 6) := (endpoint_alignment (hk i)).choose
  have he (i : Fin 6) := (endpoint_alignment (hk i)).choose_spec
  let pair : (Fin 6 × Fin 2) ≃ (Fin 6 × Fin 2) := {
    toFun := fun (i,j) => (ix i, ends i j)
    invFun := fun (i,j) => (ix.symm i, (ends (ix.symm i)).symm j)
    left_inv := by rintro ⟨i,j⟩; simp
    right_inv := by rintro ⟨i,j⟩; simp }
  let e := pair.optionCongr
  have he_at (i j) : e (some (i,j)) = some (ix i, ends i j) := rfl
  have pair_eq (i) : (pairAt i).map e.toEmbedding = pairAt (ix i) := by
    ext x
    obtain _ | ⟨k,l⟩ := x
    · simp only [pairAt, map_insert, map_singleton, Equiv.toEmbedding_apply, he_at,
        mem_insert, mem_singleton, reduceCtorEq]
    · simp only [pairAt, map_insert, map_singleton, Equiv.toEmbedding_apply, he_at,
        mem_insert, mem_singleton, Option.some.injEq, Prod.mk.injEq]
      have hj (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp
      have hl := hj ((ends i).symm l)
      have hh : l = ends i 0 ∨ l = ends i 1 := by
        rcases hl with hl | hl
        · exact Or.inl (by rw [← hl]; simp)
        · exact Or.inr (by rw [← hl]; simp)
      have := hj l
      grind
  refine ⟨e, rfl, ?_, ?_⟩
  · ext t
    constructor
    · intro ht
      obtain ⟨_, hz, rfl⟩ := mem_map.mp ht
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      change (pairAt i).map e.toEmbedding ∈ sixPairs
      rw [pair_eq]
      exact mem_image_of_mem _ (mem_univ _)
    · intro ht
      obtain ⟨i,_,rfl⟩ := mem_image.mp ht
      refine mem_map.mpr ⟨pairAt (ix.symm i), mem_image_of_mem _ (mem_univ _), ?_⟩
      simpa using pair_eq (ix.symm i)
  · ext x
    obtain ⟨x,rfl⟩ := e.surjective x
    change e.toEmbedding x ∈ _ ↔ _
    rw [mem_map']
    cases x with
    | none => exact h.1
    | some x => exact he x.1 x.2

end WildNumber.Reduction
