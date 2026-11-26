import WildNumber.Blocks
import WildNumber.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation

namespace WildNumber

open Finset

/-- Label the nine vertices outside the four-set by `Fin 9`. -/
theorem complement_embedding {D : Finset (Fin 13)} (hd : D.card = 4) :
    ∃ e : Fin 9 ↪ Fin 13, univ.map e = Dᶜ := by
  classical
  have hs : Fintype.card (Dᶜ : Finset (Fin 13)) = 9 := by simp [card_compl, hd]
  let a := (Fintype.equivFinOfCardEq hs).symm
  let e := a.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_⟩
  ext x
  constructor
  · intro h
    obtain ⟨y, _, rfl⟩ := mem_map.mp h
    exact (a y).property
  · intro h
    refine mem_map.mpr ⟨a.symm ⟨x,h⟩, mem_univ _, ?_⟩
    exact congrArg Subtype.val (a.apply_symm_apply ⟨x,h⟩)

private theorem partition_unique {B : Fin 4 → Finset (Fin 13)}
    (covers : ∀ v, ∃ i, v ∈ B i) (hc : ∑ i, (B i).card = 13) :
    ∀ v, ∃! i, v ∈ B i := by
  classical
  let f : (Σ i, B i) → Fin 13 := fun p => p.2.val
  have onto : Function.Surjective f := by
    intro v
    obtain ⟨i,hi⟩ := covers v
    exact ⟨⟨i,⟨v,hi⟩⟩, rfl⟩
  have same : Fintype.card (Σ i, B i) = Fintype.card (Fin 13) := by
    simpa only [Fintype.card_sigma, Fintype.card_coe, Fintype.card_fin] using hc
  have inj := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨onto, same⟩).injective
  intro v
  obtain ⟨i,hi⟩ := covers v
  exact ⟨i,hi,fun j hj => congrArg Sigma.fst (inj (show f ⟨j,⟨v,hj⟩⟩ = f ⟨i,⟨v,hi⟩⟩ from rfl))⟩

/-- A good split on the nine labelled points gives a single wild set
on the original thirteen vertices, valid for every color. -/
theorem upper_of_good_split (C : Coloring 13) {D : Finset (Fin 13)}
    (hd : D.card = 4) (e : Fin 9 ↪ Fin 13) (he : univ.map e = Dᶜ)
    (B : Nine.Family) (split : Nine.GoodSplit B) (dCross : ∀ c, Crosses C c D)
    (tripleCross : ∀ t : Finset (Fin 9), t.card = 3 → t ∉ B →
      ∀ c, Crosses C c (t.map e) ∧ Crosses C c (D ∪ t.map e)) : Upper C 9 := by
  classical
  obtain ⟨X,Y,Z,hx,hy,hz,hcover,xgood,ygood,zgood⟩ := split
  let A : Fin 4 → Finset (Fin 13) := ![D, X.map e, Y.map e, Z.map e]
  have unionEq : X.map e ∪ Y.map e ∪ Z.map e = Dᶜ := by
    rw [← map_union, ← map_union, hcover, he]
  have covers (v : Fin 13) : ∃ i, v ∈ A i := by
    by_cases hv : v ∈ D
    · exact ⟨0, hv⟩
    · have hm : v ∈ X.map e ∪ Y.map e ∪ Z.map e := unionEq ▸ (mem_compl.mpr hv)
      simp only [mem_union] at hm
      rcases hm with (hm|hm)|hm
      · exact ⟨1, hm⟩
      · exact ⟨2, hm⟩
      · exact ⟨3, hm⟩
  have cardSum : ∑ i, (A i).card = 13 := by
    simp [Fin.sum_univ_succ, A, hd,hx,hy,hz]
  apply upper_of_four_blocks C A (partition_unique covers cardSum)
  · intro i
    apply card_pos.mp
    fin_cases i <;> simp [A,hd,hx,hy,hz]
  · intro c
    constructor
    · intro i
      fin_cases i
      · exact dCross c
      · exact (tripleCross X hx xgood c).1
      · exact (tripleCross Y hy ygood c).1
      · exact (tripleCross Z hz zgood c).1
    · intro i hi
      fin_cases i
      · exact False.elim (hi rfl)
      · exact (tripleCross X hx xgood c).2
      · exact (tripleCross Y hy ygood c).2
      · exact (tripleCross Z hz zgood c).2

end WildNumber
