import WildNumber.MatchingModel
import WildNumber.Reduction
import Mathlib.Tactic.FinCases

namespace WildNumber.Reduction

open Finset

/-- Label the six pairs of a matching and label the two endpoints inside
each pair. The only remaining point is the missed vertex. -/
theorem exists_standard_matching (M : NamedClasses) (c : V) :
    ∃ e : Pos ≃ V, e none = c ∧ (sixPairs.map e.finsetCongr.toEmbedding) = M.edges c := by
  classical
  let ix := ((M.edges c).equivFinOfCardEq (M.six c)).symm
  let J (i : Fin 6) := (ix i).val.equivFinOfCardEq (M.pair c _ (ix i).property)
  let pt (i : Fin 6) (j : Fin 2) : V := ((J i).symm j).val
  have mem (i j) : pt i j ∈ (ix i).val := ((J i).symm j).property
  have hp (i : Fin 6) : ({pt i 0, pt i 1} : Finset V) = (ix i).val := by
    ext v
    constructor
    · simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl) <;> exact mem _ _
    · intro hv
      obtain ⟨j, hj⟩ := (J i).symm.surjective ⟨v,hv⟩
      have h := congrArg Subtype.val hj
      change pt i j = v at h
      subst v
      fin_cases j <;> simp
  let f : Pos → V := fun p => p.elim c (fun a => pt a.1 a.2)
  have hf : Function.Injective f := by
    rintro ( _ | ⟨i,j⟩) ( _ | ⟨k,l⟩) h
    · rfl
    · change c = pt k l at h
      exact False.elim (M.misses c _ (ix k).property
        (Eq.mpr (congrArg (fun x => x ∈ (ix k).val) h) (mem k l)))
    · change pt i j = c at h
      exact False.elim (M.misses c _ (ix i).property
        (Eq.mp (congrArg (fun x => x ∈ (ix i).val) h) (mem i j)))
    · change pt i j = pt k l at h
      have hik : i = k := by
        by_contra ne
        have hdiff : (ix i).val ≠ (ix k).val := fun eq => ne (ix.injective (Subtype.ext eq))
        have hd := M.matching c _ (ix i).property _ (ix k).property hdiff
        exact (Finset.disjoint_left.mp hd) (mem i j) (h ▸ mem k l)
      subst k
      have hjl : j = l := (J i).symm.injective (Subtype.ext h)
      simp [hjl]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by decide⟩)
  have he (i) : (pairAt i).map e.toEmbedding = (ix i).val := by
    simpa [pairAt, e, f] using hp i
  refine ⟨e, rfl, ?_⟩
  ext t
  constructor
  · intro ht
    obtain ⟨_,hz,rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    change (pairAt i).map e.toEmbedding ∈ M.edges c
    rw [he i]
    exact (ix i).property
  · intro ht
    obtain ⟨i, h⟩ := ix.surjective ⟨t,ht⟩
    exact Finset.mem_map.mpr ⟨pairAt i, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (he i).trans (congrArg Subtype.val h)⟩

end WildNumber.Reduction
