import WildNumber.Graph
import Mathlib.Data.Fintype.Powerset

namespace WildNumber

/-- Up to complement, the seven nontrivial cuts of four blocks are the
four singleton cuts and the three pair cuts containing block zero. -/
private theorem four_cuts : ∀ I : Finset (Fin 4), I.Nonempty → I ≠ Finset.univ →
    (∃ i, I = {i}) ∨ (∃ i, Iᶜ = {i}) ∨
    (∃ i, i ≠ 0 ∧ I = {0, i}) ∨ (∃ i, i ≠ 0 ∧ Iᶜ = {0, i}) := by
  decide

/-- Choosing a star in each of four blocks costs nine edges. It connects
every color if each of the seven cuts of the blocks is crossed. -/
theorem upper_of_four_blocks (C : Coloring 13) (B : Fin 4 → Finset (Fin 13))
    (mem_unique : ∀ v, ∃! i, v ∈ B i) (nonempty : ∀ i, (B i).Nonempty)
    (good : ∀ c, (∀ i, Crosses C c (B i)) ∧
      ∀ i, i ≠ 0 → Crosses C c (B 0 ∪ B i)) : Upper C 9 := by
  classical
  let tag (v : Fin 13) := (mem_unique v).exists.choose
  let rep (i : Fin 4) := (nonempty i).choose
  have htag {v i} : v ∈ B i ↔ tag v = i := by
    constructor
    · exact fun h => (mem_unique v).unique (mem_unique v).exists.choose_spec h
    · rintro rfl
      exact (mem_unique v).exists.choose_spec
  have hrep (i) : tag (rep i) = i := htag.mp (nonempty i).choose_spec
  have hinj : Function.Injective rep := fun i j e =>
    (hrep i).symm.trans ((congrArg tag e).trans (hrep j))
  let centers := Finset.univ.image rep
  let leaves := Finset.univ \ centers
  let W := leaves.image fun v => s(v,rep (tag v))
  have leaf_iff (v) : v ∈ leaves ↔ v ≠ rep (tag v) := by
    simp only [leaves, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h eq
      exact h (Finset.mem_image.mpr ⟨tag v, Finset.mem_univ _, eq.symm⟩)
    · intro h hc
      obtain ⟨i, _, e⟩ := Finset.mem_image.mp hc
      subst v
      exact h (congrArg rep (hrep i).symm)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact fun hd => (leaf_iff v).mp hv (Sym2.mk_isDiag_iff.mp hd)
  · refine Finset.card_image_le.trans ?_
    have hc : centers.card = 4 := by
      simp [centers, Finset.card_image_of_injective _ hinj]
    simp [leaves, Finset.card_sdiff_of_subset (Finset.subset_univ centers), hc]
  intro c start finish
  let G := joined C W c
  have to_rep (v) : G.Reachable v (rep (tag v)) := by
    by_cases e : v = rep (tag v)
    · rw [← e]
    · have adj : G.Adj v (rep (tag v)) := ⟨e, Or.inr
        (Finset.mem_image_of_mem _ ((leaf_iff v).mpr e))⟩
      exact adj.reachable
  let I := Finset.univ.filter fun i => G.Reachable start (rep i)
  have side (v) : tag v ∈ I ↔ G.Reachable start v := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans (to_rep v).symm, fun h => h.trans (to_rep v)⟩
  by_contra no_path
  have hI : I.Nonempty := ⟨tag start, (side _).mpr (.refl _)⟩
  have hI' : I ≠ Finset.univ := by
    intro eq
    exact no_path ((side _).mp (eq ▸ Finset.mem_univ _))
  have conflict (S : Finset (Fin 13)) (cross : Crosses C c S)
      (hs : (∀ v, v ∈ S ↔ tag v ∈ I) ∨ (∀ v, v ∈ S ↔ tag v ∉ I)) : False := by
    obtain ⟨u, hu, v, hv, edge⟩ := cross
    have adj : G.Adj u v := ⟨fun e => hv (e ▸ hu), Or.inl edge⟩
    have same : tag u ∈ I ↔ tag v ∈ I :=
      ⟨fun h => (side v).mpr (((side u).mp h).trans adj.reachable),
       fun h => (side u).mpr (((side v).mp h).trans adj.reachable.symm)⟩
    rcases hs with pos | neg
    · exact hv ((pos v).mpr (same.mp ((pos u).mp hu)))
    · exact hv ((neg v).mpr (fun h => (neg u).mp hu (same.mpr h)))
  rcases four_cuts I hI hI' with ⟨i, eq⟩ | ⟨i, eq⟩ | ⟨i, hi, eq⟩ | ⟨i, hi, eq⟩
  · apply conflict (B i) ((good c).1 i) (Or.inl ?_)
    intro v
    simp [eq, htag]
  · apply conflict (B i) ((good c).1 i) (Or.inr ?_)
    intro v
    rw [← Finset.mem_compl, eq]
    simp [htag]
  · apply conflict (B 0 ∪ B i) ((good c).2 i hi) (Or.inl ?_)
    intro v
    simp [eq, htag]
  · apply conflict (B 0 ∪ B i) ((good c).2 i hi) (Or.inr ?_)
    intro v
    rw [← Finset.mem_compl, eq]
    simp [htag]

end WildNumber
