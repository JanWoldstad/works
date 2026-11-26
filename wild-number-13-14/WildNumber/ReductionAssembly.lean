import WildNumber.MatchingModel
import WildNumber.Normalization
import WildNumber.ReductionBounds
import WildNumber.Split

namespace WildNumber.Reduction
open Finset

/-- The finite conclusion used in the global proof. The hypotheses make no
extendibility assumption on the nine-point family. -/
def NinePointClaim : Prop :=
  ∀ B : Nine.Family, (∀ T ∈ B, T.card = 3) → B.card ≤ 35 →
  (∀ v, (B.filter (v ∈ ·)).card ≤ 19) →
  ∀ C : Finset (Fin 9), 5 ≤ C.card → (∀ x ∈ C, Nine.CoversPairs B x) → Nine.GoodSplit B

private def pull {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (S : Finset β) : Finset α := univ.filter fun x => e x ∈ S

@[simp] private theorem mem_pull {α β : Type*} [Fintype α] [DecidableEq β]
    {e : α ↪ β} {S : Finset β} {x} : x ∈ pull e S ↔ e x ∈ S := by simp [pull]

private theorem map_pull_subset {α β : Type*} [Fintype α] [DecidableEq β]
    (e : α ↪ β) (S : Finset β) : (pull e S).map e ⊆ S := by
  intro v hv
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
  exact mem_pull.mp hx

private theorem map_pull_eq {α β : Type*} [Fintype α] [DecidableEq β]
    (e : α ↪ β) (S : Finset β) (h : S ⊆ univ.map e) : (pull e S).map e = S := by
  apply Subset.antisymm (map_pull_subset e S)
  intro v hv
  obtain ⟨x,_,rfl⟩ := mem_map.mp (h hv)
  exact mem_map.mpr ⟨x,mem_pull.mpr hv,rfl⟩

private theorem crosses_of_edge {C : Coloring 13} {c : V} {S : Finset V}
    (h : EdgeCrosses (edgeClass C.color c) S) : Crosses C c S := by
  obtain ⟨e,he,u,hu,huS,v,hv,hvS⟩ := h
  obtain ⟨w,_,hw,rfl⟩ := edge_at C.color C.symm he hu
  have hne : v ≠ u := fun h => hvS (h ▸ huS)
  have hvw : v = w := by simpa [hne] using hv
  exact ⟨u,huS,v,hvS,hvw ▸ hw⟩

/-- Given the per-color cut classification and the nine-point finite theorem,
the same nine wild edges connect every color of an arbitrary coloring. -/
theorem upper_of_reduction
    (localCheck : ∀ (M : NamedClasses) (c : V) (D : Finset V), D.card = 4 →
      (inside M D c).card ≤ 1 → LocalSpec (M.edges c) D c)
    (nine : NinePointClaim) (C : Coloring 13) : Upper C 9 := by
  classical
  apply upper_of_normalize
  let N := normalize C
  let M := namedClasses N.color N.symm (normalizedColor_diag C) (normalizedColor_injective C)
  obtain ⟨D,hD⟩ := card_pos.mp (show 0 < (eligible M).card from
    lt_of_lt_of_le (by decide : 0 < 130) (eligible_card M))
  obtain ⟨h4,hr,_⟩ := eligible_properties M hD
  obtain ⟨e,he⟩ := complement_embedding h4
  let E := (mapEmbedding e).toEmbedding
  let f := fun c => colorBad (M.edges c) D
  let F := univ.biUnion f
  let B := pull E F
  let centers := used M D \ D
  let K := pull e centers
  have outside (v : Fin 9) : e v ∉ D := mem_compl.mp (he ▸ mem_map.mpr ⟨v,mem_univ _,rfl⟩)
  have localSpec (c : V) := localCheck M c D h4 (hr c)
  have active (c : V) : c ∈ used M D ↔ (inside M D c).card = 1 := by
    rw [mem_used, ← card_pos]
    have := hr c
    omega
  have size : F.card ≤ 35 := by
    apply total_bad_le M hD
    intro c
    simpa only [active, inside] using (localSpec c).1
  have degree (v : V) (hv : v ∉ D) : (F.filter (v ∈ ·)).card ≤ 19 := by
    apply bad_degree_le M hD
    intro c
    simpa only [mem_inter, active, inside, and_comm] using (localSpec c).2.1 v hv
  have rep {t : Finset (Fin 9)} : t ∈ B ↔ t.map e ∈ F := mem_pull
  have typed {T} (hT : T ∈ F) : T ⊆ Dᶜ ∧ T.card = 3 := by
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp hT
    exact mem_powersetCard.mp (mem_filter.mp hc).1
  have key : Nine.GoodSplit B := by
    refine nine B ?_ ?_ ?_ K ?_ ?_
    · intro t ht
      simpa using (typed (rep.mp ht)).2
    · have hsmall := card_le_card (map_pull_subset E F)
      rw [card_map] at hsmall
      exact hsmall.trans size
    · intro v
      apply le_trans _ (degree (e v) (outside v))
      apply card_le_card_of_injOn (Finset.map e) _ (map_injective e).injOn
      intro t ht
      obtain ⟨ht,hv⟩ := mem_filter.mp ht
      exact mem_filter.mpr ⟨rep.mp ht,mem_map.mpr ⟨v,hv,rfl⟩⟩
    · have hK : K.map e = centers := map_pull_eq e centers (by
        rw [he]
        intro v hv
        exact mem_compl.mpr (mem_sdiff.mp hv).2)
      rw [← card_map e, hK]
      exact five_centers M hD
    · intro x hx y hxy
      have hcx := mem_sdiff.mp (mem_pull.mp hx)
      obtain ⟨T,hT,hxT,hyT⟩ := (localSpec (e x)).2.2.1 hcx.2 ((active _).mp hcx.1)
        (e y) (outside y) (fun h => hxy (e.injective h.symm))
      have hTF : T ∈ F := mem_biUnion.mpr ⟨e x,mem_univ _,hT⟩
      have hmap : (pull e T).map e = T := map_pull_eq e T (he ▸ (typed hTF).1)
      exact ⟨pull e T,rep.mpr (by rw [hmap]; exact hTF),mem_pull.mpr hxT,mem_pull.mpr hyT⟩
  apply upper_of_good_split N h4 e he B key
  · intro c
    exact crosses_of_edge (localSpec c).2.2.2
  · intro t ht hgood c
    have htD : t.map e ⊆ Dᶜ := he ▸ (map_subset_map.mpr (subset_univ t))
    have hnot : t.map e ∉ f c := fun h => hgood (rep.mpr (mem_biUnion.mpr ⟨c,mem_univ _,h⟩))
    have htPow : t.map e ∈ Dᶜ.powersetCard 3 := mem_powersetCard.mpr ⟨htD, by simpa using ht⟩
    have dis : ¬ (¬ EdgeCrosses (M.edges c) (t.map e) ∨ ¬ EdgeCrosses (M.edges c) (D ∪ t.map e)) :=
      fun h => hnot (mem_filter.mpr ⟨htPow,h⟩)
    push Not at dis
    exact ⟨crosses_of_edge dis.1,crosses_of_edge dis.2⟩

end WildNumber.Reduction
