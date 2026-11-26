import WildNumber.MatchingModel

namespace WildNumber.Reduction

open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

private theorem cross_map (e : α ≃ β) (E : Finset (Finset α)) (S : Finset α) :
    EdgeCrosses (E.map e.finsetCongr.toEmbedding) (S.map e.toEmbedding) ↔ EdgeCrosses E S := by
  constructor
  · rintro ⟨t,ht,u,hu,hS,v,hv,hn⟩
    obtain ⟨t, ht, rfl⟩ := mem_map.mp ht
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hu
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hv
    exact ⟨t, (mem_map' e.finsetCongr.toEmbedding).mp ht, u, (mem_map' _).mp hu,
      (mem_map' _).mp hS, v, (mem_map' _).mp hv, fun h => hn (mem_map_of_mem _ h)⟩
  · rintro ⟨t,ht,u,hu,hS,v,hv,hn⟩
    exact ⟨_, mem_map_of_mem _ ht, _, mem_map_of_mem _ hu, mem_map_of_mem _ hS,
      _, mem_map_of_mem _ hv, fun hm => hn ((mem_map' _).mp hm)⟩

private theorem colorBad_map (e : α ≃ β) (E : Finset (Finset α)) (D : Finset α) :
    colorBad (E.map e.finsetCongr.toEmbedding) (D.map e.toEmbedding) =
      (colorBad E D).map e.finsetCongr.toEmbedding := by
  ext t
  obtain ⟨t,rfl⟩ := e.finsetCongr.surjective t
  change e.finsetCongr.toEmbedding t ∈ _ ↔ e.finsetCongr.toEmbedding t ∈ _
  rw [mem_map' e.finsetCongr.toEmbedding]
  change t.map e.toEmbedding ∈ _ ↔ _
  simp only [colorBad, mem_filter, mem_powersetCard, card_map, ← map_union, cross_map]
  have eq : (D.map e.toEmbedding)ᶜ = Dᶜ.map e.toEmbedding := by ext; simp
  rw [eq, map_subset_map]

theorem inside_map_card (e : α ≃ β) (E : Finset (Finset α)) (D : Finset α) :
    ((E.map e.finsetCongr.toEmbedding).filter (· ⊆ D.map e.toEmbedding)).card =
      (E.filter (· ⊆ D)).card := by
  rw [filter_map, card_map]
  congr 1
  exact filter_congr (fun t _ => map_subset_map)

theorem localSpec_map (e : α ≃ β) {E : Finset (Finset α)} {D : Finset α} {c : α}
    (h : LocalSpec E D c) :
    LocalSpec (E.map e.finsetCongr.toEmbedding) (D.map e.toEmbedding) (e c) := by
  obtain ⟨size, degree, center, cross⟩ := h
  unfold LocalSpec
  dsimp only
  rw [colorBad_map, inside_map_card, card_map]
  have hm {x : α} : e x ∈ D.map e.toEmbedding ↔ x ∈ D := mem_map' e.toEmbedding
  simp only [hm]
  refine ⟨size, ?_, ?_, (cross_map e E D).mpr cross⟩
  · intro v hv
    obtain ⟨v,rfl⟩ := e.surjective v
    simp only [e.injective.eq_iff, filter_map, card_map]
    convert degree v (fun h => hv (hm.mpr h)) using 2
    apply filter_congr
    exact fun t _ => mem_map' e.toEmbedding
  · intro hc ha v hv hvc
    obtain ⟨v,rfl⟩ := e.surjective v
    obtain ⟨t,ht,hc',hv'⟩ := center hc ha v (fun h => hv (hm.mpr h))
      (fun h => hvc (congrArg e h))
    exact ⟨_, mem_map_of_mem _ ht, mem_map_of_mem _ hc', mem_map_of_mem _ hv'⟩

end WildNumber.Reduction
