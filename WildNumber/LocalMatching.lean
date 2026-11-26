import WildNumber.MatchingOrbit
import WildNumber.MatchingProfile
import WildNumber.MatchingRelabel

namespace WildNumber.Reduction

open Finset

/-- The four local cut rules, transported from the four shapes of a
four-set in a six-edge matching to an arbitrary named color class. -/
theorem per_color (M : NamedClasses) (c : V) (D : Finset V) (hD : D.card = 4)
    (ha : (inside M D c).card ≤ 1) : LocalSpec (M.edges c) D c := by
  classical
  obtain ⟨e, miss, edges⟩ := exists_standard_matching M c
  obtain ⟨F, hF⟩ := e.finsetCongr.surjective D
  change F.map e.toEmbedding = D at hF
  subst D
  have cardF : F.card = 4 := by simpa using hD
  have full : (sixPairs.filter (· ⊆ F)).card ≤ 1 := by
    change ((M.edges c).filter (· ⊆ F.map e.toEmbedding)).card ≤ 1 at ha
    rwa [← edges, inside_map_card] at ha
  obtain ⟨j,hj⟩ := four_set_profiles F (mem_powersetCard.mpr ⟨subset_univ _, cardF⟩) full
  obtain ⟨f,hf,hpair,hD'⟩ := relabel_profile hj
  have h := localSpec_map f (representative_spec j)
  rw [hf, hpair, hD'] at h
  have result := localSpec_map e h
  rwa [edges,miss] at result

end WildNumber.Reduction
