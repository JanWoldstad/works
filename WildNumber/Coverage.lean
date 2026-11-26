import WildNumber.Normalization
import WildNumber.Reduction

namespace WildNumber

/-- The matchings of an arbitrary coloring, named by their missing vertices. -/
noncomputable def classesOf (C : Coloring 13) : Reduction.NamedClasses :=
  Reduction.namedClasses (normalizedColor C) (normalizedColor_symm C)
    (normalizedColor_diag C) (normalizedColor_injective C)

/-- Every coloring has at least 130 suitable four-sets. Each is rainbow and
belongs to one of the two cases, according to the number of internal edges
whose color is named for a vertex of the four-set. -/
theorem reduction_covers_every_coloring (C : Coloring 13) :
    let M := classesOf C
    130 ≤ (Reduction.eligible M).card ∧ ∀ D ∈ Reduction.eligible M,
      D.card = 4 ∧ (∀ c, (Reduction.inside M D c).card ≤ 1) ∧
        ((Reduction.internalNames M D).card = 0 ∨ (Reduction.internalNames M D).card = 1) := by
  refine ⟨Reduction.eligible_card _, fun D hD => ?_⟩
  obtain ⟨h4, hr, hk⟩ := Reduction.eligible_properties _ hD
  exact ⟨h4, hr, by omega⟩

end WildNumber
