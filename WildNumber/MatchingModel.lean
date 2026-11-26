import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace WildNumber.Reduction

open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

def EdgeCrosses (E : Finset (Finset α)) (S : Finset α) : Prop :=
  ∃ e ∈ E, ∃ u ∈ e, u ∈ S ∧ ∃ v ∈ e, v ∉ S

instance (E : Finset (Finset α)) (S : Finset α) : Decidable (EdgeCrosses E S) := by
  unfold EdgeCrosses; infer_instance

def colorBad (E : Finset (Finset α)) (D : Finset α) : Finset (Finset α) :=
  (Dᶜ.powersetCard 3).filter fun X => ¬ EdgeCrosses E X ∨ ¬ EdgeCrosses E (D ∪ X)

def LocalSpec (E : Finset (Finset α)) (D : Finset α) (c : α) : Prop :=
  let bad := colorBad E D
  let a := (E.filter (· ⊆ D)).card
  bad.card ≤ (if a = 1 then 4 else if c ∈ D then 1 else 2) ∧
  (∀ v ∉ D, (bad.filter (v ∈ ·)).card ≤
    if v = c ∨ (c ∈ D ∧ a = 1) then 4 else 1) ∧
  (c ∉ D → a = 1 → ∀ v ∉ D, v ≠ c → ∃ T ∈ bad, c ∈ T ∧ v ∈ T) ∧
  EdgeCrosses E D

instance (E : Finset (Finset α)) (D : Finset α) (c : α) : Decidable (LocalSpec E D c) := by
  unfold LocalSpec; dsimp only; infer_instance

abbrev Pos := Option (Fin 6 × Fin 2)
def pairAt (i : Fin 6) : Finset Pos := {some (i,0), some (i,1)}
def sixPairs : Finset (Finset Pos) := univ.image pairAt

end WildNumber.Reduction
