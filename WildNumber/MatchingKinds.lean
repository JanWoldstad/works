import WildNumber.MatchingCheck

namespace WildNumber.Reduction

/-- The number of endpoints of pair `i` in the four-set. -/
def kind (D : Finset Pos) (i : Fin 6) : Fin 3 :=
  if some (i,0) ∈ D then (if some (i,1) ∈ D then 2 else 1)
  else if some (i,1) ∈ D then 1 else 0

def profile (D : Finset Pos) (k : Fin 3) := (Finset.univ.filter fun i => kind D i = k).card

def SameProfile (D F : Finset Pos) : Prop :=
  (none ∈ D ↔ none ∈ F) ∧ ∀ k, profile D k = profile F k

instance (D F : Finset Pos) : Decidable (SameProfile D F) := by
  unfold SameProfile; infer_instance

end WildNumber.Reduction
