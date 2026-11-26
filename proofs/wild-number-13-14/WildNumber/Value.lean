import WildNumber.Graph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.Lattice.Nat

namespace WildNumber

/-- On a nonempty vertex set, the connectivity condition in the definition
is equivalent to each augmented color class containing a spanning tree. -/
theorem connects_iff_spanning_trees {n : Nat} [Nonempty (Fin n)] (C : Coloring n)
    (W : Finset (Sym2 (Fin n))) :
    Connects C W ↔ ∀ c, ∃ T : SimpleGraph (Fin n), T ≤ joined C W c ∧ T.IsTree := by
  constructor
  · intro h c
    exact (show (joined C W c).Connected from ⟨h c⟩).exists_isTree_le
  · intro h c
    obtain ⟨T,hT,htree⟩ := h c
    exact htree.connected.preconnected.mono hT

/-- The paper's wild number: the least cardinality of a set of genuine
unordered edges whose union with each color class is spanning and connected. -/
noncomputable def wildNumber {n : Nat} (C : Coloring n) : Nat :=
  sInf {w | ∃ W : Finset (Sym2 (Fin n)), ValidWild W ∧ Connects C W ∧ W.card = w}

theorem wildNumber_eq_of_bounds {n k : Nat} (C : Coloring n) (hu : Upper C k)
    (hl : ∀ W : Finset (Sym2 (Fin n)), ValidWild W → Connects C W → k ≤ W.card) :
    wildNumber C = k := by
  obtain ⟨W, hv, hk, hc⟩ := hu
  have hcard := Nat.le_antisymm hk (hl W hv hc)
  let S := {w | ∃ W : Finset (Sym2 (Fin n)), ValidWild W ∧ Connects C W ∧ W.card = w}
  have member : k ∈ S := ⟨W, hv, hc, hcard⟩
  apply Nat.le_antisymm (Nat.sInf_le member)
  obtain ⟨W',hv',hc',hw'⟩ := Nat.sInf_mem (show S.Nonempty from ⟨k,member⟩)
  exact hw' ▸ hl W' hv' hc'

end WildNumber
