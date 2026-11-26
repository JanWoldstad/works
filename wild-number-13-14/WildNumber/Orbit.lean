import WildNumber.Orbit.All
import WildNumber.Orbit.Membership

namespace WildNumber.Nine.Orbit

set_option maxRecDepth 50000

/-- The explicitly checked list contains a relabeling of every eight-point
graph having at most eleven edges. -/
theorem canonicalize (S : Finset (Finset (Fin 8))) (pairs : ∀ t ∈ S, t.card = 2)
    (hs : S.card ≤ 11) :
    ∃ g ∈ reps S.card, ∃ p : Equiv.Perm (Fin 8), ∀ x y, x ≠ y →
      ({x,y} ∈ S ↔ g.testBit (pairIndex (p x) (p y)) = true) := by
  apply canonicalize_of_rows reps (by decide +kernel) _ S pairs hs
  intro d hd
  interval_cases d
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10

end WildNumber.Nine.Orbit
