import WildNumber.AbstractCases
import WildNumber.Coverage
import WildNumber.FiniteRoot
import WildNumber.FiniteTheorem
import WildNumber.Lift
import WildNumber.LocalMatching
import WildNumber.Lower
import WildNumber.Orbit
import WildNumber.Palette
import WildNumber.Value

namespace WildNumber

/-- A forbidden family subject to the reduction's bounds always admits a
partition into three good triples. The imported proofs establish coverage
of the representatives and check every branch of their refutations. -/
theorem nine_point_split : Reduction.NinePointClaim :=
  Nine.Census.split_of_orbits Nine.Orbit.canonicalize
    (fun d hd g hg => (Nine.Orbit.rep_facts d hd g hg).1)
    (fun d hd g hg => Nine.Census.all_representatives g (Nine.Orbit.rep_facts d hd g hg).2)

theorem case_zero (A : Nine.Endgame 0) : Nine.GoodSplit A.forbidden :=
  Nine.A13_zero nine_point_split A

theorem case_one (A : Nine.Endgame 1) : Nine.GoodSplit A.forbidden :=
  Nine.A13_one nine_point_split A

theorem nine_suffice_thirteen (C : Coloring 13) : Upper C 9 :=
  Reduction.upper_of_reduction Reduction.per_color nine_point_split C

/-- Conjecture 6.1 for every minimum proper edge coloring on thirteen vertices. -/
theorem wildNumber_K13 (C : Coloring 13) : wildNumber C = 9 :=
  wildNumber_eq_of_bounds C (nine_suffice_thirteen C) (fun _ _ => lower_thirteen C)

/-- Conjecture 6.1 for every minimum proper edge coloring on fourteen vertices. -/
theorem wildNumber_K14 (C : Coloring 14) : wildNumber C = 9 :=
  wildNumber_eq_of_bounds C (upper_fourteen_of_thirteen nine_suffice_thirteen C)
    (fun _ _ => lower_fourteen C)

end WildNumber
