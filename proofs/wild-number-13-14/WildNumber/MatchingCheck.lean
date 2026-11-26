import WildNumber.MatchingModel
import Mathlib.Tactic.FinCases

namespace WildNumber.Reduction

/-- Representatives indexed by whether the missed point belongs to the
four-set and whether the four-set contains a full edge. -/
def representative : Fin 4 → Finset Pos
  | 0 => {some (0,0), some (1,0), some (2,0), some (3,0)}
  | 1 => {some (0,0), some (0,1), some (1,0), some (2,0)}
  | 2 => {none, some (0,0), some (1,0), some (2,0)}
  | 3 => {none, some (0,0), some (0,1), some (1,0)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem representative_spec (j : Fin 4) : LocalSpec sixPairs (representative j) none := by
  fin_cases j <;> decide +kernel

end WildNumber.Reduction
