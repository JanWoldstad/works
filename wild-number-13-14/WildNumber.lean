import WildNumber.Main
import Lean.Util.CollectAxioms

/-! Building the default target also checks the transitive axiom dependencies
of the public results, including the finite computations they use. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for decl in #[``WildNumber.wildNumber_K13, ``WildNumber.wildNumber_K14,
      ``WildNumber.case_zero, ``WildNumber.case_one, ``WildNumber.reduction_covers_every_coloring,
      ``WildNumber.minimum_palette_thirteen, ``WildNumber.minimum_palette_fourteen] do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} checked with axioms {axioms}"
