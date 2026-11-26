import JanischLehericy
import Lean.Util.CollectAxioms

#print axioms JanischLehericy.adjacent_pair_inequality
#print axioms JanischLehericy.stein_estimate
#print axioms JanischLehericy.truncated_bound
#print axioms JanischLehericy.janisch_lehericy
#print axioms JanischLehericy.conjecture_one_four

open Lean in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for n in [`JanischLehericy.truncated_bound, `JanischLehericy.janisch_lehericy,
      `JanischLehericy.conjecture_one_four] do
    for ax in ← collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {n}"
