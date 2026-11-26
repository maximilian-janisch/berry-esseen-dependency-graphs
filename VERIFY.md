# Checking the Lean proof

Theorem 3 of the paper is `JanischLehericy.conjecture_one_four` in
[Published.lean](JanischLehericy/Published.lean). The stronger truncated-moment
bound is `JanischLehericy.truncated_bound` in [Theorem.lean](JanischLehericy/Theorem.lean).

With [elan](https://github.com/leanprover/elan) installed, run these commands
from the directory containing `lean-toolchain` and `lakefile.toml`. The first
run needs internet access for the pinned toolchain, dependencies, and mathlib cache.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean Replay.lean
```

The build compiles the proof. The audit prints the axiom dependencies and fails
if any of the three end theorems uses an axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. The replay rechecks the theorems and
their dependencies with the Lean kernel, starting from `Init`. For the pinned
versions, the audit reported those three axioms for each theorem and the
replay checked 39,553 declarations above `Init`.
