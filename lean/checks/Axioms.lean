import SourceRuntime
import Lean

/-!
Run after `lake build` with `lake env lean checks/Axioms.lean`.
Check axiom dependencies of project theorems, including private and generated
helpers. The allowed axioms are Lean's standard logical axioms; in particular,
`sorryAx` is not allowed. This does not check agreement with the paper's rules.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (privateToUserName name).toString.startsWith "SourceRuntime." then
      if let .thmInfo _ := info then
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "{name} depends on unexpected axiom {axiomName}"
        count := count + 1
  logInfo m!"Checked {count} project theorem constants (including private and generated helpers)."
