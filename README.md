# Application Delegation

Code accompanying the POPL 2027 SRC extended abstract.

`lean/` contains the calculus and proofs. The main results are
`preservation` in `Runtime/Preservation.lean`, `seq_to_obs` in
`Runtime/Completeness.lean`, and `obs_to_seq` in `Runtime/Soundness.lean`,
under `lean/SourceRuntime/` (namespace `SourceRuntime.Runtime`).
`ocaml/` contains the concurrent and sequential interpreters.
`examples/` contains the three-stage list pipeline and a type checker for
object-oriented programs, with a successful input and a return-type error.
Executable examples use the existing `fix` syntax; the abstract presents
recursive definitions using `let rec` shorthand.

Use Lean 4.30.0 (selected by `lean-toolchain`) and an opam environment with
OCaml, Dune 3.7 or later, Menhir, and Zarith. From this directory:

```sh
(cd lean && lake build && lake env lean checks/Axioms.lean)
opam exec -- dune build --root ocaml
opam exec -- dune runtest --root ocaml
./run.sh runtime pipeline --trace-rules
./run.sh source pipeline
./run.sh runtime checker-valid --trace-rules
./run.sh source checker-valid
./run.sh runtime checker-error
```

The pipeline returns the list `[6, 4, 2]` paired with `12`.
The checker returns an annotated program or a structured error.
`checks/Axioms.lean` checks that project theorems use only Lean's standard
logical axioms and do not depend on `sorryAx`.

Lean uses the pinned [lean-wsln](https://github.com/elefthei/lean-wsln)
dependency. OCaml includes Bindlib 6.0.0 and PL Zoo support code with their
licenses. The checker adapts part of
[Developing a Monadic Type Checker for an Object-Oriented Language](https://doi.org/10.1145/3357766.3359545);
its upstream license is included in `examples/LICENSE.checker`.
