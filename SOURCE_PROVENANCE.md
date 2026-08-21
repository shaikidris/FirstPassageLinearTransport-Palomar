# Source provenance and preservation port

## Submission scaffold

The repository layout, metadata validator, CI structure, and Comparator wrapper
were derived from the official
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) at commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`. The toy theorem and every template
metadata value were removed.

## Frozen source

The formal proof in this repository was extracted from the public release:

- repository: <https://github.com/shaikidris/FirstPassageLinearTransport>
- annotated tag: `lean-v3.2.0`
- commit: `ef3410843bf58d69f771f5ba2c0571d54b54da59`
- Git tree: `cba3f26b483c431fc8b86e291b7cb5e5e6475f72`
- software archive: <https://doi.org/10.5281/zenodo.21930432>
- archived file: `FirstPassageLinearTransport_lean_ef34108.zip`
- archived file size: `404886` bytes
- archived file MD5: `49c68a22851018bf58b25f65b26117eb`
- original toolchain: Lean `v4.15.0`
- original pinned Mathlib commit:
  `9837ca9d65d9de6fad1ef4381750ca688774e608`

The source tag was first built and axiom-audited before extraction. The isolated
root was `FirstPassageLinearTransport.ShrinkingNaturalDensityDescent`. Its
source dependency cone contains 58 modules. Legacy, alternate, companion, and
unrelated roots were not copied.

## Exact paper-strength theorem wrapper

`FirstPassageLinearTransport/PaperCor12Item1.lean` adds the literal
specialization corresponding to preprint Corollary 1.2(1). It selects every
exceptional exponent
`0 < gamma < kappa_* (A - A_FP)`, keeps separate landing and exceptional
constants, and absorbs the finite startup without reducing the chosen
exceptional exponent. Together with the 58-module cone, this makes 59 project
modules in the submission package.

This wrapper was not present in the frozen `lean-v3.2.0` release and this file
does not claim otherwise. It was assembled from the already-proved shrinking
natural-density interface and the paper's scalar specialization, then built on
the original Lean 4.15.0/Mathlib pins. Its public theorem was axiom-audited
before the Palomar port and reported only `propext`, `Classical.choice`, and
`Quot.sound`.

## Port to Palomar's supported toolchain

Palomar requires Lean 4.28.0 or later. This package uses the preservation-first
choice Lean `v4.28.0` and the exact Mathlib revision in `lake-manifest.json`.
The migration changed no advertised hypotheses or conclusions. Compatibility
edits in the frozen dependency cone were limited to:

- moved Mathlib import paths;
- replacement of the frozen umbrella `import Mathlib` with explicit Mathlib
  imports, including explicit imports for declarations that the old umbrella
  supplied transitively;
- current scoped notation for finite sums and products;
- explicit namespace qualification for moved lemmas;
- explicit cast, addition-order, and square-root normalization where the newer
  elaborator no longer inferred the old proof term;
- removal of tactic calls that became redundant after stronger simplification;
- replacement of renamed library lemmas by their direct successors.

For the exact-rate wrapper itself, the Lean 4.28 port needed only one algebraic
step removed after stronger simplification and one explicit ordered-addition
proof. `Solution.lean` proves the auditable `Challenge.lean` declaration by
definitional reduction to
`FirstPassageLinearTransport.paper_cor12_item1_fixed_polylog`.

## Verification boundary

The proof development outside `Challenge.lean` contains no `sorry`, `admit`, or
project-specific `axiom`. `Challenge.lean` contains one deliberate `sorry` in
the statement-only surface required by the Comparator workflow. `Audit.lean`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The strengthened package was also replayed from a fresh copy on Linux with the
pinned Comparator, `lean4export`, Landrun, and NanoDa revisions in
`scripts/verify-comparator.sh`. Comparator exported the declaration from both
`Challenge.lean` and `Solution.lean`; NanoDa and Lean's default kernel accepted
the solution.

This provenance record does not claim that Palomar has reviewed or accepted the
submission, nor that kernel checking establishes the informal manuscript's
novelty or significance.
