# Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density — Lean 4

This repository is the self-contained Palomar package for four strengthened
Version 4 consequences of Idris Ali Shaik's preprint
[*Polylogarithmic Descent for Almost All Collatz Orbits in Natural
Density*](https://doi.org/10.2139/ssrn.7290240). The selected results concern
ordinary natural density and use one common shortcut/raw landing where both
maps occur in the same theorem.

The four declarations prove:

1. critical polylogarithmic descent with arbitrary positive functions
   `U(n), R(n) → ∞`, centered shortcut/raw clocks, trajectory tubes, both
   `n R(n)` ceilings, and actual first-passage comparisons at every
   intermediate level;
2. for each fixed `A > A_FP`, the exact upper exceptional exponent
   `q = κ_* A - 1/2`, a common landing, centered clocks, and the balanced joint
   height ceiling;
3. an explicit lower bound of order `X (log X)^(-q)` for failure of the joint
   target-and-height conclusion, forced by the height ceiling; and
4. for `0 < delta < 1`, every strict `0 < sigma < 1-delta`, and `zeta > 0`, a
   quantitative stretched-logarithmic common landing, fixed shortcut/raw
   clock slacks, and both relative-height ceilings
   `n exp(zeta (log n)^(1-delta))`.

Here

```text
κ_*  = 1 - H₂(log₃ 2),
A_FP = 1 / (2 κ_*),
c_*  = 2 / log(4/3).
```

These are almost-all theorems. They do **not** prove pointwise Collatz
convergence, exclude exceptional cycles or divergent trajectories, control an
orbit after a selected witness, or establish density-one descent below a fixed
multiple of the pure critical target `(log n)^A_FP`.

## Auditable statement and proof

- [`Challenge.lean`](Challenge.lean) is the Mathlib-only statement surface. Its
  four `sorry`s are deliberate and excluded from proof-status counts.
- [`Solution.lean`](Solution.lean) states the same four declarations and
  reduces them to the completed project proofs.
- [`FirstPassageLinearTransport/`](FirstPassageLinearTransport/) contains the
  substantive Lean proof modules.
- [`comparator.json`](comparator.json) selects the four Version 4 declarations
  and enables NanoDa replay.
- [`Audit.lean`](Audit.lean) prints the selected declarations' axiom
  dependencies.
- [`formalization.yaml`](formalization.yaml) records scope, paper alignment,
  fidelity boundaries, authorship, automation, and review status.
- [`SOURCE_PROVENANCE.md`](SOURCE_PROVENANCE.md) records the preceding public
  release and this strengthening's preservation boundary.

The preceding surface and its dependencies remain available at the immutable
version-3 source commit; they are not carried as unreachable modules in this
Version 4 release cone.

## Reproduce the checks

The package uses Lean `v4.33.0` and the exact Mathlib revision committed in
`lake-manifest.json`.

```bash
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/check-submission.sh
```

On Linux, with Git, Go, Ruby, Rust/Cargo, Python 3, and Landrun available, run
the independent statement and NanoDa check:

```bash
./scripts/verify-comparator.sh
```

The expected axiom report for every selected declaration is:

```text
propext, Classical.choice, Quot.sound
```

There are no project-specific axioms or admitted obligations in the proof
development.

## Fidelity boundary

The selected fixed-`A` Lean theorem retains a positive target constant `C`;
the paper's normalization to constant one is a separate terminal-rank
adjustment. The joint lower bound is height-forced and is not a lower bound for
target-only failure. The selected stretched theorem retains every strict
`sigma < 1-delta`, with clock coefficients `6953/1000` and `261/25`; it does
not expose the endpoint rate or every admissible clock coefficient. The exact
scope map is in [`formalization.yaml`](formalization.yaml).

## Public records and current candidate status

- persistent preprint/citation record:
  [SSRN Paper 7290240](https://doi.org/10.2139/ssrn.7290240);
- immutable Version 4 manuscript:
  [Zenodo DOI 10.5281/zenodo.22525724](https://doi.org/10.5281/zenodo.22525724);
- canonical Version 4 Lean release:
  [tag `lean-v4.0.0`](https://github.com/shaikidris/FirstPassageLinearTransport/tree/lean-v4.0.0)
  at commit `a419e012be2aeb735387385a711c211651ccf527`;
- immutable Version 4 software archive:
  [Zenodo DOI 10.5281/zenodo.22525757](https://doi.org/10.5281/zenodo.22525757);
- preceding immutable manuscript version:
  [Zenodo Version 3.2.4](https://doi.org/10.5281/zenodo.22130385);
- preceding software archive:
  [Zenodo DOI 10.5281/zenodo.21930432](https://doi.org/10.5281/zenodo.21930432);
- preceding registered verification:
  [PALOMAR-2026-08-26-000005 version 3](https://palomar-registry.org/entry?id=PALOMAR-2026-08-26-000005&version=3).

The Version 4 manuscript, source release, and software archive are public.
They do not replace Palomar verification: this candidate still requires a
fresh mechanical and editorial replay before a new registry version is
registered.

## Provenance and AI disclosure

The preceding proof cone was based on the public `lean-v3.2.0` release at
commit `ef3410843bf58d69f771f5ba2c0571d54b54da59`. The canonical Version 4
development is frozen at tag `lean-v4.0.0`, commit
`a419e012be2aeb735387385a711c211651ccf527`, and adds the finite-ballot
endpoint, centered-clock and first-passage consequences, joint height
obstruction, and stretched relative-height development. The canonical release
uses Lean 4.15.0; this registry-facing port is separately checked with Lean
4.33.0.

OpenAI Codex assisted with proof exploration, Lean construction and diagnosis,
dependency-cone work, statement alignment, audits, and package preparation.
Idris Ali Shaik supplied the research direction, mathematical constraints,
protocol and audit harnesses, evaluated the proof architecture and outputs,
made all release decisions, and accepts responsibility for every claim. Other
generative-AI tools were used only for exposition or minor review, not for the
formalized proof argument.

## Licence

Apache License 2.0. See [`LICENSE`](LICENSE).

Palomar submissions use <https://submit.palomar-registry.org/>.
