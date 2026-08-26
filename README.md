# Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density — Lean 4

This repository is the self-contained Palomar submission package for four
formally proved almost-all results from Idris Ali Shaik's preprint
[*Polylogarithmic Descent for Almost All Collatz Orbits in Natural
Density*](https://doi.org/10.2139/ssrn.7290240). The primary public preprint
record is [SSRN Paper 7290240](https://www.ssrn.com/abstract=7290240); the
versioned manuscript archive is
[Zenodo Version 3.2.3](https://doi.org/10.5281/zenodo.21984038).

The submitted declarations are:

1. a general moving-endpoint first-passage theorem for bounded exponent
   profiles whose explicit entropy buffer tends to infinity, including a
   quantitative dyadic-shell exceptional-ratio estimate;
2. the exact fixed-exponent specialization below;
3. a stretched-logarithmic same-witness companion for every
   `0 < delta < 1`, with a `6.953 log n` clock and an orbit ceiling through the
   same witness; and
4. a quantitative stretched-logarithmic exceptional-count theorem for every
   strict exponent `0 < sigma < 1 - delta`.

For the fixed-exponent theorem, every polylogarithmic exponent

```text
A > 1 / (2 * (1 - H₂(log₃ 2))),
```

put `κ_* = 1 - H₂(log₃ 2)` and
`A_FP = 1 / (2 κ_*)`. For every clock coefficient
`c > 2 / log(4/3)`, every `beta > 0`, and every

```text
0 < gamma < κ_* (A - A_FP),
```

there are separate positive constants `Ctar` and `Cexc` such that almost every
positive integer `n` has one witness `k < c log n` satisfying

```text
T^[k](n) ≤ Ctar (log n)^A
```

and every earlier iterate through that same witness is at most
`n^(1 + beta)`. The exceptional count up to `X` is eventually at most
`Cexc X (log X)^(-gamma)`.

The stretched declaration reaches
`exp((log n)^(1-delta))` on a natural-density-one set for every
`0 < delta < 1`, within `6953/1000 * log n` shortcut steps, while every
iterate through the witness is at most `n^(1+beta)`.

Separately, for every `0 < sigma < 1 - delta`, the quantitative stretched
declaration supplies a constant `rate > 0` such that the number of `n ≤ X`
with no shortcut iterate below `exp((log n)^(1-delta))` is eventually at most

```text
5 X exp(-rate (log X)^sigma).
```

This count concerns the unclocked landing event. It is not the manuscript's
stronger joint clock/ceiling predicate, and it does not include the endpoint
`sigma = 1 - delta`.

These are almost-all theorems. They do **not** prove the pointwise Collatz
conjecture, exclude exceptional cycles or divergent trajectories, or control
an orbit after a selected witness.

## Auditable statement and proof

- [`Challenge.lean`](Challenge.lean) is the small, Mathlib-only statement
  surface. Its four `sorry`s are deliberate and are excluded from proof-status
  counts.
- [`Solution.lean`](Solution.lean) states the same four declarations and
  connects each one to the completed proof.
- [`FirstPassageLinearTransport/`](FirstPassageLinearTransport/) contains the
  complete 82-module union of the four source dependency cones plus the exact
  paper-strength fixed-rate wrapper (83 project modules in total).
- [`comparator.json`](comparator.json) asks Comparator to check all four
  advertised declarations and replay them with NanoDa.
- [`Audit.lean`](Audit.lean) prints each theorem's axiom dependencies.
- [`formalization.yaml`](formalization.yaml) records scope, source alignment,
  authorship, automation, fidelity, and review status.
- [`SOURCE_PROVENANCE.md`](SOURCE_PROVENANCE.md) pins the frozen source and
  records the preservation-oriented port.

## Reproduce the checks

The project uses Lean `v4.33.0` and a committed Lake manifest.

```bash
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/check-submission.sh
```

On Linux, with Git, Go, Ruby, Rust/Cargo, Python 3, and Landrun available, run
the independent statement and NanoDa check as well:

```bash
./scripts/verify-comparator.sh
```

The expected axiom report for each of the following declarations is exactly
the three-item list shown below:

- `CollatzFirstPassage.moving_polylogarithmic_natural_density_descent`
- `CollatzFirstPassage.polylogarithmic_natural_density_descent`
- `CollatzFirstPassage.stretched_logarithmic_descent_with_orbit_ceiling`
- `CollatzFirstPassage.stretched_logarithmic_quantitative_exceptional_count`

```text
propext, Classical.choice, Quot.sound
```

These are standard Lean/Mathlib logical axioms; there are no project-specific
axioms or admitted obligations in the proof development.

## Scope relative to the full formalization

This package contains the exact dependency-cone union for the four advertised
declarations. It does not advertise the manuscript's literal critical
log-log/triple-log specializations, the stretched theorem's endpoint
`sigma = 1 - delta`, one joint quantitative predicate with every clock
`c > 2/log(4/3)` and the same-witness ceiling, the unaccelerated-map clock
conversion, or the remaining companion interfaces. See the precise
correspondence and exclusions in
[`formalization.yaml`](formalization.yaml).

## Provenance and AI disclosure

The proof cone was extracted from the public frozen release
[`lean-v3.2.0`](https://github.com/shaikidris/FirstPassageLinearTransport/tree/lean-v3.2.0)
at commit `ef3410843bf58d69f771f5ba2c0571d54b54da59`. The union of the moving,
fixed, qualitative stretched, and quantitative stretched theorem cones was
extracted from that release. The exact-rate Corollary 1.2(1) wrapper was
assembled from the proved cone, checked on Lean 4.15.0, and the resulting
83-module package was ported to Lean 4.33.0
without strengthening any advertised hypothesis or conclusion.
The archived source release is
[Zenodo DOI 10.5281/zenodo.21930432](https://doi.org/10.5281/zenodo.21930432).

OpenAI Codex assisted with Lean proof
construction, diagnostics, dependency-cone extraction, the preservation port,
and documentation. Idris Ali Shaik supplied the research direction,
mathematical constraints, protocol and audit harnesses, evaluated the proof
architecture and outputs, made the release decisions, and accepts
responsibility for every claim. Other generative-AI tools were used only for
exposition or minor review, not for the formalized proof argument.

## Licence

Apache License 2.0. See [`LICENSE`](LICENSE).

Palomar submissions use <https://submit.palomar-registry.org/>.
