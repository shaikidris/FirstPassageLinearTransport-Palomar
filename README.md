# Polylogarithmic Collatz Descent in Natural Density — Lean 4

This repository is the self-contained Palomar submission package for one
principal theorem from Idris Ali Shaik's preprint
[*Polylogarithmic Descent for Almost All Collatz Orbits in Natural
Density*](https://doi.org/10.5281/zenodo.21984038).

For the shortcut Collatz map, the formalized theorem says that for every fixed
polylogarithmic exponent

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

This is an almost-all theorem. It does **not** prove the pointwise Collatz
conjecture, exclude exceptional cycles or divergent trajectories, or control
an orbit after the selected witness.

## Auditable statement and proof

- [`Challenge.lean`](Challenge.lean) is the small, Mathlib-only statement
  surface. Its single `sorry` is deliberate and is excluded from proof-status
  counts.
- [`Solution.lean`](Solution.lean) states the same declaration and connects it
  to the completed proof.
- [`FirstPassageLinearTransport/`](FirstPassageLinearTransport/) contains the
  complete 58-module source dependency cone plus the exact paper-strength
  theorem module (59 project modules in total).
- [`comparator.json`](comparator.json) asks Comparator to check the advertised
  declaration and replay it with NanoDa.
- [`Audit.lean`](Audit.lean) prints the theorem's axiom dependencies.
- [`formalization.yaml`](formalization.yaml) records scope, source alignment,
  authorship, automation, fidelity, and review status.
- [`SOURCE_PROVENANCE.md`](SOURCE_PROVENANCE.md) pins the frozen source and
  records the preservation-oriented port.

## Reproduce the checks

The project uses Lean `v4.28.0`, the minimum stable version accepted by Palomar
when this package was prepared, and a committed Lake manifest.

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

The expected axiom report for
`CollatzFirstPassage.polylogarithmic_natural_density_descent` is exactly:

```text
propext, Classical.choice, Quot.sound
```

These are standard Lean/Mathlib logical axioms; there are no project-specific
axioms or admitted obligations in the proof development.

## Scope relative to the full formalization

This package intentionally contains only the dependency cone needed for
Corollary 1.2(1), the fixed-exponent polylogarithmic natural-density theorem
with its full exceptional-rate range. The larger formalization also contains
moving-endpoint, critical log-log,
stretched-logarithmic, raw-map, and other companion interfaces; those are not
advertised or copied here. See the precise exclusions in
[`formalization.yaml`](formalization.yaml).

## Provenance and AI disclosure

The proof cone was extracted from the public frozen release
[`lean-v3.2.0`](https://github.com/shaikidris/FirstPassageLinearTransport/tree/lean-v3.2.0)
at commit `ef3410843bf58d69f771f5ba2c0571d54b54da59`. The exact-rate Corollary
1.2(1) wrapper was then assembled from that proved cone, checked on Lean
4.15.0, and ported to Lean 4.28.0 without changing its hypotheses or
conclusions.
The archived source release is
[Zenodo DOI 10.5281/zenodo.21930432](https://doi.org/10.5281/zenodo.21930432).

OpenAI Codex materially assisted with proof exploration, Lean proof
construction, diagnostics, dependency-cone extraction, the preservation port,
and documentation. Idris Ali Shaik supplied the research direction,
mathematical constraints, protocol and audit harnesses, evaluated the proof
architecture and outputs, made the release decisions, and accepts
responsibility for every claim. Other generative-AI tools were used only for
exposition or minor review, not for the formalized proof argument.

## Licence

Apache License 2.0. See [`LICENSE`](LICENSE).

Palomar submissions use <https://submit.palomar-registry.org/>.
