# Contributing

This repository is a preservation-oriented Palomar package for selected
mathematical results. Contributions that improve compatibility, documentation,
or verification are welcome. A change to the mathematical statement or proof
architecture must be proposed separately and must not be presented as a
mechanical port of an earlier release.

Before opening a pull request:

1. Keep `Challenge.lean` a small Mathlib-only statement surface with exactly
   four deliberate `sorry`s, one for each selected declaration.
2. Keep the corresponding completed proof in `SolutionV4.lean` and update
   `comparator.json` if the advertised declaration surface changes.
3. Record any source-fidelity or toolchain change in `SOURCE_PROVENANCE.md` and
   `formalization.yaml`.
4. Do not add legacy, alternate, manuscript, generated, or unrelated modules to
   the selected four-theorem dependency cone.
5. Run:

   ```bash
   lake build
   ruby scripts/validate-formalization.rb
   ./scripts/check-submission.sh
   ```

6. On a supported Linux host, also run:

   ```bash
   ./scripts/verify-comparator.sh
   ```

The repository is Apache-2.0 licensed. By contributing, you agree that your
contribution is made under that licence.
