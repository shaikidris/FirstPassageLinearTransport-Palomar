# Source provenance and Version 4 strengthening

## Submission scaffold

The repository layout, metadata validator, CI structure, and Comparator wrapper
derive from the official
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) at commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`. Template theorem and placeholder
metadata were removed.

## Paper records

The four selected declarations correspond to the Version 4 manuscript of
[*Polylogarithmic Descent for Almost All Collatz Orbits in Natural
Density*](https://doi.org/10.2139/ssrn.7290240). The persistent SSRN DOI is the
primary citation record and was revised to Version 4 on 6 September 2026.
Zenodo DOI `10.5281/zenodo.22525724` is the immutable Version 4 manuscript.
Zenodo DOI `10.5281/zenodo.22130385` remains the preceding immutable Version
3.2.4 manuscript and is not evidence for the Version 4 additions.

The corresponding immutable Version 4 Lean archive is Zenodo DOI
`10.5281/zenodo.22525757`. The canonical source release is tag
`lean-v4.0.0`, commit `a419e012be2aeb735387385a711c211651ccf527`, in
`shaikidris/FirstPassageLinearTransport`.

## Preceding frozen source

The earlier formal proof was released as:

- repository: <https://github.com/shaikidris/FirstPassageLinearTransport>
- annotated tag: `lean-v3.2.0`
- commit: `ef3410843bf58d69f771f5ba2c0571d54b54da59`
- Git tree: `cba3f26b483c431fc8b86e291b7cb5e5e6475f72`
- software archive: <https://doi.org/10.5281/zenodo.21930432>
- archived file: `FirstPassageLinearTransport_lean_ef34108.zip`
- archived file size: `404886` bytes
- archived file MD5: `49c68a22851018bf58b25f65b26117eb`
- original toolchain: Lean `v4.15.0`
- original Mathlib commit: `9837ca9d65d9de6fad1ef4381750ca688774e608`

That release and Palomar version 3 predate the finite-ballot endpoint,
centered-clock, first-passage, reciprocal-height, and stretched
relative-height additions selected here.

## Immutable identifier roles

| Role | Repository | Commit |
|---|---|---|
| Palomar scaffold | `PalomarRegistry/PalomarTemplate` | `128a6c5ce5f48622e69927ccd639cbff401022e8` |
| Preceding research source | `shaikidris/FirstPassageLinearTransport` | `ef3410843bf58d69f771f5ba2c0571d54b54da59` |
| Preceding research source tree | Git tree of the preceding source | `cba3f26b483c431fc8b86e291b7cb5e5e6475f72` |
| Preceding source Mathlib | `leanprover-community/mathlib4` | `9837ca9d65d9de6fad1ef4381750ca688774e608` |
| Preceding registered Palomar source | `shaikidris/FirstPassageLinearTransport-Palomar` | `68d0ab1454968a75c90b1423439477f456225713` |
| Version 4 substantive proof-cone checkpoint | `shaikidris/FirstPassageLinearTransport-Palomar` | `a72e440e4e862724e027b6101c0ec5e0958597f1` |
| Canonical Version 4 source release | `shaikidris/FirstPassageLinearTransport` | `a419e012be2aeb735387385a711c211651ccf527` |
| Version 4 Mathlib dependency pin | `leanprover-community/mathlib4` | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The exact Palomar submission snapshot is recorded out of band by the registry;
it is not written into its own commit. The registry-facing package was ported
from the canonical Version 4 release and retains its own immutable commit
history.

## Version 4 proof development

The strengthened proof was developed first in the isolated Version 4 research
tree. The candidate adds the following substantive modules and their transitive
dependencies:

- `FiniteBallot.lean` for the finite survival and endpoint estimate;
- `TimeoutDensity.lean` and `TimeoutProfile.lean` for the improved timeout
  density and transported terminal factor;
- `TimeoutTrajectoryProfile.lean` and `CriticalEndpointConsequences.lean` for
  centered tubes, first-passage clocks, arbitrary divergent multipliers, and
  the exact fixed-`A` endpoint;
- `ReciprocalHeightObstruction.lean`, `FixedJointExceptionalOrder.lean`, and
  `SharpJointExceptionalOrders.lean` for the height-forced joint lower bound;
- `StretchedRelativeHeight.lean` for the smaller common height ceiling in the
  stretched-logarithmic result.

The selected reader-facing roots are imported by `SolutionV4.lean`. Their
exact statements are duplicated in the Mathlib-only `Challenge.lean` and
matched by `comparator.json`.

## Palomar toolchain

This package uses Lean `v4.33.0` and the exact Mathlib revision committed in
`lake-manifest.json`. Compatibility changes made while porting project-local
dependencies are limited to import paths, current notation, namespace and
lemma names, explicit casts or normalizations needed by the newer elaborator,
and tactic compatibility. No selected hypothesis or conclusion is changed by
those porting edits.

## Selected-surface fidelity

`SolutionV4.lean` reduces its four declarations to:

- `FirstPassageLinearTransport.critical_polylogarithmic_descent_with_arbitrary_multipliers`;
- `FirstPassageLinearTransport.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate`;
- `FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge_log_order`;
- `FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeightQuantitative`.

The fixed-`A` selected theorem retains a target constant `C`; the manuscript's
constant-one normalization is a separate written adjustment. The reciprocal
lower bound is joint and height-forced. The stretched theorem uses strict
`sigma < 1-delta` and fixed rational clock slacks. These boundaries are
recorded in `formalization.yaml` and are not promoted silently.

## Verification boundary

The proof development outside `Challenge.lean` contains no `sorry`, `admit`,
or project-specific `axiom`. `Challenge.lean` contains four deliberate
`sorry`s required by the Comparator workflow. `AuditV4.lean` is expected to
report only `propext`, `Classical.choice`, and `Quot.sound` for all selected
declarations.

The preceding Solution/Audit surface and its unreachable dependencies remain
available at its immutable Git commit and Palomar record rather than being
copied into this release cone. The current Comparator and default Lake targets
use `SolutionV4` and `AuditV4`. The strengthened candidate requires its own
local full build and a fresh independent Comparator/Landrun/NanoDa replay. No
earlier Palomar review is treated as verification of the Version 4 additions.

This provenance record does not claim that the strengthened candidate has
already been registered by Palomar, reviewed by a person, or accepted by a
journal. The public preprint and software deposits are archival records, not
peer review or registry verification.
