# NPA Toolchain Reference v0.8.0

This is the current adjacent-source reference for `npa-cli 0.8.0`. It keeps
`package_api::v1`, advances package command results to
`npa.package.command_result.v0.4`, and adds bounded fast-kernel fuel hotspot
diagnostics to package certificate authoring. The diagnostics are operational
telemetry: they do not change proof acceptance and never enter certificates,
package locks, declaration identities, cache keys, or checker identities.

The [v0.7 reference](npa-toolchain-reference-v0.7.0.md) is retained as an
immutable historical compatibility reference. Do not relabel a v0.7 result or
release record as v0.8.

## Version axes

| Axis | Current value |
| --- | --- |
| Host CLI crate | `npa-cli 0.8.0` |
| Programmatic facade | `package_api::v1` |
| Package command result | `npa.package.command_result.v0.4` |
| Common performance measurements | `npa.performance.measurements.v0.3` |
| Package timing envelope | `npa.package.timings.v0.2` |
| Kernel fuel diagnostic | `npa.kernel-fuel-diagnostic.v0.1` |
| Reference checker | `0.4.0` |
| External checker | `0.3.0` |
| Current emitted certificate/core pair | `NPA-CERT-0.3.0` / `NPA-Core-0.3.0` |
| Read-only certificate compatibility inputs | exact v0.2.0, v0.1.2, and v0.1 pairs |
| Generated-artifact release manifest | `npa.generated_artifact_release_manifest.v0.2` |

The release validator accepts only these exact host/result families:

| Host CLI | Command-result schema | Classification |
| --- | --- | --- |
| `npa-cli 0.3.x` / `0.4.x` | `npa.package.command_result.v0.1` | historical |
| `npa-cli 0.5.x` | `npa.package.command_result.v0.2` | historical |
| `npa-cli 0.6.x` / `0.7.x` | `npa.package.command_result.v0.3` | historical |
| `npa-cli 0.8.x` | `npa.package.command_result.v0.4` | current |

Cross-pairs reject. In particular, an 0.7 host cannot emit a v0.4 result and
a v0.3 result cannot be renamed to v0.4.

## Rust crate versions

The public Rust changes were migrated atomically so adjacent path consumers do
not observe a partially compatible workspace:

| Crate | Historical v0.7 axis | Current v0.8 axis | Source boundary |
| --- | ---: | ---: | --- |
| `npa-kernel` | 0.2.0 | 0.3.0 | domain-separated fuel and bounded work observations |
| `npa-frontend` | 0.3.0 | 0.4.0 | fuel-report selection and declaration observations |
| `npa-api` | 0.3.0 | 0.4.0 | common measurement v0.3 and nullable declaration `kernel` data |
| `npa-cli` | 0.7.0 | 0.8.0 | CLI/API selectors and command-result v0.4 writers |

The other current workspace axes used by this reference are `npa-cert 0.4.0`,
`npa-checker-ref 0.4.0`, `npa-package 0.3.0`, and `npa-tactic 0.2.0`.

`npa-web` and `npa-corpus/tools/proof-corpus` require the adjacent path
dependency `npa-cli = "0.8"`. From the aggregate container root, verify the
complete locked/offline consumer set with:

```sh
./scripts/check-package-api-compatibility.sh
```

The gate discovers every adjacent `npa-cli` path consumer, checks its tracked
lockfile, rejects raw construction of non-exhaustive package options, and
verifies that the run does not mutate source, locks, or proof artifacts.

## Package authoring flags and defaults

`package build-certs` accepts two independent operational selections:

```text
--kernel-fuel-report off|failure|detailed
--timings off|summary|detailed
```

The defaults are `--kernel-fuel-report failure` and `--timings off` for the
CLI and every `package_api::v1` build/refresh constructor. Neither selection
implies the other.

From a theorem package root, an ordinary checked build with explicit defaults
is:

```sh
npa package build-certs --root . --check \
  --kernel-fuel-report failure --timings off --json
```

Fuel mode semantics are:

| Fuel mode | Exhaustion report | Structural path | Retained delta hotset | Successful declaration kernel record |
| --- | --- | --- | --- | --- |
| `off` | none | existing conversion context only | none | none |
| `failure` | fuel and bounded operation/declaration work | yes | none | none |
| `detailed` | same failure data | yes | bounded names and counts | only with timing `detailed` |

Timing mode semantics are:

| Timing mode | Common measurement output | Declaration rows |
| --- | --- | --- |
| `off` | none | none |
| `summary` | aggregate counters | none |
| `detailed` | aggregate and bounded detail | retained independently of fuel mode |

All nine mode pairs are distinct and supported:

| Fuel | Timings | Failure behavior | Successful output |
| --- | --- | --- | --- |
| `off` | `off` | no `kernel_fuel` | no common report |
| `failure` | `off` | failure-local fuel/work/path | no common report |
| `detailed` | `off` | failure-local data plus hotset | no common report; successful kernel summary is discarded |
| `off` | `summary` | no `kernel_fuel` | aggregate counters only |
| `failure` | `summary` | failure-local fuel/work/path | aggregate counters only |
| `detailed` | `summary` | failure-local data plus hotset | aggregate counters only; successful kernel summary is discarded |
| `off` | `detailed` | no `kernel_fuel` | declaration rows with `kernel: null` |
| `failure` | `detailed` | failure-local fuel/work/path | declaration rows with `kernel: null` |
| `detailed` | `detailed` | failure-local data plus hotset | declaration rows with non-null accepted-kernel summaries |

`off` creates no fuel-specific path/name collector. With timings also off it
uses the disabled work-meter fast path. A timing mode may collect existing
scalar work counters, but it cannot create `kernel_fuel` or enable memoization.
Every pair preserves certificate bytes, declaration hashes, package locks,
cache keys, proof identities, the primary error, and acceptance/rejection.

## Programmatic package API v1

Use the versioned constructors rather than raw `PackageBuildCertsOptions`
literals:

```rust
use npa_cli::args::{KernelFuelReportMode, PackageTimingMode};
use npa_cli::package_api::v1::{build_certs_check, common_options};

let options = build_certs_check(common_options("proofs", true))
    .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
    .with_timings(PackageTimingMode::Detailed);
```

The additive selectors apply to all four build constructors:

- `build_certs_check`;
- `build_certs_write`;
- `refresh_artifacts_check`; and
- `refresh_artifacts_write`.

`with_kernel_fuel_report` and `with_timings` replace only their own selection;
their call order is immaterial. Existing `with_build_check_cache`,
`with_modules`, and `with_changed` builders retain their v1 meaning. Raw
`PackageBuildCertsOptions` construction remains outside the adjacent-consumer
contract because that type is non-exhaustive.

## Command-result v0.4 and fuel diagnostics

All package command writers now emit v0.4, including commands that cannot
produce a fuel report. V0.4 adds one optional `kernel_fuel` sibling to a
command diagnostic; it does not mutate the strict historical `conversion`
object. `kernel_fuel` is absent in fuel mode `off`, for non-fast checkers, and
for errors unrelated to fast-kernel WHNF or conversion exhaustion.

A present `npa.kernel-fuel-diagnostic.v0.1` records:

- `trusted: false` and `proof_evidence: false`;
- subsystem `fast_kernel` and resource `conversion` or `whnf`;
- exact failed-operation budget, spent, remaining, and bounded work;
- domain-separated declaration fuel plus declaration work;
- a bounded structural comparison path;
- an optional bounded retained-delta summary in detailed mode; and
- explicit truncation and overflow markers.

The failed operation is a subset of the enclosing declaration. A standalone
WHNF exhaustion has an empty, non-truncated comparison path and is never
misreported as conversion. Names, paths, and counters describe kernel work;
they are not source spans or complete expression/proof dumps.

## Common performance measurement v0.3

The outer `npa.package.timings.v0.2` object is unchanged. Its nested common
measurement is now strictly `npa.performance.measurements.v0.3`; exact v0.1
and v0.2 inputs remain historical read-only compatibility.

Every retained declaration row has this required shape:

```json
{
  "module": "Example",
  "declaration_index": 0,
  "declaration": "Example.theorem",
  "term_nodes": 42,
  "elaboration_elapsed_ns": 0,
  "kernel": null
}
```

The `kernel` member is required and nullable. It is non-null only for the joint
`--kernel-fuel-report detailed --timings detailed` selection and then records
subsystem `fast_kernel`, outcome `accepted`, declaration fuel/work, a required
bounded retained-delta summary, and overflow state. Other timing-detailed pairs
retain the ordinary declaration row with `kernel: null`. At most 2,048 rows are
retained in canonical module/index/name order; attempted, retained, and omitted
counts disclose truncation.

Measurements are operational and nonsemantic. They never enter `.npcert`
bytes, declaration/certificate/export/axiom hashes, package manifests or locks,
generated artifact identities, cache keys, runner policies, or checker
identities. They must never be treated as trusted artifacts or proof evidence.

## Cache identity and one-time migration effect

The crate-version migration intentionally causes one ordinary cache miss for
identities that already include `CARGO_PKG_VERSION`: `npa-api 0.4.0` changes
built-in package-verifier checker identities and `npa-cli 0.8.0` changes
package build-check tool identities. Existing cache rules rebuild the entries;
no cache schema is relabeled.

Within a fixed v0.8 toolchain, neither fuel-report nor timing selection enters
compiler-option projections, audit/build cache keys, verifier memo keys, or
checker identities. Switching among the nine pairs therefore causes no second
version-derived invalidation and cannot select cache/memo behavior.

## Troubleshooting kernel fuel exhaustion

Rerun the same checked authoring command with detailed fuel reporting; do not
change the fuel limit:

```sh
npa package build-certs --root . --check \
  --kernel-fuel-report detailed --timings detailed --json
```

Interpret the bounded output structurally:

| Observation | Proof-authoring response |
| --- | --- |
| Delta steps dominate and one retained constant dominates | Put an opaque theorem boundary around that computation and expose a semantic specification theorem. |
| Declaration work is much greater than failed-operation work | Split the declaration into meaningfully named, independently kernel-checkable lemmas. |
| Application-argument path steps dominate | Replace whole-term definitional equality with explicit operation congruence lemmas. |
| Dependent-function-body path steps dominate | Isolate binder transport with an explicit transport theorem or prove a pointwise lemma. |
| WHNF work/fuel dominates | Replace deep unfolding with small explicit evaluation theorems and compose them across opaque boundaries. |

A truncated hotset is not a global top-K. Refactor and rerun rather than
inferring completeness. Never respond by raising kernel conversion fuel: doing
so hides proof structure and increases worst-case trusted work without
identifying the cause.

## External checker and trust boundary

Fuel diagnostics describe only the fast Rust kernel. The Rust reference
checker and OCaml `npa-checker-ext 0.3.0` retain their independent resource
limits and diagnostics; no v0.8 evidence may attribute a `kernel_fuel` report
to an external checker run.

From an aggregate root where `npa-core/` and the literal package root `proofs/`
are siblings, collect cache-disabled checker results with:

```sh
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked --checker fast \
  --audit-cache off --verifier-memo off --json
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked --checker external \
  --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.release.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json --json
```

The current external-checker compatibility gate runs from the `npa-core` root:

```sh
checkers/npa-checker-ext/scripts/toolchain-v0.8.sh
checkers/npa-checker-ext/scripts/toolchain-v0.8.sh --functional-only
```

The full gate is a clean Linux release requirement. On a platform without
kernel-sealed immutable checker staging, the functional command completes its
portable checker-build and host-test checks and then fails closed, before
policy preflight or external execution, with
`checker_binary_immutable_snapshot_unsupported`; finish both functional
closure and the full release gate on clean Linux. The generated v0.8 archive,
checksum, and manifest are disposable compatibility evidence and must not be
published as theorem-package release assets.

Canonical certificates plus a kernel or source-free checker verdict remain the
proof authority. Command results, fuel/performance measurements, runner logs,
release metadata, and compatibility-gate status are review evidence only.

## Previous capabilities

V0.8 retains the v0.7 theorem-premise report, six-part generated-artifact
closure, interface-proposal validation, promotion-origin reconciliation,
package-root-relative export paths, targeted artifact refresh/rebind, external
prerequisite closure, package-lock modes, ledger audit, and checker selection.
Their original contracts remain documented in the historical
[v0.7 reference](npa-toolchain-reference-v0.7.0.md); v0.8 changes their shared
command-result envelope to v0.4 without changing their semantic artifact
formats.

For the complete fuel diagnostic invariants and bounds, see the
[kernel fuel hotspot design](../../docs/core/kernel-fuel-hotspot-diagnostics-design.md).
For the common measurement contract, see the
[performance observability design](../../docs/core/proof-authoring-performance-observability-design.md).
