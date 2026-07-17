# npa-checker-ext

`npa-checker-ext` is the clean-room OCaml external checker for NPA checked
package verification. It is intentionally outside the Cargo workspace and has
no Rust crate dependency.

Its compatibility axes are independent: the host is `npa-cli 0.7.x` through
`package_api::v1`, while the checker, `NPA-CERT-0.2.0`, and `NPA-Core-0.2.0`
remain `0.2.0`. Raw checker and machine results remain v1, package command
results use `npa.package.command_result.v0.3`, and new generated-artifact
evidence uses manifest v0.2. A CLI bump does not relabel the checker or proof
formats.

This checker is not part of the default public package-author path. Base
external package verification remains reference-checker-only, with an optional
labeled fast-kernel verifier result. External checker evidence is optional
release evidence only when the run pins the checker bytes, runner policy,
registry, and build identity. It is not by itself a `verified_high_trust`
outcome; that separate outcome also requires the aggregate release/challenge
policy and audit bundle.

## Trust Boundary

The external checker path is source-free. High-trust verifier commands may read:

```text
package metadata
package lock
canonical .npcert files
import certificates
runner policy
checker registry
checker executable bytes
axiom policy
```

They must not trust:

```text
.npa source files
replay files
meta files
theorem indexes
AI traces
tactic traces
registry network data
hidden package caches
plugins
source-derived unchecked environments
```

Certificate, policy, and import-directory paths are opened component by
component with no-follow semantics. A required input rejects a symlink in
either the final component or an ancestor. Symlinked import candidates are
ignored, and regular candidates are read from the descriptor opened during
bounded traversal.

Release pages, registry metadata, benchmark rows, and uploaded artifacts are
review or release metadata. They are not proof evidence by themselves.

## Checked External And High-Trust Use

For ordinary pinned external verification, use an explicit checked NPA lock,
one job, and disabled acceleration. Policy, registry, and checker paths are
relative to the package root; `--locked` and `--offline` belong to Cargo, not
to the installed `npa` command:

```sh
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked \
  --checker external --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.release.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json --json
```

External mode rejects reconstructed lock input, changed-only selection, local
cache or memo modes, and more than one job before package I/O. Successful runs
write only these package-relative trees:

```text
generated/checker-imports/<package>/<version>/<module>/external/
generated/checker-results/<package>/<version>/<module>/external/
```

An explicit high-trust release check additionally provides all of these inputs
before external checker commands run:

```text
NPA_CHECKER_EXT_BINARY_PATH
NPA_RELEASE_POLICY_HASH
NPA_RUNNER_POLICY_HASH
NPA_CHALLENGE_RUNNER_POLICY_HASH
ci/release.high-trust.json
ci/runner.high-trust.json
ci/runner.challenge.json
ci/checker-binaries.json
generated/release-audit/manifest.json
```

The installed-command equivalent retains the same checked, unaccelerated
contract:

```sh
npa package verify-certs --root . --package-lock checked --checker external \
  --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.high-trust.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json \
  --json
```

`verified_high_trust` must be generated or checked only after external checker
and high-trust-reference release audit evidence validates. It must not be
emitted from reference-checker-only release evidence.

Do not depend on runner caches, package registries, implicit latest resolution,
or unpinned checker binaries for high-trust evidence.

## Current Scope

The executable implements the source-free Core v0.2.0 check path and its
documented v0.1.2 and v0.1 compatibility paths:

```text
versioned source-free certificate decoding and canonical re-encoding
versioned declaration, export, report, and certificate hash recomputation
universe constraints and constraint-committing public interfaces
normal decoded/hash-checked imports
recursive policy-checked high-trust import DAGs
typing, conversion, and exact Nat/Eq builtins
simple, indexed, mutual, and approved List/Option/Prod nested inductives
constructor universe bounds, positivity, recursors, and iota
axiom report recomputation
axiom policy parsing and enforcement
runner-compatible checked and failed raw JSON
deterministic certificate, table, term-depth, import, and conversion limits
```

The axiom-policy artifact uses the exact runner schema: current `format` plus a
canonically ordered `allowed_axioms` array. High-trust sorry/custom-axiom denial
cannot be disabled by policy fields. The runner supplies `--policy-hash`, and
the checker hashes the exact bytes it parses before applying that policy.

Rust-side raw-result adoption and package integration live in `crates/npa-api`
and `crates/npa-cli`. High-trust evidence still requires the runner to pin the
actual binary and build identities; building this directory alone does not
manufacture release evidence.

## Build

Build the checker from this directory:

```sh
scripts/build.sh
_build/npa-checker-ext --version
```

`scripts/build.sh` builds one executable at `_build/npa-checker-ext` using
`ocamlc`. Generated files stay under `_build/`.

The executable exits 0 for a checked verdict, 1 for a structured rejection,
and 2 for CLI misuse or an internal checker failure.

Set `OCAMLC=/path/to/ocamlc` when `ocamlc` is not on `PATH`. On macOS the
scripts also check Homebrew's `ocaml` prefix.

The checker binary can be built and tested directly on macOS, but the current
`npa package verify-certs --checker external` high-trust launcher is enabled
only on Linux/Android, where it executes the hash-verified bytes from a sealed
`memfd`. Other platforms fail closed with
`checker_binary_immutable_snapshot_unsupported`; they do not fall back to a
mutable temporary executable.

## Test

Run the full external checker test suite from this directory:

```sh
scripts/test.sh
```

Targeted suites can be run by passing a suite name:

```sh
scripts/test.sh cli
scripts/test.sh sha256
scripts/test.sh feature-policy
scripts/test.sh axiom-report
scripts/test.sh axiom-policy
scripts/test.sh axiom-policy-parse
scripts/test.sh decoder-bytes
scripts/test.sh decoder-header
scripts/test.sh decoder-tables
scripts/test.sh decoder-declarations
scripts/test.sh decoder-reachability
scripts/test.sh hash-encoder
scripts/test.sh hash-level-term
scripts/test.sh hash-declarations
scripts/test.sh hash-module
scripts/test.sh import-store
scripts/test.sh import-normal
scripts/test.sh import-high-trust
scripts/test.sh type-env
scripts/test.sh type-core
scripts/test.sh type-declarations
scripts/test.sh subst
scripts/test.sh reduce
scripts/test.sh defeq
scripts/test.sh inductive-constructors
scripts/test.sh inductive-universe
scripts/test.sh positivity
scripts/test.sh recursor
scripts/test.sh checker-pipeline
```

Run the cross-implementation, real-package, and source-free boundary gate with:

```sh
scripts/differential.sh
```

This regenerates the committed conformance fixtures, compares the fast kernel,
reference checker, and OCaml verdicts and identities, parses every checker raw
result through the Rust runner schema, exercises a real external package import
DAG, and runs the filesystem/network trace when `strace` is available.

On Linux, run the complete `npa-cli 0.7.x` host compatibility and ephemeral
release-evidence closure from the `npa-core` root with:

```sh
checkers/npa-checker-ext/scripts/toolchain-v0.7.sh
```

The developer-only functional form permits a dirty checkout, runs the same
facade and two direct checks without requiring `strace`, and deliberately does
not evaluate release evidence:

```sh
checkers/npa-checker-ext/scripts/toolchain-v0.7.sh --functional-only
```

The combined gate uses the actual OCaml executable through the v1 facade and
two direct locked/offline runs. It checks a frozen checked lock, full identity
chain, exact command/raw repeatability, narrow machine telemetry differences,
source/network access, transient mutations, and—in full mode—the archive,
checksum, and dynamic v0.2 manifest.

The obsolete v0.3/v0.4 host compatibility scripts and their dedicated tests
have been removed. Historical design records describe those releases but do
not provide a supported or callable compatibility contract.

Remediation is fail-closed: update a stale Cargo lock only through the intended
Cargo dependency workflow; restore or explicitly freeze a missing/stale NPA
package lock; correct invalid external options; regenerate policy, registry,
identity-manifest, or binary pins from final bytes; use Linux sealed staging
for the package launcher; clean the candidate before full mode; install every
required trace tool; and discard/rebuild assets whose checksum disagrees.
Rollback disables the compatibility/release claim—it never rewrites proof
bytes or reinterprets a published schema.

The tests are local checker development tests. External theorem packages should
use `npa package ...` commands against their own package root instead of
copying these development commands.
