# npa-checker-ext

`npa-checker-ext` is the clean-room OCaml external checker for NPA checked
package verification. It is intentionally outside the Cargo workspace and has
no Rust crate dependency.

The clean-room checker is `0.4.0`, advertises the exact
`NPA-CERT-0.4.0` / `NPA-Core-0.4.0` capability pair, and emits raw checker
result v2. It accepts only that pair. Every older, unknown, or mixed pair is
rejected while decoding the header, before any term or module payload is
interpreted.

In raw-result v2, capability fields are always
`certificate_format = NPA-CERT-0.4.0` and
`core_spec = NPA-Core-0.4.0`. Once the exact header pair is decoded,
`input_certificate_format` and `input_core_spec` record that exact input pair;
they are not copied from package manifest/lock profiles. A checked result also
binds `module`, `certificate_hash`, `export_hash`, and `axiom_report_hash`.

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

The executable implements only the source-free Core v0.4.0 check path:

```text
strict v0.4 source-free certificate decoding and canonical re-encoding
v0.4 declaration/module and retained export/report hash recomputation
the exact six-form term grammar with retired tag 0x06 rejection
tagged interface and local-implementation dependency verification
independent local opaque-transparency closure recomputation
checked local opaque bodies exposed only after checking
assumption-only local typing contexts with beta, delta, and iota conversion
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
scripts/test.sh fixture-matrix
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

The live three-way differential runner, Rust raw-result v2 parser, checker
registry binding, and committed Rust-derived fixtures are implemented. Run the
integration gate with:

```sh
scripts/differential.sh
```

That gate reads the shared v0.4 fixture matrix, regenerates and byte-compares
all 16 committed conformance certificates, and compares fast, reference, and
OCaml verdicts. For every accepted certificate it also compares the module,
certificate, export, and axiom-report identities and binds the decoded input
pair separately from the checker's capability pair. It covers every old or
mixed header row, all retired-`0x06` tail shapes, source-path rejection, a
resource-bound failure, Rust raw-result parsing, a source-free import DAG, and
the facade argument and policy/registry boundary, plus the filesystem/network
trace when `strace` is available. Full v0.9 package-runner adoption belongs to
Milestone 5.

### Current host and release gate

The checker is exercised from the current `npa-cli 0.9.0` host. Use
`scripts/differential.sh` for the v0.4 checker acceptance matrix, then run the
package release gates from the self-contained v0.9.0 toolchain reference. The
runner binds checker identity, binary hash, input pair, policy, and raw-result
schema; an unpinned local build is not release evidence.

No retired host script, compatibility facade, or old-host allowlist is callable
from this repository. Historical specifications remain version-scoped records
only and do not define a supported command path.

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
