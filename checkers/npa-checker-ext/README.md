# npa-checker-ext

`npa-checker-ext` is the clean-room OCaml external checker prototype for NPA
high-trust release workflows. It is intentionally outside the Cargo workspace
and has no Rust crate dependency.

This checker is not part of the default public package-author path. Base
external package CI remains reference-checker-only, with an optional labeled
fast-kernel verifier result. External checker evidence is optional high-trust
release evidence only when the release workflow supplies pinned checker
binaries, runner policy, checker registry, release policy, and release audit
evidence.

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

GitHub Actions status, release pages, registry metadata, benchmark rows, and
uploaded artifacts are review or release metadata. They are not proof evidence
by themselves.

## High-Trust Use

Use this checker only through an explicit high-trust release workflow such as
`ci-templates/github-actions/npa-package-high-trust.yml`. That workflow must
provide all of these inputs before external checker commands run:

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

The external checker command shape is:

```sh
npa package verify-certs --root . --checker external \
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

The current executable still uses the first-release skeleton check path. It
provides deterministic CLI behavior for `--version`, deterministic errors for
incomplete CLI input, and a stable failed raw result for complete check-shaped
invocations.

The OCaml modules and fixtures cover the checker substrate:

```text
source-free certificate decoding
canonical hash recomputation
import store loading
normal and high-trust import policy
type checking
conversion
simple inductive and recursor checks
axiom report recomputation
axiom policy parsing and enforcement
```

These modules are not yet wired into the standalone executable's complete check
path. Rust-side runner and package integration lives in `crates/npa-api` and
`crates/npa-cli`.

## Build

Build the checker from this directory:

```sh
scripts/build.sh
_build/npa-checker-ext --version
```

`scripts/build.sh` builds one executable at `_build/npa-checker-ext` using
`ocamlc`. Generated files stay under `_build/`.

Set `OCAMLC=/path/to/ocamlc` when `ocamlc` is not on `PATH`. On macOS the
scripts also check Homebrew's `ocaml` prefix.

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
scripts/test.sh positivity
scripts/test.sh recursor
```

The tests are local checker development tests. External theorem package CI
should use the package workflows documented in
`docs/external-theorem-library-ci.md` instead of copying these development
commands.
