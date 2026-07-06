# External Theorem Library CI

This document explains how an external NPA theorem package repository should
run pull request and release checks. It is written for package authors who want
to copy the GitHub Actions templates from this repository.

The current source-build toolchain recommendation is:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

CI is orchestration and review evidence. It is not proof evidence. A passing
GitHub Actions workflow does not become checker input and does not change proof
acceptance. Proof acceptance remains based on canonical `.npcert` bytes,
source-free checker or kernel verifier verdicts, and deterministic package
artifact hashes.

## Template Files

Copyable templates live under:

```text
ci-templates/github-actions/
```

The base package-author files are:

```text
ci-templates/github-actions/npa-package-pr.yml
ci-templates/github-actions/npa-package-release.yml
ci-templates/github-actions/setup-pinned-npa.sh
ci-templates/github-actions/summarize-npa-diagnostics.py
ci-templates/github-actions/validate-workflows.py
ci-templates/github-actions/README.md
```

The optional high-trust release extension is:

```text
ci-templates/github-actions/npa-package-high-trust.yml
```

Install the copied `npa-package-*.yml` files under `.github/workflows/` in the
theorem package repository. Keep helper scripts under
`ci-templates/github-actions/`, or update the helper script paths in the
workflow YAML in the same review.

Do not copy local `npa` repository development gates such as:

```sh
scripts/phase8-release-audit.sh
scripts/phase9-regression.sh
```

Those scripts test this repository's checker and regression fixtures. External
theorem package repositories should run package commands against their own
package root.

## Pinned Toolchain Setup

External theorem package CI must use exactly one pinned `npa` source:

```text
NPA_BINARY_PATH
  Path to an existing executable npa binary.

NPA_VERSION
  Exact release version or release tag for a later release-download strategy.
  This mode is currently rejected until release-download artifacts are added.
  The value latest is invalid.

NPA_GIT_TAG
  Exact immutable Git tag for building npa-cli.

NPA_GIT_COMMIT
  Full lowercase 40-hex Git commit SHA for building npa-cli.
```

If none or multiple are set, `setup-pinned-npa.sh` fails before running package
commands. Branch names such as `main`, `master`, `HEAD`, `stable`, and
floating values such as `latest` are not valid verifier implementation pins.

When CI builds `npa-cli` from `NPA_GIT_TAG` or `NPA_GIT_COMMIT`, it fetches the
pinned `npa` implementation and the exact Rust toolchain as tool setup. That is
separate from theorem package dependency resolution. Package checks must not
fetch theorem packages, package imports, registry metadata, hidden package
cache entries, or implicit latest versions.

The setup step prints:

```sh
npa --version
cargo --version
rustc --version
```

`cargo --version` and `rustc --version` are required only when Rust is used to
build `npa-cli`.

## Pull Request Gate

The pull request workflow is the default contributor gate. It checks a theorem
package from a fresh checkout with a pinned `npa` toolchain and explicit
package root:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package check-hashes --root . --json
npa package verify-certs --root . --checker reference --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
```

PR mode should save deterministic command JSON under package-relative paths
such as:

```text
ci-output/package-check.json
ci-output/build-certs.json
ci-output/check-hashes.json
ci-output/verify-certs-reference.json
ci-output/axiom-report.json
ci-output/index.json
```

The PR gate is full-package reference verification. It intentionally does not
use changed-module selectors until package-command changed-module support is a
documented public workflow.

PR mode must not:

- use `--changed`;
- use `--all`;
- use `--checker external`;
- use `--registry`, `--network`, or `--latest`;
- write back to the contributor branch;
- upload secrets;
- contact an NPA package registry;
- resolve imports through hidden package caches or implicit latest versions;
- trust source, replay, meta, tactic trace, AI trace, prompt metadata, or
  theorem index data as proof evidence.

## Release Gate

The base release workflow runs from a clean checkout at the release ref. It
records package artifact checks and source-free verification results:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package check-hashes --root . --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
npa package verify-certs --root . --checker fast --json
npa package verify-certs --root . --checker reference --json
```

Fast verifier output must be labeled fast-kernel. It must not be reported as
reference checker success.

Release mode may also check publish metadata when the package intentionally
checks in `generated/publish-plan.json` and sets `NPA_ENABLE_PUBLISH_PLAN` to
`true`:

```sh
npa package publish-plan --root . --check --json
```

Publish metadata is release review metadata, not proof evidence, and it does
not imply that a registry server exists.

Allowed release uploads include generated package metadata, checked
certificates, command JSON diagnostics, and plain text summaries. Default
uploads must exclude AI traces, tactic traces, prompt metadata, secrets,
host-specific caches, absolute runner paths, unredacted environment dumps, and
unchecked source-derived state.

## Evidence Profiles

Base PR and release workflows produce reference-checker-only evidence:

```text
reference checker source-free verdict
optional labeled fast-kernel verifier result
deterministic package diagnostics and artifact hashes
```

Reference-checker-only evidence does not produce `verified_high_trust` and does
not require an external checker binary.

High-trust evidence is a separate opt-in release profile. It requires pinned
checker binaries, runner policy, checker registry metadata, release policy, and
release audit evidence before verifier commands run. It is not part of the PR
hot path and must not be inferred from reference-checker-only CI.

## Optional High-Trust Extension

`npa-package-high-trust.yml` is the optional high-trust workflow. Copy it only
after the theorem package repository provides all of these inputs:

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

The external checker command is source-free:

```sh
npa package verify-certs --root . --checker external \
  --runner-policy ci/runner.high-trust.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json \
  --json
```

That command may read package metadata, package lock, canonical `.npcert`
files, import certificates, runner policy, checker registry, checker
executable bytes, and axiom policy. It must not read `.npa` source, replay
files, meta files, theorem index files, AI traces, registry network data,
hidden package caches, plugins, or source-derived unchecked environments.

The high-trust workflow also validates release audit evidence and generates or
checks `verified_high_trust` through:

```sh
npa package high-trust --root . \
  --release-policy ci/release.high-trust.json \
  --release-policy-hash "$NPA_RELEASE_POLICY_HASH" \
  --runner-policy ci/runner.high-trust.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --challenge-runner-policy ci/runner.challenge.json \
  --challenge-runner-policy-hash "$NPA_CHALLENGE_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json \
  --out generated/verified-high-trust.json \
  --check \
  --json
```

`verified_high_trust` must be emitted only after external checker and
high-trust-reference release audit evidence validates. It must not be emitted
from reference-checker-only release evidence.

External checker benchmark rows are release audit metadata. They can support a
release/high-trust regression policy, but they are not proof input and do not
change proof validity or checker verdicts.

## Diagnostics

Structured command output should be saved as deterministic JSON diagnostics.
Failure summaries may show the failed command, exit code, diagnostic kind,
reason code, module, package-relative path, and expected or actual hashes when
available.

Copyable templates may use
`ci-templates/github-actions/summarize-npa-diagnostics.py` to render a summary
table from package command JSON:

```text
file | command | status | exit_code | kind | reason_code | module | path | expected_hash | actual_hash
```

The table must use package-relative paths such as
`generated/package-lock.json` or `Proofs/A/certificate.npcert`. It must not
include absolute host paths, environment dumps, secrets, caches, or raw stderr
with local runner state.

Common diagnostic mappings:

| Diagnostic | Likely cause | Contributor action |
| --- | --- | --- |
| `source_hash_mismatch` | A checked source file changed but the package metadata still pins the old source bytes. | Review the source change, then update package metadata through the normal package update flow. Rerun `npa package check-hashes --root . --json`. |
| `certificate_hash_mismatch`, `certificate_file_hash_mismatch`, or `export_hash_mismatch` | A certificate artifact is stale, missing from the package lock, or no longer matches manifest pins. | Rebuild/check certificates explicitly, review the certificate and lock diffs, then rerun hash checks and source-free verification. |
| `reference_checker_rejected` | The canonical `.npcert` bytes are not accepted by the independent reference checker. | Treat this as a proof/certificate failure. Fix the theorem or certificate generation path and rerun reference verification. |
| `axiom_policy_rejected` or `axiom_report_policy_violation` | A certificate or package axiom report uses an axiom outside package policy. | Remove the unapproved axiom dependency or update the package axiom policy through review. |
| `axiom_report_stale` or `axiom_report_hash_mismatch` | The checked axiom report no longer matches verified certificates. | Regenerate `generated/axiom-report.json`, review the diff, then rerun `npa package axiom-report --root . --check --json`. |
| `theorem_index_stale` or `theorem_index_hash_mismatch` | The theorem index metadata no longer matches verified certificates. | Regenerate `generated/theorem-index.json`, review the diff, then rerun `npa package index --root . --check --json`. |
| missing `NPA_CHECKER_EXT_BINARY_PATH`, missing `ci/checker-binaries.json`, or `checker_binary_file_unreadable` | The high-trust workflow cannot resolve a pinned external checker from the fresh checkout. | Add the reviewed `npa-checker-ext` executable and matching checker registry entry. Do not depend on a runner cache or registry network lookup. |
| `checker_binary_hash_mismatch`, `checker_identity_mismatch`, or `checker_build_hash_mismatch` | External checker bytes or identity metadata differ from runner policy pins. | Treat the checker binary as changed release evidence. Review build provenance, then update runner policy, checker registry, and checker identity metadata together. |
| `not_verified`, `checker_disagreement`, `status_disagreement`, or normalized comparison failure | Required checker profiles did not all produce the same checked release result. | Inspect saved external and release audit JSON. Fix the certificate/checker disagreement; do not relabel fast-kernel or reference output as external success. |

Theorem index and axiom report metadata are derived review/search artifacts.
They are not proof evidence.

## Template Validation

Run the local no-network validator from the `npa` repository root:

```sh
python3 ci-templates/github-actions/validate-workflows.py
```

The validator checks YAML syntax, required package commands, forbidden base
workflow flags, and high-trust command wiring. `actionlint` is also useful when
installed:

```sh
actionlint ci-templates/github-actions/*.yml
```

If `actionlint` is unavailable, use the local validator and a YAML parser
fallback:

```sh
for workflow in ci-templates/github-actions/*.yml; do
  ruby -e 'require "yaml"; YAML.load_file(ARGV.fetch(0))' "$workflow"
done
```

## Explicit Exclusions

Base package workflows must not:

- use registry lookup;
- use hidden package caches;
- use package dependency solvers;
- resolve implicit latest package versions;
- require external checker mode;
- emit `verified_high_trust`;
- trust source files, replay files, theorem indexes, publish plans, CI status,
  GitHub release pages, registry metadata, AI traces, or tactic traces as
  proof evidence;
- depend on this repository's local phase gates.
