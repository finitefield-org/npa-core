# Package-Verifier Process-Memo Execution-Scope Rollout

Status: mandatory implementation and deterministic acceptance complete; one
historical pre-v0.2 dirty diagnostic recorded; clean current-source rebuild and
reviewed release comparison pending

First `npa-api` release line: `0.4.0`

This note records the source-breaking migration from an implicit unbounded
process-global verifier memo to explicit caller-owned bounded storage. It does
not change certificate acceptance, checker identity, package-lock validation,
or the proof-evidence boundary. The current adjacent-source line is newer than
the last published external toolchain tag; the version above identifies the
first crate release line containing this API and does not assert that a newer
external tag has already been published.

## Source migration

The zero-data `PackageVerificationMemoMode::ProcessLocal` constructor now
requires a `PackageVerificationProcessMemoHandle`. Construct the handle with
explicit `PackageVerificationProcessMemoLimits`, retain the owner for as long
as reuse is wanted, and pass clones of that same handle in successive
`PackageVerificationExecutionOptions` values. A fresh handle is an isolated
empty store.

The following global APIs were removed without deprecated wrappers:

| Removed symbol | Replacement |
| --- | --- |
| `clear_package_verification_process_memo()` | `PackageVerificationProcessMemoHandle::clear()` on the caller-owned handle |
| `package_verification_process_memo_entry_count()` | `PackageVerificationProcessMemoHandle::stats()?.retained_entries` |
| implicit process-global singleton | `PackageVerificationProcessMemoHandle::new(PackageVerificationProcessMemoLimits { ... })` |

`PackageVerificationProcessMemoHandle::limits()` is infallible. `stats()` and
`clear()` return `PackageVerificationProcessMemoAccessError::Poisoned` when the
store mutex cannot be accessed. Verification does not turn that acceleration
failure into a package-verification failure: the first unavailable-store access
increments the run's `bypassed_store_unavailable` counter once, disables store
access for the remainder of that run, and continues through the live checker.

## Capacity and execution scope

Every handle has two required nonzero limits: retained entry count and aggregate
weighted certificate bytes. Entry weight is the exact checked certificate byte
slice used by its memo key; it is a deterministic logical retention budget, not
an allocator-specific resident-set-size claim. An individually oversized value
is rejected without evicting current residents. Otherwise least-recently-used
entries are evicted until both limits admit the insertion. Lookup refreshes
recency, replacement removes the old weight first, cumulative counters
saturate, and `clear()` returns the shared store to the exact fresh state while
preserving immutable limits.

Memo-key work is restricted to the selected module's transitive execution
closure, while every key still contains the canonical full package-lock hash
and the existing checker, policy, import, expected-hash, and certificate-byte
identities. Disabled memoization and a valid empty execution closure build no
memo keys, hash no certificate bytes for memoization, and access no handle.
The ordinary CLI always disables this API-owned process memo, including live
work under disk-memo and audit-cache policies.

Process-memo reuse is local acceleration only. Cached values, memo counters,
store statistics, benchmark output, and `locally_accelerated` diagnostics are
not persistent proof evidence and cannot replace canonical cache-disabled
source-free fast/reference verification.

## Performance evidence boundary

The deterministic structural gate is the closed 11-profile baseline at
`testdata/performance/baselines/package-verifier-process-memo-scope.v0.1.json`.
It checks disabled and empty zero work, closure-scoped key and byte counts, warm
hits, and bounded post-warmup store state without storing elapsed thresholds or
absolute paths. The hermetic script test checks the exact 11-forward plus
11-reverse matrix order, shared build identities, canonical five-field outer
schema, atomic no-replace publication, failure closure, and the zero-placeholder
self-hash rule.

The release diagnostic command is:

```sh
./scripts/check-performance.sh \
  --package-verifier-process-memo-iut-root ../npa-project-iut/proofs \
  --output target/performance/package-verifier-process-memo-execution-scope.json
```

Current runs use the build-bound
`npa.package_verifier.process_memo_scope.run.v0.2` schema. The matrix validator
re-applies the complete nested run contract and scenario baseline before
self-hash acceptance; the pre-v0.2 shape below is retained only as history.

A local macOS arm64 dirty-worktree release binary has run that command to
completion. This is historical diagnostic evidence only, not build-bound or
current-source acceptance: the pre-v0.2 record accepted runtime Cargo.lock and
caller-supplied source identity, omitted target/rustflags/harness-source
identity, and the binary may predate the final Summary serializer
strengthening. Its reported source identity is
`d6e67f0ee1b1e43d6c2b5e6ca2b245aee216e58e-dirty`, its build identity is
`sha256:651e8f2726133b019c59997afeaca9734a8d829006d03d3f48321884a2d79729`,
and its `npa.package_verifier.process_memo_scope.matrix.v0.1` envelope contains
11 catalog entries, two passes, 22 records, and 11 unique scenarios. The
internal zero-placeholder artifact hash is
`sha256:c294d6334578f5fe32a659f464abd022999f42007aceb42c0e45ab8a186e1089`;
the emitted whole-file SHA-256 is
`2c5efa10da76c843856edc796a47920c838a46bd2f73b3b4044f37a1a3a51ec2`.
The temporary file is not preserved release evidence, and no elapsed
comparison is published from it. The current serializer is covered separately
by its focused exact-envelope test and scoped Clippy gate.

A clean current-source rebuild, clean committed source identity, preserved
release binaries/artifact, and reviewed comparison therefore remain pending.
The blocking deterministic
conclusion is that an exact comparable empty IUT closure records zero memo keys
and zero memo hash bytes; the audited historical input was 46,772,555 potential
memo-hash bytes. If the current IUT identity differs from 992 local modules,
six external imports, 998 full execution entries, 46,772,555 checked
certificate bytes, or zero changed certificates, the workload is non-comparable
rather than a new baseline.

Timing-off totals and timing-enabled attribution remain separate populations.
Any eventual elapsed conclusion is advisory, and this rollout proves no
cross-revision regression or speedup because it does not pin a pre-change
executable. The raw matrix stays under `target/` and is not committed.
