# NPA Toolchain Reference v0.8.0

This is the current adjacent-source reference for `npa-cli 0.8.0`. It keeps
`package_api::v1`, advances package command results to
`npa.package.command_result.v0.4`, and adds typed source-delimiter and bounded
fast-kernel fuel hotspot diagnostics to package authoring. It also publishes
the composed `npa.performance.measurements.v0.8` operational-measurement union
and the prepared-retention-aware fast-shard memory model described below.
These observations are operational telemetry: they do not change proof
acceptance and never enter certificates, package locks, declaration identities,
cache keys, or checker identities.

The [v0.7 reference](npa-toolchain-reference-v0.7.0.md) is retained as an
immutable historical compatibility reference. Do not relabel a v0.7 result or
release record as v0.8.

## Version axes

| Axis | Current value |
| --- | --- |
| Host CLI crate | `npa-cli 0.8.0` |
| Programmatic facade | `package_api::v1` |
| Package command result | `npa.package.command_result.v0.4` |
| Common performance measurements | `npa.performance.measurements.v0.8` |
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
| `npa-api` | 0.3.0 | 0.4.0 | common measurement v0.8, exhaustive fast-shard memory-model additions, and nullable declaration `kernel` data |
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
lockfile, rejects raw construction of non-exhaustive package options, rejects
facade coupling to low-level targeted-cache DTO/context/directory types, and
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

## Source structure preflight

`package check-source-structure` is a read-only, dependency-free authoring
check for Human Surface files. It runs the production lexer and validates the
nesting of `()`, `[]`, and `{}` while correctly ignoring delimiters inside
comments and strings. It does not parse declarations, load imports, elaborate
or type-check terms, read or write certificates, update a manifest or lock, or
produce proof evidence.

The selectors are closed and mutually exclusive:

```text
no selector                 all manifest modules in topological order
--module MODULE ...         registered modules, filtered into topological order
--path PACKAGE_PATH ...     package-relative files in argument order
```

Path mode deliberately does not load `npa-package.toml`, so a newly created
source can be checked before manifest registration. Every selected path is
read through the bounded no-follow package reader. Repeated CLI selector values
are deduplicated without changing their deterministic order. The command stops
at the first selected-source error and never writes package state.

Delimiter failures have diagnostic kind `SourceStructure` and stable reason
codes `unexpected_closing_delimiter`, `mismatched_closing_delimiter`, or
`unclosed_delimiter`. In JSON, `diagnostics[].source` is the unexpected close
or EOF position, while `diagnostics[].delimiter.opening_source` identifies the
corresponding opener when one exists. The delimiter object also exposes
`kind`, nullable `expected_closing`, and nullable `actual_closing`. Ordinary
lexer and UTF-8 failures use `source_lexical_error` and
`source_structure_invalid_utf8`. Consumers must use these typed fields rather
than parsing prose or counting raw source characters.

This preflight should precede the ordinary targeted build after each direct
Human Surface edit. A pass does not imply that balanced delimiters group the
right expressions, so parser and application-shape failures remain the
responsibility of `package build-certs`.

## Canonical refresh fail-fast ordering

`package build-certs --update-manifest-hashes` preserves complete-package
canonical output and validation, but orders its read and build work so a
selected Human Surface error is not hidden behind unrelated certificate work.

After root, manifest, graph, selection, and refresh-target validation, full
refresh reads every local source in package topological order and runs the
Human lexer plus balanced `()`, `[]`, and `{}` validation before reading a
certificate. Targeted `--module` or `--changed` refresh performs that structural
preflight only for the explicit selected seeds. It then processes the smallest
dependency-closed priority prefix needed by those seeds: exact external
support, live-checked local support, and selected or bridge rebuilds. Only
after that prefix and its deferred metadata succeed does the command process
reverse-only dependents, remaining support, and unrelated package snapshots.

Consequently, failure precedence is deterministic:

1. option, package, graph, selection, target-safety, and local-plan failures;
2. selected-source read, UTF-8, lexer, and delimiter failures;
3. priority external and local support failures;
4. priority parser, resolver, application-shape, elaborator, kernel-handoff,
   axiom-policy, and metadata failures;
5. deferred dependents, remaining imports, unrelated snapshots, and refresh
   assembly failures; and
6. artifact comparison or atomic publication failures.

The successful priority outputs are retained as part of the one canonical
build; selected modules are not compiled twice. External certificates read for
priority dependency discovery are verified from those same retained bytes, and
both external phases share one verifier session. A source changed after
preflight is still reread by the canonical module build and may fail there.
No build-check cache supplies canonical refresh context.

Targeted refresh results include `package_build_selection` with the appended
`promotion=none|manifest_changed` value and, after certificate-free planning,
`package_build_refresh_schedule`. The latter reports these bounded counts:

```text
priority_rebuild=<n>,priority_support_local=<n>,
priority_external_roots=<n>,declared_external=<n>,deferred_rebuild=<n>,
deferred_support_local=<n>,snapshot_unrelated_local=<n>
```

On a structural, priority, or completion failure, the result contains
selection, schedule, and the primary diagnostic in that order. The existing
`package_build_refresh_plan` is emitted only after canonical build completion;
comparison or publication failures therefore contain selection, schedule,
completed plan, and primary diagnostic. A changed selection with neither a
local seed nor the package lock keeps its existing no-local-work behavior. A
lock-only changed refresh has an empty priority phase and performs complete
snapshot work in completion.

With `--timings summary|detailed`, targeted refresh adds the optional ordered
metrics `source_preflight_ms`, `priority_build_ms`, and
`completion_build_ms` immediately after `selection_ms`. Full refresh reports
`source_preflight_ms` and `completion_build_ms` but omits
`priority_build_ms`. Entered refresh paths initialize applicable fields to zero,
so a skipped phase remains visible as zero after an early failure. Timing mode
`off` allocates no phase clocks and emits none of these metrics. The timing and
planning records are untrusted diagnostics with `build_evidence=false` and
`proof_evidence=false`; canonical `.npcert` and source-free verification gates
remain unchanged.

## Targeted build-check cache

`package build-certs --check` exposes one closed cache mode selector:

```text
--build-check-cache off|read-through|local-hit
```

The default is `off` for the CLI and every `package_api::v1` constructor. The
supported matrix is:

| Selection and mode | Support work | Explicit targets | Result authority |
| --- | --- | --- | --- |
| full, `off` | all live | all live | ordinary live build-check result |
| full, `read-through` | all live | all live | ordinary live result; cache rows are diagnostic metadata |
| targeted, `off` | selected closure live | every reached target fresh | ordinary targeted live result |
| targeted, `read-through` | selected closure live | every reached target fresh | ordinary targeted live result; eligible live support may be warmed |
| targeted, `local-hit` | exact eligible support hits may be reused; misses and forced/ineligible support are live | every reached target fresh | local-only authoring feedback |

Here “targeted” means exactly one of `--module MODULE` or `--changed` together
with `--check`. Full `local-hit`, any non-off mode without `--check`, and any
non-off refresh or write combination fail as usage errors. Cache mode is never
enabled automatically.

`read-through` is diagnostic warming: it does not skip a support check. It may
write `npa.package.build_check_result.v0.2` result summaries and, for eligible
targeted live support, `npa.package.targeted_authoring_support_context.v0.1`
entries. `build-certs --build-check-cache local-hit` is authoring-only reuse:
it never loads the result-summary store, may consume exact support-context
entries, and may warm only eligible cache-free live miss subtrees whose complete
required local closure was checked live in that invocation. A hit later covered
by a miss-promoted subtree is bypassed and checked live. Support after the first
target, legacy/fallback consumers, and unsupported interfaces remain forced
live. Both non-off modes may write only these disclosed untrusted local stores;
neither writes a package source, certificate, manifest, metadata ledger, or
package lock.

The `build-certs --build-check-cache local-hit` command is local-only even when
it consumes no hit. Its result contains `targeted_authoring_cache_local_only`
with `trusted=false;build_evidence=false;proof_evidence=false` and reports
`locally_accelerated=true` only when a retained exact support hit actually
avoided both its live kernel check and source-interface resolution. Cache
diagnostics and measurements are bounded and omit source text, proof terms,
absolute checkout paths, and payloads.

The similarly named `verify-certs --audit-cache local-hit` is separate. It
selects the verification audit store for `verify-certs`; it does not select the
build-check support store. The two commands and stores are not interchangeable,
and neither kind of cache hit is proof evidence.

## Verify-certs selector modes

`package verify-certs` accepts exactly one of four selection modes:

| CLI selector | Workload | Git input |
| --- | --- | --- |
| none | complete current package | none |
| `--changed` | working-tree changed certificate paths plus imports | current worktree versus `HEAD` |
| one or more `--module MODULE` | explicit local seeds plus imports | none |
| `--base REF` | structurally attributed committed seeds plus imports, or full escalation | unique merge base through committed `HEAD` |

`--changed`, any `--module`, and `--base` are mutually exclusive. Module values
are logical `Name` values, not paths; duplicates, invalid names, and empty
programmatic module lists are usage errors. Unknown valid names fail with
`selected_module_missing` before checker execution. Explicit module selection
uses the current validated manifest and package lock, does not require a clean
worktree, and lets the existing verifier compute the transitive source-free
import closure and canonical output order.

Base mode resolves the raw ref and `HEAD` to immutable commit IDs with
`/usr/bin/git`, computes exactly one merge base, and thereafter passes only
validated hexadecimal object IDs to blob and diff operations. Every Git child
used by package selection first removes every inherited `GIT_*` variable, so
the caller cannot redirect repository discovery, the worktree, index, object
store, refs, configuration injection, or explicit pathspec interpretation.
Every selector Git child then receives command-scoped
`GIT_NO_REPLACE_OBJECTS=1`, so replace refs cannot redirect `HEAD` or validated
object IDs. Base-mode children additionally receive `GIT_NO_LAZY_FETCH=1`, so
unavailable objects fail locally. The effective overridden environment is
included in exec-headroom accounting. This also prevents literal, glob,
noglob, or icase process modes from changing the explicit long-form exact
pathspec protocol. It reads the exact base
`npa-package.toml` and `generated/package-lock.json` blobs, builds a sorted union
of base/current declared source, certificate, meta, replay,
external-certificate, manifest, and lock paths, and uses only top-literal exact
pathspecs. Each literal include is paired atomically with a glob-escaped
descendant exclusion, and different path depths run in separate batches, so a
directory-valued candidate cannot widen the query and an ancestor exclusion
cannot hide a separately declared descendant. Before interpreting the committed diff it rejects every staged,
unstaged, deleted, ordinary untracked, or ignored untracked protected path; it
also rejects protected tracked entries carrying `assume-unchanged`,
`skip-worktree`, unmerged, or other non-ordinary index tags, nonzero stages, or
object modes other than `100644` and `100755`. This prevents index state or
`core.symlinks=false` from presenting a non-ordinary `HEAD` entry as a clean
regular file. It compares the index to `HEAD` and the worktree to the index in
separate diffs, so an unstaged edit cannot cancel a staged content or mode
change. For every otherwise-clean ordinary index blob, bounded
`git hash-object --no-filters` batches compare the raw worktree blob identity
to the index identity, preventing clean filters or end-of-line normalization
from hiding different protected bytes. Every protected clean-head `diff`,
`ls-files`, and raw-hash invocation
uses command-scoped `-c core.fsmonitor=false`, `-c core.trustctime=true`, and
`-c core.checkStat=default`, plus `-c core.fileMode=true`, so neither a stale
fsmonitor hook, weakened stat-cache settings, nor disabled executable-bit
checking can hide a modified protected input, same-size/same-mtime inode
replacement, or worktree mode change. It also queries every
strict protected-path ancestor exactly in both the index and the cached
index-to-`HEAD` diff,
excluding ordinary descendants and disabling submodule ignoring. Protected
inputs below a tracked, removed, or replaced gitlink, symlink, sparse-directory,
or other non-directory index entry that would hide the requested child from Git
are rejected. A no-follow filesystem metadata walk also rejects a protected
leaf hidden inside an untracked embedded repository, which the parent Git
untracked query can otherwise collapse; it reads no protected file body.
Unrelated repository files do not block the run.

Ordinary current-module artifact and normalized manifest/lock refresh changes
become seeds. A deleted module, routing rename, package identity or policy
change, external-import change, or unattributable metadata change escalates
monotonically to the ordinary full verifier. Missing or historically invalid
base package metadata also escalates to full. Git/object/blob protocol failures
fail closed as `git_base_selection_failed`; dirty protected inputs use
`base_selection_dirty_inputs`, and a range with neither seeds nor an escalation
uses `base_selection_empty` instead of reporting a no-op success.

Both new partial selectors reject the external checker and non-off audit-cache
or verifier-memo modes. Module selection accepts checked or reconstructed lock
input; base selection requires `--package-lock checked`. Base selection is one
committed-range acceptance component, not a complete PR gate: a source-only
change can select a module while its old certificate remains independently
valid, so the matching canonical build/hash gate must still run at the same
head/base boundary.

The two new modes attach `npa.package.verify-selection.v0.1` under
`verify_selection`. It records bounded seeds and escalation details, complete
list identities, resolved Git IDs when applicable, changed-path and closure
counts, and the targeted/full-escalated outcome. Its `trusted` and
`proof_evidence` fields are always false. The checker result retains its normal
evidence classification for exactly the certificates it actually reports.
Legacy full and changed results do not gain this object.
Generated-artifact release manifests continue to require an unselected full
verification command and deliberately reject command results that contain
`verify_selection`; selector results are PR-boundary review evidence only.

## Changed-selection Git batching

`package verify-certs --changed` and `package build-certs --changed` query only
their already validated candidate paths. Each path is passed directly to
`/usr/bin/git` as an atomic `:(top,literal)<worktree-relative-path>` include and
glob-escaped descendant exclusion after `--`; candidate depths are isolated so
overlapping ancestor and descendant candidates remain independently exact. Git
output must then match the exact candidate map before it can enter selection.
The selector does not query a package prefix, follow candidate symlinks, enable
rename detection, invoke a shell, or use `git status`.

On supported Unix systems, `ExecBudget` batching charges each pathspec's bytes,
terminating NUL, and argv pointer against the smaller of 64 KiB and conservative
exec headroom. Headroom subtracts the inherited environment, fixed Git argv,
and a 32-KiB safety reserve from `_SC_ARG_MAX`. A batch has at most 1,024
pathspec arguments, or 512 atomic exact-path include/exclude pairs. If that
premise is unavailable, arithmetic saturates, headroom is zero, or one atomic
pair exceeds the effective target, the complete operation selects `Legacy128`
with at most 128 pathspec arguments (64 pairs) before running a tracked or
untracked query. It does not run a partially optimized prefix and then fall
back.

Every batch executes in tracked/parse/untracked/parse order. Combining paths
that the former fixed-128 implementation put in separate batches can change
which of two independent Git failures is returned; this is the sole intended
diagnostic-order change. Successful parity assumes the repository, index, and
process environment remain stable during selection. Changed selection is not a
repository snapshot.

With timings enabled, the common measurement report owns the closed
`package.selection_*` labels for policy, candidates, pathspec and batch bytes,
batch/process counts, raw Git output records, and the final changed set. The
labels contain no path, environment, argv, or stderr content. Timing-off does
not allocate the selection observation or add clocks/output.

The audited Apple Git used for this rollout rejects
`--pathspec-from-file` for both `git diff` and `git ls-files`; no runtime probe
or retry is performed. A future NUL-stdin transport requires guaranteed support
from both subcommands and the complete compatibility matrix.

### Placement, storage, and recovery

There is no ordinary CLI cache-root flag or environment variable. For a package
nested in a Git checkout, the resolver normally selects
`<checkout>/target/npa-package-audit-cache`. If the package is the checkout root,
or no safe checkout anchor exists, it selects the same
`target/npa-package-audit-cache` suffix below the package's parent so the cache
remains outside the package root. It rejects overlap with package artifacts and
Git metadata and refuses symlink or non-directory traversal. Programmatic tests
and benchmark children alone may inject a complete base with
`with_build_check_cache_root(PathBuf)`; the same safety checks still apply.

Below the safe base, a fixed package/policy namespace isolates two versioned
stores:

```text
packages/<namespace>/build-check-v0.2
packages/<namespace>/targeted-authoring-support-v0.1
```

The first contains replaceable diagnostic result summaries. Support-context
entries in the second use immutable no-replace publication: a colliding writer
must validate identical canonical bytes and never overwrite differing or
malformed content. The historical unnamespaced
`<base>/build-check-v0.2` layout remains an exported compatibility locator but
is inert; current commands do not scan, migrate, or remove it.

Failure to place, validate, open, or identify a requested store emits at most
one bounded `build_check_cache_unavailable` diagnostic for the affected stores,
then continues with live work and no later cache I/O for those stores. Missing,
stale, unsupported-schema, malformed, and over-limit entries degrade to misses;
the live result determines the command verdict. Commands never prune either
store. Recovery never requires a package rollback: ignore the cache, or
manually remove the external cache base and rerun with
`--build-check-cache off`.

### Proof-authoring and completion boundary

An optional tight loop can warm and then consume eligible support entries:

```sh
npa package build-certs --root . --check --module Proofs.Example \
  --build-check-cache read-through --json
npa package build-certs --root . --check --module Proofs.Example \
  --build-check-cache local-hit --json
```

Treat both results as feedback. Before completion, refresh canonical artifacts
through the ordinary write path, run a full cache-disabled canonical build
check where the package gate requires it, and verify the checked-in `.npcert`
bytes source-free with cache and memo off:

```sh
npa package build-certs --root . --update-manifest-hashes \
  --build-check-cache off --json
npa package build-certs --root . --check --build-check-cache off --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
```

Canonical certificate bytes are proof evidence only after ordinary source-free
checking. Policy-required reference or external verification remains mandatory;
cache hits, command results, and authoring diagnostics cannot satisfy it.
Completion and release workflows keep every local acceleration off.

## Caller-owned package-verifier process memo

`npa-api 0.4.0` has no implicit process-global package-verification memo. An
embedding process that performs repeated verification over the same exact
inputs may opt in by creating one bounded handle and passing clones of that
same handle to successive API calls:

```rust
use std::num::{NonZeroU64, NonZeroUsize};

use npa_api::{
    verify_package_fast_source_free_with_options,
    PackageVerificationDecodeCacheMode, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PackageVerificationProcessMemoHandle,
    PackageVerificationProcessMemoLimits, PerformanceMeasurementMode,
};

let memo = PackageVerificationProcessMemoHandle::new(
    PackageVerificationProcessMemoLimits {
        max_entries: NonZeroUsize::new(2_048).unwrap(),
        max_weighted_certificate_bytes: NonZeroU64::new(128 * 1024 * 1024).unwrap(),
    },
);

let options = |memo: &PackageVerificationProcessMemoHandle| {
    PackageVerificationExecutionOptions {
        jobs: 4,
        selected_modules: None,
        memoization: PackageVerificationMemoMode::ProcessLocal(memo.clone()),
        decode_cache: PackageVerificationDecodeCacheMode::Disabled,
        collect_decode_cache_counters: false,
        measurement_mode: PerformanceMeasurementMode::Off,
    }
};

// `validated_manifest`, `package_lock`, and each fresh artifact iterator are
// the ordinary exact source-free inputs supplied by the embedding application.
let first = verify_package_fast_source_free_with_options(
    &validated_manifest,
    &package_lock,
    first_artifacts,
    options(&memo),
)?;
let second = verify_package_fast_source_free_with_options(
    &validated_manifest,
    &package_lock,
    second_artifacts,
    options(&memo),
)?;

let stats = memo.stats()?;
assert!(stats.retained_entries <= memo.limits().max_entries.get());
memo.clear()?;
assert_eq!(memo.stats()?.retained_entries, 0);
```

Clones share one bounded store; separately constructed handles are isolated.
Both the entry limit and aggregate checked-certificate-byte limit are mandatory
and nonzero. `stats()` and `clear()` are fallible management operations because
a poisoned store is inaccessible. Verifier execution treats that condition as
an acceleration failure: it disables memo access for the rest of the run and
continues with authoritative live checking.

The CLI never constructs this handle. `verify-certs --verifier-memo off` uses
`PackageVerificationMemoMode::Disabled`; the `read-through` and `disk` CLI
policies retain their disk-specific behavior, while every live verifier miss
also runs with the API process memo disabled. Process-memo hits are local
acceleration only. They are not persistent proof evidence and cannot replace
cache-disabled source-free verification.

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

An explicit targeted local-only request uses the same additive builder:

```rust
use npa_cert::Name;
use npa_cli::args::PackageBuildCheckCacheMode;
use npa_cli::package_api::v1::{build_certs_check, common_options};

let options = build_certs_check(common_options("proofs", true))
    .with_modules(vec![Name::from_dotted("Proofs.Example")])
    .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit);
assert_eq!(options.build_check_cache.as_str(), "local-hit");
```

Certificate verification has additive constructors for the two new selectors:

```rust
use npa_cert::Name;
use npa_cli::args::PackageChecker;
use npa_cli::package_api::v1::{
    common_options, verify_certs_base, verify_certs_modules,
};

let modules = verify_certs_modules(
    common_options("proofs", true),
    PackageChecker::Reference,
    vec![Name::from_dotted("Proofs.Example")],
);
let committed = verify_certs_base(
    common_options("proofs", true),
    PackageChecker::Reference,
    "origin/main",
);
```

`PackageVerifyCertsOptions::with_modules` and `with_base` replace the current
selector and clear the other selector fields. Existing full and changed
constructors retain their behavior. Shared validation still rejects raw
conflicting states, duplicate or empty module selection, and incompatible
checker/cache/lock combinations before package I/O.

Source-structure checks have separate constructors so programmatic callers
cannot create ambiguous selector states:

```rust
use npa_cli::package_api::v1::{
    check_source_structure_all, check_source_structure_modules,
    check_source_structure_paths, common_options,
};

let all = check_source_structure_all(common_options("proofs", true));
let modules = check_source_structure_modules(
    common_options("proofs", true),
    vec![npa_cert::Name::from_dotted("Proofs.Example")],
);
let paths = check_source_structure_paths(
    common_options("proofs", true),
    vec![npa_package::PackagePath::new("Proofs/Example/source.npa")],
);
```

Explicit module or path vectors must be nonempty and contain canonical module
names or validated package-relative paths. The runtime reports malformed
programmatic selectors as usage errors and fails closed before package I/O.
Raw `PackageCheckSourceStructureOptions` construction remains outside the
adjacent consumer contract.

The additive selectors apply to all four build constructors:

- `build_certs_check`;
- `build_certs_write`;
- `refresh_artifacts_check`; and
- `refresh_artifacts_write`.

`with_kernel_fuel_report` and `with_timings` replace only their own selection;
their call order is immaterial. Existing `with_build_check_cache`,
`with_modules`, and `with_changed` builders retain their v1 meaning. The closed
`PackageBuildCheckCacheMode::{Off, ReadThrough, LocalHit}` values are selectable
with `with_build_check_cache`; callers can query the selected public mode
through `PackageBuildCertsOptions::build_check_cache` and its stable `as_str()`
spelling. A returned `CommandResult` exposes the bounded
`targeted_authoring_cache_summary` and `targeted_authoring_cache_local_only`
diagnostics through its existing diagnostic fields; that local-only statement
is not a capability and cannot be converted into ordinary build or proof
evidence. Cache DTOs, pending orchestration state, retained directory
capabilities, and writer operations are not part of `package_api::v1`.

The programmatic-only `with_build_check_cache_root(PathBuf)` builder supplies a
complete temporary cache base for tools, tests, and performance harnesses; all
v1 constructors default it to `None`, and no ordinary CLI flag or environment
variable exposes it. The later cache-anchor resolver still validates an
injected root before use. Raw `PackageBuildCertsOptions` construction remains
outside the adjacent-consumer contract because that type is non-exhaustive.

## Command-result v0.4 source and fuel diagnostics

All package command writers now emit v0.4, including commands that cannot
produce a fuel report. V0.4 adds optional `delimiter` and `kernel_fuel`
siblings to a command diagnostic; it does not mutate the strict historical
`source` or `conversion` objects. `delimiter` is present only for typed Human
Surface delimiter failures. `kernel_fuel` is absent in fuel mode `off`, for
non-fast checkers, and for errors unrelated to fast-kernel WHNF or conversion
exhaustion.

Rust consumers read validated delimiter context through
`CommandDiagnostic::delimiter()`. The backing field is private, so construction
cannot bypass the coherence checks performed by `with_delimiter`.

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

## Common performance measurement v0.8

The outer `npa.package.timings.v0.2` object is unchanged. Its nested common
measurement is now strictly `npa.performance.measurements.v0.8`; exact v0.1
through v0.7 inputs remain historical read-only compatibility and are validated
against their original closed label vocabularies and nested package-sharding
shapes. A newer label or memory-model shape is never accepted by relabeling it
as an older schema.

V0.1 is the original closed label/report shape and has no package-sharding
fields. V0.2 adds only `package.avoided_base_context_clone_bytes` to that label
table and introduces the v1-only package-sharding shape. V0.3 keeps the exact
v0.2 label table and v1 sharding shape, but advances declaration detail to the
current nullable `kernel` field. Consequently v0.2 and v0.3 have equal label
vocabularies even though their declaration-detail shapes are distinct.

V0.4 retains the v0.3 meanings and units of `cache.context_hits`,
`cache.context_misses`, `cache.live_prerequisite_checks`,
`cache.avoided_kernel_checks`, `cache.reconstruction_elapsed`, and
`cache.fresh_target_elapsed`. It adds these targeted-authoring observations:

- count: `cache.support_selected`, `cache.targets_forced_live`,
  `cache.context_ineligible`, `cache.context_bypassed_hits`,
  `cache.context_stale`, `cache.context_schema_misses`,
  `cache.avoided_source_interface_resolutions`, and
  `cache.target_fresh_builds`;
- bytes: `cache.tool_identity_bytes`, `cache.bytes_loaded`, and
  `cache.bytes_written`; and
- nanoseconds: `cache.tool_identity_elapsed`,
  `cache.current_byte_validation_elapsed`, `cache.live_support_elapsed`, and
  `cache.source_interface_resolution_elapsed`.

The declaration shape introduced in v0.3 remains current through v0.8. A v0.4
or newer label is never accepted in a relabeled historical block, and FastLoop
status projection emits only counters that the status can represent. The
existing coarse
`cache_lookup_ms` timing accumulates result-entry and support-entry lookup
intervals; there is no common `cache.lookup_elapsed` label.

V0.5 retains the complete v0.4 table and introduces the 15 changed-selection
labels. They are the two policy counts
`package.selection_exec_budget_policy` and
`package.selection_legacy128_policy`, plus
`package.selection_candidate_paths`, `package.selection_pathspec_payload_bytes`,
`package.selection_effective_argv_charge_bytes`,
`package.selection_max_batch_payload_bytes`,
`package.selection_max_batch_argv_charge_bytes`,
`package.selection_pathspec_batches`,
`package.selection_worktree_root_queries`, `package.selection_head_queries`,
`package.selection_tracked_queries`, `package.selection_untracked_queries`,
`package.selection_tracked_output_paths`,
`package.selection_untracked_output_paths`, and
`package.selection_changed_paths`. Units are count except for the four labels
whose identifiers end in `_bytes`.

V0.6 retains that table and introduces the 11 certificate term-materialization
labels: `certificate.term_root_requests`,
`certificate.term_unique_nodes_materialized`,
`certificate.term_selected_edges`, `certificate.term_reused_child_arcs`,
`certificate.term_owned_root_handoffs`, `certificate.term_leaf_root_clones`,
`certificate.term_compound_root_clones`,
`certificate.term_materialization_slots`,
`certificate.term_materialization_charged_bytes`,
`certificate.term_materialization_capacity_stops`, and
`certificate.term_materialization_legacy_fallbacks`. Only
`certificate.term_materialization_charged_bytes` has byte units. V0.6 also
adds `prepared_shared_bytes`, `combined_shared_bytes`, and
`term_materialization_bytes_per_worker` to each package-layer and
package-sharding summary. Under `npa.fast-shard-memory.v1` they must be
`(0, shared_base_context_bytes, 0)`; under
`npa.fast-shard-memory.v2-term-materialization` they must be
`(0, shared_base_context_bytes, 268435456)`.

V0.7 retains the complete v0.6 label and nested-shape history. It introduces
11 shared-payload ownership labels:
`package.module_payloads_frozen`, `package.module_payload_unique_bytes`,
`package.module_payload_handle_clones`,
`package.avoided_module_payload_clone_bytes`,
`package.session_snapshot_clones`, `package.session_index_cow_copies`,
`package.session_index_cow_entries`, `package.decode_cache_retained_bytes`,
`package.decode_cache_peak_retained_bytes`,
`package.decode_cache_capacity_stops`, and
`package.process_memo_payload_handle_clones`. It also introduces 19 snapshot
and prepared-retention labels: `package.artifact_files_read`,
`package.artifact_file_hashes`, `package.artifact_full_decodes`,
`package.artifact_prepared_reuses`, `package.prepared_artifact_admissions`,
`package.prepared_artifact_admitted_bytes`,
`package.prepared_artifact_current_entries`,
`package.prepared_artifact_peak_entries`,
`package.prepared_artifact_current_bytes`,
`package.prepared_artifact_peak_bytes`,
`package.prepared_artifact_derivation_current_bytes`,
`package.prepared_artifact_derivation_peak_bytes`,
`package.prepared_artifact_key_current_bytes`,
`package.prepared_artifact_key_peak_bytes`,
`package.prepared_artifact_entry_limit_fallbacks`,
`package.prepared_artifact_byte_limit_fallbacks`,
`package.prepared_artifact_saturated_charge_fallbacks`,
`package.prepared_artifact_releases`, and
`package.prepared_artifact_released_bytes`. Their units are fixed by the
`_bytes` suffix; the remaining labels are counts.

The v0.7-compatible
`npa.fast-shard-memory.v3-term-materialization-prepared-retention` model keeps
the exact 268,435,456-byte per-worker term reservation and admits nonzero
`prepared_shared_bytes`. Its `combined_shared_bytes` is the checked or
saturated sum of `shared_base_context_bytes` and `prepared_shared_bytes`; a
saturated addition must set `estimate_overflowed`. V0.7 readers continue to
accept v1 and v2 only with their exact zero-prepared tuples above. Adding the
v2 and v3 variants to the exhaustive public
`PerformancePackageShardMemoryModel` enum is an intentional `npa-api`
compatibility change; consumers must handle all three published variants.

V0.8 retains the complete v0.7 label table and nested report shape and adds 17
committed-base selection labels. Count labels record base-commit, committed
`HEAD`, and merge-base queries; protected candidates and dirty inputs;
committed-diff batches, processes, and raw output paths; seed modules; full
escalations; selected closure modules; and four big-endian u64 words containing
the complete SHA-256 escalation-reason identity. The two byte labels are
`package.selection_base_manifest_blob_bytes` and
`package.selection_base_lock_blob_bytes`. The remaining exact identifiers are
`package.selection_base_commit_queries`,
`package.selection_committed_head_queries`,
`package.selection_merge_base_queries`,
`package.selection_protected_candidate_paths`,
`package.selection_dirty_paths`, `package.selection_committed_diff_batches`,
`package.selection_committed_diff_processes`,
`package.selection_committed_diff_output_paths`,
`package.selection_seed_modules`, `package.selection_full_escalations`,
`package.selection_full_escalation_reason_identity_word_0` through
`package.selection_full_escalation_reason_identity_word_3`, and
`package.selection_closure_modules`. These counters are projected only for a
timing-enabled committed-base operation. Timing-off performs no clock read or
selection-observation allocation, and all measurement fields remain untrusted
and outside proof, package-lock, cache, and selection identities.

Committed-base clean-head validation reuses the v0.5
`package.selection_tracked_queries` counter for protected index/worktree
diffs, raw `git hash-object --no-filters`, protected index-state
`git ls-files -s -v`, and strict protected-ancestor index/cached-HEAD processes.
The ancestor processes, raw hashes, and index-state `ls-files` do not
contribute to `package.selection_tracked_output_paths`, which remains the raw
path-record count emitted by the protected-path diffs.

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

The external invocation is presently a fail-closed contract probe. It returns
`external_checker_supervisor_unavailable` before creating import/result state.
Execution remains disabled until the host can own the whole descendant tree,
enforce memory and timeout, and obtain an authenticated checker step count;
zero-valued unavailable measurements are not release evidence.

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

## Bounded theorem-premise report storage

`package theorem-premise-report` preserves the logical
`npa.package.theorem_premise_report.v0.1` report, its canonical UTF-8 bytes,
analysis limits, self hash, and complete theorem coverage. Reports of at most
128 MiB retain the original single-file representation at
`generated/theorem-premise-report.json`, byte for byte.

For larger reports, that path contains a canonical storage index with schema
`npa.package.theorem_premise_report_chunks.v0.1`. The index records the whole
logical report's file hash and byte length, followed by an ordered `chunks`
array of `file_hash` / `bytes` pairs. Chunk paths are derived exclusively from
validated lowercase SHA-256 hashes:
`generated/theorem-premise-report-chunks/<64-hex-file-hash>.part`. These are raw
byte fragments of the canonical report; an individual fragment need not be a
complete JSON document or end at a UTF-8 character boundary.

The writer uses 16 MiB chunks, at most 32 chunks (512 MiB total), and an index
of at most 16 KiB. The reader enforces those per-chunk, count, aggregate, and
index bounds, with bounded index JSON parsing, exact byte totals, every chunk
hash, and the reconstructed whole-report file hash. It also accepts smaller
nonempty chunks within the same bounds. Arbitrary path fields, duplicate or
unknown index fields, noncanonical indexes, missing or changed chunks, and
symlinked directories or files are rejected. The existing shared **128 MiB
per-regular-file read/write guard is unchanged**; no oversized regular file is
written or accepted through that guard.

All chunks are synced, immutable, content-addressed create-only artifacts.
The root index is atomically published last under the existing package
mutation lock. An interrupted write cannot replace the previously published
report with an incomplete one. Identical chunks are reused. Old unreferenced
chunks are retained so readers of an older index remain valid; automatic
garbage collection is not part of this command. Archive the index together
with its referenced chunks when moving a report. Older CLIs that know only
the inline report schema cannot consume this storage representation.

The standalone `--check`, `publish-plan` input loader, and shared six-part
`check-generated` loader use the same reconstruction path. Ordinary canonical
report validation and comparison with the current certificate-derived
projection still run on the complete logical report. Write results list the
root artifact and the distinct chunk artifacts. A package's generated-file
ignore rules should also cover the chunk directory when generated metadata is
intentionally untracked.

This is a CLI storage layer, not a proof checker, a compressed summary, a
partial projection, or a replacement report schema. Certificate bytes,
package locks, theorem and axiom semantics, kernel/checker fuel, and proof
acceptance are unchanged. Existing external-release archive limits are not
expanded by this feature.

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
