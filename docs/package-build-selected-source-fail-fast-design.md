# Package Build Selected-Source Fail-Fast Design

Status: implemented on 2026-09-03 in the current `npa-core` package CLI.
This document is retained as the design, failure-order contract, and
implementation record.

## Summary

Move selected-source failure detection ahead of the package-wide artifact work
performed by targeted `package build-certs --update-manifest-hashes`.

The change has two parts:

1. Run a context-free lexical and delimiter preflight over explicit selected
   Human Surface sources before reading any certificate. This catches malformed
   strings and mismatched `()`, `[]`, or `{}` immediately.
2. Process the smallest dependency-closed local prefix needed to compile the
   explicit selected seeds before traversing reverse-only dependents or
   snapshotting unrelated package artifacts. Support modules are live-checked,
   and priority rebuild modules use the existing qualification, rebind, or
   source-rebuild path. Successful in-memory outputs are retained as the first
   part of the ordinary canonical refresh; no module is processed twice.

The first stage catches parenthesis mistakes present in the source bytes it
scans without dependency work. The second stage catches parser, resolver,
elaborator, application-shape, kernel handoff, and selected-module axiom-policy
failures after only the forward closure needed to interpret the selected
source. Neither stage weakens the existing all-or-nothing write, manifest,
metadata, package-lock, or source-free verification requirements.

## Motivation And Observed Failure

A targeted canonical refresh currently constructs a dependent rebuild closure,
loads every external import, and traverses all local modules in package
topological order. It sets `snapshot_unrelated = true` because the regenerated
package lock must contain the complete package artifact set. The selected
source is read and passed to the Human frontend only when the global traversal
eventually reaches that module.

Concretely, `build_package_certificates_targeted_refresh` calls
`build_targeted_refresh_inputs` with `snapshot_unrelated = true`,
`refresh_metadata = true`, `interface_aware = true`, and
`selected_external = None`. The last value makes `load_external_imports` read
and verify every declared external import before the local loop starts.

This makes a local authoring error appear to be expensive:

- an unmatched parenthesis is independent of every imported theorem;
- a malformed application needs the selected module's direct semantic import
  context, but not unrelated modules or reverse dependents;
- nevertheless, both failures can currently be reported only after substantial
  certificate traversal.

The concrete 2026-08-31 observation was an eight-module IUT refresh that took
914,549 ms before reporting a Human Surface parser error. After repairing the
source, a targeted no-write check of the quotient module took 4,883 ms. The
latency difference is consistent with the command ordering, not with slow
parser error construction.

The existing
`package_build_certs_frontend_failure_check_dependent_reports_source_context_without_writes`
test establishes the frontend diagnostic and no-write behavior, but does not
assert which certificate reads occurred before that failure. The counter-based
tests below close that ordering gap.

There is a separate selection problem: `--changed` promotes the selection to
all local modules when `npa-package.toml` changed. This design records the
promotion reason in the selection plan and still runs the cheap structural
scan first, but it does not narrow or reinterpret that selection.

## Terminology

This design keeps three different closures explicit.

| Term | Direction | Purpose |
| --- | --- | --- |
| selected seeds | none | Local modules named by repeated `--module`, selected from changed paths, or promoted by current selection rules. |
| forward support closure | imports of seeds | Modules and external imports needed to parse, resolve, elaborate, build, and verify the selected source. |
| reverse dependent closure | importers of seeds | Local modules whose certificate identity may need rebuilding or rebinding after a selected module changes. |
| package artifact closure | whole package | Every certificate artifact required to regenerate a complete package lock. |

Only the forward support closure is intrinsically required before an
application-shape error in a selected module can be diagnosed. No certificate
is required to detect a lexical or delimiter error.

In this document, “before any certificate read” means before `npa-cli` opens a
package certificate through its artifact/dependency-discovery readers or sends
certificate bytes to a decoder or verifier. The existing `--changed` Git
selection query remains in Phase 0 and may inspect working-tree paths according
to Git's own change-detection semantics; this design does not alter that
subprocess boundary.

The lexical and delimiter failure-order guarantee applies to the source bytes
actually read by Phase 1. Phase 1 and the canonical build intentionally use
separate reads, so a source mutation after a successful scan can be diagnosed
later by the ordinary canonical frontend. The concurrency section defines that
case explicitly; no successful preflight result validates bytes read later.

The term **priority closure** below means the smallest local dependency-closed
set that must be processed to freshly build the selected seeds. It can include
a non-seed rebuild module when that module lies on an import path between two
selected seeds; that non-seed continues to use the current dependent-refresh
qualification, rebind, and fallback rules.

The term **reverse-only dependent** means a member of the reverse dependent
closure that is not also in the priority closure. These are exactly the
completion-rebuild modules defined below; a bridge needed by another selected
seed is not reverse-only.

## Goals

- Report selected-source lexical and delimiter errors observed by structural
  preflight before any certificate read, decode, or verification.
- Report selected-source parser, resolver, elaborator, application-shape,
  kernel-handoff, and axiom-policy failures after only the priority closure.
- Never compile a successfully front-loaded module twice in one command.
- Preserve byte-for-byte canonical certificates, refreshed manifest fields,
  metadata ledgers, and package-lock JSON for successful commands.
- Preserve the complete package artifact snapshot and all existing validation
  before check-mode success or write-mode publication.
- Preserve no-follow reads, resource bounds, deterministic ordering, and the
  all-or-nothing write transaction.
- Keep canonical refresh cache-off. No advisory authoring-cache entry may
  satisfy the priority closure.
- Make the planned early and deferred work visible in structured diagnostics
  and optional timing output.
- Share one implementation between refresh check mode and refresh write mode.

## Non-Goals

- Do not change which modules `--module` or `--changed` selects.
- Do not change the current manifest-change promotion to a full selection.
- Do not omit unrelated artifacts from the regenerated package lock.
- Do not turn frontend success, timing data, or a command diagnostic into proof
  evidence.
- Do not add parallel module compilation in this change.
- Do not add a persistent cache for canonical refresh work.
- Do not change certificate encoding, hash domains, axiom policy, kernel fuel,
  or source-free verification.
- Do not stream partial JSON command results. The command still emits one
  complete `CommandResult` after it stops or succeeds.
- The first rollout did not add a standalone `package check-syntax` command.
  The context-free validator was made public in `npa-frontend` so a later
  command could reuse the lexer. That follow-up is now implemented as the
  narrower `package check-source-structure` authoring command; it does not
  change this canonical-refresh design or turn structural success into proof
  evidence.

## Current Ordering

For targeted refresh, the current effective order is:

```text
load and validate package root
select seeds
expand reverse dependent rebuild closure
load and verify every external import
walk every local module in global dependency-topological order
  selected support: validate source and certificate, reconstruct interface
  selected rebuild: read source and invoke Human frontend
  unrelated module: decode and verify certificate for the lock snapshot
regenerate manifest and package lock
compare or publish artifacts
```

`build_package_certificates_targeted_refresh` currently requests all external
imports and `snapshot_unrelated = true`. `build_local_modules_for_refresh`
therefore reaches the selected frontend call only after all earlier entries in
the global topological order have been processed.

The command stops immediately after that frontend call returns an error, but
rendering happens only after the `CommandResult` is returned. Streaming would
not fix the work performed before the frontend call.

## Proposed Ordering

Targeted refresh will use the following phases:

| Phase | Work | Earliest failures |
| --- | --- | --- |
| 0. Load, validate, and select | Existing package-root, graph, selection, and refresh-target safety validation; construct and validate the certificate-free local plan. | Manifest, graph, path, selection, target-safety, and internal local-plan failures. |
| 1. Structural source preflight | Read explicit selected source files one at a time; run the existing Human lexer plus delimiter validation; discard bytes after each scan. | UTF-8/read limits, malformed strings/tokens, extra, missing, or mismatched delimiters. |
| 2. Priority closure | Load exact external support; live-check local support; process priority rebuild modules in dependency-topological order through the existing refresh path; only after every priority module succeeds, finalize their metadata. | Exact parser, notation, resolver, application-shape, elaborator, kernel-handoff, axiom-policy, selected dependency, or priority-metadata failures. |
| 3. Completion traversal | Load remaining external imports; process remaining support and reverse dependents, including their ordinary per-module metadata refresh; snapshot unrelated local certificates. | Deferred rebuild/metadata, unrelated certificate, and complete-closure failures. |
| 4. Refresh assembly | Refresh manifest fields and construct the complete package lock from all retained artifacts. | Manifest rewrite and lock failures. |
| 5. Compare or publish | Existing check comparison or atomic write transaction. | Staleness, target replacement, staging, and publication failures. |

Phases 2 and 3 are two parts of one canonical build. Phase 2 is front-loaded
canonical work, not an advisory check: its successful outputs have the same
authority as the corresponding work performed in the current global traversal.

### Mode Matrix

| Build mode | Structural preflight | Priority closure scheduling |
| --- | --- | --- |
| `--update-manifest-hashes --module ...` | explicit selected seed sources | yes |
| `--update-manifest-hashes --check --module ...` | explicit selected seed sources | yes |
| `--update-manifest-hashes --changed` | selected seed sources after current promotion rules | yes when at least one local seed is selected |
| `--update-manifest-hashes --check --changed` | selected seed sources after current promotion rules | yes when at least one local seed is selected |
| full `--update-manifest-hashes` | every local source in topological order | no special reorder; the structural scan still precedes certificates |
| targeted non-refresh `--check` | unchanged in the first rollout | existing exact selected-closure path already supplies the relevant fast feedback |
| full non-refresh build/check | unchanged in the first rollout | none |

The canonical targeted-refresh branch constructs the plan whenever its local
seed set is nonempty or `--changed` selected the package lock. If its computed
priority closure is the complete local module set, the priority order is the
ordinary global topological order and the local completion order is empty;
there is no local reordering benefit. External imports not referenced by any
local module can still remain completion work. In particular, this local-order
degeneration is the result when `--changed` promotes the seed set to every
module. The structural scan still catches context-free mistakes before
certificate work. A later selection preview or narrower changed-selection
design remains separate.

When `--changed` selects no local seed, Phase 1 and the local part of Phase 2
are empty. Preserve the current branch behavior: if the package lock was not
selected, the existing external-selection validation/no-op return remains; if
the package lock was selected, all external loading and local artifact
snapshotting belongs to completion traversal before the lock is compared or
rewritten.

## Structural Source Preflight

### Frontend API

Add a public API owned by `npa-frontend`:

```rust
pub fn validate_human_source_lexical_structure(
    file_id: FileId,
    source: &str,
) -> HumanResult<()>;
```

It must use the existing `lex_human` implementation. It must not implement a
second character scanner in `npa-cli`.

After lexing, it validates properly nested pairs for `()`, `[]`, and `{}`.
Comments and string contents are already excluded by the lexer, so delimiter
characters in either do not affect the stack. The stack is bounded by the
number of lexer tokens. The package CLI's existing 128 MiB regular-file reader
bounds the source supplied by this command; the frontend API introduces no
separate token-count limit.

The API returns success only for lexical structure. It does not claim that the
module parses, resolves, elaborates, or type-checks. In particular, it does not
interpret imported notation.

Lexer failures retain their existing `HumanDiagnosticKind`, message, and span,
and receive `HumanDiagnosticPhase::Parser` only when no phase is already set.
Delimiter-stack failures use `HumanDiagnosticKind::ParseError` and
`HumanDiagnosticPhase::Parser`, with:

- the exact closing-delimiter span and `unexpected closing delimiter '<close>'`
  when the stack is empty;
- the exact closing-delimiter span and
  `mismatched closing delimiter '<close>'; '<open>' at byte <offset> expects
  '<expected>'` when the closer does not match the stack top; or
- an EOF primary span and
  `unclosed delimiter '<open>' at byte <offset>; expected '<expected>' before
  end of input` for the innermost unmatched opening delimiter.

The displayed delimiters are quoted token spellings. Messages and offsets are
derived from the lexer token and `Span`, not by rescanning source characters.

The CLI maps the diagnostic through the common base of the existing
`frontend_build_failed` path, retaining module, manifest field,
package-relative source path, byte range, line, column, and token where
applicable. Phase 1 must disable the optional
`frontend_containing_declaration` lookup: reparsing the malformed source would
duplicate work and could require imported notation interfaces. Structural
preflight diagnostics therefore omit only the optional declaration name;
ordinary Phase 2 frontend diagnostics retain the current declaration lookup.

### Read Set And Ordering

The CLI scans only explicit selected seeds in dependency-topological order,
deduplicated by module index. A non-seed bridge or support source is left to the
ordinary priority-closure path because scanning it here would delay semantic
feedback from the selected source without improving the selected-source
guarantee. Full refresh has every module as a seed and scans all local modules
in dependency-topological order.

Each source is opened through the existing no-follow bounded `read_source`
path. The source is dropped after validation. The later canonical build reads
it again: targeted refresh does so in Phase 2, while full refresh does so in
its ordinary full-build completion path. This deliberate duplicate read keeps
Phase 1 memory bounded and ensures Phase 1 success is never used to skip the
real parser.

A Phase 1 failure changes failure precedence: the selected seed failure is
reported before an invalid support, bridge, or unrelated certificate that the
old traversal happened to encounter first. That change is intentional. If
Phase 1 succeeds, every existing certificate and artifact check still runs
before command success or publication.

## Priority Closure Planning

Let:

```text
S = selected local seed indices
R = current reverse dependent rebuild closure of S
D = transitive local dependencies of S
P = S union D
PR = P intersect R
PS = P minus PR
Q = transitive local dependencies of R, minus R
U = every local module index
CR = R minus PR
CS = Q minus PS
CU = U minus (R union Q)
```

`PR` contains modules that must pass through the canonical rebuild role during
the priority phase. An explicit seed is source-built; a non-seed retains the
current interface-aware unchanged/rebind qualification and source-rebuild
fallback. `PS` contains checked support modules whose current certificate and
source interface are sufficient. Because `S` is contained in `R`, every member
of `P` outside `R` is also in `Q`; equivalently, `PS = P intersect Q`.

The completion roles are therefore defined, rather than inferred during
execution: `CR` is `completion_rebuild`, `CS` is `completion_support`, and
`CU` is `completion_snapshot`. The current selection plan's `rebuild` and
`support_local` sets are exactly `R` and `Q`. These equations make the five
priority/completion roles a disjoint cover of `U` and keep unrelated snapshots
outside both semantic closures.

The intersection is important for multi-seed requests. For example:

```text
A (selected) -> B (not explicitly selected) -> C (selected)
```

where arrows point from a changed producer to a dependent. `B` belongs to both
the reverse closure of `A` and the forward dependency closure of `C`; loading
its old certificate as ordinary support would be incorrect. `B` therefore
belongs to `PR` and is qualified, rebound, or rebuilt before `C`.

The priority local order is the existing package topological order filtered to
`P`. The completion local order is the same topological order filtered to
`U minus P`. Concatenating the two orders is not globally topological, but
every processed module still follows all modules it imports:

- every priority node's imports are in `P` and precede it in the filtered
  priority order;
- a deferred node may import a priority node, which is already available;
- a deferred node's deferred imports precede it in the filtered completion
  order;
- a completion snapshot still follows its certificate imports even though it
  does not read or compile source; its existing verified/fallback import state
  may remain available for a later snapshot consumer.

The planner must also validate that the structural seed order is exactly `S`
filtered from package topological order and that the priority rebuild, priority
support, completion rebuild, completion support, and unrelated-snapshot roles
form a disjoint cover of all local modules. It fails with an internal structured
diagnostic if any node is duplicated, omitted, out of range, or scheduled
before a required import. Use reason code `targeted_refresh_plan_invalid` and a
bounded `actual_value` such as `duplicate_local`, `missing_local`,
or `local_dependency_after_consumer`; do not panic or render an unbounded node
list.

### External Priority Closure

Collect direct external imports referenced by every module in `P` as the
priority external roots. This is manifest-graph work and belongs in Phase 0.
An external certificate selected by `--changed` but not referenced by `P`
remains completion work; it is still verified before command success but does
not delay an independent selected-source frontend diagnostic.

The existing `external_import_dependency_plan` discovers transitive imports by
reading and decoding external certificate bytes. It must therefore run only
after structural source preflight succeeds. Refactor its refresh-mode callback
to retain each bounded byte buffer that it reads and return both the exact
transitive order and the retained buffers. The subsequent priority loader
verifies those same bytes instead of reopening the files. Untrusted dependency
discovery cannot make a certificate available; only ordinary verification can
do that. This preserves the existing import-count, dependency-edge,
certificate-byte, cycle, and index bounds while avoiding a second read.

Validate that the priority external order is dependency-closed and contains
every root, that the completion order is the manifest-order complement, and
that the two orders are disjoint and cover every external import exactly once.
External-plan invariant failures use `targeted_refresh_plan_invalid` with a
bounded `actual_value` such as `external_root_missing`,
`external_dependency_after_consumer`, or `external_partition_invalid`.

After the entire priority phase succeeds, load the remaining external imports
in the existing validated full order. Already loaded imports are skipped by
index, but their bytes and verified modules remain part of the same operation
state. Within this canonical two-phase targeted-refresh branch, every declared
external-import index is opened, read, and verified at most once. The
no-local-seed/no-lock validation branch is outside this two-phase state and
retains its current behavior in the first rollout.

## Runtime Data Model

Introduce a certificate-free local plan separate from the user-facing
selection plan:

```rust
struct TargetedRefreshLocalPlan {
    structural_seed_order: Vec<usize>,
    priority_local_order: Vec<usize>,
    priority_rebuild: BTreeSet<usize>,
    priority_support: BTreeSet<usize>,
    priority_external_roots: BTreeSet<usize>,
    completion_local_order: Vec<usize>,
    completion_rebuild: BTreeSet<usize>,
    completion_support: BTreeSet<usize>,
    completion_snapshot: BTreeSet<usize>,
}

struct TargetedRefreshExternalPlan {
    priority_external_order: Vec<usize>,
    completion_external_order: Vec<usize>,
}
```

Extend the existing selection plan with a bounded promotion reason:

```rust
enum PackageBuildSelectionPromotion {
    None,
    ManifestChanged,
}
```

This records the current `--changed` behavior; it does not alter the selected
set. It prevents `mode=changed,seeds=<all modules>` from being the only clue
that a package-wide promotion occurred.

Introduce operation-scoped state so both phases use the same accepted values:

```rust
struct TargetedRefreshExecutionState {
    external_verifier_session: VerifierSession,
    discovered_external_bytes_by_index: BTreeMap<usize, Vec<u8>>,
    loaded_external: BTreeSet<usize>,
    processed_local: BTreeSet<usize>,
    available_modules: BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts_by_path: BTreeMap<PackagePath, CertificateArtifactBuffer>,
    pending_priority_metadata_by_index: BTreeMap<usize, PendingPriorityMetadata>,
    refreshed_modules_by_index: BTreeMap<usize, LocalModuleRefreshIdentity>,
    stats: TargetedRefreshStats,
}

struct PendingPriorityMetadata {
    identity: LocalModuleRefreshIdentity,
    verified: Arc<VerifiedModule>,
    source_interface: HumanSourceInterface,
}
```

The exact field layout may follow ownership constraints in the implementation,
but it must preserve these invariants:

- both external-loading phases share one operation-scoped verifier session;
- each declared external-import index is opened, read, and verified at most
  once in the two-phase targeted-refresh branch;
- dependency discovery bytes remain untrusted and unavailable to import
  consumers until ordinary verification succeeds;
- the discovery-byte map is empty after priority external loading, and the
  loaded-external set covers every manifest import after completion;
- a local module is processed at most once;
- a refreshed module is compiled, rebound, or reused exactly once;
- every priority module with declared metadata retains the verified module and
  source interface needed for bounded deferred metadata derivation;
- an artifact path has one byte identity or fails as a duplicate;
- final vectors are materialized in manifest or package topological order, not
  execution-phase order;
- no cache-derived context enters this state.

`PendingPriorityMetadata` retains one additional source-interface clone only
for a priority rebuild module that declares `meta`. The existing imported
interface ownership continues to feed downstream compilation. The pending copy
is bounded by `priority_rebuild`, is released before completion traversal, and
has `identity.metadata_path` and `identity.metadata_bytes` set exactly once at
the priority-finalization boundary. Priority modules without `meta` can enter
`refreshed_modules_by_index` immediately.

The current `refreshed_module_metadata` helper accepts `&ModuleCert`, although
its only certificate-owned input is the already recorded axiom-report hash.
Refactor that parameter to accept `identity.axiom_report_hash` (or an
equivalent compact metadata input). Priority finalization must not retain a
second decoded certificate or decode `identity.certificate_bytes` again merely
to render metadata.

The existing global import-use counts may otherwise be retained for the first
implementation. They can over-retain an `Arc` or imported source interface when
an unrelated certificate-only snapshot does not consume it, but they must never
remove an import before its last actual semantic consumer. Any later lifetime
optimization needs separate memory measurements and tests.

## Build Algorithm

### 1. Load, Validate, And Select

Keep `load_package_root`, option validation, path safety, graph validation,
refresh-target safety validation, and the selection semantics of
`resolve_package_build_selection` unchanged. Populate the new bounded
promotion reason while resolving the existing selection.

When targeted selection enters canonical refresh because it has a local seed
or selected lock, construct and validate `TargetedRefreshLocalPlan` after the
existing selection and refresh-target safety checks. This validation uses only
the validated manifest graph and must finish before any source or certificate
read. Do not call `external_import_dependency_plan` yet. Construct the bounded
`package_build_refresh_schedule` diagnostic from this local plan. A lock-only
plan has empty structural and priority orders and assigns every local module to
`completion_snapshot`.

Full refresh does not construct the targeted role partition or schedule
diagnostic. After its existing full refresh-target safety check, use the global
topological order directly as `structural_seed_order`, run Phase 1, and then
enter the unchanged full canonical build as completion work.

### 2. Scan Selected Seed Source Structure

For each index in `structural_seed_order`:

1. derive its existing `FileId`;
2. read it with `read_source`;
3. call `validate_human_source_lexical_structure`;
4. map failure through the shared frontend diagnostic helper with declaration
   lookup disabled, so this stage never calls the parser or interprets imported
   notation;
5. drop the source before scanning the next module.

Do not check `expected_source_hash` here. Source drift is the input that refresh
mode is meant to repair.

### 3. Load Priority External Imports

Expand `priority_external_roots` only now, using the bounded external dependency
planner. Retain the exact bytes read during dependency discovery, then construct
and validate `TargetedRefreshExternalPlan`.

Refactor `load_external_imports` into an incremental helper accepting an exact
ordered index slice and mutable execution state. Load
`priority_external_order` using the retained bytes, ordinary verifier, the
state-owned verifier session, and package axiom policy. A missing retained byte
buffer for an index discovered in this phase is an internal plan/state error;
the loader must not silently reopen it.

No persistent authoring cache, result cache, or support-context cache is
consulted. Priority failure is an ordinary refresh failure.

### 4. Process Priority Local Modules

Refactor the body of `build_local_modules_for_refresh` into a single-module
operation that accepts a role:

```rust
enum RefreshModuleRole {
    CheckedSupport,
    Rebuild,
    UnrelatedSnapshot,
}
```

Walk `priority_local_order`:

- `priority_support` uses `CheckedSupport`, including current-source hash
  validation, certificate verification, parsing/resolution needed to recreate
  the source interface, and direct-import drift checks;
- `priority_rebuild` uses `Rebuild`, including the current interface-aware
  qualification, fallback rebuild, certificate encoding and verification,
  import-identity checks, and axiom-policy checks. Priority metadata derivation
  is delayed until the entire priority local order succeeds so a
  metadata-sidecar problem cannot hide a later selected frontend error.

The selected seed and any required bridge rebuild therefore pass the same
canonical frontend and certificate path they use today. Retain every successful
output in `TargetedRefreshExecutionState`. For a priority rebuild module with
declared metadata, retain the verified module and one source-interface clone in
`pending_priority_metadata_by_index`; do not read or render its metadata yet.

Only after every priority module has succeeded, iterate pending priority
metadata in `priority_local_order`, call the compact-input form of
`refreshed_module_metadata`, finalize each `LocalModuleRefreshIdentity`, and
release the pending entries. This prevents an earlier metadata-sidecar problem
from hiding a later selected frontend error without retaining those interfaces
during the package-wide completion traversal or decoding a certificate twice.
A priority-metadata failure stops before completion and stages no write.

If any priority module fails, return the existing primary diagnostic together
with the selection/plan diagnostic. Do not enter completion traversal and do
not stage a write.

### 5. Complete The Package Traversal

After all priority modules and priority metadata finalization succeed:

1. load the remaining external imports;
2. walk `completion_local_order`;
3. apply the prevalidated `completion_rebuild`, `completion_support`, and
   `completion_snapshot` role partition rather than recomputing it during
   traversal;
4. process `completion_rebuild` as `Rebuild`, `completion_support` as
   `CheckedSupport`, and `completion_snapshot` as `UnrelatedSnapshot`;
5. derive metadata for each completion-phase `Rebuild` immediately after that
   module succeeds, preserving the current per-module behavior now that no
   selected frontend work remains.

This retains the current behavior in which a missing, stale, malformed, or
policy-invalid unrelated certificate prevents canonical refresh from claiming
a complete package lock.

### 6. Assemble Canonical Outputs

Materialize refreshed modules and artifacts in the order required by their
existing canonical consumers. Then run the existing operations:

- refresh manifest hash fields;
- parse and validate the refreshed manifest;
- prove all non-hash manifest fields unchanged;
- construct and canonicalize the complete package lock;
- in check mode, compare every expected artifact without writing;
- in write mode, stage and atomically publish the existing allowed target set.

Execution order must not affect any canonical byte. Differential fixture tests
must compare every output byte with the current algorithm for valid inputs.

## Diagnostic Contract

Keep the existing primary failure reason `build_failed` for frontend errors.
The existing `field` continues to identify `parser`, `resolver`, `elaborator`,
`certificate_handoff`, or another frontend phase.

Extend the existing informational `package_build_selection` value only with the
bounded `promotion=none|manifest_changed` reason, appended after the existing
`changed_external` count so the current prefix remains stable. Add a separate
informational `DiagnosticKind::Build` diagnostic with reason code
`package_build_refresh_schedule`, field `refresh_schedule`, and the following
`actual_value`, constructed from the certificate-free local plan before
Phase 1:

```text
priority_rebuild=<n>,priority_support_local=<n>,
priority_external_roots=<n>,declared_external=<n>,deferred_rebuild=<n>,
deferred_support_local=<n>,snapshot_unrelated_local=<n>
```

`declared_external` is the manifest import count. Exact transitive priority
external membership is intentionally unavailable until after Phase 1 reads
the certificate graph; the certificate-free diagnostic reports its root count
and the bounded declared total instead of speculating.

The existing selection diagnostic's `support_external` count retains its
current meaning: direct external roots needed by the complete selected rebuild
and support closure. `priority_external_roots` is the subset needed before the
selected seeds can be built. `changed_external` remains a separate selection
count and does not become priority work unless `P` references it.

After selection and local-plan construction succeed, both diagnostics are
included in success and later failure `CommandResult` values, including a
structural-preflight failure. Selection or local-plan construction failures
retain their existing bounded diagnostics because no complete local schedule
exists to summarize. The diagnostics are untrusted planning metadata and remain
part of the final result, not an early streaming or preview channel. No source
bytes, proof terms, absolute paths, or unbounded module lists are added.

The existing `package_build_refresh_plan` diagnostic remains the completed
execution summary; the new schedule diagnostic does not replace it. A Phase 1,
priority, or completion failure returns selection, schedule, and the primary
failure, without a success-looking execution summary. Successful canonical
builds, including later comparison or publication failures, return selection,
schedule, the existing completed refresh-plan summary, and then any primary
failure in that order.

Keep the existing completed refresh-plan counters semantically stable. In
particular, its `source_scans` field continues to count canonical refresh-path
source scans and does not include the additional structural-preflight reads;
the selection seed count already bounds the latter.

Add these optional command timing fields when `--timings summary|detailed` is
selected:

```text
source_preflight_ms
priority_build_ms
completion_build_ms
```

`source_preflight_ms` covers bounded source reads plus lexical-structure
validation. `priority_build_ms` covers priority external dependency discovery,
external-plan validation and loading, priority local processing, and priority
metadata finalization. `completion_build_ms` covers the remaining external and
local traversal; for full refresh it covers the existing complete canonical
build after structural preflight. Existing projection, JSON-write,
artifact-compare, and total metrics retain their current meanings. The three
intervals do not overlap each other.

Once package loading, selection, target safety, and local planning have
succeeded and refresh phase execution begins, initialize its applicable timing
fields to zero. An early failure therefore leaves every phase that was not
entered at zero instead of making the field disappear. Targeted refresh emits
all three fields, including zero `priority_build_ms` for an empty priority
phase. Full refresh emits `source_preflight_ms` and `completion_build_ms` and
omits `priority_build_ms`. Failures before refresh phase execution retain the
existing timing shape, and non-refresh commands emit none of the three fields.
Insert the fields in stable collector order immediately after `selection_ms`
and before `cache_lookup_ms`, in the order shown above. The existing
timing-envelope schema remains unchanged because it already permits optional
`_ms` metrics.

The fields are retained in `CommandTimings` and rendered in structured JSON.
Keep the existing compact human timing line limited to its current
`total_ms`/`checker_ms` selection; users inspect these phase fields with
`--json`. Expanding the human timing renderer is not required for this change.

They are informational and must not influence the verdict. Timing mode `off`
must avoid clocks and measurement allocations, following the existing timing
collector contract.

Do not emit a success-looking `preflight_passed` diagnostic. A priority-phase
success is only intermediate state and may still be followed by an unrelated
certificate, lock, or publication failure.

## Failure Precedence

The intended deterministic precedence is:

1. option, root, manifest, graph, selection, refresh-target safety, and
   certificate-free local-plan validation;
2. selected-seed source read, UTF-8, lexical, and delimiter failures;
3. priority external dependency discovery, external-plan validation, and
   support verification failures;
4. priority local failures in `priority_local_order`, whether the current role
   is checked support or rebuild;
5. priority metadata failures;
6. remaining external and local completion failures, including completion
   rebuild metadata;
7. refreshed manifest and lock failures;
8. comparison or atomic-publication failures.

Within each group, use the relevant canonical ordered index sequence and stop
at the first failure. Do not group all priority support ahead of all priority
rebuilds: the filtered topological order may interleave the two roles, and that
order is required for available import identities.

This intentionally differs from the old incidental ordering, where an
unrelated certificate earlier in the global traversal could hide a selected
source typo for many minutes. The complete invalid package still cannot pass;
fixing the selected source exposes the next deterministic failure.

## Trust And Safety Boundary

The Human lexer, parser, resolver, elaborator, scheduling plan, and diagnostics
remain untrusted. Front-loading them does not expand the kernel trusted base.

The following conditions remain mandatory:

- successful rebuilt certificates pass the ordinary certificate verifier with
  the package axiom policy;
- bytes decoded only to discover the priority external dependency order remain
  untrusted and cannot enter an import context until ordinary verification;
- every unchanged support or unrelated certificate used in the complete
  snapshot is verified live in canonical refresh;
- refreshed import hashes come from the operation's verified values;
- final certificate and package-lock bytes retain canonical encodings;
- no output path is opened for staging until every required module and artifact
  has succeeded;
- existing no-follow target checks, retained directory capabilities, rollback,
  and all-or-nothing publication remain unchanged;
- proof acceptance still requires the package's cache-disabled source-free
  checker gates after refresh.

The structural preflight is allowed to stop a command early because the same
untrusted frontend can already stop that command. Its success cannot authorize
a write or suppress any later check.

## Concurrency And Mutation During A Run

This design does not claim a filesystem-wide atomic input snapshot. Preserve
the existing no-follow and target-identity protections.

Phase 1 deliberately scans source bytes that are read again by the later
canonical build. If a source changes between reads, that build compiles the
later bytes and performs all ordinary checks. A successful structural scan
never validates different bytes by identity. Consequently, a lexical or
delimiter error introduced after Phase 1 may be reported only when the
canonical frontend reaches that module, after priority certificate work has
started. This is outside the pre-certificate guarantee for the earlier scanned
bytes. In targeted refresh it still stops before targeted completion traversal;
in every refresh mode it stops before any staged write.

Within Phases 2 through 5, retain the exact external certificate buffers,
verified modules, source interfaces, and generated bytes that feed later steps.
Drop a local source string after its canonical build unless an existing helper
still needs it in that step. Do not re-open an already accepted priority
artifact merely to make the execution look globally ordered. Existing
publication-time target identity validation remains the authority for safe
replacement.

## Resource Bounds

- Structural preflight reuses the package CLI's existing 128 MiB no-follow
  regular-file read limit; it adds no claim of a separate lexer-token limit.
- The delimiter stack contains at most one entry per lexer token and is
  released with the token vector after each source.
- Priority external planning reuses
  `TARGETED_EXTERNAL_IMPORT_LIMIT`,
  `TARGETED_EXTERNAL_DEPENDENCY_EDGE_LIMIT`, and
  `TARGETED_EXTERNAL_CERTIFICATE_BYTES_LIMIT`.
- External certificate bytes retained between dependency discovery and
  verification count against the same targeted certificate-byte limit and are
  moved, not cloned, into the final artifact map after verification.
- Priority planning stores at most one bounded set or vector per local module
  and external import.
- Each certificate byte buffer and rebuilt module is retained no more than
  once. A priority rebuild with declared metadata retains at most one
  additional bounded source-interface clone until priority finalization.
- Detailed diagnostics retain the existing bounded declaration rows and source
  context only.
- Do not raise kernel conversion or WHNF fuel to implement this design.

## Implementation Areas

### `crates/npa-frontend/src/human_parser.rs`

- add `validate_human_source_lexical_structure` using `lex_human` tokens;
- add exact tests for strings, comments, nested delimiters, mismatched closers,
  missing closers, empty input, and non-ASCII byte spans.

### `crates/npa-frontend/src/lib.rs`

- export the new lexical-structure validator.

### `crates/npa-cli/src/package_build.rs`

- build and validate `TargetedRefreshLocalPlan` and
  `TargetedRefreshExternalPlan` at their certificate-free and certificate-read
  boundaries, respectively;
- run structural preflight after selection and before certificate loading;
- split frontend diagnostic construction from the optional containing-
  declaration lookup, and disable that lookup for structural failures;
- make external dependency discovery retain bounded bytes, and make external
  loading incremental and idempotent by index;
- split the local refresh loop into a reusable one-module operation;
- execute priority and completion orders against one state;
- refactor metadata refresh to consume the retained compact identity fields
  without re-decoding a priority certificate;
- canonicalize collected outputs independently of execution phase;
- extend bounded selection/refresh diagnostics.

### `crates/npa-cli/src/timing.rs`

- add the three optional millisecond timing fields in stable render order and
  preserve the no-clock behavior of timing mode `off`.

### `crates/npa-cli/tests/package_timings.rs`

- cover targeted refresh success and early failure, stable field order, and
  absence of all three fields when timing mode is `off`;
- cover initialized zero values for phases skipped after an early failure and
  the full-refresh omission of `priority_build_ms`.

### `crates/npa-cli/tests/package_build_certs_write.rs`

- add targeted refresh scheduling, output-parity, failure-order, and no-write
  regressions.

### `crates/npa-cli/tests/package_build_certs_check.rs`

- add check-mode parity and frontend diagnostic regressions where shared
  fixture support makes that clearer.

### Documentation

- after implementation, update `README.md`, `docs/README.md`,
  `docs/package-artifact-refresh-command-design.md`, and
  `docs/npa-toolchain-reference-v0.8.0.md` with the implemented failure-order
  contract, timing fields, and non-proposed status;
- retain this document as the design and implementation record, changing its
  status only when all acceptance criteria pass.

No change is expected in `npa-kernel`, `npa-cert` formats, package manifest
schema, package-lock schema, or the programmatic `package_api::v1` option
surface.

## Test Plan

### Frontend Unit Tests

- balanced nested `()`, `[]`, and `{}` pass;
- a delimiter in a line comment is ignored;
- a delimiter in a string literal is ignored;
- malformed string lexing retains the existing diagnostic;
- extra `)`, `]`, and `}` identify the closing token;
- missing closers identify EOF and the expected closer;
- crossed delimiters such as `([)]` report the first mismatch;
- Unicode before the failure preserves UTF-8 byte offsets;
- success does not require imported notation metadata;
- structural failure mapping does not invoke the full parser or declaration
  lookup;
- lexical success does not claim full parser success.

### Planner Unit Tests

- structural seed order is exactly the deduplicated selected set filtered from
  package topological order;
- a single leaf seed produces its exact forward support closure;
- multiple independent seeds are deduplicated and topologically ordered;
- a selected producer and selected downstream consumer put intervening rebuild
  modules in `priority_rebuild` rather than `priority_support`;
- lock-only changed selection produces an empty priority phase and the existing
  complete snapshot traversal;
- changed external selection without a selected lock preserves the existing
  validation/no-op branch and does not invent a local priority phase;
- manifest-change promotion records `promotion=manifest_changed`, scans every
  promoted seed, and degenerates to the ordinary local topological order;
- external roots expand through the existing exact bounded closure planner;
- priority and completion external orders are disjoint, cover every external
  import, and move each discovery byte buffer into verification without a
  reopen;
- priority and completion local sets are disjoint and cover the expected full
  targeted-refresh traversal;
- every semantic import precedes its consumer in the relevant phase history;
- out-of-range, duplicate, omitted, or cyclic synthetic plans fail closed.

### Failure-Order Integration Tests

Use compact temporary packages and operation counters or injected readers so
the tests establish read/verification boundaries without timing assertions.

- unmatched parenthesis in a selected seed fails before the first certificate
  read;
- missing, oversized, or non-UTF-8 selected source fails before the first
  certificate read through the existing `read_source` diagnostic mapping;
- malformed source in the second of two seeds scans seeds in deterministic
  topological order and writes nothing;
- an injected targeted-seed source replacement after successful preflight is
  read by the canonical build; a newly introduced lexical or delimiter error
  follows the ordinary priority-local failure order and writes nothing, rather
  than being treated as covered by the earlier scan;
- application of a non-function in a selected seed fails after exact support
  is loaded but before any unrelated certificate is read;
- invalid metadata for an earlier priority module does not hide a later
  selected frontend failure; after the source is repaired, the metadata error
  is reported before completion traversal;
- full refresh reports a structural source failure before its first
  certificate read and then uses the ordinary full build after preflight on a
  valid fixture;
- imported notation parses through the priority support source interface and
  is not rejected by the structural preflight;
- a malformed priority support source fails before unrelated snapshots;
- a missing unrelated certificate is not observed when a selected source
  fails first;
- after repairing the selected source, that missing unrelated certificate is
  still a hard failure;
- a failure in any phase leaves source, certificates, metadata, manifest, and
  package lock byte-identical to their initial state.
- structural, priority, completion, and comparison failures contain the exact
  selection/schedule/completed-plan diagnostic subset and ordering specified
  above.

### Success And Canonical-Parity Tests

- compare old/reference and new scheduling implementations on the same valid
  single-seed, multi-seed, diamond, and export-stable rebind fixtures;
- require byte equality for every generated certificate, refreshed metadata
  file, `npa-package.toml`, and `generated/package-lock.json`;
- in the two-phase targeted-refresh branch, assert every declared
  external-import index is opened, read, and verified at most once and every
  local index is processed at most once;
- assert selected seed compilation happens exactly once;
- assert deferred priority metadata does not re-decode its certificate;
- retain existing dependent rebuild, strict rebind, unchanged reuse, stale
  support, external hash mismatch, and atomic write tests;
- run check mode and write mode through the same planner and compare their
  expected in-memory outputs;
- verify refreshed fixtures through checked-lock source-free reference
  verification with caches disabled.

### Performance Regression Fixture

Add a generated compact package with:

- a long but cheap unrelated certificate chain;
- a small exact support chain;
- one selected malformed application module near the end of the old global
  order.

The blocking assertion is based on deterministic counters:

- only priority external and local support modules are visited before the
  selected frontend failure;
- zero unrelated snapshots and zero reverse-only dependents are visited;
- the selected module is attempted once.

Elapsed time and RSS remain advisory. Record the historical IUT observation as
context, not as a deterministic gate or proof evidence.

## Acceptance Criteria

The design is implementation-complete when all of the following hold:

- every selected lexical/delimiter error observed by structural preflight is
  returned before any certificate read; a source mutation after that scan
  follows the separately tested later-read behavior;
- selected application-shape and other exact frontend errors are returned
  after only the validated priority closure;
- no unrelated snapshot or reverse-only dependent is visited before a selected
  frontend failure;
- a successful selected module is not parsed, elaborated, built, encoded, or
  verified twice in one refresh command;
- the canonical two-phase targeted-refresh branch entered for a local seed or
  selected lock opens, reads, and verifies each declared external-import index
  at most once, including imports used during priority dependency discovery;
  the preserved no-local-seed/no-lock validation branch remains outside this
  invariant;
- every successful command performs the complete current refresh checks and
  produces byte-identical canonical artifacts to the reference ordering;
- check mode remains write-free and write mode remains all-or-nothing;
- missing or invalid unrelated artifacts still prevent successful canonical
  refresh and package-lock generation;
- external closure and source/certificate resource bounds remain enforced;
- `--changed` manifest promotion semantics are unchanged and visible in the
  plan counts;
- selection, schedule, completed refresh-plan, and primary diagnostics obey
  the specified presence, field, value, and ordering contract;
- timing-enabled refresh emits the specified phase fields and timing-off adds
  no clock or measurement work;
- cache modes, kernel fuel, certificate schemas, and package schemas are
  unchanged;
- focused frontend and CLI tests pass;
- `./scripts/check-fast.sh` passes from the `npa-core` repository root;
- `git diff --check` passes.

For a large proof package, acceptance evidence should additionally show a
targeted malformed-source run whose counters stop at the priority boundary and
a valid targeted refresh followed by the package's ordinary cache-disabled
source-free reference verification. The malformed run and timing report are
diagnostic evidence only.

## Implementation Record

The 2026-09-03 implementation follows the phase boundary in this document:

- `npa-frontend` exports `validate_human_source_lexical_structure`, backed by
  the ordinary Human lexer and delimiter token kinds;
- targeted refresh constructs and validates disjoint priority/completion local
  roles before source or certificate reads;
- external priority discovery retains its bounded certificate buffers, and
  the incremental loader verifies those same buffers before exposing them;
- one operation-owned execution state and verifier session span priority and
  completion, with duplicate local processing, external loading, or artifact
  paths rejected as internal plan/state errors;
- priority metadata consumes retained verified modules, source interfaces, and
  compact axiom-report hashes only after every priority local module succeeds;
- full refresh runs the structural scan and then its existing complete build,
  while targeted non-refresh checks retain their prior behavior; and
- selection promotion, refresh scheduling, completed-plan diagnostics, and the
  three optional timing fields follow the ordering specified above.

The regression suite covers ignored delimiters in strings and comments,
UTF-8 byte spans, every delimiter family, post-preflight source replacement,
first-certificate precedence, application-shape precedence over an unrelated
external import, deferred priority metadata, lock-only and manifest-promotion
plans, one read and verification per declared external index across priority
and completion, check/write atomicity, canonical byte parity, and timing-field
presence and ordering. Successful fixture refreshes continue through the
cache-disabled source-free reference verifier where the existing refresh suite
requires it.

The 2026-09-03 acceptance exercise also covered real proof-package scale. An
IUT temporary copy with an unmatched `(` in the selected
`RationalSetoidQuotient` source returned the structural parser diagnostic with
both `priority_build_ms` and `completion_build_ms` equal to zero and with every
kernel counter equal to zero. On the valid 255-module Riemann Hypothesis
package, a targeted canonical refresh of `FourierKernelRecovery` completed a
plan with 90 priority local support modules and 164 unrelated local snapshots.
The resulting 93-module closure then passed checked-lock source-free reference
verification with audit cache and verifier memo disabled,
`reference_checker_verdict=true`, `locally_accelerated=false`, and live proof
evidence. The timing values from these runs remain diagnostic rather than
acceptance or proof evidence.

## Alternatives Considered

### Parse Selected Sources With Empty Import Interfaces

Rejected. Human parsing activates notation from imported source interfaces.
Calling `parse_human_module(file_id, source)` without those interfaces can
reject valid imported notation and would create false diagnostics.

### Check Parenthesis Balance With A CLI Character Scanner

Rejected. It would mishandle comments, strings, UTF-8 spans, and future lexer
syntax, creating a second partial frontend. The validator must reuse the Human
lexer and token kinds.

### Run The Existing Targeted Check Before Every Refresh

Rejected as the implementation. It gives good failure latency, but every valid
command would compile the selected module twice and would still leave two
different orchestration paths. Users may continue to run targeted check
manually, but canonical refresh should schedule its own existing work once.

### Snapshot Unrelated Artifacts From The Existing Lock Without Verification

Rejected. That would weaken canonical refresh and could publish a new lock or
manifest around stale or unverified bytes.

### Emit Diagnostics From A Background Build While Traversal Continues

Rejected. Once a selected source is invalid, continued expensive work has no
value, and partial streamed JSON would complicate the command-result contract.

### Make The Priority Phase An Advisory Cache Hit

Rejected. Canonical refresh must use live, operation-owned verified state. An
authoring cache remains local, replaceable, and non-evidence feedback.

## Rollout

1. Add and test the frontend lexical-structure API.
2. Add the priority-closure planner and invariant tests without changing
   execution order.
3. Refactor external and local refresh processing into incremental,
   operation-scoped helpers.
4. Enable structural preflight and two-phase scheduling for targeted refresh
   check mode; establish no-write and byte-parity tests.
5. Enable the same path for targeted refresh write mode; establish atomicity
   and byte-parity tests.
6. Enable structural preflight for full refresh.
7. Add timing fields and the deterministic performance fixture.
8. Run focused tests, `check-fast`, compact checked-lock reference verification,
   and one large-package acceptance exercise.
9. Update the toolchain reference and mark this design implemented only after
   all gates pass.

Each rollout step must leave the old complete-closure validation in place on
successful runs. If output parity or safe state reuse cannot be demonstrated,
keep the scheduling change disabled rather than falling back to duplicate
canonical compilation.
