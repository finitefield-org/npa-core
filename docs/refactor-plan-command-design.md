# Package Refactor Plan Command Design

## Summary

Add a read-only package command that ranks modules, and optionally theorem
families, that are good candidates for refactoring:

```sh
npa package refactor-plan --root . --scope modules --top 20 --json
npa package refactor-plan --root . --scope theorems --module Proofs.Ai.Basic
```

The command uses package metadata to estimate:

- local module complexity;
- reverse dependent impact;
- theorem-family clustering;
- refactor risk;
- a conservative recommended refactor action.

The MVP is source-free. It reads package metadata and checked generated
artifacts, but it does not read `source.npa`, replay files, meta files, tactic
traces, or AI traces.

The command is advisory only. Its output is not proof evidence and must not
change certificate acceptance, package hashes, theorem-index hashes, publish
metadata, or verifier behavior.

## Final MVP Decisions

These choices are fixed for the first implementation.

- Command name: `npa package refactor-plan`.
- Default scope: `modules`.
- Default top count: `20`.
- Maximum top count: `200`.
- Default theorem-index behavior: read checked
  `generated/theorem-index.json` when present; otherwise continue with module
  graph metrics and render theorem/export counts as `null` in diagnostic
  `actual_value`.
- No in-memory theorem-index projection in the MVP.
- No source metrics in the MVP. The parser recognizes
  `--include-source-metrics` only to return the standard usage error
  `unsupported_flag` before loading the package root.
- Module recommendations are implemented in the MVP.
- Theorem-scope recommendations are family-signal recommendations only. They
  must not claim exact proof dependents.
- Exact theorem-level dependents require a later certificate-derived dependency
  index and are out of scope for the first command.

## Goals

- Rank refactor candidates from checked package metadata.
- Quantify reverse dependency impact before a human edits public modules.
- Prefer refactor suggestions that reduce future verification and maintenance
  cost.
- Keep output deterministic across platforms.
- Make every score explainable by emitted metrics and evidence strings.
- Preserve the existing NPA trust boundary.

## Non-Goals

- Do not prove, rewrite, move, or rename any theorem.
- Do not modify package manifests, generated artifacts, certificates, or source
  files.
- Do not treat the ranking as proof evidence or high-trust input.
- Do not make exact theorem-level proof-dependency claims in the MVP.
- Do not replace `gate-plan`, `verify-certs --changed`, package audit
  selection, or incremental generated-artifact projection planning.

## Command Shape

Add a new package subcommand. The full parser-recognized shape is:

```text
npa package refactor-plan [--root PATH] [--json]
  [--scope modules|theorems|both]
  [--module NAME]
  [--top N]
  [--include-source-metrics]
```

Examples:

```sh
npa package refactor-plan --root .
npa package refactor-plan --root . --scope modules --top 10 --json
npa package refactor-plan --root . --scope theorems --module Proofs.Ai.Basic
npa package refactor-plan --root . --scope both --module Mathlib.Logic.Basic
```

### Flags

`--scope modules|theorems|both`

- Optional.
- Defaults to `modules`.
- `modules` emits only module candidates.
- `theorems` emits theorem-family candidates. `--module` is strongly
  recommended but not required.
- `both` emits module candidates followed by theorem-family candidates.

`--module NAME`

- Optional.
- `NAME` is a dotted NPA module name.
- If present in `modules` scope, only that module candidate is emitted if it
  exists.
- If present in `theorems` scope, only theorem-family candidates from that
  module are emitted.
- Invalid module syntax is a usage error.
- Unknown module is a package failure with reason
  `refactor_plan_module_unknown`.
- A module that exists only as an external lock entry is a package failure with
  reason `refactor_plan_module_not_local`.

`--top N`

- Optional.
- Defaults to `20`.
- Must be an integer in `1..=200`.
- Applies after filtering by `--scope` and `--module`.
- Duplicate `--top` is a usage error.

`--include-source-metrics`

- Optional reserved flag.
- Recognized but unsupported in the MVP.
- The parser must return a usage error with reason `unsupported_flag` before
  loading the package root.
- Do not advertise this flag in the command help text until a source-reading
  implementation is accepted.
- Rationale: source-reading metrics require a separate trust-boundary review.

`--json`

- Uses the existing common package option.
- Human output remains diagnostics-based. JSON output must be stable and must
  not include absolute temp paths.

## Parser Changes

Modify `crates/npa-cli/src/args.rs`.

Add:

```rust
use npa_cert::Name;

pub enum PackageRefactorPlanScope {
    Modules,
    Theorems,
    Both,
}

pub struct PackageRefactorPlanOptions {
    pub common: PackageCommonOptions,
    pub scope: PackageRefactorPlanScope,
    pub module: Option<Name>,
    pub top: usize,
    pub include_source_metrics: bool,
}
```

Add `PackageCommand::RefactorPlan(PackageRefactorPlanOptions)`.

`parse_package_refactor_plan_args` must parse `--module` with
`Name::from_dotted(value)` and reject it when `!name.is_canonical()` with a
usage error reason `invalid_module_name`. Store the parsed `Name` in
`PackageRefactorPlanOptions`. Runtime module existence checks happen later
against the package lock.

Update:

- `PackageCommand::command_name`;
- `PackageCommand::common_options`;
- package subcommand parsing;
- package help;
- `parse_package_refactor_plan_args`;
- CLI parser tests in `crates/npa-cli/tests/package_cli_args.rs`.

Suggested help text:

```text
Usage: npa package refactor-plan [--root PATH] [--json]
  [--scope modules|theorems|both] [--module NAME] [--top N]

Rank advisory module and theorem-family refactor candidates from package
metadata. The plan is not proof evidence and does not read source files.
```

## Runtime Files

Add a new implementation file:

```text
crates/npa-cli/src/package_refactor_plan.rs
```

Update:

- `crates/npa-cli/src/package.rs` to route `PackageCommand::RefactorPlan`;
- `crates/npa-cli/src/lib.rs` or module declarations if required by the crate
  layout;
- docs/help tests if existing tests assert command lists.

## Data Sources

The MVP reads:

- `npa-package.toml`, through `load_package_root`;
- `generated/package-lock.json`, through the same package-lock loading path used
  by other package commands;
- `generated/theorem-index.json`, if present;
- certificate file metadata only for byte length, using package-lock
  certificate paths.

The command creates refactor candidates only for package-lock entries whose
origin is `PackageLockEntryOrigin::Local`. External lock entries may appear in
imports needed for graph validation, but they are never emitted as candidates.

The MVP must not read:

- `source.npa`;
- replay JSON;
- meta JSON;
- theorem search sidecars;
- AI traces;
- tactic traces;
- checker-result sidecars;
- registry or network data.

If `generated/theorem-index.json` is missing, malformed, stale, or noncanonical:

- missing: continue with `theorem_index_status = "missing"` and omit theorem
  metrics;
- malformed or noncanonical: return package failure with reason
  `refactor_plan_theorem_index_invalid`;
- stale detection is not required in the MVP because this command is advisory.
  If stale checks are added later, they must be reported as advisory freshness
  diagnostics, not proof evidence.

## Existing APIs To Reuse

Use these existing APIs where possible:

- `load_package_root` in `npa-cli::package`;
- package-lock read/parse helpers used by package commands;
- `PackageLockManifest`;
- `build_package_lock_graph`;
- `package_lock_reverse_dependencies`;
- `parse_package_theorem_index_json`;
- `PackageTheoremIndexEntry`;
- `PackageTheoremIndexKind`;
- `PackageArtifactOrigin`.
- `PackageLockEntryOrigin`.

Do not duplicate package-lock graph validation logic. If the lock graph is
invalid, return package failure with the underlying package-lock diagnostic.

## Internal Data Model

Implement internal structs in `package_refactor_plan.rs`.

```rust
struct RefactorPlanReport {
    schema: &'static str,
    root: String,
    scope: PackageRefactorPlanScope,
    theorem_index_status: TheoremIndexStatus,
    warnings: Vec<String>,
    candidates: Vec<RefactorCandidate>,
    proof_evidence: bool,
}

enum TheoremIndexStatus {
    Loaded,
    Missing,
}

enum RefactorCandidate {
    Module(ModuleRefactorCandidate),
    TheoremFamily(TheoremFamilyRefactorCandidate),
}

struct ModuleRefactorCandidate {
    module: Name,
    score: f64,
    recommendation: RefactorRecommendation,
    risk: RefactorRisk,
    metrics: ModuleRefactorMetrics,
    evidence: Vec<String>,
    suggested_unit: String,
    suggested_verification: Vec<String>,
    proof_evidence: bool,
}

struct TheoremFamilyRefactorCandidate {
    module: Name,
    family: String,
    score: f64,
    recommendation: RefactorRecommendation,
    risk: RefactorRisk,
    theorem_names: Vec<String>,
    metrics: TheoremFamilyMetrics,
    evidence: Vec<String>,
    suggested_unit: String,
    suggested_verification: Vec<String>,
    proof_evidence: bool,
}

struct ModuleRefactorMetrics {
    local_complexity: f64,
    dependent_complexity: f64,
    direct_dependents: usize,
    transitive_dependents: usize,
    direct_import_count: usize,
    theorem_count: Option<usize>,
    axiom_count: Option<usize>,
    public_export_count: Option<usize>,
    certificate_size_bytes: Option<u64>,
    certificate_size_weight: f64,
    family_cluster_count: usize,
}

struct TheoremFamilyMetrics {
    theorem_count: usize,
    axiom_count: usize,
    shared_prefix_length: usize,
    statement_head_count: usize,
    statement_constant_count: usize,
    module_dependent_complexity: f64,
}

enum RefactorRecommendation {
    ModuleSplit,
    ExtractFoundation,
    TheoremFamilyGroup,
    LocalCleanup,
    DependencyHygiene,
    StabilizeBoundary,
    NoAction,
}

enum RefactorRisk {
    Low,
    Medium,
    High,
}
```

All string renderings must be lower-case kebab-case:

- `module-split`
- `extract-foundation`
- `theorem-family-group`
- `local-cleanup`
- `dependency-hygiene`
- `stabilize-boundary`
- `no-action`
- `low`
- `medium`
- `high`

## Module Graph Algorithm

Input:

- `PackageLockManifest`.

Output:

- modules in package-lock topological order;
- direct imports per module;
- direct reverse dependents per module;
- transitive reverse dependents per module with distance.

Steps:

1. Build package-lock graph using existing package graph logic.
2. Get topological module order from the graph.
3. Build `direct_imports: BTreeMap<Name, BTreeSet<Name>>` from
   `PackageLockEntry.imports`.
4. Build `reverse_direct: BTreeMap<Name, Vec<Name>>` using
   `package_lock_reverse_dependencies`.
5. For each module, run breadth-first traversal over `reverse_direct`:
   - direct dependents have distance `1`;
   - dependents of dependents have distance `2`;
   - visit each module once at the shortest distance;
   - traversal order must follow package-lock topological order.

Pseudocode:

```text
for module in topological_order:
  queue = reverse_direct[module].map(distance=1)
  seen = {}
  while queue not empty:
    dependent, distance = pop_front(queue)
    if dependent in seen: continue
    seen[dependent] = distance
    for next in reverse_direct[dependent]:
      push_back(next, distance + 1)
  reverse_closure[module] = seen
```

## Theorem Index Aggregation

Input:

- optional `PackageTheoremIndex`.

For each eligible theorem-index entry:

- use `entry.global_ref.module` as the module key;
- count `kind == theorem` as theorem;
- count `kind == axiom` as axiom;
- count every entry as public export;
- collect theorem name strings for family clustering;
- collect `statement.head`, if present;
- collect `statement.constants`.

Build `local_lock_modules: BTreeSet<Name>` from package-lock entries whose
origin is `PackageLockEntryOrigin::Local`.

For module and theorem-family candidates, aggregate only entries that satisfy
both conditions:

- `entry.artifact.origin == PackageArtifactOrigin::Local`;
- `entry.global_ref.module` is in `local_lock_modules`.

External theorem-index entries are ignored. If a local theorem-index entry
points to a module outside `local_lock_modules`, skip that entry, append the
summary warning `theorem_index_entry_unknown_module`, and continue. Do not add
that warning to any candidate's `evidence`, because no candidate owns the
unknown module.

Entry tags are ignored in MVP scoring and output.

## Certificate Size Metric

For each local package-lock entry:

1. Use `entry.certificate`.
2. Join it with package root using existing package path helpers.
3. Read file metadata only.
4. If metadata read fails, set `certificate_size_bytes = null` and
   `certificate_size_weight = 0.0`; also add evidence
   `certificate_metadata_unavailable`.

Do not decode certificate bytes in this command.

Bucket:

```text
certificate_size_weight = min(bytes / 65_536, 10) as f64
```

Use `0` for external imports and missing metadata.

## Exact Scoring Constants

Use fixed constants in the MVP:

```text
AXIOM_WEIGHT = 3.0
DIRECT_IMPORT_WEIGHT = 2.0
PUBLIC_EXPORT_WEIGHT = 1.0
THEOREM_WEIGHT = 1.0
DEPENDENT_COMPLEXITY_WEIGHT = 2.0
MIXED_PURPOSE_BONUS = 4.0
FAMILY_CLUSTER_BONUS_PER_CLUSTER = 2.0
FAMILY_CLUSTER_BONUS_CAP = 10.0
VERIFICATION_CONTAINMENT_BONUS = 5.0
HIGH_FANOUT_DIRECT_THRESHOLD = 5
HIGH_FANOUT_TRANSITIVE_THRESHOLD = 12
LARGE_MODULE_EXPORT_THRESHOLD = 25
FAMILY_CLUSTER_MIN_SIZE = 3
```

Local complexity:

```text
theorem_score = theorem_count.unwrap_or(0) * THEOREM_WEIGHT
axiom_score = axiom_count.unwrap_or(0) * AXIOM_WEIGHT
export_score = public_export_count.unwrap_or(0) * PUBLIC_EXPORT_WEIGHT
import_score = direct_import_count * DIRECT_IMPORT_WEIGHT

local_complexity =
  theorem_score
  + axiom_score
  + export_score
  + import_score
  + certificate_size_weight
```

Dependent complexity:

```text
dependent_complexity =
  sum(local_complexity(dependent) / distance)
```

Cast integer terms and `distance` to `f64` before arithmetic. The certificate
size bucket uses integer division before the final `f64` cast.

Family cluster bonus:

```text
family_cluster_bonus =
  min(family_cluster_count * FAMILY_CLUSTER_BONUS_PER_CLUSTER,
      FAMILY_CLUSTER_BONUS_CAP)
```

Mixed-purpose bonus:

```text
mixed_purpose_bonus = MIXED_PURPOSE_BONUS
  if module has at least 2 family clusters and direct_import_count >= 2
  else 0
```

Verification containment bonus:

```text
verification_containment_bonus = VERIFICATION_CONTAINMENT_BONUS
  if transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
     and local_complexity <= 20
  else 0
```

Final module score:

```text
score =
  local_complexity
  + dependent_complexity * DEPENDENT_COMPLEXITY_WEIGHT
  + mixed_purpose_bonus
  + family_cluster_bonus
  + verification_containment_bonus
```

Keep raw `f64` values in memory. Round scores and `f64` metric values to one
decimal place when rendering diagnostic `actual_value` strings.

## Theorem Family Clustering

Only theorem-index entries participate.

For each module:

1. Collect theorem and axiom names.
2. Split each name into tokens:
   - start from `entry.global_ref.name.as_dotted()`;
   - use only the last dotted component for family tokenization;
   - split on `_`;
   - do not split camel case in the MVP;
   - drop empty tokens.
3. For each name, create a family prefix from the first token.
4. Group names by prefix.
5. Keep only groups with at least `FAMILY_CLUSTER_MIN_SIZE` entries.
6. Sort groups by:
   - descending group size;
   - ascending prefix;
   - ascending first theorem name.

The family key is:

```text
<module>::<prefix>_*
```

Example:

```text
module: Mathlib.Algebra.Field.Basic
names:
  field_add_assoc
  field_add_comm
  field_add_zero
family:
  Mathlib.Algebra.Field.Basic::field_*
```

Theorem-family score:

```text
score =
  theorem_count * 2.0
  + axiom_count * 4.0
  + min(shared_prefix_length, 12)
  + module_dependent_complexity
```

`shared_prefix_length` is the byte length of the prefix string.

Theorem-family risk:

- `high` if the owning module risk is `high` or `axiom_count > 0`;
- `medium` if theorem count is at least `8`;
- otherwise `low`.

Theorem-family recommendation:

- `theorem-family-group` when theorem count is at least `3`;
- `local-cleanup` otherwise.

Theorem-family metric details:

- `statement_head_count` is the number of distinct non-null `statement.head`
  global references in the family.
- `statement_constant_count` is the number of distinct
  `statement.constants` global references in the family.
- Distinct statement references are compared by stable string key
  `<module>::<name>`.

## Recommendation Rules

Evaluate module recommendations in this order:

1. `stabilize-boundary`
   - direct dependents >= `HIGH_FANOUT_DIRECT_THRESHOLD`, or
   - transitive dependents >= `HIGH_FANOUT_TRANSITIVE_THRESHOLD`,
   - and local complexity <= `20`.
2. `extract-foundation`
   - transitive dependents >= `HIGH_FANOUT_TRANSITIVE_THRESHOLD`, and
   - family cluster count >= `1`.
3. `module-split`
   - public export count >= `LARGE_MODULE_EXPORT_THRESHOLD`, and
   - family cluster count >= `2`.
4. `dependency-hygiene`
   - direct import count >= `5`, and
   - direct dependents <= `2`.
5. `local-cleanup`
   - local complexity >= `15`.
6. `no-action`
   - everything else.

Risk:

```text
high:
  transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
  or direct_dependents >= HIGH_FANOUT_DIRECT_THRESHOLD

medium:
  transitive_dependents >= 4
  or public_export_count.unwrap_or(0) >= LARGE_MODULE_EXPORT_THRESHOLD

low:
  otherwise
```

Suggested verification:

- Always include:
  `npa package verify-certs --root <root> --changed --checker reference --json`
- For high-risk candidates, also include:
  `npa package index --root <root> --check --json`
  and
  `npa package export-summary --root <root> --check --json`

Suggested units:

- For module candidates with at least one theorem-family cluster, use the
  largest family key after the theorem-family sort order, for example
  `Proofs.Ai.Basic::eq_*`.
- For module candidates without theorem-family clusters, use the module dotted
  name.
- For theorem-family candidates, use the theorem-family key.
- Suggested units must be deterministic ASCII strings and must not contain
  semicolons or pipes.

## Evidence Strings

Evidence strings must be stable lower-case snake-case identifiers.

Module evidence examples:

- `high_direct_dependents`
- `high_transitive_dependents`
- `large_public_export_count`
- `multiple_theorem_family_clusters`
- `many_direct_imports`
- `small_foundational_high_fanout`
- `certificate_metadata_unavailable`
- `theorem_index_missing`

Theorem-family evidence examples:

- `large_theorem_family`
- `axiom_bearing_family`
- `shared_name_prefix`
- `high_fanout_owner_module`
- `statement_constant_signal`

Summary warning examples:

- `theorem_index_entry_unknown_module`

Evidence assignment:

- Add `high_direct_dependents` when direct dependents are at least
  `HIGH_FANOUT_DIRECT_THRESHOLD`.
- Add `high_transitive_dependents` when transitive dependents are at least
  `HIGH_FANOUT_TRANSITIVE_THRESHOLD`.
- Add `large_public_export_count` when
  `public_export_count.unwrap_or(0) >= LARGE_MODULE_EXPORT_THRESHOLD`.
- Add `multiple_theorem_family_clusters` when `family_cluster_count >= 2`.
- Add `many_direct_imports` when `direct_import_count >= 5`.
- Add `small_foundational_high_fanout` when
  `transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD` and
  `local_complexity <= 20`.
- Add `certificate_metadata_unavailable` only when certificate metadata cannot
  be read.
- Add `theorem_index_missing` to every module candidate when theorem-index
  status is `Missing`.
- Add `large_theorem_family` when family theorem count is at least `8`.
- Add `axiom_bearing_family` when family axiom count is greater than `0`.
- Add `shared_name_prefix` to every theorem-family candidate.
- Add `high_fanout_owner_module` when the owning module risk is `high`.
- Add `statement_constant_signal` when `statement_constant_count > 0`.

Human output may render a short explanation after each evidence code, but JSON
must include the stable codes.

## Output Model

Human output is diagnostics-based and should emit one diagnostic per candidate
plus one summary diagnostic.

Recommended diagnostic fields:

- `kind = GeneratedArtifact`
- summary reason code: `refactor_plan_summary`
- module candidate reason code: `refactor_plan_module_candidate`
- theorem family candidate reason code:
  `refactor_plan_theorem_family_candidate`
- `field = "refactor_plan"`
- `module = <module>` when applicable;
- `actual_value` is a semicolon-separated stable key-value string using the
  exact field order below.

JSON output must use the existing `CommandResult` renderer with schema
`npa.package.command_result.v0.1`. The MVP must not add a command-specific JSON
payload and must not add `CommandArtifact` entries. All refactor-plan data lives
in `diagnostics[].actual_value`.

Diagnostic `actual_value` encoding:

- use semicolon-separated `key=value` pairs;
- use the exact field order documented below for deterministic tests;
- use lower-case snake-case keys;
- use `null` for absent nullable metrics;
- use comma-separated lists for evidence and warnings;
- use `none` for empty lists;
- use pipe-separated commands for `suggested_verification`;
- use the literal `<root>` placeholder inside suggested commands instead of
  embedding absolute or temporary paths;
- never emit semicolons or pipes inside values.

Summary diagnostic:

```text
schema=npa.cli.package.refactor_plan.v0.1;scope=modules;theorem_index_status=loaded;candidate_count=1;module_candidate_count=1;theorem_family_candidate_count=0;warnings=none;proof_evidence=false
```

Module candidate diagnostic field order:

```text
kind=module;module=<module>;score=<f64>;recommendation=<recommendation>;risk=<risk>;local_complexity=<f64>;dependent_complexity=<f64>;direct_dependents=<usize>;transitive_dependents=<usize>;direct_import_count=<usize>;theorem_count=<usize|null>;axiom_count=<usize|null>;public_export_count=<usize|null>;certificate_size_bytes=<u64|null>;certificate_size_weight=<f64>;family_cluster_count=<usize>;evidence=<csv|none>;suggested_unit=<text>;suggested_verification=<cmd|cmd>;proof_evidence=false
```

Theorem-family candidate diagnostic field order:

```text
kind=theorem-family;module=<module>;family=<module>::<prefix>_*;score=<f64>;recommendation=<recommendation>;risk=<risk>;theorem_count=<usize>;axiom_count=<usize>;shared_prefix_length=<usize>;statement_head_count=<usize>;statement_constant_count=<usize>;module_dependent_complexity=<f64>;evidence=<csv|none>;suggested_unit=<text>;suggested_verification=<cmd|cmd>;proof_evidence=false
```

Example module candidate `actual_value`:

```text
kind=module;module=Proofs.Ai.Basic;score=91.4;recommendation=extract-foundation;risk=medium;local_complexity=22.0;dependent_complexity=34.7;direct_dependents=5;transitive_dependents=14;direct_import_count=3;theorem_count=38;axiom_count=0;public_export_count=38;certificate_size_bytes=51200;certificate_size_weight=0.0;family_cluster_count=2;evidence=high_transitive_dependents,multiple_theorem_family_clusters;suggested_unit=Proofs.Ai.Basic::eq_*;suggested_verification=npa package verify-certs --root <root> --changed --checker reference --json;proof_evidence=false
```

Representative JSON shape:

```json
{
  "schema": "npa.package.command_result.v0.1",
  "command": "package refactor-plan",
  "root": ".",
  "status": "passed",
  "diagnostics": [
    {
      "kind": "GeneratedArtifact",
      "reason_code": "refactor_plan_summary",
      "severity": "info",
      "field": "refactor_plan",
      "actual_value": "schema=npa.cli.package.refactor_plan.v0.1;scope=modules;theorem_index_status=loaded;candidate_count=1;module_candidate_count=1;theorem_family_candidate_count=0;warnings=none;proof_evidence=false"
    },
    {
      "kind": "GeneratedArtifact",
      "reason_code": "refactor_plan_module_candidate",
      "severity": "info",
      "module": "Proofs.Ai.Basic",
      "field": "refactor_plan",
      "actual_value": "kind=module;module=Proofs.Ai.Basic;score=91.4;recommendation=extract-foundation;risk=medium;local_complexity=22.0;dependent_complexity=34.7;direct_dependents=5;transitive_dependents=14;direct_import_count=3;theorem_count=38;axiom_count=0;public_export_count=38;certificate_size_bytes=51200;certificate_size_weight=0.0;family_cluster_count=2;evidence=high_transitive_dependents,multiple_theorem_family_clusters;suggested_unit=Proofs.Ai.Basic::eq_*;suggested_verification=npa package verify-certs --root <root> --changed --checker reference --json;proof_evidence=false"
    }
  ],
  "artifacts": []
}
```

Diagnostic nullability:

- theorem-derived counts are `null` when theorem index is missing;
- certificate size is `null` when metadata is unavailable;
- scores are still rendered with missing components treated as zero.

## Sorting And Determinism

Sort candidates by:

1. descending score;
2. descending dependent complexity;
3. descending local complexity;
4. ascending candidate kind string;
5. ascending module dotted name;
6. ascending theorem-family key, for theorem-family candidates.

Apply `--top` after sorting.

All maps should be `BTreeMap` or sorted vectors. All sets should be `BTreeSet`
or sorted vectors before output.

## Error Handling

Use existing `CommandDiagnostic` patterns.

Usage errors:

- invalid `--scope`;
- invalid `--module` syntax, with reason `invalid_module_name`;
- missing value for flags requiring values;
- duplicate `--scope`, `--module`, or `--top`;
- `--top` outside `1..=200`;
- `--include-source-metrics` in MVP.

Package failures:

- package root cannot be loaded;
- package lock missing or invalid;
- requested module is syntactically valid but absent from the package lock;
- requested module exists only as an external lock entry;
- theorem index exists but is invalid or noncanonical.

Missing theorem index is not a failure. It is advisory metadata absence.

## Source-Free Contract

The MVP command must never open or stat source, replay, meta, tactic trace, or
AI trace files.

Allowed filesystem reads:

- manifest;
- package lock;
- theorem index;
- certificate file metadata.

If future `--include-source-metrics` is implemented, it must:

- be disabled by default;
- add `source_metrics_enabled=true` to summary diagnostics;
- clearly mark source-derived metrics as advisory;
- have tests showing default mode does not read source files.

## Future Dependency Index

Exact theorem dependent recommendations require a new generated artifact:

```text
generated/dependency-index.json
```

Out-of-scope future schema sketch:

```json
{
  "schema": "npa.package.dependency_index.v0.1",
  "profile": "npa.package.dependency_index.v0.1.certificate_derived",
  "entries": [
    {
      "global_ref": {
        "module": "Proofs.Ai.Basic",
        "name": "foo"
      },
      "direct_dependencies": [
        {
          "module": "Std.Logic.Eq",
          "name": "Eq.rec"
        }
      ]
    }
  ],
  "proof_evidence": false
}
```

Until that artifact exists, theorem-scope output must say `family-signal` or
`statement-constant-signal`, not `proof-dependent`.

## Implementation Steps

1. Add parser data types and command enum variant.
2. Add parser and help tests.
3. Add `package_refactor_plan.rs` with internal model and pure scoring
   functions.
4. Add package command routing.
5. Implement lock loading and reverse dependency metrics.
6. Implement optional theorem-index parsing and aggregation.
7. Implement certificate metadata size buckets.
8. Implement module scoring, recommendations, risk, and evidence.
9. Implement theorem-family clustering and scoring.
10. Implement diagnostics and JSON rendering.
11. Add fixture integration tests.
12. Add source-free guard tests.
13. Document the command in the toolchain reference only after implementation is
    accepted.

## Required Tests

Parser tests:

- parses defaults;
- parses `--scope modules`;
- parses `--scope theorems`;
- parses `--scope both`;
- parses `--module Proofs.Ai.Basic`;
- rejects invalid `--module Proofs..Bad`;
- parses `--top 1` and `--top 200`;
- rejects `--top 0`;
- rejects `--top 201`;
- rejects duplicate flags;
- rejects `--include-source-metrics` in MVP;
- help text includes `not proof evidence`.

Pure scoring tests:

- score calculation uses exact constants;
- candidate sorting is deterministic;
- reverse dependent distance divides dependent contribution;
- missing theorem index uses zero theorem contribution;
- family clusters require at least three names;
- high fanout plus small local complexity recommends
  `stabilize-boundary`;
- large module with multiple clusters recommends `module-split`.

Fixture integration tests:

- diamond dependency graph ranks the shared dependency highest;
- large leaf module recommends `local-cleanup`;
- high-fanout module reports `high` risk;
- `--module` filters to one module;
- CommandResult JSON diagnostics have stable order and `proof_evidence=false`;
- CommandResult JSON has an empty `artifacts` array;
- output contains no absolute temp paths.

Source-free guard tests:

- default command succeeds when source files are absent;
- default command succeeds when `generated/verified-export-summary.json` is
  absent;
- default command output does not change when source-only files change;
- default command does not open `source.npa`, replay, meta, tactic trace, or AI
  trace paths. Use missing-file fixtures or unreadable sentinel files where
  portable.

Theorem-family tests:

- groups `foo_a`, `foo_b`, `foo_c` into `foo_*`;
- does not group two-name prefixes;
- theorem-family risk is high when any family entry is an axiom;
- theorem-family output does not claim exact proof dependents.

## Trust Boundary

`refactor-plan` is planning metadata only. It is not proof evidence.

Trusted proof evidence remains:

- canonical `.npcert` bytes;
- Rust kernel / verifier verdict;
- source-free checker verdict;
- deterministic certificate, export, import, and axiom-report hashes.

Untrusted advisory metadata includes:

- refactor scores;
- recommendations;
- theorem-index tags;
- theorem-family clusters;
- future dependency-index entries;
- future source metrics.

Every report must include `proof_evidence=false`.

## Risks And Mitigations

- Risk: a score can make a risky public refactor look objective.
  Mitigation: always show evidence, recommendation, and risk.
- Risk: theorem-family MVP can overstate dependency precision.
  Mitigation: avoid `dependent` wording for theorem families until a
  certificate-derived dependency index exists.
- Risk: source reads would violate package-command expectations.
  Mitigation: source metrics remain unsupported in the MVP.
- Risk: weights may need tuning.
  Mitigation: keep constants in one internal module and cover them with tests.
- Risk: large packages may make transitive closure expensive.
  Mitigation: compute reverse closure once per module and reuse it for scoring.

## Non-MVP Follow-Ups

- Implement `--include-source-metrics`.
- Add `generated/dependency-index.json`.
- Add user-configurable score presets.
- Add `--recommendation KIND` filtering.
- Add `--min-score VALUE`.
- Add markdown output for issue creation.
