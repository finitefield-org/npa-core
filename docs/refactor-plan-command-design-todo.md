# Package Refactor Plan Command Todo

Source: `npa-core/docs/refactor-plan-command-design.md`

## Scope

This task breakdown implements the `npa package refactor-plan` MVP described in
the source design. The MVP is a read-only, source-free package command that
ranks local package modules and theorem families from checked package metadata.

The milestones cover parser work, runtime wiring, package-lock graph metrics,
optional theorem-index aggregation, scoring, deterministic diagnostic output,
source-free tests, and final documentation handoff.

This task breakdown does not cover non-MVP follow-ups: source-reading metrics,
`generated/dependency-index.json`, configurable score presets, recommendation
filtering, minimum score filtering, or markdown issue output.

## Global Constraints

- Keep `refactor-plan` advisory only; it is never proof evidence.
- Do not read `source.npa`, replay JSON, meta JSON, theorem search sidecars, AI
  traces, tactic traces, checker-result sidecars, registry data, or network
  data.
- Do not modify package manifests, generated package artifacts, certificates,
  package hashes, theorem-index hashes, publish metadata, verifier behavior, or
  certificate acceptance.
- Emit only existing `CommandResult` JSON with diagnostics for the MVP. Do not
  add command-specific JSON payloads or `CommandArtifact` entries.
- Create candidates only for local package-lock entries. External entries may
  contribute to graph validation and import context, but they are not refactor
  candidates.
- Preserve deterministic ordering, deterministic score rendering, stable reason
  codes, and lower-case stable string identifiers.
- Do not document the command in the toolchain reference until the runtime and
  required tests have been accepted.

## Milestones

### RFP-01 Parser And CLI Surface

- Status: Pending
- Depends on: None
- Inputs: design sections `Command Shape`, `Parser Changes`, `Error Handling`,
  and `Required Tests`; files `npa-core/crates/npa-cli/src/args.rs`,
  `npa-core/crates/npa-cli/src/package.rs`, and
  `npa-core/crates/npa-cli/tests/package_cli_args.rs`.
- Deliverables:
  - Add `PackageRefactorPlanScope`.
  - Add `PackageRefactorPlanOptions` with `common`, `scope`, `module`,
    `top`, and `include_source_metrics`.
  - Add `PackageCommand::RefactorPlan`.
  - Add `HelpTopic::PackageRefactorPlan`.
  - Parse `npa package refactor-plan` with common `--root` and `--json`.
  - Parse `--scope modules`, `--scope theorems`, and `--scope both`.
  - Parse `--module` into `npa_cert::Name` and reject non-canonical names with
    usage reason `invalid_module_name`.
  - Parse `--top` and enforce `1..=200`.
  - Reject duplicate `--scope`, `--module`, and `--top`.
  - Recognize `--include-source-metrics` and return usage reason
    `unsupported_flag` before any package root is loaded.
  - Add help text that includes `not proof evidence` and does not advertise
    `--include-source-metrics`.
  - Update package command list help and command-name/common-options plumbing.
  - Add an explicit failing runtime match arm if needed for enum exhaustiveness.
- Acceptance criteria:
  - Parser defaults are `scope=modules`, `top=20`, `root=.` and `json=false`.
  - Parser preserves parsed `Name` values for valid module names.
  - Invalid scope, invalid module syntax, out-of-range top values, duplicate
    flags, and the reserved source-metrics flag all return stable usage errors.
  - The crate compiles without adding any runtime path that reports a passed
    refactor plan before metadata loading exists.
- Verification:
  - `cargo test -q -p npa-cli package_cli_args`
  - `cargo test -q -p npa-cli package_cli_diagnostics`
- Notes:
  - If Rust exhaustiveness requires a temporary runtime match arm before
    RFP-06, it must fail explicitly and must not report an empty plan as
    successful.
  - Keep source-metrics support parser-only and unsupported in this milestone.

### RFP-02 Runtime Module And Metadata Loading

- Status: Pending
- Depends on: RFP-01
- Inputs: design sections `Runtime Files`, `Data Sources`, `Existing APIs To
  Reuse`, `Error Handling`, and `Source-Free Contract`; files
  `npa-core/crates/npa-cli/src/package.rs`,
  `npa-core/crates/npa-cli/src/lib.rs`,
  `npa-core/crates/npa-cli/src/package_artifacts.rs`,
  `npa-core/crates/npa-cli/src/package_index.rs`, and
  `npa-core/crates/npa-cli/src/package_verify.rs`.
- Deliverables:
  - Add `npa-core/crates/npa-cli/src/package_refactor_plan.rs`.
  - Add module declarations needed for focused `package_refactor_plan` tests.
  - Keep the public `PackageCommand::RefactorPlan` path on the explicit
    failing parser-stage runtime arm from RFP-01 until RFP-06 replaces it with
    the complete implementation.
  - Load the package root through `load_package_root`.
  - Load `generated/package-lock.json` through existing package-lock parsing
    patterns and preserve existing package-lock diagnostics where possible.
  - Build the package-lock graph with existing validation logic.
  - Read checked `generated/theorem-index.json` only when the file exists.
  - Treat missing theorem index as `theorem_index_status=missing`.
  - Map malformed or noncanonical theorem index errors to package failure
    reason `refactor_plan_theorem_index_invalid`.
  - Reject requested modules that are absent from the lock with
    `refactor_plan_module_unknown`.
  - Reject requested modules that exist only as external lock entries with
    `refactor_plan_module_not_local`.
  - Introduce the internal report and candidate data structures from the design.
- Acceptance criteria:
  - Metadata-loading helpers never read source, replay, meta, tactic trace, AI
    trace, checker-result, registry, or network data.
  - Missing theorem index is not a failure.
  - Invalid theorem index is a package failure with the design reason code.
  - Unknown and external-only requested modules are distinct package failures.
  - The public command still cannot report a passed refactor plan until module
    scoring and output are implemented.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-cli package_cli_args`
- Notes:
  - Reuse existing constants such as `PACKAGE_LOCK_PATH` and
    `PACKAGE_THEOREM_INDEX_PATH` where visibility allows; otherwise define
    identical local constants rather than importing private helpers by making
    broad API changes.
  - Do not add skeletal public success diagnostics in this milestone. Test the
    metadata-loading helpers directly.

### RFP-03 Package-Lock Graph And Module Metrics

- Status: Pending
- Depends on: RFP-02
- Inputs: design sections `Internal Data Model`, `Module Graph Algorithm`,
  `Certificate Size Metric`, `Exact Scoring Constants`, `Sorting And
  Determinism`, and `Required Tests`; files
  `npa-core/crates/npa-package/src/audit_selection.rs`,
  `npa-core/crates/npa-package/src/lock.rs`, and
  `npa-core/crates/npa-cli/src/package_refactor_plan.rs`.
- Deliverables:
  - Build topological module order from `build_package_lock_graph`.
  - Build direct import counts from `PackageLockEntry.imports`.
  - Build direct reverse dependents with `package_lock_reverse_dependencies`.
  - Compute transitive reverse dependents by breadth-first traversal, shortest
    distance, and package-lock topological traversal order.
  - Filter module candidates to `PackageLockEntryOrigin::Local`.
  - Read certificate file metadata only, using package-lock certificate paths.
  - Compute `certificate_size_bytes` and integer-bucket
    `certificate_size_weight`.
  - Add `certificate_metadata_unavailable` evidence when metadata cannot be
    read.
  - Compute module metrics that do not require theorem-index data.
- Acceptance criteria:
  - Direct and transitive dependent counts are deterministic.
  - Dependent complexity divides each dependent contribution by graph distance.
  - External lock entries are not emitted as candidates.
  - Certificate bytes are not opened or decoded by this command.
  - Missing certificate metadata produces nullable size and zero weight without
    failing the command.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-package package_lock`
- Notes:
  - Keep all maps as `BTreeMap` or sorted vectors and all sets as `BTreeSet` or
    sorted vectors before output.

### RFP-04 Theorem Index Aggregation And Family Clustering

- Status: Pending
- Depends on: RFP-03
- Inputs: design sections `Theorem Index Aggregation`, `Theorem Family
  Clustering`, `Future Dependency Index`, and `Required Tests`; files
  `npa-core/crates/npa-package/src/theorem_index.rs`,
  `npa-core/crates/npa-cli/src/package_index.rs`, and
  `npa-core/crates/npa-cli/src/package_refactor_plan.rs`.
- Deliverables:
  - Aggregate only theorem-index entries whose artifact origin is local and
    whose module is a local package-lock module.
  - Ignore external theorem-index entries.
  - Skip local theorem-index entries for unknown modules and add summary
    warning `theorem_index_entry_unknown_module`.
  - Count theorems, axioms, and public exports.
  - Collect theorem and axiom names for family clustering.
  - Ignore theorem-index tags in MVP scoring and output.
  - Build family prefixes from the last dotted declaration component split on
    underscores.
  - Keep only families with at least three entries.
  - Sort families by descending size, ascending prefix, and ascending first
    theorem name.
  - Compute distinct statement head and statement constant counts by stable
    module/name keys.
  - Avoid exact theorem-dependent wording in theorem-family output.
- Acceptance criteria:
  - Missing theorem index keeps theorem-derived module metrics nullable.
  - Families `foo_a`, `foo_b`, and `foo_c` group into `foo_*`.
  - Two-entry families are not emitted.
  - Axiom-bearing theorem families are identifiable for later risk scoring.
  - Theorem-family output and diagnostics use family-signal wording, not exact
    proof-dependent claims.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-cli package_index`
- Notes:
  - Do not project a theorem index in memory when the checked file is missing.

### RFP-05 Scoring, Recommendations, Risk, And Evidence

- Status: Pending
- Depends on: RFP-04
- Inputs: design sections `Exact Scoring Constants`, `Recommendation Rules`,
  `Evidence Strings`, `Trust Boundary`, and `Risks And Mitigations`; file
  `npa-core/crates/npa-cli/src/package_refactor_plan.rs`.
- Deliverables:
  - Implement all fixed scoring constants exactly as documented.
  - Compute local complexity, dependent complexity, family cluster bonus,
    mixed-purpose bonus, verification containment bonus, and final module
    score.
  - Compute theorem-family scores, risk, and recommendation.
  - Apply module recommendation priority order:
    `stabilize-boundary`, `extract-foundation`, `module-split`,
    `dependency-hygiene`, `local-cleanup`, then `no-action`.
  - Compute module risk thresholds exactly as documented.
  - Emit lower-case kebab-case recommendation and risk strings.
  - Assign all documented module evidence, theorem-family evidence, and
    summary warnings.
  - Build deterministic suggested units.
  - Build suggested verification command lists, with high-risk candidates
    including index and export-summary checks.
  - Ensure every report and candidate includes `proof_evidence=false`.
- Acceptance criteria:
  - Pure scoring tests cover exact constants.
  - Missing theorem-index counts contribute zero to local complexity while
    remaining nullable in rendered diagnostics.
  - Candidate sorting inputs use raw `f64` values; rendering rounds to one
    decimal place only at diagnostic output time.
  - High fanout plus small local complexity recommends `stabilize-boundary`.
  - Large modules with multiple clusters recommend `module-split`.
  - Evidence strings are stable lower-case snake-case.
  - Suggested units never contain semicolons or pipes.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
- Notes:
  - Keep scoring constants in one internal module or section so future tuning is
    localized and testable.

### RFP-06 Filtering, Sorting, Diagnostics, And JSON Output

- Status: Pending
- Depends on: RFP-05
- Inputs: design sections `Command Shape`, `Output Model`, `Sorting And
  Determinism`, `Error Handling`, and `Required Tests`; files
  `npa-core/crates/npa-cli/src/diagnostic.rs`,
  `npa-core/crates/npa-cli/src/package.rs`,
  `npa-core/crates/npa-cli/src/package_refactor_plan.rs`, and
  `npa-core/crates/npa-cli/tests/package_cli.rs`.
- Deliverables:
  - Replace the temporary parser-stage runtime failure and route
    `PackageCommand::RefactorPlan` from `run_package_command` to the complete
    runtime implementation.
  - Implement `--scope modules`, `--scope theorems`, and `--scope both`.
  - Apply `--module` filtering after local module validation.
  - Apply `--top` after deterministic sorting.
  - Sort candidates by descending score, descending dependent complexity,
    descending local complexity, ascending candidate kind, ascending module
    name, and ascending theorem-family key.
  - Emit one summary diagnostic and one diagnostic per candidate.
  - Use `DiagnosticKind::GeneratedArtifact`, field `refactor_plan`, and the
    documented reason codes.
  - Encode diagnostic `actual_value` fields in the exact documented key order.
  - Use `null` for absent nullable metrics and `none` for empty lists.
  - Use pipe-separated suggested verification command lists.
  - Use the existing `CommandResult` JSON renderer and emit no artifacts.
  - Keep output free of absolute temporary paths.
- Acceptance criteria:
  - Fixture integration tests cover diamond dependency ranking, large leaf
    cleanup, high-fanout risk, module filtering, stable JSON order, empty
    artifacts array, and path sanitization.
  - Human output remains diagnostics-based.
  - JSON output schema remains `npa.package.command_result.v0.1`.
  - The MVP does not add any command-specific JSON payload.
  - Valid package fixtures can run the public command successfully.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-cli package_cli`
  - `cargo test -q -p npa-cli package_cli_diagnostics`
- Notes:
  - Use the literal root placeholder required by the design in suggested
    commands, not actual absolute roots.

### RFP-07 Source-Free Guard Tests And Negative Coverage

- Status: Pending
- Depends on: RFP-06
- Inputs: design sections `Data Sources`, `Source-Free Contract`, `Required
  Tests`, and `Trust Boundary`; files
  `npa-core/crates/npa-cli/tests/package_cli.rs` and any new focused
  `package_refactor_plan` test fixture helpers.
- Deliverables:
  - Add tests proving the default command succeeds when source files are absent.
  - Add tests proving the default command succeeds when
    `generated/verified-export-summary.json` is absent.
  - Add tests proving output does not change when source-only files change.
  - Add tests proving the command does not open source, replay, meta, tactic
    trace, or AI trace paths, using missing-file fixtures or portable unreadable
    sentinels.
  - Add negative tests for malformed theorem index, unknown requested module,
    and external-only requested module.
  - Add tests that theorem-family output does not claim exact proof dependents.
- Acceptance criteria:
  - The source-free guard would fail if the implementation opened any forbidden
    sidecar path in default mode.
  - The command reads manifest, package lock, optional theorem index, and
    certificate metadata only.
  - The command does not require verified export summary metadata.
  - Failure diagnostics use the documented reason codes and do not reveal host
    paths.
- Verification:
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-cli package_cli_source_free`
  - `cargo test -q -p npa-cli package_cli`
- Notes:
  - Prefer compact in-repository fixtures under `npa-core/testdata` or temporary
    integration fixtures. Do not depend on sibling NPA repository checkouts.

### RFP-08 Documentation Handoff And Final Gate

- Status: Pending
- Depends on: RFP-07
- Inputs: design sections `Implementation Steps`, `Required Tests`,
  `Trust Boundary`, and `Non-MVP Follow-Ups`; files
  `npa-core/docs/refactor-plan-command-design.md`,
  `npa-core/docs/npa-toolchain-reference-v0.2.0.md`,
  `npa-core/docs/README.md`, `npa-core/README.md`, and
  `npa-core/CONTRIBUTING.md`.
- Deliverables:
  - Document `npa package refactor-plan` in the toolchain reference only after
    the command and required tests are accepted.
  - State that the command is advisory metadata, not proof evidence.
  - State that default mode is source-free and does not read source, replay,
    meta, tactic trace, AI trace, checker-result, registry, or network data.
  - Include concise command examples for module and theorem-family scopes.
  - Keep non-MVP features listed as future work, not current CLI behavior.
  - Run final formatting, focused package tests, and the repository fast gate
    unless a resource limit prevents it.
- Acceptance criteria:
  - Documentation agrees with implemented behavior and design constraints.
  - No docs imply source metrics, exact theorem dependents, command-specific
    JSON payloads, or proof-evidence status for the MVP.
  - Final code and docs pass focused tests.
  - If `./scripts/check-fast.sh` cannot be completed, the reason is recorded in
    the implementation report with the focused tests that did pass.
- Verification:
  - `cargo fmt --all -- --check`
  - `cargo test -q -p npa-cli package_cli_args`
  - `cargo test -q -p npa-cli package_refactor_plan`
  - `cargo test -q -p npa-cli package_cli_source_free`
  - `./scripts/check-fast.sh`
- Notes:
  - Keep `npa-core` self-contained. Do not add gates that require sibling
    repository checkouts.
