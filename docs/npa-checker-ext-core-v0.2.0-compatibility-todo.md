# OCaml External Checker Core v0.2.0 Compatibility Audit And Task List

Audit date: 2026-07-11

Normative baseline:

- `core-spec-v0.2.0.md`
- `npa-checker-ext-ocaml.md`

Implementation under review:

- `checkers/npa-checker-ext/`
- the `npa-checker-ext` launch and raw-result adoption paths in
  `crates/npa-api/src/independent_checker.rs`

## Implementation Status

Completed on 2026-07-11. All EXT-COMPAT-01 through EXT-COMPAT-12 work items
are implemented and covered by the following release-authority commands:

```sh
checkers/npa-checker-ext/scripts/test.sh
checkers/npa-checker-ext/scripts/differential.sh
```

The differential gate regenerates and byte-compares the committed conformance
fixtures and runs the fast kernel, reference checker, and OCaml checker with the
same high-trust axiom policy and recursively checked import closure. It covers
legacy/current/previous certificates, checked `Std.Logic.Eq` interoperability,
local and imported indexed and mutual recursor iota,
indexed/mutual/nested positives, constructor-universe attacks, direct semantic
rejection, invalid pinned import closures, missing pins, duplicate candidates,
empty and malformed leaves, noncanonical and hash-invalid unrelated candidates,
candidate-count exhaustion during bounded directory traversal before decoding,
per-file and aggregate candidate-byte limits, oversized candidates, exact
source/replay subtree exclusion, symlink-root rejection, import cycles, and
explicit axiom denial. It compares raw error kind, reason, and section while
leaving implementation-private byte offsets unconstrained, parses raw output
through the Rust runner, and runs a real external package import DAG with the
OCaml binary. The source-free trace gate
enforces an allowlist over every observed filesystem and network syscall and
requires successful read opens for the leaf, policy, and imported certificates.
The dedicated launch contract passes the pinned policy file hash. On
Linux/Android, package execution uses a sealed `memfd` snapshot of the checker
bytes that satisfied the binary registry hash. Platforms without that
kernel-backed immutable snapshot fail closed with
`checker_binary_immutable_snapshot_unsupported` and cannot produce external
high-trust evidence.

| Tasks | Status | Primary evidence |
| --- | --- | --- |
| EXT-COMPAT-01–04 | Complete | `test/conformance-manifest.tsv`, canonical re-encoding/hash suites, generated fixtures |
| EXT-COMPAT-05–08 | Complete | abstract checker capability, indexed/mutual/nested fixtures, recursor/positivity suites |
| EXT-COMPAT-09–11 | Complete | policy-checked DAG session, real CLI, raw parser, deterministic resource and trace gates |
| EXT-COMPAT-12 | Complete | `scripts/differential.sh` and the real OCaml external-package test |

## Original Audit Verdict (Closed)

The implementation audited at the start of this document was not fully
compatible with NPA Core v0.2.0. The following list records the now-closed
baseline findings that motivated the tasks:

- the executable returns a deterministic `checker_internal_error` skeleton
  result for every complete check-shaped invocation;
- the decoder and module hash domains identify only
  `NPA-CERT-0.1` / `NPA-Core-0.1`;
- current and previous public exports cannot carry the required universe
  constraints;
- indexed inductives, mutual inductive blocks, and approved nested recursion
  are not semantically checked;
- high-trust import evidence cannot be constructed solely from successful
  OCaml checker results; and
- some certificate-wide canonical-order rules are not enforced.

Those findings are retained as historical audit evidence; they no longer
describe the current executable.

## Compatibility Standard Used By This Audit

“Fully compatible” means that the standalone OCaml checker:

1. accepts every valid certificate construct required by Core v0.2.0;
2. rejects every invalid or non-canonical construct required to be rejected by
   Core v0.2.0;
3. implements the current, previous, and legacy version behavior recorded by
   the core specification;
4. computes the same module identity, public environment, hashes, axiom report,
   and trust-mode result as the Rust implementation;
5. consumes only the source-free inputs supplied through the runner contract;
6. emits raw results accepted by the runner with deterministic failure
   classification; and
7. can participate in the documented recursive high-trust package check
   without manufacturing checked-import evidence.

Exact agreement on an implementation-private error offset is not required
unless the external-checker raw-result contract makes that offset normative.
Agreement on acceptance, module identity, hashes, and the stable error kind and
reason code is required.

## Original Audit Method And Evidence

The original audit reviewed the complete normative core specification, the OCaml
external-checker specification, every OCaml source module, the OCaml test
runner, and the Rust runner boundary. It also exercised the current build and
test path as it existed before EXT-COMPAT-01 through EXT-COMPAT-12 were
implemented.

Originally observed commands and outcomes:

```sh
cd npa-core
checkers/npa-checker-ext/scripts/test.sh
checkers/npa-checker-ext/_build/npa-checker-ext --version
checkers/npa-checker-ext/_build/npa-checker-ext \
  --cert <certificate.npcert> \
  --import-dir <import-directory> \
  --policy <axiom-policy.toml> \
  --output json
```

- The test suite passes.
- `--version` reports `NPA-CERT-0.1` and `NPA-Core-0.1`.
- A complete check-shaped invocation exits normally but returns the stable
  skeleton failure with reason `checker_reported_internal_error` and section
  `skeleton`; it does not check the supplied certificate.
- At the time of the original audit, the Rust external-checker launch plan
  passed exactly `--cert`, `--import-dir`, `--policy`, and `--output`. The
  completed contract now additionally passes the pinned `--policy-hash`;
  generic import-manifest flags remain outside this dedicated path.

The original source evidence most directly establishing the blockers was:

- `Ext_cli.run` returns `Ext_result.skeleton_failure` for a complete invocation.
- `Ext_typecheck.check_certificate` returns `Type_check_not_implemented`.
- `Ext_cert.expected_format` and `expected_core_spec` are the legacy tags.
- `Ext_result` publishes the same legacy identity.
- `Ext_canonical` uses `NPA-MODULE-EXPORT-0.1` and
  `NPA-MODULE-CERT-0.1` unconditionally.
- `Ext_cert.export_entry` has no universe-constraint field.
- the recursor checker rejects non-empty index lists as
  `unsupported_declaration`.
- the declaration checker rejects mutual blocks as
  `unsupported_declaration`, while `Ext_inductive.check_block` remains a stub.
- positivity and iota handling cover direct recursion, not the exact approved
  nested and mutual cases required by v0.2.0.
- `Ext_import_store.from_checked_modules` changes an entry’s checked marker
  without tying that marker to a successful checker result.

## Compatibility Matrix (Original Audit Baseline)

This matrix records the pre-implementation state. The implementation-status
table above and the conformance manifest are authoritative for the completed
state.

| Core area | Status | Implemented evidence | Remaining incompatibility |
| --- | --- | --- | --- |
| Clean-room and source-free boundary | Partial | The project has no Rust linkage; import loading accepts certificate files and rejects known source/replay paths. | The real executable path does not yet read or check its allowed inputs, so the boundary has not been demonstrated for a successful verdict. |
| Names, levels, terms, and de Bruijn scope | Substrate compatible | Strict name grammar, level/term decoding, well-formedness, table reachability, and local scope checks are present. | These checks are reachable only through unit APIs for real checking, and must be revalidated through current-format end-to-end fixtures. |
| Certificate versions and layout | Incompatible | A legacy header and a hybrid set of constrained declaration tags can be decoded. | Current `0.2.0` and previous `0.1.2` header pairs, export constraints, and version-specific layout rules are absent. |
| Universe constraints | Partial | Canonical contexts, satisfiability, entailment, substitution, bounded right-hand `max`, and constructor-field bounds are implemented and tested. | Current/previous export entries cannot encode or import constraints, and the current certificate versions cannot reach this substrate. |
| Canonical binary encoding | Partial | Minimal byte decoding, strict name/level/term ordering, normalization, reachability, and derived export ordering are checked. | There is no complete version-aware canonical re-encode comparison, and import-table plus dependency-depth/declaration-name ordering are not explicitly enforced. |
| Declaration, interface, export, and certificate hashes | Incompatible for current core | Legacy declaration, export, axiom-report, and certificate hash recomputation exists. | Current/previous domains and export/interface commitment to universe constraints are absent. |
| Basic typing and conversion | Substrate mostly compatible | Sort, bound variable, constant, Pi, lambda, application, let, beta/delta/zeta, theorem opacity, fuel, and builtin `Nat.rec` iota are implemented. | `check_certificate` is a stub, so no complete certificate runs these phases; full differential coverage is also absent. |
| Initial builtin environment | Substrate compatible | Exact local signatures and identities exist for Nat, Eq, their constructors, and their recursors. | The identities have not been exercised through a current-format executable check or the cross-implementation corpus. |
| Simple inductives | Substrate compatible | Family, constructor target, positivity, generated interface, simple recursor shape/iota, Prop motive, and constructor universe-bound checks exist for non-indexed single families. | They are not reachable from a complete executable check and must remain correct when the generalized inductive implementation lands. |
| Indexed inductive families | Incompatible | Certificate values can preserve index binders. | Recursor construction/checking and iota explicitly reject non-empty indices. |
| Mutual inductive blocks | Incompatible | The decoder and canonical export derivation can represent mutual blocks. | Semantic checking, atomic installation, mutual positivity, recursors, and iota are unsupported. |
| Approved nested recursion | Incompatible | Direct positive recursive fields are recognized. | Exact structural List/Option/Prod recognition, nested positivity, fake-functor rejection, nested induction hypotheses, and mutual nested behavior are absent. |
| Normal imports | Substrate compatible | Module/export matching and optional certificate-hash matching use a decoded, hash-checked, source-free store. | It is not wired into a real module check. Normal mode must remain distinct from high-trust mode; semantic validation of every normal import is not a v0.2.0 requirement. |
| High-trust import closure | Incompatible | Resolution can require a certificate hash and a checked marker. | No recursive OCaml check produces an unforgeable checked-entry capability; the public marker-conversion helper is insufficient evidence. |
| Core feature profile | Partial | The required empty supported set and deterministic unsupported-feature rejection are implemented. | The gate is not part of an executable check. |
| Axiom report and policy | Partial | Policy TOML parsing, dependency recomputation, report comparison, imported dependencies, standard exceptions, and allow/deny rules are implemented. | Policy file loading, phase orchestration, checked-result report hash, and raw-result error mapping are not wired. |
| Raw result and CLI | Incompatible | Argument-shape validation, `--version`, deterministic skeleton JSON, and result rendering helpers exist. | There is no checked-result path and no real input processing or semantic failure mapping. |
| Resource determinism | Partial | Conversion fuel and universe-solver caps exist; the runner owns timeout and memory enforcement. | Explicit import/table/depth caps, stack-safe certificate traversal, and end-to-end deterministic exhaustion tests are incomplete. |
| Differential and package release gate | Incompatible | Rust runner registry, launch-plan, normalization, and package test scaffolding exist. | No real OCaml checked verdict is compared with the kernel/reference checker or used to close a package import DAG. |

## Required Tasks

Tasks are ordered by dependency, not by estimated duration. A task is complete
only when its acceptance criteria and focused tests pass. Temporary support for
only a subset of valid Core v0.2.0 constructs must continue to fail closed and
must not be described as full compatibility.

### EXT-COMPAT-01: Freeze A Cross-Implementation Conformance Corpus

**Purpose:** Establish a reviewable compatibility oracle before changing the
wire format or semantics.

**Work:**

- Add a manifest under `checkers/npa-checker-ext/test/` that maps every
  normative Core v0.2.0 area to positive and negative certificate fixtures.
- Commit canonical source-free `.npcert` fixtures for current `0.2.0`, previous
  `0.1.2`, and legacy `0.1`. Keep fixture-generation source or a reproducible
  generator command separate from the OCaml runtime checker.
- Include basic declarations, reducible and opaque bodies, universe
  constraints, public constraint substitution, simple/indexed/mutual/nested
  inductives, recursor iota, Prop elimination, imports, features, and axiom
  policy.
- Cover exact Nat/Eq builtin identities, sort cumulativity, normalized
  `max`/`imax`, the syntactic-`Sort 0` Prop exemption, and the rejection of a
  universe parameter that is merely constrained equal to zero as a Prop
  exemption.
- Include a negative conversion fixture whose proof would succeed only if a
  universe constraint were incorrectly treated as a definitional-equality
  assumption.
- Include self-consistent mutations for non-canonical order, wrong hashes,
  wrong import identities, malformed recursors, positivity violations,
  constructor universe violations, and forbidden axioms.
- Record expected acceptance, module name, certificate/export/axiom hashes, and
  stable error kind/reason for each fixture from the normative Rust
  implementation.
- Add a differential test driver that can run the Rust reference checker and
  the OCaml executable over exactly the same source-free inputs.

**Acceptance criteria:**

- Every row of the compatibility matrix has at least one fixture or an explicit
  non-fixture assertion.
- Current, previous, and legacy version behavior is represented.
- The corpus distinguishes normal imports from recursively checked high-trust
  imports.
- The corpus distinguishes universe entailment obligations from definitional
  equality and covers the exact initial builtin interfaces.
- Corpus generation is reproducible and the committed expected hashes are
  checked for staleness.
- The initial differential result is allowed to document known OCaml failures;
  the harness itself must pass by matching the declared known-gap manifest.

**Dependencies:** None.

### EXT-COMPAT-02: Implement The Versioned Certificate Data Model And Decoder

**Purpose:** Decode the exact current, previous, and legacy certificate
languages without silently changing their public meaning.

**Work:**

- Replace the single fixed header expectation with an internal certificate
  version selected from an exact format/core-spec pair.
- Accept only these matched pairs:
  `NPA-CERT-0.2.0` / `NPA-Core-0.2.0`,
  `NPA-CERT-0.1.2` / `NPA-Core-0.1.2`, and
  `NPA-CERT-0.1` / `NPA-Core-0.1`.
- Reject mixed pairs and unknown versions deterministically.
- Extend export entries and public signatures with canonical universe
  constraints for current and previous certificates.
- Preserve the exact current/previous declaration tags and export-block shape.
- Decode legacy exports without a constraint field, but reject a legacy module
  when an exported declaration has non-empty universe constraints rather than
  erasing them.
- Carry the selected version through all later canonicalization, hashing,
  import, and result phases.

**Acceptance criteria:**

- Positive fixtures for all three supported pairs decode.
- Mixed-pair, unknown-version, truncated-constraint, unsorted-constraint, and
  duplicate-constraint fixtures reject with stable structured errors.
- Current and previous imported public signatures retain their constraint
  vectors exactly.
- The legacy constrained-public-export fixture rejects.
- No decoder branch infers a certificate version from payload shape after the
  header pair has been selected.

**Dependencies:** EXT-COMPAT-01.

### EXT-COMPAT-03: Complete Version-Aware Canonical Encoding Validation

**Purpose:** Enforce the full canonical-byte contract rather than only selected
table and export invariants.

**Work:**

- Implement a complete canonical encoder for each supported certificate
  version and compare its output byte-for-byte with the input.
- Canonicalize and validate the import table using the Rust/Core ordering key.
- Compute local declaration dependency depth and require declarations at each
  depth to be ordered by canonical declaration name.
- Enforce sorted, duplicate-free dependency and axiom vectors independently of
  later hash or axiom-report mismatches.
- Retain the existing name, level, term, normalization, reachability, and
  derived-export checks in the complete re-encoding path.
- Reject duplicate imports, declarations, generated names, and unreachable
  table entries at the phase where the core contract defines them.
- Keep version-specific absent/present fields exact so a legacy encoding cannot
  be accepted as a current encoding or vice versa.

**Acceptance criteria:**

- Every canonical conformance fixture re-encodes to identical bytes.
- Reordered imports, equal-depth declarations, dependency vectors, axiom
  vectors, exports, and DAG tables reject even when stored hashes are adjusted
  to be self-consistent with the mutated byte sequence.
- Forward local dependencies and incorrect dependency-depth placement reject.
- Non-minimal integers, trailing bytes, mixed version layout, duplicate keys,
  and unreachable nodes reject.
- Canonical rejection is deterministic across repeated executions.

**Dependencies:** EXT-COMPAT-02.

### EXT-COMPAT-04: Implement Versioned Hashes And Constraint-Committing Public Interfaces

**Purpose:** Produce the same identities as Core v0.2.0 and its two compatibility
paths.

**Work:**

- Select module export and module certificate hash domains from the decoded
  version.
- Implement current domains `NPA-MODULE-EXPORT-0.2.0` and
  `NPA-MODULE-CERT-0.2.0`.
- Implement previous domains `NPA-MODULE-EXPORT-0.1.2` and
  `NPA-MODULE-CERT-0.1.2`, while retaining exact legacy behavior.
- Include universe constraints in current/previous declaration interfaces,
  generated family/constructor/recursor interfaces, export entries, and public
  import environments.
- Use `NPA-UNIVERSE-CONSTRAINTS-0.1` exactly as specified for constraint
  commitment.
- Retain and cross-check the stable `NPA-LEVEL-0.1`, `NPA-TERM-0.1`,
  `NPA-CORE-EXPR-0.1`, and `NPA-AXIOM-REPORT-0.1` domains rather than changing
  them as a side effect of module-version support.
- Verify declaration body/type/interface/dependency hashes, derived export
  material, axiom-report hash, and certificate hash in a version-aware order.

**Acceptance criteria:**

- All cross-language hash goldens match byte-for-byte for all three versions.
- Changing an exported constraint changes the current/previous declaration
  interface hash and export hash.
- Changing an opaque theorem proof without changing its interface or axiom
  dependencies preserves the export hash and changes the certificate hash.
- A forged export constraint, generated artifact constraint, declaration hash,
  dependency hash, report hash, or certificate hash rejects with the expected
  stable classification.
- Legacy behavior is preserved only for valid unconstrained public exports.

**Dependencies:** EXT-COMPAT-03.

### EXT-COMPAT-05: Compose A Real Source-Free Semantic Module Check

**Purpose:** Replace the library stub with a single semantic pipeline that
cannot skip a required phase and that produces the only semantic capability
eligible to proceed to policy finalization.

**Work:**

- Replace `Ext_typecheck.check_certificate`’s stub with a typed check result, or
  introduce an equivalently central checker module and remove the stub API.
- Execute, in a fixed order, decode/structure, canonical bytes, declaration and
  module hashes, core-feature policy, import resolution/environment
  construction, declaration type checking, and axiom-report recomputation and
  comparison.
- Check declarations sequentially and publish local families, constructors,
  recursors, definitions, and theorems only after their required checks pass.
- Provide staged environment operations for atomic inductive installation;
  until EXT-COMPAT-07 lands, an unsupported mutual block must install nothing.
- Return a private `semantically_checked` value containing the decoded version,
  module name, certificate hash, export hash, axiom-report hash, declarations
  checked, and the data needed for later policy finalization.
- Preserve typed phase errors with the declaration/core path, section, offset,
  and expected/actual hash data needed by the raw-result mapping in
  EXT-COMPAT-10.
- Ensure malformed input and ordinary rejection never escape as an OCaml
  exception or host-specific message.
- Keep final axiom-policy acceptance and raw `checked` result construction out
  of this capability; those are added after EXT-COMPAT-09 supplies a complete
  import plan and EXT-COMPAT-10 processes that plan child-first.

**Acceptance criteria:**

- Valid current certificates containing axioms, definitions, theorems, and
  simple inductives reach a `semantically_checked` library result without
  source files.
- Exact Nat/Eq builtin fixtures resolve only at the specified names,
  interfaces, universe arities, and hashes.
- Universe constraints are used for well-formedness and entailment obligations
  but never to make two levels definitionally equal.
- One negative fixture from every completed phase reaches the intended typed
  phase error.
- Removing or bypassing any phase causes a test failure.
- A failed declaration leaves no generated or local signature visible to the
  next declaration.
- A `semantically_checked` value cannot be constructed directly from decoded
  or merely hash-checked certificate data, and cannot itself be registered as
  final high-trust evidence.
- The `Type_check_not_implemented` result and all equivalent skeleton-only
  library paths are gone.

**Dependencies:** EXT-COMPAT-04.

### EXT-COMPAT-06: Generalize Inductive Checking To Indexed Families

**Purpose:** Support the indexed inductive and recursor behavior required by
Core v0.2.0.

**Work:**

- Validate constructor results as `I params index_args`, including exact
  universe arguments, uniform parameters, index arity, and scope.
- Generalize motive, minor-premise, major-premise, and result construction to
  carry indices and dependent field substitutions.
- Require the major premise to be the final recursor binder.
- Generate recursive induction hypotheses at the correctly substituted motive
  and index arguments.
- Implement indexed iota reduction after weak-head reduction of the major
  premise.
- Preserve the syntactic-Prop motive restriction and the constructor-field
  universe bound for index-determining and dependent fields.
- Remove `unsupported_declaration` branches whose only cause is a non-empty
  index list.

**Acceptance criteria:**

- Canonical `Vec`- and `Fin`-style fixtures check and their recursor reductions
  agree with the kernel and reference checker.
- Wrong result indices, wrong parameter prefixes, wrong universe arguments,
  misplaced major premises, malformed motives/minors, and incorrect recursive
  induction-hypothesis indices reject.
- Indexed Prop families cannot eliminate into Type.
- Indexed constructor universe-bound failures retain
  `constructor_universe_bound_violation`.

**Dependencies:** EXT-COMPAT-05.

### EXT-COMPAT-07: Implement Mutual Inductive Blocks Atomically

**Purpose:** Check the full mutual block against a shared provisional
environment and publish it only after all members succeed.

**Work:**

- Replace the mutual-block `unsupported_declaration` path and the
  `Ext_inductive.check_block` stub.
- Validate block and member uniqueness, family shapes, constructors, generated
  artifacts, and cross-family references against the whole provisional block.
- Check every non-parameter field against its target member’s family sort using
  the block’s shared universe context.
- Implement direct mutual positivity and route recursive induction hypotheses
  to the matching family motive.
- Check mutual recursor types and implement cross-family iota routing.
- Commit all family, constructor, and recursor signatures atomically only after
  the entire block succeeds.

**Acceptance criteria:**

- Positive direct-mutual and indexed-mutual fixtures check and reduce exactly
  like the kernel/reference checker.
- A constructor universe violation in any member rejects the complete block.
- Negative cross-family occurrence, malformed member recursor, duplicate
  generated name, wrong family target, and wrong universe/context fixtures
  reject deterministically.
- A declaration after a failed block cannot resolve any block artifact.
- No mutual fixture is accepted by treating members as independent single
  inductives.

**Dependencies:** EXT-COMPAT-06.

### EXT-COMPAT-08: Implement Exact Approved Nested Positivity And Iota

**Purpose:** Match the Core v0.2.0 nested-recursion policy without expanding the
trusted language by name matching or alias unfolding.

**Work:**

- Recognize approved List, Option, and Prod functors by their exact structural
  public interfaces, including universe parameters, constraints, constructors,
  and canonical hashes required by the Rust rule.
- Track polarity through function domains/codomains and approved positive
  functor arguments for single and mutual families.
- Reject unknown functors, name-only lookalikes, unsupported aliases,
  higher-order negative occurrences, and recursive occurrences in negative
  positions.
- Construct the exact nested recursive induction-hypothesis terms required by
  generated recursors.
- Extend iota reduction for approved nested fields and mutual nested routing,
  using deterministic fuel accounting.

**Acceptance criteria:**

- Positive List-, Option-, Prod-, and mutual-nested fixtures agree with both
  Rust checkers on checking and representative iota reductions.
- Fake approved names with different interfaces reject.
- Recursive occurrences under unapproved wrappers or aliases reject.
- Negative nested and higher-order negative fixtures reject as
  `positivity_failure` with stable reason codes.
- Adding nested support does not make a previously rejected unapproved shape
  valid.

**Dependencies:** EXT-COMPAT-07.

### EXT-COMPAT-09: Build Normal Imports And A Deterministic Import-DAG Plan

**Purpose:** Preserve normal-mode semantics and prepare a closed, child-first
import plan without prematurely manufacturing high-trust evidence.

**Work:**

- Keep normal resolution limited to decoded, canonical, hash-checked
  source-free public environments, with optional requested certificate-hash
  matching as specified.
- Keep the `semantically_checked` capability from EXT-COMPAT-05 private and
  distinct from the final high-trust ledger entry introduced by
  EXT-COMPAT-10.
- Remove, privatize, or redesign `from_checked_modules` so arbitrary decoded
  module entries cannot be relabeled as externally checked.
- From the runner-provided import directory, construct the requested import
  closure, reject duplicate module identities and cycles, and produce one
  deterministic topological plan with every dependency before its consumer.
- Require every planned high-trust edge to include and match the exact
  certificate hash of the selected certificate bytes.
- Expose a child-first fold over the plan that EXT-COMPAT-10 can use to
  semantically check, apply policy to, and register one module before checking
  its consumers.
- Do not add filesystem discovery outside the explicit import directory and do
  not read package indexes or source files.

**Acceptance criteria:**

- Normal mode accepts the same decoded/hash-checked import cases as the Core
  specification, including a missing requested certificate hash.
- A focused boundary fixture demonstrates that a semantically unchecked import
  is never upgraded into high-trust evidence merely because its export hash
  matches.
- High-trust planning rejects missing certificate hashes, stale/replaced
  certificates, cycles, duplicates, ambiguous module identities, and missing
  transitive imports before checking the leaf.
- A valid multi-level DAG produces exactly one deterministic child-first plan.
- No public helper can create a final checked ledger entry from a bare decoded,
  hash-checked, or merely `semantically_checked` module.

**Dependencies:** EXT-COMPAT-04 through EXT-COMPAT-08.

### EXT-COMPAT-10: Finalize High-Trust Policy Sessions And Structured Raw Results

**Purpose:** Process the import plan child-first and convert each semantic
result into a final policy-checked session entry and runner-compatible raw
result.

**Work:**

- Accept exact policy bytes from the caller, parse the documented TOML schema,
  and map input errors to `policy_input_error` rather than
  `checker_internal_error`.
- Fold over the EXT-COMPAT-09 plan in deterministic topological order. For each
  module, resolve imports only from already policy-checked entries, run the
  semantic module check, apply the same parsed policy, and then register the
  result.
- Consume the core-feature result and recomputed direct/transitive
  per-declaration and module axiom sets from the semantic checks, including
  imports and generated artifacts.
- Require every stored report and report hash to have matched before applying
  policy.
- Enforce mandatory `deny_sorry`, custom-axiom allowlisting, and the exact
  built-in exception identities. The runner policy artifact contains exactly
  `format` and `allowed_axioms`; denial gates are not caller-overridable fields.
- Distinguish the internal `semantically_checked` capability from a final
  policy-checked verdict so no caller can render raw status `checked` before
  policy succeeds.
- Make the final high-trust ledger constructor private and accept only the
  policy-checked capability produced in this phase.
- Define one exhaustive mapping from typed phase and policy errors to raw-result
  kind, reason, declaration/core path, section, offset, and expected/actual
  hash fields.
- Produce checked raw results with module, certificate hash, export hash, and
  axiom-report hash.
- Include the raw-result schema, checker id, checker version, and build hash in
  both checked and failed results, using the same identity advertised by
  `--version` and pinned by the runner registry.
- Produce failed raw results with every field required by the Rust raw-result
  parser, including module and certificate hash for semantic/hash-aware error
  kinds when those values are available and required.
- Reject duplicate, unknown, null, or incorrectly typed result material in
  tests rather than relying on runner normalization to repair it.

**Acceptance criteria:**

- Checked and failed OCaml output parses through
  `parse_independent_checker_raw_result` without special cases.
- Raw identity fields match the resolved checker registry entry and the
  executable’s `--version` output.
- High-trust checking accepts a valid multi-level DAG and records exactly the
  policy-checked certificates processed in child-first order.
- High-trust checking rejects a semantic or policy failure in any imported
  certificate and never checks a consumer against a failed or merely semantic
  entry.
- Stored axiom-report mutations reject even when the policy would otherwise
  allow the recorded names.
- Imported forbidden axioms and transitive local forbidden axioms reject.
- Unsupported core-feature fixtures reject before a checked verdict.
- Valid allowlist, default denial, exact standard exceptions, and invalid TOML
  agree with the Rust runner/reference behavior.
- Repeated checks emit byte-identical raw JSON for the same inputs and build.

**Dependencies:** EXT-COMPAT-05 and EXT-COMPAT-09.

### EXT-COMPAT-11: Replace The Skeleton CLI And Close Resource Gaps

**Purpose:** Make the built executable implement the runner-owned command
contract safely and deterministically.

**Work:**

- Replace the complete-invocation skeleton branch with exact binary reads of
  `--cert`, recursive high-trust construction from `--import-dir`, exact policy
  byte loading, and the composed checker pipeline.
- Use the child-first policy-checked session path from EXT-COMPAT-10 for the
  standalone executable; no new `--trust-mode` flag is needed for the current
  runner contract.
- Preserve the current runner argument contract: `--cert`, `--import-dir`,
  `--policy`, `--policy-hash`, and `--output json`, plus `--version`.
- Reject `.npa` certificate/policy inputs and known source, tactic, replay, AI,
  package-index, and plugin inputs without following them. Open every path
  component relative to an already-open directory descriptor with no-follow
  semantics, and read candidates from the descriptors returned by traversal.
- Enforce deterministic maximum certificate depth, table entries, imports,
  universe-solver work, and semantic steps before host stack or allocation
  failure.
- Bound import-directory traversal identically at depth 128, 16,384 directory
  entries, and 4,096 candidate certificates, aborting traversal before an
  over-limit entry is retained or decoded.
- Bound every certificate read at 64 MiB and the complete retained import
  candidate byte set at 64 MiB. Check regular-file length before allocation and
  cap the actual read to the remaining budget plus one byte to close file-growth
  races.
- Make large table and term traversals stack-safe where the accepted limit
  would otherwise exceed the OCaml runtime stack.
- Leave wall-clock timeout and process memory enforcement to the runner and do
  not emit forbidden raw error kinds `timeout` or `resource_exhausted`.
- Emit raw JSON only on stdout, deterministic human diagnostics only on stderr,
  and the documented exit status for checker verdicts versus CLI misuse.
- Update `--version` and checker build identity so the advertised formats and
  core specification match the implementation.

**Acceptance criteria:**

- A valid current leaf and import DAG receive a checked executable result.
- Each supported version receives the intended verdict through the executable,
  not just a unit API.
- Missing files, wrong extensions, malformed policy, malformed certificates,
  semantic rejection, internal failure, and CLI misuse have stable distinct
  behavior.
- Boundary and over-limit fixtures terminate deterministically without uncaught
  exceptions or backtraces in proof evidence.
- Filesystem tracing or an equivalent test proves that a successful check reads
  only the certificate, explicit import certificates, policy, executable, and
  required runtime libraries.
- The old `skeleton` result and legacy-only advertised identity are absent.

**Dependencies:** EXT-COMPAT-02 through EXT-COMPAT-10.

### EXT-COMPAT-12: Make Differential And Package Gates The Release Authority

**Purpose:** Prevent compatibility regressions and only then promote the OCaml
checker to release/high-trust evidence.

**Work:**

- Run the complete conformance and mutation corpus through the fast kernel,
  `npa-checker-ref`, and the built OCaml executable.
- Require agreement on verdict, module identity, certificate/export/report
  hashes, and stable normalized failure classification.
- Exercise `npa package verify-certs --checker external` with a real registered
  OCaml binary rather than a scripted checked-result fixture.
- Exercise a multi-package recursive import DAG, import replacement/hash
  attacks, forbidden axioms, current constraints, indexed/mutual/nested
  inductives, and constructor-universe attacks.
- Pin the final checker binary id, binary hash, checker id, version, and build
  hash in runner policy/registry fixtures.
- Add the OCaml suite, differential corpus, external package check, and resource
  boundaries to the appropriate CI/release gates.
- Update `checkers/npa-checker-ext/README.md` and
  `npa-checker-ext-ocaml.md` only after all acceptance criteria pass; remove
  target/skeleton caveats only when the corresponding release gate is live.

**Acceptance criteria:**

- The known-gap manifest introduced by EXT-COMPAT-01 is empty.
- No valid Core v0.2.0 supported shape returns `unsupported_declaration` or a
  skeleton/internal placeholder.
- The full positive corpus agrees across all three implementations.
- Every mutation is rejected by all required checkers, with no unexpected
  acceptance in high-trust mode.
- The external package workflow produces runner-owned checked and normalized
  artifacts whose hashes and checker identity are verified.
- Missing, stale, or identity-mismatched OCaml binaries cannot produce
  `verified_high_trust`.
- Documentation and `--version` describe exactly the gated implementation.

**Dependencies:** EXT-COMPAT-01 through EXT-COMPAT-11.

## Dependency And Delivery Order

| Milestone | Tasks | Exit condition |
| --- | --- | --- |
| A. Compatibility oracle and wire identity | 01-04 | All versions decode, canonicalize, and hash exactly like Core v0.2.0, while known semantic gaps remain explicit. |
| B. Complete semantic checker | 05-08 | Every declaration and inductive shape in the active core profile has a real OCaml verdict. |
| C. Trust and executable boundary | 09-11 | Import evidence, policy, results, resources, and the runner CLI are end-to-end and source-free. |
| D. Release promotion | 12 | Differential and package gates pass with no known gaps; documentation may promote the checker. |

Tasks 03 and 04 should remain sequential because hash correctness depends on
the exact versioned canonical representation. Tasks 06 through 08 should also
remain sequential: indexed recursor generalization is the base for mutual
routing, and the mutual representation must exist before mutual nested
recursion can be implemented correctly. Normal import resolution and policy
rendering primitives may be developed in parallel after task 05, but final
high-trust registration in task 10 depends on task 09’s closed child-first
import plan.

## Definition Of Full Compatibility

The audit can be closed only when all of the following are true:

- the OCaml executable checks, rather than merely decodes, the current
  certificate supplied by the runner;
- current `0.2.0`, previous `0.1.2`, and legacy `0.1` compatibility behavior is
  exact;
- canonical bytes and all versioned hashes agree with the normative Rust
  implementation;
- universe constraints survive every current/previous local and imported
  public interface;
- simple, indexed, mutual, and exact approved nested inductives check and reduce
  correctly, including Prop and constructor-universe restrictions;
- normal imports remain normal, while high-trust imports are recursively
  checked with exact certificate identities in the current OCaml session;
- axiom reports, feature policy, and axiom policy are recomputed and enforced;
- raw output is accepted without repair by the runner contract;
- deterministic resource boundaries and source-free filesystem behavior are
  tested; and
- the full differential and real package gates have no known compatibility
  exceptions.

## Non-Goals

This compatibility plan does not add language features excluded by Core
v0.2.0. In particular, it does not add generic coinductives, arbitrary nested
functors, Prop-to-Type singleton elimination, universe constraints as
definitional-equality assumptions, source parsing, tactic replay, AI evidence,
network lookup, package discovery, plugin loading, or checker-registry signing.
It also does not require generic `--imports-hash`; the dedicated
`npa-checker-ext` contract uses `--policy-hash` to bind the policy bytes parsed
by the checker.
