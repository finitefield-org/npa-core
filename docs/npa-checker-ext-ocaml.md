# OCaml clean-room npa-checker-ext specification

This document specifies the external checker `npa-checker-ext`, added as a
Phase 8 / CLR-08 **OCaml clean-room implementation**.

This document is both the implementation specification and the release-evidence
contract. `crates/npa-checker-ref` remains the source-free Rust reference
checker, while `checkers/npa-checker-ext/` contains the independent OCaml
implementation and its conformance gates. The standalone executable now checks
current v0.2.0, previous v0.1.2, and legacy v0.1 certificates end to end,
including indexed, mutual, and exact approved nested inductives, recursive
high-trust imports, axiom policy, and raw-result rendering.

`npa-checker-ext` counts as release / high-trust evidence only when the built
executable is resolved from a runner-owned checker registry and the runner
validates its policy, binary hash, checker identity, and build hash. The real
package gate in `scripts/differential.sh` exercises that contract; an unpinned
local build is still not release evidence by itself.

---

## 1. Decision

The initial implementation of `npa-checker-ext` is in OCaml. The OCaml project
lives in `checkers/npa-checker-ext/` inside `npa-core` and is not split into an
external repository. However, it is not treated as a Rust workspace crate, and
the clean-room boundary is maintained by not linking from the OCaml project to
`crates/*`.
SHA-256 uses the vendored implementation inside `npa-core`, not a pinned
external library. The first release has an empty supported core feature set,
and certificates that require any unsupported core feature are rejected with
`unsupported_core_feature`.
The first release does not require a cryptographic signature for the checker
identity manifest. Manifest hash pinning and checker binary hash pinning through
runner policy are required; signing, key rotation, and revocation are later
hardening scope.

```text
checker id:
  npa-checker-ext

implementation profile:
  ocaml-clean-room

input:
  canonical .npcert bytes
  explicit import certificate store
  axiom/checker policy

output:
  deterministic checker_raw_result JSON
```

### 1.1 Toolchain v0.7 host adapter

The implemented host compatibility combination is `npa-cli 0.7.x`,
`package_api::v1`, and `npa-checker-ext 0.2.0`. The checker continues to decode
current `NPA-CERT-0.2.0` / `NPA-Core-0.2.0`, previous v0.1.2, and legacy v0.1
certificate pairs. The host crate version does not change checker semantics,
raw-result v1 or machine-result v1. The current host emits command-result v0.3;
historical 0.3/0.4 hosts retain v0.1 and 0.5 hosts retain v0.2.

The Linux closure gate is
`checkers/npa-checker-ext/scripts/toolchain-v0.7.sh`. It runs the real checker
through the v1 facade and the exact direct checked external command with one
job, cache/memo off, canonical runner-policy identity, raw-byte-pinned policy
inputs, and immutable sealed execution. Its `--functional-only` form is a
dirty-tree developer gate and explicitly does not create release evidence.
The full form also creates disposable generated-artifact manifest v0.2 assets,
validates their bytes, and deletes them on exit.

The obsolete v0.3/v0.4 host scripts and their dedicated compatibility tests
have been removed. Their design records are historical context only and are
not supported operator contracts.

Ordinary external checked verification, a byte-validated v0.2 release envelope,
and `verified_high_trust` are distinct outcomes. The first two do not acquire
the separate release/challenge policy bundle required by the third. The host
may create only `generated/checker-imports/.../external/` and
`generated/checker-results/.../external/`; unsupported immutable staging fails
with `checker_binary_immutable_snapshot_unsupported` and cannot emit a checked
artifact.

Reasons for choosing OCaml:

- Pattern matching makes canonical AST / declaration / error classification compact.
- It separates implementation language, runtime, and dependency graph from the Rust fast kernel implementation.
- It remains easy to compare with the reference checker while not sharing Rust crates.
- It is easy to treat as an auditable external implementation before moving to a more formalized checker in the future.

---

## 2. Trust Boundary

`npa-checker-ext` may read only:

```text
- the canonical .npcert specified by --cert
- import certificate inputs explicitly provided by the runner through --import-dir or --imports
- the axiom/checker policy specified by --policy, bound to the runner's
  `--policy-hash`
- version / build identity embedded in the checker binary itself
```

It must not read:

```text
- .npa source
- replay.json
- meta.json
- tactic trace
- AI trace / prompt / sidecar
- theorem index
- package registry network data
- hidden package cache
- plugin output
- unchecked source-derived environment
```

The external checker must not re-elaborate source. The only acceptance basis is
the deterministic check result over canonical certificate bytes and explicit
import certificate bytes.

---

## 3. Clean-room Constraints

`npa-checker-ext` must not link to internal crates from the NPA Rust workspace.

Forbidden:

```text
- npa-kernel
- npa-cert
- npa-api
- npa-frontend
- npa-tactic
- port-like copies of Rust reference checker code
- reuse of the source parser / elaborator / tactic
```

Allowed:

```text
- docs/core-spec-v0.2.0.md
- public certificate and toolchain reference docs in docs/
- canonical certificate fixtures
- public CLI / JSON schema contract
- golden hash fixtures
- differential test result
```

Here, clean-room means "checking the same specification with a separate
implementation." Do not trace the function structure of the Rust
implementation; build from the public specification, canonical byte format, and
golden/mutation corpus.

---

## 4. CLI contract

target command:

```sh
npa-checker-ext \
  --cert path/to/module.npcert \
  --import-dir path/to/import-certs \
  --policy path/to/axiom-policy.toml \
  --policy-hash sha256:<64-lower-hex> \
  --output json
```

Requirements:

- Reject anything other than `--output json`.
- Reject input paths with the `.npa` extension.
- Require `--policy-hash` and compare it with the exact policy bytes before
  parsing or checking.
- Read `--cert` as the exact bytes of a single certificate file.
- Use only the import store explicitly provided by the runner for import resolution.
- Do not perform network access, package discovery, or registry lookup.
- Run in a deterministic environment equivalent to `LC_ALL=C.UTF-8`, `LANG=C.UTF-8`, `TZ=UTC`.
- Emit only raw result JSON on stdout.
- Use stderr only for human-facing diagnostics; do not treat it as proof evidence.
- Exit 0 only for `checked` (and `--version`), exit 1 for a structured checker
  rejection, and exit 2 for CLI misuse or a structured internal failure.

If `--imports` / `--imports-hash` are accepted in the future, their meaning
must match the Phase 8 runner contract. AI output or package metadata must not
select or override the checker executable.

---

## 5. Raw result JSON

`npa-checker-ext` outputs `npa.independent-checker.checker_raw_result.v1`.

checked result:

```json
{
  "schema": "npa.independent-checker.checker_raw_result.v1",
  "checker_id": "npa-checker-ext",
  "checker_version": "0.2.0",
  "checker_build_hash": "sha256:...",
  "status": "checked",
  "module": "Std.Nat.Basic",
  "certificate_hash": "sha256:...",
  "export_hash": "sha256:...",
  "axiom_report_hash": "sha256:..."
}
```

failed result:

```json
{
  "schema": "npa.independent-checker.checker_raw_result.v1",
  "checker_id": "npa-checker-ext",
  "checker_version": "0.2.0",
  "checker_build_hash": "sha256:...",
  "status": "failed",
  "module": "Std.Nat.Basic",
  "certificate_hash": "sha256:...",
  "error": {
    "kind": "type_mismatch",
    "section": "declarations",
    "offset": 123
  }
}
```

JSON is deterministic.

- Object key order is fixed.
- Integers use decimal canonical form.
- Hashes use lowercase `sha256:<64 hex>`.
- Do not output timestamps, host paths, absolute paths, or locale-dependent messages.
- Do not include human-readable error strings in raw result identity.

Error kinds follow the stable classifications handled by the Phase 8 raw result
normalizer.

```text
certificate_decode_error
noncanonical_encoding
declaration_hash_mismatch
dependency_hash_mismatch
export_hash_mismatch
axiom_report_mismatch
certificate_hash_mismatch
import_not_found
import_hash_mismatch
forbidden_axiom
type_mismatch
conversion_failure
universe_inconsistency
positivity_failure
inductive_invalid
unsupported_core_feature
unsupported_schema_version
checker_internal_error
```

Universe-context and constructor checks use these stable reason codes:

```text
noncanonical_universe_params
noncanonical_universe_constraints
duplicate_universe_constraint
unsupported_universe_constraint
unsatisfiable_universe_constraints
universe_constraint_violation
constructor_universe_bound_violation
```

The two `noncanonical_*` reasons have kind `noncanonical_encoding`; the other
five have kind `universe_inconsistency`.

---

## 6. Certificate decoding

The checker accepts only canonical binary `.npcert`.

Checked targets:

```text
- current header pair = NPA-CERT-0.2.0 / NPA-Core-0.2.0
- previous header pair = NPA-CERT-0.1.2 / NPA-Core-0.1.2
- legacy header pair = NPA-CERT-0.1 / NPA-Core-0.1
- module name grammar
- import table
- name table
- universe level table
- term table
- declaration table
- export block
- axiom report block
- stored module hashes
```

The decoder rejects:

```text
- empty input
- unknown tag
- invalid UTF-8
- non-canonical varint
- table order violation
- duplicate name / declaration / import binding
- dangling reference
- unused canonical table entry
- non-normalized level / term table entry
- trailing bytes
```

In the OCaml implementation, the decoded AST is stored as algebraic data types,
not strings. de Bruijn indexes, level expressions, global references, and
declaration payloads are all handled structurally. Before accepting module
decode, construct reachability roots from the header / imports / declarations /
export block / axiom report and structurally traverse terms / levels. If name /
level / term tables contain entries unreachable from roots, reject as
`noncanonical_encoding`. Level / term DAG order is checked using deterministic
order based on canonical payloads and domain-separated SHA-256 hashes. If bytes
remain after the stored module hash trailer, reject as `certificate_decode_error`.

---

## 7. Hash verification

`npa-checker-ext` does not trust stored hashes; it recomputes them from
certificate bytes. The canonical encoder for hash input uses only the checker
internal source-free decoded AST, and does not reference pretty printers, JSON
renderers, filesystem paths, source spans, or debug sidecars. Domain labels are
implemented as fixed strings that match Rust `npa-cert` byte-for-byte. Level /
term hash recomputation follows canonical table order, and child hashes are
obtained only from already resolved table entries.

Required recomputation:

```text
- level hash
- term hash
- declaration interface hash
- declaration certificate hash
- export hash
- axiom report hash
- module certificate hash
```

Hash domain separation must match the Rust implementation bit-for-bit. However,
the implementation does not call Rust crates; the OCaml side reconstructs the
canonical encoder and SHA-256 input.

The SHA-256 implementation uses the vendored implementation inside `npa-core`.
The implementation source, test vector fixtures, and how it is
reflected into the checker build hash are fixed by the OCaml project in
`checkers/npa-checker-ext/`.

```text
vendored implementation:
  small OCaml SHA-256 implementation
  no transitive runtime dependency
  standard SHA-256 test vectors required
  Rust sha2 differential fixtures required
```

The vendored SHA-256 source identity and build hash are fixed in the checker
identity manifest.

---

## 8. Import resolution

Import resolution uses only the explicit import store.

normal mode:

```text
- find an import whose requested module name and export_hash match
- if certificate_hash exists in the certificate, require it to match
- missing import / export hash mismatch is a deterministic error
```

high-trust mode:

```text
- require import certificate_hash
- check import certificate bytes with the external checker first
- do not treat unchecked source-free imports as high-trust imports
- check the import closure in topological order
```

The external checker must not search the filesystem to discover imports.
`--import-dir` is treated only as a source-free import store constructed by the
runner.

---

## 9. Type checking scope

The initial `npa-checker-ext` targets the same semantic scope as the
`npa-checker-ref` Phase 8 MVP.

Required:

```text
- sort / universe level validation
- Pi / Lam / App / Let
- local de Bruijn scope check
- builtin / imported / local global reference resolution
- axiom declaration check
- reducible definition check
- theorem proof type check
- declaration dependency check
- universe parameter arity check
- unresolved universe metavariable rejection
- canonical, duplicate-free, satisfiable universe-constraint contexts
- substituted public-signature constraint entailment
- obligation-only finite `max` support on the right-hand side
```

conversion:

```text
- alpha-equivalence through de Bruijn representation
- beta reduction
- delta reduction for reducible definitions only
- zeta reduction for let
- iota reduction for supported recursors
- opaque theorem unfolding forbidden
- deterministic fuel / step bound
```

inductive / recursor:

```text
- constructor result targets declared family
- every non-parameter constructor field in a non-Prop family inhabits a sort
  entailed to be at most the family sort
- uniform parameter-prefix exclusion and canonical Prop exemption
- conservative strict positivity check
- generated constructor / recursor interface validation
- recursor parameter / motive / major / minor / result shape validation
- malformed or unsupported inductive shape rejected with structured error
```

Core features unsupported by the initial implementation are rejected as
`unsupported_core_feature`. The first release supported core feature set is
empty. When adding feature gates, enable them only after adding a golden corpus
for all three of fast kernel, reference checker, and external checker.

In M0-05, the first-release supported core feature set is implemented as the
empty set. Therefore, when any unsupported feature appears in a canonical
certificate feature report, the external checker returns
`checker_raw.error.kind = unsupported_core_feature`. MVP certificates with empty
feature reports are not rejected by this gate. Feature policy input is only the
canonical certificate feature report; AI sidecars, package metadata, and
source-derived environments are not used for feature enablement. When a new core
feature is introduced, extend the fast kernel / reference checker / external
checker golden corpus at the same time before adding it to the supported set.

---

## 10. Axiom report and policy

The external checker recomputes the axiom report from the certificate.

Required:

```text
- direct axiom set for each declaration
- transitive axiom set for each declaration
- module-level transitive axiom set
- axiom dependencies from imports
- axiom dependencies in the export block
- axiom_report_hash
```

policy:

```text
- the policy TOML contains exactly `format` and `allowed_axioms`
- `format` is exactly `npa.independent-checker.axiom_policy.v1`
- missing, duplicate, legacy, or unknown policy fields are rejected
- deny_sorry and custom-axiom denial are mandatory high-trust gates, not caller overrides
- custom axioms are rejected unless they are on the exact allowlist
- the standard exception for Std.Logic.Eq.rec is allowed only by exact name/hash
- axiom policy parse errors are treated on the runner side as policy input errors, not checker_internal_error
```

The checker must not trust axiom descriptions or source spans. Decisions are
based on canonical names and `decl_interface_hash`.

---

## 11. Resource and determinism rules

`npa-checker-ext` has deterministic resource bounds.

```text
- certificate/policy file bytes: 64 MiB
- table/declaration/export/report vectors: 10,000 entries
- imports and import-directory certificate candidates: 4,096
- level/term depth: 1,024
- import-DAG depth: 1,024
- import-directory depth: 128
- decoded structural traversal: 5,000,000 nodes
- each conversion/typechecking fuel budget: 100,000 steps
```

The runner separately owns `max_memory_mb` and `timeout_ms`.

Timeout / resource exhaustion enforced by the runner is represented as
`timeout` / `resource_exhausted` in the runner-owned `MachineCheckResult`, not as
a checker raw result. When `npa-checker-ext` emits a raw result itself, it must
not put `resource_exhausted` or `timeout` in `checker_raw.error.kind`.
Deterministic decoder limits use reason `resource_limit` under the existing
`certificate_decode_error` kind. Fuel failure inside the semantic checker is
classified as `conversion_failure` or the applicable typed semantic error.
OCaml exception backtraces and host-specific messages are never included in raw
results.

Even when parallelized, result order is fixed to certificate order / import
topological order.

---

## 12. Implementation layout

Recommended module split:

```text
ext_cli.ml
  argv validation, file input, stdout JSON

ext_bytes.ml
  byte reader, canonical varint, offset tracking

ext_name.ml
  module/declaration name grammar

ext_level.ml
  universe level AST, normalization, hashing

ext_term.ml
  core term AST, de Bruijn utilities, hashing

ext_cert.ml
  certificate decoder, table validation, root reachability

ext_universe.ml
  canonical difference constraints, closure, substitution, and entailment

ext_hash.ml
  domain-separated SHA-256 input construction

ext_import.ml
  canonical import identity

ext_import_store.ml
  decoded/hash-checked public environments and normal import resolution

ext_axiom.ml
  axiom report recomputation and policy gates

ext_env.ml
  checked environment and public environment

ext_typecheck.ml
  inference, checking, definitional equality, and beta/delta/iota/zeta reduction

ext_inductive.ml
  positivity and recursor shape checks

ext_checker.ml / ext_checker.mli
  ordered semantic pipeline and abstract normal/high-trust capabilities

ext_session.ml
  deterministic child-first policy-checked import DAG

ext_result.ml
  deterministic checker_raw_result JSON
```

Dependencies between modules are one-directional.

```text
bytes/name/level/term
  -> cert/hash
  -> import/env
  -> reduce/typecheck/inductive/axiom
  -> cli/result
```

Design the system so that only `ext_cli` touches the filesystem.

---

## 13. Differential testing

Minimal test set:

```text
- valid golden certificates accepted by npa-checker-ref and npa-checker-ext
- malformed binary corpus rejected without crash
- hash mutation corpus rejected with matching stable error class
- ill-typed theorem proof rejected
- bad de Bruijn index rejected
- wrong universe arity rejected
- import export_hash mismatch rejected
- high-trust missing certificate_hash rejected
- forbidden custom axiom rejected
- synthetic sorry rejected
- unsupported core feature rejected
```

Comparison targets:

```text
fast-kernel:
  acceptance baseline for generated certificates

npa-checker-ref:
  source-free reference baseline

npa-checker-ext:
  clean-room external verdict
```

For release / high-trust, mismatches in checked / failed status, module name,
export_hash, certificate_hash, or axiom_report_hash are release blockers.
Natural-language error message equality is not required.

---

## 14. Completed milestones

M0: repository and build identity

```text
- OCaml project layout and build boundary
- in-repository OCaml project placement
- vendored OCaml SHA-256 implementation
- unsupported core feature rejected for first release
- checker_id = npa-checker-ext
- manifest hash pinning and checker binary hash pinning required
- checker identity manifest signature not required for first release
- deterministic --version / build hash
- --output json only
```

M1: source-free decoder

```text
- .npcert decode
- canonical table validation
- offset-preserving structured errors
```

M1-01 adds an immutable byte reader as the foundation for the decoder. At
construction time, the reader copies input bytes into an immutable string; read
operations return `(value, next_reader)` without mutating the reader. Every
decode error has a certificate section, byte offset, and reason code. Canonical
unsigned varints allow only minimal ULEB128 and reject unexpected EOF,
non-minimal encoding, u64 overflow, and host length overflow. This layer does
not reference the filesystem, source parser, or JSON rendering.

The original M1-02 slice decoded the legacy `NPA-CERT-0.1` /
`NPA-Core-0.1` header and the name grammar source-free. The completed
version-aware decoder now also accepts the current and previous header pairs
listed in Section 6. Module names and name table entries are stored as
structured component lists in `Ext_name.t`. Empty names, empty components,
dotted components, invalid UTF-8, and duplicate name table entries are rejected
as decode errors with reason codes.

M1-03 decodes `LevelTable` and `TermTable` source-free. Levels are stored as
OCaml algebraic data types `Zero` / `Succ` / `Max` / `Imax` / `Param`, and terms
as `Sort` / `BVar` / `Const` / `App` / `Lam` / `Pi` / `Let`, then passed to later
checkers without returning to source text. Level children and term children
follow table topological order and can reference only earlier entries. Universe
level references in `Sort` and `Const`, plus name references in `Param` and
global references, are rejected as `dangling_reference` if they do not exist in
the relevant table. Unknown tags become deterministic errors with section and
byte offset. Level entries that change after normalization, such as
`Max Zero u`, duplicate term entries, and unresolved universe metavariable names
containing `?` are rejected before semantic trust.

M1-04 decodes the remaining top-level sections after the header source-free:
imports, declarations, export block, axiom report, optional core feature report,
and module hash trailer. Declaration payloads are kept as structured OCaml
values for axiom / definition / theorem / inductive / constrained variants /
mutual inductive block. Dependency entries and axiom references are decoded
while preserving the structure of `GlobalRef`, canonical names, and hash bytes.
Export entries keep name, kind, universe params, type, optional body, type/body
hash, optional reducibility/opacity, interface hash, and axiom dependencies.
Because this legacy export layout cannot carry declaration universe
constraints, public-environment construction rejects an export owned by a
constrained declaration with kind `unsupported_schema_version`, reason
`constrained_export_requires_format_upgrade`, and section `export_block`.
Unconstrained exports carry an explicitly empty signature-constraint vector.
Duplicate declaration names, dangling term references in the export block, and
dangling local declaration references in export axiom dependencies become
deterministic decode errors. However, declaration count mismatches in the axiom
report are not rejected in M1-04; they remain as preserved state in the decoded
value and are passed to axiom-report validation in M1-05 and later.

M2: hash verifier

```text
- declaration/export/axiom/certificate hash recomputation
- golden hash parity with npa-checker-ref
```

M3: import store

```text
- normal import resolution
- high-trust import certificate hash policy
- topological import checking harness
```

M4: minimal type checker

```text
- sort/Pi/Lam/App/Let
- local/imported/global references
- theorem and definition check
```

M5: conversion

```text
- beta/delta/iota/zeta
- opaque theorem unfolding boundary
- deterministic fuel
```

M6: inductive / recursor

```text
- conservative direct and exact approved nested positivity
- simple, indexed, and mutual inductive declarations
- generated constructor and recursor checks with indexed/mutual iota routing
- constructor-field universe bound with explicit declaration constraints
- canonical Prop exception and atomic mutual-block installation
```

M7: axiom report / policy

```text
- axiom report recomputation
- deny_sorry
- allowed axioms
- exact Std.Logic.Eq.rec exception
```

M8: runner integration

```text
- CheckerBinaryRegistry identity
- MachineCheckResult adoption
- normalized comparison with fast/reference/external
```

M9: release gate

```text
- npa package verify-certs --checker external
- release/high-trust comparison gate
- benchmark and audit bundle collection
```

---

## 15. Acceptance criteria

Conditions for using `npa-checker-ext` as the release / high-trust external
checker:

```text
- tests fix that source, tactics, replay, and AI traces are not read
- valid Phase 8 MVP certificate corpus is accepted without source
- required mutation corpus is rejected with deterministic structured errors
- checked module identity matches npa-checker-ref
- high-trust import closure can be constructed from external checker results
- forbidden axioms / sorry can be rejected by policy
- checker binary hash and identity manifest are pinned by runner policy
- first-release pass/fail is defined even without a checker identity manifest signature
- missing external checker does not generate a verified_high_trust artifact
```

These conditions are exercised by `scripts/test.sh` and
`scripts/differential.sh`. Whether external-checker evidence is required for a
particular release remains an explicit runner/release-policy decision; it is
never inferred from an unpinned local executable.

---

## 16. Directory decision and open decisions

M0-01 fixes the OCaml project directory as follows.

```text
OCaml project directory:
  checkers/npa-checker-ext/

Rust workspace membership:
  not a Cargo workspace member
  do not add this path to Cargo.toml workspace.members
  do not link from the OCaml project to crates/*
```

The project layout from M0-02 onward uses the following subdirectories under
this directory.

```text
checkers/npa-checker-ext/src/
checkers/npa-checker-ext/test/fixtures/
checkers/npa-checker-ext/test/golden/
checkers/npa-checker-ext/scripts/
```

M0-02 fixed the project build / test commands as follows.

```sh
checkers/npa-checker-ext/scripts/build.sh
checkers/npa-checker-ext/_build/npa-checker-ext --version
checkers/npa-checker-ext/scripts/test.sh
```

M0-03 fixes the vendored SHA-256 layout and test command as follows.

```text
implementation:
  checkers/npa-checker-ext/src/ext_sha256.ml

adapter:
  checkers/npa-checker-ext/src/ext_hash.ml

fixtures:
  checkers/npa-checker-ext/test/golden/sha256_vectors.tsv

test:
  checkers/npa-checker-ext/scripts/test.sh sha256
```

`Ext_sha256.source_identity` is included in checker build hash material. Whole
source file hash pinning is handled by checker binary hash / manifest hash
pinning in runner policy.

M0-04 fixes the first-release CLI boundary and build identity material as
follows.

```text
accepted CLI:
  --cert path
  --import-dir path
  --policy path
  --policy-hash sha256:<64-lower-hex>
  --output json
  --version

--version:
  must be used alone
  prints nine ordered lines covering checker_id/checker_version,
  checker_build_hash, certificate_format, core_spec, implementation_profile,
  project_directory, feature_policy_contract,
  vendored_sha256_source_identity, and
  checker_identity_manifest_signature_required

checker_build_hash material:
  checker_id
  checker_version
  certificate_format
  core_spec
  implementation_profile
  project_directory
  CLI contract version
  feature policy contract version
  vendored SHA-256 source identity
```

In the first release, the checker identity manifest signature is not included in
required identity material, and version output fixes
`checker_identity_manifest_signature_required false`.

M0-05 fixes first-release feature policy as follows.

```text
supported_core_features:
  []

rejected unsupported feature examples:
  unsupported_feature_a
  unsupported_feature_b
  unsupported_feature_c

error kind:
  unsupported_core_feature

policy input:
  canonical certificate feature report only

build identity material:
  feature_policy_contract = m0-05:first-release-empty-core-feature-set
```

This placement keeps the clean-room boundary narrow. The OCaml project may use
public specifications, canonical certificate fixtures, JSON schema contracts,
and differential test results from the same repository as inputs, but it must
not reference Rust workspace crates as build dependencies.

Open decision:

```text
- which of Lean / Rocq / NPA itself to prioritize when moving toward a verified checker
```

These are not decisions that expand the trust boundary of `npa-checker-ext`.
When decided, update Phase 8 / CLR-08 docs and runner policy tests.
