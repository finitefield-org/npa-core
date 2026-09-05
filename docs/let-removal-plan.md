# Term-Level `let` Removal Design

Status: implementation in progress. The design was planned on 2026-09-04
against container commit `1ad3ae0f0971046935f78a467ca1998f866fe64c`.
Milestone 0 was completed against the refreshed final let-capable checkpoint
`5d22858ffed16d75bcf01a61381abdb4040ae275`; its untrusted baseline evidence
is recorded in [let-removal-milestone-0/](let-removal-milestone-0/).
Milestone 1 froze the self-contained
[v0.4 core specification](core-spec-v0.4.0.md), reviewed canonical-identity
ledger, shared fixture matrix, and temporary migration/deletion records in
[let-removal-milestone-1/](let-removal-milestone-1/). Milestones 2 and 3
removed let from producers and the Rust core and established the strict v0.4
format. Milestone 4 restored clean-room OCaml parity. Public API/sidecar,
package-ecosystem, and final release cleanup work remains in Milestones 5–7.

## Executive Decision

NPA will remove term-level `let` completely from the current language and
trusted implementation. The completed system will have no accepted `let`
syntax, no `Let` node in source or proof intermediate representations, no
`Expr::Let` in the Rust kernel, no local-definition entries in kernel contexts,
no zeta-reduction rule, no `TermNode::Let` or encodable term tag `0x06`, and no
`Let` case in either independent checker.

This is an intentionally breaking core transition. The first let-free release
will emit and accept only:

```text
NPA-CERT-0.4.0
NPA-Core-0.4.0
```

This migration has exactly one supported source and destination:

```text
npa-cli 0.8.0 + NPA-CERT-0.3.0 / NPA-Core-0.3.0
    -> npa-cli 0.9.0 + NPA-CERT-0.4.0 / NPA-Core-0.4.0
```

`npa-cli 0.7.0` is neither a migration input nor a compatibility target. Its
unused repository remnants are deleted as part of this work; they are not
carried into the 0.9.0 toolchain.

The 0.9.0 binary will not retain v0.3.0, v0.2.0, v0.1.2, or v0.1 certificate
decoders. The v0.8.0 toolchain is a temporary migration checkpoint, not a
permanent compatibility release. Before changing the format, the migration
records its exact source commit, tree identity, build inputs, checker
identities, and checksums; a clean detached checkout of that commit is then
used once to inventory and verify the v0.3 baseline. Do not create a new
long-lived `v0.8.0` tag, hosted release, or reusable release asset for this
purpose. If any such tag, release, or asset already exists, inventory its exact
identity for later deletion.

After the baseline evidence is captured and the v0.9.0 replacements pass their
targeted checks, remove the v0.8.0 executable toolchain, compatibility branches,
reference document, examples, tests, fixtures, scripts, and live links from the
v0.9.0 release candidate. After the complete v0.9.0 package closure and all
independent release gates pass, publish and verify v0.9.0, then delete the exact
standalone v0.7.0 and v0.8.0 local/remote tags and matching hosted
releases/assets if they exist. Historical v0.3 certificate/core specifications
and the recorded migration evidence may remain, but no retained released
toolchain will support or verify v0.3 certificates. Keeping either an old
semantic decoder in a current checker or a runnable v0.7/v0.8 toolchain lane in
the current checkout would preserve the term constructor and zeta rule as a
live compatibility path, which contradicts the requested terminal state.

The removal does **not** affect module-level `def` or `opaque def`. It also does
not remove lambda abstraction, application, the beta rule, global-definition
delta reduction, or the `have` and `suffices` tactics. Those constructs cover
the useful authoring cases without adding a separate core term.

## Meaning Of “Complete Removal”

In this design, complete removal is a semantic and implementation boundary,
not a ban on the English word “let” or Rust's own `let` statement. Completion
requires all of the following:

- Human Surface and Machine Surface reject term-level `let`.
- Refine terms, proof skeletons, serialized AI state, and generated terms
  cannot represent it under a different internal name.
- The Rust kernel has assumption-only local contexts and no zeta path.
- Current canonical certificates have six term forms: `Sort`, `BVar`, `Const`,
  `App`, `Lam`, and `Pi`.
- The fast verifier, independent Rust checker, and clean-room OCaml checker
  accept only the let-free current pair.
- Current diagnostics and performance output do not report zeta work.
- Current live source, accepted package source, positive fixtures, and generated
  certificates contain no term-level let. Rejection-only fixtures may contain
  former source or certificate encodings only when they are excluded from every
  accepted package manifest/build selection and deterministically fail.

The following historical material may still contain the term-level syntax
spelling because it does not implement or accept the feature:

- version-scoped v0.3.0 and older certificate/core specification documents;
- release notes describing the migration;
- negative tests asserting that former syntax and retired bytes are rejected;
- historical release-manifest readers that treat old diagnostic JSON only as
  untrusted archival data and do not recognize a retired CLI host as supported.

This historical exception does not protect obsolete 0.7.0 or 0.8.0
CLI/toolchain references, gates, examples, schemas, host-version validator
branches, or runnable instructions. Those compatibility remnants must be
removed. Except for this design and the v0.9.0 release note that records the
migration and deletion, completed design chronology that needs to mention an
older host must use version-neutral wording rather than preserve a live-looking
identifier or link. A version number belonging to a different axis, such as
`npa.performance.measurements.v0.7`, `npa.performance.measurements.v0.8`, or a
third-party dependency at 0.7.x or 0.8.x, is not a CLI/toolchain remnant merely
because the digits coincide.

A lexer error that says “term-level `let` has been removed” is also permitted.
It is a rejection-only diagnostic, not a parser production, AST node, lowering
rule, or compatibility path.

## Motivation And Baseline Evidence

Term-level `let` currently duplicates expressivity already available through
substitution, lambda/application, named module declarations, and local proof
lemmas. Its implementation cost is disproportionately broad because it crosses
every trusted and untrusted representation.

The baseline inventory at the commit above found:

| Item | Baseline |
|---|---:|
| Tracked `.npa` source files | 8,216 |
| `.npa` files containing the accepted typed `let ... := ... in ...` shape | 6 |
| Typed source occurrences | 12 |
| `npa-core` Rust files containing known semantic `Let` cases | 46 |
| Rust consumer files outside `npa-core` containing known semantic `Let` cases | 4 |
| OCaml checker files containing semantic `Let` or term-tag handling | 7 |
| Files containing current zeta counters or reduction-profile identifiers | 16 |

These counts are tied to the stated baseline commit. They were produced with
the following tracked-file inventory; Milestone 0 must rerun the same commands,
save every matching path rather than only the counts, and then supplement the
text results with decoded-certificate inspection:

```sh
base_commit=1ad3ae0f0971046935f78a467ca1998f866fe64c
let_source_pattern='let[[:space:]]+[A-Za-z_][A-Za-z0-9_]*[[:space:]]*:[^:=]+:=[^[:cntrl:]]*[[:space:]]in([[:space:]]|$)'
semantic_let_pattern='Expr::Let|TermNode::Let|CanonTerm::Let|MachineTerm::Let|HumanExpr::Let|ProofExpr::Let|ProofSkeletonTerm::Let|RefineTermAstKind::Let|ReferenceCoreExpr::Let|OwnerAwareExpr::Let|LeanExprNode::Let|enum LeanExprNode|KernelExprHead::Let|RewriteDiagnosticTargetKind::LocalValue|LetValue|LetType|LetBody'
ocaml_let_pattern='Ext_term\.Let|(byte|one_byte)[[:space:]]+0x06|[|][[:space:]]+0x06[[:space:]]+->'
/usr/bin/git ls-tree -r --name-only "$base_commit" | rg '\.npa$' | wc -l
/usr/bin/git grep -l -E "$let_source_pattern" "$base_commit" -- '*.npa'
/usr/bin/git grep -o -E "$let_source_pattern" "$base_commit" -- '*.npa' | wc -l
/usr/bin/git grep -l -E "$semantic_let_pattern" "$base_commit" -- 'npa-core/*.rs' 'npa-core/**/*.rs'
/usr/bin/git grep -l -E "$semantic_let_pattern" "$base_commit" -- '*.rs' ':(exclude)npa-core/**'
/usr/bin/git grep -l -E "$ocaml_let_pattern" "$base_commit" -- 'npa-core/checkers/npa-checker-ext/*.ml' 'npa-core/checkers/npa-checker-ext/*.mli'
/usr/bin/git grep -l -E 'zeta_steps|beta-delta-iota-zeta\.v0\.1' "$base_commit"
```

The four out-of-core Rust consumers are the exporter files `ir.rs`, `lower.rs`,
`render.rs`, and `resource.rs` under
`npa-lean-exporter/crates/npa-lean-exporter/src/`. The typed-source regular
expression is only an inventory aid for the known old spelling; it is not a
replacement for lexer/parser rejection tests or decoded term-table inspection.
A broader OCaml search for the bare substring `0x06` also matches the unrelated
SHA-256 constant `0x06ca6351l` in `ext_sha256.ml`; it is a reviewed false
positive, not an eighth let implementation file.

All 12 source occurrences are two reduction examples copied across the live
Mathlib/corpus modules and four compact fixtures:

- `npa-mathlib/Mathlib/Core/Reduction/source.npa`;
- `npa-corpus/proofs/Proofs/Ai/Reduction/source.npa`;
- the `npa-mathlib` and `npa-mathlib-seed` fixtures in `npa-core/testdata`;
- the matching two fixtures in `npa-corpus/fixtures`.

The exported declarations are named `let_identity_nat` or `let_id_nat` and
`let_const_nat`. A source-level dependency search found no mathematical client;
the remaining references are manifest export lists, metadata, replay records,
promotion/catalog history, generated artifacts, and fixture assertions. The
implementation phase must repeat both the source search and a decoded
certificate inventory because source text alone cannot reveal `Let` nodes
created by tactics or lowering passes.

The baseline is evidence for planning, not an acceptance result. Counts must be
refreshed immediately before implementation because `origin/main` may gain new
source or generated artifacts.

The baseline is exactly `npa-cli 0.8.0` with the v0.3 certificate/core pair.
Milestone 0 pins it only long enough to inventory and verify the pre-removal
state from a clean detached checkout. No earlier CLI release is semantically
inspected, translated, or accepted as the baseline or proof of this transition.
The pinned commit and checksums are migration evidence, not a supported archive
or a reason to create a standalone release tag.

### Planning-Time 0.7.0 Toolchain Remnant Inventory

The implementation must refresh this inventory, but the planning-time scan
already identifies four tracked files that exist only for the unused 0.7.0
toolchain:

- `npa-core/docs/npa-toolchain-reference-v0.7.0.md`;
- `npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.7.sh`;
- `npa-core/crates/npa-cli/examples/verify_ext_v0_7_facade.rs`;
- `npa-core/crates/npa-cli/examples/inspect_ext_v0_7_policy.rs`.

The standalone `npa-core` `refs/tags/v0.7.0` ref and any matching hosted release
or release assets are also cleanup targets. Resolve their exact identities only
to make deletion auditable; do not treat their source or artifacts as a
migration baseline. Record them provisionally in the external-deletion ledger
during Milestone 0, re-resolve and freeze that ledger after the temporary
v0.8.0 checkpoint passes its clean-checkout verification, retain them until the
standalone v0.9.0 publication is independently verified, and then delete them
in the same post-publication cleanup as any v0.8.0 identities.

Delete those files. Also remove their embedded support from these shared files:

- `npa-core/crates/npa-cli/examples/inspect_ext_v0_3_policy.rs`;
- `npa-core/crates/npa-cli/src/checker_ext_toolchain_evidence.rs` and
  `npa-core/crates/npa-cli/tests/checker_ext_toolchain_evidence.rs`;
- `npa-core/crates/npa-cli/src/release_manifest.rs` and
  `npa-core/crates/npa-cli/tests/release_manifest_validator.rs`.

Milestone 5 already replaced the package-build cache regression and invalid
CLI fixture from this planning-time inventory with version-neutral stale-tool
and unsupported-host cases. They are no longer Milestone 7 deletion targets.

Remove every link, command, allowlist entry, and compatibility instruction that
refers to them across the root, `npa-core`, exporter, Mathlib, tracked `.agents`
guidance, and completed design documentation. Where a historical design needs
chronology to remain intelligible, use version-neutral wording such as “the
pre-0.8 host”; do not retain an executable 0.7.0 instruction or a link to a
deleted file.

Use both content and filename scans. At minimum, classify matches for
`v0.7.0`, `npa-cli 0.7`, `toolchain-v0.7`, `toolchain_v0_7`,
`HISTORICAL_V0_7`, `verify_ext_v0_7`, and `inspect_ext_v0_7`. The final tree may
retain those spellings only in this removal design, a release note recording
that cleanup, and explicitly version-scoped certificate/core specifications
whose normative history contains no live link, command, or claim that the
retired host remains currently supported. It must have no matching executable
code, test fixture, configuration, current documentation, or compatibility
branch. Separately classify measurement-schema and dependency-version matches
so the cleanup does not corrupt unrelated version axes.

### Planning-Time 0.8.0 Toolchain Remnant Inventory

The planning-time filename scan identifies four tracked files dedicated to the
current 0.8.0 toolchain:

- `npa-core/docs/npa-toolchain-reference-v0.8.0.md`;
- `npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.8.sh`;
- `npa-core/crates/npa-cli/examples/verify_ext_v0_8_facade.rs`; and
- `npa-core/crates/npa-cli/examples/inspect_ext_v0_8_policy.rs`.

These files are temporary migration inputs and final deletion targets. Their
shared support is spread across `npa-core` README and documentation indexes,
the checker README and OCaml runbook,
`inspect_ext_v0_3_policy.rs`,
`npa-checker-ext-toolchain-evidence.rs`,
`checker_ext_toolchain_evidence.rs` and its tests,
`release_manifest.rs` and its validator tests, package-API and build-cache
tests, repository compatibility scripts,
`.agents/skills/prove-theorem/SKILL.md`,
`.agents/skills/prove-theorem/references/kernel-fuel-debugging.md`, other agent
guidance, and completed design documents that link to the current v0.8
reference or gate. Refresh and save the full path inventory before editing;
this list is a minimum, not an allowlist.

The retained historical references
`npa-core/docs/npa-toolchain-reference-v0.5.0.md` and
`npa-core/docs/npa-toolchain-reference-v0.6.0.md` currently link forward to the
v0.8 reference and are therefore explicit shared-support edits: replace those
links with the self-contained v0.9 reference while preserving the documents'
release-scoped historical meaning. The corresponding pre-0.7 scripts and
references are not migration baselines or deletion targets of this plan. If
retained, they remain checkout-scoped historical snapshots rather than live
current-host lanes and must not advertise the deleted v0.8 reference as the
active contract.

The final cleanup must also query the standalone repository for the exact
`refs/tags/v0.8.0` local and remote refs and the release host for a matching
release and assets. Do not create any missing identity. If one exists, retain it
only through the v0.9.0 release verification gate, then delete that exact
identity and verify its absence. Any temporary source or binary bundle used for
Milestone 0 stays off live release surfaces and is deleted with the migration
workspace.

Use content and filename patterns at least for `v0.8.0`, `npa-cli 0.8`,
`toolchain-v0.8`, `toolchain_v0_8`, `HISTORICAL_V0_8`,
`verify_ext_v0_8`, and `inspect_ext_v0_8`. The final tree may retain those
CLI/toolchain spellings only in this removal design, the v0.9.0 release note
that records the completed transition, and explicitly version-scoped
certificate/core specifications whose normative history contains no live link,
command, or claim that the retired host remains currently supported. Classify
bare numeric `0.8` matches by version axis so performance schemas, protocol
revisions, and dependencies are not deleted accidentally.

## Goals

- Reduce the trusted core grammar and conversion relation.
- Make the current producer and all current checkers let-free by construction.
- Preserve useful proof-authoring workflows through direct terms,
  lambda/application, module declarations, `have`, and `suffices`.
- Keep the certificate transition explicit, versioned, deterministic, and
  fail-closed.
- Prevent a retired tag or old header from being reinterpreted as a v0.4 term.
- Refresh every affected certificate, hash pin, lock, metadata file, and
  downstream toolchain pin with repository writers rather than hand edits.
- Retain source-free, cache-disabled, independently checked proof acceptance.
- Remove stale zeta terminology from current APIs, profiles, diagnostics, and
  performance reports.
- Delete unused 0.7.0 toolchain files, identities, validator branches, tests,
  links, and compatibility instructions rather than preserving them as a
  second migration source.
- Use 0.8.0 only as a temporary, pinned migration checkpoint, then delete its
  executable toolchain, reference, compatibility identities, tests, live refs,
  releases, and assets after v0.9.0 is fully verified.
- Deliver an implementation sequence in which every temporary compatibility
  state is confined to the unmerged feature branch.

## Non-Goals

- Do not remove module-level definitions or their delta reduction.
- Do not remove `have`, `suffices`, `specialize`, lambda abstraction, or
  function application.
- Do not introduce a hidden `Bind`, `LocalValue`, macro, or certificate
  extension that is semantically the removed constructor under another name.
- Do not add Lean-style layout `let`, pattern bindings, recursive local
  definitions, or inferred let types before removal.
- Do not keep old certificate acceptance in a “legacy” branch of the current
  Rust or OCaml checkers.
- Do not perform a header-only migration of any certificate.
- Do not make source, a migration report, a replay file, or AI output part of
  the proof trust boundary.
- Do not decide whether unrelated language or tactic features should be
  removed. That requires a separate usage and cost audit.
- Do not rewrite historical certificate/core specifications as if their
  formats had never supported let. This does not preserve either the unused
  0.7.0 layer or the temporary 0.8.0 CLI/toolchain compatibility layer,
  documentation, runnable instructions, tags, or releases.
- Do not rewrite Git history merely to erase old version strings or commit
  objects. Removal means no current-tree implementation, live compatibility
  surface, named ref, hosted release, or asset; recorded object identities may
  remain as non-executable audit history.
- Do not add CI through GitHub Actions or Git LFS configuration.

## Terminology

This document uses these distinct terms:

- **term-level let**: the current `let name : Type := value in body` term.
- **local definition context**: a kernel or tactic context entry carrying both
  a type and a value and unfolded by local zeta reduction.
- **module definition**: a declaration introduced with `def` or `opaque def`.
  It remains supported.
- **zeta expansion**: capture-avoiding substitution of the bound value for the
  bound variable in the body.
- **zeta reduction**: a runtime conversion step that unfolds a `Let` node or a
  value-bearing local context entry. It is removed.
- **diagnostic tombstone**: recognition of the bytes `let` only to report that
  the syntax was removed. It never produces a term.

## Target Core Contract

### Term Grammar

The v0.4 core term grammar is exactly:

```text
e ::= Sort level
    | BVar index
    | Const global_ref levels
    | App e e
    | Lam e e
    | Pi e e
```

There is no value-bearing local binder. A local context is a sequence of typed
assumptions only. Type lookup still shifts a stored local type by the ordinary
de Bruijn distance, but context lookup never returns a value.

Definitional equality retains:

- beta reduction for applying a lambda;
- delta reduction for permitted global definitions;
- iota reduction for recursors;
- congruence, universe normalization, and the existing bounded conversion
  rules.

It removes both forms of zeta work:

1. reducing an explicit `Let` term; and
2. unfolding a bound variable from a value-bearing local context entry.

The current conversion-fuel limits remain unchanged initially. Performance
evidence, rather than intuition, decides whether the replacement of a small
number of zeta steps with beta steps justifies later retuning.

### Semantic Migration Rule

The semantics-preserving elimination of an already elaborated term is
capture-avoiding zeta expansion:

```text
let x : A := v in b    ==>    b[v / x]
```

That rule is for reasoning about migration, not a v0.4 parser or kernel rule.
It must be applied while the old representation is still available, followed
by ordinary v0.4 type checking and certificate construction.

The superficially similar expression below is not the universal migration
algorithm:

```text
(fun (x : A) => b) v
```

It is extensionally appropriate when `b` type-checks with `x` as an ordinary
assumption. An old let body, however, was checked in a context where `x` was
definitionally equal to `v`; blindly abstracting it can therefore lose a
conversion fact used while checking `b`. General automated migration must use
capture-avoiding substitution and then recheck the result.

The repository's 12 current source occurrences are confined to exported
`let_identity_nat` / `let_id_nat` and `let_const_nat` declarations that have no
mathematical clients. Delete those declarations from the Reduction modules and
positive fixtures rather than adding renamed `fun n => n` or direct `Nat.zero`
replacements. Existing direct and beta-reduction declarations already exercise
the retained term forms; the let-only names must not survive as misleading
examples.

### Authoring Replacements

| Former use | Let-free replacement |
|---|---|
| Short computational alias used once | Inline the value |
| Repeated closed expression in generated core | Share with `App(Lam(...), value)` when the lambda body type-checks under an assumption |
| Reusable mathematical construction | Give it a meaningfully named module-level `def` |
| Local proposition or intermediate proof | Use `have` or `suffices` |
| Local function | Apply an explicitly typed `fun` term |
| Expensive computation hidden for conversion | Prove a named theorem and use its opaque boundary; do not depend on large reduction |

`have` and `suffices` already construct a lambda whose body is the continuation
and apply it to the local lemma proof. They must remain supported and receive
regression tests proving that they emit no retired node. `specialize` uses the
same local-lemma skeleton for its `AddLocal` policy, which keeps the original
hypothesis; both `AddLocal` and `ReplaceOriginal` must receive the same
no-retired-node regression coverage.

### Equation Compiler Sharing

The Human equation compiler's `share_repeated_closed_result_terms` pass
currently introduces `Expr::let_in` to share a repeated closed result term.
Replace that exact lowering with:

```text
App(
  Lam(__eqc_shared_HASH, result_type, shared_body),
  candidate
)
```

The existing pass already shifts the body and replaces each matching closed
candidate with the new bound variable. The lowering API must make sharing
conditional on a kernel validation capability supplied with the real checked
environment, local binder context, and universe parameters. The validator must
check the candidate against `result_type`, then check the rewritten body with
the new binder as an ordinary assumption, before the transformed body is
committed. A caller that cannot supply that capability, or either failed check,
must receive the unmodified body. A test-only `verify_lowered_bundle` call or a
later certificate-build failure is not an implementation of this fallback, and
the fallback must not reintroduce a value-bearing context.

The current profitability formula charges one wrapper node for `Expr::Let`.
`App(Lam(...), candidate)` has two wrapper nodes, so the new logical-node cost
is:

```text
shared_nodes = 2 + result_type_nodes + candidate_nodes + occurrences
```

Update the selection threshold and `saved_nodes` calculation before enabling
the replacement. Add a boundary test whose old one-wrapper calculation would
share but whose two-wrapper calculation correctly declines, in addition to a
profitable checked-sharing case and each validation-failure fallback.

The canonical certificate term table is a hash-deduplicated DAG, so repeated
identical subterms remain physically shareable even when a source alias is
inlined. Benchmarks must compare unique certificate nodes, expanded-node
charges, elaboration allocations, beta steps, and total conversion fuel before
and after this lowering change.

## Surface Syntax And Diagnostics

Both Human and Machine Surface will remove:

- `Let` AST variants;
- parser productions and `parse_let` helpers;
- resolver scopes created specifically for let;
- elaborator cases and source-rendering cases;
- `TokenKind::Let` and `TokenKind::In`.

Each Human and Machine lexer will reject an identifier lexeme equal to `let`
with a stable source-located diagnostic whose reason code is
`removed_term_let`. Both frontend diagnostic enums gain a dedicated
`RemovedTermLet` variant; it replaces the obsolete Machine-only
`MachineDiagnosticKind::UnannotatedLet` instead of being collapsed into a
generic parse or unsupported-syntax diagnostic. The API adds
`MachineApiErrorKind::RemovedTermLet`, serialized as the exact
`removed_term_let` code and classified in the Machine-term parse phase; both
frontend-to-API mappings use it. Human LSP serialization independently maps the
new Human variant to the same exact code. This gives authors an actionable
failure without preserving an accepted token or parser path. The diagnostic
message must mention direct substitution, `fun`, `have`, and a named
module-level declaration as alternatives, without attempting to rewrite source
automatically.

The tombstone matches the complete identifier lexeme only. Identifiers such as
`letter`, comments containing `let`, and string-literal contents remain
unaffected; tests must distinguish all three from an actual `let` token. A
declaration or binder named exactly `let` is rejected by the same tombstone, so
there is no context in which the retired spelling silently becomes an ordinary
name.

The word `in` is used by no other current grammar production. It becomes an
ordinary identifier after `TokenKind::In` is removed. Tests must cover `in` in
every identifier position that the surfaces ordinarily permit and must prove
that former `let ... in ...` source still fails at `let` rather than being
partially reinterpreted.

`package check-source-structure` remains only a lexical/delimiter preflight. A
successful structure check must not be presented as evidence that source is
let-free; ordinary parse/elaboration and the dedicated negative tests enforce
that property.

## Certificate And Version Design

### Exact Version Policy

The current producer, fast verifier, reference checker, and OCaml checker will
recognize exactly one pair:

| Version | `format` | `core_spec` | Accepted term tags |
|---|---|---|---|
| `V0_4_0` | `NPA-CERT-0.4.0` | `NPA-Core-0.4.0` | `0x00` through `0x05` |

The header pair is validated before any version-owned body is decoded. All
mixed pairs and all older pairs fail at the header boundary. The independent
checkers retain their established distinction between format and core-spec
mismatch, but they do not retry another layout.

Dropping all older pairs, including a v0.3 certificate that happens not to use
tag `0x06`, is deliberate. A specialized compatibility decoder could in
principle accept the let-free subset of an old format while rejecting the
retired tag. This design rejects that alternative: it would preserve multiple
historical wire layouts, version branches, hash domains, and a subtle
“old-but-let-free” support promise in the current trusted checker. The chosen
boundary is one current grammar and one current pair. The pre-migration
v0.8.0 checkpoint supplies one-time historical verification evidence; after
the final cleanup, verification of v0.3 bytes is deliberately unsupported
rather than delegated to a retained released binary.

### Term Tags

The v0.4 canonical term table assigns:

```text
0x00  Sort
0x01  BVar
0x02  Const
0x03  App
0x04  Lam
0x05  Pi
```

Tag `0x06` is retired permanently. It is never reassigned. A v0.4 byte stream
containing `0x06` in a term-node position fails with the checker's ordinary
unsupported-encoding classification before structural or semantic use of its
three former child indexes.

The structural preflight, term arity logic, table dependency checks,
materialization planner, retained-byte accounting, declaration closure,
premise analysis, theorem graph, and all term walkers must have no three-child
let branch.

### Hash Domains

The versioned certificate domains change to:

```text
NPA-DECL-CERT-0.4.0
NPA-MODULE-CERT-0.4.0
```

The remaining term encodings are byte-identical, so these existing domains are
retained:

```text
NPA-TERM-0.1
NPA-CORE-EXPR-0.1
NPA-DECL-IFACE-0.1
NPA-MODULE-EXPORT-0.2.0
NPA-AXIOM-REPORT-0.1
NPA-LEVEL-0.1
NPA-UNIVERSE-CONSTRAINTS-0.1
```

Reusing the term domain is safe because v0.4 is a strict subset whose retained
node payloads have unchanged meanings, while retired tag `0x06` is rejected and
never reinterpreted. The new declaration-certificate domain prevents a current
declaration certificate from being confused with evidence checked under the
larger old core. The module header and new module-certificate domain ensure all
module certificate identities change.

Consequences that tests must pin:

- a let-free retained term has the same term hash before and after migration;
- a let-free public declaration interface can retain its interface hash;
- every module certificate hash changes;
- declaration-certificate hashes change under the new domain;
- modules whose public reduction examples are deleted receive new export
  hashes;
- no old certificate becomes valid by editing its header or hash fields.

### Package Profile Axes

The package manifest identifiers remain:

```text
npa.package.v0.1
npa.core.v0.1
npa.kernel.v0.1
npa.certificate.canonical.v0.1
npa.checker.reference.v0.1
npa.package.lock.v0.1
```

They are package-contract profiles, not aliases for the exact `NPA-Core-*` and
`NPA-CERT-*` pair. The current package format already records the exact decoded
pair in build-check caches, audit caches, and verified export summaries. Those
keys naturally miss after the pair changes. A separate package-schema project
may rename these axes later; coupling that migration to let removal would add
artifact churn without strengthening this boundary.

Mixed v0.3/v0.4 package closures are forbidden because the v0.4 checker does
not accept v0.3 imports. Every certificate in one verified closure must be
rebuilt under v0.4, even when its export hash remains stable.

## Public API, Sidecar, And Telemetry Changes

### Kernel And Certificate APIs

Remove these semantic shapes rather than deprecating them:

- `npa_kernel::Expr::Let` and `Expr::let_in`;
- `Ctx::push_definition`, `LocalDecl.value`, and `Ctx::lookup_value`;
- `KernelWorkCounter::ZetaStep`,
  `PerformanceMeasurementLabel::KernelZetaSteps`, and every `zeta_steps` field
  in current work summaries;
- `KernelExprHead::Let`, `RewriteDiagnosticTargetKind::LocalValue`, and the
  latter's `local_value` wire spelling;
- `npa_cert::TermNode::Let`;
- reference-checker and OCaml `Let` term variants;
- `CanonTerm::Let`, `ReferenceCoreExpr::Let`, `ProofSkeletonTerm::Let`,
  `ProofExpr::Let`, `RefineTermAstKind::Let`, and `OwnerAwareExpr::Let`;
- `VerifiedTheoremPremiseUseSite::LetValue` and
  `PackageTheoremPremiseUseSite::LetValue`;
- all advanced-AI expression path steps named `LetType`, `LetValue`, or
  `LetBody`;
- value fields from current frontend, tactic, prompt, hole-goal, LSP, and
  machine-local views. In particular, current `MachineLocalDecl`,
  `MachineLocalView`, `MachinePromptLocal`, `HumanHoleGoalLocal`, and
  `HumanLspHoleGoalLocal` become assumption-only shapes. Current
  `StructuredHypothesis` loses both `value` and the now-meaningless
  `is_local_def` discriminator while retaining ordinary hypothesis metadata;
- local-definition-only display and proof-generalization controls. Remove
  `HumanDisplayContextOptions.fold_local_def_values` and remove
  `ProofLocalStatementGeneralizationPolicy` entirely, including the policy
  argument to `generalize_local_context_statement`. Remove
  `ProofLocalStatementGeneralization.unfold_local_definitions` and
  `ProofLocalStatementGeneralizationBinder.value_hash`; and
- value slots from derived local-context artifacts, including
  `DiagnosticLocalSummary.value_hash`, `DiagnosticLocalSummary.value_summary`,
  `MinimalFailingArtifactLocal.value_hash`,
  `LemmaGeneralizationLocal.value_hash`, and
  `StatementNormalizationBinder.value_hash`. These fields are deleted rather
  than retained as permanent `None` values.

This is a semver-breaking Rust API change. The intended release family is:

| Component | Current | Let-free target |
|---|---:|---:|
| `npa-cli` | 0.8.0 | 0.9.0 |
| `npa-kernel` | 0.3.0 | 0.4.0 |
| `npa-cert` | 0.4.0 | 0.5.0 |
| `npa-package` | 0.3.0 | 0.4.0 |
| `npa-checker-ref` | 0.4.0 | 0.5.0 |
| `npa-frontend` | 0.4.0 | 0.5.0 |
| `npa-api` | 0.4.0 | 0.5.0 |
| `npa-tactic` | 0.2.0 | 0.3.0 |
| `npa-checker-ext` | 0.3.0 | 0.4.0 |
| `npa-lean-exporter` workspace | 0.2.0 | 0.3.0 |

These are fixed endpoints for this plan. If unrelated work advances any listed
component before implementation begins, rebase and re-review the plan rather
than silently substituting a different source or target version. Any replacement
plan must still apply the appropriate pre-1.0 minor bump for public breaking
changes.

### Proof State And Tactic Encodings

`ProofExpr::Let` and the `value` field on both
`npa_frontend::machine::MachineLocalDecl` and
`npa_tactic::MachineLocalDecl` must be removed. Both local-declaration shapes
become assumptions containing only `name` and `ty`. Refine syntax no longer has
an `infer_let` path. `have`, `suffices`, and `specialize` continue to construct
`App(Lam(...), proof)`.

Every canonical sidecar whose own payload grammar changes receives a new tag
and hash domain. Aggregates also advance when the let-free core changes the
semantic epoch represented by otherwise identical fields. The planning-time
minimum required mappings are:

| Payload | Current identity | Let-free identity |
|---|---|---|
| Human authoring ABI | `npa.frontend.human_authoring_interface_abi.v1` | `npa.frontend.human_authoring_interface_abi.v2` |
| Frontend Machine term source bytes | `npa.frontend.machine-term-source.v1` | `npa.frontend.machine-term-source.v2` |
| Refine term source bytes/hash | `npa.machine-tactic.refine-term-source.v1` / `npa.machine-tactic.refine-term-source.hash.v1` | `npa.machine-tactic.refine-term-source.v2` / `npa.machine-tactic.refine-term-source.hash.v2` |
| Machine term source bytes/hash | `npa.machine-tactic.machine-term-source.v1` / `npa.machine-tactic.machine-term-source.hash.v1` | `npa.machine-tactic.machine-term-source.v2` / `npa.machine-tactic.machine-term-source.hash.v2` |
| Proof expression bytes/hash | `npa.machine-tactic.proof-expr.v1` / `npa.machine-tactic.proof-expr.hash.v1` | `npa.machine-tactic.proof-expr.v2` / `npa.machine-tactic.proof-expr.hash.v2` |
| Machine local declaration bytes/hash | `npa.machine-tactic.machine-local-decl.v1` / `npa.machine-tactic.machine-local-decl.hash.v1` | `npa.machine-tactic.machine-local-decl.v2` / `npa.machine-tactic.machine-local-decl.hash.v2` |
| Machine local context bytes/hash | `npa.machine-tactic.machine-local-context.v1` / `npa.machine-tactic.machine-local-context.hash.v1` | `npa.machine-tactic.machine-local-context.v2` / `npa.machine-tactic.machine-local-context.hash.v2` |
| Diagnostic local-context summary bytes/hash | `npa.machine-tactic.diagnostic-local-context-summary.v1` / `npa.machine-tactic.diagnostic-local-context-summary.hash.v1` | `npa.machine-tactic.diagnostic-local-context-summary.v2` / `npa.machine-tactic.diagnostic-local-context-summary.hash.v2` |
| Machine API diagnostic canonical bytes/hash | `npa.machine-api.api-diagnostic.v1` | `npa.machine-api.api-diagnostic.v2` |
| Machine diagnostic tree schema/hash | `npa.machine-diagnostic-tree.v1` / `npa.machine-diagnostic-tree.v1` | `npa.machine-diagnostic-tree.v2` / `npa.machine-diagnostic-tree.v2` |
| Failure-memory key schema/hash | `npa.failure_memory.v1` / `npa.failure-memory.key-hash.v1` | `npa.failure_memory.v2` / `npa.failure-memory.key-hash.v2` |
| Hard-negative export schema/hash | `npa.hard_negative_export.v1` / `npa.machine-api.hard-negative-export.hash.v1` | `npa.hard_negative_export.v2` / `npa.machine-api.hard-negative-export.hash.v2` |
| Proof local-statement generalization hash | `npa.proof.local-statement-generalization.v1` | `npa.proof.local-statement-generalization.v2` |
| Proof skeleton API/hash domains | `npa.proof-skeleton.v1`, `npa.proof-skeleton.skeleton-hash.v1`, `npa.proof-skeleton.hole-hash.v1` | `npa.proof-skeleton.v2`, `npa.proof-skeleton.skeleton-hash.v2`, `npa.proof-skeleton.hole-hash.v2` |
| Proof-skeleton core-expression encoding/schema | `npa.core-expr.canonical-bytes.v0.1` / `npa.core-expr-artifact.v0.1` | `npa.core-expr.canonical-bytes.v0.2` / `npa.core-expr-artifact.v0.2` |
| Checked declaration signature bytes/hash | `npa.machine-tactic.checked-decl-signature.v1` / `npa.machine-tactic.checked-decl-signature.hash.v1` | `npa.machine-tactic.checked-decl-signature.v2` / `npa.machine-tactic.checked-decl-signature.hash.v2` |
| Current core declaration package | `npa.machine-api.current-core-decl-package.v1` | `npa.machine-api.current-core-decl-package.v2` |
| Current core declaration term table | `npa.machine-api.current-core-decl-package.term-table.v1` | `npa.machine-api.current-core-decl-package.term-table.v2` |
| Checked current declaration package / JSON encoding | `npa.machine-api.checked-current-decl-package.v6` / `npa.machine-api.checked-current-decl-package.canonical.v6.hex` | `npa.machine-api.checked-current-decl-package.v7` / `npa.machine-api.checked-current-decl-package.canonical.v7.hex` |
| Lean export profile / manifest | `npa.lean.native.v0.2` / `npa.lean.export.v0.2` | `npa.lean.native.v0.3` / `npa.lean.export.v0.3` |
| Machine proof delta hash | `npa.machine-tactic.machine-proof-delta.v1` | `npa.machine-tactic.machine-proof-delta.v2` |
| Machine proof state hash | `npa.machine-tactic.machine-proof-state.v1` | `npa.machine-tactic.machine-proof-state.v2` |
| Machine tactic environment hash | `npa.machine-tactic.machine-tactic-env.v2` | `npa.machine-tactic.machine-tactic-env.v3` |
| Kernel-check profile hash | `npa.machine-tactic.kernel-check-profile.v1` | `npa.machine-tactic.kernel-check-profile.v2` |
| Minimal failing artifact schema/hash | `npa.minimal_failing_artifact.v2` / `npa.machine-api.minimal-failing-artifact.hash.v2` | `npa.minimal_failing_artifact.v3` / `npa.machine-api.minimal-failing-artifact.hash.v3` |
| Focused replay failure artifact schema/hash | `npa.focused_replay_failure_artifact.v2` / `npa.machine-api.focused-replay-failure-artifact.hash.v2` | `npa.focused_replay_failure_artifact.v3` / `npa.machine-api.focused-replay-failure-artifact.hash.v3` |
| Lemma-generalization input profile/hash | `npa.library-growth.lemma-generalization-input.v1` / `npa.library-growth.lemma-generalization-input.hash.v1` | `npa.library-growth.lemma-generalization-input.v2` / `npa.library-growth.lemma-generalization-input.hash.v2` |
| Generalized-statement profile/hash | `npa.library-growth.generalized-statement.v1` / `npa.library-growth.generalized-statement.hash.v1` | `npa.library-growth.generalized-statement.v2` / `npa.library-growth.generalized-statement.hash.v2` |
| Statement-normalization report profile/hash | `npa.library-growth.statement-normalization-report.v1` / `npa.library-growth.statement-normalization-report.hash.v1` | `npa.library-growth.statement-normalization-report.v2` / `npa.library-growth.statement-normalization-report.hash.v2` |

The Advanced AI canonical encoders inline `MachineLocalDecl` or `Expr` payloads
rather than committing only a newly domain-separated child hash. The following
hash tags are therefore mandatory v1-to-v2 bumps as part of the same table:

```text
npa.advanced-ai.candidate.v1                           -> v2
npa.advanced-ai.goal.v1                                -> v2
npa.advanced-ai.validation_result.v1                   -> v2
npa.advanced-ai.smt.problem.v1                         -> v2
npa.advanced-ai.smt.proof_payload.v1                   -> v2
npa.advanced-ai.smt.reconstruction_plan.v1             -> v2
npa.advanced-ai.smt.command_id.v1                      -> v2
npa.advanced-ai.smt.nat_to_int_side_condition.v1       -> v2
npa.advanced-ai.formalization.candidate_statement.v1   -> v2
npa.advanced-ai.formalization.accepted_statement.v1    -> v2
```

Milestone 1 must trace every caller of the shared Advanced AI
`encode_goal_to`, `encode_machine_local_decl_to`, and `encode_expr_to` helpers.
The list above is a mandatory floor, not a substitute for the complete
canonical-tag disposition ledger. Advanced AI identities that contain only one
of these newly separated hashes may retain their own tags only when the ledger
records that child boundary explicitly.

An aggregate whose byte layout is unchanged and whose changed child is already
represented by a newly domain-separated hash retains its own tag. For example,
the tactic cache-key layout retains v1 because its state and tactic
fields contain the new hashes, making every old key a deterministic miss. A
container that embeds changed bytes inline, omits the child's versioned hash,
or changes field meaning must advance. Milestone 1 records a complete generated
ledger of all canonical tags with one of three reviewed dispositions: `bump`,
`retain-with-domain-separated-child`, or `unrelated`. An unclassified tag blocks
Milestone 3.

`NPA-KERNEL-CORE-EXPR-0.1` is retained for the same reason as
`NPA-CORE-EXPR-0.1`: all remaining expression payloads and meanings are
byte-identical, and tag `0x06` is unreachable. Containers of expressions still
advance when their own field grammar changes.

`npa.proof.local-context-binder-fingerprint.v1` retains its tag because it
contains only the newly domain-separated machine-local-declaration hashes, not
inline local-declaration bytes. The proof-local-statement generalization domain
advances because its own binder encoding deletes `value_hash` and
`unfold_local_definitions`. The focused-replay failure artifact advances because
it embeds the changed minimal-failing-artifact canonical bytes inline; sidecars
that carry only either artifact's newly separated hash may retain their outer
tag under the generated disposition ledger.

Removing local-value fields also changes the public Machine API wire shape.
Advance `npa.machine-api.v1` to `npa.machine-api.v2`, update prompt/session
payload tags that commit the old local shape, and make v1 input an explicit
unsupported-protocol error. Do not retain always-null value fields: they would
continue to advertise a state the current calculus cannot represent.
Advance these directly affected identities as well:

```text
npa.machine-api.display.v1                 -> v2
npa.human-api.display.v1                   -> v2
npa.human-ide-api.v1                       -> v2
npa.machine-api.prompt-payload.v1          -> v2
npa.machine-api.prompt-rendered-content.v1 -> v2
npa.machine-api.stored-snapshot-view.v1    -> v2
npa.machine-api.session-root.v2            -> v3
npa.machine-api.session-checked-current.v1 -> v2
```

`RemovedTermLet` remains a pre-normalization Machine-term parse failure, not an
accepted failed-candidate identity. Preserve the existing boundary: a batch
item rejected for this reason has no candidate hash, AI search records it in
the non-accepted-error bucket with the exact `removed_term_let` kind and
Machine-term parse phase, and it does not enter `FailedCandidateErrorKind`, a
failed-candidate prompt, negative-training identity, or rule-based repair and
premise-retrieval flow. Consequently,
`npa.ai-search.training-trace.v1` and
`npa.ai-search.training-negative-identity.v1` retain their identities because
their own closed error vocabulary does not change; any diagnostic hashes they
carry already use the newly separated API-diagnostic domain. By contrast, the
public failure-memory key and hard-negative record directly encode
`MachineApiErrorKind`, so their closed vocabularies and identities advance as
listed in the table.

The AI-search candidate payload hash may retain
`npa.ai-search.candidate-payload.v1` because its raw candidate field grammar is
unchanged, but every consumer must reparse the term under
`npa.machine-api.v2`; a retained candidate hash cannot make a `let` candidate
reusable.

`HumanDisplayContextOptions` retains `max_context_items` and `relevant_first`
but no longer accepts `fold_local_def_values`. The Human display v2 request
validator must reject that removed field rather than ignore it. Likewise,
machine diagnostic tree v2 permits rewrite targets `goal` and `local_type` but
not `local_value`; a v1 tree or a v2 tree carrying the retired target kind must
not validate as current.

The stored expression-view, local-name-map, goal-fingerprint, retrieval-local-
context, and tactic-cache-key layouts retain their current tags because
they contain no removed field and already commit a newly domain-separated core,
context, state, or session hash. Tests must prove old material misses; a
retained outer tag is not permission to accept an old child identity.
The current-core declaration package and checked declaration signature embed
core-expression or term-table bytes inline, so their explicit bumps above are
mandatory rather than deferred to the Milestone 1 ledger. Their name-table,
level-table, and root-declaration subencodings retain v1 because their own byte
grammars are unchanged; the bumped term-table and package tags delimit the
changed child grammar. The raw
`npa.machine_tactic_candidate.v1` schema retains v1: its JSON field grammar is
unchanged, its term strings remain untrusted, and every use must parse and
revalidate them under `npa.machine-api.v2`. An old candidate containing `let`
therefore becomes a deterministic source diagnostic rather than reusable
proof state.

The new reduction profile identifier is:

```text
beta-delta-iota.v0.1
```

Do not retain `beta-delta-iota-zeta.v0.1` as an alias in current session or
cache identity. Old replay and cache material is untrusted and becomes a clean
miss or an explicit unsupported-profile error.

### Diagnostics And Performance Schemas

Current output removes `zeta_steps`; `physical_reductions` becomes exactly
`beta_steps + delta_steps + iota_steps`. This changes closed JSON vocabularies,
so the current output schemas advance as follows:

```text
npa.kernel-fuel-diagnostic.v0.1  -> v0.2
npa.performance.measurements.v0.8 -> v0.9
npa.package.command_result.v0.4 -> v0.5
npa.kernel-whnf-application-spine.measurements.v0.1 -> v0.2
npa.kernel-whnf-application-spine.micro-child.v0.1 -> v0.2
npa.kernel-whnf-application-spine.package-child.v0.1 -> v0.2
npa.kernel-whnf-application-spine.package-compare.v0.1 -> v0.2
npa.package.theorem_premise_report.v0.1 -> v0.2
npa.package.theorem_premise_report.v0.1.certificate_structural ->
  npa.package.theorem_premise_report.v0.2.certificate_structural
npa.generated_artifact_release_manifest.v0.2 -> v0.3
npa.generated_artifact_release_manifest.validation.v0.1 -> v0.2
```

The package-timings envelope retains its current version because its own fields
and meanings do not change and it explicitly embeds the new nested measurement
schema identifier. The theorem-premise chunk-storage envelope likewise retains
`npa.package.theorem_premise_report_chunks.v0.1`: it transports opaque report
bytes and their hash without interpreting report fields. The theorem-premise
analysis-limits v1 record also remains unchanged because no numeric or semantic
limit changes. The release-manifest validator continues to parse v0.1 and v0.2
manifests as untrusted historical evidence only for the hosts explicitly
retained by the Milestone 1 disposition ledger. Add the exact
0.9.0-to-command-result-v0.5 mapping. Use the 0.8.0-to-v0.4 mapping only while
collecting migration evidence, then remove it together with the 0.7.x mapping
before release; neither retired host is an archival input family in the final
binary. Change `command_result_schema_for_cli` to return a fallible result or
option backed by an explicit host-version disposition table; otherwise a
removed host could fall through to v0.1 and remain accidentally valid. A
manifest that claims a 0.7.x or 0.8.x host must fail as unsupported before
nested evidence is trusted. Current release evidence must identify 0.9.0 and
use manifest v0.3 plus command-result v0.5, and the validator must report its
new validation schema. New commands emit only the new diagnostic and
measurement shapes. Historical schema parsing must not reintroduce a retired
host mapping, kernel counter, reduction rule, or certificate acceptance path.

The v0.2 fuel diagnostic also removes `let` from the bounded
`KernelExprHead` vocabulary. The machine diagnostic tree change is independent
of the fuel schema: its v2 parser rejects both the v1 schema identity and the
retired `target_kind = local_value` attribute instead of preserving a
diagnostic-only local-definition vocabulary.

The raw independent-checker result v2 shape does not need a schema bump because
its fields are unchanged; its capability values and checker build/version
identity change to v0.4. The runner must still compare the claimed input pair
with the independently decoded requested certificate header.

The CLI/checker compatibility closure advances from the exact v0.8.0 lane to
the exact v0.9.0 lane. Replace `toolchain-v0.8.sh`,
`toolchain-v0.8.0-compat`, and every
`npa.checker_ext.toolchain_v0_8...` schema/profile with their v0.9 counterparts,
including policy-preflight, fixture, prepared-input, archive, checksum, and
manifest identities. Exercise the old lane once at the pinned Milestone 0
checkpoint, record the result, and then remove its runner and compatibility
closure. The final repository has only the v0.9 live/current-host
checker/evidence lane; explicitly historical pre-0.7 checkout snapshots, if
retained, do not count as current support and must not link to or select the
deleted v0.8 lane.

### Retired 0.7.0 And 0.8.0 Toolchain Cleanup

The transition must preserve neither a parallel 0.7 compatibility lane nor a
post-migration 0.8 lane. Perform these changes in a buildable order: use the
pinned 0.8 checkpoint to establish the baseline, replace the live lane with
v0.9, verify the full v0.9 closure, and then finish both cleanup ledgers.

- delete the four 0.7-only files listed in the baseline inventory;
- during Milestone 0, resolve and provisionally record the exact standalone
  `refs/tags/v0.7.0` remote/local tag and any matching hosted release/assets;
  after the temporary v0.8 checkpoint is verified, re-resolve them and freeze
  the final external-deletion ledger. Do not use them as migration evidence or
  delete them ahead of the verified v0.9 publication;
- remove the 0.7 entry-point cases from the shared v0.3 policy example; the
  separately deleted facade wrapper must have no replacement. Remove the
  frozen-gate byte inclusion, constants, checksum assertion, and old-schema
  rejection fixtures from checker-evidence tests;
- replace `command_result_schema_for_cli` with an explicit fallible host table,
  remove its `version.starts_with("0.7.")` and `version.starts_with("0.8.")`
  branches and accepted host/result matrix rows, and use a version-neutral
  dummy host in generic unsupported-host negative tests;
- transiently replace the 0.8.0-versus-0.7.x build-cache test with an exact
  0.9.0-versus-0.8.0 cache-miss test to prove the real migration boundary,
  record that result, and then replace that transitional fixture with a
  version-neutral stale-key test before release so it does not preserve a
  fabricated 0.8 cache entry;
- remove the deleted reference and gate from documentation indexes, checker
  runbooks, no-Python allowlists, exporter notes, Mathlib notes, tracked
  `.agents` guidance, and design histories; and
- after the v0.9 replacement passes targeted parity checks and the package
  closure is rebuilt, delete the four v0.8-only files, every shared
  `toolchain_v0_8` identity and host mapping, every v0.8-specific test/fixture,
  current link, command, allowlist entry, and reusable verification instruction
  before running the final release-candidate gates;
- publish and verify the v0.9.0 standalone tag/release, then delete the exact
  `refs/tags/v0.7.0` and `refs/tags/v0.8.0` local/remote refs and matching hosted
  releases/assets if they exist and verify their absence. Immediately before
  each deletion, re-resolve the ref object and hosted release/asset IDs and stop
  if any existing target differs from the frozen deletion ledger. The release
  note prepared before tagging records the exact identities scheduled for
  deletion; after deletion, update only the hosted v0.9 release body with the
  deletion result, then reverify that the v0.9 tag and assets are unchanged and
  valid; and
- make the v0.9 reference self-contained and current-only. Record the source
  version and break in the v0.9 release note, which must not link to a deleted
  reference or provide a command that treats v0.8.0 as a retained supported
  toolchain.

Do not delete or relabel the separate historical
`npa.performance.measurements.v0.7` reader/fixtures merely as a side effect of
this cleanup. Apply the same rule to independently versioned numeric 0.8
schemas: their disposition follows the schema ledger and the zeta-field change,
not the CLI version. Likewise, ordinary dependency versions matching 0.7.x or
0.8.x are outside this work unless they independently require an upgrade.

## Component Change Map

### `npa-frontend`

- Delete Human and Machine AST variants, lexer tokens, parser branches,
  resolver branches, elaborator branches, source spans, and renderers for let.
- Collapse `LocalDecl`, `HumanLocalDecl`, `HumanMetaLocalSnapshot`, and
  `HumanLoweringLocalDecl` to assumption-only records; remove every mirrored
  value push, lookup, snapshot, restore, and rendering path.
- Replace `MachineDiagnosticKind::UnannotatedLet` with the shared
  `RemovedTermLet` Human/Machine lexer diagnostic and emit the exact
  `removed_term_let` Human LSP reason code.
- Unreserve `in` and test it as an identifier.
- Remove let handling from term-source validation and Human/Machine conversion.
- Replace equation-compiler sharing with the guarded lambda/application form.
- Remove refine-let parsing and lowering.

### `npa-kernel`

- Delete the `Expr` variant and constructor.
- Delete `KernelExprHead::Let`; the new fuel diagnostic may report only the six
  retained expression heads plus `unknown`.
- Simplify equality, traversal, shifting, substitution, occurrence, memo, and
  resource-accounting walkers to the six-form grammar.
- Make `Ctx` assumption-only and remove value-sensitive memo identity.
- Delete explicit-let inference and both local-definition whnf paths.
- Delete zeta counters and update the physical-reduction invariant.
- Retain module-definition delta behavior unchanged.

### `npa-cert`

- Define only `V0_4_0` and delete compatibility version enums/constants.
- Remove `TermNode::Let`, its encoder, decoder, canonical key, hash key,
  materializer, structural child rules, dependency scans, and verification
  branches.
- Remove `CanonTerm::Let`, let-specific iterative materialization frames, and
  `VerifiedTheoremPremiseUseSite::LetValue`; regenerate theorem-premise
  analysis fixtures without a `let_value` use-site kind.
- Retire tag `0x06` and add malformed-current negative fixtures.
- Apply the v0.4 declaration/module domains and recompute canonical goldens.
- Keep tagged v0.3 dependency-entry layout as the v0.4 layout.
- Remove legacy positive decode/verify tests; replace them with header rejection
  tests while preserving historical fixture bytes when useful as negative data.

### `npa-package`

- Remove retired-term traversal from L2 namespace transport and any other
  certificate-derived package projection.
- Remove `PackageTheoremPremiseUseSite::LetValue` and reject `let_value` as a
  current report value while retaining it only in explicitly historical report
  readers, if such a reader is still required.
- Retain the independent v0.1 package profile axes, while requiring all decoded
  module rows and cache identities to carry the exact v0.4 pair.
- Make old cached certificate summaries deterministic misses and keep package
  lock validation fail-closed on an old pair.
- Apply the crate-version bump after checking every public type re-exported from
  `npa-cert` for the breaking term-enum change.

### `npa-checker-ref`

- Independently reduce its term representation and decoding table.
- Make `TypeContext` assumption-only and remove `LocalType.value`,
  `TypeContext::push_definition`, and `TypeContext::lookup_value` together with
  both local-definition reduction paths.
- Delete all old format/core variants and their domains.
- Implement v0.4 header, domains, retained term hashes, and tag rejection
  without importing producer logic.
- Update retained-charge and structural accounting for two-child binders only.
- Add differential fixtures for each accepted and rejected boundary.

### `npa-checker-ext`

- Remove `Ext_term.Let` and all matching cases in decoding, canonicalization,
  type checking, substitution, inductive validation, axiom analysis, and tests.
- Collapse `local_binding` to `local_ty` only and remove `local_value`,
  `push_definition`, and `lookup_value`; the clean-room checker must not retain
  a second value-bearing context representation after `Ext_term.Let` is gone.
- Advertise checker 0.4.0 with the v0.4 pair only.
- Delete current compatibility format selection rather than leaving dormant
  branches.
- Reject `0x06` and every old/mixed header pair deterministically.
- Preserve clean-room independence: do not copy Rust implementation code or
  trust Rust-produced semantic summaries.

### `npa-api`, `npa-cli`, And `npa-tactic`

- Remove term cases from current/human APIs, advanced AI paths, theorem graphs,
  search, solver, renderer, proof semantics, standard-library handling,
  package artifact handling, package verification, and CLI interface-proposal
  traversal.
- Remove `ProofSkeletonTerm::Let`, `ProofExpr::Let`,
  `RefineTermAstKind::Let`, `OwnerAwareExpr::Let`, and value-bearing local
  declarations.
- Remove `StructuredHypothesis.value`, `StructuredHypothesis.is_local_def`, and
  local-value fields from machine views, prompts, Human hole goals, and LSP
  responses; update each owning protocol, hash, fixture, and compatibility
  diagnostic rather than serializing permanent `null` placeholders.
- Remove `HumanDisplayContextOptions.fold_local_def_values`,
  `RewriteDiagnosticTargetKind::LocalValue`, and the value hash/summary fields
  from diagnostic, minimal-failure, proof-generalization, and library-growth
  local records. Delete the now-empty
  `ProofLocalStatementGeneralizationPolicy` and its function parameter.
- Add `MachineApiErrorKind::RemovedTermLet` with the wire spelling
  `removed_term_let`, update the frontend-to-Machine-API and
  Human-to-diagnostic-tree mappings to use it, and classify it in the
  Machine-term parse phase. Do not retain the former elaboration-error
  classification of `UnannotatedLet`. Update the diagnostic canonicalizer,
  parser, primary-name rule, and goal/tactic-population tables so the new kind
  has the same structural population rules as a Machine-term parse failure.
- Preserve the raw-term parse boundary in tactic batches: report no candidate
  hash and propagate the exact new kind and phase through the AI-search
  non-accepted-error trace without adding a `FailedCandidateErrorKind` case.
  Advance the API-diagnostic, failure-memory, and hard-negative identities
  listed above while retaining the unchanged AI-training identities.
- Change the shared Advanced AI goal/local/expression encoders to the let-free
  shapes and advance every directly embedding hash domain listed above; trace
  all helper callers in the canonical-tag ledger before accepting any retained
  aggregate domain.
- Update session, cache, replay, diagnostics, performance, and release-manifest
  contracts as specified above.
- Keep historical JSON validation isolated from current semantic structures.
- Ensure every public exhaustive match and serialized enum is intentionally
  versioned rather than mechanically patched until it compiles.

### `npa-lean-exporter`

- Remove let from exporter IR, lowering, rendering, and resource accounting.
- Advance `npa.lean.native.v0.2` to `npa.lean.native.v0.3` and
  `npa.lean.export.v0.2` to `npa.lean.export.v0.3`; accept only v0.4 package
  closures and forbid mixed input pairs. The unchanged
  `npa.lean.command_result.v0.1` envelope may retain its schema because it
  reports the newly versioned manifest only by hash and path.
- Update the pinned `npa-core` revision only after the v0.4 core commit is
  stable.
- Retain the existing rule that export is narrower than NPA proof acceptance.
- Add a let-free lambda/application fixture and prove no Lean output path can
  receive a retired core node.

### Packages, Corpus, And Agents

- Delete the two let-only declarations from every live and positive-fixture
  Reduction module.
- Update manifest theorem lists, metadata, replay records, corpus registries,
  promotion-origin materialization, generated indexes, and tests through their
  owning generators.
- Treat `npa-mathlib` as a new mutable-catalog revision at a strictly newer
  package version. Append the required catalog-change/revision event with the
  reconciliation transaction; never edit or delete an existing
  `promotion-origins.json` history entry or a released promotion attestation.
- Rebuild all certificates and complete package artifacts under v0.4.
- Update `npa-agents` toolchain pins, checker capability assumptions, cached
  profile identities, fixtures, and service tests.
- Update tracked `.agents` skills and references so authoring instructions name
  only the v0.9 toolchain and current profiles.
- Audit `npa-web` only for displayed version/profile metadata; it must not
  become a proof authority.
- Update root `AGENTS.md`, current README material, toolchain references, and
  checker documentation. Keep v0.3 and older certificate/core specifications
  as historical.

## Migration Order

The dependency order is:

```text
temporary pinned npa-cli 0.8.0 / v0.3 inventory and verification
    -> let-free untrusted producers
    -> v0.4 kernel + certificate producer
    -> independent Rust and OCaml checkers
    -> npa-cli 0.9.0 checker/evidence closure
    -> foundational package certificates
    -> Mathlib/corpus/project closures
    -> agents/exporter/web pins
    -> local 0.7.0/0.8.0-remnant cleanup + release-candidate evidence
    -> v0.9.0 publication
    -> retired external ref/release/asset cleanup
```

No final merge or release may expose an intermediate state where the producer
emits a pair that either required independent checker cannot verify.

### Milestone 0: Freeze And Decode The Baseline

Status: completed on 2026-09-04. See the exact commits, checksums, full path and
decoded-term inventories, producer classifications, three-checker verdicts,
and provisional external-deletion identities in
[let-removal-milestone-0/](let-removal-milestone-0/).

1. Fetch `origin`, record the exact implementation base commit, and assert that
   its package metadata reports `npa-cli 0.8.0` and the v0.3 certificate/core
   pair. Stop rather than silently changing either endpoint if that assertion
   fails.
2. Pin the final let-capable container commit and its matching standalone
   `npa-core` commit. Record both commit identities, tracked-tree equivalence,
   crate locks, Rust toolchain, checker builds, and source/binary/checker
   checksums. Use a clean detached checkout at the standalone commit; do not
   create or publish a new v0.8.0 tag, release, or asset. Query the exact v0.7.0
   and v0.8.0 local/remote refs and hosted releases. For each existing tag,
   provisionally record its ref target, tag object, and peeled commit when
   annotated; for each existing release, record its release and asset IDs. Use
   those identities only for the final deletion ledger. The v0.7.0 identity is
   cleanup metadata, not part of the migration baseline.
3. Verify at least one v0.3 certificate source-free with the pinned fast, Rust
   reference, and OCaml checkers from that detached clean checkout. Any
   temporary bundle used for this run must remain outside tracked/live release
   surfaces and be listed for deletion.
4. Repeat the source and semantic-symbol inventory commands from this document
   and preserve their full path lists with the refreshed counts.
5. Before deleting the v0.3 decoder, decode every tracked `.npcert` with the
   pinned temporary v0.8.0 toolchain and count term-node tags by artifact path.
6. Classify each let-bearing artifact as source-authored, tactic-produced,
   equation-compiler-produced, fixture-only, or unexplained.
7. Stop if any unexplained producer exists; locate and assign it before code
   removal.
8. Record public declarations and downstream imports of the two Reduction
   modules using certificate-derived indexes, not source grep alone.

Exit criteria:

- every accepted source occurrence and decoded `0x06` node has an owner and
  migration action;
- the exact v0.8.0/v0.3 commits, trees, build inputs, and checksums are recorded,
  and a detached clean checkout reproduces all three checker verdicts without
  requiring a newly published tag or release;
- no artifact is classified only from its filename or metadata;
- the inventory is attached as untrusted implementation evidence; and
- every existing v0.7 tag, release, asset, instruction, and compatibility entry
  point, and every existing or temporary v0.8 tag, release, asset, bundle,
  instruction, and compatibility entry point has an exact final-cleanup
  disposition.

### Milestone 1: Freeze The v0.4 Contract

Status: completed on 2026-09-04. The frozen specification, complete reviewed
identity dispositions, Advanced AI caller trace, shared Rust/OCaml fixture
contract, temporary v0.8 command/result record, and Milestone 7 deletion ledger
are indexed in [let-removal-milestone-1/](let-removal-milestone-1/).

1. Add a self-contained `core-spec-v0.4.0.md` implementing this decision.
2. Specify the six tag encodings, retired-tag behavior, domains, strict header
   matrix, and source diagnostic.
3. Generate and review the complete canonical-tag disposition ledger required
   by the sidecar policy; no tag may remain unclassified.
4. Prepare the exact positive and negative fixture matrix for old-pair
   rejection, tag `0x06` rejection, and the new hash-domain expectations. The
   assertions land atomically with Milestone 3; no milestone commit may leave
   the workspace intentionally failing or tests ignored.
5. Record the exact one-time v0.8.0 baseline commands and their results in the
   temporary migration ledger before deleting compatibility code. Do not
   publish those commands as a retained user-facing verification path; carry
   only the non-executable commit/checksum/verdict summary into the release
   note, and add every raw instruction or helper to the Milestone 7 deletion
   ledger.

Exit criteria:

- the wire and compatibility decisions have no unresolved options;
- Rust and OCaml tests use the same fixture matrix but independent logic;
- every canonical payload has an explicit bump, justified retention, or
  unrelated classification;
- no implementation can silently choose to preserve an old pair.

### Milestone 2: Eliminate Let From All Producers

Status: completed on 2026-09-04. Current Human/Machine source and
refine/proof-expression producers are let-free; guarded equation sharing and
the remaining internal producers emit no retired term form. The 12 live source
occurrences and their let-only declarations were removed, and the transitional
package artifacts and npa-mathlib catalog revision were refreshed and
independently verified.

1. Remove the 12 baseline live/positive-fixture source occurrences and the
   let-only declarations.
2. Remove Human/Machine accepted syntax, replace the old Machine-only
   `UnannotatedLet` kind with the shared rejection-only `RemovedTermLet` kind,
   and update both API diagnostic mappings.
3. Remove refine-let and `ProofExpr::Let`.
4. Change equation sharing to guarded lambda/application.
5. Convert every remaining internal producer before removing `Expr::Let`.
6. Add regression tests for `have`, `suffices`, `specialize`, equations, and
   generated inductive/solver terms.

At the end of this milestone, temporary old kernel/checker branches may still
decode old certificates inside the unmerged feature branch, but no current
source or tactic path may create a new let node.

Exit criteria:

- producer-focused tests observe no `Expr::Let` or term tag `0x06`;
- all live, accepted package, and positive-fixture `.npa` sources pass structure
  checks and ordinary targeted builds with the transitional toolchain;
- rejection-only `.npa` fixtures are absent from accepted package manifests and
  build selections and fail with their specified removal diagnostic;
- the equation compiler meets its correctness and resource tests.

### Milestone 3: Remove Let From The Rust Core

Status: completed on 2026-09-04. The Rust kernel, certificate crate, reference
checker, and direct API callers now expose assumption-only local contexts and
the strict v0.4 certificate/core pair with no let term or zeta reduction. The
old semantic decoders were removed, the shared v0.4 conformance fixtures were
regenerated, and the direct core crate versions were advanced together.

Make one coordinated, buildable change across `npa-kernel`, `npa-cert`, the
Rust reference checker, and their direct API callers:

1. remove the semantic variants and local-definition context;
2. remove zeta conversion and accounting;
3. switch to the strict v0.4 pair and new certificate domains;
4. remove old decoders and positive compatibility tests;
5. update all trusted and untrusted term walkers;
6. update the direct core crate versions (`npa-kernel`, `npa-cert`, and
   `npa-checker-ref`) and lockfiles. Milestone 5 updates the remaining public
   API/tooling crate versions with their wire changes.

Exit criteria:

- the entire Rust workspace compiles with no compatibility feature flag;
- fast and reference checkers agree on all v0.4 positive/negative fixtures;
- an old pair fails before term decoding;
- a v0.4 `0x06` fixture fails as unsupported encoding;
- no current Rust public type can construct a let or value-bearing local.

### Milestone 4: Restore Independent Checker Parity

Status: completed on 2026-09-04. The clean-room OCaml checker now implements
only the strict v0.4 six-form core, publishes its v0.4 capability and refreshed
build identity, consumes the shared fixture matrix, and agrees with the fast
and Rust reference checkers on accepted identities and required verdicts.

1. Implement the OCaml changes independently.
2. Regenerate its checker build identity and capability output.
3. Run direct, facade, malformed-input, resource-bound, and differential tests.
4. Verify matching module/export/axiom identities for accepted v0.4 fixtures.
5. Verify stable but checker-specific rejection classifications for old pairs,
   mixed pairs, and tag `0x06`.

Exit criteria:

- the clean-room checker accepts every required v0.4 conformance positive;
- it fails closed on every negative without consulting source or Rust output;
- the toolchain runner binds actual input pair and checker capability pair.

### Milestone 5: Migrate APIs, Sidecars, And Telemetry

Status: completed on 2026-09-04. The remaining public `npa-core` crates now
use their let-free semver endpoints; current sidecar, kernel-profile, fuel,
measurement, command-result, and release-manifest identities use the planned
domains. Release validation accepts only the exact 0.9.0 host as current,
treats retained pre-0.7 hosts as historical v0.2 evidence, and rejects 0.7.x
and 0.8.x hosts before nested evidence validation. The one-time 0.9.0-versus-
0.8.0 cache miss is recorded in the Milestone 1 migration ledger, while the
tracked regression test is version-neutral. Package and downstream consumer
rebuilds remain Milestone 6 work.

1. Complete public enum/struct removals and semver bumps.
2. Advance proof-state/cache, proof-generalization, API-diagnostic,
   diagnostic-tree, failure-memory, hard-negative, minimal-failure,
   focused-replay, and library-growth identity domains whose payloads changed.
3. Emit only `beta-delta-iota.v0.1` for current kernel profile identity.
4. Advance the fuel, measurements, and command-result schemas.
5. Update release-manifest current validation while retaining explicitly
   historical untrusted schema readers only where needed; a retained schema
   reader must not imply support for a 0.7.x or 0.8.x CLI host.
6. Remove the 0.7.x and 0.8.x release-manifest host mappings. Exercise the
   exact 0.9.0-versus-0.8.0 cache boundary during migration, record its miss,
   and replace the transitional version-specific fixture with a
   version-neutral stale-key negative before release.
7. Invalidate local caches and replay state by identity, never by undocumented
   directory deletion as part of proof acceptance.

Exit criteria:

- no current API output contains `zeta_steps`;
- physical reductions equal beta plus delta plus iota in implementation and
  validators;
- stale v0.3 cache/replay material is a miss or clear unsupported-version
  error, never a hit;
- current sidecar hashes use their new domains.

### Milestone 6: Rebuild The Package Ecosystem

Rebuild in topological waves with repository-local `npa-cli 0.9.0`, which
produces the v0.4 certificate/core pair:

1. `npa-core` compact and security fixtures;
2. `npa-std`;
3. `npa-mathlib`;
4. `npa-corpus`;
5. every `npa-project-*` proof package present at implementation time; the
   current set is `npa-project-bsd`, `npa-project-collatz`,
   `npa-project-fermat-last-theorem`, `npa-project-hodge`, `npa-project-iut`,
   `npa-project-navier-stokes`, `npa-project-p-vs-np`,
   `npa-project-poincare`, `npa-project-riemann-hypothesis`,
   `npa-project-sunflower`, and `npa-project-yang-mills`;
6. `npa-agents`, `npa-lean-exporter`, `npa`, and `npa-web` consumers.

For each package, use the canonical writer to refresh certificate bytes,
declared hashes, metadata, and `generated/package-lock.json`. Then regenerate
the axiom report, theorem index, theorem-premise report, export summary,
publish plan, promotion registry material, and other checked generated outputs
through their owning commands. Do not hand-edit final hashes.

Because mixed closures are forbidden, a wave may begin only after all imported
packages in the preceding wave have v0.4 certificate bundles available. An
unchanged export hash does not permit importing old certificate bytes.

From the container root, the full per-package command shape is:

```sh
npa-core/target/debug/npa package check-source-structure --root PACKAGE_ROOT --json
npa-core/target/debug/npa package build-certs --root PACKAGE_ROOT \
  --update-manifest-hashes --json
npa-core/target/debug/npa package build-certs --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package verify-certs --root PACKAGE_ROOT \
  --package-lock checked --checker reference --audit-cache off \
  --verifier-memo off --json
npa-core/target/debug/npa package check-hashes --root PACKAGE_ROOT --json
npa-core/target/debug/npa package axiom-report --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package index --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package theorem-premise-report \
  --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package export-summary --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package publish-plan --root PACKAGE_ROOT --check --json
npa-core/target/debug/npa package check-generated --root PACKAGE_ROOT --json
```

Run the commands with `ulimit -s 65520` for the established large package
closures. Add package-specific promotion-origin, artifact-ledger, external
checker, and high-trust gates where their manifest or release policy requires
them. Read the JSON `status` and every diagnostic; process exit and progress
output alone are insufficient.

Exit criteria:

- every package closure contains only the v0.4 pair;
- every source-free reference verification is cache-disabled;
- required external checker gates pass with checker 0.4.0;
- package locks and generated ledgers agree with canonical bytes;
- axiom reports do not grow.

### Milestone 7: Documentation, Release, And Cleanup

1. Make `core-spec-v0.4.0.md` the current core reference.
2. Add a self-contained, current-only exact toolchain 0.9.0 reference. Prepare
   the v0.9.0 release note with the v0.8.0-to-v0.9.0 source boundary, break, and
   exact retired identities scheduled for deletion; it neither links to nor
   teaches use of a retained v0.8.0 toolchain.
3. Update current README/index/checker/exporter/agent documentation, including
   tracked `.agents` skills and their references.
4. Replace the `NPA let Syntax` guidance in root `AGENTS.md` with the removal
   rule and let-free alternatives.
5. Mark v0.3.0 and older specs as historical through indexes without changing
   their normative bodies.
6. Delete `npa-toolchain-reference-v0.7.0.md`, `toolchain-v0.7.sh`,
   `verify_ext_v0_7_facade.rs`, and `inspect_ext_v0_7_policy.rs`.
7. After the temporary v0.8.0 checkpoint evidence is complete, remove all
   embedded 0.7.0 CLI/toolchain branches, identities, tests,
   fixtures, allowlist entries, links, commands, and compatibility instructions
   identified by the baseline inventory; rewrite necessary design chronology in
   version-neutral terms.
8. Replace the v0.8 checker/evidence closure with v0.9 identities and tests.
   Delete `npa-toolchain-reference-v0.8.0.md`, `toolchain-v0.8.sh`,
   `verify_ext_v0_8_facade.rs`, `inspect_ext_v0_8_policy.rs`, all embedded v0.8
   support, and all transitional audit helpers or compatibility-only code after
   their migration evidence has been summarized as non-executable
   commit/checksum/verdict data. Delete the raw v0.8 command transcript and
   temporary migration ledger rather than publishing them as instructions.
9. Run the term-level-let and local 0.7.0/0.8.0-remnant audits, then complete
   the full v0.9.0 release-candidate gates and publish and independently verify
   the exact standalone v0.9.0 tag/release/assets.
10. Delete the exact v0.7.0 and v0.8.0 standalone local/remote tags and matching
    hosted releases/assets if they exist. Immediately re-resolve every target
    and compare its object or hosted ID with the frozen ledger; stop on identity
    drift rather than deleting by name alone. Delete temporary v0.8 bundles and
    workspaces and verify every targeted ref/release/asset is absent. Update the
    hosted v0.9.0 release body, not the immutable tagged source, with the
    deletion results; reverify the unchanged v0.9.0 tag and assets, then rerun
    both remnant audits against the final published state.

Exit criteria:

- current documentation contains no claim that current NPA accepts let or old
  certificate pairs;
- historical certificate/core specifications are clearly version-scoped;
- no executable, test, fixture, configuration, operational document, or live
  link outside the explicitly allowed audit/history records retains a 0.7.0 or
  0.8.0 toolchain identity or compatibility path;
- the standalone 0.7.0 and 0.8.0 Git refs and matching hosted releases/assets
  no longer resolve;
- every retained numeric 0.7 or 0.8 match is recorded as a different version
  axis, allowlisted non-runnable core/certificate history, or this
  design/release note's cleanup record;
- the worktree is clean after generated artifacts are committed;
- release evidence identifies the exact source commit, checker builds, and
  v0.4 pair.

## Verification Plan

### Static Absence Audit

The final audit must return no current semantic hits for at least:

```text
Expr::Let
Expr::let_in
Ctx::push_definition
Ctx::lookup_value
push_definition
lookup_value
TermNode::Let
CanonTerm::Let
MachineTerm::Let
HumanExpr::Let
ProofExpr::Let
ProofExpr::let_in
ProofSkeletonTerm::Let
RefineTermAstKind::Let
RefineTermAst::let_in
KernelExprHead::Let
RewriteDiagnosticTargetKind::LocalValue
npa_kernel::context::LocalDecl.value
npa_frontend::elaborator::LocalDecl.value
npa_frontend::machine::MachineLocalDecl.value
npa_tactic::MachineLocalDecl.value
npa_tactic::MachineLocalDecl::definition
HumanLocalDecl.value
HumanMetaLocalSnapshot.value
HumanLoweringLocalDecl.value
HumanHoleGoalLocal.value
HumanLspHoleGoalLocal.value
MachineLocalView.value
MachinePromptLocal.value_machine
MachinePromptLocal.value_pretty
StructuredHypothesis.value
StructuredHypothesis.is_local_def
TokenKind::Let
TokenKind::In
TokenKindName::Let
TokenKindName::In
parse_let
infer_let
MachineDiagnosticKind::UnannotatedLet
ReferenceCoreExpr::Let
Build::Let
Frame::BuildLet
OwnerAwareExpr::Let
LeanExprNode::Let
Ext_term.Let
VerifiedTheoremPremiseUseSite::LetValue
PackageTheoremPremiseUseSite::LetValue
AdvancedMachineExprPathStep::LetType
AdvancedMachineExprPathStep::LetValue
AdvancedMachineExprPathStep::LetBody
KernelWorkCounter::ZetaStep
PerformanceMeasurementLabel::KernelZetaSteps
zeta_steps
let_value
local_value
fold_local_def_values
unfold_local_definitions
ProofLocalStatementGeneralizationPolicy
LocalType.value
DiagnosticLocalSummary.value_hash
DiagnosticLocalSummary.value_summary
MinimalFailingArtifactLocal.value_hash
ProofLocalStatementGeneralizationBinder.value_hash
LemmaGeneralizationLocal.value_hash
StatementNormalizationBinder.value_hash
beta-delta-iota-zeta.v0.1
```

Search the full tracked container tree, including `npa-core`,
`npa-lean-exporter`, `npa-agents`, tracked hidden guidance such as `.agents`,
and every Rust/OCaml consumer. Use a tracked-file inventory or `rg --hidden` so
dot-directories are not omitted. Allowed historical certificate/core
specification and negative-fixture matches must be reviewed individually; do
not use a blanket repository-wide exclusion that could hide current code.
Qualified field entries in the list denote structural inspection targets, not
only literal grep strings; the audit must inspect the named record definitions
and their encoders so a missing qualified call-site spelling cannot yield a
false clean result.

A separate `.npa` scan must find no accepted source occurrence matching the
typed old form. This text scan supplements, but never replaces, parsing,
elaboration, decoded-certificate inspection, and source-free verification.

The separate retired-toolchain audit must combine filename scans with the
content patterns listed in both baseline inventories. Drive it from
`/usr/bin/git ls-files` plus `/usr/bin/git grep`, or use an equivalent
hidden-file-aware scan, so tracked `.agents` instructions cannot escape the
audit. At minimum it searches for:

```text
v0.7.0
npa-cli 0.7
toolchain-v0.7
toolchain_v0_7
HISTORICAL_V0_7
verify_ext_v0_7
inspect_ext_v0_7
v0.8.0
npa-cli 0.8
toolchain-v0.8
toolchain_v0_8
HISTORICAL_V0_8
verify_ext_v0_8
inspect_ext_v0_8
```

The only permitted CLI/toolchain matches are this design, the v0.9.0 release
note that records the deletion, and explicitly version-scoped
certificate/core specifications containing non-runnable normative chronology.
No exception may contain a live link, verification command, compatibility
branch, or claim that the retired host remains currently supported. Review
every remaining numeric `0.7` or `0.8` match and classify unrelated measurement
schemas, protocol versions, dependency versions, and mathematical notation by
their own version axis; a broad numeric exclusion is forbidden. Query the
configured standalone remote for the exact `refs/tags/v0.7.0` and
`refs/tags/v0.8.0` refs and query the release host for both matching releases
and assets. All queries must report absence after cleanup.

### Required Positive Tests

- all six core term forms infer/check and round-trip canonically;
- beta, delta, and iota positive and negative conversion cases;
- lambda/application replacement for equation sharing;
- `have`, `suffices`, and both `specialize` result policies produce and extract
  valid proofs without a retired node;
- valid v0.4 certificates pass fast, reference, and OCaml checkers;
- let-free terms retain their specified term hashes;
- let-free public interfaces retain hashes where their export lists are
  unchanged;
- deep binders, shared DAGs, and resource limits remain stack-safe and bounded.

### Required Negative Tests

- Human and Machine source containing `let` produces `RemovedTermLet` with an
  exact source span; Human LSP and Machine API output carry the exact
  `removed_term_let` code, and Machine API classifies it in the Machine-term
  parse phase;
- former syntax cannot be smuggled through refine, annotations, notation, AI
  adapters, session replay, or direct public constructors;
- every old and mixed certificate header pair is rejected;
- tag `0x06` in both reachable and otherwise unused term-table positions is
  rejected during complete table decoding;
- a header-only v0.3-to-v0.4 edit fails hash/canonical validation;
- stale proof-state, replay, cache, and performance schema identities do not
  validate as current;
- old proof-generalization, diagnostic-tree, minimal-failure, focused-replay,
  API-diagnostic, failure-memory, hard-negative, library-growth, and directly
  embedding Advanced AI identities do not validate as current;
  diagnostic tree v2 also rejects `target_kind = local_value`;
- a `RemovedTermLet` tactic candidate has no candidate hash, appears under the
  exact kind and phase in the AI-search non-accepted-error trace, and does not
  enter failed-candidate prompts, negative-training identities, or repair and
  premise-retrieval flows;
- malformed retired-tag payloads cannot cause allocation before rejection;
- current release-manifest validation rejects `zeta_steps` in current schemas
  and accepts it only in explicitly historical untrusted schemas, if retained.

### Local Commands

Use the checked-out local toolchain. At minimum, the implementation must run:

```sh
cd npa-core
./scripts/check-fast.sh
cargo test -p npa-kernel
cargo test -p npa-cert
cargo test -p npa-checker-ref
cargo test -p npa-frontend
cargo test -p npa-tactic
cargo test -p npa-api
cargo test -p npa-cli
checkers/npa-checker-ext/scripts/test.sh
```

Run focused malformed-certificate and differential checker suites in addition
to the broad commands. For every changed Human source, run the lexer-aware
`package check-source-structure` preflight before building. At package
completion boundaries, use `ulimit -s 65520`, canonical write mode, full
cache-off build checks, checked locks, axiom/hash/generated gates, and full
source-free reference verification as required by each package.

The final container validation must cover every package root, not only
`npa-core/testdata`. Cache hits, source checking, successful elaboration, and AI
review are authoring feedback and are not proof evidence.

## Acceptance Criteria

The implementation is complete only when every statement below is true:

1. Current Human and Machine Surface cannot construct a term-level let.
2. Current tactics and generators cannot construct it indirectly.
3. Rust kernel contexts contain types only and conversion has no zeta rule.
4. Canonical v0.4 certificates encode only tags `0x00` through `0x05`.
5. Tag `0x06` is rejected and permanently unassigned.
6. Current binaries accept exactly the v0.4 format/core pair.
7. Fast, Rust reference, and OCaml checkers agree on the full conformance
   matrix.
8. Current schemas and profile identities contain no zeta measurement.
9. All live, accepted package, and positive-fixture `.npa` source is let-free;
   rejection-only fixtures are isolated from accepted manifests and builds and
   deterministically reject the retired spelling.
10. All checked certificates, locks, hashes, reports, indexes, summaries,
    registries, replays, and toolchain pins are coherently regenerated.
11. Every package passes its full canonical and source-free acceptance gates.
12. Axiom reports are unchanged except for deterministic removal of obsolete
    let-only declarations; no new axiom is introduced.
13. Current documentation describes v0.4 accurately and historical
    certificate/core specifications remain discoverable as historical material.
14. Static semantic-symbol searches have no unexplained findings.
15. The implementation branch contains no compatibility flag or dead legacy
    decoder that can re-enable let.
16. One-time migration evidence records the exact v0.8.0/v0.3 commits, trees,
    inputs, checksums, decoded-term inventory, and successful clean-checkout
    fast/reference/OCaml verdicts before that toolchain is removed.
17. No executable, test, fixture, configuration, operational documentation,
    live link, standalone Git ref, hosted release, or release asset outside the
    explicitly allowed audit/history records retains a 0.8.0 toolchain
    identity, compatibility path, or reusable verification instruction; every
    remaining numeric 0.8 match belongs to a reviewed different version axis,
    non-runnable version-scoped core/certificate history, or the cleanup record
    in this design/release note.
18. The equivalent absence condition holds for 0.7.0, and every remaining
    numeric 0.7 match is likewise classified.

## Risks And Mitigations

### Hidden Generated Let Nodes

Risk: source grep misses nodes introduced by refine or equation lowering.

Mitigation: decode all existing certificates before removing the old decoder,
classify every hit, migrate producers first, and repeat a producer-output audit
before the core deletion.

### Loss Of Local Definitional Equality

Risk: an old body may type-check only because its local name unfolds to the
bound value.

Mitigation: use capture-avoiding substitution for general migration, recheck
all results under v0.4, and do not advertise blind lambda/application rewriting
as universally equivalent during elaboration.

### Equation-Lowering Resource Regression

Risk: replacing let sharing could increase expanded nodes, allocation, or beta
fuel.

Mitigation: use the guarded lambda/application form, retain certificate DAG
deduplication, measure both logical and physical work, and decline the
optimization when its type or resource preconditions fail.

### Historical Certificate Availability

Risk: after final cleanup, users cannot verify old v0.3 bytes with either the
newest binary or a retained released v0.8.0 toolchain.

Mitigation: state this deliberate support break prominently. Before removal,
run and record one clean-checkout verification and complete decoded inventory;
retain the versioned certificate/core specifications, exact source commit and
tree identities, checksums, and non-executable result record. Migrate or rebuild
every supported package to v0.4 before cleanup. These records support audit and
an explicitly authorized future reconstruction, but are not a supported
verification entry point. Do not weaken complete removal by embedding or
publishing the old checker.

### Cross-Repository Atomicity

Risk: v0.4 packages cannot import v0.3 certificates, creating a broken mixed
window.

Mitigation: rebuild in topological waves, pin exact commits, keep the branch
unreleased until all required closures and checkers are ready, and publish the
foundational package artifacts before their dependents.

### Stale Untrusted Sidecars

Risk: old proof states or caches appear reusable because their outer schema did
not change.

Mitigation: bump every changed canonical payload domain and kernel profile
identity, test clean misses, and regenerate replay/metadata only through owning
tools.

### Over-Broad Text Cleanup

Risk: searching for `let` would target ordinary Rust/OCaml bindings, English
prose, or mathematical zeta functions.

Mitigation: use semantic symbol patterns, typed NPA syntax searches, decoded
term tags, and reviewed allowlists. The Riemann zeta function is unrelated and
must not be renamed.

### Over-Broad Retired-Version Cleanup

Risk: a blanket search for `0.7` or `0.8` could delete historical measurement
readers, third-party dependency pins, protocol versions, or unrelated design
data that does not represent either retired CLI/toolchain.

Mitigation: remove the enumerated toolchain files and semantic identities, use
the specific content/filename patterns in both baseline inventories, and record
the version axis for every remaining numeric match. Do not use a blanket
numeric replacement.

### Deleting Retired Standalone Tags And Releases

Risk: deleting the wrong remote ref, or deleting v0.8.0 before the verified
v0.9.0 release is live, could remove the only usable toolchain prematurely.

Mitigation: resolve and record the exact 0.7.0 and 0.8.0 tag and hosted-release
identities without creating missing ones. Verify the temporary v0.8.0 baseline
first, publish and verify v0.9.0 before deleting either retired external
identity, re-resolve each target immediately before mutation, and stop if its
object or hosted ID has drifted from the frozen ledger. Delete only the matched
ref/release/asset and confirm remote and hosted absence afterward. The recorded
object identity is recovery metadata, not a supported compatibility path.

## Rollback And Recovery

Before migration, record the exact final `npa-cli 0.8.0` / v0.3 container
commit, matching standalone commit, verified subtree/tree equivalence, crate
locks, checker build identities, temporary package artifact bundle checksums,
and the exact existing 0.7.0/0.8.0 ref, release, and asset identities scheduled
for deletion. Record tag objects and peeled commits only when those tags
already exist. If the feature branch fails before release, revert the
coordinated removal commits rather than partially restoring a decoder.

After the v0.9.0/v0.4 release and retired-version cleanup, rollback to v0.8.0
is not supported. A v0.4 certificate cannot be downgraded by editing headers or
hashes, and a current package closure cannot mix restored v0.3 imports with
v0.4 modules. Emergency recovery would require an explicitly authorized,
full-source reconstruction from the recorded commit followed by a newly named
release and matching complete v0.3 artifact closure; it cannot rely on a live
v0.8.0 tag, asset, instruction, or compatibility lane. The ordinary rollback
is to revert or supersede the v0.9 implementation while preserving the v0.4
wire contract, not to resurrect either retired toolchain.

## Implementation Review Checklist

Reviewers must answer all of these questions from code and generated evidence:

- Can any public or crate-private constructor still create a value-bearing
  local term?
- Can any parser, notation, refine, tactic, equation, solver, or AI path bypass
  the `removed_term_let` diagnostic?
- Does any checker accept an old pair or interpret `0x06`?
- Are the Rust and OCaml implementations independently derived from the same
  written v0.4 contract?
- Did every changed canonical payload receive an explicit domain decision?
- Are unchanged hash domains justified by byte-identical retained meanings?
- Did current zeta output disappear without making historical report data
  trusted?
- Were all package artifacts regenerated by owning writers?
- Do full source-free cache-disabled gates pass on every closure?
- Does the recorded one-time v0.8.0 checkpoint evidence identify exact commits,
  trees, inputs, checksums, decoded terms, and all three successful checker
  verdicts without depending on a retained release?
- Are the 0.7.0- and 0.8.0-only files, entry points, release-manifest branches,
  fixtures, links, instructions, local/remote tags, hosted releases, and assets
  gone, with remaining numeric 0.7/0.8 matches proven to belong to another
  version axis, allowlisted non-runnable core/certificate history, or this
  design/release-note cleanup record?
- Does the final diff preserve module-level `def`, `opaque def`, `have`, and
  `suffices`?
- Are all remaining matches historical, rejection-only, unrelated language
  syntax, or the mathematical zeta function?

No implementation milestone is complete while any answer is unknown.
