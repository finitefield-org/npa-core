# NPA Core Implementation Specification v0.3.0

Status: implemented

This document specifies the implemented `NPA-CERT-0.3.0` /
`NPA-Core-0.3.0` certificate contract emitted by the current source tree. The
fast verifier, independent Rust checker, and clean-room OCaml checker implement
this contract and retain exact read-only compatibility with v0.2.0, v0.1.2,
and v0.1 inputs. [`core-spec-v0.2.0.md`](core-spec-v0.2.0.md) remains the
version-scoped specification for v0.2 inputs; it is not the current producer
contract.

The v0.3 change gives an opaque definition a checked, locally transparent
implementation inside its defining module while keeping its imported body
sealed. It therefore changes certificate dependencies and certificate hashes,
but not the public interface meaning of an otherwise unchanged declaration.

## 1. Normative Baseline And Scope

Except where this document explicitly replaces a rule, v0.3 uses the exact
core calculus and canonical structures specified for v0.2 in
[`core-spec-v0.2.0.md`](core-spec-v0.2.0.md):

- names, levels, terms, declarations, universe constraints, typing, and
  bounded definitional equality;
- inductive, mutual-inductive, constructor, recursor, positivity, and iota
  behavior;
- builtin profiles and axiom policy;
- table canonicalization, import binding, export entries, axiom reports, and
  structural resource limits; and
- the trusted boundary of canonical certificate bytes plus independently
  recomputed checker evidence.

The v0.2 document continues to specify v0.2 only. Nothing in this document
retroactively grants same-module transparency to a v0.2 or older opaque
definition.

Surface syntax, parsing, elaboration, tactics, source maps, package metadata,
caches, replay files, theorem graphs, and AI artifacts remain outside the core
trust boundary. A source producer may spell `opaque def`, but proof acceptance
depends only on the canonical v0.3 certificate described here.

## 2. Exact Version Model

A checker recognizes exactly these four format/core pairs:

| Semantic version | `format` | `core_spec` | Dependency layout | Opaque behavior |
|---|---|---|---|---|
| `V0_3_0` | `NPA-CERT-0.3.0` | `NPA-Core-0.3.0` | tagged v0.3 entries | locally transparent, sealed on export |
| `V0_2_0` | `NPA-CERT-0.2.0` | `NPA-Core-0.2.0` | untagged interface entries | immediately opaque |
| `V0_1_2` | `NPA-CERT-0.1.2` | `NPA-Core-0.1.2` | untagged interface entries | immediately opaque |
| `V0_1` | `NPA-CERT-0.1` | `NPA-Core-0.1` | untagged interface entries | immediately opaque |

The decoder validates the complete pair before interpreting any
version-owned payload. A mixed pair, such as `NPA-CERT-0.3.0` with
`NPA-Core-0.2.0`, and every unknown pair fail at the header boundary. They are
not retried as another dependency layout.

The fast verifier reports this boundary through
`CertError::UnsupportedFormat` carrying the received strings. Independent
checkers retain their decode classifications: a format-string mismatch uses
`format_mismatch`, and a core-spec mismatch after a recognized format uses
`core_spec_mismatch`. Neither case is relabeled as a local-implementation
dependency error.

The three pre-v0.3 variants are read-only compatibility inputs. Their existing
bytes, hash domains, export shapes, and checking behavior do not change.
`V0_1` still cannot represent non-empty exported universe constraints; such a
certificate is rejected rather than projected lossy.

Every ordinary public producer now emits the exact v0.3 pair, including for a
module containing only plain definitions. V0.2 remains decoder-only
compatibility input: no caller-controlled version switch may make a current
producer emit v0.2, and changing only a v0.2 header to v0.3 is not a migration.

## 3. Common Binary Primitives And Certificate Layout

The unchanged canonical primitives are:

```text
UVar        unsigned base-128 varint, least-significant group first,
            shortest encoding only
String      UVar byte_length || exact UTF-8 bytes
Name        UVar component_count || String component ...
Hash        exactly 32 raw SHA-256 bytes
Vector<T>   UVar element_count || T ...
Option<T>   0x00, or 0x01 || T
```

The logical and binary field order remains:

```text
String format
String core_spec
Name module
Vector<ImportEntry> imports
Vector<Name> name_table
Vector<LevelNode> level_table
Vector<TermNode> term_table
Vector<Declaration> declarations
Vector<ExportEntry> export_block
AxiomReport axiom_report
Hash export_hash
Hash axiom_report_hash
Hash certificate_hash
```

Each declaration retains its v0.2 payload encoding. Immediately after that
payload it encodes, in order, its dependency vector, axiom-dependency vector,
declaration-interface hash, and declaration-certificate hash. V0.3 replaces
only the dependency-vector entry layout. All other tags and fields retain
their v0.2 bytes.

## 4. Global Reference Bytes

Both dependency variants contain the existing canonical `GlobalRef` bytes:

```text
Imported:
  0x00 || UVar import_index || UVar name_id || Hash embedded_interface_hash

Local:
  0x01 || UVar declaration_index

LocalGenerated:
  0x02 || UVar source_declaration_index || UVar name_id

Builtin:
  0x03 || UVar name_id || Hash embedded_interface_hash
```

For an imported or builtin reference, the dependency entry's separate
declaration-interface hash must equal the hash embedded in the reference.
Existing reference-origin, name-table, import-table, and generated-name checks
remain mandatory.

## 5. V0.3 Dependency Wire Encoding

The v0.3 dependency vector is:

```text
UVar dependency_count
DependencyEntry ...
```

Each entry begins with exactly one mode byte:

```text
Interface:
  0x00
  GlobalRef
  Hash declaration_interface_hash

LocalImplementation:
  0x01
  GlobalRef
  Hash declaration_interface_hash
  Hash declaration_certificate_hash
```

No other mode byte is valid. The mode byte is outside and immediately before
the `GlobalRef` tag; it is not folded into the reference encoding.

V0.2, v0.1.2, and v0.1 retain the untagged entry bytes exactly:

```text
GlobalRef
Hash declaration_interface_hash
```

Their decoders materialize those entries semantically as `Interface`. They
must not consume a mode byte, infer a local implementation commitment, or
change their re-encoded bytes.

Within a v0.3 dependency vector, entries are sorted by unsigned
lexicographic comparison of their complete encoded entry bytes, beginning
with the mode byte and including every hash. The order must be strictly
increasing, so exact duplicate entries are non-canonical. Canonical declaration
ordering treats both variants as dependency edges.

The structural preflight counts the new mode byte and the additional 32-byte
certificate hash before semantic checking or allocation. V0.3 does not raise
the existing limits:

```text
MAX_CERTIFICATE_BYTES          67,108,864
MAX_IMPORTS                         4,096
MAX_NAME_TABLE_ENTRIES          1,048,576
MAX_LEVEL_TABLE_NODES             262,144
MAX_TERM_TABLE_NODES            4,194,304
MAX_DECLARATIONS                  262,144
MAX_EXPORTS                     1,048,576
MAX_NESTED_VECTOR_ENTRIES         262,144
MAX_STRUCTURAL_DEPTH                8,192
MAX_ROOT_EXPANDED_NODES         1,048,576
MAX_CERTIFICATE_EXPANDED_NODES 16,777,216
MAX_CLOSURE_MODULES                 4,097
MAX_CLOSURE_EXPANDED_NODES      67,108,864
```

## 6. Local Implementation Dependency Validity

An untrusted `LocalImplementation` entry is decoded completely before its
reference kind and target are validated. For each entry, validation proceeds
in this deterministic order:

1. the reference is exactly `GlobalRef::Local`; otherwise use
   `wrong_reference_kind`;
2. the target index exists and is strictly earlier than the dependent
   declaration; otherwise use `target_not_earlier`;
3. the target is a definition with declared reducibility `Opaque`; otherwise
   use `target_not_opaque`;
4. the claimed interface hash equals the target declaration-interface hash;
   otherwise use `interface_hash_mismatch`; and
5. the claimed certificate hash equals the target declaration-certificate
   hash; otherwise use `certificate_hash_mismatch`.

After all individual entries pass, the checker recomputes the semantic local
transparency closure. If a required opaque target is absent, it reports
`missing_implementation_dependency`; if no required target is absent but an
extra implementation entry remains, it reports
`surplus_implementation_dependency`. Canonical byte, duplicate, header, and
ordinary interface-dependency failures are checked at their existing earlier
boundaries rather than being relabeled with an implementation reason.

Builtin, imported, local-generated, missing, current, later, reducible,
theorem, axiom, inductive, constructor, and recursor targets can never satisfy
a local implementation entry.

## 7. Semantic Local Transparency Closure

For each root declaration, the producer and every checker independently
compute the same closure:

1. scan constants in the root declaration's declared type and in its own value
   or proof;
2. for every referenced local declaration, scan its declared type;
3. additionally scan the body of a referenced reducible definition;
4. additionally scan the body of a referenced v0.3 current-module opaque
   definition;
5. never scan a referenced theorem proof; and
6. never scan an imported opaque body or recover one from producer state,
   source, cache, replay, or metadata.

Every reached current-module opaque definition contributes exactly one
`LocalImplementation` entry. Reachability includes paths through declared
types, reducible aliases, and other locally transparent opaque bodies. A
reference used only through a stable theorem interface does not cause the
referenced theorem's proof to be traversed and therefore does not, by itself,
add an implementation entry.

The traversal is iterative, not recursive in certificate depth. Its worklist
and visited sets use deterministic reference ordering. Per-root and
whole-certificate work are charged to the existing expanded-node and
structural-depth budgets; exhaustion rejects rather than truncating the
closure.

The full set of implementation entries must equal the recomputed reached set.
The checker does not attempt to observe whether a successful conversion
actually unfolded a reached opaque body.

## 8. Current-Module Environment Transition

V0.3 declarations are checked sequentially in canonical dependency order.
Imports are reconstructed only from verified export entries.

For an opaque definition, the checker:

1. checks its type under the ordinary declaration rules;
2. checks its body against that type under the ordinary deterministic body,
   conversion-fuel, structural, and universe limits while the declaration is
   still `Opaque` in trusted data;
3. on success only, retains the original opaque declaration for certificate,
   export, hash, and report purposes; and
4. inserts a private reducible copy into the v0.3 current-module checking
   environment used for later declarations.

A failed type or body check inserts no view. The reducible copy is not a second
certificate declaration, is never exported, and is not available after
import. Plain reducible definitions retain their existing checking and export
behavior.

When an opaque export is imported, its type, universe context, name,
reducibility, interface hash, and axiom dependencies remain available, but its
body and body hash do not. A kernel representation that is internally
axiom-shaped does not change its semantic declaration kind from definition to
axiom.

V0.2 and older inputs do not perform step 4. Their opaque definitions remain
opaque immediately, including for later declarations in the same certificate.

## 9. Public Interface Projection And Export

The v0.3 declaration dependency vector is certificate-private evidence. The
public declaration-interface payload retains the pre-v0.3 interface-dependency
encoding with no mode byte and no declaration-certificate hash.

For each local implementation entry:

- if its reference is required by the declaration's existing public payload,
  project it as the untagged `GlobalRef || declaration_interface_hash` entry;
- if it exists only because of the semantic local transparency closure, omit
  it from the public projection.

The public payload includes the same portions as v0.2: a declaration type,
the exported body of a reducible definition, public inductive artifacts, and
the applicable axiom dependencies. An opaque body and theorem proof are not
public payloads.

An opaque definition's declaration certificate contains its checked body. Its
export entry contains `Opaque` reducibility and its public type but has no body
and no body hash. A reducible definition continues to export its body.

## 10. Hash Domains And Payloads

All core hashes are:

```text
SHA-256(exact ASCII domain bytes || canonical payload bytes)
```

V0.3 uses these changed domains:

```text
NPA-DECL-CERT-0.3.0
NPA-MODULE-CERT-0.3.0
```

The v0.3 declaration-certificate payload retains the v0.2 declaration-kind
field order, but every dependency vector inside it uses the tagged v0.3 entry
bytes. It starts with the declaration-interface hash and then commits to the
existing kind-specific body/proof or inductive material, the complete
certificate dependency vector, and the existing axiom-dependency material.
The v0.3 module-certificate payload is the complete canonical v0.3 certificate
from the header through `axiom_report_hash`, excluding only the final
`certificate_hash` field.

These domains and payload rules remain unchanged:

```text
NPA-DECL-IFACE-0.1
NPA-MODULE-EXPORT-0.2.0
NPA-AXIOM-REPORT-0.1
NPA-AXIOM-POLICY-HASH-0.1
NPA-LEVEL-0.1
NPA-TERM-0.1
NPA-CORE-EXPR-0.1
NPA-UNIVERSE-CONSTRAINTS-0.1
NPA-GEN-REC-SIG-0.1
NPA-GEN-COMP-RULE-0.1
```

The interface hash uses the projected untagged dependencies from Section 9.
The module export hash uses the byte-identical v0.2 export-block encoding.
Name, level, term, expression, universe-constraint, and axiom-report payloads
do not acquire a v0.3 mode field.

`NPA-AXIOM-POLICY-CANONICAL-BYTES-0.1` also remains the exact prefix inside
the payload hashed by `NPA-AXIOM-POLICY-HASH-0.1`; it is a payload tag, not a
second hash domain. Names continue to be encoded directly into the applicable
canonical payload and do not have a separate name-hash domain.

Compatibility inputs retain their original domains:

```text
v0.2 declaration certificate  NPA-DECL-CERT-0.1
v0.2 module certificate       NPA-MODULE-CERT-0.2.0
v0.2 module export            NPA-MODULE-EXPORT-0.2.0

v0.1.2 declaration certificate NPA-DECL-CERT-0.1
v0.1.2 module certificate      NPA-MODULE-CERT-0.1.2
v0.1.2 module export           NPA-MODULE-EXPORT-0.1.2

v0.1 declaration certificate  NPA-DECL-CERT-0.1
v0.1 module certificate       NPA-MODULE-CERT-0.1
v0.1 module export            NPA-MODULE-EXPORT-0.1
```

Every other retained domain above applies unchanged to all four semantic
versions whenever that payload exists.

With unchanged transitive axiom dependencies, changing only an opaque body:

- changes that definition's declaration-certificate hash;
- changes the module-certificate hash;
- changes or invalidates each later declaration whose semantic closure reaches
  the definition;
- does not change the definition's declaration-interface hash or the module
  export hash; and
- does not change an unrelated declaration that uses only a stable theorem
  interface.

If the body's transitive axiom dependencies change, the applicable public
interface and export identities change under their retained domains.

## 11. Canonical Ordering

Canonical declaration ordering includes both dependency variants. A local
implementation target must precede every declaration whose semantic closure
reaches it. A propagated implementation edge is valid only when it follows a
real path through a root type/value/proof, a referenced local type, or a
reducible/current-module-opaque body. It does not create independent
source-order authority.

Existing cycle and forward-reference rejection remains in force. V0.3 does
not enable recursion or forward declarations. Dependency vectors use the
strict complete-byte order from Section 5 after declaration indexes and hashes
have been finalized.

## 12. Compatibility And Migration

A v0.2 certificate is never upgraded by changing only its two header strings.
It must be rebuilt, recanonicalized, rehashed, and verified under v0.3 rules.
Even a plain-only rebuild receives new certificate identity because the header
and certificate hash domains change; its public export identity remains stable
when its public payload and axiom dependencies are unchanged.

A package closure may contain v0.2 and v0.3 modules simultaneously. Each
module is decoded and verified under its own exact header pair. A package-wide
profile cannot replace that per-module pair.

The package identifiers `npa.core.v0.1`,
`npa.certificate.canonical.v0.1`, `npa.package.v0.1`, and
`npa.package.lock.v0.1` are independent package-contract axes. They are not
aliases for `NPA-Core-*` or `NPA-CERT-*`, and v0.3 does not silently rename
them or add unversioned pair fields to the package lock.

The `npa.package.build_check_cache.v0.2` key records the exact emitted pair as
`output_certificate_format` / `output_core_spec`, separately from the package
profiles. `npa.package.audit_cache.v0.2` keys and
`npa.package.verified_export_summary.v0.2` module rows similarly record each
decoded module's `certificate_format` / `core_spec`. A mixed v0.2/v0.3 package
therefore retains each module's actual pair instead of inheriting a package
default. Pair-unaware or mismatched entries are misses, never trusted evidence.
No cache, source interface, replay artifact, or producer side channel may
restore an imported opaque body.

Package artifact refresh rebuilds selected stale modules under v0.3 and then
rebinds and source-free revalidates the complete affected certificate chain.
When an opaque body changes without changing its stable public interface, an
unrelated interface-only consumer may be reused only after that rebind and
revalidation. Refresh never performs a header-only upgrade.

The first delivery's Lean exporter may translate a selected v0.3 closure only
if it contains no local implementation dependency. Otherwise it fails before
output staging; it must not weaken an opaque definition to a reducible Lean
definition, invent an axiom, or emit a partial tree.

## 13. Checker Result Identity

After exact header validation, fast `VerifiedModule` and independent
`ReferenceCheckedModule` summaries retain the actual input
`certificate_format` and `core_spec`. Those values are distinct from an
independent checker's advertised current capability pair.

The Rust reference checker and OCaml external checker use the strict envelope:

```text
npa.independent-checker.checker_raw_result.v2
```

Every v2 result contains capability fields `certificate_format` and
`core_spec` immediately after `checker_build_hash`. Once an exact input header
pair is known, it also contains `input_certificate_format` and
`input_core_spec` immediately before `status`, including for semantic or hash
rejection. Both input fields are absent only when header validation fails
before a pair is known; they are omitted, never encoded as `null`. A checked
result always has both.

The remaining raw-result v1 field order is preserved. Duplicate and unknown v2
fields reject. The runner independently decodes the requested certificate
header and rejects a claimed input-pair mismatch. Raw-result v1 is valid only
under explicitly historical checker bindings; a checker 0.3.0 binding cannot
adopt it.

`npa.independent-checker.machine_check_result.v1` retains its schema because
its envelope does not gain these capability fields. The Core v0.3 capability
migration originally retained `npa.package.command_result.v0.3` for the same
reason. The later `npa-cli 0.8.x` operational fuel-diagnostic migration
advances current package results to `npa.package.command_result.v0.4`; exact
v0.3 results remain historical read-only compatibility and are never
relabeled. A package command's per-module verification record continues to
retain the actual input pair.

## 14. Required Conformance Vectors

The committed conformance corpus contains compact canonical vectors with these
minimum cases and expectations:

| Vector | Requirement |
|---|---|
| `v3_plain_reducible` | accepted; tagged interface dependencies; reducible body remains exported |
| `v3_opaque_unused` | accepted; body checked, absent from export, no later implementation edge |
| `v3_opaque_direct` | accepted; later declaration carries the exact opaque interface and certificate hashes |
| `v3_opaque_alias_chain` | accepted; closure follows a reducible alias and records the opaque implementation |
| `v3_opaque_declared_type` | accepted; closure follows a referenced local declaration type |
| `v3_nested_opaque` | accepted; closure follows one locally transparent opaque body to another |
| `v3_theorem_interface_only` | accepted without traversing the referenced theorem proof or adding an unrelated implementation edge |
| `v3_imported_opaque` | accepted only without an imported body; downstream body-dependent conversion rejects |
| `v3_wrong_reference_kind` | builtin, imported, and local-generated implementation targets reject with `wrong_reference_kind` |
| `v3_target_not_earlier` | current, later, and missing local targets reject with `target_not_earlier` |
| `v3_target_not_opaque` | reducible and non-definition targets reject with `target_not_opaque` |
| `v3_interface_hash_mismatch` | forged target interface hash rejects with the named reason |
| `v3_certificate_hash_mismatch` | stale or forged target certificate hash rejects with the named reason |
| `v3_missing_implementation` | omitted reached opaque target rejects with `missing_implementation_dependency` |
| `v3_surplus_implementation` | extra valid-looking but unreached opaque target rejects with `surplus_implementation_dependency` |
| `v3_unknown_or_truncated_tag` | structural/decode rejection occurs before semantic acceptance |
| `mixed_header_pair` | every v0.3/v0.2 mixed format/core header rejects before dependency decoding |
| `v2_v1_2_v1_compatibility` | prior canonical bytes and verdicts remain unchanged with immediate opacity |
| `header_only_upgrade` | replacing only the v0.2 header with v0.3 rejects |
| `opaque_body_hash_invariance` | body-only change alters certificate identities but preserves interface/export identity when axiom dependencies are stable |
| `opaque_axiom_drift` | body axiom-dependency change updates the applicable interface/export identities |
| `reached_opaque_stale_cache` | cached later declaration whose closure reaches a changed opaque body rejects or is recomputed against the new certificate hash |
| `unrelated_opaque_body_reuse` | stable theorem-interface consumer remains dependency-selectively reusable only after full-chain rebind and revalidation |

Fast, independent Rust, and clean-room OCaml checking must agree on canonical
bytes, acceptance or rejection, all applicable hashes, and structured error
kind/reason for every vector. Compatibility vectors remain byte-identical to
their historical fixtures.

## 15. Source Surfaces And Author Guidance

Both Human Surface and Machine Surface accept the same declaration modifier;
Machine Surface retains its existing fully explicit term grammar:

```text
-- Human Surface
opaque def Eval.cachedInvariant (x : Input) : Result :=
  expensiveEvaluation x

-- Machine Surface
opaque def Eval.cachedInvariant (x : Input) : Result :=
  Eval.expensiveEvaluation x
```

The grammar is `definition-item ::= ["opaque"] "def"
declaration-signature ":=" term`. The modifier is invalid on theorems, axioms,
inductives, or another `opaque`; Human equation-style `opaque def ... where`
is not part of this surface. Frontend diagnostics identify these syntax cases.
Certificate diagnostics for forged or inconsistent local implementation edges
use the stable reasons `wrong_reference_kind`, `target_not_earlier`,
`target_not_opaque`, `interface_hash_mismatch`,
`certificate_hash_mismatch`, `missing_implementation_dependency`, and
`surplus_implementation_dependency`.

Place a substantial opaque implementation and its specification theorems in
the smallest semantically appropriate leaf module. State stable semantic
properties or selected computation laws; do not publish a whole-body equality
theorem that repeats the implementation expression and defeats the abstraction
boundary. The defining module can unfold the checked private body, so opacity
does not promise faster checking there. The expected performance and stability
benefits begin in importing modules, where the body is sealed and consumers
must use the specification API.

## 16. Acceptance Boundary

The current implementation conforms to this specification because:

- it accepts only the four exact header pairs and dispatches version behavior
  before version-owned decoding;
- v0.3 dependency tags, bytes, ordering, projection, closure, and hashes match
  this document;
- every opaque body is checked under ordinary limits before any local view is
  installed;
- v0.3 later declarations can use the private local view, while imports and
  all pre-v0.3 versions remain unable to unfold it;
- every checker independently reconstructs and validates the same closure and
  environment transition;
- the required conformance and compatibility vectors pass source-free; and
- the full fast, independent Rust, and clean-room OCaml implementation gates
  have passed.

This establishes the Core v0.3 implementation boundary. It does not by itself
claim the complete opaque-definition feature Definition of Done: Lean exporter
representability/pinning and final performance/release qualification remain
separate integration work.
