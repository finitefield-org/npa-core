# NPA Core Implementation Specification v0.4.0

Status: frozen implementation target for the term-level `let` removal. The
v0.4 producer and checkers are not claimed to conform until the implementation
and acceptance milestones in the removal plan are complete.

This document is the self-contained normative contract for the first let-free
NPA core and canonical certificate format. The words **must**, **must not**,
**should**, and **may** are normative. Older core specifications are historical
records only; an implementation of this specification must not consult an old
specification to decide current bytes or semantics.

The only current certificate header pair is:

```text
format:    NPA-CERT-0.4.0
core_spec: NPA-Core-0.4.0
```

The v0.4 calculus contains exactly six term constructors: `Sort`, `BVar`,
`Const`, `App`, `Lam`, and `Pi`. It contains no term-level local definition,
no value-bearing local-context entry, and no zeta reduction. Module-level
`def` and `opaque def`, lambda abstraction, application, beta reduction,
global delta reduction, and recursor iota reduction remain supported.

## 1. Scope And Trust Boundary

The implementation is divided into three semantic lanes:

```text
npa-kernel and npa-cert
  Core data, typing, reduction, canonical production, hashing, import
  resolution, policy checking, and the fast verifier.

npa-checker-ref
  A source-free Rust checker with its own decoder, hash verification, and
  semantic implementation.

npa-checker-ext
  A clean-room source-free OCaml checker with an independent decoder, hash
  verification, and semantic implementation.
```

Trusted proof evidence consists of canonical `.npcert` bytes, independently
recomputed hashes and axiom reports, and successful checker verdicts under the
required package policy. Source text, parsers, elaborators, tactics, AI output,
replay records, theorem indexes, metadata, caches, diagnostic text, and source
maps are untrusted authoring aids. A cache hit is not proof evidence.

All three semantic lanes must enforce this document. The independent checkers
may share fixture bytes and the case matrix specified here, but must not share
Rust semantic code or trust a producer-generated semantic summary.

## 2. Exact Version And Header Dispatch

### 2.1 Single Current Pair

A v0.4 implementation emits only the exact current pair. It accepts only that
pair for semantic checking. There is no caller-controlled compatibility mode,
fallback decoder, header upgrade, or per-module old-format selection.

The following strings are old certificate/core identities:

```text
NPA-CERT-0.3.0    NPA-Core-0.3.0
NPA-CERT-0.2.0    NPA-Core-0.2.0
NPA-CERT-0.1.2    NPA-Core-0.1.2
NPA-CERT-0.1      NPA-Core-0.1
```

They are invalid as v0.4 input even when paired with their historical mate.
An old certificate must be rebuilt from accepted let-free source and rehashed;
editing only its header is invalid.

### 2.2 Complete Known-Header Matrix

Rows are `format`; columns are `core_spec`. `accept` means continue decoding.
Every `reject` occurs before the module name, imports, tables, declarations,
hashes, or body-dependent allocation is decoded.

| format \ core_spec | `NPA-Core-0.4.0` | `NPA-Core-0.3.0` | `NPA-Core-0.2.0` | `NPA-Core-0.1.2` | `NPA-Core-0.1` |
| --- | --- | --- | --- | --- | --- |
| `NPA-CERT-0.4.0` | accept | reject | reject | reject | reject |
| `NPA-CERT-0.3.0` | reject | reject | reject | reject | reject |
| `NPA-CERT-0.2.0` | reject | reject | reject | reject | reject |
| `NPA-CERT-0.1.2` | reject | reject | reject | reject | reject |
| `NPA-CERT-0.1` | reject | reject | reject | reject | reject |

Unknown strings follow the same fail-closed rule. Header validation has this
deterministic order:

1. decode the canonical `format` string;
2. decode the canonical `core_spec` string as bounded header data, without
   selecting semantics from it;
3. if `format` is not exactly `NPA-CERT-0.4.0`, reject;
4. if `core_spec` is not exactly `NPA-Core-0.4.0`, reject; and
5. only then decode the module name or any remaining certificate field.

The fast decoder reports its structured unsupported-format result containing
both observed strings. The Rust and OCaml independent decoders report
`format_mismatch` for step 3 and `core_spec_mismatch` for step 4. This ordering
is part of the conformance contract; a mixed pair must not reach an old body
decoder.

Every imported certificate in a package closure is checked by the same rule.
A current root cannot make an old import acceptable through an export hash,
package profile, cache entry, lock entry, or checker result.

### 2.3 Independent Package Axes

The following package-contract axes retain their current identities because
they do not name the core syntax or certificate epoch:

```text
npa.package.v0.1
npa.core.v0.1
npa.kernel.v0.1
npa.certificate.canonical.v0.1
npa.checker.reference.v0.1
npa.package.lock.v0.1
```

They are not aliases for the two header strings. Every cache, lock, result, or
package record that carries a certificate pair must still carry the exact
v0.4 values.

## 3. Canonical Binary Primitives And Layout

Canonical binary values use:

```text
Byte        one octet
UVar        unsigned base-128 varint, least-significant group first,
            shortest encoding only
String      UVar byte_length || exact UTF-8 bytes
Name        UVar component_count || String component ...
Hash        exactly 32 raw SHA-256 bytes
Vector<T>   UVar element_count || T ...
Option<T>   0x00, or 0x01 || T
```

Overlong varints, integer overflow, invalid UTF-8, invalid option tags,
truncation, trailing bytes, and lengths beyond the resource limits reject.
The canonical certificate field order is:

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

After decoding, a checker independently re-encodes the certificate. Any byte
difference is non-canonical and rejects.

### 3.1 Imports

Each `ImportEntry` is:

```text
Name module
Hash export_hash
Option<Hash> certificate_hash
```

Import entries are sorted by canonical module name and unique. Normal mode
resolves by module plus export hash; a present certificate hash must also
match. High-trust mode requires the imported module to have been verified in
the current session with the exact certificate hash. Neither mode may use
source, a theorem index, metadata, or a stale summary to supply an import.

The name table is sorted by complete canonical `Name` bytes and duplicate-free.
All `name_id` fields are indices into that table.

## 4. Names, Levels, And Terms

### 4.1 Names

Global names are dotted ASCII component paths:

```text
DeclarationName = Component ("." Component)*
Component       = [A-Za-z_][A-Za-z0-9_']*
```

Components are non-empty. Operator names, embedded dots, invalid UTF-8, and
Unicode lookalikes are rejected. Binder names are untrusted display data and
are absent from the certificate term DAG; binding uses de Bruijn indices.

### 4.2 Universe Levels

The level grammar is:

```text
Level ::=
  zero
| succ Level
| max Level Level
| imax Level Level
| param Name

Prop   = Sort zero
Type u = Sort (succ u)
```

Universe parameters are declared, ASCII names that are sorted, unique, and
free of unresolved meta-like names. The level table uses only backward table
references and these bytes:

```text
0x00                         Zero
0x01 || UVar level_id        Succ
0x02 || UVar lhs || UVar rhs Max
0x03 || UVar lhs || UVar rhs IMax
0x04 || UVar name_id         Param
```

Level normalization is deterministic:

```text
max u u         => u
max zero u      => u
max u zero      => u
max n m         => the larger numeral when both are numerals
max u v         => recursively normalized operands in canonical order

imax u zero     => zero
imax u (succ v) => max u (succ v)
```

Other `imax` values remain canonical `imax` nodes after child normalization.

### 4.3 Six-Term Calculus

The complete core grammar is:

```text
Term ::=
  Sort Level
| BVar u32
| Const Name [Level]
| App Term Term
| Lam binder : Term, Term
| Pi  binder : Term, Term
```

There is no seventh constructor. In particular, the calculus has no local
definition, local value, hole, unresolved metavariable, implicit argument,
notation, tactic block, macro, or source-level match constructor.

The local context is assumption-only:

```text
LocalEntry = Assumption { type: Term }
```

A context entry has no value field and cannot trigger unfolding. Multiple
local computations are represented by substitution, lambda/application,
proved local lemmas, or module-level declarations.

## 5. Universe Contexts

Declarations may carry sorted, duplicate-free constraints:

```text
Level <= Level
Level = Level
```

The checker validates declared and normalized parameters, well-formed and
normalized levels, canonical constraint order, uniqueness, and satisfiability.
Its conservative difference-constraint fragment uses atoms consisting of
`zero`, declared parameters, and finite successor offsets.

A finite `max` on the left decomposes into obligations for each atom. A
symbolic left `imax a b` uses the same sound upper-bound approximation as
`max a b`, because `imax a b <= max a b`. A symbolic `imax` on the right, a
stored constraint with multiple right atoms, nonlinear arithmetic, and other
unsupported shapes reject. Equality is checked in both directions.

For an entailment obligation, but not for a stored assumption, a finite `max`
may appear on the right. Each left atom must be bounded by at least one right
atom in the closed difference relation. Constant lookup substitutes supplied
levels into the referenced public constraints and requires the current
universe context to entail every result.

Definitional equality compares levels only by deterministic normalization; it
does not use declaration constraints to invent additional level equalities.

## 6. Typing And Conversion

Typing is inference plus conversion checking:

```text
infer(ctx, env, term) -> type
check(ctx, env, term, expected)
  succeeds exactly when infer(term) is definitionally equal to expected
```

The rules are:

```text
Sort u
  has type Sort (succ u).

BVar i
  has the lifted type of the i-th assumption in ctx.

Const c levels
  checks c's universe arity, substitutes levels into its public signature,
  and checks all instantiated universe constraints.

Pi A B
  checks A and B inhabit sorts and computes the result sort with imax.

Lam A body
  checks A is a type, infers body under Assumption(A), and returns Pi A body_ty.

App f a
  weak-head reduces f's type to Pi A B, checks a against A, and substitutes a
  into B.
```

The local context extension used by `Lam` and `Pi` is always an assumption.
Typing has no local-definition rule.

## 7. Definitional Equality And Reduction

Conversion is deterministic, bounded, and fail-closed on fuel or structural
resource exhaustion. It is generated by:

```text
alpha equivalence through de Bruijn representation
beta reduction for App (Lam A body) argument
delta reduction for permitted global definition bodies
iota reduction for generated recursors on constructor-headed major premises
```

There is no zeta rule, no local-definition lookup, and no `Let` head. The
reduction profile identity is exactly:

```text
beta-delta-iota.v0.1
```

`beta-delta-iota-zeta.v0.1` is not an alias. Eta conversion, proof irrelevance,
theorem-proof unfolding, imported opaque-body unfolding, axiom unfolding, and
equality-proof normalization are not definitional equality.

The checker must not compensate for an expensive conversion by silently
raising limits. Proofs should cross named theorem boundaries rather than rely
on large definitional reductions.

## 8. Declarations And Current-Module Opacity

Source certificate declarations are:

```text
Axiom
Def { reducibility = Reducible | Opaque }
Theorem
Inductive
MutualInductiveBlock
```

Constructors and recursors are generated environment artifacts rather than
independent source declarations.

An axiom type must inhabit a sort. A definition's type must inhabit a sort and
its value must check against that type. A theorem's type must inhabit a sort
and its proof must check against the type. Theorem proofs and opaque bodies are
not exported. Reducible definition bodies are exported.

Declarations are checked in canonical dependency order. Cycles, forward local
references, duplicate names, and non-canonical order reject.

V0.4 retains the v0.3 current-module opacity rule. After an opaque definition's
type and body have checked successfully, the original opaque declaration stays
in certificate and export data while a private reducible view becomes
available to later declarations in the same certificate. The view:

- is inserted only after successful checking;
- is not a second declaration;
- is not exported;
- is never reconstructed for an import; and
- does not change the declaration kind or public reducibility.

Thus `opaque def` is transparent to later declarations in its defining module
and sealed after export. This behavior is global delta reduction in a private
current-module environment; it is unrelated to, and does not preserve, zeta
reduction.

### 8.1 Declaration Bytes

All name, level, and term operands below are `UVar` table indices. A universe
parameter list is `Vector<name_id>`. A universe-constraint list is:

```text
UVar count
(UVar lhs_level_id || relation || UVar rhs_level_id) ...

relation = 0x00 for <=
relation = 0x01 for =
```

The declaration payload tags and field order are:

```text
0x00 Axiom
  name || universe_params || type

0x10 AxiomConstrained
  name || universe_params || universe_constraints || type

0x01 Def
  name || universe_params || type || value || reducibility

0x11 DefConstrained
  name || universe_params || universe_constraints
       || type || value || reducibility

0x02 Theorem
  name || universe_params || type || proof || opacity

0x12 TheoremConstrained
  name || universe_params || universe_constraints
       || type || proof || opacity

0x03 Inductive
  name || universe_params || params || indices || sort
       || constructors || optional_recursor

0x13 InductiveConstrained
  name || universe_params || universe_constraints
       || params || indices || sort || constructors || optional_recursor

0x04 MutualInductiveBlock
  block_name || universe_params || universe_constraints
             || inductive_members
```

`params` and `indices` are vectors of binder-type term IDs. A constructor is
`name_id || type_term_id`. A recursor option is `0x00`, or:

```text
0x01 || name_id || universe_params || type_term_id
     || UVar minor_start || UVar major_index
```

Each mutual member contains its name, binder-type parameter and index vectors,
sort, constructor vector, and optional recursor in that order.

`reducibility` is `0x00` for `Reducible` and `0x01` for `Opaque`. The only
theorem `opacity` byte is `0x00` for `Opaque`; no transparent theorem variant
exists.

Immediately after every declaration payload, the certificate encodes:

```text
Vector<DependencyEntry> dependencies
Vector<AxiomRef> axiom_dependencies
Hash declaration_interface_hash
Hash declaration_certificate_hash
```

An `AxiomRef` is `GlobalRef || UVar name_id || Hash
declaration_interface_hash`. Both dependency and axiom vectors are strictly
canonical and duplicate-free.

## 9. Inductives, Positivity, And Iota

V0.4 supports simple and indexed families, mutual inductive blocks, and
approved nested recursive occurrences through structurally recognized `List`,
`Option`, and `Prod` functors. It does not support generic coinductives.

An inductive declaration carries its name, universe parameters and
constraints, uniform parameters, indices, result sort, constructors, and an
optional recursor description. A constructor must end in the target family
with the canonical parameters and expected universe arguments.

Non-parameter constructor domains must satisfy the declared family universe
bound. A family whose normalized sort is syntactically `Prop` is exempt from
that bound, and its recursor motive must return `Prop`; singleton Prop-to-Type
exceptions are not implemented.

Positivity permits direct recursive fields, mutual recursive fields, and
recursive occurrences under the exact approved positive functors. It rejects
negative domains, higher-order negative occurrences, unknown or name-only
functors, and unsupported aliases.

The recursor's major premise is its final binder. Iota fires when that premise
weak-head reduces to a constructor-headed term. Recursive fields receive the
corresponding recursive call, and mutual recursors select the recursor for the
matching family.

The builtin-enabled core environment contains exactly:

```text
Nat, Nat.zero, Nat.succ, Nat.rec
Eq, Eq.refl, Eq.rec
```

`Nat` and `Eq` arise from inductive declarations and generated artifacts.
`Eq.rec` is the only builtin axiom and therefore appears in every affected
axiom report. Its exact standard-policy treatment is specified in Section
10.2; builtin status never bypasses reference-origin or interface-hash checks.
Certificate construction and checking begin with an empty environment and
materialize only members of this exact set that are reached through a
canonical `Builtin` reference. The empty authoring profile contributes no
builtins; the builtin-enabled authoring profile contributes this set. A
profile choice cannot add another builtin or change any builtin interface
hash, and it does not weaken certificate reference validation.

## 10. References And Dependency Entries

`GlobalRef` bytes are:

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

V0.4 retains the v0.3 tagged declaration-dependency layout:

```text
Vector<DependencyEntry>

Interface:
  0x00 || GlobalRef || Hash declaration_interface_hash

LocalImplementation:
  0x01 || GlobalRef || Hash declaration_interface_hash
       || Hash declaration_certificate_hash
```

No other dependency mode is valid. Complete encoded entries are sorted in
strict unsigned lexicographic byte order and duplicates reject.

A `LocalImplementation` reference must target an earlier local opaque
definition and must carry the exact interface and declaration-certificate
hashes. The semantic closure starts from the root declaration's type and own
value or proof, follows referenced local types, reducible bodies, and private
current-module opaque bodies, never follows theorem proofs or imported opaque
bodies, and records every reached current-module opaque definition exactly
once. Missing and surplus entries reject.

Validation order is reference kind, earlier target, opaque-definition kind,
interface hash, certificate hash, then exact closure equality. The stable
semantic reasons are `wrong_reference_kind`, `target_not_earlier`,
`target_not_opaque`, `interface_hash_mismatch`,
`certificate_hash_mismatch`, `missing_implementation_dependency`, and
`surplus_implementation_dependency`.

The public declaration-interface projection uses the untagged bytes
`GlobalRef || declaration_interface_hash`. A local implementation entry needed
only for private semantic transparency is omitted from the public projection.

### 10.1 Export Block And Axiom Report

The v0.4 export block retains the v0.3/v0.2 layout. Each sorted, unique entry
is:

```text
UVar name_id
Byte export_kind
Vector<name_id> universe_params
Vector<UniverseConstraintSpec> universe_constraints
UVar type_term_id
Option<UVar> body_term_id
Hash type_hash
Option<Hash> body_hash
Option<reducibility> reducibility
Option<opacity> opacity
Hash declaration_interface_hash
Vector<AxiomRef> axiom_dependencies
```

Export kinds are `0x00` Axiom, `0x01` Def, `0x02` Theorem, `0x03` Inductive,
`0x04` Constructor, and `0x05` Recursor. Only a reducible definition exports a
body and body hash. The option encoding is the common `0x00`/`0x01 || value`
encoding from Section 3.

The axiom report is:

```text
UVar per_declaration_count
(UVar declaration_index
 || Vector<AxiomRef> direct_axioms
 || Vector<AxiomRef> transitive_axioms) ...
Vector<AxiomRef> module_axioms
```

The active v0.4 core has no optional core features. A non-empty feature report
would append `String "core_features" || Vector<String> features`; because no
feature is supported, ordinary v0.4 verification rejects a non-empty report.
Structural audit is not semantic acceptance.

### 10.2 Axiom And Feature Verification Policy

Every checker recomputes the root and imported axiom reports before applying
policy. A policy is applied to every reported axiom in the complete import
closure, not only to axioms named by the root module. Names are canonical
dotted `Name` values. An imported axiom may match either its exact exported
name or its exact module-qualified name, but only after its reference origin,
export membership, and declaration-interface hash have been verified.

The canonical fast-verifier `AxiomPolicy` has these exact rules:

- if `deny_sorry` is true, an axiom name containing the lowercase ASCII bytes
  `sorry` rejects before allowlist admission;
- Normal mode with an empty allowlist permits every remaining axiom;
- Normal mode with a non-empty allowlist requires every remaining axiom to be
  in that exact set; and
- HighTrust mode always requires every remaining axiom to be in that exact
  set.

The required source-free release policy is stricter: `deny_sorry` and custom-
axiom denial are both enabled, so every nonstandard axiom must be exactly
allowlisted. Its only standard exception is `Eq.rec`, and the exception
matches only either the canonical `Builtin` reference whose exact interface
hash is defined in Section 13 or an exact imported export qualified as
`Std.Logic.Eq.rec` with a verified origin and interface hash. A local axiom
merely named `Eq.rec`, a differently qualified export, or a matching name with
the wrong hash is not the exception. A checker whose policy type has no
separate standard-exception flag must first enforce those origin and hash
conditions and only then represent that verified reference in its effective
allowlist. Adding the `Eq.rec` name alone is insufficient. A package may still
admit a local axiom by explicitly allowlisting it as a custom axiom, but that
admission is not the standard exception and must not weaken custom-axiom
denial for any other name.

No v0.4 core feature exists, so the effective supported-feature set is empty
in every mode and every non-empty feature report rejects. Policy configuration
is verifier input rather than certificate data; it cannot alter the canonical
certificate bytes or make a mismatched header, hash, reference, report, or
semantic check acceptable.

## 11. Term-Table Wire Encoding

The term table is `UVar node_count` followed by exactly `node_count` nodes.
All `TermId` and `LevelId` values are zero-based table indices. A child
`TermId` in a term node and a child `LevelId` in a level node must point to a
strictly earlier entry of the same table. A term node's `LevelId` may name any
valid entry in the already decoded level table. A `BVar` payload is a de
Bruijn index and is not a table reference.

The six and only six term-node encodings are:

| Tag | Constructor | Bytes after tag |
| --- | --- | --- |
| `0x00` | `Sort` | `UVar level_id` |
| `0x01` | `BVar` | `UVar de_bruijn_index`, bounded to `u32` |
| `0x02` | `Const` | `GlobalRef || UVar level_count || UVar level_id ...` |
| `0x03` | `App` | `UVar function_term_id || UVar argument_term_id` |
| `0x04` | `Lam` | `UVar binder_type_term_id || UVar body_term_id` |
| `0x05` | `Pi` | `UVar binder_type_term_id || UVar body_term_id` |

Binder display names are absent. Every other byte value is an unsupported term
encoding.

### 11.1 Permanently Retired `0x06`

`0x06` is permanently unassigned in v0.4. It must not be reused for another
constructor, extension escape, compatibility envelope, or reserved payload.

After reading a term-node tag byte equal to `0x06`, a decoder must reject
immediately. It must not read any former child index, allocate from a claimed
child length, construct an intermediate node, or defer rejection to
reachability, normalization, hashing, or semantic checking. This applies to a
reachable node, an unused table entry, truncated bytes, and bytes followed by
maliciously large varints.

The fast decoder returns its structured unsupported-encoding result with
`tag = 0x06`. The Rust and OCaml independent decoders return `unknown_tag`
with `tag = 0x06`. A high-level package layer may wrap the decode failure, but
must preserve the structured reason and tag.

## 12. Canonical Structure And Resource Limits

Name, level, term, declaration, dependency, export, constraint, and axiom
vectors use their prescribed canonical ordering and reject duplicates. All
table entries must be reachable from the certificate roots; unreachable nodes
do not create a compatibility hiding place. Structural analysis is iterative
where input depth could exhaust the host call stack.

The v0.4 limits are unchanged:

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

Rejecting `0x06` before child reads is required even when the remaining bytes
would fit these limits.

## 13. Hash Domains And Stability Rules

Every core hash is:

```text
SHA-256(exact ASCII domain bytes || canonical payload bytes)
```

V0.4 introduces these semantic-epoch domains:

```text
NPA-DECL-CERT-0.4.0
NPA-MODULE-CERT-0.4.0
```

These domains retain their exact spelling and payload grammar:

```text
NPA-TERM-0.1
NPA-CORE-EXPR-0.1
NPA-KERNEL-CORE-EXPR-0.1
NPA-DECL-IFACE-0.1
NPA-MODULE-EXPORT-0.2.0
NPA-AXIOM-REPORT-0.1
NPA-LEVEL-0.1
NPA-UNIVERSE-CONSTRAINTS-0.1
NPA-AXIOM-POLICY-HASH-0.1
NPA-GEN-REC-SIG-0.1
NPA-GEN-COMP-RULE-0.1
NPA-BUILTIN-INTERFACE-0.1
```

`NPA-AXIOM-POLICY-CANONICAL-BYTES-0.1` remains the exact prefix inside the
policy payload; it is not a second hash domain.

The following notation fixes the retained payload grammars. `N(i)` means the
canonical `Name` bytes for name-table entry `i`, not the `UVar` bytes of `i`.
`L(i)` and `T(i)` mean the 32-byte hashes of level-table and term-table entry
`i`. `V<X>` means the canonical `UVar` count followed by the listed `X`
elements. `I` is the public, untagged dependency vector
`V<GlobalRef || declaration_interface_hash>`. `D` is the full tagged v0.4
dependency vector from Section 10. `A` is the exact `Vector<AxiomRef>` from
Section 8.1. Concatenation below is in the displayed order with no implicit
separator.

The `NPA-LEVEL-0.1` payload for a table node is exactly:

```text
Zero         0x00
Succ         0x01 || L(inner)
Max          0x02 || L(lhs) || L(rhs)
IMax         0x03 || L(lhs) || L(rhs)
Param        0x04 || N(name)
```

The `NPA-TERM-0.1` payload for a table node is exactly:

```text
Sort         0x00 || L(level)
BVar         0x01 || UVar index
Const        0x02 || GlobalRef || V<L(level)>
App          0x03 || T(function) || T(argument)
Lam          0x04 || T(type) || T(body)
Pi           0x05 || T(type) || T(body)
```

Table order guarantees that every child hash already exists. These rules make
the hashes of all six surviving v0.3 nodes byte-for-byte stable. There is no
`0x06` payload and no v0.4 hash may be computed for a retired node.

`NPA-CORE-EXPR-0.1` hashes one direct, owner-free core expression encoding.
It uses the same six expression tags in preorder; `Sort` contains an inline
normalized level, `BVar` contains its `UVar`, `Const` contains a canonical
`Name` and a vector of inline normalized levels, and binary nodes contain
their two inline child expressions. `NPA-KERNEL-CORE-EXPR-0.1` instead uses a
Merkle payload: `Sort` contains a kernel level hash, `BVar` contains its
`UVar`, `Const` contains its exact kernel-name `String` and vector of kernel
level hashes, and binary nodes contain their two child expression hashes.
Both encoders omit binder display names and have no `0x06` branch.

An inline normalized level uses tags `0x00` through `0x04` in the same
`Zero`, `Succ`, `Max`, `IMax`, `Param` order, with children encoded inline and
`Param` followed by a canonical `Name`. A kernel level hash uses the same
Merkle shape as the table-level payload, except that `Param` is followed by
the exact parameter `String`. `NPA-UNIVERSE-CONSTRAINTS-0.1` hashes:

```text
V<Name universe_parameter>
|| V<inline_normalized_lhs || relation || inline_normalized_rhs>

relation = 0x00 for <=
relation = 0x01 for =
```

The `NPA-DECL-IFACE-0.1` payload uses canonical names for
declaration-owned names and Merkle hashes for referenced nodes. Its exact
kind-specific field order is:

```text
Axiom:
  kind || N(name) || V<N(universe_param)> || [constraints]
       || T(type) || I

Def:
  kind || N(name) || V<N(universe_param)> || [constraints]
       || T(type) || reducibility || I || A
       || [T(value) only when reducible]

Theorem:
  kind || N(name) || V<N(universe_param)> || [constraints]
       || T(type) || opacity || I || A

Inductive:
  kind || N(name) || V<N(universe_param)> || [constraints]
       || V<T(parameter_type)> || V<T(index_type)> || L(sort)
       || V<N(constructor_name) || T(constructor_type)>
       || generated_recursor_signature_hash
       || generated_computation_rule_hash || I || A

MutualInductiveBlock:
  0x04 || N(block_name) || V<N(universe_param)> || constraints
       || V<N(member_name)
            || V<T(parameter_type)> || V<T(index_type)> || L(sort)
            || V<N(constructor_name) || T(constructor_type)>
            || generated_recursor_signature_hash
            || generated_computation_rule_hash>
       || I || A
```

Here `kind` is the declaration tag from Section 8.1; the bracketed constraint
field exists only for tags `0x10`, `0x11`, `0x12`, and `0x13`. In this hash
payload, constraints are
`V<L(lhs) || relation || L(rhs)>`. `I` contains only dependencies reached by
the public interface projection. The generated-recursor-signature hash uses
domain `NPA-GEN-REC-SIG-0.1` and payload `0x00`, or
`0x01 || N(name) || V<N(universe_param)> || T(type)`. The generated
computation-rule hash uses domain `NPA-GEN-COMP-RULE-0.1` and payload `0x00`,
or `0x01 || UVar minor_start || UVar major_index`.

Every `NPA-DECL-CERT-0.4.0` payload starts with the 32-byte declaration
interface hash, followed by exactly:

```text
Axiom                  A
Def                    T(value) || D || A
Theorem                T(proof) || D
Inductive              D || A
MutualInductiveBlock   D || A
```

The constrained and unconstrained forms of a kind use the same row. No field
outside the displayed row is appended implicitly. In particular, an axiom's
certificate row carries `A` and no `D`; a theorem's interface hash already
commits its complete `A` vector, while its certificate row adds
`T(proof) || D` and no trailing `A`.

The remaining aggregate hashes are exact hashes of previously specified
canonical bytes:

```text
NPA-MODULE-EXPORT-0.2.0  || encoded export_block from Section 10.1
NPA-AXIOM-REPORT-0.1     || encoded axiom_report from Section 10.1
NPA-MODULE-CERT-0.4.0    || certificate bytes from format through
                              axiom_report_hash, excluding certificate_hash
```

The axiom-policy payload is exactly:

```text
ASCII "NPA-AXIOM-POLICY-CANONICAL-BYTES-0.1"
|| 0x00 || mode
|| 0x01 || deny_sorry
|| 0x02 || V<Name allowlisted_axiom>
|| 0x03 || V<String supported_core_feature>

mode       = 0x00 Normal | 0x01 HighTrust
deny_sorry = 0x00 false  | 0x01 true
```

`NPA-AXIOM-POLICY-HASH-0.1` hashes that complete payload. Both vectors must be
in their prescribed canonical order. These policy bytes are a verifier and
candidate-identity input only: they are not encoded in a module certificate
and do not participate in any certificate hash.

Each builtin interface hash is `NPA-BUILTIN-INTERFACE-0.1` applied to exactly
one of these unframed ASCII payloads; no length or terminating byte is added:

```text
Nat       npa.machine-tactic.builtin.nat.v1
Nat.zero  npa.machine-tactic.builtin.nat.zero.v1
Nat.succ  npa.machine-tactic.builtin.nat.succ.v1
Nat.rec   npa.machine-tactic.builtin.nat.rec.v1
Eq        npa.machine-tactic.builtin.eq.v1
Eq.refl   npa.machine-tactic.builtin.eq.refl.v1
Eq.rec    npa.machine-tactic.builtin.eq.rec.v1
```

When a public declaration payload is otherwise unchanged, its interface hash
remains stable. When an export block and transitive axiom data are unchanged,
the module export and axiom-report hashes remain stable. Declaration and module
certificate hashes always move to the v0.4 domains and therefore differ from
v0.3 even when the surviving semantic payload happens to be otherwise equal.
Deleting the two public let-only Reduction theorems changes that module's
export hash as well.

Rehashing a v0.4 declaration or module under an old certificate domain is a
hash mismatch, never compatibility. Changing only the two header strings and
retaining an old final hash must fail `certificate_hash_mismatch` after the
current header has passed.

## 14. Source-Surface Tombstone

Human Surface and Machine Surface both reserve the exact identifier token
`let` as a rejection-only tombstone wherever an identifier can occur. The
lexer/parser boundary must produce:

```text
diagnostic variant: RemovedTermLet
wire kind:          removed_term_let
frontend boundary:  lexer/parser, before AST construction
Machine API phase:  machine_term_parse
message:            term-level `let` has been removed; use direct substitution, `fun` application, `have`, or a named module-level `def` or `opaque def` declaration
```

This diagnostic is not an AST constructor and must not lower to core data. It
is a pre-normalization Machine-term parse failure: a rejected batch item has no
candidate hash and cannot enter failed-candidate repair, proof-state, cache,
replay, or training flows that require an accepted candidate.

The source span is exactly the bytes of the offending `let` lexeme, excluding
leading/trailing whitespace and following punctuation. Human LSP and Machine
API serialization both preserve that span and the exact wire kind.

Token boundaries matter. `letter` is an ordinary identifier; the characters
inside comments and strings are inert; and `in` remains an ordinary identifier.
The old typed spelling, an unannotated spelling, nested spellings, and a
function-typed local value all receive the same removal diagnostic once the
exact `let` token is encountered. The parser must not retain the former grammar
long enough to issue a missing-type or missing-`in` compatibility error.

The source surfaces retain `fun`, application, `have`, `suffices`, and
module-level `def` / `opaque def`. A sequence that previously used a local
definition must be expressed with one of those current forms.

## 15. Diagnostics And Operational Profiles

Kernel fuel and performance records contain `beta_steps`, `delta_steps`, and
`iota_steps`. They contain no `zeta_steps`. `physical_reductions` is exactly:

```text
beta_steps + delta_steps + iota_steps
```

The kernel semantic profile advances to `npa-kernel.core.v0.2`; the Machine
kernel profile member advances from `core-spec-v0.1` to `core-spec-v0.2`; and
the old zeta-bearing reduction profile is unsupported. Canonical sidecars that
inline a removed term, local value, diagnostic variant, or zeta field must use
their reviewed let-free identity. Sidecars with unchanged bytes may retain an
identity only when the changed child is separately domain-separated. The
complete disposition is frozen in the Milestone 1 canonical-tag ledger.

## 16. Required Conformance Matrix

The shared v0.4 fixture matrix is normative. At minimum it contains:

- the complete 5-by-5 known-header cross product and unknown-header cases;
- a positive canonical node for each tag `0x00` through `0x05`;
- successful beta, delta, and iota cases;
- reachable, unreachable, truncated, and oversized-tail `0x06` cases;
- same-hash vectors for the six term forms and unchanged interface, export,
  axiom-report, level, and universe-constraint payloads;
- different-hash vectors for declaration and module certificates;
- header-only and old-domain-rehash rejection vectors; and
- mixed current/old import-closure rejection.

The producer/fast verifier, Rust reference checker, and OCaml checker must
agree on acceptance, applicable hashes, and the structured rejection boundary.
The two independent checkers implement their own decoding, hashing, structure,
typing, and reduction logic. Neither may accept a producer verdict as proof of
the expected outcome.

Deep-binder and shared-DAG positive vectors must prove that the six-form
calculus remains iterative and resource-bounded. A malicious `0x06` tail must
prove zero former-child reads and zero former-child allocations.

## 17. Compatibility, Migration, And Acceptance

The supported transition is a one-time rebuild from the previous pinned
checkpoint to npa-cli 0.9.0 and this v0.4 pair. The v0.9 implementation does
not ship any retired executable lane or any v0.3, v0.2, v0.1.2, or v0.1
decoder. A package closure is current only when every selected certificate and
import has the exact v0.4 pair and passes all required source-free checks.

Historical specifications and rejection fixtures may preserve old bytes for
documentation or negative testing. They must not be selected by an accepted
package manifest, advertised by a current checker capability, or exposed as a
runnable compatibility workflow.

This specification is implemented only after all of the following hold:

- every producer representation and accepted source path is let-free;
- all three checkers have exactly six core term cases and no zeta behavior;
- `0x06` and every old or mixed header pair reject at the specified boundary;
- all reviewed canonical identities and hashes follow Section 13;
- positive package closures are rebuilt under the exact v0.4 pair;
- the fast, Rust reference, and clean-room OCaml gates pass without cache;
- the package axiom, hash, lock, and source-free release gates pass; and
- no current executable, fixture selection, documentation, or toolchain path
  silently preserves the old pair.
