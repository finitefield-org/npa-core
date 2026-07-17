# Inductive Constructor Universe Bounds Design

Status: implemented on 2026-07-11. The Rust kernel and verifier, independent
Rust reference checker, and supported OCaml external-checker substrate enforce
the rule below. Certificate encoding and hash domains are unchanged.

## Summary

NPA must reject a non-parameter constructor field whose type lives in a
universe above the declared sort of its inductive family. If a family has
result sort `Sort u`, and a constructor field type checks as `Sort v`, the
declaration universe context must entail `v <= u`.

The check is mandatory in every semantic implementation that can accept an
inductive declaration:

- the Rust kernel, for single and mutual inductives;
- certificate construction and certificate verification through the kernel;
- the source-free Rust reference checker, for single and mutual inductives;
- the OCaml external checker for every inductive shape it accepts.

Canonical Prop-valued families are the only exception. They may contain fields
from higher universes because NPA restricts their recursor motives to Prop and
does not implement singleton large-elimination exceptions. The exception and
the elimination restriction are one policy: neither may be changed in
isolation.

This is a semantic validation change. It does not change certificate bytes,
hash domains, format tags, or the public export schema. Certificates that rely
on the omission become invalid; valid certificates keep the same identity.

## Security Problem

Before this fix, the implementations checked that constructor types were well
formed, returned the declared family with canonical parameters, and satisfied
positivity, but did not compare the universe of each stored field type with the
family's declared sort.

In NPA notation:

```text
Prop   = Sort 0
Type   = Sort 1
Sort u : Sort (succ u)
```

The formerly accepted declaration below has no parameters, so `A` is a stored
constructor field:

```text
Code : Sort 1
mk   : (A : Sort 1) -> Code
```

The field type is `Sort 1`, and `Sort 1 : Sort 2`. The missing obligation is
therefore:

```text
2 <= 1
```

The generated recursor can then define:

```text
El : Code -> Sort 1
El (mk A) = A
```

This places a code for every small type inside the same small universe and
provides a decoding computation rule. It violates the predicative inductive
invariant and supplies the classic small-universe self-encoding primitive. The
fix must be treated as security-critical even if no checked closed proof of
`False` is included in the regression corpus.

The security regression fixtures now pin the affected paths:

- `crates/npa-cert/tests/audit_inductive_universe.rs` requires construction and
  verification of the axiom-free `Code`/`El` module to fail;
- `crates/npa-checker-ref/tests/audit_inductive_universe.rs` requires the same
  single fixture and a mutual-block fixture to fail in both trust modes;
- `checkers/npa-checker-ext/test/test_runner.ml` requires the legacy fixture to
  fail in the OCaml single-inductive type-checking substrate.

All three surfaces report a constructor-universe-bound failure. The mutual
OCaml path remains fail-closed as unsupported, as required by this design.

## Intended Outcome

After implementation:

1. An otherwise well-formed Type-valued single or mutual inductive is accepted
   only when every non-parameter constructor field satisfies the bound.
2. Explicit declaration or mutual-block universe constraints may discharge the
   obligation; the checker never invents a missing constraint.
3. Canonical Prop-valued families retain impredicative fields, but every
   recursor for such a family remains Prop-eliminating only.
4. `build_module_cert`, producer-backed certificate generation, Rust
   verification, reference checking, and the supported OCaml semantic substrate
   agree on the result.
5. Rejection is atomic: a failing single inductive or any failing member of a
   mutual block installs no family, constructor, or recursor artifacts.
6. The original `Code : Type` certificate is rejected without consulting its
   axiom report or checker trust mode.

Implementation note: the AI producer-candidate MVP remains fail-closed for all
inductive candidates, so it cannot emit either the single or mutual exploit.
`build_module_cert`, current certificate verification, and the frozen pre-fix
fixtures exercise the kernel-backed generation and verification paths. The
OCaml checker still rejects mutual blocks before semantic installation, while
the Rust kernel and reference checker enforce the member-specific rule.

## Goals

- Restore the predicative constructor-field universe invariant.
- State the rule in terms of inferred sorts, rather than constructor syntax.
- Cover dependent constructor telescopes and explicit universe constraints.
- Cover each family in a mutual block using that family's own declared sort.
- Preserve ordinary parameterized inductives such as `List` and `Prod`.
- Preserve the existing impredicative Prop policy without enabling large
  elimination.
- Produce stable, checker-specific diagnostics for the new rejection.
- Keep certificate encoding and valid certificate hashes unchanged.
- Add a malicious, canonically encoded fixture that can test independent
  verifiers after the Rust producer starts rejecting the declaration.

## Non-Goals

- Do not add cumulative subtyping or use universe constraints as definitional
  equality.
- Do not infer, insert, or minimize declaration universe constraints.
- Do not automatically lift an inductive family to a larger sort.
- Do not change positivity, nested-functor recognition, recursor reduction, or
  iota rules except where tests confirm the existing Prop elimination policy.
- Do not add singleton elimination or any other Prop-to-Type elimination.
- Do not make `generate_inductive_artifacts_v1` or
  `generate_mutual_inductive_artifacts_v1` a standalone semantic authority;
  they remain structural artifact generators.
- Do not change normal-mode unchecked-import semantics in this change. A
  certificate supplied through an API that promises only decode/hash checking
  is still not a semantically checked import; see the trust-boundary section.
- Do not make the OCaml checker accept mutual blocks as part of this fix. It
  currently rejects all `MutualInductiveBlockDecl` payloads as unsupported and
  must continue to fail closed until independent mutual-inductive checking is
  implemented.
- Do not upgrade the OCaml prototype from its current `NPA-CERT-0.1` decoder or
  wire its standalone skeleton executable into a complete checker as part of
  this fix. The semantic substrate and its tests must enforce the rule for the
  legacy-compatible exploit fixture; current-format support remains governed
  by `npa-checker-ext-ocaml.md`.

## Normative Constructor Rule

### Notation And Binder Classification

Let an inductive family `I` have:

```text
I : Pi (p0 : P0) ... (p[p-1] : P[p-1]),
    Pi (i0 : X0) ... (i[q-1] : X[q-1]),
    Sort u
```

Let one of its constructors have a Pi telescope:

```text
c : Pi (d0 : D0) ... (d[n-1] : D[n-1]), I params index_args
```

The existing constructor-result rule requires `n >= p` and requires the first
`p` result arguments to be the canonical de Bruijn references to the first `p`
constructor domains. Those first `p` domains are the uniform parameter prefix.
Every domain at position `k >= p` is a non-parameter field for the universe
bound, including:

- ordinary stored values;
- constructor-local type fields;
- binders used to determine result indices;
- recursive and mutually recursive fields;
- fields whose types depend on earlier constructor fields.

Classification is positional and uses the existing canonical parameter rule.
Names and surface syntax do not affect it.

### Sequential Field Checking

For each constructor domain, build the local context from left to right. Before
checking `Dk`, the context contains assumptions for `D0` through `D[k-1]`.
Infer the sort of the domain type in the declaration universe context:

```text
Gamma, d0 : D0, ..., d[k-1] : D[k-1] |- Dk : Sort vk
```

For a non-Prop family and each `k >= p`, require:

```text
declaration_universe_context entails normalize(vk) <= normalize(u)
```

The relevant level is the level returned by `expect_sort(Dk)`. It is not a
level guessed from syntax and it is not necessarily the level written inside
`Dk`.

Examples:

- If `Dk` is `Sort 1`, then `Dk : Sort 2`; the field obligation uses `2`.
- If an earlier parameter is `A : Sort u` and `Dk` is `A`, then
  `Dk : Sort u`; the field obligation uses `u`.
- If `Dk` is a Pi type, its inferred sort uses the existing NPA Pi rule and the
  normalized result is the field level.
- If `Dk` weak-head reduces to a type whose type is `Sort v`, the obligation
  uses `v` returned by the ordinary type checker.

Failure to infer a sort remains `ExpectedSort` or the existing type-checking
error. A supported but unentailed inequality is the new constructor-universe
bound error. An inequality outside the supported level fragment remains an
unsupported-universe-constraint error.

### Why Uniform Parameters Are Excluded

The parameter telescope describes inputs to the family; it is not stored data
introduced by the constructor. Applying the field bound to that prefix would
reject standard declarations. For example:

```text
List.{u} (A : Sort u) : Sort u
List.nil  : (A : Sort u) -> List A
List.cons : (A : Sort u) -> A -> List A -> List A
```

The parameter domain `Sort u` itself lives in `Sort (succ u)` and is excluded.
The stored `A` field lives in `Sort u` and satisfies `u <= u`; the recursive
`List A` field also lives in `Sort u`.

Excluding the prefix does not allow a higher-universe parameter to be stored
silently. Any later field of that parameter type is checked. For example:

```text
Box.{u,v} (A : Sort u) : Sort v
Box.mk : (A : Sort u) -> A -> Box A
```

requires `u <= v`. If the declaration context does not entail that relation,
`Box.mk` is rejected.

### Explicit Prop Policy

A family is Prop-valued only when `normalize(u) = 0`. A universe parameter that
happens to be constrained equal to zero is not classified as Prop. This matches
the current recursor generator and checkers, which do not use universe
constraints as definitional equality assumptions.

For a canonical Prop-valued family:

- do not impose the constructor field `v <= 0` obligations;
- continue to require every generated or supplied recursor motive for that
  family to return `Sort 0`;
- retain the rule for Prop members of mutual blocks independently of the
  target sort of other members;
- do not recognize singleton-elimination exceptions;
- reject any recursor shape that would eliminate the Prop family into a
  positive universe.

This exception supports propositions such as existential packages with
higher-universe witnesses while preventing those witnesses from being decoded
into Type by recursion. If NPA later adds large elimination from Prop, that
feature must either remove this exception or provide a separate soundness
argument and feature-gated rule before it is enabled.

### Mutual Inductives

A mutual block has one shared universe context and uniform parameter telescope,
but each member has its own declared result sort. For a constructor owned by
family `Ij`:

```text
field_level <= normalize(Ij.sort)
```

is the required obligation. The sort of another family mentioned by a
recursive field does not replace the owning family's bound. Ordinary inference
of that recursive field type determines `field_level`.

Consequences:

- one failing field rejects the entire block atomically;
- constraints are taken from the block, because member declarations in the
  current representation must not carry independent constraints;
- a mixed Prop/Type block applies the Prop exception only to constructors owned
  by a canonical Prop family;
- every Type-valued member is checked even if another member is Prop-valued;
- existing shared-parameter and positivity rules run unchanged.

The Rust kernel and reference checker already accept mutual blocks and must
perform this full rule. The OCaml checker currently rejects mutual blocks before
semantic acceptance. That rejection satisfies the security invariant
`accepted mutual block => all fields were checked` vacuously. Enabling OCaml
mutual support later is forbidden until the new universe-bound helper is wired
into its mutual constructor loop and the cross-checker mutual corpus passes.

## Universe Entailment Contract

### Reuse Of Declaration Contexts

The Rust kernel must use the `UniverseContext` built from the inductive's
universe parameters and constraints. The reference checker must use its
independent `ReferenceUniverseContext`. The OCaml checker must build an
independent context from the decoded declaration or block constraints.

The checker does not append a field obligation to the declaration context and
then test satisfiability. That would accept a declaration by silently
strengthening its public signature. It must prove the obligation from the
context already present in the certificate.

### Max On The Right-Hand Side

The current difference-constraint implementation decomposes `max` on the left
of a declared inequality and requires a single atom on the right. A constructor
family sort may nevertheless be `max u v`, and useful tautologies such as
`u <= max u v` must not be rejected.

Add an obligation-only level comparison operation in the Rust kernel and
implement the same specified behavior independently in the other checkers:

```text
entails_level_le(context, lhs, rhs) -> supported-and-true | false | unsupported
```

For normalized levels in the existing atom-plus-finite-offset fragment:

1. Decompose `lhs` and `rhs` into their sets of `max` atoms.
2. For every atom in `lhs`, require at least one atom in `rhs` such that the
   declaration constraint closure entails the first atom is less than or equal
   to the second.
3. Return false if any left atom has no right witness.
4. Return unsupported if either side contains a residual `imax`, an unresolved
   metavariable, arithmetic outside finite successor offsets, or another shape
   outside the documented fragment.
5. Before searching, compute `left_atom_count * right_atom_count` with checked
   arithmetic and return the existing universe-constraint resource-limit error
   if it exceeds `MAX_UNIVERSE_ATOM_INEQUALITIES`.

This is a conservative proof procedure. It proves reflexive and structural-max
obligations such as `u <= max u v` and uses the existing closure for transitive
relations such as `u <= v <= w`. It does not allow a right-hand-side `max` in
the declaration's assumed constraints; that remains outside the current
context format because such an assumption is disjunctive. The extension is for
proving obligations only.

In Rust, add this operation to `UniverseContext` in
`crates/npa-kernel/src/level.rs`:

```rust
pub fn entails_level_le(&self, lhs: &Level, rhs: &Level) -> Result<bool>
```

It returns `Ok(true)` or `Ok(false)` only for supported normalized levels and
returns the existing structured error for an unsupported shape or resource
limit. It validates each level against the context parameters, but it must not
call the stored-vector `ensure_universe_constraints_wf` path: that path
correctly rejects right-hand `max` assumptions, while this operation is proving
an obligation. Change `UniverseContext::entails` to use it for each `<=`
direction and to convert `Ok(false)` back to the existing
`Error::UniverseConstraintViolation`. The constructor checker calls
`entails_level_le` directly so it can map `Ok(false)` to the new
constructor-specific error.

Add the independent reference-checker equivalent:

```text
ReferenceUniverseContext.entails_level_le(lhs, rhs, offset)
  -> DecodeResult<bool>
```

and use it under the same mapping rules. The reference implementation must not
call into `npa-kernel`.

This deliberately broadens proof of valid obligations, including substituted
public-signature obligations, from a singleton right-hand atom to the safe
conservative `max` rule above. It does not broaden the allowed declaration
assumptions.

### Unsatisfiable And Unsupported Contexts

The declaration context must be canonical, supported, and satisfiable before
it can discharge any field obligation. In particular, a malicious certificate
cannot add `succ u <= u` and use explosion in an inconsistent constraint
context.

Use the existing deterministic limits in every implementation:

```text
maximum universe-context nodes:       65
maximum decomposed atom inequalities: 1024
```

Limit exhaustion retains the implementation's existing resource-limit
classification; it is not reported as a false field inequality.

The Rust kernel and reference checker already validate this property. The
OCaml checker currently checks only level well-formedness and does not retain
public signature constraints in its environment. Its universe-context work is
therefore a prerequisite for claiming independent enforcement, not an optional
refactor.

## Constructor Validation Order

For both single and mutual constructors, preserve existing diagnostics by
running the new rejection only after the current structural checks have
succeeded:

1. Check that the complete constructor type has a sort.
2. Peel its Pi domains and result.
3. Run the existing positivity checks.
4. Normalize and validate the existing constructor result, including family,
   universe arguments, argument count, and canonical uniform parameters.
5. Traverse the domains left to right in a local context and collect their
   inferred sort levels.
6. Skip the uniform parameter prefix.
7. Apply the Prop policy or prove each remaining field obligation.

The traversal should share deterministic inference and conversion fuel across
one constructor-bound pass. It may reuse a helper based on the existing
`expect_sort_with_remaining_fuel` machinery. Avoid resetting a full fuel budget
for every field.

This order means an old non-positive constructor still reports positivity, and
a constructor returning the wrong family still reports a bad constructor
result. The new error identifies an otherwise valid constructor that fails the
universe bound.

## Trust Boundary

The rule is semantic, not producer metadata. A hostile party can construct and
rehash canonical certificate bytes without calling NPA's producer, so no
checker may trust that certificate generation already ran the rule.

The required acceptance boundary is:

```text
source / API declaration
  -> structural inductive artifact generation
  -> kernel-checked certificate construction
  -> canonical bytes
  -> independent source-free semantic checking
```

Both the kernel-backed verifier and every independent checker must reject the
malicious bytes. Axiom reports do not mitigate the issue: the exploit fixture
has an empty module axiom set.

Trust mode also does not change the declaration rule. Normal and high-trust
checking use the same inductive semantics. High-trust mode additionally
requires a semantically checked import closure.

`ReferenceImportStore::from_source_free_certificates` currently represents a
separate boundary: it can expose public interfaces from certificates that were
decoded and hash-checked but not semantically checked. This design does not
relabel those entries as checked or make a normal-mode leaf verdict a closure
verdict. Consequently:

- the malicious certificate itself is rejected whenever it is semantically
  checked under this design;
- package DAG and high-trust tests must show an invalid dependency is rejected
  before a dependent leaf is trusted;
- callers must not promote a normal-mode result over unchecked imports to
  high-trust evidence;
- hardening or removing unchecked normal imports remains a separate change.

The external checker remains high-trust evidence only under the executable,
identity, policy, and import-closure conditions in
`npa-checker-ext-ocaml.md`.

## Implementation Design

### Rust Kernel

Primary files:

- `crates/npa-kernel/src/env.rs`;
- `crates/npa-kernel/src/level.rs`;
- `crates/npa-kernel/src/error.rs`;
- `crates/npa-kernel/src/lib.rs` for unit tests.

Add a private constructor-telescope helper that takes:

```text
inductive name
constructor name
parameter count
family sort
constructor domains
declaration universe context
```

It must infer domain sorts sequentially, skip the first `parameter_count`
domains, apply the canonical Prop exception, and call the new
obligation-entailment operation for every remaining domain. Both
`Env::check_constructor_decl` and `Env::check_mutual_constructor_decl` must call
the same helper after their existing positivity and result checks.

Add this kernel error:

```rust
ConstructorUniverseBoundViolation {
    inductive: String,
    constructor: String,
    field_index: usize,
    field_level: Level,
    inductive_sort: Level,
}
```

`field_index` is zero-based among non-parameter fields, not among the complete
Pi domains. Store normalized levels in the error so equal failures render
deterministically.

The helper must not mutate `Env`. Existing candidate-environment construction
then preserves atomic insertion for both single declarations and blocks.

### Certificate Generation And Rust Verification

Primary paths:

- `crates/npa-cert/src/canonical.rs` builds a candidate environment before
  emitting a certificate;
- `crates/npa-cert/src/producer.rs` checks producer candidates through the
  kernel;
- `crates/npa-cert/src/kernel.rs` maps decoded declarations into `Env`;
- `crates/npa-cert/src/verify.rs` reconstructs and checks declarations during
  verification.

These paths should inherit the new rule through `Env::add_inductive` and
`Env::add_mutual_inductive`. Do not duplicate a weaker syntactic check in
`npa-cert`.

Required behavior:

- `build_module_cert` returns
  `CertError::Kernel(Error::ConstructorUniverseBoundViolation { .. })` before
  certificate bytes are emitted;
- the AI producer-candidate MVP rejects every inductive candidate before
  certificate construction; if inductive candidates are enabled there later,
  their semantic precheck must preserve the same kernel rejection;
- verification of a pre-existing, correctly hashed malicious certificate
  returns the same kernel rejection;
- package write commands do not install a partially generated certificate when
  the rule fails;
- artifact-only generation may still return a proposed recursor shape, but no
  caller may treat that result as semantic acceptance.

No new `CertError` variant is required because `CertError::Kernel` preserves the
structured kernel error.

### Rust Reference Checker

Primary files:

- `crates/npa-checker-ref/src/decode.rs`;
- `crates/npa-checker-ref/src/lib.rs`;
- `crates/npa-checker-ref/src/main.rs`;
- `crates/npa-api/src/package_verifier.rs` for normalized package diagnostics.

Implement the rule independently over `ReferenceCoreExpr`, `TypeContext`, and
`ReferenceUniverseContext`. Add one shared helper used by
`check_constructor_decl` and `check_mutual_constructor_decl`. It must follow the
same normative ordering, binder classification, Prop policy, and obligation
semantics without importing or calling `npa-kernel`.

Add:

```rust
ReferenceCheckReason::ConstructorUniverseBoundViolation
```

Map it to:

```text
reason_code = constructor_universe_bound_violation
raw error kind = universe_inconsistency
section = declarations
offset = the owning declaration offset
```

Add the same reason-code mapping to
`reference_check_reason_code` in `npa-api` so package verification does not
lose the constructor-specific cause. Preserve the package checker's existing
nested error shape:

```text
package reason_code = reference_checker_rejected
checker_error.kind = type_check
checker_error.reason_code = constructor_universe_bound_violation
```

The standalone `npa-checker-ref` raw-result mapping is the surface that uses
`error.kind = universe_inconsistency`.

### OCaml External Checker

Primary files:

- `checkers/npa-checker-ext/src/ext_universe.ml` for constraint contexts and
  obligation entailment;
- `checkers/npa-checker-ext/src/ext_env.ml` for signature constraints;
- `checkers/npa-checker-ext/src/ext_typecheck.ml` for declaration and
  constructor checking;
- `checkers/npa-checker-ext/scripts/build.sh` and `scripts/test.sh` to compile
  `ext_universe.ml` after `ext_cert.ml` and before `ext_env.ml` and
  `ext_typecheck.ml`, and to link it in the same position;
- `checkers/npa-checker-ext/test/test_runner.ml` for the independent corpus.

The external checker needs the following prerequisite substrate:

1. Add `signature_universe_constraints : Ext_cert.universe_constraint list` to
   `Ext_env.signature`. Local axioms, definitions, theorems, and inductive
   families retain their declaration constraints. Generated constructors and
   recursors inherit the parent inductive constraints. Builtins use an empty
   constraint list.
2. Validate supported constraint shape, canonical parameters, resource bounds,
   and satisfiability before constructing an OCaml universe context.
3. Thread an explicit `Ext_universe.context` through `infer`, `check`, and
   `expect_sort`, including all recursive calls. Declaration checking builds it
   once from `decl_universe_params` and `decl_universe_constraints`; helpers
   must not silently replace a non-empty declaration context with an empty
   default.
4. During constant inference, substitute `signature_universe_params` in
   `signature_universe_constraints` with the supplied level arguments and
   require the ambient context to entail every substituted obligation before
   returning the substituted type. Reusing a context only for constructors
   while ignoring signature obligations would leave the external universe
   model unsound. Generated recursor signatures may have an additional motive
   universe parameter, but inherited constraints mention only the parent names
   and remain well formed in that extended parameter list.
5. Implement the obligation-only right-hand `max` rule specified above.
6. Pass the declaration context and `ind_sort` into the single-inductive
   constructor loop and check every non-parameter domain sequentially.

`Ext_universe.context` owns the declared parameter order, normalized constraint
vector, and a closed difference-bound relation. Construct it deterministically:

1. Require unique universe parameters and individually well-formed, normalized
   levels.
2. Require the stored constraint vector to be strictly sorted and duplicate
   free.
3. Decompose an assumed `lhs <= rhs` only when `lhs` is a finite `max` of
   atom-plus-successor terms and `rhs` is one such atom. Decompose equality as
   both directions.
4. Create nodes for zero and every declared parameter, add the natural-number
   lower bounds `0 <= parameter`, enforce the shared node/inequality limits,
   and compute a deterministic transitive closure.
5. Reject a negative self-bound as
   `unsatisfiable_universe_constraints`.
6. Use the obligation algorithm above for queries. A false signature
   obligation becomes `universe_constraint_violation`; a false constructor
   field obligation becomes `constructor_universe_bound_violation`.

This specifies semantics, not a port of the Rust function layout. The OCaml
implementation remains independently authored.

The current OCaml decoder accepts `NPA-CERT-0.1`, whose public export layout
does not carry universe constraints. It must continue to reject any legacy
certificate whose exported declaration would require non-empty constraints;
it must never manufacture an empty imported constraint list for such an
export. Use:

```text
reason_code = constrained_export_requires_format_upgrade
raw error kind = unsupported_schema_version
section = export_block
```

Unconstrained legacy exports create signatures with an empty constraint list.
Extending `Ext_cert.export_entry`, `Ext_import_store.public_export`,
`Ext_canonical`, and imported `Ext_env.signature` to the v0.2 constrained
export layout belongs to the separate current-format support work. That work
must preserve the same signature-constraint substitution rule before the new
format is accepted.

Add OCaml error reasons and stable mappings for:

```text
noncanonical_universe_constraints
duplicate_universe_constraint
unsupported_universe_constraint
unsatisfiable_universe_constraints
universe_constraint_violation
constructor_universe_bound_violation
```

`noncanonical_universe_constraints` maps to raw error kind
`noncanonical_encoding`; the other five map to
`universe_inconsistency`. The constructor-specific reason is used only for a
supported inequality that is not entailed. All type-checker-originated failures
use section `declarations` and the owning declaration offset.

The OCaml implementation must be authored from this public semantic contract
and golden/mutation fixtures, consistent with its clean-room constraints. It
must not link to or call Rust code.

For mutual blocks, keep the current `unsupported_declaration` failure. Add a
test that a malicious mutual payload cannot reach `checked` status. Full OCaml
mutual positivity, recursor, and environment support remains a separate
feature, but its release checklist must include this rule before removing the
fail-closed branch.

### Frontend And Diagnostic Callers

The frontend is not trusted to enforce the rule, but callers should surface the
kernel error clearly:

- `npa-api` human inductive checking should report rejection and must not mark
  positivity as the cause;
- `npa-tactic::kernel_diag` should classify the new error as a universe
  diagnostic with `UniverseDiagnosticKind::InvalidInstantiation`, constructing
  the displayed `field_level <= inductive_sort` obligation from the error,
  rather than as a generic proof-expression failure;
- CLI package build failures should remain kernel/certificate-generation
  failures and must not suggest adding an axiom;
- no caller should retry by raising the family universe or adding a constraint
  silently.

Surface elaborators may later emit an advisory suggestion such as declaring a
larger family sort or an explicit valid constraint, but that is not required
for the security fix.

## Error And Compatibility Contract

The three semantic implementations expose different internal error types and
their enclosing schemas use different kind vocabularies. The
constructor-specific reason must remain visible at every boundary:

| Boundary | Structured reason | Enclosing classification |
| --- | --- | --- |
| Rust kernel / `npa-cert` | `ConstructorUniverseBoundViolation` | kernel error wrapped by `CertError::Kernel` |
| Standalone Rust reference raw result | `constructor_universe_bound_violation` | `universe_inconsistency` |
| `npa-api` package checker details | `constructor_universe_bound_violation` | `type_check` under `reference_checker_rejected` |
| OCaml external raw result | `constructor_universe_bound_violation` | `universe_inconsistency` |

This change does not require:

- a new `NPA-CERT-*` tag;
- a new `NPA-Core-*` tag;
- a new declaration or export field;
- a new hash domain;
- regeneration of valid certificates solely for identity compatibility.

It does change semantic acceptance. A previously generated certificate that
violates the rule must be rejected even if all stored hashes are correct. There
is no legacy-format exemption and no policy flag that restores acceptance.

## Regression Fixture Strategy

After the kernel fix lands, `build_module_cert` can no longer create malicious
bytes for independent-checker tests. Before changing the kernel, freeze the
full `Code`/`El` certificate in the legacy unconstrained encoding accepted by
all three current semantic substrates:

```text
testdata/certificates/security/
  inductive-constructor-universe-bound-v0.1.npcert
  mutual-inductive-constructor-universe-bound-v0.2.npcert
  README.md
```

The README must record:

- the fixture's SHA-256 file digest;
- the exact `NPA-CERT-0.1` and `NPA-Core-0.1` tags and the reason the legacy
  encoding is used for cross-language coverage;
- that its internal certificate, export, and axiom-report hashes are valid;
- that its module axiom set is empty;
- the exact invalid field obligation `2 <= 1`;
- that rejection, not successful verification, is the expected result;
- the command or pre-fix test helper used to reproduce it.

Create the legacy bytes with the existing `legacy_bytes_from_current_cert`
test pattern in `crates/npa-cert/src/tests.rs`: retag the pre-fix current
certificate, encode the legacy export block, and recompute the legacy export,
axiom-report, and module-certificate hash domains. Before committing the
fixture, assert that the pre-fix Rust verifier and reference checker both
accept it and that the OCaml decoder reaches semantic type checking. Remove
any one-off file-writing helper after the fixture is frozen.

The fixture is proof-security test input, never a vendored package dependency.
Keep it as ordinary Git content. Do not use Git LFS and do not add LFS
attributes.

The additional current-format mutual fixture freezes a block with one invalid
`Code` member and one valid member. It pins the independent reference checker's
mutual path and the kernel verifier's atomic rejection after pre-fix producers
can no longer recreate those bytes.

Rust verifier, reference checker, and the OCaml decoder/type-checker substrate
must consume the same bytes. Rust construction tests separately exercise the
current certificate format by requiring rejection before encoding. Unit tests
may also construct smaller in-memory declarations to pin exact error variants,
but they do not replace the cross-checker fixture.

## Test Plan

### Kernel Unit Tests

Add tests in `crates/npa-kernel/src/lib.rs` for:

- rejecting `Code : Sort 1` with field `A : Sort 1`, whose field level is `2`;
- rejecting polymorphic `succ u <= u` field obligations;
- accepting a stored `A : Sort u` when the family is `Sort u`;
- accepting `Box.{u,v}` only when the context entails `u <= v`;
- accepting a uniform higher-universe parameter that is not stored;
- checking dependent fields under all preceding domains;
- accepting `u <= max u v` through obligation-only right-hand `max` support;
- retaining an unsupported error for residual `imax` or unsupported arithmetic;
- retaining the canonical Prop exception and Prop-only recursor motive;
- preserving positivity and bad-result diagnostic precedence;
- rejecting an oversized field in any member of a mutual block atomically;
- applying each mutual member's own sort;
- enforcing the Type member while exempting only the Prop member of a mixed
  block;
- preserving the existing valid `Even`/`Odd`, `Nat`, `Eq`, `List`, `Option`,
  and `Prod` cases.

### Certificate And Producer Tests

Update `crates/npa-cert/tests/audit_inductive_universe.rs` so that:

- artifact generation may produce the structural proposal;
- `build_module_cert` rejects before encoding;
- the error identifies `Audit.Code.mk`, field index `0`, field level `2`, and
  inductive sort `1`;
- no axiom-policy choice changes the result.

Add or update tests for:

- producer-backed construction rejection;
- frozen malicious certificate rejection by `verify_module_cert`;
- mutual certificate construction rejection;
- unchanged encoding and hashes for representative valid inductives;
- no partial package certificate write on failure.

### Reference Checker Tests

Update `crates/npa-checker-ref/tests/audit_inductive_universe.rs` to read the
frozen bytes and require:

```text
ReferenceCheckResult::Rejected
reason = ConstructorUniverseBoundViolation
section = Declarations
```

Add direct reference-checker coverage for:

- single and mutual violations;
- explicit entailed and missing constraints;
- right-hand `max` obligations;
- dependent field contexts;
- canonical Prop acceptance and non-Prop rejection;
- package diagnostic reason-code normalization;
- identical rejection in normal and high-trust modes when the malicious
  declaration is in the certificate being checked.

### OCaml External Checker Tests

Extend `checkers/npa-checker-ext/test/test_runner.ml` with:

- universe-context normalization, satisfiability, and transitive entailment
  tests;
- unsorted and duplicate stored-constraint rejection tests;
- the shared node and atom-inequality resource limits;
- supported false and unsupported obligation cases;
- constant-signature constraint substitution tests;
- inheritance of local inductive constraints by generated constructor and
  recursor signatures;
- direct single-inductive rejection with
  `constructor_universe_bound_violation`;
- valid parameter exclusion, explicit-constraint, right-hand `max`, and Prop
  cases;
- decoding and semantic checking of the shared legacy malicious certificate
  fixture through the test substrate;
- a mutual malicious payload that remains rejected as
  `unsupported_declaration`, never checked.

Run:

```sh
checkers/npa-checker-ext/scripts/test.sh
```

If OCaml is unavailable in a development environment, that limitation may be
reported locally, but the release/CI gate for this security change must execute
and pass the suite.

### Package And Closure Tests

Add a package-level fixture or in-memory DAG test in `npa-api` that places the
malicious certificate below a valid-looking leaf. Require:

- high-trust/package DAG verification rejects the dependency;
- the leaf does not receive a trusted package verdict;
- the package error uses `reference_checker_rejected`, nested checker kind
  `type_check`, and nested reason code
  `constructor_universe_bound_violation`;
- an empty axiom report does not alter rejection.

Keep the existing normal-mode unchecked-import audit test. Its expected result
documents the separate import-store boundary until that boundary is hardened;
do not reinterpret it as evidence that the universe rule failed to run on a
certificate that was never semantically checked.

### Repository Gates

At minimum, run:

```sh
cargo test -p npa-kernel
cargo test -p npa-cert --test audit_inductive_universe
cargo test -p npa-checker-ref --test audit_inductive_universe
checkers/npa-checker-ext/scripts/test.sh
./scripts/check-fast.sh
```

Run the commands from `npa-core`. If the implementation touches checked package
fixtures, also run the fixture and package gates required by `CONTRIBUTING.md`.

## Documentation And Rollout

Land the semantic implementations together. A kernel-only release would still
allow an independent checker to accept hostile prebuilt bytes, while a
reference-only release would leave producer and fast-verifier acceptance
unchanged.

Implementation sequence:

1. Freeze and document the malicious canonical certificate fixture.
2. Add failing cross-checker and valid-control tests.
3. Add obligation-only right-hand `max` entailment and parity tests.
4. Implement the kernel single/mutual rule and invert certificate-generation
   tests.
5. Implement the independent reference rule and stable diagnostics.
6. Implement the OCaml universe-context prerequisite and single-inductive
   rule; retain fail-closed mutual rejection.
7. Run package closure and full fast gates.
8. Update `core-spec-v0.2.0.md` and `npa-checker-ext-ocaml.md` from proposed to
   implemented behavior in the same release change.
9. Add a release note that semantic validation is stricter but certificate
   encoding is unchanged.

Do not add a compatibility flag. If valid declarations regress, fix the
entailment implementation or add a sound explicit constraint; do not disable
the bound. Rolling back the release would reintroduce a security-critical
acceptance path.

## Acceptance Criteria

The work is complete only when all of the following are true:

- The Rust kernel rejects every supported non-Prop single-inductive violation.
- The Rust kernel rejects a violation in any member of a mutual block without
  installing partial artifacts.
- The Rust reference checker independently rejects the shared malicious bytes
  for the constructor-specific reason.
- The OCaml decoder/type-checker substrate independently rejects the shared
  legacy malicious bytes and can soundly use canonical, satisfiable universe
  contexts for supported single inductives.
- The OCaml checker continues to reject every mutual block until its full
  mutual implementation includes the same bound.
- Certificate construction and producer APIs reject the `Code`/`El` module
  before emitting bytes.
- Rust certificate verification rejects the frozen, correctly hashed,
  axiom-free malicious certificate.
- Explicit valid constraints discharge obligations; absent or insufficient
  constraints do not.
- Uniform parameters, dependent fields, right-hand `max`, recursive fields,
  mixed mutual sorts, and the Prop exception have positive and negative tests.
- Prop recursors cannot eliminate into Type, and no singleton exception is
  introduced.
- Package/high-trust verification rejects a malicious dependency before
  trusting a leaf.
- Stable reason-code mappings preserve the constructor-specific cause, with
  each enclosing error kind matching the boundary table above.
- Existing valid package fixtures and representative certificate hashes remain
  unchanged.
- The core specification and external-checker specification describe the
  shipped rule accurately.
- All required Rust, OCaml, package, and repository gates pass.
