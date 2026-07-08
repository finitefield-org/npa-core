# NPA Core Implementation Specification v0.2.0

This document records the core behavior implemented by the current v0.2.0
Rust crates. It supersedes the historical v0.1.2 implementation snapshot for
certificate-format and universe-constraint behavior.

New certificates use:

```text
format:    NPA-CERT-0.2.0
core_spec: NPA-Core-0.2.0
```

`NPA-CERT-0.1.2` / `NPA-Core-0.1.2` remains a previous-format decode path with
the same export-block shape as v0.2.0 and its original hash domains.
`NPA-CERT-0.1` / `NPA-Core-0.1` remains a legacy decode path for older
unconstrained public exports. Old-format legacy certificates whose exported
declarations would carry non-empty universe constraints are rejected rather
than silently dropping those constraints from the public interface.

## 1. Implementation Map

The implementation is split across these trusted or checker-facing crates.

```text
crates/npa-kernel
  Core expression, level, declaration, context, substitution, reduction,
  typing, definitional equality, inductive checks, and builtin profiles.

crates/npa-cert
  Canonical certificate construction, binary encoding/decoding, hashing,
  import resolution, axiom policy, fast verification, and Rust kernel replay.

crates/npa-checker-ref
  Source-free independent reference checker for canonical certificate bytes.
  It has its own decoder, hash verifier, axiom-report verifier, and semantic
  type checker. It does not depend on npa-frontend, npa-api, npa-tactic, or
  npa-cert at runtime.
```

Higher-level crates such as `npa-frontend`, `npa-api`, `npa-tactic`,
`npa-cli`, and package authoring helpers are outside the core trust boundary.
They may produce or orchestrate certificates, but they are not proof evidence.

## 2. Trust Boundary

Trusted proof evidence is:

```text
- canonical .npcert bytes
- Rust kernel / fast verifier verdict
- source-free reference checker verdict
- deterministic export_hash, certificate_hash, and axiom_report_hash
- recomputed axiom reports and import hashes
```

Untrusted helper input is:

```text
- .npa source text
- parser, resolver, elaborator, and notation handling
- tactic scripts and tactic search
- AI output, replay files, theorem indexes, and metadata sidecars
- source maps, diagnostics, comments, and pretty-printed goals
- package publish plans and registry metadata
```

The core checker input is canonical core data, not surface syntax. Source maps,
comments, diagnostics, tactic traces, replay traces, and AI traces are not
encoded into the trusted certificate payload.

## 3. Core Syntax

### 3.1 Names

Global names are dotted ASCII component paths.

```text
DeclarationName = Component ("." Component)*
Component       = [A-Za-z_][A-Za-z0-9_']*
```

Only ASCII apostrophe is accepted. Empty components, operator names, Unicode
prime-like characters, and source notation names are rejected.

Binder names in `Expr` are display/debug data. The certificate term DAG stores
lambda, pi, and let binders without binder display names. Binding structure is
represented by de Bruijn indexes.

### 3.2 Universe Levels

The implemented level grammar is:

```text
Level ::=
  zero
| succ Level
| max Level Level
| imax Level Level
| param Name
```

Abbreviations:

```text
Prop   = Sort zero
Type u = Sort (succ u)
```

Universe parameters must be declared, sorted, unique, and free of unresolved
meta-like names such as `?u` or internal human-universe metavariable names.

### 3.3 Terms

The implemented core term grammar is:

```text
Term ::=
  Sort Level
| BVar u32
| Const Name [Level]
| App Term Term
| Lam binder : Term, Term
| Pi  binder : Term, Term
| Let binder : Term := Term in Term
```

The certificate `TermNode` representation uses the same logical constructors
but stores table references and omits binder display names.

The core calculus has no holes, unresolved metavariables, implicit arguments,
notation, tactic blocks, source-level macros, or source-level match syntax.

## 4. Universe Behavior

### 4.1 Sort Hierarchy

The kernel and reference checker implement:

```text
Sort u : Sort (succ u)
```

`Sort u : Sort u` is not accepted.

### 4.2 Level Normalization

Level normalization is deterministic. The implemented reductions include:

```text
max u u        => u
max zero u     => u
max u zero     => u
max n m        => the larger numeral, when both sides are numerals
max u v        => operands sorted into canonical order otherwise

imax u zero     => zero
imax u (succ v) => max u (succ v)
```

Other `imax` expressions remain as canonical `imax` nodes after recursive
normalization of their children.

### 4.3 Universe Constraints

Declarations may carry sorted, duplicate-free universe constraints:

```text
Level <= Level
Level = Level
```

The current v0.2.0 implementation records these constraints in declaration
payloads, public export entries, certificates, certificate-side hashes, and
checker validation. Public export entries carry `universe_constraints`
immediately after `universe_params`, so downstream imports reconstruct the
same public signature constraints that the producer checked.

It validates:

```text
- declared, sorted, unique universe parameters
- well-formed constraint levels
- normalized constraint levels
- sorted, duplicate-free constraint vectors
- rejection of unresolved universe metavariables
- satisfiable declaration universe contexts for the supported fragment
```

The implemented solver is a conservative difference-constraint fragment.
`UniverseContext` decomposes supported constraints into atom inequalities over
`zero`, declared universe parameters, and finite `succ` offsets. `max` is
supported on the left-hand side by decomposing it into obligations for each
atom. Equality is checked as both directions of `<=`. `imax` is supported only
when deterministic level normalization reduces it to this fragment. A
right-hand side that decomposes to multiple atoms, nonlinear arithmetic, or any
level shape outside this fragment is rejected as an unsupported universe
constraint.

The kernel and reference checker reject unsatisfiable declaration contexts. A
constant reference checks universe arity and well-formed level arguments, then
substitutes the referenced declaration's public constraints over the supplied
levels and requires the current universe context to entail every resulting
obligation. This applies to local, imported, and generated public signatures,
including inductive constructors and recursors that inherit the parent
inductive or mutual block constraints.

Definitional equality still compares levels by deterministic normalization,
not by using declaration constraints to prove additional level equalities.
General Presburger arithmetic, SMT-backed universe solving, and constraint
reasoning outside the documented fragment remain outside the v0.2.0 core.

## 5. Typing

Typing is implemented by inference plus conversion checking.

```text
infer(ctx, delta, term) -> type
check(ctx, delta, term, expected) succeeds when infer(term) is defeq expected
```

The implemented typing rules cover:

```text
Sort
BVar lookup through the local context
Const lookup with universe arity check and level substitution
Pi formation with imax sort computation
Lam inference
App with weak-head reduction of the function type to Pi
Let with local definition context and zeta behavior
Conversion through definitional equality
```

Local definitions are part of the local context. Looking up a local definition
supports both type lookup and weak-head zeta unfolding.

Errors are structured enums in the fast kernel and deterministic structured
errors in the reference checker. Human strings are not the acceptance boundary.

## 6. Definitional Equality And Reduction

The implemented conversion checker is deterministic and fuel-limited. It
returns rejection when resource fuel is exhausted.

Definitional equality is generated by:

```text
alpha equivalence through de Bruijn representation
beta reduction
delta reduction for reducible definitions
iota reduction for generated recursors
zeta reduction for let and local definitions
```

The following are not definitional equality:

```text
eta conversion
proof irrelevance conversion
theorem proof unfolding
opaque definition unfolding
axiom unfolding
equality-class proof terms as equality normalization
```

Theorems are checked with proof bodies but exported as opaque constants. Opaque
definitions retain their bodies for certificate checking, but their bodies are
not exported for downstream delta reduction.

## 7. Declarations

The implemented declaration model includes:

```text
Axiom
Def
Theorem
Inductive
Constructor        (environment artifact generated from an inductive)
Recursor           (environment artifact generated from an inductive)
MutualInductiveBlock
```

Certificate source declarations encode axioms, definitions, theorems,
inductives, and mutual inductive blocks. Constructors and recursors are
generated public artifacts of inductive declarations rather than separate
source declarations.

Declaration checking behavior:

```text
Axiom:
  type must infer to a Sort.

Def:
  type must infer to a Sort.
  value must check against type.
  reducibility is either Reducible or Opaque.

Theorem:
  type must infer to a Sort.
  proof must check against type.
  theorem is exported as opaque.

Inductive:
  names must be fresh.
  universe context and result sort must be well formed.
  constructor types and generated recursor shape are checked.
  generated constructors and recursor are inserted atomically.

MutualInductiveBlock:
  all family names and generated names must be fresh.
  families share universe parameters and parameter telescope.
  constructors and recursors are checked against the whole block.
```

Certificates canonicalize declaration order by local dependencies. At each
dependency depth, declarations are ordered by canonical name. Reference checking
rejects non-canonical declaration order.

## 8. Inductives

### 8.1 Supported Shapes

v0.2.0 supports more than the older v0.1 baseline:

```text
- simple inductives
- indexed inductive families
- mutual inductive blocks
- approved nested recursive occurrences through exact List, Option, and Prod
  functor declarations
```

Generic coinductives are not implemented.

### 8.2 Declaration Shape

An inductive declaration carries:

```text
name
universe_params
universe_constraints
params
indices
sort
constructors
optional recursor
```

The conceptual type of the inductive family is:

```text
Pi params, Pi indices, Sort sort
```

### 8.3 Constructor Rule

Each constructor type must end in the target inductive family with canonical
parameters and the expected universe parameters.

```text
Pi fields, I params index_args
```

Constructors returning a non-target type, wrong parameter count, wrong
universe arguments, or non-canonical parameter arguments are rejected.

### 8.4 Positivity

The positivity checker is conservative. It allows:

```text
- fields with no recursive occurrence
- direct recursive occurrences as fields
- recursive occurrences under exact approved positive functors:
  List, Option, Prod
- corresponding mutual recursive occurrences inside a mutual block
```

It rejects:

```text
- recursive occurrence on the domain side of a function
- higher-order negative occurrences
- unknown nested functors
- name-only fake approved functors
- recursive occurrences hidden behind unsupported aliases
```

Approved nested functor recognition is structural: the relevant functor
declaration must match the expected canonical shape, not merely the name.

### 8.5 Recursors And Iota

Recursors are generated or checked as part of the inductive artifact. The
current kernel core requires the major premise to be the final binder of the
recursor type.

Iota reduction fires when the major premise weak-head reduces to a constructor
headed term. For recursive fields, the reducer passes the corresponding
recursive recursor call to the minor premise. Mutual recursors route recursive
calls to the recursor of the matching family.

For Prop-valued inductives, the recursor motive must return Prop. Singleton
elimination exceptions are not implemented.

### 8.6 Initial Builtins

The default builtin environment contains:

```text
Nat
Nat.zero
Nat.succ
Nat.rec

Eq
Eq.refl
Eq.rec
```

`Nat` and `Eq` are introduced through inductive declarations and generated
artifacts. `Eq.rec` is a builtin axiom with the standard policy exception used
by the checker boundary.

## 9. Optional Core Feature Profile

The current active core profile has no optional core features. Certificate
feature reports are still parsed and enforced so that unsupported future
features fail closed, but no built-in equivalence-class primitive,
relation-bundle primitive, or related reduction rule is part of this
implementation boundary.

## 10. Certificate Schema

The v0.2.0 implementation uses these current certificate tags:

```text
format:    NPA-CERT-0.2.0
core_spec: NPA-Core-0.2.0
```

The previous-format tags preserve their v0.1.2 hash domains and export-block
shape:

```text
format:    NPA-CERT-0.1.2
core_spec: NPA-Core-0.1.2
```

The legacy tags are accepted only through the compatibility rule described at
the top of this document:

```text
format:    NPA-CERT-0.1
core_spec: NPA-Core-0.1
```

The logical certificate layout is:

```text
Certificate:
  header:
    format
    core_spec
    module
  imports
  name_table
  level_table
  term_table
  declarations
  export_block
  axiom_report
  hashes:
    export_hash
    axiom_report_hash
    certificate_hash
```

Imports contain:

```text
module
export_hash
optional certificate_hash
```

Normal mode resolves imports by module and export hash and permits a missing
certificate hash. If a certificate hash is present in normal mode, it must
match. High-trust mode requires the imported module to have been verified in
the current session with the exact certificate hash.

## 11. Canonical Binary Encoding

On-disk `.npcert` files are canonical binary. The verifier decodes bytes and
then re-encodes the decoded certificate; byte mismatch is rejection.

Canonical encoding uses:

```text
- fixed field order
- explicit vector lengths
- minimal unsigned variable-length integer encodings
- UTF-8 strings with canonical name validation
- sorted import table
- sorted reachable name table
- topologically ordered level and term DAGs
- normalized level nodes
- dependency-ordered declarations
- sorted dependency and axiom vectors
- no unreachable name, level, or term table entries
```

The binary payload has no whitespace, comments, source maps, notation,
implicit arguments, unresolved metavariables, tactic scripts, or AI traces.

## 12. Hashes And Reports

The implemented hash domains include:

```text
NPA-MODULE-EXPORT-0.2.0
NPA-MODULE-EXPORT-0.1.2    previous-format compatibility
NPA-AXIOM-REPORT-0.1
NPA-MODULE-CERT-0.2.0
NPA-MODULE-CERT-0.1.2      previous-format compatibility
NPA-LEVEL-0.1
NPA-TERM-0.1
NPA-CORE-EXPR-0.1
NPA-UNIVERSE-CONSTRAINTS-0.1
```

The export block is derived from declarations. It exports:

```text
- axiom interfaces
- definition interfaces and reducible bodies
- theorem interfaces without proof bodies
- inductive family interfaces
- generated constructor interfaces
- generated recursor interfaces
```

Each exported interface includes `universe_params` and
`universe_constraints`. Interface hashes and export hashes commit the
constraint field. Changing exported constraints changes the declaration
interface hash and module export hash.

The axiom report is recomputed during verification. It records direct and
transitive axiom dependencies per declaration, module-wide axiom dependencies,
and required core feature profiles.

Changing opaque theorem proof bodies does not change the export hash unless the
change alters axiom dependencies. It does change the certificate hash.

## 13. Reference Checker Boundary

The reference checker accepts only:

```text
- canonical certificate bytes
- a source-free import store
- checker policy
```

It rejects `.npa` source paths as certificate or policy inputs and does not
read tactics, source maps, replay data, package indexes, or AI artifacts.

The reference checker performs:

```text
- decode and structural validation
- canonical order checks
- hash recomputation
- import resolution
- core feature policy enforcement
- axiom report recomputation
- source-free semantic type checking
- deterministic structured rejection reporting
```

Its semantic checker implements the same core term typing, weak-head reduction,
definitional equality, universe-constraint validation and entailment, inductive
checks, recursor iota behavior, approved nested positivity policy, mutual
inductive behavior needed to check current v0.2.0 certificates.

## 14. Unsafe Policy

The trusted Rust core does not use unsafe code in `npa-kernel`, `npa-cert`, or
`npa-checker-ref`. The reference checker crate explicitly forbids unsafe code.

Unsafe code or non-Rust unsafe primitives that appear in higher-level API,
automation, profiling, external checker experiments, or unrelated tooling are
outside this core specification unless they are moved into the kernel,
certificate verifier, or reference checker trust boundary.

## 15. Out Of Scope For v0.2.0 Core

The following are not part of the v0.2.0 core implementation contract:

```text
- eta conversion
- proof irrelevance as conversion
- theorem proof unfolding
- axiom unfolding
- using universe constraints as definitional equality assumptions
- general Presburger, SMT-backed, or nonlinear universe solving
- typeclass search as trusted proof checking
- unresolved metavariables in certificates
- source-level macros
- source-level pattern matching as trusted syntax
- general recursion
- coinductives
- external SMT solver trust
- theorem graph trust
- AI search trust
```

Advanced automation may use some of these concepts outside the trusted
boundary, but accepted proof evidence must return to canonical certificate
checking.

## 16. Focused Validation Commands

For core-only validation of this implementation boundary:

```sh
cargo test -p npa-kernel -p npa-cert -p npa-checker-ref
```

For normal repository development outside the proof corpus:

```sh
./scripts/check-fast.sh
```

Run package fixture and external-checker / high-trust gates only at package
verifier, certificate compatibility, release, or high-trust boundaries. Public
package-author commands are described in `npa-toolchain-reference-v0.2.0.md`;
contributor gates are described in `../CONTRIBUTING.md`.
