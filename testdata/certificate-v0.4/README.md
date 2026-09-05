# Certificate v0.4 Fixture Contract

Status: active three-checker fixture contract as of let-removal Milestone 4.
The fast producer/verifier, Rust reference checker, and clean-room OCaml
checker consume this matrix directly. Canonical v0.4 integration certificates
live in `../../checkers/npa-checker-ext/test/fixtures/conformance/`; the
remaining rows use independently constructed test builders.

[fixture-matrix.tsv](fixture-matrix.tsv) is the single case inventory that the
producer/fast-verifier tests and both independent checker suites must consume.
Milestone 3 added the canonical byte fixtures and Rust assertions. Milestone 4
adds an independent OCaml matrix reader, six-form encoder checks, complete
header-pair rejection coverage, retired-tag checks, and live three-checker
differential identity comparisons. No consumer may add a failing or ignored
transitional row.

The tab-separated columns are:

```text
case_id
class
template
format
core_spec
mutation
producer_fast_or_frontend_result
rust_ref_result
ocaml_result
hash_or_boundary
```

`-` and `not_applicable` mean that a field has no consumer for that case.
The first result column is the producer/fast-verifier outcome for certificate
rows and the Human/Machine frontend outcome for source rows. `checked` is
semantic certificate success; `accepted` is source-token success;
`unsupported_format`, `format_mismatch`, `core_spec_mismatch`,
`unsupported_encoding:0x06`, `unknown_tag:0x06`, and the named hash errors are
exact structured outcomes. Package-level wrappers may add context but must
preserve the named leaf reason.

Every `source_*` row is run independently through both the Human and Machine
frontends; the shared result cell applies to both runs. Every source-rejection
row also inherits the specification's exact `RemovedTermLet` variant,
`removed_term_let` wire kind, and `let`-lexeme span. The Machine API run must
add phase `machine_term_parse`, while the Human LSP run has no Machine phase
field. These are two assertions over one shared token case, not permission to
test only one source surface.

## Fixture Templates

The future test builders independently construct these templates:

- `minimal_six_form_module`: one fully canonical, semantically valid v0.4
  module whose reachable term table includes all tags `0x00` through `0x05`.
- `node_codec_fixture`: one independently constructed canonical module per
  matrix row. Its earlier table entries, binders, and declarations are chosen
  so the named target node is reachable, has the exact listed fragment, and is
  semantically valid; IDs are local to that row rather than shared across the
  six rows.
- `reduction_module`: a canonical v0.4 module with separate successful beta,
  delta, and iota declarations and no local definition.
- `deep_binders_module`: a maximum-interest but in-limit lambda/pi binder chain
  built iteratively.
- `shared_dag_module`: a canonical DAG in which multiple parents reuse the
  same earlier term nodes.
- `stable_payload_pair`: semantically identical six-form v0.3 and v0.4 payloads
  used only to compare retained hash domains; the v0.3 member is historical
  test input, never accepted by a v0.4 decoder.
- `empty_module_v3`: a canonical historical v0.3 module with empty tables,
  declaration vector, exports, and axiom report. Replacing only its equal-length
  header strings reaches the final module hash without an earlier declaration
  hash and must fail there.
- `reduction_without_let_exports`: the rebuilt Reduction module after its two
  let-only public declarations have been deleted.
- `source_snippet`: a lexer/parser input, not certificate bytes.

For header cases, the builder starts with `minimal_six_form_module`, replaces
only the two length-prefixed header strings with the matrix values, and leaves
the remainder untouched. The one current/current row uses the unmodified
canonical fixture. Every other row must reject at the header before hashes or
the body are considered.

The exact standalone term-node fragments, excluding the term-table length,
are:

```text
Sort level 0                  0000
BVar 0                       0100
Const Local(0), no levels    02010000
App term 0 term 1            030001
Lam type 0 body 1            040001
Pi type 0 body 1             050001
former Let 0 0 0             06000000
```

The full `node_codec_fixture` builder supplies the declarations, levels,
context, roots, canonical ordering, and hashes needed to make each positive
row semantically valid. A fragment is not itself a certificate, and the
numeric IDs in fragments from different rows do not refer to one shared table.

## Independence And Instrumentation

Rust and OCaml tests read the same rows and fixture bytes, but each suite must
independently decode headers, tags, tables, hashes, and semantics. The OCaml
suite must not call the Rust producer to determine an expected verdict. Golden
bytes may be generated once by the canonical producer and then checked in only
after both independent implementations have reviewed their layout.

The retired-tag cases require a decoder test hook or counting reader that
records bytes read and allocation attempts after the tag. For `0x06`, both
counts must be zero. The `retired_06_unused` case proves that reachability
does not hide the retired tag; the truncated and oversized-tail cases prove
that no former child is decoded before rejection.

The matrix must remain free of `ignore`, `skip`, `todo`, or expected-failure
markers. A `not_applicable` source cell is not a skipped checker assertion: the
source-free checkers intentionally have no source parser. Until the applicable
assertions land atomically, the matrix is a reviewed contract rather than a
partially wired test.
