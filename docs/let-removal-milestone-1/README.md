# Let-Removal Milestone 1 Contract Freeze

Status: completed on 2026-09-04 for Milestone 1 only. This milestone freezes
the v0.4 wire, hash, source-diagnostic, sidecar, and fixture contracts. It does
not change a producer, parser, kernel, checker, package artifact, or accepted
test yet.

The implementation source audited here is unchanged from the final let-capable
checkpoint `5d22858ffed16d75bcf01a61381abdb4040ae275`. The working branch began
this milestone at documentation commit
`b8d8345c1b956cea753e7af2aedbdb67908f3c77`.

Every retained file in this directory other than the checksum manifest is
bound by [SHA256SUMS](SHA256SUMS).

## Frozen Deliverables

- [Core Specification v0.4.0](../core-spec-v0.4.0.md) is the self-contained
  normative target. It fixes the six term tags, permanently retires `0x06`,
  fixes hash domains, preserves the v0.3 tagged dependency layout and
  same-module opaque behavior, defines the source tombstone, and accepts only
  `NPA-CERT-0.4.0` / `NPA-Core-0.4.0`.
- [canonical-tag-disposition.tsv](canonical-tag-disposition.tsv) assigns every
  discovered implementation identity exactly one reviewed disposition.
- [canonical-identity-inventory.txt](canonical-identity-inventory.txt) is the
  sorted raw input to that disposition ledger.
- [advanced-ai-encoder-callers.tsv](advanced-ai-encoder-callers.tsv) traces all
  calls to the three shared Advanced AI expression/local-context encoders.
- [Certificate v0.4 Fixture Contract](../../testdata/certificate-v0.4/README.md)
  and its [shared matrix](../../testdata/certificate-v0.4/fixture-matrix.tsv)
  freeze the Rust/OCaml conformance cases without wiring an intentionally
  failing transitional test.
- [Temporary v0.8 Baseline Command Ledger](v0.8-baseline-command-results.md)
  records the one-time path-normalized argument vectors and their exact
  results. It is internal migration material, not a user verification path.
- [Milestone 7 deletion ledger](milestone-7-deletion-ledger.tsv) registers all
  new raw commands/helpers and the inherited v0.7/v0.8 cleanup surface.

## Closed Wire And Compatibility Decisions

There is one current pair and no compatibility branch:

```text
NPA-CERT-0.4.0
NPA-Core-0.4.0
```

All 25 combinations of the current and four known old format/core strings are
enumerated in the fixture matrix. Only current/current continues past the
header. Three additional rows cover unknown format, unknown core, and both
unknown. Format is checked first, so every old or unknown format returns the
format error even if its core string is also invalid. A current format with an
old or unknown core returns the core-spec error. Header rejection precedes
module, import, table, body, allocation, and hash decoding.

The term table has exactly:

```text
0x00 Sort     0x01 BVar     0x02 Const
0x03 App      0x04 Lam      0x05 Pi
```

`0x06` is permanently unassigned and rejects as soon as its tag byte is read.
No former child index is consumed and no former-child allocation is attempted.
The same rule covers reachable, unused, truncated, and oversized-tail nodes.

Declaration and module certificate domains advance to
`NPA-DECL-CERT-0.4.0` and `NPA-MODULE-CERT-0.4.0`. The term and both direct and
Merkle core-expression domains retain their identities because the six
surviving payloads are byte-for-byte unchanged and `0x06` is unreachable.
Level and universe-constraint payloads are unaffected. Public interface,
export, and axiom-report layouts retain their domains because every affected
descendant is rebound through a current term, interface, or module hash.

Both source surfaces reject the exact `let` identifier before AST creation as
`RemovedTermLet`, wire kind `removed_term_let`; Machine API classifies it in
phase `machine_term_parse`. Comments, strings, and `letter` do not trigger it;
`in` is an ordinary identifier.

## Canonical Identity Audit

The temporary generator scans quoted canonical/versioned identities in Rust,
OCaml, Shell, JavaScript, and TypeScript implementation/checker/tooling roots:

```text
npa-core/crates
npa-core/checkers
npa-core/scripts
npa-lean-exporter/crates
npa-lean-exporter/scripts
npa-agents/apps
npa-agents/crates
npa-agents/scripts
npa-web/src
tools
```

Documentation, generated artifacts, package source, and testdata are excluded
as identity definitions; identity occurrences inside implementation-unit tests
remain included because those tests are below scanned source roots.

The reviewed inventory contains 787 unique identities and the disposition
ledger contains exactly 787 data rows. Milestone 5 execution added the
escaped-string `package-compare` identity that the original generator missed
and corrected the four WHNF sidecars that inline the removed zeta field:

| Disposition | Count | Meaning |
| --- | ---: | --- |
| `bump` | 118 | Own bytes, meaning, semantic epoch, current host, or closed vocabulary changes; the row names the replacement or deletion. |
| `retain-with-domain-separated-child` | 172 | Own layout is unchanged and every affected child is explicitly rebound by a new hash, pair, profile, or parser boundary. |
| `unrelated` | 497 | Reviewed identity does not encode the removed term/local value/diagnostic/zeta shape or a current-host compatibility choice. Synthetic negatives, distinct performance axes, generic string hashes, and unrelated schemas are included here. |

No empty, duplicate, invalid, or unclassified disposition remains. Each row
records the first source path and line, occurrence count, exact target, and a
machine-readable rationale. The retained rows were separately inspected for a
real child boundary; an unchanged outer tag is not permission to accept an old
child. The committed ledger is also the generator's reviewed decision
allowlist: a newly discovered identity defaults to `unclassified` and makes the
generator fail until a reviewer assigns it deliberately.

The generated audit confirmed the plan's mandatory sidecar floor and found
these additional direct owners that must advance rather than inherit another
hash implicitly:

```text
NPA-FRONTEND-MACHINE-TERM-CONTEXT-0.1       -> 0.2
npa.cert.local_authoring_producer_abi.v1    -> v2
npa.kernel.local_authoring_context_abi.v1   -> v2
core-spec-v0.1                              -> v0.2
npa-kernel.core.v0.1                        -> v0.2
NPA-DECLARATION-CLOSURE-PROJECTION-TERM-v1  -> v2
NPA-DECLARATION-CLOSURE-PROJECTION-v1       -> v2
NPA-L2-TRANSPORT-PROJECTION-v1              -> v2
NPA-L2-TRANSPORT-CLOSURE-v1                 -> v2
npa.kernel-whnf-application-spine.measurements.v0.1 -> v0.2
npa.kernel-whnf-application-spine.micro-child.v0.1 -> v0.2
npa.kernel-whnf-application-spine.package-child.v0.1 -> v0.2
npa.kernel-whnf-application-spine.package-compare.v0.1 -> v0.2
```

The projection-term and L2 projection formats inline the changed term grammar;
their outer closure formats then hash those changed inline bytes. The frontend
and local-authoring ABIs directly describe the term/context shape. These are
therefore hard implementation requirements for Milestones 2, 3, and 5.

The agent platform, `npa-client` envelopes, and theorem-index schema were also
included in the widened scan. Their layouts retain their identities because
they bind rebuilt current certificate/state/diagnostic hashes or validate a
separately owned nested payload; the current pins and values still change in
Milestone 6.

The same rule is explicit for Human incremental-document hashes, package audit
and build-check caches, targeted-authoring support caches, proof-candidate and
proof-hole scheduling envelopes, parent-proof/local-lemma/theorem-invention
lifecycle records, focused-replay subhashes, and standard-library artifacts.
Their outer layouts remain unchanged, but old values cannot cross the new
pair, ABI, parser, profile, state, certificate, or verifier hash boundaries.

## Advanced AI Trace

The trace has 38 call sites: 30 `encode_expr_to`, seven `encode_goal_to`, and
one `encode_machine_local_decl_to`. It distinguishes public owners, recursive
calls, test-only calls, and the exact calls removed with the local value and
retired term branch.

Every public Advanced AI owner that inlines a goal, local declaration, or core
expression advances from v1 to v2. An outer Advanced AI envelope retains its
identity only when the trace and ledger show that it contains a newly
domain-separated child hash rather than inline changed bytes. Milestone 3 must
compare the live caller inventory against this trace before consuming it.

## Shared Fixture Matrix

The shared matrix contains 72 cases:

| Class | Cases |
| --- | ---: |
| complete known plus unknown header matrix | 28 |
| six positive term encodings | 6 |
| beta/delta/iota semantics | 3 |
| iterative structure and shared DAG | 2 |
| retired `0x06` boundaries | 6 |
| retained/bumped hash expectations | 10 |
| hash rejection | 3 |
| old and mixed import closure rejection | 3 |
| source tombstone/token boundaries | 11 |

The matrix freezes exact header strings, node fragments, structured outcomes,
domain relationships, and rejection boundaries. It contains no ignored,
skipped, TODO, or expected-failure test. Milestone 3 must add canonical bytes
and Rust assertions atomically with the Rust format change. Milestone 4 must
consume the same rows in OCaml while preserving an independent decoder,
hasher, and semantic implementation.

## Temporary v0.8 Record And Final Deletion

The baseline command ledger records only the already completed one-time audit
against the SHA-bound detached checkpoint. It does not create a tag, release,
asset, reusable bundle, or supported old verifier. Random temporary path
prefixes are normalized to labels; the certificate inputs are bound by their
complete checksum manifests, and all semantically relevant flags and argument
order are retained.

Milestone 7 must first copy the non-executable commit, checksum, checker
identity, and pass/checked summary into the v0.9.0 release note. It then deletes
the raw command ledger, helper, raw inventories/results/manifests, and all live
v0.7/v0.8 operational paths enumerated by the deletion ledger. It must not
delete the shared v0.4 fixture matrix or this v0.4 specification.

## Verification Performed

Milestone 1 verification is structural because production behavior has not
changed. The review gate regenerates the ledger, proves stable output and exact
row coverage, checks all three dispositions and the Advanced AI call-site
inventory, validates the 25-row header cross product and all 72 matrix rows,
checks local Markdown links, checks whitespace, and reviews the complete diff.

No Rust or OCaml semantic test is expected to pass against v0.4 in this
milestone; adding such a test before the producer/checker transition would
create the intentionally failing intermediate state that the plan forbids.
