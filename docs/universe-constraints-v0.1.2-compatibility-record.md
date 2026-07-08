# Universe Constraints v0.1.2 Compatibility Record

This is the final compatibility and release-gate record for
UC-01 through UC-06 of the universe constraint alignment plan.

The normative implementation snapshot is
the historical v0.1.2 alignment snapshot. The current public implementation
snapshot is [`core-spec-v0.2.0.md`](core-spec-v0.2.0.md). This record
summarizes what must remain true when shipping or consuming certificates
produced after the universe constraint alignment work.

## Scope

The alignment changes the trusted checking behavior for universe constraints
and the certificate public interface that carries them. It does not move
surface syntax, parser output, elaborator output, tactic output, AI output,
package metadata, replay files, or theorem indexes into the trust boundary.

Trusted acceptance remains:

```text
canonical .npcert bytes
Rust kernel / fast verifier verdict
source-free reference checker verdict
deterministic hashes and axiom reports
```

## Compatibility Record

| Area | Current v0.1.2 behavior | Compatibility rule |
| --- | --- | --- |
| Certificate header | New certificates use `NPA-CERT-0.1.2` and `NPA-Core-0.1.2`. | `NPA-CERT-0.1` / `NPA-Core-0.1` remains a legacy decode path only for unconstrained public exports. |
| Module hash domains | Export and module certificate hashes use `NPA-MODULE-EXPORT-0.1.2` and `NPA-MODULE-CERT-0.1.2`. | Level, term, core expression, universe-constraint-vector, axiom-report, declaration-interface, and declaration-certificate domains are unchanged. |
| Public export format | `ExportEntry` carries `universe_constraints` immediately after `universe_params`. The field is always encoded, including an empty vector. | Any consumer of current exports must preserve and recheck this field. Dropping it is a public interface change. |
| Interface hashes | Declaration interface hashes commit the public universe constraints. Export hashes commit the export block including constraints. | Changing exported constraints changes the declaration interface hash and module export hash. Opaque proof-body-only changes still do not change export hash unless public axioms or dependencies change. |
| Imports | Imported public signatures store exported constraints and use them when checking `Const imported levels`. | Normal mode still resolves by module plus export hash, with optional certificate hash. High-trust mode still requires module plus export hash plus certificate hash in the verified session. |
| Generated signatures | Inductive constructors and recursors inherit the parent inductive constraints. Mutual generated signatures inherit the shared mutual-block constraints. | Generated public signatures must not drop parent constraints. Narrower generated constraints would require a later core spec update. |
| Legacy certificates | Old-format certificates decode export constraints as empty. | Old-format certificates whose full declaration payload would export non-empty constraints are rejected with `ConstrainedExportRequiresFormatUpgrade` or the reference checker equivalent. |
| Definitional equality | Level equality remains deterministic normalization equality. | Universe constraints are not used as conversion assumptions. Constraint-aware conversion is out of scope for v0.1.2. |

## Implemented Constraint Boundary

The kernel and reference checker enforce the same conservative
difference-constraint fragment:

- declaration universe parameters must be canonical, sorted, unique, and free
  of unresolved meta-like names;
- declaration universe constraints must be canonical, sorted, duplicate-free,
  normalized, and well formed over declared parameters;
- declaration contexts must be satisfiable inside the supported fragment;
- constant instantiations substitute referenced public constraints over the
  supplied levels and require the caller universe context to entail every
  resulting obligation;
- `max` is supported on the left-hand side by decomposition into atom
  obligations;
- equality is checked as both directions of `<=`;
- `imax` is supported only when deterministic level normalization reduces it to
  the supported fragment;
- unsupported right-hand `max`, nonlinear arithmetic, SMT-style solving, and
  general Presburger reasoning fail closed.

Resource behavior remains bounded by the kernel/reference checker universe
context node and atom-inequality limits. Empty constraint contexts and empty
obligation lists use the documented fast paths.

## Release Checklist

Kernel:

- [x] Declaration universe contexts reject unsatisfiable constraints.
- [x] Constant inference rejects instantiations not entailed by the caller
  universe context.
- [x] Definitional equality does not use universe constraints as assumptions.
- [x] Resource-limit and empty-fast-path behavior is covered by tests.

Certificate producer and verifier:

- [x] Producer APIs emit canonical constraint vectors in current certificates.
- [x] Current certificates use `NPA-CERT-0.1.2` / `NPA-Core-0.1.2`.
- [x] Current export and module certificate hashes use the v0.1.2 domains.
- [x] Public exports include and hash `universe_constraints`.
- [x] Old unconstrained certificates remain readable.
- [x] Old constrained public exports are rejected instead of silently dropping
  constraints.

Reference checker:

- [x] The source-free reference checker preserves imported public constraints.
- [x] Reference checker constant inference enforces the same constraint
  obligations as the kernel-backed verifier for the supported fragment.
- [x] Rejections use stable structured categories where available.

Package compatibility implications:

- [x] This compatibility record does not regenerate checked-in package
  metadata.
- [x] Package compatibility gates are required when public package artifacts,
  canonical encoding, import hashes, package verifier behavior, or release
  artifacts are intentionally changed.
- [x] `npa package ...` fixture gates and `./scripts/check-fast.sh` are the
  public `npa-core` validation boundary for package verifier examples,
  axiom-report, theorem-index, publish-plan, and source-free verifier
  regressions.
- [ ] Run the explicit release or high-trust gates immediately before an
  actual release or high-trust handoff that materializes public package
  artifacts.

## Trust Boundary Audit Note

Universe constraints are enforced only by trusted checking paths:

- `npa-kernel` builds and queries `UniverseContext` during declaration and
  constant checking.
- `npa-cert` canonicalizes, encodes, hashes, decodes, verifies, and replays
  constraints into the Rust kernel.
- `npa-checker-ref` independently decodes source-free certificates, rebuilds
  public signatures, and enforces the same constraint obligations.

The parser, elaborator, tactic engine, AI search, replay sidecars, package
metadata, theorem indexes, and publish plans remain untrusted orchestration.
They may propose declarations or organize certificates, but they do not accept
proofs and cannot override kernel or reference-checker rejection.

## Required Verification For This Record

For this UC-06 record, run:

```sh
./scripts/check-fast.sh
cargo run -q -p npa-cli -- package check --root testdata/package/npa-std --json
cargo run -q -p npa-cli -- package verify-certs --root testdata/package/npa-std --checker reference --json
cargo run -q -p npa-cli -- package check-hashes --root testdata/package/npa-std --json
```

Release and high-trust commands are reserved for the actual release or
high-trust handoff that updates or publishes public package artifacts.
