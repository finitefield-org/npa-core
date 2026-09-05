# NPA Toolchain Reference v0.9.0

This is the current, self-contained toolchain reference. It describes the
only supported current host: `npa-cli 0.9.0`, with the certificate/core pair
`NPA-CERT-0.4.0` / `NPA-Core-0.4.0` and checker `npa-checker-ext 0.4.0`.

## Install and build

Use Rust 1.95.0 and build the repository-local CLI:

```sh
rustup toolchain install 1.95.0 --profile minimal
cargo +1.95.0 build --locked -p npa-cli
target/debug/npa --version
```

The last command must print `npa 0.9.0`. Package commands take the directory
containing `npa-package.toml` through `--root`; they never infer a package root
from the container repository.

## Canonical package gates

After editing Human Surface source, run the lexer-aware structure check. Before
publication, use the canonical writer and then every cache-disabled check:

```sh
npa package check-source-structure --root PACKAGE_ROOT --json
npa package build-certs --root PACKAGE_ROOT --update-manifest-hashes --json
npa package build-certs --root PACKAGE_ROOT --check --json
npa package verify-certs --root PACKAGE_ROOT --package-lock checked \
  --checker reference --audit-cache off --verifier-memo off --json
npa package check-hashes --root PACKAGE_ROOT --json
npa package axiom-report --root PACKAGE_ROOT --check --json
npa package index --root PACKAGE_ROOT --check --json
npa package theorem-premise-report --root PACKAGE_ROOT --check --json
npa package export-summary --root PACKAGE_ROOT --check --json
npa package publish-plan --root PACKAGE_ROOT --check --json
npa package check-generated --root PACKAGE_ROOT --json
```

Canonical `.npcert` bytes, source-free checker verdicts, deterministic hashes,
and axiom reports are evidence. Source, metadata, indexes, replay files,
command results, and cache entries are untrusted sidecars. Do not hand-edit
hashes or generated locks.

## Authoring cache boundary

`build-certs --build-check-cache read-through` is an advisory live-check loop.
`build-certs --check --module MODULE --build-check-cache local-hit` may reuse
an exact support context for a targeted authoring check. Both modes are local
feedback only; release and completion gates remain cache-off. The separate
`verify-certs --audit-cache` option is also never proof evidence.

## Checker and export contracts

The independent Rust reference checker and the OCaml clean-room checker accept
only the exact v0.4 pair. The Lean exporter consumes source-free certificates,
uses the same pair, and requires a direct Lean 4.31.0 binary. Export success is
not a replacement for NPA certificate verification.

## Compatibility and history

The v0.9 host is a breaking source/API boundary. Packages must be rebuilt with
the v0.4 certificate/core pair; changing only a header is invalid. Historical
specifications remain version-scoped records and are not supported host lanes.
