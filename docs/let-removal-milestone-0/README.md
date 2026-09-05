# Let-Removal Milestone 0 Baseline Evidence

Status: completed on 2026-09-04 for Milestone 0 only. The implementation base
and final let-capable container checkpoint are
`5d22858ffed16d75bcf01a61381abdb4040ae275`, fetched as `origin/main` before
the inventory. No let-removal implementation, format bump, tag, release, or
release asset is created here.

This directory is untrusted implementation evidence. It is not proof evidence,
not a supported old-toolchain distribution, and not a verification procedure
for users. The temporary checkouts, audit helpers, binaries, and source-free
bundles used to produce it were kept outside tracked and release surfaces and
were deleted after collection. Milestone 7 must delete the raw checker-result
and bundle-manifest files after carrying their non-executable identity and
verdict summary into the v0.9.0 release note. The path and decoded-term
inventories may remain as historical migration evidence because they contain no
executable compatibility path.

Every retained evidence file in this directory, other than the checksum
manifest itself, is bound by [SHA256SUMS](SHA256SUMS).

## Frozen commits and trees

| Identity | Value |
| --- | --- |
| Container implementation base and final let-capable checkpoint | `5d22858ffed16d75bcf01a61381abdb4040ae275` |
| Container root tree | `3369ab98a01879f1c1bbaf0d36ace132967decae` |
| Container `npa-core` subtree | `30a32721384162e01662a568fa7acdd72f52993b` |
| Standalone remote `main` observed before the checkpoint | `144cdba6f5d52b2955818ce66f7a8fc93adbbe51` |
| Observed standalone `main` tree | `75ce5effe935106c0fc1e3e48c9bcd796a2875e8` |
| Unpublished standalone checkpoint | `a216383edb1a3dd789ccb1391800d1d34a6a6676` |
| Unpublished checkpoint parent | `144cdba6f5d52b2955818ce66f7a8fc93adbbe51` |
| Unpublished checkpoint tree | `30a32721384162e01662a568fa7acdd72f52993b` |

The standalone remote lagged behind the fetched container subtree, so using
its `main` commit would not have frozen the implementation being migrated. A
clean clone of standalone `main` was populated with the exact tracked
`5d22858ff:npa-core` tree and committed locally with parent `144cdba6`, author
and committer `NPA Baseline Recorder <npa-baseline@users.noreply.github.com>`,
timestamp `2026-09-04T11:57:01+09:00`, and subject
`Checkpoint npa-core from npa-container 5d22858ff`. The resulting detached,
unpublished commit is `a216383e`; its tree is byte-for-byte the same Git tree
as the container subtree. It was never pushed or named by a branch or tag.

The standalone archive SHA-256 is
`f5e4981285200f116116a129ed8dcbd6021de76fb6c4c88fb4f0416e66e8dbcf`.
The container prefix archive SHA-256 is
`3e570359ae7e0a424a97e82a10538f47dd826c585e43528071b639e6ea6d7c71`;
the archive hashes differ because the latter retains the `npa-core/` path
prefix, while the Git tree identity above establishes tracked-tree
equivalence.

The endpoint assertion passed before any audit helper was introduced:

- `crates/npa-cli/Cargo.toml` reports `npa-cli 0.8.0`;
- `crates/npa-cert/src/lib.rs` emits `NPA-CERT-0.3.0` and
  `NPA-Core-0.3.0`;
- the Rust reference checker advertises that same pair; and
- the OCaml checker advertises that same pair.

## Build inputs and checker identities

There is no tracked `rust-toolchain` or `rust-toolchain.toml` in the checkpoint.
The clean detached build therefore used the recorded active host toolchain.

| Input or output | Identity |
| --- | --- |
| Active Rust toolchain | `stable-aarch64-apple-darwin (default)` |
| `rustc` | `1.97.1 (8bab26f4f 2026-07-14)`, host `aarch64-apple-darwin`, LLVM `22.1.6` |
| `cargo` | `1.97.1 (c980f4866 2026-06-30)`, host `aarch64-apple-darwin` |
| `ocamlc` | `5.4.1` |
| Host | Darwin `25.5.0`, `arm64` |
| `Cargo.lock` SHA-256 | `eede524a812effddcde0aa7bc0850c2d53d68b4eeed0241425e5efeb2073b47b` |
| Workspace `Cargo.toml` SHA-256 | `806b7b14d6bed6e15b3cd397db8fa61dbac2abf3661ea86ab7b000548b3dd6bf` |
| `npa-cli` manifest SHA-256 | `44e32256916a5fc13496b56e370935808b848fe936d22fdd4f733e93ac02ee6a` |
| Locked/offline Cargo metadata SHA-256 | `1039ccae1f40d10be20d2995cc212eef65acd2a5580b9aead5bc8d3bb1edea6d` |
| `npa-cert` source boundary SHA-256 | `24778b5fa9e2009424deeca4d7f3d2bf4f06f1872a9f741bc2c97751ed0a37d2` |
| Rust reference source boundary SHA-256 | `6da41d970b9f0f49e793cee42e7fb74a6c548d750f95b0c6e668ceebd810f281` |
| OCaml certificate decoder source SHA-256 | `99ffd867e01bb45d4d85ab62db8197c18a5e7860334cd81613760aab170870f4` |
| `npa 0.8.0` binary SHA-256 | `33662c62caa1f2c69cd40f3644ca4416649e64a70ec39965b1b9597b93d135bb` |
| Rust reference binary SHA-256 | `339dba1d32ebf6d3566192c392bfdd50d4e950d3a25f0fa876900defd89c3083` |
| Rust reference semantic identity | `npa-checker-ref 0.4.0`, build hash `sha256:60ffe42ecdac82d459181ba04ae8f7281d020206ef8588b794c37350a98b969e` |
| OCaml checker binary SHA-256 | `7094f79d9bf7a26b230841ce5d24a13ef80fe4f14f0ec780721685f1e223237f` |
| OCaml checker semantic identity | `npa-checker-ext 0.3.0`, build hash `sha256:9aa52e8766e816e239395bbf3a1a0e33adab4cb741693a6160e9e904611e70eb` |

The term-tag helper and Reduction-interface helper were temporary Rust examples
compiled only inside the detached checkout. Their source SHA-256 values were
`99eb9b71526f217dc9e56c803fdae11c79b499d1b4d022a3edf5158786d55dac`
and `78fd1431d45a81e55eb2cfdbb57713a60b29f4d3c5754838308ffc79a6a16949`;
their binary SHA-256 values were
`efd7ab14f860fee28dab8dbbe479f35f0a042cd037d62ebbe21577b32a15c497`
and `4a4c2be6202fc25eba598df8cc5e3227bb83311a94c3f3645f89ee6bb4830bb5`.
Both sources were removed before the checker builds and verdicts below, and the
temporary binaries were deleted with the checkout.

## Source-free v0.3 checker agreement

The selected certificate was
`npa-mathlib/Mathlib/Core/Reduction/certificate.npcert`, copied without source
to the temporary bundle. Its file SHA-256 was
`5e44933df2dc379e592ac6d993f46b6b6f843005ebd047949b0785c563a8671d`.
Its sole import closure member was `Std.Nat.Basic`, whose copied file SHA-256
was `a84a45eff4172c38592533067f5953adf3dba47a57c5bfda9e824c9679187fe2`.
The policy SHA-256 was
`fb597a7a3fbcc12b8bc8f578cf7338238a5072eb08262a1a771b9afbf054e362`.
The package bundle contained 158 files, including 135 certificates and no
`.npa` source; the direct-checker bundle contained exactly those two
certificates plus the policy and no source. Their complete checksum manifests
are [source-free-v0.3-bundle-sha256.txt](source-free-v0.3-bundle-sha256.txt)
and [v0.3-direct-input-sha256.txt](v0.3-direct-input-sha256.txt).

All required verdicts passed from the clean detached checkpoint:

| Lane | Result |
| --- | --- |
| Fast package verifier | `passed`, live checker, two-module v0.3 closure |
| CLI Rust reference verifier | `passed`, live checker, two-module v0.3 closure |
| Standalone Rust reference checker | `checked` |
| Clean-room OCaml checker | `checked` |

Both independent raw checkers reported module `Mathlib.Core.Reduction`, input
pair `NPA-CERT-0.3.0` / `NPA-Core-0.3.0`, certificate hash
`sha256:5f41593f1808aa002beef370fd9e98fd3b88136d81edee6077829f873aa00c69`,
export hash
`sha256:120b7b3159ffd579eb36f46cdea94f38ae51efb50df31ec6f02f946e395e6b48`,
and axiom-report hash
`sha256:70b2d0f35f9ebfff46bdf399b80487f0c76ffd6460ab930f733af1f889d2fc65`.
The exact untrusted result documents are
[v0.3-fast-verdict.json](v0.3-fast-verdict.json),
[v0.3-reference-cli-verdict.json](v0.3-reference-cli-verdict.json),
[v0.3-reference-binary-verdict.json](v0.3-reference-binary-verdict.json), and
[v0.3-ocaml-verdict.json](v0.3-ocaml-verdict.json).

The Rust reference crate test suite passed 141 tests across its library,
binary, integration, and normal-import suites. The OCaml checker test script
also exited successfully. The certificate-derived `npa-mathlib` theorem-index
check passed; its result is
[npa-mathlib-index-check.json](npa-mathlib-index-check.json). The live
`npa-corpus/proofs` package has no tracked `generated/package-lock.json`, so a
built-in index check is not available there. The direct decoded-certificate
index below covers that Reduction certificate without treating source,
metadata, or a missing generated index as authority.

## Refreshed source and implementation inventory

All counts are anchored to `5d22858ff` and were collected after fetching the
then-current `origin/main`.

| Item | Refreshed count |
| --- | ---: |
| Tracked `.npa` paths | 8,216 |
| `.npa` paths with the accepted typed-let shape | 6 |
| Typed source occurrences | 12 |
| `npa-core` Rust files with known semantic `Let` cases | 46 |
| Out-of-core Rust consumer files | 4 |
| OCaml checker files with semantic `Let` or tag handling | 7 |
| Files with current zeta counters/profile identifiers | 16 |
| Tracked `.npcert` artifacts decoded structurally | 8,337 |

The complete path and occurrence records are:

- [all-npa-paths.txt](all-npa-paths.txt)
- [typed-let-source-paths.txt](typed-let-source-paths.txt)
- [typed-let-source-occurrences.txt](typed-let-source-occurrences.txt)
- [npa-core-semantic-let-rust-paths.txt](npa-core-semantic-let-rust-paths.txt)
- [out-of-core-semantic-let-rust-paths.txt](out-of-core-semantic-let-rust-paths.txt)
- [ocaml-semantic-let-paths.txt](ocaml-semantic-let-paths.txt)
- [zeta-profile-paths.txt](zeta-profile-paths.txt)

## Decoded certificate inventory and producer classification

[term-tag-inventory.tsv](term-tag-inventory.tsv) contains one row for every
tracked `.npcert`, the exact header pair, strict decoder result, and counts for
all seven pre-removal term tags. Its path-list input SHA-256 was
`22eaa6d0382d9710b34cf6d8ce62b0d01e90e4ab013fefc7cdacca2fa38b962b`;
the resulting TSV SHA-256 is
`4540f17a19fa93adbe2219b218b7ce83dc21d8f2a6c4feb8cc7363af8d75beb3`.

| Tag | Count |
| --- | ---: |
| `Sort` / `0x00` | 16,483 |
| `BVar` / `0x01` | 181,655 |
| `Const` / `0x02` | 319,645 |
| `App` / `0x03` | 6,405,706 |
| `Lam` / `0x04` | 2,428,767 |
| `Pi` / `0x05` | 2,539,792 |
| `Let` / `0x06` | 12 |
| All nodes | 11,892,060 |

The header distribution is 5,021 v0.3 pairs, 3,265 v0.2 pairs, 7 v0.1.2
pairs, and 44 v0.1 pairs. The ordinary semantic decoder accepted 8,328
artifacts. Nine old `npa-mathlib` quotient artifacts carry the unsupported
`quotient_v1` feature and therefore fail the ordinary current semantic feature
gate; the pinned decoder's existing non-verifying structural-audit mode decoded
their complete certificate structure and term tables. Their rows record that
strict rejection, and none contains `0x06`. They are unrelated to let
production and are not silently counted as accepted proof evidence.

Every `0x06` row maps to an explicit typed source occurrence and a
`human-surface-explicit-term` manifest producer:

| Artifact | Header pair | `0x06` | Classification | Migration action |
| --- | --- | ---: | --- | --- |
| `npa-mathlib/Mathlib/Core/Reduction/certificate.npcert` | v0.3 | 2 | source-authored | Delete `let_identity_nat` and `let_const_nat`; regenerate the module and package closure under v0.4. |
| `npa-corpus/proofs/Proofs/Ai/Reduction/certificate.npcert` | v0.3 | 2 | source-authored | Delete `let_id_nat` and `let_const_nat`; regenerate the module and package closure under v0.4. |
| `npa-core/testdata/package/npa-mathlib/Mathlib/Core/Reduction/certificate.npcert` | v0.1.2 | 2 | fixture-only | Delete both positive-fixture let declarations and regenerate the fixture under v0.4. |
| `npa-core/testdata/package/npa-mathlib-seed/Proofs/Ai/Reduction/certificate.npcert` | v0.1 | 2 | fixture-only | Delete both positive-fixture let declarations and regenerate the fixture under v0.4. |
| `npa-corpus/fixtures/npa-mathlib/Mathlib/Core/Reduction/certificate.npcert` | v0.3 | 2 | fixture-only | Delete both positive-fixture let declarations and regenerate the fixture under v0.4. |
| `npa-corpus/fixtures/npa-mathlib-seed/Proofs/Ai/Reduction/certificate.npcert` | v0.3 | 2 | fixture-only | Delete both positive-fixture let declarations and regenerate the fixture under v0.4. |

There are zero tactic-produced, zero equation-compiler-produced, and zero
unexplained let-bearing artifacts. No producer blocker remains for Milestone 1.

## Certificate-derived Reduction interfaces

[reduction-certificate-index.tsv](reduction-certificate-index.tsv) was derived
directly from every tracked certificate's decoded import and export tables. It
does not consult `.npa`, manifest theorem lists, metadata, or replay records.
Its SHA-256 is
`23b2eb64ca61beedd74dfee86e2b836ae052526f365c87408598f011b629587f`.

`Mathlib.Core.Reduction` exports the definition `reduction_identity_nat` and
the theorems `beta_identity_nat`, `beta_const_nat`, `let_identity_nat`,
`let_const_nat`, and `delta_identity_nat`. `Proofs.Ai.Reduction` exports the
definition `reduction_id_nat` and the theorems `beta_id_nat`, `beta_const_nat`,
`let_id_nat`, `let_const_nat`, and `delta_id_nat`. Exact module-plus-export-hash
matching across all 8,337 certificate import tables found no downstream
importer of either live Reduction certificate. The let-only declarations can
therefore be deleted without a mathematical client migration; their owning
manifest, metadata, replay, registry, and generated package artifacts still
require coherent regeneration.

## Retired 0.7/0.8 surfaces and deletion ledger

The exact local/remote/hosted query was refreshed at `2026-09-04T04:55:46Z`.

| Surface | v0.7.0 | v0.8.0 | Final disposition |
| --- | --- | --- | --- |
| Fresh-clone local tag | `refs/tags/v0.7.0` -> `34b62dc0de4fed4cbf726627775bd62a9c8b0a20`; object type `commit` (lightweight, so no tag object and the peeled commit is the same commit) | absent | The temporary clone and its fetched local tag were deleted after collection. |
| Standalone remote tag | `refs/tags/v0.7.0` -> `34b62dc0de4fed4cbf726627775bd62a9c8b0a20`; no annotated peel ref | absent | Re-resolve after v0.9.0 publication, require the same identity, delete v0.7.0, and stop on drift. No v0.8 action unless a matching ref appears before the freeze; appearance is a stop condition. |
| Hosted GitHub release | release ID `357554052`, tag `v0.7.0`, not draft/prerelease | HTTP 404 / absent | Re-resolve after v0.9.0 publication, require ID `357554052`, delete it, and stop on drift. |
| Hosted release assets | empty list | absent with the release | No asset deletion for the provisional inventory; re-query immediately before release deletion and stop if assets appear. |

No v0.8 branch, tag, release, or asset was created. The exact tracked
toolchain/compatibility path dispositions are in
[retired-toolchain-entrypoints.tsv](retired-toolchain-entrypoints.tsv). The
broader numeric review is in
[numeric-version-axis-disposition.tsv](numeric-version-axis-disposition.tsv),
with raw path and occurrence inputs in
[numeric-0.7-0.8-content-paths.txt](numeric-0.7-0.8-content-paths.txt) and
[numeric-0.7-0.8-occurrences.txt](numeric-0.7-0.8-occurrences.txt). The specific
scan inputs are [v0.7-specific-content-paths.txt](v0.7-specific-content-paths.txt),
[v0.8-specific-content-paths.txt](v0.8-specific-content-paths.txt), and
[v0.7-v0.8-filename-paths.txt](v0.7-v0.8-filename-paths.txt).

The specific scans found 20 v0.7 content paths, 40 v0.8 content paths, and
8 dedicated filenames, collapsing to 49 unique paths. The broad numeric scan
found 516 occurrences in 104 content paths; 61 were not already in the
specific set. Every one of those 61 paths has an explicit version-axis
classification. Third-party crate versions, performance-measurement schema
versions, synthetic checker/runner fixture versions, mathematical scores, and
TeX dimensions remain distinct from the retired CLI/toolchain axis.

## Temporary material disposition

The following material existed only below `/private/tmp` and was removed after
the recorded checks:

- detached container worktree for `5d22858ff`;
- detached standalone clone and unpublished `a216383e` checkpoint;
- both temporary Rust audit helpers and their binaries;
- the initial v0.2 diagnostic bundle and verdicts;
- the source-free v0.3 package and direct-checker bundles;
- locked Cargo metadata and build output; and
- untracked raw generation workspace used before copying this evidence.

The retained checksum manifests and verdict JSON bind the deleted temporary
inputs and results without preserving a runnable v0.8 toolchain or release
asset.
