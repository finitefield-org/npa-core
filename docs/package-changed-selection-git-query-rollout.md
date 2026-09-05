# Package changed-selection Git query rollout

Status: production implementation and deterministic catalog gates complete;
reviewed release benchmark and elapsed comparison pending

Date: 2026-08-13
Updated: 2026-09-02

## Schema allocation

The reviewed implementation base is repository object
`d6e67f0ee1b1e43d6c2b5e6ca2b245aee216e58e`. The design and implementation
remain uncommitted in the shared integration worktree, so this value identifies
the published base, not a fabricated GITSEL source revision.

The active published common measurement schema before GITSEL is
`npa.performance.measurements.v0.4`. Its 136-label table has canonical SHA-256
`2cb98dd1ca9f169095a54df9e630670ca702acf56956a4ab658659c927f344d3`.
The closed same-baseline ledger is:

| Key | State | Source | Decision |
| --- | --- | --- | --- |
| GITSEL | `co_landing` | `docs/core/package-changed-selection-git-query-design.md` | publish the 15 labels below |
| TARGET | `landed` | `docs/core/targeted-build-certs-authoring-cache-design.md` | already published in v0.4 |
| TERM | `landed_after_gitsel` | `docs/core/certificate-term-dag-materialization-design.md` | its 11 labels and `v2-term-materialization` extension are the v0.6 boundary after GITSEL v0.5 |
| SNAP | `co_landed_after_term` | `docs/core/package-certificate-artifact-snapshot-design.md` | its prepared-artifact counters and retained-memory model are part of the v0.7 union |
| VMSP | `co_landed_after_term` | `docs/core/verified-module-shared-payload-design.md` | its payload-ownership counters are part of the v0.7 union |

No sixth same-baseline proposal was found in the audited design ledger. Because
v0.4 is already published, the next-unused allocation is
`npa.performance.measurements.v0.5`. It appends the following exact table to
the complete v0.4 table:

| Identifier | Unit |
| --- | --- |
| `package.selection_exec_budget_policy` | count |
| `package.selection_legacy128_policy` | count |
| `package.selection_candidate_paths` | count |
| `package.selection_pathspec_payload_bytes` | bytes |
| `package.selection_effective_argv_charge_bytes` | bytes |
| `package.selection_max_batch_payload_bytes` | bytes |
| `package.selection_max_batch_argv_charge_bytes` | bytes |
| `package.selection_pathspec_batches` | count |
| `package.selection_worktree_root_queries` | count |
| `package.selection_head_queries` | count |
| `package.selection_tracked_queries` | count |
| `package.selection_untracked_queries` | count |
| `package.selection_tracked_output_paths` | count |
| `package.selection_untracked_output_paths` | count |
| `package.selection_changed_paths` | count |

The resulting 151-label v0.5 table has canonical SHA-256
`d81e90d6d9529de508e058714cc6ce594c2b0866b782e1ce189cbb776377e8be`.
Historical v0.1 through v0.4 readers remain enabled and reject the selection
labels.

The co-landed integration then publishes TERM under the next-unused
`npa.performance.measurements.v0.6`, retaining all 15 GITSEL labels. Its
162-label table has canonical SHA-256
`15a58751513eb9d49583c12f96cbc2050056a942a74ae11858731211f2ca3415`.
The v0.6 nested memory shape adds `prepared_shared_bytes`,
`combined_shared_bytes`, and `term_materialization_bytes_per_worker`; the
strict reader validates `(0, shared_base, 0)` for historical v1 memory and
`(0, shared_base, 268435456)` for `v2-term-materialization`. v0.5 remains a
strict readable historical schema and continues to own the GITSEL introduction
boundary.

The subsequent SNAP/VMSP union publishes
`npa.performance.measurements.v0.7`. It retains the GITSEL v0.5 and TERM v0.6
historical boundaries, appends 30 labels for shared payload ownership and
prepared-artifact snapshot retention, and produces a 192-label table with
canonical SHA-256
`b0607b6e52d368dcf7327909f99270f56a54373e9f6f348ea7fba751d7f89651`.
The strict reader accepts v1 and `v2-term-materialization` as above and accepts
`npa.fast-shard-memory.v3-term-materialization-prepared-retention` only when
`combined_shared_bytes` is the checked/saturated sum of shared base and
prepared retained bytes, overflow is reported when that addition saturates,
and the per-worker term charge remains 268,435,456 bytes.

## Implemented behavior

Changed package selection now builds inspectable `/usr/bin/git` invocations,
executes them through one raw process-runner seam, and decodes raw
`std::process::Output` separately. Each exact candidate query uses an atomic
`:(top,literal)PATH` include plus a glob-escaped
`:(top,exclude,glob)PATH/**` descendant exclusion. Candidate pairs at different
slash depths are queried in separate groups so an ancestor exclusion cannot
hide an explicitly cataloged descendant. The
tracked/parse/untracked/parse ordering is unchanged.

On Unix, one environment snapshot, `_SC_ARG_MAX`, fixed tracked/untracked argv
charge, pointer charge, and a 32-KiB reserve determine the effective pathspec
budget, capped at 64 KiB. A batch contains at most 1,024 pathspec arguments,
which is at most 512 complete candidate pairs. An unusable premise or one
individually oversized pair selects the complete `Legacy128` partition before
the first tracked/untracked query; that partition contains at most 128
pathspec arguments, or 64 pairs. There is no runtime capability probe, shell,
`xargs`, retry, or temporary pathspec file.

The new partition intentionally changes which error can win when it combines
paths formerly separated at 128. Within every selected-policy batch the order
remains tracked, tracked parse, untracked, untracked parse. Stable repository
and environment state are required for successful-result parity; this is not a
repository snapshot.

Timing-enabled changed build and verify calls record the complete selection
phase and project the same closed observation. Verify merges the later checker
report through an `Unknown`/`Exact`/`Conflict` input-identity state, retaining
the normal one-child exact identity and representing conflicts as omitted
identity plus measurement overflow. Timing-off creates no observation DTO or
common recorder update.

## Deterministic evidence

- Pure builder, decoder, batching, fallback arithmetic, exact filtering,
  process order, short-circuit, output counters, and merged-boundary tests are
  owned by `package_verify.rs`.
- `bench_package_changed_selection` owns the exact 25-scenario catalog and the
  canonical synthetic path generator. Its checked hash-oracle test covers all
  20 synthetic catalog profiles; IUT remains a separate checked catalog.
- For the current 1,401-local-certificate IUT package, the exact top-relative
  candidate catalog is 177,575 path bytes and its NUL-stream SHA-256 is
  `434e068753f94f9ddcadf6159538cdd7497a2b29dc3eafe405db1f3c623ce663`.
  The package-relative certificate suffixes occupy 145,352 bytes. Including
  both members of every exact-path pair produces 408,388 pathspec payload
  bytes. At the nominal 64-KiB target, depth-isolated production planning uses
  ten batches and twenty query processes, plus the two repository-discovery
  processes; the largest batch argv charge is 65,422 bytes.

## Pending release evidence

The complete release harness is implemented: it materializes valid packages,
uses real Git mutations, runs one warmup plus seven retained samples for both
populations, validates build-bound v3 provenance sidecars against both
preserved executables (including the hidden `npa` build attestation), and the
repository script assembles the four-population, 100-record interleaved v3
comparison with recursive nested validation and a strict self-hash. A real tiny
clean/summary run and tracked/timing-off run pass in this worktree; these
integration checks are not release evidence.

The design still requires two clean, committed, source-bound revisions and
preserved release binaries for the fixed128/optimized comparison. This shared
integration worktree is intentionally dirty, so those source/binary identities
and host elapsed records cannot be produced honestly here. The actual fixed128
and optimized artifact directories, comparison JSON, median/MAD values, and
advisory 25%/5% conclusion therefore remain pending a reviewed clean-release
run.

No elapsed result is fabricated. Deterministic behavior, process counts, argv
bounds, schema compatibility, and functional parity are the blocking evidence
available in this worktree; elapsed ratios remain advisory by design.
