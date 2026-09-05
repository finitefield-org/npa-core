# Local performance fixtures

`fixtures/manifest.v0.1.json` defines compact, repository-local scenarios.
`baselines/measurements.v0.1.json` contains only deterministic work and
verification-coverage expectations. Host-specific elapsed thresholds are not
universal baselines and must live under `baselines/elapsed/` when explicitly
reviewed.

`fixtures/targeted-authoring-cache-limits-v1.tsv` freezes the TBAC-01 sizing
observations for the compact standard-library fixture, a proof package, and a
large targeted package. It records manifest-declared local source/certificate
bytes and interface-shape proxies only; it is checked against the versioned
Rust limit profile and is not an elapsed-time baseline or an automatically
tuned runtime policy.

`baselines/opaque-definition.v0.1.tsv` records trusted physical-reduction and
logical-fuel counters for a paired opaque/reducible semantic leaf, its
specification-theorem consumer, and a downstream normalization query under
memo-off and ephemeral-memo execution. The corresponding `npa-api` test runs
the fixture twice in fresh processes and excludes elapsed time and process
metadata from comparison.

Run `scripts/check-performance.sh`. The script builds once with the locked,
offline dependency graph, performs the declared warmup, then checks the
machine-readable package-verifier and proof-authoring true-batching outputs. It
does not update baselines. The current compact verifier
`npa.performance.run.v0.2` and true-batching
`npa.true-batching.elapsed.v0.2` envelopes bind the build source identity,
Cargo.lock, target/profile/features/rustflags, harness/production source sets,
and are re-read by the runtime-used strict validators; their v0.1 predecessors
are historical diagnostics only. The true-batching harness covers fixed small,
medium, and large proof-state fixtures plus the ordered certificate producer at
candidate counts 1, 8, 32, and 256. Its producer work counters verify that one
prepared name index is reused and that fingerprinting copies no accepted-prefix
elements.

The targeted `package build-certs --check` baseline adds generated small and
large dependency chains to the same fixture manifest. Its six scenarios cover
cache off, cold read-through, and warm read-through. Every recorded consumer
runs in a fresh process with a fresh explicit cache root. A warm read-through
root is populated by a distinct unmeasured process, so a recorded hit cannot
be process-global memoization. The checked-in baseline stores only the
deterministic diagnostic counters; raw wall time, peak RSS, exact
build/resource identities, and descriptive statistics belong in the targeted
performance evidence document or the harness output.

The Rust harness strictly validates every counter listed in the selected
baseline scenario and reports raw elapsed samples, median, median absolute
deviation, minimum, and maximum. Elapsed values remain advisory unless a
separately reviewed profile is explicitly added; the default report records
`elapsed_profile: null` and `elapsed_gate: "advisory"` rather than guessing a
profile from the host.

To change a baseline, edit the JSON explicitly and include the reason in the
reviewed change. Never derive or commit an elapsed profile automatically.

## SNAP/VMSP fixture union and generator

`fixtures/manifest.v0.2.json` is the selected additive successor to the closed
v0.1 fixture schema. It preserves every inherited v0.1 row and adds one typed,
strict union: 40 `package-artifact-snapshot` rows followed by 47 shared-payload
rows (`shared-payload-clone`, `shared-payload-cache`,
`shared-payload-memo`, `shared-payload-session`, `shared-payload-shard`, and
`shared-payload-small`). Unknown or extra fields, duplicate IDs, a selector not
allowed by its tag, or a row outside the closed policy matrix are errors. The
public selector enums are non-exhaustive for source compatibility, but each
versioned parser remains a closed allowlist. v0.1 parsing remains available and
accepts exactly its historical shapes.

Every new row binds `measurement_mode: "detailed"` directly to
`PackageTimingMode::Detailed` in the in-process CLI lane and
`PerformanceMeasurementMode::Detailed` in API/shared-payload lanes. No runner
may infer an execution lane or replace this mode with an ambient default. SNAP
rows bind all four cache/memo policies and `jobs`; VMSP rows bind their complete
tag-specific implementation, phase, count, and policy selectors. The
activation record in each design-task document names the one selected manifest;
`scripts/validate-performance-fixture-activation.sh` resolves that path and
never globs historical manifests.

Both benchmark examples include the single generator-v1 implementation from
`crates/npa-api/examples/support/performance_fixture_generator.rs`. It builds
canonical `CoreModule` values, solves exact certificate byte sizes using only
canonical declaration names, verifies every generated certificate normally,
and materializes manifest/lock files beneath a private temporary root. Generated
certificate/package trees are never checked in. The small checked artifact
`fixture-generator.v1.tsv` pins the ordered ten-profile descriptor, logical,
and artifact-tree SHA-256 identities plus exact shape and byte counts. A runner
must match that oracle before warmup and prove the workload tree is unchanged
after every sample.

Cache roots are private siblings of the generated workload. Prepopulation and
warmup work is excluded from internal elapsed/allocation samples; cache state is
cleared or retained exactly as selected by the typed row. Deterministic work,
reuse, retention, and lifecycle counters are blocking. Raw elapsed time,
allocator samples, and direct-child peak RSS are advisory unless a separately
reviewed host profile is added. `measure_process` must launch the owning
benchmark example as its direct child; the example performs API and CLI-local
verification in process and never delegates measured work to an `npa`
grandchild.

The previously collected SNAP 40-row and VMSP 47-row reports predate the
row-specific direct-child, sample-major interleave, build-bound production
source-set, fd-confined private-tree, and strict aggregate-validation
contracts. They are historical diagnostics only. No current-source SNAP or
VMSP matrix is accepted by this directory until a fresh locked-release run is
published under `results/`, re-read by the runtime-used strict validator, and
recorded here with its exact filename and SHA-256. Host elapsed/RSS acceptance
remains independently pending even after those deterministic matrices exist.

`generate_snap_vmsp_performance_manifest` is the only supported writer for the
selected v0.2 manifest, generator oracle, and SNAP baseline rows. A normal
generation creates a previously absent output. Updating a tracked artifact
requires the explicit update mode and the exact SHA-256 of the reviewed
preimage; publication is no-follow, atomic, and fsync-backed. The generator
never follows a caller-provided output symlink or silently overwrites unknown
bytes.
