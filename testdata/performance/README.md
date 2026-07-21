# Local performance fixtures

`fixtures/manifest.v0.1.json` defines compact, repository-local scenarios.
`baselines/measurements.v0.1.json` contains only deterministic work and
verification-coverage expectations. Host-specific elapsed thresholds are not
universal baselines and must live under `baselines/elapsed/` when explicitly
reviewed.

Run `scripts/check-performance.sh`. The script builds once with the locked,
offline dependency graph, performs the declared warmup, then checks the
machine-readable v0.1 measurement output. It does not update baselines.
The Rust harness strictly validates every counter listed in the selected
baseline scenario and reports raw elapsed samples, median, median absolute
deviation, minimum, and maximum. Elapsed values remain advisory unless a
separately reviewed profile is explicitly added; the default report records
`elapsed_profile: null` and `elapsed_gate: "advisory"` rather than guessing a
profile from the host.

To change a baseline, edit the JSON explicitly and include the reason in the
reviewed change. Never derive or commit an elapsed profile automatically.
