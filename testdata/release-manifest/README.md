# Generated-Artifact Release-Manifest Fixtures

These JSON documents test the offline generated-artifact release-manifest
parser and its internal agreement rules. They are static schema fixtures, not
live release evidence. The Rust `release_manifest_validator` integration test
requires every positive and named negative fixture to retain its deterministic
classification or rejection.

`valid-v0.2-external.json` intentionally uses an illustrative external checker
version `0.1.0`. That value exercises the v0.2 schema; it does not describe the
current binary, select executable bytes, or prove compatibility with
`npa-checker-ext 0.2.0`. The live toolchain gate derives current checker,
binary, build, policy, registry, Cargo, host, source, and archive identities at
runtime instead of rewriting this historical test datum.

The validator checks schema shape and agreement among manifest fields. It does
not open generated files, machine results, the checker identity manifest, or
the archive. Release workflows must first recompute raw file/archive hashes,
validate the canonical runner-policy identity, cross-check live machine
results, extract the archive, and run `sha256sum -c`. Only then may
`validate-generated-artifact-release-manifest.sh --require-v0.2` classify a new
manifest as checked v0.2 evidence.

Historical v0.1 fixtures remain schema-valid history, but `--require-v0.2`
rejects them for a new release. Neither a valid static fixture nor dynamic v0.2
external checked evidence is automatically `verified_high_trust`.
