# NPA Test Specification Snapshot

This crate-local snapshot exists only for `npa-core` tests that pin public
standard-library contract wording. The full design/specification documents are
owned outside this testdata snapshot.

Release modules:

- Std.Logic
- Std.Nat
- Std.List
- Std.Algebra.Basic

Legacy fixture module names that remain compatibility test inputs:

- Std.Nat.Basic
- Std.Logic.Eq
- Eq.rec

Axiom reporting terms:

- imported Std.Logic Eq.rec
- module_axioms
- transitive_axioms

Machine release artifacts:

- Std.machine-release.json
- Std.machine-import-bundles.json
- Std.machine-theorem-index.json
- release/build artifact
- source_built_std_artifacts_feed_machine_release_sessions_retrieval_and_audit

Source boundary wording:

- source skeletons
- Rust core-module builders
- manifest fixes module membership/certificate paths
- source skeleton fixes import intent

Human source simplification and rewrite-only profile names are intentionally
listed below so the std-library contract test can detect accidental API drift:

- Nat.add_zero
- Nat.add_succ
- Nat.zero_add
- Nat.mul_zero
- Nat.mul_succ
- Nat.zero_mul
- Nat.pred_zero
- Nat.pred_succ
- List.nil_append
- List.cons_append
- List.append_nil
- List.length_nil
- List.length_cons
- List.map_nil
- List.map_cons
- List.map_id
- List.foldr_nil
- List.foldr_cons
- Nat.add_comm
- Nat.add_assoc
- List.append_assoc
- List.length_append
