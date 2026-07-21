#![deny(missing_docs)]

//! Contributor-facing NPA command-line parsing.
//!
//! The CLI crate is an untrusted orchestration layer. CLR-04 starts with
//! argument parsing only; later milestones add package loading and command
//! execution behind the parsed command model.

pub mod agent_adapter;
pub mod args;
pub mod checker_ext_toolchain_evidence;
pub mod diagnostic;
pub mod fs;
pub mod generated_artifact_writer;
pub mod governance_writer;
pub mod package;
pub mod package_api;
pub mod package_artifact_ledger;
pub mod package_artifacts;
pub mod package_axiom_report;
pub mod package_build;
pub mod package_candidate_metadata;
pub mod package_check;
pub mod package_export_summary;
pub mod package_gate_plan;
pub mod package_hashes;
pub mod package_high_trust;
pub mod package_index;
pub mod package_l2_acceptance;
pub mod package_l2_acceptance_aggregate;
pub mod package_l2_namespace_transport;
pub mod package_l2_review_input;
pub mod package_lock;
pub mod package_promotion_materialization_validate;
pub mod package_promotion_materialize;
pub mod package_promotion_prepare;
mod package_promotion_prepare_declaration;
pub mod package_promotion_registry;
mod package_promotion_transaction;
pub mod package_publish;
pub mod package_refactor_plan;
pub mod package_theorem_premise_report;
pub mod package_verify;
pub mod release_manifest;
mod timing;
