//! Frontend profiles for NPA source syntax.
//!
//! This crate lowers source into `npa_cert::CoreModule` values and, when asked
//! to produce a certificate, crosses the canonical `build_module_cert` /
//! `verify_module_cert` boundary. Certificate producer fast-path candidates remain
//! in `npa-cert` until a separate bridge is designed.

mod callable;
mod derive_policy;
mod diagnostic;
mod elaborator;
mod equation;
mod human;
mod human_diagnostic;
mod human_elaborator;
mod human_parser;
mod human_resolver;
mod lexer;
mod machine;
mod parser;
mod resolver;
mod span;
mod term_source;

pub use callable::{
    builtin_machine_callable_profile, is_machine_surface_renderable_name,
    machine_callable_profile_from_human_binders,
    machine_callable_visibility_from_human_binder_info, MachineCallableBinderVisibility,
    MachineSurfaceCallableInterfaceEntry, MachineSurfaceCallableInterfaceError,
    MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableRef,
};
pub use derive_policy::{
    human_default_derived_declaration_plan, human_default_inductive_derivation_plan,
    human_explicit_derivation_plan, human_explicit_derived_declaration_plan,
    human_explicit_derived_declaration_plan_from_names, human_foundational_allowlist_artifacts,
    human_foundational_derivation_plan, human_foundational_derived_declaration_plan,
    human_is_heavy_derive_artifact, human_parse_derive_artifact, HumanDeriveArtifact,
    HumanDeriveArtifactSource, HumanDeriveBudget, HumanDeriveBudgetError, HumanDeriveBudgetField,
    HumanDeriveBudgetUsage, HumanDerivePlan, HumanDerivePlanError, HumanDeriveProofIdentityEffect,
    HumanDerivedDeclarationKind, HumanDerivedDeclarationPlan, HumanDerivedDeclarationPlanError,
    HumanDerivedDeclarationSpec, HumanPlannedDerivedArtifact, HumanUnsupportedDeriveArtifactName,
    HUMAN_HEAVY_DERIVE_ARTIFACTS, HUMAN_MANDATORY_INDUCTIVE_ARTIFACTS,
};
pub use diagnostic::{
    MachineDiagnostic, MachineDiagnosticKind, MachineDiagnosticPayload, MachineDiagnosticSeverity,
    MachineRepairCandidate, MachineRepairSuggestion, MachineRepairSuggestionKind, Result,
};
pub use elaborator::{
    compile_machine_source_to_certificate, compile_machine_source_to_core,
    elaborate_machine_module, elaborate_machine_term_check, elaborate_machine_term_infer_from_ast,
    MachineTermElabContextInModuleRequest,
};
pub use equation::{
    check_human_equation_coverage, check_human_equation_coverage_block,
    check_human_equation_coverage_block_with_options, check_human_equation_coverage_with_options,
    check_human_equation_recursion, check_human_equation_recursion_block,
    check_human_equation_structural_recursion, check_human_equation_structural_recursion_block,
    construct_human_equation_decision_tree,
    human_equation_constructor_family_table_from_resolved_module,
    human_equation_constructor_order_from_resolved_module, human_equation_global_ref_sort_key,
    lower_human_equation_decision_tree_to_core,
    lower_human_equation_decision_tree_to_core_with_theorems,
    normalize_human_equation_pattern_matrix,
    normalize_human_equation_pattern_matrix_with_constructor_order, HumanEquationBudget,
    HumanEquationBudgetError, HumanEquationBudgetField, HumanEquationBudgetUsage,
    HumanEquationConstructorFamily, HumanEquationConstructorFamilyTable,
    HumanEquationConstructorFieldPath, HumanEquationConstructorFieldSegment,
    HumanEquationConstructorLoweringProfile, HumanEquationConstructorOrder,
    HumanEquationCoreArtifact, HumanEquationCoreArtifactBundle, HumanEquationCoreArtifactKind,
    HumanEquationCoverageBlockResult, HumanEquationCoverageDiagnostic,
    HumanEquationCoverageDiagnosticKind, HumanEquationCoverageOptions, HumanEquationCoverageResult,
    HumanEquationCoverageRowStatus, HumanEquationCoverageRowStatusKind,
    HumanEquationDecisionBranch, HumanEquationDecisionBranchCell,
    HumanEquationDecisionBranchContext, HumanEquationDecisionLeaf, HumanEquationDecisionSwitch,
    HumanEquationDecisionTree, HumanEquationDecisionTreeError, HumanEquationDecisionTreeMetrics,
    HumanEquationDecisionTreeNode, HumanEquationDecisionTreeResult, HumanEquationEqRecTransport,
    HumanEquationHelperCandidate, HumanEquationHelperSplitPlan, HumanEquationImpossibleBranchFact,
    HumanEquationLoweringBinder, HumanEquationLoweringError, HumanEquationLoweringMetrics,
    HumanEquationLoweringProfile, HumanEquationLoweringResult, HumanEquationMatrixError,
    HumanEquationMeasureDecreaseObligation, HumanEquationMeasureLoweringPlan,
    HumanEquationMeasureLoweringStrategy, HumanEquationMissingConstructorSet,
    HumanEquationMutualCycle, HumanEquationPatternMatrix, HumanEquationPatternMatrixCell,
    HumanEquationPatternMatrixColumn, HumanEquationPatternMatrixColumnPath,
    HumanEquationPatternMatrixConstructor, HumanEquationPatternMatrixConstructorSet,
    HumanEquationPatternMatrixPathSegment, HumanEquationPatternMatrixRow,
    HumanEquationPatternMatrixRowKind, HumanEquationPatternMatrixRowProvenance,
    HumanEquationRecursionBlockResult, HumanEquationRecursionDefinition,
    HumanEquationRecursionDiagnostic, HumanEquationRecursionDiagnosticKind,
    HumanEquationRecursionGraph, HumanEquationRecursionResult, HumanEquationRecursiveCall,
    HumanEquationRecursorLoweringProfile, HumanEquationStructuralDecreaseEvidence,
    HumanEquationTheoremBudget, HumanEquationTheoremBudgetError, HumanEquationTheoremBudgetField,
    HumanEquationTheoremBudgetUsage, HumanEquationTheoremPlan, HumanEquationTheoremProofStrategy,
    HumanEquationTheoremRequest, HumanEquationTheoremSource, HumanEquationTheoremSpec,
};
pub use human::{
    HumanAxiomDecl, HumanBinder, HumanBinderInfo, HumanBinderKind, HumanClassDecl,
    HumanClassFieldDecl, HumanCompileOptions, HumanConstructorDecl, HumanDecl, HumanDeclValue,
    HumanEquationDecl, HumanEquationRow, HumanExpr, HumanFrontendState,
    HumanGeneratedDeclarationKind, HumanGeneratedDeclarationMetadata, HumanImplicitMode,
    HumanImportedSourceInterface, HumanInductiveDecl, HumanInstanceDecl, HumanInstanceFieldDecl,
    HumanItem, HumanLevel, HumanModule, HumanName, HumanNotationAssociativity, HumanNotationDecl,
    HumanNotationHead, HumanNotationKind, HumanOpenScope, HumanOpenScopeFrame, HumanPattern,
    HumanProofBlock, HumanRewriteDirection, HumanRewriteRuleSyntax, HumanSourceBinderMetadata,
    HumanSourceDeclarationKind, HumanSourceDeclarationMetadata, HumanSourceInterface,
    HumanSourceInterfaceStore, HumanSourceNotationMetadata, HumanTacticKind, HumanTacticScript,
    HumanTacticSyntax, HumanTerminationAnnotation, HumanTypeclassClassMetadata,
    HumanTypeclassFieldMetadata, HumanTypeclassInstanceMetadata, HumanTypeclassSearchOutput,
    HumanTypeclassSearchPolicy, HumanTypeclassSearchStatus, HumanUniverseParam,
};
pub use human_diagnostic::{
    HumanDiagnostic, HumanDiagnosticConversionContext, HumanDiagnosticKind, HumanDiagnosticPayload,
    HumanDiagnosticPhase, HumanDiagnosticSeverity, HumanHoleGoal, HumanHoleGoalLocal, HumanResult,
    HumanUnsolvedMeta, HumanUnsolvedMetaKind,
};
pub use human_elaborator::{
    certificate_imports_for_human_core_module,
    collect_human_by_proof_targets_with_source_interfaces,
    compile_human_source_to_built_certificate_only_with_available_import_refs,
    compile_human_source_to_built_certificate_only_with_import_refs,
    compile_human_source_to_built_certificate_output_with_available_import_refs,
    compile_human_source_to_built_certificate_output_with_import_refs,
    compile_human_source_to_certificate,
    compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy,
    compile_human_source_to_certificate_output_with_import_refs_and_axiom_policy,
    compile_human_source_to_certificate_output_with_source_interfaces,
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy,
    compile_human_source_to_certificate_with_source_interfaces, compile_human_source_to_core,
    compile_human_source_to_core_output_with_source_interfaces,
    compile_human_source_to_core_output_with_source_interfaces_and_by_proofs,
    compile_human_source_to_core_with_source_interfaces, elaborate_human_module,
    elaborate_human_tactic_term_check, elaborate_human_tactic_term_infer,
    prepare_human_proof_start_core_with_source_interfaces,
    prepare_human_proof_start_core_with_source_interfaces_and_by_proofs,
    search_human_typeclass_from_source, HumanBuiltCertificateCompileOutput,
    HumanBuiltCertificateOnlyCompileOutput, HumanByProofCore, HumanByProofTarget,
    HumanByProofTargetsOutput, HumanCertificateCompileOutput, HumanCoreCompileOutput,
    HumanProofStartCore, HumanProofStartCoreOutput, HumanProofStartCoreWithProofsRequest,
    HumanTacticTermCheckOutput, HumanTacticTermElabContext, HumanTacticTermElabContextRequest,
    HumanTacticTermInferOutput,
};
pub use human_parser::{
    parse_human_import_spans, parse_human_module, parse_human_module_with_source_interfaces,
    parse_human_name_spans, parse_human_term, HumanImportSpan, HumanNameSpan,
};
pub use human_resolver::{
    resolve_human_module, resolve_human_module_with_source_interfaces,
    HumanEquationSemanticIdentity, HumanGlobalRef, HumanGlobalScope, HumanGlobalScopeEntry,
    HumanResolvedEquationItem, HumanResolvedEquationRow, HumanResolvedMeasureDecreaseProof,
    HumanResolvedName, HumanResolvedNameUse, HumanResolvedNotationEntry, HumanResolvedNotationUse,
    HumanResolvedPattern, HumanResolvedTerminationAnnotation, ResolvedHumanModule,
};
pub use lexer::{lex, Token, TokenKind};
pub use machine::{
    MachineBinder, MachineCheckedCurrentDecl, MachineCheckedCurrentGeneratedDecl,
    MachineCompileOptions, MachineDecl, MachineGlobalScope, MachineGlobalScopeEntry, MachineItem,
    MachineKernelEnvView, MachineLevel, MachineLocalDecl, MachineModule, MachineName,
    MachineResolvedConstant, MachineSurfaceMode, MachineTerm, MachineTermAst,
    MachineTermCheckResult, MachineTermElabContext, MachineTermSourceCanonical,
    MachineUniverseParam,
};
pub use parser::{parse_machine_module, parse_machine_term};
pub use resolver::{
    resolve_machine_module, resolve_machine_module_with_options, ResolvedMachineModule,
    VerifiedDependency, VerifiedExport, VerifiedImport,
};
pub use span::{ByteOffset, FileId, Span};
pub use term_source::{
    canonicalize_machine_term_source, decode_machine_term_source_canonical,
    lex_machine_surface_tokens, MachineSurfaceToken, MachineSurfaceTokenKind,
};
