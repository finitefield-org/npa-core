use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::current::{encode_machine_axiom_ref_wire, MachineAxiomRefWire};
use crate::renderer::{core_expr_metadata, render_kernel_core_expr};
use crate::types::HumanProofStateStoreMutationError;
use crate::{
    HumanApiCompileOptions, HumanApplyTacticError, HumanApplyTacticOk, HumanApplyTacticRequest,
    HumanAssistantAvailableTactic, HumanAssistantCandidate, HumanAssistantCandidateValidationOk,
    HumanAssistantCandidateValidationRequest, HumanAssistantFailedTacticDiagnostic,
    HumanAssistantPayloadError, HumanAssistantPayloadOk, HumanAssistantPayloadRequest,
    HumanAssistantRejectedCandidate, HumanAssistantValidatedCandidate, HumanCertificatePayload,
    HumanCompileCertificateOk, HumanCompileCertificateRequest, HumanCompileCoreOk,
    HumanCompileCoreRequest, HumanCompileError, HumanCurrentModuleSource, HumanDisplayContextOk,
    HumanDisplayContextOptions, HumanDisplayContextRequest, HumanDisplayDiffOk,
    HumanDisplayDiffRequest, HumanDisplayError, HumanDisplayExprRequest, HumanDisplayGoalRequest,
    HumanDisplayMode, HumanDisplayTextOk, HumanDocumentIncrementalCache,
    HumanDocumentIncrementalDeclCacheEntry, HumanDocumentIncrementalDeclReuse,
    HumanDocumentSnapshot, HumanDocumentUpdateError, HumanDocumentUpdateOk,
    HumanDocumentUpdateRequest, HumanExactTacticOk, HumanExactTacticRequest,
    HumanFormalizationIntentCertificate, HumanFormalizationProofSearchStatus,
    HumanFormalizationReviewStatus, HumanFormalizeCandidateReport, HumanFormalizeCandidateRequest,
    HumanFormalizeOk, HumanFormalizeRequest, HumanGoalDisplayDiffItem, HumanGoalDisplayDiffKind,
    HumanGoalId, HumanGoalMapping, HumanInductionTacticError, HumanInductionTacticOk,
    HumanInductionTacticRequest, HumanInductiveCheckError, HumanInductiveCheckRequest,
    HumanInductiveCheckResponse, HumanInductiveCheckStatus, HumanInductivePositivityStatus,
    HumanIntroTacticError, HumanIntroTacticOk, HumanIntroTacticRequest, HumanLspCodeAction,
    HumanLspCodeActionKind, HumanLspCodeActionOk, HumanLspCodeActionRequest, HumanLspCommand,
    HumanLspCompletionItem, HumanLspCompletionItemKind, HumanLspCompletionOk,
    HumanLspCompletionRequest, HumanLspDiagnostic, HumanLspDiagnosticData,
    HumanLspDiagnosticSeverity, HumanLspDiagnosticsOk, HumanLspDiagnosticsRequest,
    HumanLspDocumentPayloadOk, HumanLspDocumentPayloadRequest, HumanLspDocumentSymbol,
    HumanLspGoalViewOk, HumanLspGoalViewRequest, HumanLspHoleGoal, HumanLspHoleGoalLocal,
    HumanLspHover, HumanLspHoverOk, HumanLspHoverRequest, HumanLspHoverTheorem, HumanLspInlayHint,
    HumanLspInlayHintKind, HumanLspPosition, HumanLspRange, HumanLspSemanticToken,
    HumanLspSemanticTokenType, HumanLspSymbolKind, HumanLspUnsolvedMeta, HumanProofSession,
    HumanProofSessionStatus, HumanProofSessionStore, HumanProofStateEntry,
    HumanProofStateStartError, HumanProofStateStartOk, HumanProofStateStartRequest,
    HumanProofStateStore, HumanRewriteTacticError, HumanRewriteTacticOk, HumanRewriteTacticRequest,
    HumanSessionCreateError, HumanSessionCreateOk, HumanSessionCreateRequest,
    HumanSessionVerifyError, HumanSessionVerifyImport, HumanSessionVerifyImportAxiom,
    HumanSessionVerifyOk, HumanSessionVerifyRequest, HumanSessionVerifyStatus,
    HumanSimpLiteTacticError, HumanSimpLiteTacticOk, HumanSimpLiteTacticRequest,
    HumanSmtProveRequest, HumanSmtProveResponse, HumanSmtTacticOk, HumanSmtTacticRequest,
    HumanSourcePosition, HumanStartProofError, HumanStartProofOk, HumanStartProofRequest,
    HumanStateApiError, HumanStateAtRequest, HumanStateByIdRequest, HumanStateCurrentRequest,
    HumanStateGoalSummary, HumanStateGoalsOk, HumanStateGoalsRequest, HumanStateLookupOk,
    HumanStateRequestError, HumanStateRequestHeader, HumanStructuredProofStateError,
    HumanTacticCheckRequest, HumanTacticCheckResponse, HumanTacticRunErrorKind,
    HumanTacticRunErrorReport, HumanTacticRunRequest, HumanTacticRunResponse, HumanTacticRunStatus,
    HumanTacticRunSuggestion, HumanTacticRunSuggestionKind, HumanTacticScriptError,
    HumanTacticScriptRunOk, HumanTacticScriptRunRequest, HumanTacticStateRecordError,
    HumanTacticStateRecordOk, HumanTacticStateRecordRequest, HumanTacticSuggestRequest,
    HumanTacticSuggestResponse, HumanTacticSuggestion, HumanTacticSuggestionSource,
    HumanTacticTermCheckOk, HumanTacticTermCheckRequest, HumanTacticTermError,
    HumanTheoremAxiomInfo, HumanTheoremDependency, HumanTheoremDependencyKind,
    HumanTheoremGoalSearchRequest, HumanTheoremIndex, HumanTheoremIndexEntry,
    HumanTheoremIndexError, HumanTheoremIndexKind, HumanTheoremIndexSource,
    HumanTheoremMatchBinding, HumanTheoremNameSearchRequest, HumanTheoremRewriteSearchRequest,
    HumanTheoremSearchAxiomPolicy, HumanTheoremSearchError, HumanTheoremSearchMode,
    HumanTheoremSearchOk, HumanTheoremSearchOptions, HumanTheoremSearchResult,
    HumanTheoremTypeSearchRequest, HumanTypeclassSearchError, HumanTypeclassSearchOk,
    HumanTypeclassSearchRequest, LocalId, StructuredExpr, StructuredGoal, StructuredGoalStatus,
    StructuredHypothesis, StructuredProofState, HUMAN_DISPLAY_PROFILE_ID,
};
use npa_cert::{
    AxiomRef, DeclPayload, DependencyEntry, ExportEntry, ExportKind, GlobalRef, Hash, LevelId,
    LevelNode, ModuleName, Name, NameId, TermId, TermNode, VerifiedModule,
};
use npa_kernel::{subst::instantiate, Ctx, Decl, Env, Expr, Level};
use sha2::{Digest, Sha256};

const HUMAN_CERTIFICATE_ENCODING: &str = "npa.certificate.canonical.v0.1.hex";

/// Compile Human source through the Human tactic API adapter.
///
/// Unlike the plain `npa_frontend::compile_human_source_to_core*` helpers, this
/// wrapper executes Human `by` proof blocks through the `npa-api` tactic bridge
/// and substitutes the extracted core proof terms before returning the core
/// module. The request keeps the current module/source/imports/options explicit
/// and does not create a Machine API session.
pub fn compile_human_source_to_core(
    request: HumanCompileCoreRequest<'_, '_>,
) -> Result<HumanCompileCoreOk, HumanCompileError> {
    compile_human_source_to_core_with_tactic_proofs(
        request.current_module,
        request.current_source,
        request.verified_modules,
        request.imported_source_interfaces,
        request.options,
    )
    .map(|output| HumanCompileCoreOk {
        core_module: output.core_module,
        source_interface: output.source_interface,
    })
}

/// Compile Human source to a certificate through the Human API adapter.
///
/// Plain frontend certificate compilation remains responsible for already-core
/// Human terms only. This API wrapper is the layer that runs Human `by` proof
/// blocks, verifies the resulting core module, and hashes the returned source
/// interface for downstream Human imports. It does not widen `/machine/*`
/// request grammar or implicitly allocate a Machine session.
pub fn compile_human_source_to_certificate(
    request: HumanCompileCertificateRequest<'_, '_>,
) -> Result<HumanCompileCertificateOk, HumanCompileError> {
    let options = npa_frontend::HumanCompileOptions::from(&request.options);
    let verified_imports: Vec<_> = request
        .verified_modules
        .iter()
        .map(npa_frontend::VerifiedImport::from)
        .collect();
    let by_targets = npa_frontend::collect_human_by_proof_targets_with_source_interfaces(
        request.current_source.file_id,
        request.current_module.clone(),
        request.current_source.source,
        &verified_imports,
        request.imported_source_interfaces,
        &options,
    )?;

    if !by_targets.targets.is_empty() {
        let core = compile_human_source_to_core_with_tactic_proofs(
            request.current_module,
            request.current_source,
            request.verified_modules,
            request.imported_source_interfaces,
            request.options,
        )?;
        let certificate_imports = npa_frontend::certificate_imports_for_human_core_module(
            &core.core_module,
            &core.active_imports,
            request.verified_modules,
            request.current_source.file_id,
        )?;
        let certificate = human_build_and_verify_certificate(
            core.core_module,
            &certificate_imports,
            request.current_source,
        )?;
        let source_interface =
            human_source_interface_with_certificate_hashes(core.source_interface, &certificate);
        return Ok(HumanCompileCertificateOk {
            certificate,
            source_interface,
        });
    }

    let output = npa_frontend::compile_human_source_to_certificate_output_with_source_interfaces(
        request.current_source.file_id,
        request.current_module,
        request.current_source.source,
        request.verified_modules,
        request.imported_source_interfaces,
        &options,
    )?;
    Ok(HumanCompileCertificateOk {
        certificate: output.certificate,
        source_interface: output.source_interface,
    })
}

/// Run bounded Human typeclass search for an explicit class goal.
///
/// This is the library equivalent of `POST /typeclass/search`. The returned
/// trace is Human diagnostic metadata only; proof acceptance remains the
/// canonical core term checked by the kernel and certificate verifier.
pub fn search_human_typeclass(
    request: HumanTypeclassSearchRequest<'_, '_>,
) -> Result<HumanTypeclassSearchOk, HumanTypeclassSearchError> {
    let options = npa_frontend::HumanCompileOptions::from(&request.options);
    let verified_imports: Vec<_> = request
        .verified_modules
        .iter()
        .map(npa_frontend::VerifiedImport::from)
        .collect();
    let output = npa_frontend::search_human_typeclass_from_source(
        request.current_source.file_id,
        request.current_module,
        request.current_source.source,
        request.goal_source,
        &verified_imports,
        request.imported_source_interfaces,
        &options,
    )?;
    Ok(HumanTypeclassSearchOk {
        status: output.status,
        instance: output.instance,
        core_term: output.core_term,
        search_trace: output.search_trace,
    })
}

/// Check an indexed inductive declaration for Human IDE diagnostics.
///
/// This is the library equivalent of `POST /inductive/check`. The response is
/// diagnostic metadata only: proof acceptance still comes from canonical
/// certificate verification and the independent checker.
pub fn check_human_inductive(
    request: HumanInductiveCheckRequest<'_>,
) -> HumanInductiveCheckResponse {
    let constructors = request
        .declaration
        .constructors
        .iter()
        .map(|constructor| constructor.name.clone())
        .collect::<Vec<_>>();

    let base_kernel_error = check_inductive_with_kernel(request.declaration.clone()).err();
    if let Some(error) = base_kernel_error {
        return HumanInductiveCheckResponse {
            status: HumanInductiveCheckStatus::Rejected,
            constructors,
            recursor: request
                .declaration
                .recursor
                .as_ref()
                .map(|recursor| recursor.name.clone()),
            positivity: human_inductive_positivity_status(&error),
            recursor_signature_hash: None,
            iota_rules_hash: None,
            diagnostic_only: true,
            error: Some(HumanInductiveCheckError::Kernel(error)),
        };
    }

    let generated = match if request.declaration.recursor.is_some() {
        Ok(request.declaration.clone())
    } else {
        npa_cert::generate_inductive_artifacts_v1(request.declaration)
    } {
        Ok(generated) => generated,
        Err(error) => {
            return HumanInductiveCheckResponse {
                status: HumanInductiveCheckStatus::Rejected,
                constructors,
                recursor: None,
                positivity: HumanInductivePositivityStatus::Passed,
                recursor_signature_hash: None,
                iota_rules_hash: None,
                diagnostic_only: true,
                error: Some(HumanInductiveCheckError::Certificate(error)),
            };
        }
    };

    if let Err(error) = check_inductive_with_kernel(generated.clone()) {
        return HumanInductiveCheckResponse {
            status: HumanInductiveCheckStatus::Rejected,
            constructors,
            recursor: generated
                .recursor
                .as_ref()
                .map(|recursor| recursor.name.clone()),
            positivity: HumanInductivePositivityStatus::Passed,
            recursor_signature_hash: None,
            iota_rules_hash: None,
            diagnostic_only: true,
            error: Some(HumanInductiveCheckError::Kernel(error)),
        };
    }

    match npa_cert::inductive_generated_artifact_hashes_v1(&generated) {
        Ok(hashes) => HumanInductiveCheckResponse {
            status: HumanInductiveCheckStatus::AcceptedByKernelAndCertificate,
            constructors,
            recursor: generated
                .recursor
                .as_ref()
                .map(|recursor| recursor.name.clone()),
            positivity: HumanInductivePositivityStatus::Passed,
            recursor_signature_hash: hashes.recursor_signature_hash,
            iota_rules_hash: hashes.iota_rules_hash,
            diagnostic_only: true,
            error: None,
        },
        Err(error) => HumanInductiveCheckResponse {
            status: HumanInductiveCheckStatus::Rejected,
            constructors,
            recursor: generated
                .recursor
                .as_ref()
                .map(|recursor| recursor.name.clone()),
            positivity: HumanInductivePositivityStatus::Passed,
            recursor_signature_hash: None,
            iota_rules_hash: None,
            diagnostic_only: true,
            error: Some(HumanInductiveCheckError::Certificate(error)),
        },
    }
}

fn check_inductive_with_kernel(data: npa_kernel::InductiveDecl) -> npa_kernel::Result<()> {
    let mut env = Env::with_builtins()?;
    env.add_inductive(data)
}

fn human_inductive_positivity_status(error: &npa_kernel::Error) -> HumanInductivePositivityStatus {
    match error {
        npa_kernel::Error::NonPositiveOccurrence { .. } => HumanInductivePositivityStatus::Failed,
        _ => HumanInductivePositivityStatus::NotReached,
    }
}

/// Create a Human IDE proof session from explicit source and imports.
///
/// This is the library equivalent of Phase 5 Human `POST /sessions`. It stores
/// the caller-provided source text, module, verified imports, Human source
/// interfaces, and options in an in-memory `HumanProofSessionStore`. It does
/// not read from the filesystem, perform network lookup, or create a
/// `MachineProofSession`.
pub fn create_human_session(
    store: &mut HumanProofSessionStore,
    request: HumanSessionCreateRequest<'_, '_>,
) -> Result<HumanSessionCreateOk, HumanSessionCreateError> {
    let (session_id, document_id) = store.allocate_session_ids()?;
    let document = HumanDocumentSnapshot {
        document_id: document_id.clone(),
        document_version: crate::HumanDocumentVersion::initial(),
        current_module: request.current_module,
        file_id: request.current_source.file_id,
        source: request.current_source.source.to_owned(),
        verified_modules: request.verified_modules.to_vec(),
        imported_source_interfaces: request.imported_source_interfaces.to_vec(),
        options: request.options,
    };
    let collected = collect_human_session_document(&document);
    let messages = collected.messages.clone();
    let incremental_cache = build_human_document_incremental_cache(&document, &collected, None);
    let session = HumanProofSession {
        session_id: session_id.clone(),
        status: HumanProofSessionStatus::Open,
        document,
        source_interface: collected.source_interface,
        active_imported_source_interfaces: collected.active_imports,
        incremental_cache: incremental_cache.clone(),
        proof_states: HumanProofStateStore::new(),
        current_state_id: None,
        messages: collected.messages,
    };
    store.insert_session(session);

    Ok(HumanSessionCreateOk {
        session_id,
        document_id,
        document_version: crate::HumanDocumentVersion::initial(),
        status: HumanProofSessionStatus::Open,
        messages,
        incremental_cache,
    })
}

/// Start a theorem proof from a Human session and store the initial proof state.
///
/// This records the `MachineProofState` returned by `start_human_proof` under a
/// Human-only `HumanStateId`. The handle is for Human API state lookup and is
/// not a replacement for Machine `state_fingerprint` in AI search paths.
pub fn start_human_session_proof(
    store: &mut HumanProofSessionStore,
    request: HumanProofStateStartRequest,
) -> Result<HumanProofStateStartOk, HumanProofStateStartError> {
    let (current_module, file_id, source, verified_modules, imported_source_interfaces, options) = {
        let session = store.session(&request.session_id).ok_or_else(|| {
            HumanProofStateStartError::UnknownSession {
                session_id: request.session_id.clone(),
            }
        })?;
        (
            session.document.current_module.clone(),
            session.document.file_id,
            session.document.source.clone(),
            session.document.verified_modules.clone(),
            session.document.imported_source_interfaces.clone(),
            session.document.options.clone(),
        )
    };
    let started = start_human_proof(HumanStartProofRequest {
        current_module,
        theorem_name: request.theorem_name,
        current_source: HumanCurrentModuleSource {
            file_id,
            source: &source,
        },
        verified_modules: &verified_modules,
        imported_source_interfaces: &imported_source_interfaces,
        options,
    })
    .map_err(HumanProofStateStartError::Start)?;
    let session = store
        .session_mut(&request.session_id)
        .expect("session was checked before proof start");
    session.source_interface = Some(started.source_interface);
    let entry = session
        .proof_states
        .insert_initial_state(
            started.state,
            session.document.document_version,
            request.source_span,
            request.selected_goal,
            request.messages,
        )
        .map_err(human_proof_state_start_error)?;
    session.current_state_id = Some(entry.state_id.clone());

    Ok(HumanProofStateStartOk {
        session_id: request.session_id,
        state_id: entry.state_id,
        document_version: entry.document_version,
        selected_goal: entry.selected_goal,
        goal_mappings: entry.goal_mappings,
        messages: entry.messages,
    })
}

/// Record a new Human proof state after a tactic has produced a new Machine state.
///
/// The parent entry is left untouched. Existing open Machine goals keep their
/// Human goal handles where possible, and new Machine goals receive fresh
/// Human-only handles.
pub fn record_human_tactic_state(
    store: &mut HumanProofSessionStore,
    request: HumanTacticStateRecordRequest,
) -> Result<HumanTacticStateRecordOk, HumanTacticStateRecordError> {
    let session = store.session_mut(&request.session_id).ok_or_else(|| {
        HumanTacticStateRecordError::UnknownSession {
            session_id: request.session_id.clone(),
        }
    })?;
    let entry = session
        .proof_states
        .insert_transition_state(
            &request.parent_state_id,
            request.state,
            request.source_span,
            request.selected_goal,
            request.messages,
        )
        .map_err(|error| {
            human_tactic_state_record_error(
                error,
                request.session_id.clone(),
                request.parent_state_id.clone(),
            )
        })?;
    session.current_state_id = Some(entry.state_id.clone());

    Ok(HumanTacticStateRecordOk {
        session_id: request.session_id,
        parent_state_id: request.parent_state_id,
        state_id: entry.state_id,
        document_version: entry.document_version,
        selected_goal: entry.selected_goal,
        goal_mappings: entry.goal_mappings,
        messages: entry.messages,
    })
}

pub fn get_human_proof_state<'session>(
    store: &'session HumanProofSessionStore,
    session_id: &crate::HumanSessionId,
    state_id: &crate::HumanStateId,
) -> Option<&'session HumanProofStateEntry> {
    store
        .session(session_id)
        .and_then(|session| session.proof_states.state(state_id))
}

pub fn materialize_human_proof_state(
    store: &HumanProofSessionStore,
    session_id: &crate::HumanSessionId,
    state_id: &crate::HumanStateId,
) -> Result<StructuredProofState, HumanStructuredProofStateError> {
    let session = store.session(session_id).ok_or_else(|| {
        HumanStructuredProofStateError::UnknownSession {
            session_id: session_id.clone(),
        }
    })?;
    let entry = session.proof_states.state(state_id).ok_or_else(|| {
        HumanStructuredProofStateError::UnknownState {
            session_id: session_id.clone(),
            state_id: state_id.clone(),
        }
    })?;
    let mut goals = Vec::with_capacity(entry.state.open_goals.len());
    for machine_goal_id in &entry.state.open_goals {
        goals.push(materialize_human_structured_goal(entry, *machine_goal_id)?);
    }

    Ok(StructuredProofState {
        session_id: session_id.clone(),
        state_id: entry.state_id.clone(),
        document_version: entry.document_version,
        source_span: entry.source_span,
        selected_goal: entry.selected_goal.clone(),
        goals,
        messages: entry.messages.clone(),
    })
}

pub fn get_human_state_by_id(
    store: &HumanProofSessionStore,
    request: HumanStateByIdRequest,
) -> Result<HumanStateLookupOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    Ok(HumanStateLookupOk {
        state: materialize_human_state_for_api(store, &request.header, &request.state_id)?,
    })
}

pub fn get_human_state_goals(
    store: &HumanProofSessionStore,
    request: HumanStateGoalsRequest,
) -> Result<HumanStateGoalsOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    let entry = human_state_entry_for_api(store, &request.header, &request.state_id)?;
    let goals = human_state_goal_summaries_for_api(&request.header, entry)?;

    Ok(HumanStateGoalsOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        document_version: entry.document_version,
        selected_goal: entry.selected_goal.clone(),
        goals,
    })
}

pub fn get_current_human_state(
    store: &HumanProofSessionStore,
    request: HumanStateCurrentRequest,
) -> Result<HumanStateLookupOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    let session = store
        .session(&request.header.session_id)
        .expect("Human state request document validation checked session existence");
    let state_id =
        session
            .current_state_id
            .clone()
            .ok_or_else(|| HumanStateApiError::NoCurrentState {
                session_id: request.header.session_id.clone(),
                document_version: request.header.document_version,
            })?;

    Ok(HumanStateLookupOk {
        state: materialize_human_state_for_api(store, &request.header, &state_id)?,
    })
}

pub fn get_human_state_at(
    store: &HumanProofSessionStore,
    request: HumanStateAtRequest,
) -> Result<HumanStateLookupOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    let session = store
        .session(&request.header.session_id)
        .expect("Human state request document validation checked session existence");
    let state_id =
        human_state_id_at_position(session, request.header.document_version, request.position)
            .ok_or_else(|| HumanStateApiError::NoProofStateAtPosition {
                session_id: request.header.session_id.clone(),
                document_version: request.header.document_version,
                position: request.position,
            })?;

    Ok(HumanStateLookupOk {
        state: materialize_human_state_for_api(store, &request.header, &state_id)?,
    })
}

fn materialize_human_state_for_api(
    store: &HumanProofSessionStore,
    header: &HumanStateRequestHeader,
    state_id: &crate::HumanStateId,
) -> Result<StructuredProofState, HumanStateApiError> {
    human_state_entry_for_api(store, header, state_id)?;

    materialize_human_proof_state(store, &header.session_id, state_id)
        .map_err(|error| human_state_materialization_error(header, state_id, error))
}

fn human_state_entry_for_api<'session>(
    store: &'session HumanProofSessionStore,
    header: &HumanStateRequestHeader,
    state_id: &crate::HumanStateId,
) -> Result<&'session HumanProofStateEntry, HumanStateApiError> {
    let session = store
        .session(&header.session_id)
        .expect("Human state request document validation checked session existence");
    let entry =
        session
            .proof_states
            .state(state_id)
            .ok_or_else(|| HumanStateApiError::UnknownState {
                session_id: header.session_id.clone(),
                state_id: state_id.clone(),
            })?;
    if entry.document_version != header.document_version {
        return Err(HumanStateApiError::StaleProofState {
            session_id: header.session_id.clone(),
            state_id: state_id.clone(),
            requested_document_version: header.document_version,
            state_document_version: entry.document_version,
        });
    }
    Ok(entry)
}

fn human_state_goal_summaries_for_api(
    header: &HumanStateRequestHeader,
    entry: &HumanProofStateEntry,
) -> Result<Vec<HumanStateGoalSummary>, HumanStateApiError> {
    let mut goals = Vec::with_capacity(entry.state.open_goals.len());
    for machine_goal_id in &entry.state.open_goals {
        let human_goal_id = entry
            .human_goal_for_machine_goal(*machine_goal_id)
            .cloned()
            .ok_or_else(|| {
                human_state_materialization_error(
                    header,
                    &entry.state_id,
                    HumanStructuredProofStateError::MissingGoalMapping {
                        state_id: entry.state_id.clone(),
                        machine_goal_id: *machine_goal_id,
                    },
                )
            })?;
        let goal = entry.state.goal(*machine_goal_id).map_err(|diagnostic| {
            human_state_materialization_error(
                header,
                &entry.state_id,
                HumanStructuredProofStateError::MachineGoal {
                    state_id: entry.state_id.clone(),
                    machine_goal_id: *machine_goal_id,
                    diagnostic: Box::new(diagnostic),
                },
            )
        })?;

        let mut local_names = Vec::with_capacity(goal.context.len());
        let mut context = Vec::with_capacity(goal.context.len());
        for local in &goal.context {
            let ty = human_structured_expr_pretty(&local.ty, &local_names);
            let value = local
                .value
                .as_ref()
                .map(|value| human_structured_expr_pretty(value, &local_names));
            context.push(human_state_goal_summary_hypothesis_pretty(
                &local.name,
                &ty,
                value.as_deref(),
            ));
            local_names.push(local.name.clone());
        }
        let target = human_structured_expr_pretty(&goal.target, &local_names);
        goals.push(HumanStateGoalSummary {
            goal_id: human_goal_id,
            pretty: human_state_goal_summary_pretty(&context, &target),
        });
    }
    Ok(goals)
}

fn human_state_goal_summary_hypothesis_pretty(name: &str, ty: &str, value: Option<&str>) -> String {
    match value {
        Some(value) => format!("{name} : {ty} := {value}"),
        None => format!("{name} : {ty}"),
    }
}

fn human_state_goal_summary_pretty(context: &[String], target: &str) -> String {
    let mut lines = context.to_vec();
    lines.push(format!("|- {target}"));
    lines.join("\n")
}

fn human_state_materialization_error(
    header: &HumanStateRequestHeader,
    state_id: &crate::HumanStateId,
    error: HumanStructuredProofStateError,
) -> HumanStateApiError {
    HumanStateApiError::StateMaterialization {
        session_id: header.session_id.clone(),
        state_id: state_id.clone(),
        error: Box::new(error),
    }
}

fn human_state_id_at_position(
    session: &HumanProofSession,
    document_version: crate::HumanDocumentVersion,
    position: HumanSourcePosition,
) -> Option<crate::HumanStateId> {
    if position.file_id != session.document.file_id {
        return None;
    }

    let mut best: Option<(&HumanProofStateEntry, u32, bool)> = None;
    for entry in session.proof_states.states() {
        if entry.document_version != document_version {
            continue;
        }
        let Some(span) = entry.source_span else {
            continue;
        };
        if !human_span_contains_position(span, position) {
            continue;
        }
        let span_len = span.end.0.saturating_sub(span.start.0);
        let is_current = session.current_state_id.as_ref() == Some(&entry.state_id);
        let should_replace = best.is_none_or(|(best_entry, best_len, best_is_current)| {
            span_len < best_len
                || (span_len == best_len && is_current && !best_is_current)
                || (span_len == best_len
                    && is_current == best_is_current
                    && entry.state_id > best_entry.state_id)
        });
        if should_replace {
            best = Some((entry, span_len, is_current));
        }
    }
    best.map(|(entry, _, _)| entry.state_id.clone())
}

fn human_span_contains_position(span: npa_frontend::Span, position: HumanSourcePosition) -> bool {
    if span.file_id != position.file_id {
        return false;
    }
    if span.start == span.end {
        return position.offset == span.start;
    }
    span.start <= position.offset && position.offset < span.end
}

pub fn display_human_goal(
    store: &HumanProofSessionStore,
    request: HumanDisplayGoalRequest,
) -> Result<HumanDisplayTextOk, HumanDisplayError> {
    validate_human_state_request_document(store, request.header.clone())
        .map_err(HumanStateApiError::from)?;
    let entry = human_state_entry_for_api(store, &request.header, &request.state_id)?;
    let text = human_display_goal_text_for_entry(
        &request.header,
        entry,
        &request.goal_id,
        request.mode,
        request.context_options,
    )?;
    Ok(HumanDisplayTextOk {
        display_profile: HUMAN_DISPLAY_PROFILE_ID,
        mode: request.mode,
        text,
    })
}

pub fn display_human_expr(request: HumanDisplayExprRequest) -> HumanDisplayTextOk {
    let text = match request.mode {
        HumanDisplayMode::Pretty | HumanDisplayMode::Explicit => request.expr.pretty.clone(),
        HumanDisplayMode::Core => human_display_structured_expr_core_summary(&request.expr),
        HumanDisplayMode::Json => human_display_structured_expr_json(&request.expr),
    };
    HumanDisplayTextOk {
        display_profile: HUMAN_DISPLAY_PROFILE_ID,
        mode: request.mode,
        text,
    }
}

pub fn display_human_context(
    store: &HumanProofSessionStore,
    request: HumanDisplayContextRequest,
) -> Result<HumanDisplayContextOk, HumanDisplayError> {
    validate_human_state_request_document(store, request.header.clone())
        .map_err(HumanStateApiError::from)?;
    let entry = human_state_entry_for_api(store, &request.header, &request.state_id)?;
    let (structured, machine_goal) =
        human_display_goal_data(&request.header, entry, &request.goal_id)?;
    let (text, shown_count, folded_count) = human_display_context_text(
        &structured,
        &machine_goal,
        request.mode,
        request.context_options,
    );
    Ok(HumanDisplayContextOk {
        display_profile: HUMAN_DISPLAY_PROFILE_ID,
        mode: request.mode,
        text,
        shown_count,
        folded_count,
    })
}

pub fn display_human_diff(
    store: &HumanProofSessionStore,
    request: HumanDisplayDiffRequest,
) -> Result<HumanDisplayDiffOk, HumanDisplayError> {
    validate_human_state_request_document(store, request.header.clone())
        .map_err(HumanStateApiError::from)?;
    let before = human_state_entry_for_api(store, &request.header, &request.before_state_id)?;
    let after = human_state_entry_for_api(store, &request.header, &request.after_state_id)?;
    let before_goals = human_open_goal_ids(before);
    let after_goals = human_open_goal_ids(after);
    let before_set = before_goals.iter().cloned().collect::<BTreeSet<_>>();
    let after_set = after_goals.iter().cloned().collect::<BTreeSet<_>>();
    let closed = before_goals
        .into_iter()
        .filter(|goal_id| !after_set.contains(goal_id))
        .collect::<Vec<_>>();
    let added = after_goals
        .into_iter()
        .filter(|goal_id| !before_set.contains(goal_id))
        .collect::<Vec<_>>();

    let mut items = Vec::new();
    if let Some((first_closed, remaining_closed)) = closed.split_first() {
        if added.is_empty() {
            for goal_id in std::iter::once(first_closed).chain(remaining_closed) {
                items.push(human_display_closed_goal_diff_item(
                    &request.header,
                    before,
                    goal_id,
                    request.mode,
                )?);
            }
        } else {
            items.push(human_display_replaced_goal_diff_item(
                &request.header,
                before,
                after,
                first_closed,
                &added,
                request.mode,
            )?);
            for goal_id in remaining_closed {
                items.push(human_display_closed_goal_diff_item(
                    &request.header,
                    before,
                    goal_id,
                    request.mode,
                )?);
            }
        }
    } else {
        for goal_id in &added {
            items.push(human_display_added_goal_diff_item(
                &request.header,
                after,
                goal_id,
                request.mode,
            )?);
        }
    }

    let text = if request.mode == HumanDisplayMode::Json {
        human_display_diff_json(&items)
    } else if items.is_empty() {
        "goals unchanged".to_owned()
    } else {
        items
            .iter()
            .map(|item| item.text.clone())
            .collect::<Vec<_>>()
            .join("\n\n")
    };

    Ok(HumanDisplayDiffOk {
        display_profile: HUMAN_DISPLAY_PROFILE_ID,
        mode: request.mode,
        items,
        text,
    })
}

pub fn run_human_tactic(
    store: &mut HumanProofSessionStore,
    request: HumanTacticRunRequest,
) -> HumanTacticRunResponse {
    let session_id = request.header.session_id.clone();
    let parent_state_id = request.state_id.clone();
    let requested_goal_id = request.goal_id.clone();

    if let Err(error) = validate_human_state_request_document(store, request.header.clone()) {
        let state_error = HumanStateApiError::from(error);
        return human_tactic_run_state_error_response(
            session_id,
            parent_state_id,
            requested_goal_id,
            state_error,
        );
    }

    let context = match human_tactic_run_context(store, &request) {
        Ok(context) => context,
        Err(response) => return *response,
    };
    let tactic = match human_parse_single_tactic(
        context.file_id,
        &request.tactic,
        &context.imported_source_interfaces,
    ) {
        Ok(tactic) => tactic,
        Err(diagnostic) => {
            return human_tactic_run_human_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                diagnostic,
            );
        }
    };

    let execution = human_tactic_run_execute(
        &context.parent_state,
        context.machine_goal_id,
        &tactic,
        &context.current_source_interface,
        &context.imported_source_interfaces,
        context.options.clone(),
        request.budget,
    );
    let execution = match execution {
        Ok(execution) => execution,
        Err(HumanTacticScriptError::Human(HumanCompileError { diagnostic })) => {
            return human_tactic_run_human_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                diagnostic,
            );
        }
        Err(HumanTacticScriptError::Machine(diagnostic)) => {
            return human_tactic_run_machine_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                tactic.span(),
                diagnostic,
            );
        }
    };

    let parent_open_goals = context
        .parent_state
        .open_goals
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let selected_goal = execution
        .deltas
        .iter()
        .rev()
        .flat_map(|delta| delta.added_goals.iter().rev())
        .copied()
        .find(|goal_id| execution.state.open_goals.contains(goal_id))
        .or_else(|| execution.state.open_goals.first().copied());
    let closed_goals = (!execution
        .state
        .open_goals
        .contains(&context.machine_goal_id))
    .then_some(context.human_goal_id.clone())
    .into_iter()
    .collect::<Vec<_>>();

    let recorded = match record_human_tactic_state(
        store,
        HumanTacticStateRecordRequest {
            session_id: context.session_id.clone(),
            parent_state_id: context.parent_state_id.clone(),
            selected_goal,
            state: execution.state,
            source_span: context.parent_source_span,
            messages: Vec::new(),
        },
    ) {
        Ok(recorded) => recorded,
        Err(error) => {
            return human_tactic_run_record_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                error,
            );
        }
    };

    let new_entry = get_human_proof_state(store, &context.session_id, &recorded.state_id).expect(
        "record_human_tactic_state returned a state id that should be stored in the session",
    );
    let mut new_goals = Vec::new();
    for machine_goal_id in &new_entry.state.open_goals {
        if parent_open_goals.contains(machine_goal_id) {
            continue;
        }
        match materialize_human_structured_goal(new_entry, *machine_goal_id) {
            Ok(goal) => new_goals.push(goal),
            Err(error) => {
                return human_tactic_run_state_error_response(
                    context.session_id,
                    context.parent_state_id,
                    context.human_goal_id,
                    human_state_materialization_error(&request.header, &recorded.state_id, error),
                );
            }
        }
    }
    let status = if !new_goals.is_empty() {
        HumanTacticRunStatus::Partial
    } else if !closed_goals.is_empty() {
        HumanTacticRunStatus::Closed
    } else {
        HumanTacticRunStatus::Success
    };

    HumanTacticRunResponse {
        status,
        session_id: context.session_id,
        parent_state_id: context.parent_state_id,
        new_state_id: Some(recorded.state_id),
        selected_goal: recorded.selected_goal,
        closed_goals,
        new_goals,
        proof_deltas: execution.deltas,
        messages: recorded.messages,
        error: None,
    }
}

pub fn check_human_tactic(
    store: &HumanProofSessionStore,
    request: HumanTacticCheckRequest,
) -> HumanTacticCheckResponse {
    let run_request = HumanTacticRunRequest {
        header: request.header,
        state_id: request.state_id,
        goal_id: request.goal_id,
        tactic: request.tactic,
        budget: request.budget,
    };

    if let Err(error) = validate_human_state_request_document(store, run_request.header.clone()) {
        let response = human_tactic_run_state_error_response(
            run_request.header.session_id.clone(),
            run_request.state_id.clone(),
            run_request.goal_id.clone(),
            HumanStateApiError::from(error),
        );
        return human_tactic_check_from_run_response(response);
    }

    let context = match human_tactic_run_context(store, &run_request) {
        Ok(context) => context,
        Err(response) => return human_tactic_check_from_run_response(*response),
    };
    let tactic = match human_parse_single_tactic(
        context.file_id,
        &run_request.tactic,
        &context.imported_source_interfaces,
    ) {
        Ok(tactic) => tactic,
        Err(diagnostic) => {
            return human_tactic_check_from_run_response(human_tactic_run_human_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                diagnostic,
            ));
        }
    };

    let execution = match human_tactic_run_execute(
        &context.parent_state,
        context.machine_goal_id,
        &tactic,
        &context.current_source_interface,
        &context.imported_source_interfaces,
        context.options.clone(),
        run_request.budget,
    ) {
        Ok(execution) => execution,
        Err(HumanTacticScriptError::Human(HumanCompileError { diagnostic })) => {
            return human_tactic_check_from_run_response(human_tactic_run_human_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                diagnostic,
            ));
        }
        Err(HumanTacticScriptError::Machine(diagnostic)) => {
            return human_tactic_check_from_run_response(human_tactic_run_machine_error_response(
                context.session_id,
                context.parent_state_id,
                context.human_goal_id,
                Some(&context.before_goal),
                tactic.span(),
                diagnostic,
            ));
        }
    };

    let parent_open_goals = context
        .parent_state
        .open_goals
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let selected_machine_goal = execution
        .deltas
        .iter()
        .rev()
        .flat_map(|delta| delta.added_goals.iter().rev())
        .copied()
        .find(|goal_id| execution.state.open_goals.contains(goal_id))
        .or_else(|| execution.state.open_goals.first().copied());
    let closed_goals = (!execution
        .state
        .open_goals
        .contains(&context.machine_goal_id))
    .then_some(context.human_goal_id.clone())
    .into_iter()
    .collect::<Vec<_>>();
    let check_entry =
        human_tactic_check_entry(&context, execution.state.clone(), selected_machine_goal);
    let mut expected_goals = Vec::new();
    for machine_goal_id in &check_entry.state.open_goals {
        if parent_open_goals.contains(machine_goal_id) {
            continue;
        }
        match materialize_human_structured_goal(&check_entry, *machine_goal_id) {
            Ok(goal) => expected_goals.push(goal),
            Err(error) => {
                return human_tactic_check_from_run_response(
                    human_tactic_run_state_error_response(
                        context.session_id,
                        context.parent_state_id,
                        context.human_goal_id,
                        human_state_materialization_error(
                            &run_request.header,
                            &check_entry.state_id,
                            error,
                        ),
                    ),
                );
            }
        }
    }
    let status = if !expected_goals.is_empty() {
        HumanTacticRunStatus::Partial
    } else if !closed_goals.is_empty() {
        HumanTacticRunStatus::Closed
    } else {
        HumanTacticRunStatus::Success
    };

    HumanTacticCheckResponse {
        status,
        session_id: context.session_id,
        state_id: context.parent_state_id,
        goal_id: context.human_goal_id,
        selected_goal: check_entry.selected_goal,
        closed_goals,
        expected_goals,
        proof_deltas: execution.deltas,
        messages: Vec::new(),
        error: None,
    }
}

pub fn suggest_human_tactics(
    store: &HumanProofSessionStore,
    request: HumanTacticSuggestRequest,
) -> HumanTacticSuggestResponse {
    let run_request = HumanTacticRunRequest {
        header: request.header,
        state_id: request.state_id,
        goal_id: request.goal_id,
        tactic: String::new(),
        budget: npa_tactic::TacticBudget::default(),
    };

    if let Err(error) = validate_human_state_request_document(store, run_request.header.clone()) {
        let response = human_tactic_run_state_error_response(
            run_request.header.session_id.clone(),
            run_request.state_id.clone(),
            run_request.goal_id.clone(),
            HumanStateApiError::from(error),
        );
        return human_tactic_suggest_from_run_response(response);
    }

    let context = match human_tactic_run_context(store, &run_request) {
        Ok(context) => context,
        Err(response) => return human_tactic_suggest_from_run_response(*response),
    };
    let mut suggestions =
        human_builtin_tactic_suggestions(&context.parent_state, &context.before_goal);
    suggestions.sort_by(|left, right| {
        right
            .confidence
            .cmp(&left.confidence)
            .then_with(|| left.tactic.cmp(&right.tactic))
    });
    human_tactic_suggestion_dedupe(&mut suggestions);
    suggestions.truncate(request.max_results);

    HumanTacticSuggestResponse {
        session_id: context.session_id,
        state_id: context.parent_state_id,
        goal_id: context.human_goal_id,
        suggestions,
        messages: Vec::new(),
        error: None,
    }
}

pub fn human_assistant_payload(
    store: &HumanProofSessionStore,
    request: HumanAssistantPayloadRequest,
) -> Result<HumanAssistantPayloadOk, HumanAssistantPayloadError> {
    validate_human_state_request_document(store, request.header.clone())
        .map_err(|error| HumanAssistantPayloadError::State(error.into()))?;
    let state = materialize_human_state_for_api(store, &request.header, &request.state_id)
        .map_err(HumanAssistantPayloadError::State)?;
    let structured_goal = state
        .goals
        .iter()
        .find(|goal| goal.goal_id == request.goal_id)
        .cloned()
        .ok_or_else(|| HumanAssistantPayloadError::UnknownGoal {
            session_id: request.header.session_id.clone(),
            state_id: request.state_id.clone(),
            goal_id: request.goal_id.clone(),
        })?;
    let goal_summary = HumanStateGoalSummary {
        goal_id: structured_goal.goal_id.clone(),
        pretty: structured_goal.pretty.clone(),
    };
    let tactic_suggestions = suggest_human_tactics(
        store,
        HumanTacticSuggestRequest {
            header: request.header.clone(),
            state_id: request.state_id.clone(),
            goal_id: request.goal_id.clone(),
            max_results: request.max_tactic_suggestions,
        },
    )
    .suggestions
    .iter()
    .map(human_assistant_candidate_from_suggestion)
    .collect::<Vec<_>>();
    let nearby = search_human_theorems_for_goal(
        store,
        HumanTheoremGoalSearchRequest {
            header: request.header.clone(),
            state_id: request.state_id.clone(),
            goal_id: request.goal_id.clone(),
            modes: vec![
                HumanTheoremSearchMode::Exact,
                HumanTheoremSearchMode::Apply,
                HumanTheoremSearchMode::Rw,
                HumanTheoremSearchMode::Simp,
            ],
            options: HumanTheoremSearchOptions {
                limit: request.max_nearby_theorems,
                axiom_policy: HumanTheoremSearchAxiomPolicy::Allow,
            },
        },
    )
    .map_err(HumanAssistantPayloadError::Search)?;
    let nearby_theorems = nearby
        .results
        .iter()
        .map(human_assistant_nearby_theorem_from_search_result)
        .collect();
    let failed_tactics = request
        .failed_tactics
        .iter()
        .map(|failed| {
            human_assistant_failed_tactic_diagnostic(
                store,
                &request.header,
                &request.state_id,
                &request.goal_id,
                failed,
            )
        })
        .collect();

    Ok(HumanAssistantPayloadOk {
        session_id: request.header.session_id,
        state_id: request.state_id,
        goal_id: request.goal_id,
        document_version: state.document_version,
        goal_summary,
        structured_goal,
        available_tactics: human_assistant_available_tactics(),
        tactic_suggestions,
        nearby_theorems,
        failed_tactics,
    })
}

pub fn validate_human_assistant_candidates(
    store: &HumanProofSessionStore,
    request: HumanAssistantCandidateValidationRequest,
) -> HumanAssistantCandidateValidationOk {
    let mut accepted = Vec::new();
    let mut rejected = Vec::new();
    for candidate in request.candidates {
        let mut scratch = store.clone();
        let response = run_human_tactic(
            &mut scratch,
            HumanTacticRunRequest {
                header: request.header.clone(),
                state_id: request.state_id.clone(),
                goal_id: request.goal_id.clone(),
                tactic: candidate.tactic.clone(),
                budget: request.budget,
            },
        );
        if human_assistant_tactic_response_accepts(&response) {
            accepted.push(HumanAssistantValidatedCandidate {
                candidate,
                status: response.status,
                selected_goal: response.selected_goal,
                closed_goals: response.closed_goals,
            });
        } else {
            rejected.push(HumanAssistantRejectedCandidate {
                candidate,
                status: response.status,
                messages: response.messages,
                error: response.error,
            });
        }
    }

    HumanAssistantCandidateValidationOk {
        session_id: request.header.session_id,
        state_id: request.state_id,
        goal_id: request.goal_id,
        accepted,
        rejected,
    }
}

fn human_assistant_candidate_from_suggestion(
    suggestion: &HumanTacticSuggestion,
) -> HumanAssistantCandidate {
    HumanAssistantCandidate {
        tactic: suggestion.tactic.clone(),
        confidence: suggestion.confidence,
        reason: suggestion.reason.clone(),
    }
}

fn human_assistant_nearby_theorem_from_search_result(
    result: &HumanTheoremSearchResult,
) -> crate::HumanAssistantNearbyTheorem {
    crate::HumanAssistantNearbyTheorem {
        name: result.name.clone(),
        statement_pretty: result.statement_pretty.clone(),
        suggested_tactic: result.suggested_tactic.clone(),
        mode: result.mode,
        why: result.why.clone(),
        score: result.score,
        axiom_info: result.axiom_info.clone(),
    }
}

fn human_assistant_failed_tactic_diagnostic(
    store: &HumanProofSessionStore,
    header: &HumanStateRequestHeader,
    state_id: &crate::HumanStateId,
    goal_id: &HumanGoalId,
    failed: &crate::HumanAssistantFailedTacticRequest,
) -> HumanAssistantFailedTacticDiagnostic {
    let mut scratch = store.clone();
    let response = run_human_tactic(
        &mut scratch,
        HumanTacticRunRequest {
            header: header.clone(),
            state_id: state_id.clone(),
            goal_id: goal_id.clone(),
            tactic: failed.tactic.clone(),
            budget: failed.budget,
        },
    );
    HumanAssistantFailedTacticDiagnostic {
        tactic: failed.tactic.clone(),
        status: response.status,
        messages: response.messages,
        error: response.error,
    }
}

fn human_assistant_tactic_response_accepts(response: &HumanTacticRunResponse) -> bool {
    response.error.is_none()
        && matches!(
            response.status,
            HumanTacticRunStatus::Success
                | HumanTacticRunStatus::Closed
                | HumanTacticRunStatus::Partial
        )
}

fn human_assistant_available_tactics() -> Vec<HumanAssistantAvailableTactic> {
    [
        ("intro", "Introduce a binder from a Pi/forall target"),
        ("exact", "Close the goal with a term of the target type"),
        ("apply", "Apply a theorem or function to the current goal"),
        ("rw", "Rewrite the target using an equality proof"),
        ("simp-lite", "Run deterministic built-in simplification"),
        (
            "smt",
            "Close with checked SMT reconstruction or explicit lemmas",
        ),
        (
            "induction",
            "Split a Nat local into zero and successor cases",
        ),
    ]
    .into_iter()
    .map(|(tactic, description)| HumanAssistantAvailableTactic {
        tactic: tactic.to_owned(),
        description: description.to_owned(),
    })
    .collect()
}

pub fn human_lsp_diagnostic_from_human(
    source: HumanCurrentModuleSource<'_>,
    diagnostic: &npa_frontend::HumanDiagnostic,
) -> HumanLspDiagnostic {
    HumanLspDiagnostic {
        range: human_lsp_range_for_span(source, diagnostic.primary_span),
        severity: human_lsp_diagnostic_severity(diagnostic.severity.clone()),
        code: human_lsp_diagnostic_kind_code(&diagnostic.kind).to_owned(),
        source: "npa-human",
        message: diagnostic.message.clone(),
        data: human_lsp_diagnostic_data(source, diagnostic),
    }
}

pub fn human_lsp_diagnostics(
    store: &HumanProofSessionStore,
    request: HumanLspDiagnosticsRequest,
) -> Result<HumanLspDiagnosticsOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    let session = store
        .session(&request.header.session_id)
        .expect("Human LSP diagnostics validation checked session existence");
    let source = session.document.current_source();
    let diagnostics = session
        .messages
        .iter()
        .map(|diagnostic| human_lsp_diagnostic_from_human(source, diagnostic))
        .collect();
    Ok(HumanLspDiagnosticsOk {
        session_id: request.header.session_id,
        document_id: request.header.document_id,
        document_version: request.header.document_version,
        diagnostics,
    })
}

pub fn human_lsp_hover(
    store: &HumanProofSessionStore,
    request: HumanLspHoverRequest,
) -> Result<HumanLspHoverOk, HumanTheoremSearchError> {
    let (entry, index) = human_search_index_for_state(store, &request.header, &request.state_id)?;
    let hover = index
        .entries
        .iter()
        .find(|entry| human_lsp_theorem_name_matches(&entry.name, &request.name))
        .map(human_lsp_hover_from_theorem);

    Ok(HumanLspHoverOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        hover,
    })
}

pub fn human_lsp_completions(
    store: &HumanProofSessionStore,
    request: HumanLspCompletionRequest,
) -> HumanLspCompletionOk {
    let response = suggest_human_tactics(
        store,
        HumanTacticSuggestRequest {
            header: request.header,
            state_id: request.state_id,
            goal_id: request.goal_id,
            max_results: request.max_results,
        },
    );
    let mut items = response
        .suggestions
        .iter()
        .map(human_lsp_completion_item_from_suggestion)
        .collect::<Vec<_>>();
    if request.include_search_command && response.error.is_none() {
        items.push(HumanLspCompletionItem {
            label: "Search nearby theorem".to_owned(),
            kind: HumanLspCompletionItemKind::Command,
            detail: "Open Human theorem search for the current goal".to_owned(),
            insert_text: None,
            command: Some(human_lsp_search_command(
                &response.session_id,
                &response.state_id,
                &response.goal_id,
            )),
        });
    }

    HumanLspCompletionOk {
        session_id: response.session_id,
        state_id: response.state_id,
        goal_id: response.goal_id,
        items,
        error: response.error,
    }
}

pub fn human_lsp_code_actions(
    store: &HumanProofSessionStore,
    request: HumanLspCodeActionRequest,
) -> HumanLspCodeActionOk {
    let response = suggest_human_tactics(
        store,
        HumanTacticSuggestRequest {
            header: request.header,
            state_id: request.state_id,
            goal_id: request.goal_id,
            max_results: request.max_tactic_suggestions,
        },
    );
    let mut actions = response
        .suggestions
        .iter()
        .map(human_lsp_code_action_from_suggestion)
        .collect::<Vec<_>>();
    if request.include_search_command && response.error.is_none() {
        actions.push(HumanLspCodeAction {
            title: "Search nearby theorem".to_owned(),
            kind: HumanLspCodeActionKind::Command,
            tactic: None,
            command: Some(human_lsp_search_command(
                &response.session_id,
                &response.state_id,
                &response.goal_id,
            )),
            diagnostics: Vec::new(),
        });
    }

    HumanLspCodeActionOk {
        session_id: response.session_id,
        state_id: response.state_id,
        goal_id: response.goal_id,
        actions,
        error: response.error,
    }
}

pub fn human_lsp_document_payloads(
    store: &HumanProofSessionStore,
    request: HumanLspDocumentPayloadRequest,
) -> Result<HumanLspDocumentPayloadOk, HumanStateApiError> {
    validate_human_state_request_document(store, request.header.clone())?;
    let session = store
        .session(&request.header.session_id)
        .expect("Human LSP document validation checked session existence");
    let source = session.document.current_source();
    let mut semantic_tokens = Vec::new();
    let mut document_symbols = Vec::new();
    let mut inlay_hints = Vec::new();
    if let Some(interface) = &session.source_interface {
        for decl in interface
            .declarations
            .iter()
            .filter(|decl| decl.kind != npa_frontend::HumanSourceDeclarationKind::Imported)
        {
            let selection_range = human_lsp_range_for_span(source, decl.name.span);
            semantic_tokens.push(HumanLspSemanticToken {
                range: selection_range,
                token_type: human_lsp_semantic_token_type(decl.kind),
            });
            document_symbols.push(HumanLspDocumentSymbol {
                name: decl.name.as_dotted(),
                kind: human_lsp_symbol_kind(decl.kind),
                range: human_lsp_range_for_span(source, decl.span),
                selection_range,
            });
            for binder in &decl.binders {
                inlay_hints.push(HumanLspInlayHint {
                    position: human_lsp_range_for_span(source, binder.span).end,
                    label: human_lsp_binder_hint_label(binder.binder_info),
                    kind: HumanLspInlayHintKind::Parameter,
                });
                if let Some(name) = &binder.name {
                    semantic_tokens.push(HumanLspSemanticToken {
                        range: human_lsp_range_for_span(source, name.span),
                        token_type: HumanLspSemanticTokenType::Variable,
                    });
                }
            }
        }
    }

    Ok(HumanLspDocumentPayloadOk {
        session_id: request.header.session_id,
        document_id: request.header.document_id,
        document_version: request.header.document_version,
        semantic_tokens,
        document_symbols,
        inlay_hints,
    })
}

pub fn human_lsp_goal_view(
    store: &HumanProofSessionStore,
    request: HumanLspGoalViewRequest,
) -> Result<HumanLspGoalViewOk, HumanDisplayError> {
    let goals = get_human_state_goals(
        store,
        HumanStateGoalsRequest {
            header: request.header.clone(),
            state_id: request.state_id.clone(),
        },
    )?;
    let focused_goal = display_human_goal(
        store,
        HumanDisplayGoalRequest {
            header: request.header,
            state_id: request.state_id,
            goal_id: request.goal_id,
            mode: request.mode,
            context_options: request.context_options,
        },
    )?;

    Ok(HumanLspGoalViewOk {
        session_id: goals.session_id,
        state_id: goals.state_id,
        document_version: goals.document_version,
        goals: goals.goals,
        focused_goal,
    })
}

fn human_lsp_range_for_span(
    source: HumanCurrentModuleSource<'_>,
    span: npa_frontend::Span,
) -> HumanLspRange {
    if span.file_id != source.file_id {
        let zero = HumanLspPosition {
            line: 0,
            character: 0,
        };
        return HumanLspRange {
            start: zero,
            end: zero,
        };
    }
    HumanLspRange {
        start: human_lsp_position_for_offset(source.source, span.start.0),
        end: human_lsp_position_for_offset(source.source, span.end.0),
    }
}

fn human_lsp_position_for_offset(source: &str, offset: u32) -> HumanLspPosition {
    let target = usize::try_from(offset)
        .ok()
        .map(|offset| offset.min(source.len()))
        .unwrap_or(source.len());
    let mut line = 0_u32;
    let mut character = 0_u32;
    for (index, ch) in source.char_indices() {
        if index >= target {
            break;
        }
        if ch == '\n' {
            line = line.saturating_add(1);
            character = 0;
        } else {
            character = character.saturating_add(ch.len_utf16() as u32);
        }
    }
    HumanLspPosition { line, character }
}

fn human_lsp_diagnostic_severity(
    severity: npa_frontend::HumanDiagnosticSeverity,
) -> HumanLspDiagnosticSeverity {
    match severity {
        npa_frontend::HumanDiagnosticSeverity::Error => HumanLspDiagnosticSeverity::Error,
        npa_frontend::HumanDiagnosticSeverity::Warning => HumanLspDiagnosticSeverity::Warning,
    }
}

fn human_lsp_diagnostic_data(
    source: HumanCurrentModuleSource<'_>,
    diagnostic: &npa_frontend::HumanDiagnostic,
) -> HumanLspDiagnosticData {
    let payload = diagnostic.payload.as_deref();
    HumanLspDiagnosticData {
        kind: human_lsp_diagnostic_kind_code(&diagnostic.kind).to_owned(),
        phase: payload
            .and_then(|payload| payload.phase)
            .map(|phase| phase.as_str().to_owned()),
        detail: payload.and_then(|payload| payload.detail.clone()),
        candidates: payload
            .map(|payload| payload.candidates.clone())
            .unwrap_or_default(),
        hole_goals: payload
            .map(|payload| {
                payload
                    .hole_goals
                    .iter()
                    .map(|goal| HumanLspHoleGoal {
                        hole: goal.hole.clone(),
                        range: human_lsp_range_for_span(source, goal.source_span),
                        context: goal
                            .context
                            .iter()
                            .map(|local| HumanLspHoleGoalLocal {
                                name: local.name.clone(),
                                ty: local.ty.clone(),
                                value: local.value.clone(),
                            })
                            .collect(),
                        target: goal.target.clone(),
                    })
                    .collect()
            })
            .unwrap_or_default(),
        unsolved_meta: payload
            .and_then(|payload| payload.unsolved_meta.as_ref())
            .map(|meta| HumanLspUnsolvedMeta {
                kind: human_lsp_unsolved_meta_kind(meta.kind).to_owned(),
                name: meta.name.clone(),
            }),
    }
}

fn human_lsp_diagnostic_kind_code(kind: &npa_frontend::HumanDiagnosticKind) -> &'static str {
    match kind {
        npa_frontend::HumanDiagnosticKind::NotImplemented => "not_implemented",
        npa_frontend::HumanDiagnosticKind::ParseError => "parse_error",
        npa_frontend::HumanDiagnosticKind::ImportAfterItem => "import_after_item",
        npa_frontend::HumanDiagnosticKind::UnsupportedSyntax => "unsupported_syntax",
        npa_frontend::HumanDiagnosticKind::ImportResolutionError => "import_resolution_error",
        npa_frontend::HumanDiagnosticKind::MissingVerifiedImport => "missing_verified_import",
        npa_frontend::HumanDiagnosticKind::NamespaceMismatch => "namespace_mismatch",
        npa_frontend::HumanDiagnosticKind::UnknownNamespace => "unknown_namespace",
        npa_frontend::HumanDiagnosticKind::DuplicateDeclaration => "duplicate_declaration",
        npa_frontend::HumanDiagnosticKind::UnknownIdentifier => "unknown_identifier",
        npa_frontend::HumanDiagnosticKind::AmbiguousName => "ambiguous_name",
        npa_frontend::HumanDiagnosticKind::AmbiguousConstructor => "ambiguous_constructor",
        npa_frontend::HumanDiagnosticKind::ForwardReference => "forward_reference",
        npa_frontend::HumanDiagnosticKind::NotationConflict => "notation_conflict",
        npa_frontend::HumanDiagnosticKind::AmbiguousNotation => "ambiguous_notation",
        npa_frontend::HumanDiagnosticKind::TooManyNotationCandidates => {
            "too_many_notation_candidates"
        }
        npa_frontend::HumanDiagnosticKind::TypeclassNoSolution => "typeclass_no_solution",
        npa_frontend::HumanDiagnosticKind::TypeclassAmbiguous => "typeclass_ambiguous",
        npa_frontend::HumanDiagnosticKind::TypeclassBudgetExceeded => "typeclass_budget_exceeded",
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic => "unsupported_tactic",
        npa_frontend::HumanDiagnosticKind::UnsupportedEquationGuard => "unsupported_equation_guard",
        npa_frontend::HumanDiagnosticKind::UnsupportedViewPattern => "unsupported_view_pattern",
        npa_frontend::HumanDiagnosticKind::EquationCompilerDisabled => "equation_compiler_disabled",
        npa_frontend::HumanDiagnosticKind::NonExhaustivePatterns => "non_exhaustive_patterns",
        npa_frontend::HumanDiagnosticKind::RedundantEquation => "redundant_equation",
        npa_frontend::HumanDiagnosticKind::ImpossibleBranchNotProvable => {
            "impossible_branch_not_provable"
        }
        npa_frontend::HumanDiagnosticKind::RecursiveCallNotDecreasing => {
            "recursive_call_not_decreasing"
        }
        npa_frontend::HumanDiagnosticKind::MutualCycleWithoutDecrease => {
            "mutual_cycle_without_decrease"
        }
        npa_frontend::HumanDiagnosticKind::TerminationMeasureNotNat => {
            "termination_measure_not_nat"
        }
        npa_frontend::HumanDiagnosticKind::MeasureDecreaseProofMissing => {
            "measure_decrease_proof_missing"
        }
        npa_frontend::HumanDiagnosticKind::UnsolvedImplicit => "unsolved_implicit",
        npa_frontend::HumanDiagnosticKind::UnsolvedMeta => "unsolved_meta",
        npa_frontend::HumanDiagnosticKind::UnsolvedUniverseMeta => "unsolved_universe_meta",
        npa_frontend::HumanDiagnosticKind::UnsolvedHole => "unsolved_hole",
        npa_frontend::HumanDiagnosticKind::NamedHoleContextMismatch => {
            "named_hole_context_mismatch"
        }
        npa_frontend::HumanDiagnosticKind::OccursCheckFailed => "occurs_check_failed",
        npa_frontend::HumanDiagnosticKind::ExpectedFunctionType => "expected_function_type",
        npa_frontend::HumanDiagnosticKind::ExpectedSort => "expected_sort",
        npa_frontend::HumanDiagnosticKind::TypeMismatch => "type_mismatch",
        npa_frontend::HumanDiagnosticKind::NoGoalsButTacticRemaining => {
            "no_goals_but_tactic_remaining"
        }
        npa_frontend::HumanDiagnosticKind::UnresolvedGoal => "unresolved_goal",
        npa_frontend::HumanDiagnosticKind::KernelRejected => "kernel_rejected",
        npa_frontend::HumanDiagnosticKind::MachineElaborationError => "machine_elaboration_error",
    }
}

fn human_lsp_unsolved_meta_kind(kind: npa_frontend::HumanUnsolvedMetaKind) -> &'static str {
    match kind {
        npa_frontend::HumanUnsolvedMetaKind::Hole => "hole",
        npa_frontend::HumanUnsolvedMetaKind::SyntheticImplicit => "synthetic_implicit",
        npa_frontend::HumanUnsolvedMetaKind::Universe => "universe",
    }
}

fn human_lsp_hover_from_theorem(theorem: &HumanTheoremIndexEntry) -> HumanLspHover {
    let axiom_info = HumanTheoremAxiomInfo {
        uses_axioms: !theorem.axiom_dependencies.is_empty(),
        axiom_dependencies: theorem.axiom_dependencies.clone(),
        score_penalty: 0,
    };
    let axiom_line = if axiom_info.uses_axioms {
        format!("axioms: {}", axiom_info.axiom_dependencies.len())
    } else {
        "axioms: none".to_owned()
    };
    let contents = format!(
        "```npa\n{} : {}\n```\nkind: {}\n{}",
        theorem.name.as_dotted(),
        theorem.statement_pretty,
        theorem.kind.as_str(),
        axiom_line
    );
    HumanLspHover {
        contents,
        theorem: HumanLspHoverTheorem {
            name: theorem.name.clone(),
            module: theorem.module.clone(),
            kind: theorem.kind,
            statement_pretty: theorem.statement_pretty.clone(),
            attributes: theorem.attributes.clone(),
            axiom_info,
            export_hash: theorem.export_hash,
            certificate_hash: theorem.certificate_hash,
            decl_interface_hash: theorem.decl_interface_hash,
        },
    }
}

fn human_lsp_theorem_name_matches(full_name: &Name, requested_name: &Name) -> bool {
    if full_name == requested_name {
        return true;
    }
    let full_name = full_name.as_dotted();
    let requested_name = requested_name.as_dotted();
    full_name.ends_with(&format!(".{requested_name}"))
}

fn human_lsp_completion_item_from_suggestion(
    suggestion: &HumanTacticSuggestion,
) -> HumanLspCompletionItem {
    HumanLspCompletionItem {
        label: suggestion.tactic.clone(),
        kind: HumanLspCompletionItemKind::Tactic,
        detail: suggestion.reason.clone(),
        insert_text: Some(suggestion.tactic.clone()),
        command: None,
    }
}

fn human_lsp_code_action_from_suggestion(suggestion: &HumanTacticSuggestion) -> HumanLspCodeAction {
    HumanLspCodeAction {
        title: format!("Run `{}`", suggestion.tactic),
        kind: HumanLspCodeActionKind::QuickFix,
        tactic: Some(suggestion.tactic.clone()),
        command: None,
        diagnostics: Vec::new(),
    }
}

fn human_lsp_search_command(
    session_id: &crate::HumanSessionId,
    state_id: &crate::HumanStateId,
    goal_id: &HumanGoalId,
) -> HumanLspCommand {
    HumanLspCommand {
        title: "Search nearby theorem".to_owned(),
        command: "npa.human.search.for_goal".to_owned(),
        arguments: vec![
            session_id.wire().to_owned(),
            state_id.wire().to_owned(),
            goal_id.wire().to_owned(),
        ],
    }
}

fn human_lsp_semantic_token_type(
    kind: npa_frontend::HumanSourceDeclarationKind,
) -> HumanLspSemanticTokenType {
    match kind {
        npa_frontend::HumanSourceDeclarationKind::Def => HumanLspSemanticTokenType::Function,
        npa_frontend::HumanSourceDeclarationKind::Theorem
        | npa_frontend::HumanSourceDeclarationKind::Axiom => HumanLspSemanticTokenType::Theorem,
        npa_frontend::HumanSourceDeclarationKind::Inductive
        | npa_frontend::HumanSourceDeclarationKind::Class => HumanLspSemanticTokenType::Type,
        npa_frontend::HumanSourceDeclarationKind::ClassField
        | npa_frontend::HumanSourceDeclarationKind::Instance
        | npa_frontend::HumanSourceDeclarationKind::Imported => HumanLspSemanticTokenType::Function,
    }
}

fn human_lsp_symbol_kind(kind: npa_frontend::HumanSourceDeclarationKind) -> HumanLspSymbolKind {
    match kind {
        npa_frontend::HumanSourceDeclarationKind::Def => HumanLspSymbolKind::Function,
        npa_frontend::HumanSourceDeclarationKind::Theorem
        | npa_frontend::HumanSourceDeclarationKind::Axiom => HumanLspSymbolKind::Theorem,
        npa_frontend::HumanSourceDeclarationKind::Inductive
        | npa_frontend::HumanSourceDeclarationKind::Class => HumanLspSymbolKind::Type,
        npa_frontend::HumanSourceDeclarationKind::ClassField
        | npa_frontend::HumanSourceDeclarationKind::Instance
        | npa_frontend::HumanSourceDeclarationKind::Imported => HumanLspSymbolKind::Function,
    }
}

fn human_lsp_binder_hint_label(info: npa_frontend::HumanBinderInfo) -> String {
    match info {
        npa_frontend::HumanBinderInfo::Explicit => "explicit binder".to_owned(),
        npa_frontend::HumanBinderInfo::Implicit => "implicit binder".to_owned(),
    }
}

fn human_tactic_check_from_run_response(
    response: HumanTacticRunResponse,
) -> HumanTacticCheckResponse {
    let goal_id = response
        .error
        .as_ref()
        .map(|error| error.goal_id.clone())
        .or_else(|| response.selected_goal.clone())
        .unwrap_or_else(|| HumanGoalId::new_unchecked("unknown_goal"));
    HumanTacticCheckResponse {
        status: response.status,
        session_id: response.session_id,
        state_id: response.parent_state_id,
        goal_id,
        selected_goal: response.selected_goal,
        closed_goals: response.closed_goals,
        expected_goals: response.new_goals,
        proof_deltas: response.proof_deltas,
        messages: response.messages,
        error: response.error,
    }
}

fn human_tactic_suggest_from_run_response(
    response: HumanTacticRunResponse,
) -> HumanTacticSuggestResponse {
    let goal_id = response
        .error
        .as_ref()
        .map(|error| error.goal_id.clone())
        .or_else(|| response.selected_goal.clone())
        .unwrap_or_else(|| HumanGoalId::new_unchecked("unknown_goal"));
    HumanTacticSuggestResponse {
        session_id: response.session_id,
        state_id: response.parent_state_id,
        goal_id,
        suggestions: Vec::new(),
        messages: response.messages,
        error: response.error,
    }
}

fn human_tactic_check_entry(
    context: &HumanTacticRunContext,
    state: npa_tactic::MachineProofState,
    selected_goal: Option<npa_tactic::GoalId>,
) -> HumanProofStateEntry {
    let goal_mappings = human_tactic_check_goal_mappings(context, &state);
    let selected_goal = selected_goal
        .and_then(|goal_id| {
            goal_mappings
                .iter()
                .find(|mapping| mapping.machine_goal_id == goal_id)
                .map(|mapping| mapping.human_goal_id.clone())
        })
        .or_else(|| {
            goal_mappings
                .first()
                .map(|mapping| mapping.human_goal_id.clone())
        });
    HumanProofStateEntry {
        state_id: crate::HumanStateId::new_unchecked(format!(
            "{}_check",
            context.parent_state_id.wire()
        )),
        parent_state_id: Some(context.parent_state_id.clone()),
        document_version: context.parent_document_version,
        source_span: context.parent_source_span,
        selected_goal,
        goal_mappings,
        state,
        messages: Vec::new(),
    }
}

fn human_tactic_check_goal_mappings(
    context: &HumanTacticRunContext,
    state: &npa_tactic::MachineProofState,
) -> Vec<HumanGoalMapping> {
    state
        .open_goals
        .iter()
        .map(|machine_goal_id| {
            context
                .parent_goal_mappings
                .iter()
                .find(|mapping| mapping.machine_goal_id == *machine_goal_id)
                .cloned()
                .unwrap_or_else(|| HumanGoalMapping {
                    human_goal_id: HumanGoalId::new_unchecked(format!(
                        "check_goal_{}",
                        machine_goal_id.0
                    )),
                    machine_goal_id: *machine_goal_id,
                })
        })
        .collect()
}

fn human_builtin_tactic_suggestions(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
) -> Vec<HumanTacticSuggestion> {
    let local_names = goal
        .context
        .iter()
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    let mut suggestions = Vec::new();

    for (_, local) in goal
        .context
        .iter()
        .enumerate()
        .rev()
        .filter(|(local_index, local)| {
            local.value.is_none()
                && human_tactic_local_type_matches_target(state, goal, *local_index, &local.ty)
        })
    {
        suggestions.push(human_tactic_builtin_suggestion(
            97,
            format!("context local `{}` has the target type", local.name),
            format!("exact {}", local.name),
        ));
    }

    if let Some((lhs, rhs)) = human_eq_app_sides(&goal.target) {
        if lhs == rhs {
            suggestions.push(human_tactic_builtin_suggestion(
                95,
                "target is reflexive equality",
                format!(
                    "exact Eq.refl {}",
                    human_tactic_argument_text(lhs, &local_names)
                ),
            ));
            suggestions.push(human_tactic_builtin_suggestion(
                80,
                "target can likely be simplified to reflexive equality",
                "simp-lite",
            ));
        }
    }

    if let Expr::Pi { binder, ty, .. } = &goal.target {
        let name = human_tactic_suggest_intro_name(binder, ty, goal);
        suggestions.push(human_tactic_builtin_suggestion(
            92,
            "target is a Pi/forall type",
            format!("intro {name}"),
        ));
    }

    for local in goal
        .context
        .iter()
        .rev()
        .filter(|local| local.value.is_none() && human_expr_concludes_eq(&local.ty))
    {
        suggestions.push(human_tactic_builtin_suggestion(
            67,
            format!(
                "context equality `{}` can be tried as a rewrite rule",
                local.name
            ),
            format!("rw [{}]", local.name),
        ));
    }

    for checked in &state.env.checked_current_decls {
        if human_expr_concludes_eq(checked.signature().ty()) {
            suggestions.push(human_tactic_builtin_suggestion(
                62,
                format!(
                    "checked current theorem `{}` has an equality conclusion",
                    checked.signature().name().as_dotted()
                ),
                format!("rw [{}]", checked.signature().name().as_dotted()),
            ));
        }
    }

    for import in state
        .env
        .imports
        .iter()
        .filter(|import| import.is_visible())
    {
        for export in import.exports() {
            if let Some(decl) = state.env.kernel_env().decl(&export.name.as_dotted()) {
                if human_expr_concludes_eq(decl.ty()) {
                    suggestions.push(human_tactic_builtin_suggestion(
                        60,
                        format!(
                            "verified import theorem `{}` has an equality conclusion",
                            export.name.as_dotted()
                        ),
                        format!("rw [{}]", export.name.as_dotted()),
                    ));
                }
            }
        }
    }

    for local in goal
        .context
        .iter()
        .filter(|local| local.value.is_none() && human_expr_is_nat(&local.ty))
    {
        suggestions.push(human_tactic_builtin_suggestion(
            58,
            format!("local `{}` has Nat type", local.name),
            format!("induction {}", local.name),
        ));
    }

    if human_expr_contains_nat(&goal.target) {
        for local in goal
            .context
            .iter()
            .filter(|local| local.value.is_none() && human_expr_is_nat(&local.ty))
        {
            suggestions.push(human_tactic_builtin_suggestion(
                55,
                format!(
                    "target mentions Nat and local `{}` is inductive",
                    local.name
                ),
                format!("induction {}", local.name),
            ));
        }
    }

    human_tactic_suggestion_dedupe(&mut suggestions);
    suggestions
}

fn human_tactic_builtin_suggestion(
    confidence: u8,
    reason: impl Into<String>,
    tactic: impl Into<String>,
) -> HumanTacticSuggestion {
    HumanTacticSuggestion {
        source: HumanTacticSuggestionSource::Builtin,
        confidence,
        reason: reason.into(),
        tactic: tactic.into(),
    }
}

fn human_tactic_suggestion_dedupe(suggestions: &mut Vec<HumanTacticSuggestion>) {
    let mut seen = BTreeSet::new();
    suggestions.retain(|suggestion| seen.insert(suggestion.tactic.clone()));
}

fn human_tactic_suggest_intro_name(
    binder: &str,
    ty: &Expr,
    goal: &npa_tactic::MachineGoal,
) -> String {
    let base = if human_tactic_suggest_valid_ident(binder) && binder != "_" {
        binder
    } else if human_expr_is_nat(ty) {
        "n"
    } else {
        "x"
    };
    human_tactic_suggest_fresh_name(base, goal)
}

fn human_tactic_suggest_valid_ident(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn human_tactic_suggest_fresh_name(base: &str, goal: &npa_tactic::MachineGoal) -> String {
    let existing = goal
        .context
        .iter()
        .map(|local| local.name.as_str())
        .collect::<BTreeSet<_>>();
    if !existing.contains(base) {
        return base.to_owned();
    }
    for index in 1..=usize::MAX {
        let candidate = format!("{base}{index}");
        if !existing.contains(candidate.as_str()) {
            return candidate;
        }
    }
    unreachable!("usize iteration should find a fresh Human suggestion name")
}

fn human_tactic_argument_text(expr: &Expr, local_names: &[String]) -> String {
    let text = human_render_core_expr(expr, local_names);
    if text.contains(' ') || text.starts_with("forall ") || text.starts_with("fun ") {
        format!("({text})")
    } else {
        text
    }
}

fn human_tactic_local_type_matches_target(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    local_index: usize,
    local_ty: &Expr,
) -> bool {
    if local_ty == &goal.target {
        return true;
    }
    if human_tactic_local_type_pretty_matches_target(goal, local_index, local_ty) {
        return true;
    }
    let Ok(ctx) = human_apply_goal_ctx(
        state,
        goal,
        npa_frontend::Span::empty(npa_frontend::FileId(0)),
    ) else {
        return false;
    };
    state
        .env
        .kernel_env()
        .is_defeq(&ctx, &state.root.universe_params, local_ty, &goal.target)
        .unwrap_or(false)
}

fn human_tactic_local_type_pretty_matches_target(
    goal: &npa_tactic::MachineGoal,
    local_index: usize,
    local_ty: &Expr,
) -> bool {
    let local_names_before = goal
        .context
        .iter()
        .take(local_index)
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    let local_names_all = goal
        .context
        .iter()
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    human_structured_expr_pretty(local_ty, &local_names_before)
        == human_structured_expr_pretty(&goal.target, &local_names_all)
}

fn human_expr_concludes_eq(expr: &Expr) -> bool {
    let mut current = expr;
    while let Expr::Pi { body, .. } = current {
        current = body;
    }
    human_eq_app_sides(current).is_some()
}

fn human_expr_is_nat(expr: &Expr) -> bool {
    matches!(expr, Expr::Const { name, .. } if name == "Nat")
}

fn human_expr_contains_nat(expr: &Expr) -> bool {
    match expr {
        Expr::Const { name, .. } => name == "Nat",
        Expr::App(func, arg) => human_expr_contains_nat(func) || human_expr_contains_nat(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            human_expr_contains_nat(ty) || human_expr_contains_nat(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            human_expr_contains_nat(ty)
                || human_expr_contains_nat(value)
                || human_expr_contains_nat(body)
        }
        Expr::Sort(_) | Expr::BVar(_) => false,
    }
}

#[derive(Clone, Debug)]
struct HumanTacticRunContext {
    session_id: crate::HumanSessionId,
    parent_state_id: crate::HumanStateId,
    human_goal_id: crate::HumanGoalId,
    machine_goal_id: npa_tactic::GoalId,
    parent_state: npa_tactic::MachineProofState,
    parent_document_version: crate::HumanDocumentVersion,
    parent_goal_mappings: Vec<HumanGoalMapping>,
    before_goal: npa_tactic::MachineGoal,
    parent_source_span: Option<npa_frontend::Span>,
    file_id: npa_frontend::FileId,
    current_source_interface: npa_frontend::HumanSourceInterface,
    imported_source_interfaces: Vec<npa_frontend::HumanImportedSourceInterface>,
    options: HumanApiCompileOptions,
}

fn human_tactic_run_context(
    store: &HumanProofSessionStore,
    request: &HumanTacticRunRequest,
) -> Result<HumanTacticRunContext, Box<HumanTacticRunResponse>> {
    let session = store
        .session(&request.header.session_id)
        .expect("Human tactic run document validation checked session existence");
    let entry = match human_state_entry_for_api(store, &request.header, &request.state_id) {
        Ok(entry) => entry,
        Err(error) => {
            return Err(Box::new(human_tactic_run_state_error_response(
                request.header.session_id.clone(),
                request.state_id.clone(),
                request.goal_id.clone(),
                error,
            )));
        }
    };
    let Some(machine_goal_id) = entry.machine_goal_for_human_goal(&request.goal_id) else {
        return Err(Box::new(human_tactic_run_error_response(
            HumanTacticRunErrorResponseInput {
                status: HumanTacticRunStatus::Error,
                kind: HumanTacticRunErrorKind::UnknownGoal,
                session_id: request.header.session_id.clone(),
                old_state_id: request.state_id.clone(),
                goal_id: request.goal_id.clone(),
                message: format!(
                    "unknown Human goal {} in state {}",
                    request.goal_id.wire(),
                    request.state_id.wire()
                ),
                diagnostic: None,
                machine_diagnostic: None,
                state_error: None,
                expected_hash: None,
                actual_hash: None,
                span: None,
                suggestions: Vec::new(),
                messages: Vec::new(),
            },
        )));
    };
    let before_goal = match entry.state.goal(machine_goal_id) {
        Ok(goal) => goal,
        Err(diagnostic) => {
            return Err(Box::new(human_tactic_run_machine_error_response(
                request.header.session_id.clone(),
                request.state_id.clone(),
                request.goal_id.clone(),
                None,
                npa_frontend::Span::empty(session.document.file_id),
                diagnostic,
            )));
        }
    };
    let Some(current_source_interface) = session.source_interface.clone() else {
        return Err(Box::new(human_tactic_run_error_response(
            HumanTacticRunErrorResponseInput {
                status: HumanTacticRunStatus::Error,
                kind: HumanTacticRunErrorKind::StateValidation,
                session_id: request.header.session_id.clone(),
                old_state_id: request.state_id.clone(),
                goal_id: request.goal_id.clone(),
                message: "Human tactic run requires a collected source interface for the session"
                    .to_owned(),
                diagnostic: None,
                machine_diagnostic: None,
                state_error: None,
                expected_hash: None,
                actual_hash: None,
                span: None,
                suggestions: Vec::new(),
                messages: Vec::new(),
            },
        )));
    };
    Ok(HumanTacticRunContext {
        session_id: request.header.session_id.clone(),
        parent_state_id: entry.state_id.clone(),
        human_goal_id: request.goal_id.clone(),
        machine_goal_id,
        parent_state: entry.state.clone(),
        parent_document_version: entry.document_version,
        parent_goal_mappings: entry.goal_mappings.clone(),
        before_goal,
        parent_source_span: entry.source_span,
        file_id: session.document.file_id,
        current_source_interface,
        imported_source_interfaces: session.active_imported_source_interfaces.clone(),
        options: session.document.options.clone(),
    })
}

#[derive(Clone, Debug)]
struct HumanTacticRunExecutionOk {
    state: npa_tactic::MachineProofState,
    deltas: Vec<npa_tactic::MachineProofDelta>,
}

fn human_tactic_run_execute(
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    tactic: &npa_frontend::HumanTacticSyntax,
    current_source_interface: &npa_frontend::HumanSourceInterface,
    imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
    options: HumanApiCompileOptions,
    budget: npa_tactic::TacticBudget,
) -> Result<HumanTacticRunExecutionOk, HumanTacticScriptError> {
    match tactic {
        npa_frontend::HumanTacticSyntax::Intro { name, .. } => {
            let ok = run_human_intro_tactic(HumanIntroTacticRequest {
                state,
                goal_id,
                name,
                budget,
            })
            .map_err(human_script_intro_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
        npa_frontend::HumanTacticSyntax::Exact { term, .. } => {
            let ok = run_human_exact_tactic(HumanExactTacticRequest {
                state,
                goal_id,
                term,
                current_source_interface,
                imported_source_interfaces,
                options,
            })
            .map_err(human_script_term_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
        npa_frontend::HumanTacticSyntax::Apply { term, .. } => {
            let ok = run_human_apply_tactic(HumanApplyTacticRequest {
                state,
                goal_id,
                term,
                current_source_interface,
                imported_source_interfaces,
                budget,
            })
            .map_err(human_script_apply_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
        npa_frontend::HumanTacticSyntax::Rewrite { rules, span } => {
            let ok = run_human_rewrite_tactic(HumanRewriteTacticRequest {
                state,
                goal_id,
                rules,
                span: *span,
                current_source_interface,
                imported_source_interfaces,
                budget,
            })
            .map_err(human_script_rewrite_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: ok.deltas,
            })
        }
        npa_frontend::HumanTacticSyntax::SimpLite { span } => {
            let ok = run_human_simp_lite_tactic(HumanSimpLiteTacticRequest {
                state,
                goal_id,
                span: *span,
                budget,
            })
            .map_err(human_script_simp_lite_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
        npa_frontend::HumanTacticSyntax::Smt { lemmas, span } => {
            let ok = run_human_smt_tactic(HumanSmtTacticRequest {
                state,
                goal_id,
                lemmas,
                span: *span,
                current_source_interface,
                imported_source_interfaces,
                budget,
            })
            .map_err(human_script_apply_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
        npa_frontend::HumanTacticSyntax::FiniteDecide { span } => run_human_solver_tactic(
            state,
            goal_id,
            npa_tactic::MachineTactic::FiniteDecide { goal_id },
            *span,
            budget,
        ),
        npa_frontend::HumanTacticSyntax::Omega { span } => run_human_solver_tactic(
            state,
            goal_id,
            npa_tactic::MachineTactic::Omega { goal_id },
            *span,
            budget,
        ),
        npa_frontend::HumanTacticSyntax::RingNf { span } => run_human_solver_tactic(
            state,
            goal_id,
            npa_tactic::MachineTactic::Ring { goal_id },
            *span,
            budget,
        ),
        npa_frontend::HumanTacticSyntax::Bitblast { span } => run_human_solver_tactic(
            state,
            goal_id,
            npa_tactic::MachineTactic::Bitblast { goal_id },
            *span,
            budget,
        ),
        npa_frontend::HumanTacticSyntax::Induction { name, span } => {
            let ok = run_human_induction_tactic(HumanInductionTacticRequest {
                state,
                goal_id,
                name,
                span: *span,
                budget,
            })
            .map_err(human_script_induction_error)?;
            Ok(HumanTacticRunExecutionOk {
                state: ok.state,
                deltas: vec![ok.delta],
            })
        }
    }
}

fn human_parse_single_tactic(
    file_id: npa_frontend::FileId,
    tactic_text: &str,
    imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
) -> Result<npa_frontend::HumanTacticSyntax, npa_frontend::HumanDiagnostic> {
    if tactic_text.trim().is_empty() {
        let len = u32::try_from(tactic_text.len()).unwrap_or(u32::MAX);
        return Err(npa_frontend::HumanDiagnostic::parse(
            npa_frontend::Span::new(file_id, 0, len),
            "expected one Human tactic",
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticParse));
    }

    let prefix = "theorem TacticRunDummy : Prop := by\n";
    let source = format!("{prefix}{tactic_text}");
    let parsed = npa_frontend::parse_human_module_with_source_interfaces(
        file_id,
        &source,
        imported_source_interfaces,
    )?;
    let Some(npa_frontend::HumanItem::Theorem(decl)) = parsed.items.first() else {
        return Err(npa_frontend::HumanDiagnostic::parse(
            npa_frontend::Span::new(file_id, 0, source.len() as u32),
            "expected one Human tactic",
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticParse));
    };
    let npa_frontend::HumanDeclValue::ProofBlock(block) = &decl.value else {
        return Err(npa_frontend::HumanDiagnostic::parse(
            decl.value.span(),
            "expected tactic proof block",
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticParse));
    };
    if parsed.items.len() != 1 || block.script.tactics.len() != 1 {
        return Err(npa_frontend::HumanDiagnostic::parse(
            block.script.span,
            "Human /tactic/run accepts exactly one tactic",
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticParse));
    }
    Ok(block.script.tactics[0].clone())
}

struct HumanTacticRunErrorResponseInput {
    status: HumanTacticRunStatus,
    kind: HumanTacticRunErrorKind,
    session_id: crate::HumanSessionId,
    old_state_id: crate::HumanStateId,
    goal_id: crate::HumanGoalId,
    message: String,
    diagnostic: Option<npa_frontend::HumanDiagnostic>,
    machine_diagnostic: Option<npa_tactic::MachineTacticDiagnostic>,
    state_error: Option<HumanStateApiError>,
    expected_hash: Option<npa_cert::Hash>,
    actual_hash: Option<npa_cert::Hash>,
    span: Option<npa_frontend::Span>,
    suggestions: Vec<HumanTacticRunSuggestion>,
    messages: Vec<npa_frontend::HumanDiagnostic>,
}

fn human_tactic_run_error_response(
    input: HumanTacticRunErrorResponseInput,
) -> HumanTacticRunResponse {
    HumanTacticRunResponse {
        status: input.status,
        session_id: input.session_id,
        parent_state_id: input.old_state_id.clone(),
        new_state_id: None,
        selected_goal: Some(input.goal_id.clone()),
        closed_goals: Vec::new(),
        new_goals: Vec::new(),
        proof_deltas: Vec::new(),
        messages: input.messages,
        error: Some(HumanTacticRunErrorReport {
            kind: input.kind,
            old_state_id: input.old_state_id,
            goal_id: input.goal_id,
            message: input.message,
            diagnostic: input.diagnostic,
            machine_diagnostic: input.machine_diagnostic.map(Box::new),
            state_error: input.state_error.map(Box::new),
            expected_hash: input.expected_hash,
            actual_hash: input.actual_hash,
            span: input.span,
            suggestions: input.suggestions,
        }),
    }
}

fn human_tactic_run_state_error_response(
    session_id: crate::HumanSessionId,
    old_state_id: crate::HumanStateId,
    goal_id: crate::HumanGoalId,
    error: HumanStateApiError,
) -> HumanTacticRunResponse {
    human_tactic_run_error_response(HumanTacticRunErrorResponseInput {
        status: HumanTacticRunStatus::Error,
        kind: HumanTacticRunErrorKind::StateValidation,
        session_id,
        old_state_id,
        goal_id,
        message: format!("Human tactic run state validation failed: {error:?}"),
        diagnostic: None,
        machine_diagnostic: None,
        state_error: Some(error),
        expected_hash: None,
        actual_hash: None,
        span: None,
        suggestions: Vec::new(),
        messages: Vec::new(),
    })
}

fn human_tactic_run_record_error_response(
    session_id: crate::HumanSessionId,
    old_state_id: crate::HumanStateId,
    goal_id: crate::HumanGoalId,
    error: HumanTacticStateRecordError,
) -> HumanTacticRunResponse {
    human_tactic_run_error_response(HumanTacticRunErrorResponseInput {
        status: HumanTacticRunStatus::Error,
        kind: HumanTacticRunErrorKind::StateRecord,
        session_id,
        old_state_id,
        goal_id,
        message: format!("Human tactic run could not record the transition state: {error:?}"),
        diagnostic: None,
        machine_diagnostic: None,
        state_error: None,
        expected_hash: None,
        actual_hash: None,
        span: None,
        suggestions: Vec::new(),
        messages: Vec::new(),
    })
}

fn human_tactic_run_human_error_response(
    session_id: crate::HumanSessionId,
    old_state_id: crate::HumanStateId,
    goal_id: crate::HumanGoalId,
    goal: Option<&npa_tactic::MachineGoal>,
    diagnostic: npa_frontend::HumanDiagnostic,
) -> HumanTacticRunResponse {
    let (status, kind) = human_tactic_run_human_error_status(&diagnostic);
    let suggestions = goal.map(human_tactic_run_suggestions).unwrap_or_default();
    human_tactic_run_error_response(HumanTacticRunErrorResponseInput {
        status,
        kind,
        session_id,
        old_state_id,
        goal_id,
        message: diagnostic.message.clone(),
        diagnostic: Some(diagnostic.clone()),
        machine_diagnostic: None,
        state_error: None,
        expected_hash: None,
        actual_hash: None,
        span: Some(diagnostic.primary_span),
        suggestions,
        messages: vec![diagnostic],
    })
}

fn human_tactic_run_machine_error_response(
    session_id: crate::HumanSessionId,
    old_state_id: crate::HumanStateId,
    goal_id: crate::HumanGoalId,
    goal: Option<&npa_tactic::MachineGoal>,
    span: npa_frontend::Span,
    diagnostic: npa_tactic::MachineTacticDiagnostic,
) -> HumanTacticRunResponse {
    let (status, kind) = human_tactic_run_machine_error_status(&diagnostic);
    let expected_hash = diagnostic.expected_hash.as_deref().copied();
    let actual_hash = diagnostic.actual_hash.as_deref().copied();
    let suggestions = goal.map(human_tactic_run_suggestions).unwrap_or_default();
    human_tactic_run_error_response(HumanTacticRunErrorResponseInput {
        status,
        kind,
        session_id,
        old_state_id,
        goal_id,
        message: diagnostic.message.to_string(),
        diagnostic: None,
        machine_diagnostic: Some(diagnostic),
        state_error: None,
        expected_hash,
        actual_hash,
        span: Some(span),
        suggestions,
        messages: Vec::new(),
    })
}

fn human_tactic_run_human_error_status(
    diagnostic: &npa_frontend::HumanDiagnostic,
) -> (HumanTacticRunStatus, HumanTacticRunErrorKind) {
    match &diagnostic.kind {
        npa_frontend::HumanDiagnosticKind::ParseError => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::ParseError,
        ),
        npa_frontend::HumanDiagnosticKind::ExpectedFunctionType => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::ExpectedPiType,
        ),
        npa_frontend::HumanDiagnosticKind::TypeMismatch => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::TypeMismatch,
        ),
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        | npa_frontend::HumanDiagnosticKind::UnsupportedSyntax => (
            HumanTacticRunStatus::Unsafe,
            HumanTacticRunErrorKind::Unsafe,
        ),
        _ => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::TacticExecution,
        ),
    }
}

fn human_tactic_run_machine_error_status(
    diagnostic: &npa_tactic::MachineTacticDiagnostic,
) -> (HumanTacticRunStatus, HumanTacticRunErrorKind) {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::TacticFuelExhausted { .. } => (
            HumanTacticRunStatus::Timeout,
            HumanTacticRunErrorKind::Timeout,
        ),
        npa_tactic::MachineTacticDiagnosticKind::UnsupportedMachineTactic
        | npa_tactic::MachineTacticDiagnosticKind::TacticPrimitiveUnavailable
        | npa_tactic::MachineTacticDiagnosticKind::InvalidMachineTactic => (
            HumanTacticRunStatus::Unsafe,
            HumanTacticRunErrorKind::Unsafe,
        ),
        npa_tactic::MachineTacticDiagnosticKind::ExpectedFunctionType
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedPiTarget => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::ExpectedPiType,
        ),
        npa_tactic::MachineTacticDiagnosticKind::TypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::ProofExprTypeMismatch => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::TypeMismatch,
        ),
        _ => (
            HumanTacticRunStatus::Error,
            HumanTacticRunErrorKind::TacticExecution,
        ),
    }
}

fn human_tactic_run_suggestions(goal: &npa_tactic::MachineGoal) -> Vec<HumanTacticRunSuggestion> {
    let mut suggestions = Vec::new();
    if let Some(local) = goal
        .context
        .iter()
        .rev()
        .find(|local| local.ty == goal.target)
    {
        suggestions.push(HumanTacticRunSuggestion {
            kind: HumanTacticRunSuggestionKind::TryTactic,
            tactic: format!("exact {}", local.name),
        });
    }

    let local_names = goal
        .context
        .iter()
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    if let Some((lhs, rhs)) = human_eq_app_sides(&goal.target) {
        if lhs == rhs {
            suggestions.push(HumanTacticRunSuggestion {
                kind: HumanTacticRunSuggestionKind::TryTactic,
                tactic: format!(
                    "exact Eq.refl {}",
                    human_render_core_expr(lhs, &local_names)
                ),
            });
            suggestions.push(HumanTacticRunSuggestion {
                kind: HumanTacticRunSuggestionKind::TryTactic,
                tactic: "simp-lite".to_owned(),
            });
        }
    }
    suggestions
}

fn human_open_goal_ids(entry: &HumanProofStateEntry) -> Vec<crate::HumanGoalId> {
    entry
        .state
        .open_goals
        .iter()
        .filter_map(|goal_id| entry.human_goal_for_machine_goal(*goal_id).cloned())
        .collect()
}

fn human_display_goal_text_for_entry(
    header: &HumanStateRequestHeader,
    entry: &HumanProofStateEntry,
    goal_id: &crate::HumanGoalId,
    mode: HumanDisplayMode,
    context_options: HumanDisplayContextOptions,
) -> Result<String, HumanDisplayError> {
    let (structured, machine_goal) = human_display_goal_data(header, entry, goal_id)?;
    Ok(match mode {
        HumanDisplayMode::Pretty | HumanDisplayMode::Explicit | HumanDisplayMode::Core => {
            let (context, _, _) =
                human_display_context_text(&structured, &machine_goal, mode, context_options);
            let target = human_display_target_text(&structured, &machine_goal, mode);
            if context.is_empty() {
                format!("|- {target}")
            } else {
                format!("{context}\n|- {target}")
            }
        }
        HumanDisplayMode::Json => human_display_goal_json(&structured),
    })
}

fn human_display_goal_data(
    header: &HumanStateRequestHeader,
    entry: &HumanProofStateEntry,
    goal_id: &crate::HumanGoalId,
) -> Result<(StructuredGoal, npa_tactic::MachineGoal), HumanDisplayError> {
    let machine_goal_id = entry.machine_goal_for_human_goal(goal_id).ok_or_else(|| {
        HumanDisplayError::UnknownGoal {
            session_id: header.session_id.clone(),
            state_id: entry.state_id.clone(),
            goal_id: goal_id.clone(),
        }
    })?;
    let machine_goal =
        entry
            .state
            .goal(machine_goal_id)
            .map_err(|diagnostic| HumanDisplayError::MachineGoal {
                session_id: header.session_id.clone(),
                state_id: entry.state_id.clone(),
                goal_id: goal_id.clone(),
                diagnostic: Box::new(diagnostic),
            })?;
    let structured =
        materialize_human_structured_goal(entry, machine_goal_id).map_err(|error| {
            HumanDisplayError::State(human_state_materialization_error(
                header,
                &entry.state_id,
                error,
            ))
        })?;
    Ok((structured, machine_goal))
}

fn human_display_context_text(
    structured: &StructuredGoal,
    machine_goal: &npa_tactic::MachineGoal,
    mode: HumanDisplayMode,
    options: HumanDisplayContextOptions,
) -> (String, usize, usize) {
    if mode == HumanDisplayMode::Json {
        return (
            human_display_context_json(&structured.context),
            structured.context.len(),
            0,
        );
    }

    let projection = human_display_context_projection(structured, options);
    let all_lines = match mode {
        HumanDisplayMode::Pretty => structured
            .context
            .iter()
            .map(|hypothesis| {
                human_display_structured_hypothesis_text(hypothesis, options.fold_local_def_values)
            })
            .collect(),
        HumanDisplayMode::Explicit => human_display_machine_context_lines(machine_goal, false),
        HumanDisplayMode::Core => human_display_machine_context_lines(machine_goal, true),
        HumanDisplayMode::Json => unreachable!("json mode returned above"),
    };
    let mut lines = Vec::new();
    if projection.folded_count > 0 {
        let shown_kind = if options.relevant_first {
            "relevant hypotheses"
        } else {
            "hypotheses"
        };
        lines.push(format!(
            "Context contains {} hypotheses. Showing {} {}.",
            structured.context.len(),
            projection.indices.len(),
            shown_kind
        ));
    }
    for index in &projection.indices {
        if let Some(line) = all_lines.get(*index) {
            lines.push(line.clone());
        }
    }
    (
        lines.join("\n"),
        projection.indices.len(),
        projection.folded_count,
    )
}

fn human_display_structured_hypothesis_text(
    hypothesis: &StructuredHypothesis,
    fold_local_def_value: bool,
) -> String {
    if fold_local_def_value && hypothesis.value.is_some() {
        format!("{} : {} := ...", hypothesis.name, hypothesis.ty.pretty)
    } else {
        hypothesis.pretty.clone()
    }
}

struct HumanDisplayContextProjection {
    indices: Vec<usize>,
    folded_count: usize,
}

fn human_display_context_projection(
    goal: &StructuredGoal,
    options: HumanDisplayContextOptions,
) -> HumanDisplayContextProjection {
    let mut indices = if options.relevant_first {
        let relevant = human_display_relevant_local_ids(goal);
        let mut ordered = goal
            .context
            .iter()
            .enumerate()
            .filter_map(|(index, hypothesis)| {
                relevant.contains(&hypothesis.local_id).then_some(index)
            })
            .collect::<Vec<_>>();
        ordered.extend(
            goal.context
                .iter()
                .enumerate()
                .filter_map(|(index, hypothesis)| {
                    (!relevant.contains(&hypothesis.local_id)).then_some(index)
                }),
        );
        ordered
    } else {
        (0..goal.context.len()).collect()
    };
    let folded_count = options
        .max_context_items
        .filter(|max| indices.len() > *max)
        .map_or(0, |max| {
            let folded = indices.len() - max;
            indices.truncate(max);
            folded
        });
    HumanDisplayContextProjection {
        indices,
        folded_count,
    }
}

fn human_display_relevant_local_ids(goal: &StructuredGoal) -> BTreeSet<LocalId> {
    let mut relevant = goal
        .target
        .free_locals
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut changed = true;
    while changed {
        changed = false;
        for hypothesis in &goal.context {
            if relevant.contains(&hypothesis.local_id) {
                for dependency in &hypothesis.depends_on {
                    changed |= relevant.insert(*dependency);
                }
            }
        }
    }
    relevant
}

fn human_display_machine_context_lines(
    goal: &npa_tactic::MachineGoal,
    core_mode: bool,
) -> Vec<String> {
    let mut local_names = Vec::with_capacity(goal.context.len());
    let mut lines = Vec::with_capacity(goal.context.len());
    for local in &goal.context {
        let ty = if core_mode {
            render_kernel_core_expr(&local.ty)
        } else {
            human_render_core_expr(&local.ty, &local_names)
        };
        let value = local.value.as_ref().map(|value| {
            if core_mode {
                render_kernel_core_expr(value)
            } else {
                human_render_core_expr(value, &local_names)
            }
        });
        lines.push(human_state_goal_summary_hypothesis_pretty(
            &local.name,
            &ty,
            value.as_deref(),
        ));
        local_names.push(local.name.clone());
    }
    lines
}

fn human_display_target_text(
    structured: &StructuredGoal,
    machine_goal: &npa_tactic::MachineGoal,
    mode: HumanDisplayMode,
) -> String {
    match mode {
        HumanDisplayMode::Pretty => structured.target.pretty.clone(),
        HumanDisplayMode::Explicit => {
            let local_names = machine_goal
                .context
                .iter()
                .map(|local| local.name.clone())
                .collect::<Vec<_>>();
            human_render_core_expr(&machine_goal.target, &local_names)
        }
        HumanDisplayMode::Core => render_kernel_core_expr(&machine_goal.target),
        HumanDisplayMode::Json => human_display_structured_expr_json(&structured.target),
    }
}

fn human_display_closed_goal_diff_item(
    header: &HumanStateRequestHeader,
    before: &HumanProofStateEntry,
    goal_id: &crate::HumanGoalId,
    mode: HumanDisplayMode,
) -> Result<HumanGoalDisplayDiffItem, HumanDisplayError> {
    let before_text = human_display_goal_text_for_entry(
        header,
        before,
        goal_id,
        mode,
        HumanDisplayContextOptions::default(),
    )?;
    let text = match mode {
        HumanDisplayMode::Json => format!(
            "{{\"kind\":\"goal_closed\",\"old_goal\":{},\"before\":{}}}",
            human_json_string(goal_id.wire()),
            human_json_string(&before_text)
        ),
        _ => format!("before:\n{before_text}\n\nafter:\nclosed"),
    };
    Ok(HumanGoalDisplayDiffItem {
        kind: HumanGoalDisplayDiffKind::GoalClosed,
        old_goal: Some(goal_id.clone()),
        new_goals: Vec::new(),
        text,
    })
}

fn human_display_added_goal_diff_item(
    header: &HumanStateRequestHeader,
    after: &HumanProofStateEntry,
    goal_id: &crate::HumanGoalId,
    mode: HumanDisplayMode,
) -> Result<HumanGoalDisplayDiffItem, HumanDisplayError> {
    let after_text = human_display_goal_text_for_entry(
        header,
        after,
        goal_id,
        mode,
        HumanDisplayContextOptions::default(),
    )?;
    let text = match mode {
        HumanDisplayMode::Json => format!(
            "{{\"kind\":\"goal_added\",\"new_goal\":{},\"after\":{}}}",
            human_json_string(goal_id.wire()),
            human_json_string(&after_text)
        ),
        _ => format!("added:\n{after_text}"),
    };
    Ok(HumanGoalDisplayDiffItem {
        kind: HumanGoalDisplayDiffKind::GoalAdded,
        old_goal: None,
        new_goals: vec![goal_id.clone()],
        text,
    })
}

fn human_display_replaced_goal_diff_item(
    header: &HumanStateRequestHeader,
    before: &HumanProofStateEntry,
    after: &HumanProofStateEntry,
    old_goal: &crate::HumanGoalId,
    new_goals: &[crate::HumanGoalId],
    mode: HumanDisplayMode,
) -> Result<HumanGoalDisplayDiffItem, HumanDisplayError> {
    let before_text = human_display_goal_text_for_entry(
        header,
        before,
        old_goal,
        mode,
        HumanDisplayContextOptions::default(),
    )?;
    let after_texts = new_goals
        .iter()
        .map(|goal_id| {
            human_display_goal_text_for_entry(
                header,
                after,
                goal_id,
                mode,
                HumanDisplayContextOptions::default(),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let text = match mode {
        HumanDisplayMode::Json => format!(
            "{{\"kind\":\"goal_replaced\",\"old_goal\":{},\"new_goals\":{},\"before\":{},\"after\":{}}}",
            human_json_string(old_goal.wire()),
            human_json_string_array(new_goals.iter().map(|goal_id| goal_id.wire())),
            human_json_string(&before_text),
            human_json_string_array(after_texts.iter().map(String::as_str))
        ),
        _ => format!(
            "before:\n{}\n\nafter:\n{}",
            before_text,
            after_texts.join("\n\n")
        ),
    };
    Ok(HumanGoalDisplayDiffItem {
        kind: HumanGoalDisplayDiffKind::GoalReplaced,
        old_goal: Some(old_goal.clone()),
        new_goals: new_goals.to_vec(),
        text,
    })
}

fn human_display_diff_json(items: &[HumanGoalDisplayDiffItem]) -> String {
    let entries = items
        .iter()
        .map(|item| {
            let old_goal = item
                .old_goal
                .as_ref()
                .map(|goal_id| human_json_string(goal_id.wire()))
                .unwrap_or_else(|| "null".to_owned());
            format!(
                "{{\"kind\":{},\"old_goal\":{},\"new_goals\":{},\"text\":{}}}",
                human_json_string(human_display_diff_kind_wire(item.kind)),
                old_goal,
                human_json_string_array(item.new_goals.iter().map(|goal_id| goal_id.wire())),
                human_json_string(&item.text)
            )
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(","))
}

fn human_display_diff_kind_wire(kind: HumanGoalDisplayDiffKind) -> &'static str {
    match kind {
        HumanGoalDisplayDiffKind::GoalReplaced => "goal_replaced",
        HumanGoalDisplayDiffKind::GoalClosed => "goal_closed",
        HumanGoalDisplayDiffKind::GoalAdded => "goal_added",
    }
}

fn human_display_goal_json(goal: &StructuredGoal) -> String {
    let context = goal
        .context
        .iter()
        .map(human_display_hypothesis_json)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"goal_id\":{},\"machine_goal_id\":{},\"meta_id\":{},\"name\":{},\"context_hash\":{},\"context\":[{}],\"target\":{},\"target_core_hash\":{},\"status\":{},\"pretty\":{}}}",
        human_json_string(goal.goal_id.wire()),
        goal.machine_goal_id.0,
        goal.meta_id.0,
        goal.name
            .as_deref()
            .map(human_json_string)
            .unwrap_or_else(|| "null".to_owned()),
        human_json_string(&crate::format_hash_string(&goal.context_hash)),
        context,
        human_display_structured_expr_json(&goal.target),
        human_json_string(&crate::format_hash_string(&goal.target_core_hash)),
        human_json_string(match goal.status {
            StructuredGoalStatus::Open => "open",
        }),
        human_json_string(&goal.pretty)
    )
}

fn human_display_context_json(context: &[StructuredHypothesis]) -> String {
    let entries = context
        .iter()
        .map(human_display_hypothesis_json)
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(","))
}

fn human_display_hypothesis_json(hypothesis: &StructuredHypothesis) -> String {
    format!(
        "{{\"local_id\":{},\"name\":{},\"ty\":{},\"value\":{},\"is_local_def\":{},\"is_implicit\":{},\"depends_on\":{},\"binder_index\":{},\"pretty\":{}}}",
        hypothesis.local_id.0,
        human_json_string(&hypothesis.name),
        human_display_structured_expr_json(&hypothesis.ty),
        hypothesis
            .value
            .as_ref()
            .map(human_display_structured_expr_json)
            .unwrap_or_else(|| "null".to_owned()),
        hypothesis.is_local_def,
        hypothesis.is_implicit,
        human_json_u32_array(hypothesis.depends_on.iter().map(|local_id| local_id.0)),
        hypothesis.binder_index,
        human_json_string(&hypothesis.pretty)
    )
}

fn human_display_structured_expr_json(expr: &StructuredExpr) -> String {
    format!(
        "{{\"core_hash\":{},\"head\":{},\"constants\":{},\"free_locals\":{},\"size\":{},\"pretty\":{}}}",
        human_json_string(&crate::format_hash_string(&expr.core_hash)),
        expr.head
            .as_ref()
            .map(|name| human_json_string(&name.as_dotted()))
            .unwrap_or_else(|| "null".to_owned()),
        human_json_string_array_owned(expr.constants.iter().map(npa_cert::Name::as_dotted)),
        human_json_u32_array(expr.free_locals.iter().map(|local_id| local_id.0)),
        expr.size,
        human_json_string(&expr.pretty)
    )
}

fn human_display_structured_expr_core_summary(expr: &StructuredExpr) -> String {
    let head = expr
        .head
        .as_ref()
        .map(npa_cert::Name::as_dotted)
        .unwrap_or_else(|| "none".to_owned());
    let constants = expr
        .constants
        .iter()
        .map(npa_cert::Name::as_dotted)
        .collect::<Vec<_>>()
        .join(", ");
    let free_locals = expr
        .free_locals
        .iter()
        .map(|local_id| format!("l{}", local_id.0))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "core_hash: {}\nhead: {head}\nconstants: [{constants}]\nfree_locals: [{free_locals}]\nsize: {}",
        crate::format_hash_string(&expr.core_hash),
        expr.size
    )
}

fn human_json_string_array<'a>(values: impl Iterator<Item = &'a str>) -> String {
    let values = values.map(human_json_string).collect::<Vec<_>>();
    format!("[{}]", values.join(","))
}

fn human_json_string_array_owned(values: impl Iterator<Item = String>) -> String {
    let values = values
        .map(|value| human_json_string(&value))
        .collect::<Vec<_>>();
    format!("[{}]", values.join(","))
}

fn human_json_u32_array(values: impl Iterator<Item = u32>) -> String {
    let values = values.map(|value| value.to_string()).collect::<Vec<_>>();
    format!("[{}]", values.join(","))
}

fn human_json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn materialize_human_structured_goal(
    entry: &HumanProofStateEntry,
    machine_goal_id: npa_tactic::GoalId,
) -> Result<StructuredGoal, HumanStructuredProofStateError> {
    let human_goal_id = entry
        .human_goal_for_machine_goal(machine_goal_id)
        .cloned()
        .ok_or_else(|| HumanStructuredProofStateError::MissingGoalMapping {
            state_id: entry.state_id.clone(),
            machine_goal_id,
        })?;
    let goal = entry.state.goal(machine_goal_id).map_err(|diagnostic| {
        HumanStructuredProofStateError::MachineGoal {
            state_id: entry.state_id.clone(),
            machine_goal_id,
            diagnostic: Box::new(diagnostic),
        }
    })?;

    let mut local_names = Vec::with_capacity(goal.context.len());
    let mut context = Vec::with_capacity(goal.context.len());
    for (index, local) in goal.context.iter().enumerate() {
        let hypothesis =
            materialize_human_structured_hypothesis(entry, index, local, &local_names)?;
        local_names.push(local.name.clone());
        context.push(hypothesis);
    }
    let target = materialize_human_structured_expr(entry, &goal.target, &local_names)?;
    let target_core_hash = target.core_hash;
    let pretty = human_structured_goal_pretty(&context, &target);

    Ok(StructuredGoal {
        goal_id: human_goal_id,
        machine_goal_id: goal.id,
        meta_id: goal.meta_id,
        name: Some(format!("?g{}", goal.id.0)),
        context_hash: goal.context_hash,
        context,
        target,
        target_core_hash,
        source_span: entry.source_span,
        status: StructuredGoalStatus::Open,
        pretty,
    })
}

fn materialize_human_structured_hypothesis(
    entry: &HumanProofStateEntry,
    index: usize,
    local: &npa_tactic::MachineLocalDecl,
    local_names: &[String],
) -> Result<StructuredHypothesis, HumanStructuredProofStateError> {
    let local_id = LocalId(u32::try_from(index).map_err(|_| {
        HumanStructuredProofStateError::LocalIndexExhausted {
            state_id: entry.state_id.clone(),
        }
    })?);
    let ty = materialize_human_structured_expr(entry, &local.ty, local_names)?;
    let value = local
        .value
        .as_ref()
        .map(|value| materialize_human_structured_expr(entry, value, local_names))
        .transpose()?;
    let depends_on = human_structured_hypothesis_dependencies(&ty, value.as_ref());
    let binder_index =
        u32::try_from(index).map_err(|_| HumanStructuredProofStateError::LocalIndexExhausted {
            state_id: entry.state_id.clone(),
        })?;
    let pretty = human_structured_hypothesis_pretty(&local.name, &ty, value.as_ref());

    Ok(StructuredHypothesis {
        local_id,
        name: local.name.clone(),
        ty,
        value,
        is_local_def: local.value.is_some(),
        is_implicit: false,
        depends_on,
        binder_index,
        pretty,
    })
}

fn materialize_human_structured_expr(
    entry: &HumanProofStateEntry,
    expr: &Expr,
    local_names: &[String],
) -> Result<StructuredExpr, HumanStructuredProofStateError> {
    let metadata = core_expr_metadata(expr, local_names.len()).map_err(|error| {
        HumanStructuredProofStateError::ExpressionMetadata {
            state_id: entry.state_id.clone(),
            error: Box::new(error),
        }
    })?;
    Ok(StructuredExpr {
        core_hash: metadata.core_hash,
        head: metadata.head,
        constants: metadata.constants,
        free_locals: metadata.free_locals,
        size: metadata.size,
        pretty: human_structured_expr_pretty(expr, local_names),
    })
}

fn human_structured_hypothesis_dependencies(
    ty: &StructuredExpr,
    value: Option<&StructuredExpr>,
) -> Vec<LocalId> {
    let mut dependencies = BTreeSet::new();
    dependencies.extend(ty.free_locals.iter().copied());
    if let Some(value) = value {
        dependencies.extend(value.free_locals.iter().copied());
    }
    dependencies.into_iter().collect()
}

fn human_structured_hypothesis_pretty(
    name: &str,
    ty: &StructuredExpr,
    value: Option<&StructuredExpr>,
) -> String {
    match value {
        Some(value) => format!("{name} : {} := {}", ty.pretty, value.pretty),
        None => format!("{name} : {}", ty.pretty),
    }
}

fn human_structured_goal_pretty(
    context: &[StructuredHypothesis],
    target: &StructuredExpr,
) -> String {
    let mut lines = context
        .iter()
        .map(|hypothesis| hypothesis.pretty.clone())
        .collect::<Vec<_>>();
    lines.push(format!("|- {}", target.pretty));
    lines.join("\n")
}

fn human_proof_state_start_error(
    error: HumanProofStateStoreMutationError,
) -> HumanProofStateStartError {
    match error {
        HumanProofStateStoreMutationError::IdSpaceExhausted => {
            HumanProofStateStartError::IdSpaceExhausted
        }
        HumanProofStateStoreMutationError::UnknownParentState => {
            unreachable!("initial proof state insertion has no parent state")
        }
    }
}

fn human_tactic_state_record_error(
    error: HumanProofStateStoreMutationError,
    session_id: crate::HumanSessionId,
    parent_state_id: crate::HumanStateId,
) -> HumanTacticStateRecordError {
    match error {
        HumanProofStateStoreMutationError::IdSpaceExhausted => {
            HumanTacticStateRecordError::IdSpaceExhausted
        }
        HumanProofStateStoreMutationError::UnknownParentState => {
            HumanTacticStateRecordError::UnknownParentState {
                session_id,
                parent_state_id,
            }
        }
    }
}

/// Replace the current Human document snapshot for an open Human session.
///
/// This is the library equivalent of Phase 5 Human `POST /documents/update`.
/// The document id remains stable and the document version increases
/// monotonically. Imports and source interfaces are always supplied explicitly
/// by the request; this function performs no filesystem or network lookup.
pub fn update_human_document(
    store: &mut HumanProofSessionStore,
    request: HumanDocumentUpdateRequest<'_, '_>,
) -> Result<HumanDocumentUpdateOk, HumanDocumentUpdateError> {
    let (document_id, current_version, prior_incremental_cache, prior_source_interface) = {
        let session = store.session(&request.session_id).ok_or_else(|| {
            HumanDocumentUpdateError::UnknownSession {
                session_id: request.session_id.clone(),
            }
        })?;
        (
            session.document.document_id.clone(),
            session.document.document_version,
            session.incremental_cache.clone(),
            session.source_interface.clone(),
        )
    };
    let next_version = current_version.next().ok_or_else(|| {
        HumanDocumentUpdateError::DocumentVersionOverflow {
            session_id: request.session_id.clone(),
            document_id: document_id.clone(),
            current: current_version,
        }
    })?;
    let document = HumanDocumentSnapshot {
        document_id: document_id.clone(),
        document_version: next_version,
        current_module: request.current_module,
        file_id: request.current_source.file_id,
        source: request.current_source.source.to_owned(),
        verified_modules: request.verified_modules.to_vec(),
        imported_source_interfaces: request.imported_source_interfaces.to_vec(),
        options: request.options,
    };
    let mut collected = collect_human_session_document(&document);
    let messages = collected.messages.clone();
    let incremental_cache = build_human_document_incremental_cache(
        &document,
        &collected,
        Some(&prior_incremental_cache),
    );
    reuse_human_document_incremental_prefix(
        &mut collected,
        prior_source_interface.as_ref(),
        incremental_cache.reused_prefix_len,
    );
    let session = store
        .session_mut(&request.session_id)
        .expect("session was checked before document collection");
    session.status = HumanProofSessionStatus::Open;
    session.document = document;
    session.source_interface = collected.source_interface;
    session.active_imported_source_interfaces = collected.active_imports;
    session.incremental_cache = incremental_cache.clone();
    session.current_state_id = None;
    session.messages = collected.messages;

    Ok(HumanDocumentUpdateOk {
        session_id: request.session_id,
        document_id,
        document_version: next_version,
        status: HumanProofSessionStatus::Open,
        messages,
        incremental_cache,
    })
}

/// Validate the document identity/version portion common to future Human state requests.
///
/// P5H-01 does not materialize proof states yet; it only fixes the stale
/// document-version guard that `/state/*` APIs must apply before returning any
/// session state.
pub fn validate_human_state_request_document(
    store: &HumanProofSessionStore,
    request: HumanStateRequestHeader,
) -> Result<(), HumanStateRequestError> {
    let session = store.session(&request.session_id).ok_or_else(|| {
        HumanStateRequestError::UnknownSession {
            session_id: request.session_id.clone(),
        }
    })?;
    let current_document_id = &session.document.document_id;
    if current_document_id != &request.document_id {
        return Err(HumanStateRequestError::DocumentMismatch {
            session_id: request.session_id,
            requested: request.document_id,
            current: current_document_id.clone(),
        });
    }
    let current_version = session.document.document_version;
    if request.document_version < current_version {
        return Err(HumanStateRequestError::StaleDocumentVersion {
            session_id: request.session_id,
            document_id: request.document_id,
            requested: request.document_version,
            current: current_version,
        });
    }
    if request.document_version > current_version {
        return Err(HumanStateRequestError::FutureDocumentVersion {
            session_id: request.session_id,
            document_id: request.document_id,
            requested: request.document_version,
            current: current_version,
        });
    }
    Ok(())
}

pub fn start_human_proof(
    request: HumanStartProofRequest<'_, '_>,
) -> Result<HumanStartProofOk, HumanStartProofError> {
    let frontend_options = npa_frontend::HumanCompileOptions::from(&request.options);
    let frontend_imports: Vec<_> = request
        .verified_modules
        .iter()
        .map(npa_frontend::VerifiedImport::from)
        .collect();
    let prepared = npa_frontend::prepare_human_proof_start_core_with_source_interfaces(
        request.current_source.file_id,
        request.current_module.clone(),
        request.theorem_name,
        request.current_source.source,
        &frontend_imports,
        request.imported_source_interfaces,
        &frontend_options,
    )?;
    start_human_proof_from_prepared(prepared, request.verified_modules, request.options)
}

/// Build the Human theorem index for an already-checked Human proof state.
///
/// The index is intentionally Human-only: it reads direct visible verified imports
/// and the kernel-checked current declaration prefix already stored in the
/// `MachineProofState`. It does not read Human source metadata as a source of
/// truth and does not reuse or mutate the Machine `/machine/search/for_goal`
/// theorem index fingerprint.
pub fn build_human_theorem_index(
    state: &npa_tactic::MachineProofState,
) -> Result<HumanTheoremIndex, HumanTheoremIndexError> {
    let mut import_facts = BTreeMap::new();
    let mut import_entries = Vec::new();
    for import in state
        .env
        .imports
        .iter()
        .filter(|import| import.is_visible())
    {
        for export in import.verified_module().export_block() {
            let fact = human_import_export_fact(import, export)?;
            import_facts.insert(fact.name.clone(), fact.clone());
            import_entries.push(fact);
        }
    }

    let mut entries = Vec::new();
    for fact in &import_entries {
        entries.push(human_import_export_entry(fact, &import_facts)?);
    }

    let mut current_facts = BTreeMap::new();
    for checked in &state.env.checked_current_decls {
        let entry = human_checked_current_entry(
            &state.root.module,
            checked,
            &import_facts,
            &current_facts,
        )?;
        current_facts.insert(
            entry.name.clone(),
            HumanCurrentTheoremFact {
                module: entry.module.clone(),
                name: entry.name.clone(),
                source_index: checked.source_index(),
                decl_interface_hash: entry.decl_interface_hash,
                axiom_dependencies: entry.axiom_dependencies.clone(),
            },
        );
        entries.push(entry);
    }

    entries.sort_by_key(human_theorem_index_entry_sort_key);
    let fingerprint = human_theorem_index_fingerprint(&entries);
    Ok(HumanTheoremIndex {
        fingerprint,
        entries,
    })
}

pub fn search_human_theorems_by_name(
    store: &HumanProofSessionStore,
    request: HumanTheoremNameSearchRequest,
) -> Result<HumanTheoremSearchOk, HumanTheoremSearchError> {
    let (entry, index) = human_search_index_for_state(store, &request.header, &request.state_id)?;
    let query = request.query.trim().to_lowercase();
    let mut results = Vec::new();
    for theorem in &index.entries {
        let dotted = theorem.name.as_dotted();
        let dotted_lower = dotted.to_lowercase();
        if !query.is_empty() && !dotted_lower.contains(&query) {
            continue;
        }
        let score = if dotted_lower == query { 700 } else { 500 };
        if let Some(result) = human_search_result_from_entry(
            theorem,
            HumanTheoremSearchMode::Name,
            human_default_exact_tactic(theorem),
            vec![HumanTheoremMatchBinding {
                pattern: request.query.clone(),
                value: dotted,
            }],
            "name contains the search query",
            score,
            &request.options,
        ) {
            results.push(result);
        }
    }
    human_sort_truncate_search_results(&mut results, request.options.limit);

    Ok(HumanTheoremSearchOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        goal_id: None,
        theorem_index_fingerprint: index.fingerprint,
        results,
    })
}

pub fn search_human_theorems_by_type(
    store: &HumanProofSessionStore,
    request: HumanTheoremTypeSearchRequest,
) -> Result<HumanTheoremSearchOk, HumanTheoremSearchError> {
    let (entry, index) = human_search_index_for_state(store, &request.header, &request.state_id)?;
    let pattern = human_parse_search_pattern(&request.pattern).map_err(|message| {
        HumanTheoremSearchError::InvalidPattern {
            pattern: request.pattern.clone(),
            message,
        }
    })?;
    let mut results = Vec::new();
    for theorem in &index.entries {
        let (_, conclusion) = human_theorem_conclusion(&theorem.statement_core);
        let mut bindings = BTreeMap::new();
        if !human_search_pattern_matches(&pattern, conclusion, &mut bindings) {
            continue;
        }
        let display_binders = human_search_display_binder_names(&theorem.statement_core);
        let match_info = bindings
            .into_iter()
            .map(|(pattern, value)| HumanTheoremMatchBinding {
                pattern,
                value: human_render_core_expr(&value, &display_binders),
            })
            .collect::<Vec<_>>();
        if let Some(result) = human_search_result_from_entry(
            theorem,
            HumanTheoremSearchMode::ByType,
            human_default_exact_tactic(theorem),
            match_info,
            "the theorem conclusion matches the type pattern",
            800,
            &request.options,
        ) {
            results.push(result);
        }
    }
    human_sort_truncate_search_results(&mut results, request.options.limit);

    Ok(HumanTheoremSearchOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        goal_id: None,
        theorem_index_fingerprint: index.fingerprint,
        results,
    })
}

pub fn search_human_theorems_for_goal(
    store: &HumanProofSessionStore,
    request: HumanTheoremGoalSearchRequest,
) -> Result<HumanTheoremSearchOk, HumanTheoremSearchError> {
    let modes = human_goal_search_modes(&request.modes)?;
    let (entry, index) = human_search_index_for_state(store, &request.header, &request.state_id)?;
    let machine_goal_id = entry
        .machine_goal_for_human_goal(&request.goal_id)
        .ok_or_else(|| HumanTheoremSearchError::UnknownGoal {
            session_id: request.header.session_id.clone(),
            state_id: entry.state_id.clone(),
            goal_id: request.goal_id.clone(),
        })?;
    let goal = entry.state.goal(machine_goal_id).map_err(|diagnostic| {
        HumanTheoremSearchError::State(human_state_materialization_error(
            &request.header,
            &request.state_id,
            HumanStructuredProofStateError::MachineGoal {
                state_id: request.state_id.clone(),
                machine_goal_id,
                diagnostic: Box::new(diagnostic),
            },
        ))
    })?;
    let mut results = Vec::new();
    let context = HumanGoalSearchContext {
        store,
        header: &request.header,
        state_id: &request.state_id,
        goal_id: &request.goal_id,
        state: &entry.state,
        goal: &goal,
        options: &request.options,
    };
    for theorem in &index.entries {
        if !human_theorem_relevant_to_goal(theorem, &goal) {
            continue;
        }
        for mode in &modes {
            human_push_goal_search_results(&context, theorem, *mode, &mut results);
        }
    }
    human_sort_truncate_search_results(&mut results, request.options.limit);

    Ok(HumanTheoremSearchOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        goal_id: Some(request.goal_id),
        theorem_index_fingerprint: index.fingerprint,
        results,
    })
}

pub fn search_human_theorems_for_rewrite(
    store: &HumanProofSessionStore,
    request: HumanTheoremRewriteSearchRequest,
) -> Result<HumanTheoremSearchOk, HumanTheoremSearchError> {
    search_human_theorems_for_goal(
        store,
        HumanTheoremGoalSearchRequest {
            header: request.header,
            state_id: request.state_id,
            goal_id: request.goal_id,
            modes: vec![HumanTheoremSearchMode::Rw],
            options: request.options,
        },
    )
}

pub fn verify_human_session(
    store: &HumanProofSessionStore,
    request: HumanSessionVerifyRequest,
) -> Result<HumanSessionVerifyOk, HumanSessionVerifyError> {
    validate_human_state_request_document(store, request.header.clone())
        .map_err(|error| HumanSessionVerifyError::State(HumanStateApiError::from(error)))?;
    let entry = human_state_entry_for_api(store, &request.header, &request.state_id)
        .map_err(HumanSessionVerifyError::State)?;
    if !entry.state.open_goals.is_empty() {
        return Err(HumanSessionVerifyError::OpenGoals {
            session_id: request.header.session_id,
            state_id: entry.state_id.clone(),
            open_goals: entry
                .state
                .open_goals
                .iter()
                .filter_map(|goal_id| entry.human_goal_for_machine_goal(*goal_id).cloned())
                .collect(),
        });
    }

    let error_context = HumanVerifyErrorContext {
        session_id: &request.header.session_id,
        state_id: &entry.state_id,
    };
    let handoff = npa_tactic::extract_closed_machine_certificate(&entry.state).map_err(|err| {
        error_context.error(format!(
            "Human session certificate handoff failed after closed-state check: {:?}: {}",
            err.kind, err.message
        ))
    })?;
    let root_decl_index =
        human_verify_root_decl_index(&handoff.certificate, &entry.state, error_context)?;
    let root_decl = handoff
        .certificate
        .declarations
        .get(root_decl_index)
        .ok_or_else(|| {
            error_context.error("verified certificate root declaration index is out of range")
        })?;
    let certificate_context =
        human_verify_certificate_context(&entry.state, &handoff.certificate, root_decl_index);
    let root_axioms_used = human_verify_axiom_refs_to_wire(
        &certificate_context,
        human_verify_root_axiom_refs(
            handoff.verified_module.axiom_report(),
            root_decl_index,
            error_context,
        )?,
        error_context,
    )?;
    let axioms_used = human_verify_axiom_refs_to_wire(
        &certificate_context,
        &handoff.verified_module.axiom_report().module_axioms,
        error_context,
    )?;
    let imports = human_verify_import_summaries(&entry.state, error_context)?;

    Ok(HumanSessionVerifyOk {
        session_id: request.header.session_id,
        state_id: entry.state_id.clone(),
        document_version: entry.document_version,
        theorem_name: entry.state.root.theorem_name.clone(),
        status: HumanSessionVerifyStatus::Verified,
        root_decl_interface_hash: root_decl.hashes.decl_interface_hash,
        root_decl_certificate_hash: root_decl.hashes.decl_certificate_hash,
        certificate_hash: handoff.verified_module.certificate_hash(),
        export_hash: handoff.verified_module.export_hash(),
        contains_sorry: human_verify_contains_sorry(&axioms_used),
        root_axioms_used,
        axioms_used,
        certificate: human_certificate_payload(&handoff.certificate_bytes),
        imports,
    })
}

#[derive(Clone, Copy)]
struct HumanVerifyErrorContext<'a> {
    session_id: &'a crate::HumanSessionId,
    state_id: &'a crate::HumanStateId,
}

impl HumanVerifyErrorContext<'_> {
    fn error(self, message: impl Into<String>) -> HumanSessionVerifyError {
        HumanSessionVerifyError::CertificateHandoff {
            session_id: self.session_id.clone(),
            state_id: self.state_id.clone(),
            message: message.into(),
        }
    }
}

struct HumanVerifyCertificateContext<'a> {
    cert: &'a npa_cert::ModuleCert,
    cert_decl_to_source_index: BTreeMap<usize, u64>,
}

fn human_verify_root_decl_index(
    cert: &npa_cert::ModuleCert,
    state: &npa_tactic::MachineProofState,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<usize, HumanSessionVerifyError> {
    let mut matches = cert
        .declarations
        .iter()
        .enumerate()
        .filter_map(
            |(index, decl)| match human_verify_decl_payload_name(cert, &decl.decl) {
                Ok(name) if name == state.root.theorem_name => Some(Ok(index)),
                Ok(_) => None,
                Err(message) => Some(Err(error_context.error(message))),
            },
        )
        .collect::<Result<Vec<_>, _>>()?;
    if matches.len() != 1 {
        return Err(error_context.error(
            "verified Human certificate does not contain exactly one root theorem declaration",
        ));
    }
    let index = matches.pop().expect("len checked above");
    if !matches!(
        cert.declarations[index].decl,
        DeclPayload::Theorem {
            opacity: npa_cert::Opacity::Opaque,
            ..
        }
    ) {
        return Err(error_context.error("verified Human root declaration is not an opaque theorem"));
    }
    Ok(index)
}

fn human_verify_certificate_context<'a>(
    state: &npa_tactic::MachineProofState,
    cert: &'a npa_cert::ModuleCert,
    root_decl_index: usize,
) -> HumanVerifyCertificateContext<'a> {
    let mut cert_decl_to_source_index = state
        .env
        .checked_current_decls
        .iter()
        .enumerate()
        .map(|(index, decl)| (index, decl.source_index()))
        .collect::<BTreeMap<_, _>>();
    cert_decl_to_source_index.insert(root_decl_index, state.root.source_index);
    HumanVerifyCertificateContext {
        cert,
        cert_decl_to_source_index,
    }
}

fn human_verify_root_axiom_refs<'a>(
    report: &'a npa_cert::AxiomReport,
    root_decl_index: usize,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<&'a [AxiomRef], HumanSessionVerifyError> {
    let matches = report
        .per_declaration
        .iter()
        .filter(|entry| entry.decl_index == root_decl_index)
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(error_context.error(
            "verifier output does not contain exactly one Human root theorem axiom report",
        ));
    }
    Ok(&matches[0].transitive_axioms)
}

fn human_verify_axiom_refs_to_wire(
    context: &HumanVerifyCertificateContext<'_>,
    axioms: &[AxiomRef],
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<Vec<MachineAxiomRefWire>, HumanSessionVerifyError> {
    let mut out = Vec::with_capacity(axioms.len());
    for axiom in axioms {
        out.push(human_verify_axiom_ref_to_wire(
            context,
            axiom,
            error_context,
        )?);
    }
    human_sort_dedup_axiom_refs(&mut out);
    Ok(out)
}

fn human_verify_axiom_ref_to_wire(
    context: &HumanVerifyCertificateContext<'_>,
    axiom: &AxiomRef,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<MachineAxiomRefWire, HumanSessionVerifyError> {
    let name = human_verify_cert_name(context.cert, axiom.name, error_context)?;
    match &axiom.global_ref {
        GlobalRef::Imported {
            import_index,
            decl_interface_hash,
            ..
        } => {
            let import = context.cert.imports.get(*import_index).ok_or_else(|| {
                error_context
                    .error("verifier output imported axiom ref has out-of-range import_index")
            })?;
            Ok(MachineAxiomRefWire::Imported {
                module: import.module.clone(),
                name,
                export_hash: import.export_hash,
                decl_interface_hash: *decl_interface_hash,
            })
        }
        GlobalRef::Local { decl_index } => {
            let decl = context.cert.declarations.get(*decl_index).ok_or_else(|| {
                error_context.error("verifier output local axiom ref has out-of-range decl_index")
            })?;
            if !matches!(decl.decl, DeclPayload::Axiom { .. }) {
                return Err(error_context
                    .error("verifier output local axiom ref does not point at an axiom"));
            }
            let source_index = context
                .cert_decl_to_source_index
                .get(decl_index)
                .copied()
                .ok_or_else(|| {
                    error_context.error("verifier output local axiom ref has no Human source_index")
                })?;
            Ok(MachineAxiomRefWire::CurrentModule {
                module: context.cert.header.module.clone(),
                name,
                source_index,
                decl_interface_hash: axiom.decl_interface_hash,
            })
        }
        GlobalRef::Builtin {
            decl_interface_hash,
            ..
        } => Ok(MachineAxiomRefWire::Builtin {
            name,
            decl_interface_hash: *decl_interface_hash,
        }),
        GlobalRef::LocalGenerated { .. } => {
            Err(error_context.error("verifier output axiom ref points at a generated declaration"))
        }
    }
}

fn human_verify_import_summaries(
    state: &npa_tactic::MachineProofState,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<Vec<HumanSessionVerifyImport>, HumanSessionVerifyError> {
    let mut imports = Vec::with_capacity(state.env.imports.len());
    for import in &state.env.imports {
        imports.push(HumanSessionVerifyImport {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
            module_axioms: human_verify_import_axiom_summaries(
                import.verified_module(),
                error_context,
            )?,
        });
    }
    imports.sort_by(|left, right| {
        left.module
            .as_dotted()
            .cmp(&right.module.as_dotted())
            .then_with(|| left.export_hash.cmp(&right.export_hash))
            .then_with(|| left.certificate_hash.cmp(&right.certificate_hash))
    });
    imports.dedup_by(|left, right| {
        left.module == right.module
            && left.export_hash == right.export_hash
            && left.certificate_hash == right.certificate_hash
    });
    Ok(imports)
}

fn human_verify_import_axiom_summaries(
    module: &VerifiedModule,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<Vec<HumanSessionVerifyImportAxiom>, HumanSessionVerifyError> {
    let mut axioms = Vec::with_capacity(module.axiom_report().module_axioms.len());
    for axiom in &module.axiom_report().module_axioms {
        axioms.push(HumanSessionVerifyImportAxiom {
            name: module
                .name_table()
                .get(axiom.name)
                .cloned()
                .ok_or_else(|| {
                    error_context.error(
                        "verified import axiom report references an out-of-range name table entry",
                    )
                })?,
            decl_interface_hash: axiom.decl_interface_hash,
        });
    }
    axioms.sort_by(|left, right| {
        left.name
            .as_dotted()
            .cmp(&right.name.as_dotted())
            .then_with(|| left.decl_interface_hash.cmp(&right.decl_interface_hash))
    });
    axioms.dedup();
    Ok(axioms)
}

fn human_verify_decl_payload_name(
    cert: &npa_cert::ModuleCert,
    payload: &DeclPayload,
) -> Result<Name, String> {
    let name = match payload {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    cert.name_table.get(name).cloned().ok_or_else(|| {
        "verified Human certificate declaration references an out-of-range name table entry"
            .to_owned()
    })
}

fn human_verify_cert_name(
    cert: &npa_cert::ModuleCert,
    name: NameId,
    error_context: HumanVerifyErrorContext<'_>,
) -> Result<Name, HumanSessionVerifyError> {
    cert.name_table.get(name).cloned().ok_or_else(|| {
        error_context
            .error("verified Human certificate axiom report references an out-of-range name")
    })
}

fn human_verify_contains_sorry(axioms: &[MachineAxiomRefWire]) -> bool {
    axioms.iter().any(|axiom| match axiom {
        MachineAxiomRefWire::Builtin { name, .. }
        | MachineAxiomRefWire::Imported { name, .. }
        | MachineAxiomRefWire::CurrentModule { name, .. } => name.as_dotted().contains("sorry"),
    })
}

fn human_certificate_payload(bytes: &[u8]) -> HumanCertificatePayload {
    HumanCertificatePayload {
        encoding: HUMAN_CERTIFICATE_ENCODING,
        bytes: human_hex_bytes(bytes),
    }
}

fn human_hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(human_hex_digit(byte >> 4));
        out.push(human_hex_digit(byte & 0x0f));
    }
    out
}

fn human_hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + value - 10),
        _ => unreachable!("hex nybble is in range"),
    }
}

fn human_search_index_for_state<'session>(
    store: &'session HumanProofSessionStore,
    header: &HumanStateRequestHeader,
    state_id: &crate::HumanStateId,
) -> Result<(&'session HumanProofStateEntry, HumanTheoremIndex), HumanTheoremSearchError> {
    validate_human_state_request_document(store, header.clone())
        .map_err(|error| HumanTheoremSearchError::State(HumanStateApiError::from(error)))?;
    let entry = human_state_entry_for_api(store, header, state_id)
        .map_err(HumanTheoremSearchError::State)?;
    let index = build_human_theorem_index(&entry.state).map_err(HumanTheoremSearchError::Index)?;
    Ok((entry, index))
}

fn human_goal_search_modes(
    modes: &[HumanTheoremSearchMode],
) -> Result<Vec<HumanTheoremSearchMode>, HumanTheoremSearchError> {
    let modes = if modes.is_empty() {
        vec![
            HumanTheoremSearchMode::Exact,
            HumanTheoremSearchMode::Apply,
            HumanTheoremSearchMode::Rw,
            HumanTheoremSearchMode::Simp,
        ]
    } else {
        modes.to_vec()
    };
    for mode in &modes {
        if !matches!(
            mode,
            HumanTheoremSearchMode::Exact
                | HumanTheoremSearchMode::Apply
                | HumanTheoremSearchMode::Rw
                | HumanTheoremSearchMode::Simp
        ) {
            return Err(HumanTheoremSearchError::InvalidGoalMode { mode: *mode });
        }
    }
    let mut deduped = modes;
    deduped.sort();
    deduped.dedup();
    Ok(deduped)
}

struct HumanGoalSearchContext<'a> {
    store: &'a HumanProofSessionStore,
    header: &'a HumanStateRequestHeader,
    state_id: &'a crate::HumanStateId,
    goal_id: &'a crate::HumanGoalId,
    state: &'a npa_tactic::MachineProofState,
    goal: &'a npa_tactic::MachineGoal,
    options: &'a HumanTheoremSearchOptions,
}

fn human_push_goal_search_results(
    context: &HumanGoalSearchContext<'_>,
    theorem: &HumanTheoremIndexEntry,
    mode: HumanTheoremSearchMode,
    results: &mut Vec<HumanTheoremSearchResult>,
) {
    let candidates = match mode {
        HumanTheoremSearchMode::Exact => human_exact_tactic_candidates(theorem, context.goal),
        HumanTheoremSearchMode::Apply => vec![format!("apply {}", theorem.name.as_dotted())],
        HumanTheoremSearchMode::Rw => {
            if !human_theorem_has_eq_conclusion(theorem) {
                return;
            }
            vec![format!("rw [{}]", theorem.name.as_dotted())]
        }
        HumanTheoremSearchMode::Simp => {
            if !human_theorem_has_simp_rule(context.state, theorem) {
                return;
            }
            vec!["simp-lite".to_owned()]
        }
        HumanTheoremSearchMode::Name | HumanTheoremSearchMode::ByType => return,
    };

    for tactic in candidates {
        let check = check_human_tactic(
            context.store,
            HumanTacticCheckRequest {
                header: context.header.clone(),
                state_id: context.state_id.clone(),
                goal_id: context.goal_id.clone(),
                tactic: tactic.clone(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        if !human_goal_search_check_accepts(mode, check.status, check.error.as_ref()) {
            continue;
        }
        let match_info = human_goal_search_match_info(mode, theorem, context.goal, &tactic);
        if let Some(result) = human_search_result_from_entry(
            theorem,
            mode,
            tactic,
            match_info,
            human_goal_search_why(mode),
            human_goal_search_base_score(mode),
            context.options,
        ) {
            results.push(result);
        }
        break;
    }
}

fn human_goal_search_check_accepts(
    mode: HumanTheoremSearchMode,
    status: HumanTacticRunStatus,
    error: Option<&HumanTacticRunErrorReport>,
) -> bool {
    if error.is_some()
        || matches!(
            status,
            HumanTacticRunStatus::Error
                | HumanTacticRunStatus::Timeout
                | HumanTacticRunStatus::Unsafe
        )
    {
        return false;
    }
    if mode == HumanTheoremSearchMode::Exact {
        return matches!(
            status,
            HumanTacticRunStatus::Closed | HumanTacticRunStatus::Success
        );
    }
    true
}

fn human_goal_search_base_score(mode: HumanTheoremSearchMode) -> u64 {
    match mode {
        HumanTheoremSearchMode::Exact => 1000,
        HumanTheoremSearchMode::Rw => 900,
        HumanTheoremSearchMode::Apply => 700,
        HumanTheoremSearchMode::Simp => 600,
        HumanTheoremSearchMode::ByType => 800,
        HumanTheoremSearchMode::Name => 500,
    }
}

fn human_goal_search_why(mode: HumanTheoremSearchMode) -> &'static str {
    match mode {
        HumanTheoremSearchMode::Exact => {
            "the suggested exact tactic was checked against the current goal"
        }
        HumanTheoremSearchMode::Apply => {
            "the suggested apply tactic was checked against the current goal"
        }
        HumanTheoremSearchMode::Rw => {
            "the suggested rewrite tactic was checked against the current goal"
        }
        HumanTheoremSearchMode::Simp => {
            "simp-lite was checked against the current goal with this theorem in scope"
        }
        HumanTheoremSearchMode::Name => "name contains the search query",
        HumanTheoremSearchMode::ByType => "the theorem conclusion matches the type pattern",
    }
}

fn human_goal_search_match_info(
    mode: HumanTheoremSearchMode,
    theorem: &HumanTheoremIndexEntry,
    goal: &npa_tactic::MachineGoal,
    tactic: &str,
) -> Vec<HumanTheoremMatchBinding> {
    match mode {
        HumanTheoremSearchMode::Exact => {
            let (_, names) = human_exact_tactic_base_and_args(tactic);
            let binder_names = human_search_display_binder_names(&theorem.statement_core);
            names
                .into_iter()
                .enumerate()
                .map(|(index, value)| HumanTheoremMatchBinding {
                    pattern: binder_names
                        .get(index)
                        .cloned()
                        .unwrap_or_else(|| format!("arg{index}")),
                    value,
                })
                .collect()
        }
        HumanTheoremSearchMode::Rw => vec![HumanTheoremMatchBinding {
            pattern: "target".to_owned(),
            value: human_structured_expr_pretty(
                &goal.target,
                &goal
                    .context
                    .iter()
                    .map(|local| local.name.clone())
                    .collect::<Vec<_>>(),
            ),
        }],
        HumanTheoremSearchMode::Apply | HumanTheoremSearchMode::Simp => Vec::new(),
        HumanTheoremSearchMode::Name | HumanTheoremSearchMode::ByType => Vec::new(),
    }
}

fn human_search_result_from_entry(
    theorem: &HumanTheoremIndexEntry,
    mode: HumanTheoremSearchMode,
    suggested_tactic: String,
    match_info: Vec<HumanTheoremMatchBinding>,
    why: impl Into<String>,
    base_score: u64,
    options: &HumanTheoremSearchOptions,
) -> Option<HumanTheoremSearchResult> {
    let axiom_info = human_search_axiom_info(theorem, options)?;
    let score = base_score.saturating_sub(axiom_info.score_penalty);
    Some(HumanTheoremSearchResult {
        name: theorem.name.clone(),
        module: theorem.module.clone(),
        source: theorem.source.clone(),
        kind: theorem.kind,
        mode,
        statement_core: theorem.statement_core.clone(),
        statement_pretty: theorem.statement_pretty.clone(),
        suggested_tactic,
        match_info,
        why: why.into(),
        score,
        axiom_info,
        export_hash: theorem.export_hash,
        certificate_hash: theorem.certificate_hash,
        decl_interface_hash: theorem.decl_interface_hash,
    })
}

fn human_search_axiom_info(
    theorem: &HumanTheoremIndexEntry,
    options: &HumanTheoremSearchOptions,
) -> Option<HumanTheoremAxiomInfo> {
    let uses_axioms = !theorem.axiom_dependencies.is_empty();
    if uses_axioms && options.axiom_policy == HumanTheoremSearchAxiomPolicy::Exclude {
        return None;
    }
    let score_penalty =
        if uses_axioms && options.axiom_policy == HumanTheoremSearchAxiomPolicy::Penalize {
            200
        } else {
            0
        };
    Some(HumanTheoremAxiomInfo {
        uses_axioms,
        axiom_dependencies: theorem.axiom_dependencies.clone(),
        score_penalty,
    })
}

fn human_sort_truncate_search_results(results: &mut Vec<HumanTheoremSearchResult>, limit: usize) {
    results.sort_by(|left, right| {
        right
            .score
            .cmp(&left.score)
            .then_with(|| left.name.as_dotted().cmp(&right.name.as_dotted()))
            .then_with(|| left.mode.cmp(&right.mode))
            .then_with(|| left.decl_interface_hash.cmp(&right.decl_interface_hash))
    });
    results.truncate(limit);
}

fn human_default_exact_tactic(theorem: &HumanTheoremIndexEntry) -> String {
    let mut parts = vec!["exact".to_owned(), theorem.name.as_dotted()];
    parts.extend(human_search_display_binder_names(&theorem.statement_core));
    parts.join(" ")
}

fn human_search_display_binder_names(expr: &Expr) -> Vec<String> {
    human_search_display_names(human_theorem_binder_names(expr))
}

fn human_search_display_names(names: Vec<String>) -> Vec<String> {
    names
        .into_iter()
        .enumerate()
        .map(|(index, name)| {
            if name.trim().is_empty() || name == "_" {
                human_default_display_binder_name(index)
            } else {
                name
            }
        })
        .collect()
}

fn human_default_display_binder_name(index: usize) -> String {
    match index {
        0 => "n".to_owned(),
        1 => "m".to_owned(),
        2 => "k".to_owned(),
        _ => format!("arg{index}"),
    }
}

fn human_exact_tactic_candidates(
    theorem: &HumanTheoremIndexEntry,
    goal: &npa_tactic::MachineGoal,
) -> Vec<String> {
    let binder_count = human_theorem_binder_names(&theorem.statement_core).len();
    let local_names = goal
        .context
        .iter()
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    let max_args = binder_count.min(local_names.len());
    let mut candidates = Vec::new();
    for count in (0..=max_args).rev() {
        let mut parts = vec!["exact".to_owned(), theorem.name.as_dotted()];
        parts.extend(local_names.iter().take(count).cloned());
        candidates.push(parts.join(" "));
    }
    candidates.sort();
    candidates.dedup();
    candidates.sort_by_key(|candidate| {
        std::cmp::Reverse(human_exact_tactic_base_and_args(candidate).1.len())
    });
    candidates
}

fn human_exact_tactic_base_and_args(tactic: &str) -> (Option<String>, Vec<String>) {
    let parts = tactic.split_whitespace().collect::<Vec<_>>();
    if parts.len() < 2 || parts[0] != "exact" {
        return (None, Vec::new());
    }
    (
        Some(parts[1].to_owned()),
        parts
            .iter()
            .skip(2)
            .map(|part| (*part).to_owned())
            .collect(),
    )
}

fn human_theorem_relevant_to_goal(
    theorem: &HumanTheoremIndexEntry,
    goal: &npa_tactic::MachineGoal,
) -> bool {
    let (_, conclusion) = human_theorem_conclusion(&theorem.statement_core);
    let mut theorem_constants = BTreeSet::new();
    human_collect_expr_constants(conclusion, &mut theorem_constants);
    let mut goal_constants = BTreeSet::new();
    human_collect_expr_constants(&goal.target, &mut goal_constants);
    if !theorem_constants.is_disjoint(&goal_constants) {
        return true;
    }
    let theorem_head = human_expr_head_name(conclusion);
    let goal_head = human_expr_head_name(&goal.target);
    theorem_head.is_some() && theorem_head == goal_head
}

fn human_theorem_has_eq_conclusion(theorem: &HumanTheoremIndexEntry) -> bool {
    let (_, conclusion) = human_theorem_conclusion(&theorem.statement_core);
    human_eq_app_sides(conclusion).is_some()
}

fn human_theorem_has_simp_rule(
    state: &npa_tactic::MachineProofState,
    theorem: &HumanTheoremIndexEntry,
) -> bool {
    state.env.simp_registry.rules.iter().any(|rule| {
        rule.key.name == theorem.name && rule.key.decl_interface_hash == theorem.decl_interface_hash
    })
}

fn human_expr_head_name(expr: &Expr) -> Option<Name> {
    let (head, _) = human_app_head_and_args(expr);
    let Expr::Const { name, .. } = head else {
        return None;
    };
    Some(Name::from_dotted(name))
}

fn human_theorem_conclusion(expr: &Expr) -> (Vec<String>, &Expr) {
    let mut binders = Vec::new();
    let mut current = expr;
    while let Expr::Pi { binder, body, .. } = current {
        binders.push(binder.clone());
        current = body;
    }
    (binders, current)
}

fn human_theorem_binder_names(expr: &Expr) -> Vec<String> {
    human_theorem_conclusion(expr).0
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum HumanSearchPattern {
    Hole(String),
    Const(Name),
    Add(Box<HumanSearchPattern>, Box<HumanSearchPattern>),
    Eq(Box<HumanSearchPattern>, Box<HumanSearchPattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum HumanSearchPatternToken {
    Hole(String),
    Ident(String),
    Zero,
    Plus,
    Equals,
    LParen,
    RParen,
}

struct HumanSearchPatternParser {
    tokens: Vec<HumanSearchPatternToken>,
    pos: usize,
}

fn human_parse_search_pattern(source: &str) -> Result<HumanSearchPattern, String> {
    let tokens = human_search_pattern_tokens(source)?;
    let mut parser = HumanSearchPatternParser { tokens, pos: 0 };
    let pattern = parser.parse_eq()?;
    if parser.peek().is_some() {
        return Err("unexpected trailing tokens in type pattern".to_owned());
    }
    Ok(pattern)
}

fn human_search_pattern_tokens(source: &str) -> Result<Vec<HumanSearchPatternToken>, String> {
    let chars = source.chars().collect::<Vec<_>>();
    let mut tokens = Vec::new();
    let mut pos = 0;
    while pos < chars.len() {
        let ch = chars[pos];
        if ch.is_whitespace() {
            pos += 1;
            continue;
        }
        match ch {
            '?' => {
                pos += 1;
                let start = pos;
                while pos < chars.len()
                    && (chars[pos].is_ascii_alphanumeric()
                        || chars[pos] == '_'
                        || chars[pos] == '\'')
                {
                    pos += 1;
                }
                if start == pos {
                    return Err("hole marker `?` must be followed by a name".to_owned());
                }
                tokens.push(HumanSearchPatternToken::Hole(format!(
                    "?{}",
                    chars[start..pos].iter().collect::<String>()
                )));
            }
            '0' => {
                tokens.push(HumanSearchPatternToken::Zero);
                pos += 1;
            }
            '+' => {
                tokens.push(HumanSearchPatternToken::Plus);
                pos += 1;
            }
            '=' => {
                tokens.push(HumanSearchPatternToken::Equals);
                pos += 1;
            }
            '(' => {
                tokens.push(HumanSearchPatternToken::LParen);
                pos += 1;
            }
            ')' => {
                tokens.push(HumanSearchPatternToken::RParen);
                pos += 1;
            }
            ch if ch.is_ascii_alphabetic() => {
                let start = pos;
                pos += 1;
                while pos < chars.len()
                    && (chars[pos].is_ascii_alphanumeric()
                        || chars[pos] == '_'
                        || chars[pos] == '\''
                        || chars[pos] == '.')
                {
                    pos += 1;
                }
                tokens.push(HumanSearchPatternToken::Ident(
                    chars[start..pos].iter().collect(),
                ));
            }
            _ => return Err(format!("unsupported token `{ch}` in type pattern")),
        }
    }
    Ok(tokens)
}

impl HumanSearchPatternParser {
    fn peek(&self) -> Option<&HumanSearchPatternToken> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) -> Option<HumanSearchPatternToken> {
        let token = self.peek()?.clone();
        self.pos += 1;
        Some(token)
    }

    fn parse_eq(&mut self) -> Result<HumanSearchPattern, String> {
        let lhs = self.parse_add()?;
        if !matches!(self.peek(), Some(HumanSearchPatternToken::Equals)) {
            return Ok(lhs);
        }
        self.advance();
        let rhs = self.parse_add()?;
        Ok(HumanSearchPattern::Eq(Box::new(lhs), Box::new(rhs)))
    }

    fn parse_add(&mut self) -> Result<HumanSearchPattern, String> {
        let mut lhs = self.parse_atom()?;
        while matches!(self.peek(), Some(HumanSearchPatternToken::Plus)) {
            self.advance();
            let rhs = self.parse_atom()?;
            lhs = HumanSearchPattern::Add(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_atom(&mut self) -> Result<HumanSearchPattern, String> {
        match self.advance() {
            Some(HumanSearchPatternToken::Hole(name)) => Ok(HumanSearchPattern::Hole(name)),
            Some(HumanSearchPatternToken::Ident(name)) => {
                Ok(HumanSearchPattern::Const(Name::from_dotted(&name)))
            }
            Some(HumanSearchPatternToken::Zero) => {
                Ok(HumanSearchPattern::Const(Name::from_dotted("Nat.zero")))
            }
            Some(HumanSearchPatternToken::LParen) => {
                let pattern = self.parse_eq()?;
                if !matches!(self.advance(), Some(HumanSearchPatternToken::RParen)) {
                    return Err("missing closing `)` in type pattern".to_owned());
                }
                Ok(pattern)
            }
            Some(other) => Err(format!("unexpected token {other:?} in type pattern")),
            None => Err("unexpected end of type pattern".to_owned()),
        }
    }
}

fn human_search_pattern_matches(
    pattern: &HumanSearchPattern,
    expr: &Expr,
    bindings: &mut BTreeMap<String, Expr>,
) -> bool {
    match pattern {
        HumanSearchPattern::Hole(name) => match bindings.get(name) {
            Some(bound) => bound == expr,
            None => {
                bindings.insert(name.clone(), expr.clone());
                true
            }
        },
        HumanSearchPattern::Const(name) => matches!(
            expr,
            Expr::Const { name: expr_name, .. } if expr_name == &name.as_dotted()
        ),
        HumanSearchPattern::Add(lhs, rhs) => {
            let (head, args) = human_app_head_and_args(expr);
            matches!(head, Expr::Const { name, .. } if name == "Nat.add")
                && args.len() == 2
                && human_search_pattern_matches(lhs, args[0], bindings)
                && human_search_pattern_matches(rhs, args[1], bindings)
        }
        HumanSearchPattern::Eq(lhs, rhs) => {
            let Some((expr_lhs, expr_rhs)) = human_eq_app_sides(expr) else {
                return false;
            };
            human_search_pattern_matches(lhs, expr_lhs, bindings)
                && human_search_pattern_matches(rhs, expr_rhs, bindings)
        }
    }
}

#[derive(Clone, Debug)]
struct HumanImportTheoremFact {
    module: ModuleName,
    name: Name,
    universe_params: Vec<String>,
    statement_core: Expr,
    kind: HumanTheoremIndexKind,
    declared_dependencies: Vec<HumanTheoremDependency>,
    axiom_dependencies: Vec<MachineAxiomRefWire>,
    export_hash: Hash,
    certificate_hash: Hash,
    decl_interface_hash: Hash,
}

#[derive(Clone, Debug)]
struct HumanCurrentTheoremFact {
    module: ModuleName,
    name: Name,
    source_index: u64,
    decl_interface_hash: Hash,
    axiom_dependencies: Vec<MachineAxiomRefWire>,
}

fn human_import_export_fact(
    import: &npa_tactic::VerifiedImportRef,
    export: &ExportEntry,
) -> Result<HumanImportTheoremFact, HumanTheoremIndexError> {
    let verified = import.verified_module();
    let module = import.module().clone();
    let name = human_name_from_verified(verified, export.name)?;
    let universe_params = export
        .universe_params
        .iter()
        .map(|name_id| human_universe_param_from_verified(verified, *name_id))
        .collect::<Result<Vec<_>, _>>()?;
    let statement_core = human_expr_from_verified_term(verified, export.ty)?;
    let declared_dependencies = human_export_decl_dependencies(import, export)?;
    let mut axiom_dependencies = export
        .axiom_dependencies
        .iter()
        .map(|axiom| human_import_axiom_ref_to_wire(import, axiom))
        .collect::<Result<Vec<_>, _>>()?;
    if export.kind == ExportKind::Axiom {
        axiom_dependencies.push(MachineAxiomRefWire::Imported {
            module: import.module().clone(),
            name: name.clone(),
            export_hash: import.export_hash(),
            decl_interface_hash: export.decl_interface_hash,
        });
    }
    human_sort_dedup_axiom_refs(&mut axiom_dependencies);

    Ok(HumanImportTheoremFact {
        module,
        name,
        universe_params,
        statement_core,
        kind: human_export_kind(export.kind),
        declared_dependencies,
        axiom_dependencies,
        export_hash: import.export_hash(),
        certificate_hash: import.certificate_hash(),
        decl_interface_hash: export.decl_interface_hash,
    })
}

fn human_import_export_entry(
    fact: &HumanImportTheoremFact,
    import_facts: &BTreeMap<Name, HumanImportTheoremFact>,
) -> Result<HumanTheoremIndexEntry, HumanTheoremIndexError> {
    let statement = human_index_structured_expr(&fact.name, &fact.statement_core)?;
    let mut dependencies = fact.declared_dependencies.clone();
    dependencies.extend(human_dependencies_from_constants(
        &statement.constants,
        Some(&fact.name),
        import_facts,
        &BTreeMap::new(),
    ));
    human_sort_dedup_dependencies(&mut dependencies);
    let statement_pretty = statement.pretty.clone();
    let head_symbol = statement.head.clone();
    let constants = statement.constants.clone();

    Ok(HumanTheoremIndexEntry {
        name: fact.name.clone(),
        module: fact.module.clone(),
        source: HumanTheoremIndexSource::VerifiedImport {
            export_hash: fact.export_hash,
            certificate_hash: fact.certificate_hash,
        },
        universe_params: fact.universe_params.clone(),
        statement_core: fact.statement_core.clone(),
        statement,
        statement_pretty,
        head_symbol,
        constants,
        attributes: Vec::new(),
        kind: fact.kind,
        dependencies,
        axiom_dependencies: fact.axiom_dependencies.clone(),
        export_hash: Some(fact.export_hash),
        certificate_hash: Some(fact.certificate_hash),
        decl_interface_hash: fact.decl_interface_hash,
    })
}

fn human_checked_current_entry(
    current_module: &ModuleName,
    checked: &npa_tactic::CheckedCurrentDecl,
    import_facts: &BTreeMap<Name, HumanImportTheoremFact>,
    current_facts: &BTreeMap<Name, HumanCurrentTheoremFact>,
) -> Result<HumanTheoremIndexEntry, HumanTheoremIndexError> {
    let name = checked.signature().name().clone();
    let statement_core = checked.signature().ty().clone();
    let statement = human_index_structured_expr(&name, &statement_core)?;
    let mut dependency_constants = BTreeSet::new();
    human_collect_decl_constants(checked.core_decl(), &mut dependency_constants);
    let dependencies = human_dependencies_from_constants(
        &dependency_constants.into_iter().collect::<Vec<_>>(),
        Some(&name),
        import_facts,
        current_facts,
    );
    let mut axiom_dependencies =
        human_axiom_dependencies_from_dependencies(&dependencies, import_facts, current_facts);
    if matches!(checked.core_decl(), Decl::Axiom { .. }) {
        axiom_dependencies.push(MachineAxiomRefWire::CurrentModule {
            module: current_module.clone(),
            name: name.clone(),
            source_index: checked.source_index(),
            decl_interface_hash: checked.signature().decl_interface_hash(),
        });
    }
    human_sort_dedup_axiom_refs(&mut axiom_dependencies);
    let statement_pretty = statement.pretty.clone();
    let head_symbol = statement.head.clone();
    let constants = statement.constants.clone();

    Ok(HumanTheoremIndexEntry {
        name,
        module: current_module.clone(),
        source: HumanTheoremIndexSource::CheckedCurrentDecl {
            source_index: checked.source_index(),
        },
        universe_params: checked.signature().universe_params().to_vec(),
        statement_core,
        statement,
        statement_pretty,
        head_symbol,
        constants,
        attributes: Vec::new(),
        kind: human_current_decl_kind(checked.core_decl()),
        dependencies,
        axiom_dependencies,
        export_hash: None,
        certificate_hash: None,
        decl_interface_hash: checked.signature().decl_interface_hash(),
    })
}

fn human_index_structured_expr(
    name: &Name,
    expr: &Expr,
) -> Result<StructuredExpr, HumanTheoremIndexError> {
    let metadata = core_expr_metadata(expr, 0)
        .map_err(|_| HumanTheoremIndexError::ExpressionMetadata { name: name.clone() })?;
    Ok(StructuredExpr {
        core_hash: metadata.core_hash,
        head: metadata.head,
        constants: metadata.constants,
        free_locals: metadata.free_locals,
        size: metadata.size,
        pretty: human_structured_expr_pretty(expr, &[]),
    })
}

fn human_export_kind(kind: ExportKind) -> HumanTheoremIndexKind {
    match kind {
        ExportKind::Axiom => HumanTheoremIndexKind::Axiom,
        ExportKind::Def => HumanTheoremIndexKind::Def,
        ExportKind::Theorem => HumanTheoremIndexKind::Theorem,
        ExportKind::Inductive => HumanTheoremIndexKind::Inductive,
        ExportKind::Constructor => HumanTheoremIndexKind::Constructor,
        ExportKind::Recursor => HumanTheoremIndexKind::Recursor,
    }
}

fn human_current_decl_kind(decl: &Decl) -> HumanTheoremIndexKind {
    match decl {
        Decl::Axiom { .. } | Decl::AxiomConstrained { .. } => HumanTheoremIndexKind::Axiom,
        Decl::Def { .. } | Decl::DefConstrained { .. } => HumanTheoremIndexKind::Def,
        Decl::Theorem { .. } | Decl::TheoremConstrained { .. } => HumanTheoremIndexKind::Theorem,
        Decl::Inductive { .. } | Decl::MutualInductiveBlock { .. } => {
            HumanTheoremIndexKind::Inductive
        }
        Decl::Constructor { .. } => HumanTheoremIndexKind::Constructor,
        Decl::Recursor { .. } => HumanTheoremIndexKind::Recursor,
    }
}

fn human_export_decl_dependencies(
    import: &npa_tactic::VerifiedImportRef,
    export: &ExportEntry,
) -> Result<Vec<HumanTheoremDependency>, HumanTheoremIndexError> {
    let Some(decl) = human_decl_cert_for_export(import.verified_module(), export)? else {
        return Ok(Vec::new());
    };
    decl.dependencies
        .iter()
        .map(|dependency| human_dependency_entry_to_index(import, dependency))
        .collect()
}

fn human_decl_cert_for_export<'a>(
    module: &'a VerifiedModule,
    export: &ExportEntry,
) -> Result<Option<&'a npa_cert::DeclCert>, HumanTheoremIndexError> {
    if matches!(export.kind, ExportKind::Constructor | ExportKind::Recursor) {
        return Ok(None);
    }
    let export_name = human_name_from_verified(module, export.name)?;
    for decl in module.declarations() {
        if human_decl_payload_name(module, &decl.decl)? == export_name {
            return Ok(Some(decl));
        }
    }
    Ok(None)
}

fn human_dependency_entry_to_index(
    owner: &npa_tactic::VerifiedImportRef,
    dependency: &DependencyEntry,
) -> Result<HumanTheoremDependency, HumanTheoremIndexError> {
    let module = owner.verified_module();
    match &dependency.global_ref {
        GlobalRef::Local { decl_index } => {
            let decl = module.declarations().get(*decl_index).ok_or_else(|| {
                HumanTheoremIndexError::MissingDeclaration {
                    module: module.module().clone(),
                    decl_index: *decl_index,
                }
            })?;
            Ok(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::Imported,
                name: human_decl_payload_name(module, &decl.decl)?,
                module: Some(owner.module().clone()),
                export_hash: Some(owner.export_hash()),
                source_index: None,
                decl_interface_hash: Some(dependency.decl_interface_hash),
            })
        }
        GlobalRef::LocalGenerated { name, .. } => Ok(HumanTheoremDependency {
            kind: HumanTheoremDependencyKind::Imported,
            name: human_name_from_verified(module, *name)?,
            module: Some(owner.module().clone()),
            export_hash: Some(owner.export_hash()),
            source_index: None,
            decl_interface_hash: Some(dependency.decl_interface_hash),
        }),
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let imported = module.imports().get(*import_index).ok_or_else(|| {
                HumanTheoremIndexError::MissingDeclaration {
                    module: module.module().clone(),
                    decl_index: *import_index,
                }
            })?;
            Ok(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::Imported,
                name: human_name_from_verified(module, *name)?,
                module: Some(imported.module.clone()),
                export_hash: Some(imported.export_hash),
                source_index: None,
                decl_interface_hash: Some(*decl_interface_hash),
            })
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => Ok(HumanTheoremDependency {
            kind: HumanTheoremDependencyKind::Builtin,
            name: human_name_from_verified(module, *name)?,
            module: None,
            export_hash: None,
            source_index: None,
            decl_interface_hash: Some(*decl_interface_hash),
        }),
    }
}

fn human_dependencies_from_constants(
    constants: &[Name],
    self_name: Option<&Name>,
    import_facts: &BTreeMap<Name, HumanImportTheoremFact>,
    current_facts: &BTreeMap<Name, HumanCurrentTheoremFact>,
) -> Vec<HumanTheoremDependency> {
    let mut dependencies = Vec::new();
    for name in constants {
        if self_name.is_some_and(|self_name| self_name == name) {
            continue;
        }
        if let Some(imported) = import_facts.get(name) {
            dependencies.push(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::Imported,
                name: imported.name.clone(),
                module: Some(imported.module.clone()),
                export_hash: Some(imported.export_hash),
                source_index: None,
                decl_interface_hash: Some(imported.decl_interface_hash),
            });
        } else if let Some(current) = current_facts.get(name) {
            dependencies.push(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::Current,
                name: current.name.clone(),
                module: Some(current.module.clone()),
                export_hash: None,
                source_index: Some(current.source_index),
                decl_interface_hash: Some(current.decl_interface_hash),
            });
        } else if let Some(decl_interface_hash) = npa_cert::builtin_decl_interface_hash(name) {
            dependencies.push(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::Builtin,
                name: name.clone(),
                module: None,
                export_hash: None,
                source_index: None,
                decl_interface_hash: Some(decl_interface_hash),
            });
        } else {
            dependencies.push(HumanTheoremDependency {
                kind: HumanTheoremDependencyKind::UnknownConstant,
                name: name.clone(),
                module: None,
                export_hash: None,
                source_index: None,
                decl_interface_hash: None,
            });
        }
    }
    human_sort_dedup_dependencies(&mut dependencies);
    dependencies
}

fn human_axiom_dependencies_from_dependencies(
    dependencies: &[HumanTheoremDependency],
    import_facts: &BTreeMap<Name, HumanImportTheoremFact>,
    current_facts: &BTreeMap<Name, HumanCurrentTheoremFact>,
) -> Vec<MachineAxiomRefWire> {
    let mut axioms = Vec::new();
    for dependency in dependencies {
        match dependency.kind {
            HumanTheoremDependencyKind::Imported => {
                if let Some(imported) = import_facts.get(&dependency.name) {
                    axioms.extend(imported.axiom_dependencies.clone());
                }
            }
            HumanTheoremDependencyKind::Current => {
                if let Some(current) = current_facts.get(&dependency.name) {
                    axioms.extend(current.axiom_dependencies.clone());
                }
            }
            HumanTheoremDependencyKind::Builtin => {
                if human_is_builtin_axiom_name(&dependency.name) {
                    if let Some(decl_interface_hash) = dependency.decl_interface_hash {
                        axioms.push(MachineAxiomRefWire::Builtin {
                            name: dependency.name.clone(),
                            decl_interface_hash,
                        });
                    }
                }
            }
            HumanTheoremDependencyKind::UnknownConstant => {}
        }
    }
    human_sort_dedup_axiom_refs(&mut axioms);
    axioms
}

fn human_import_axiom_ref_to_wire(
    owner: &npa_tactic::VerifiedImportRef,
    axiom: &AxiomRef,
) -> Result<MachineAxiomRefWire, HumanTheoremIndexError> {
    let module = owner.verified_module();
    match &axiom.global_ref {
        GlobalRef::Local { decl_index } => {
            let decl = module.declarations().get(*decl_index).ok_or_else(|| {
                HumanTheoremIndexError::MissingDeclaration {
                    module: module.module().clone(),
                    decl_index: *decl_index,
                }
            })?;
            let name = human_decl_payload_name(module, &decl.decl)?;
            if !matches!(decl.decl, DeclPayload::Axiom { .. }) {
                return Err(HumanTheoremIndexError::InvalidAxiomRef {
                    module: module.module().clone(),
                    name,
                });
            }
            Ok(MachineAxiomRefWire::Imported {
                module: owner.module().clone(),
                name,
                export_hash: owner.export_hash(),
                decl_interface_hash: axiom.decl_interface_hash,
            })
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let imported = module.imports().get(*import_index).ok_or_else(|| {
                HumanTheoremIndexError::MissingDeclaration {
                    module: module.module().clone(),
                    decl_index: *import_index,
                }
            })?;
            Ok(MachineAxiomRefWire::Imported {
                module: imported.module.clone(),
                name: human_name_from_verified(module, *name)?,
                export_hash: imported.export_hash,
                decl_interface_hash: *decl_interface_hash,
            })
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = human_name_from_verified(module, *name)?;
            if human_is_builtin_axiom_name(&name) {
                Ok(MachineAxiomRefWire::Builtin {
                    name,
                    decl_interface_hash: *decl_interface_hash,
                })
            } else {
                Err(HumanTheoremIndexError::InvalidAxiomRef {
                    module: module.module().clone(),
                    name,
                })
            }
        }
        GlobalRef::LocalGenerated { name, .. } => {
            let name = human_name_from_verified(module, *name)?;
            Err(HumanTheoremIndexError::InvalidAxiomRef {
                module: module.module().clone(),
                name,
            })
        }
    }
}

fn human_is_builtin_axiom_name(name: &Name) -> bool {
    name.as_dotted() == "Eq.rec"
}

fn human_collect_decl_constants(decl: &Decl, out: &mut BTreeSet<Name>) {
    match decl {
        Decl::Axiom { ty, .. } | Decl::AxiomConstrained { ty, .. } => {
            human_collect_expr_constants(ty, out)
        }
        Decl::Def { ty, value, .. } | Decl::DefConstrained { ty, value, .. } => {
            human_collect_expr_constants(ty, out);
            human_collect_expr_constants(value, out);
        }
        Decl::Theorem { ty, proof, .. } | Decl::TheoremConstrained { ty, proof, .. } => {
            human_collect_expr_constants(ty, out);
            human_collect_expr_constants(proof, out);
        }
        Decl::Inductive { ty, data, .. } => {
            human_collect_expr_constants(ty, out);
            for param in &data.params {
                human_collect_expr_constants(&param.ty, out);
            }
            for index in &data.indices {
                human_collect_expr_constants(&index.ty, out);
            }
            for constructor in &data.constructors {
                human_collect_expr_constants(&constructor.ty, out);
            }
            if let Some(recursor) = &data.recursor {
                human_collect_expr_constants(&recursor.ty, out);
            }
        }
        Decl::MutualInductiveBlock { data, .. } => {
            for inductive in &data.inductives {
                for param in &inductive.params {
                    human_collect_expr_constants(&param.ty, out);
                }
                for index in &inductive.indices {
                    human_collect_expr_constants(&index.ty, out);
                }
                for constructor in &inductive.constructors {
                    human_collect_expr_constants(&constructor.ty, out);
                }
                if let Some(recursor) = &inductive.recursor {
                    human_collect_expr_constants(&recursor.ty, out);
                }
            }
        }
        Decl::Constructor { ty, .. } | Decl::Recursor { ty, .. } => {
            human_collect_expr_constants(ty, out);
        }
    }
}

fn human_collect_expr_constants(expr: &Expr, out: &mut BTreeSet<Name>) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            out.insert(Name::from_dotted(name));
        }
        Expr::App(fun, arg) => {
            human_collect_expr_constants(fun, out);
            human_collect_expr_constants(arg, out);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            human_collect_expr_constants(ty, out);
            human_collect_expr_constants(body, out);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            human_collect_expr_constants(ty, out);
            human_collect_expr_constants(value, out);
            human_collect_expr_constants(body, out);
        }
    }
}

fn human_expr_from_verified_term(
    module: &VerifiedModule,
    term: TermId,
) -> Result<Expr, HumanTheoremIndexError> {
    let term_node =
        module
            .term_table()
            .get(term)
            .ok_or_else(|| HumanTheoremIndexError::MissingTerm {
                module: module.module().clone(),
                term_index: term,
            })?;
    match term_node {
        TermNode::Sort(level) => Ok(Expr::sort(human_level_from_verified(module, *level)?)),
        TermNode::BVar(index) => Ok(Expr::bvar(*index)),
        TermNode::Const { global_ref, levels } => Ok(Expr::konst(
            human_global_ref_name_from_verified(module, global_ref)?,
            levels
                .iter()
                .map(|level| human_level_from_verified(module, *level))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        TermNode::App(fun, arg) => Ok(Expr::app(
            human_expr_from_verified_term(module, *fun)?,
            human_expr_from_verified_term(module, *arg)?,
        )),
        TermNode::Lam { ty, body } => Ok(Expr::lam(
            "_",
            human_expr_from_verified_term(module, *ty)?,
            human_expr_from_verified_term(module, *body)?,
        )),
        TermNode::Pi { ty, body } => Ok(Expr::pi(
            "_",
            human_expr_from_verified_term(module, *ty)?,
            human_expr_from_verified_term(module, *body)?,
        )),
        TermNode::Let { ty, value, body } => Ok(Expr::let_in(
            "_",
            human_expr_from_verified_term(module, *ty)?,
            human_expr_from_verified_term(module, *value)?,
            human_expr_from_verified_term(module, *body)?,
        )),
    }
}

fn human_level_from_verified(
    module: &VerifiedModule,
    level: LevelId,
) -> Result<Level, HumanTheoremIndexError> {
    let level_node =
        module
            .level_table()
            .get(level)
            .ok_or_else(|| HumanTheoremIndexError::MissingLevel {
                module: module.module().clone(),
                level_index: level,
            })?;
    match level_node {
        LevelNode::Zero => Ok(Level::zero()),
        LevelNode::Succ(inner) => Ok(Level::succ(human_level_from_verified(module, *inner)?)),
        LevelNode::Max(lhs, rhs) => Ok(Level::max(
            human_level_from_verified(module, *lhs)?,
            human_level_from_verified(module, *rhs)?,
        )),
        LevelNode::IMax(lhs, rhs) => Ok(Level::imax(
            human_level_from_verified(module, *lhs)?,
            human_level_from_verified(module, *rhs)?,
        )),
        LevelNode::Param(name) => Ok(Level::param(human_universe_param_from_verified(
            module, *name,
        )?)),
    }
}

fn human_global_ref_name_from_verified(
    module: &VerifiedModule,
    global_ref: &GlobalRef,
) -> Result<String, HumanTheoremIndexError> {
    match global_ref {
        GlobalRef::Builtin { name, .. }
        | GlobalRef::Imported { name, .. }
        | GlobalRef::LocalGenerated { name, .. } => {
            Ok(human_name_from_verified(module, *name)?.as_dotted())
        }
        GlobalRef::Local { decl_index } => {
            let decl = module.declarations().get(*decl_index).ok_or_else(|| {
                HumanTheoremIndexError::MissingDeclaration {
                    module: module.module().clone(),
                    decl_index: *decl_index,
                }
            })?;
            Ok(human_decl_payload_name(module, &decl.decl)?.as_dotted())
        }
    }
}

fn human_decl_payload_name(
    module: &VerifiedModule,
    decl: &DeclPayload,
) -> Result<Name, HumanTheoremIndexError> {
    let name = match decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    human_name_from_verified(module, name)
}

fn human_name_from_verified(
    module: &VerifiedModule,
    name: NameId,
) -> Result<Name, HumanTheoremIndexError> {
    module
        .name_table()
        .get(name)
        .cloned()
        .ok_or_else(|| HumanTheoremIndexError::MissingName {
            module: module.module().clone(),
            name_index: name,
        })
}

fn human_universe_param_from_verified(
    module: &VerifiedModule,
    name: NameId,
) -> Result<String, HumanTheoremIndexError> {
    human_name_from_verified(module, name)
        .map(|name| name.0.into_iter().collect::<Vec<_>>().join("."))
        .map_err(|_| HumanTheoremIndexError::MissingUniverseParam {
            module: module.module().clone(),
            name_index: name,
        })
}

fn human_sort_dedup_axiom_refs(entries: &mut Vec<MachineAxiomRefWire>) {
    entries.sort_by_key(encode_machine_axiom_ref_wire);
    entries.dedup_by(|lhs, rhs| {
        encode_machine_axiom_ref_wire(lhs) == encode_machine_axiom_ref_wire(rhs)
    });
}

fn human_sort_dedup_dependencies(entries: &mut Vec<HumanTheoremDependency>) {
    entries.sort_by_key(human_theorem_dependency_canonical_bytes);
    entries.dedup_by(|lhs, rhs| {
        human_theorem_dependency_canonical_bytes(lhs)
            == human_theorem_dependency_canonical_bytes(rhs)
    });
}

fn human_theorem_index_fingerprint(entries: &[HumanTheoremIndexEntry]) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.theorem-index.v1");
    human_encode_list_len(&mut out, entries.len());
    for entry in entries {
        out.extend(human_theorem_index_entry_canonical_bytes(entry));
    }
    human_sha256(&out)
}

fn human_theorem_index_entry_sort_key(entry: &HumanTheoremIndexEntry) -> Vec<u8> {
    let mut out = Vec::new();
    human_encode_name(&mut out, &entry.module);
    human_encode_name(&mut out, &entry.name);
    out.extend(entry.decl_interface_hash);
    human_encode_theorem_source(&mut out, &entry.source);
    out
}

fn human_theorem_index_entry_canonical_bytes(entry: &HumanTheoremIndexEntry) -> Vec<u8> {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.theorem-index-entry.v1");
    human_encode_name(&mut out, &entry.module);
    human_encode_name(&mut out, &entry.name);
    human_encode_theorem_source(&mut out, &entry.source);
    human_encode_list_len(&mut out, entry.universe_params.len());
    for param in &entry.universe_params {
        human_encode_string(&mut out, param);
    }
    human_encode_string(&mut out, entry.kind.as_str());
    out.extend(entry.statement.core_hash);
    human_encode_string(&mut out, &entry.statement_pretty);
    human_encode_option_name(&mut out, entry.head_symbol.as_ref());
    human_encode_list_len(&mut out, entry.constants.len());
    for constant in &entry.constants {
        human_encode_name(&mut out, constant);
    }
    human_encode_list_len(&mut out, entry.attributes.len());
    for attribute in &entry.attributes {
        human_encode_string(&mut out, attribute);
    }
    human_encode_list_len(&mut out, entry.dependencies.len());
    for dependency in &entry.dependencies {
        out.extend(human_theorem_dependency_canonical_bytes(dependency));
    }
    human_encode_list_len(&mut out, entry.axiom_dependencies.len());
    for axiom in &entry.axiom_dependencies {
        out.extend(encode_machine_axiom_ref_wire(axiom));
    }
    human_encode_option_hash(&mut out, entry.export_hash.as_ref());
    human_encode_option_hash(&mut out, entry.certificate_hash.as_ref());
    out.extend(entry.decl_interface_hash);
    out
}

fn human_theorem_dependency_canonical_bytes(dependency: &HumanTheoremDependency) -> Vec<u8> {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.theorem-dependency.v1");
    human_encode_string(&mut out, dependency.kind.as_str());
    human_encode_name(&mut out, &dependency.name);
    human_encode_option_name(&mut out, dependency.module.as_ref());
    human_encode_option_hash(&mut out, dependency.export_hash.as_ref());
    human_encode_option_u64(&mut out, dependency.source_index);
    human_encode_option_hash(&mut out, dependency.decl_interface_hash.as_ref());
    out
}

fn human_encode_theorem_source(out: &mut Vec<u8>, source: &HumanTheoremIndexSource) {
    match source {
        HumanTheoremIndexSource::VerifiedImport {
            export_hash,
            certificate_hash,
        } => {
            out.push(0x00);
            out.extend(export_hash);
            out.extend(certificate_hash);
        }
        HumanTheoremIndexSource::CheckedCurrentDecl { source_index } => {
            out.push(0x01);
            human_encode_uvar(out, *source_index);
        }
    }
}

fn human_encode_option_name(out: &mut Vec<u8>, value: Option<&Name>) {
    match value {
        Some(value) => {
            out.push(0x01);
            human_encode_name(out, value);
        }
        None => out.push(0x00),
    }
}

fn human_encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(value) => {
            out.push(0x01);
            out.extend(*value);
        }
        None => out.push(0x00),
    }
}

fn human_encode_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            out.push(0x01);
            human_encode_uvar(out, value);
        }
        None => out.push(0x00),
    }
}

fn human_encode_name(out: &mut Vec<u8>, name: &Name) {
    human_encode_list_len(out, name.0.len());
    for component in &name.0 {
        human_encode_string(out, component);
    }
}

fn human_encode_string(out: &mut Vec<u8>, value: &str) {
    human_encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn human_encode_bytes(out: &mut Vec<u8>, value: &[u8]) {
    human_encode_uvar(out, value.len() as u64);
    out.extend(value);
}

fn human_encode_list_len(out: &mut Vec<u8>, len: usize) {
    human_encode_uvar(out, len as u64);
}

fn human_encode_option_u32(out: &mut Vec<u8>, value: Option<u32>) {
    match value {
        Some(value) => {
            out.push(0x01);
            human_encode_uvar(out, u64::from(value));
        }
        None => out.push(0x00),
    }
}

fn human_formalization_text_hash(tag: &str, value: &str) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, tag);
    human_encode_string(&mut out, value);
    human_sha256(&out)
}

fn human_formalization_text_list_hash(tag: &str, values: &[String]) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, tag);
    human_encode_list_len(&mut out, values.len());
    for value in values {
        human_encode_string(&mut out, value);
    }
    human_sha256(&out)
}

fn human_encode_formalization_review_status(
    out: &mut Vec<u8>,
    status: &HumanFormalizationReviewStatus,
) {
    match status {
        HumanFormalizationReviewStatus::MissingIntent => out.push(0),
        HumanFormalizationReviewStatus::Unreviewed => out.push(1),
        HumanFormalizationReviewStatus::Reviewed {
            reviewer,
            accepted_statement_hash,
        } => {
            out.push(2);
            human_encode_advanced_reviewer_id(out, reviewer);
            out.extend(accepted_statement_hash);
        }
        HumanFormalizationReviewStatus::Rejected {
            reviewer,
            rejection_reason_hash,
        } => {
            out.push(3);
            human_encode_advanced_reviewer_id(out, reviewer);
            out.extend(rejection_reason_hash);
        }
        HumanFormalizationReviewStatus::MalformedRequest => out.push(4),
    }
}

fn human_encode_advanced_reviewer_id(out: &mut Vec<u8>, reviewer: &crate::AdvancedReviewerId) {
    match reviewer {
        crate::AdvancedReviewerId::Human { stable_id_ascii } => {
            out.push(0);
            human_encode_bytes(out, stable_id_ascii);
        }
        crate::AdvancedReviewerId::System {
            system_id_ascii,
            actor_id_ascii,
        } => {
            out.push(1);
            human_encode_bytes(out, system_id_ascii);
            human_encode_bytes(out, actor_id_ascii);
        }
    }
}

fn human_encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn human_sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn build_human_document_incremental_cache(
    document: &HumanDocumentSnapshot,
    collection: &HumanSessionDocumentCollection,
    prior: Option<&HumanDocumentIncrementalCache>,
) -> HumanDocumentIncrementalCache {
    let import_interface_hash = human_document_import_interface_hash(document, collection);
    let mut declarations = Vec::new();
    if let Some(source_interface) = &collection.source_interface {
        for (source_index, decl) in source_interface
            .declarations
            .iter()
            .filter(|decl| decl.kind != npa_frontend::HumanSourceDeclarationKind::Imported)
            .enumerate()
        {
            let source_decl_hash = human_document_source_decl_hash(document, decl);
            let resolved_decl_hash =
                human_document_resolved_decl_hash(import_interface_hash, source_decl_hash, decl);
            let core_decl_hash = human_document_core_decl_hash(resolved_decl_hash, decl);
            declarations.push(HumanDocumentIncrementalDeclCacheEntry {
                source_index: source_index as u64,
                source_decl_hash,
                resolved_decl_hash,
                core_decl_hash,
                reuse: HumanDocumentIncrementalDeclReuse::Fresh,
            });
        }
    }

    let prior_for_reuse = prior.filter(|prior| {
        prior.document_id == document.document_id
            && prior.document_version.next() == Some(document.document_version)
            && prior.import_interface_hash == import_interface_hash
    });
    let reused_prefix_len = prior_for_reuse
        .map(|prior| {
            declarations
                .iter()
                .zip(&prior.declarations)
                .take_while(|(current, previous)| {
                    current.source_index == previous.source_index
                        && current.source_decl_hash == previous.source_decl_hash
                })
                .count()
        })
        .unwrap_or(0);
    if let Some(prior) = prior_for_reuse {
        for (current, previous) in declarations
            .iter_mut()
            .zip(&prior.declarations)
            .take(reused_prefix_len)
        {
            current.resolved_decl_hash = previous.resolved_decl_hash;
            current.core_decl_hash = previous.core_decl_hash;
            current.reuse = HumanDocumentIncrementalDeclReuse::Reused;
        }
    }

    let prior_len = prior.map(|prior| prior.declarations.len()).unwrap_or(0);
    let suffix_changed = match prior_for_reuse {
        Some(_) => reused_prefix_len < declarations.len() || prior_len != declarations.len(),
        None => !declarations.is_empty() || prior_len != 0,
    };

    HumanDocumentIncrementalCache {
        document_id: document.document_id.clone(),
        document_version: document.document_version,
        import_interface_hash,
        prior_document_version: prior.map(|prior| prior.document_version),
        prior_import_interface_hash: prior.map(|prior| prior.import_interface_hash),
        reused_prefix_len: reused_prefix_len as u64,
        recomputed_from: suffix_changed.then_some(reused_prefix_len as u64),
        declarations,
    }
}

fn reuse_human_document_incremental_prefix(
    collection: &mut HumanSessionDocumentCollection,
    prior_source_interface: Option<&npa_frontend::HumanSourceInterface>,
    reused_prefix_len: u64,
) {
    if reused_prefix_len == 0 {
        return;
    }
    let (Some(current), Some(prior)) =
        (collection.source_interface.as_mut(), prior_source_interface)
    else {
        return;
    };

    for (current_decl, prior_decl) in current
        .declarations
        .iter_mut()
        .filter(|decl| decl.kind != npa_frontend::HumanSourceDeclarationKind::Imported)
        .zip(
            prior
                .declarations
                .iter()
                .filter(|decl| decl.kind != npa_frontend::HumanSourceDeclarationKind::Imported),
        )
        .take(reused_prefix_len as usize)
    {
        *current_decl = prior_decl.clone();
    }
}

fn human_document_import_interface_hash(
    document: &HumanDocumentSnapshot,
    collection: &HumanSessionDocumentCollection,
) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.document-import-interface.v1");
    human_encode_name(&mut out, &document.current_module);
    human_encode_uvar(&mut out, document.file_id.0 as u64);
    human_encode_human_api_options(&mut out, &document.options);
    human_encode_list_len(&mut out, document.verified_modules.len());
    for verified in &document.verified_modules {
        human_encode_name(&mut out, verified.module());
        out.extend(verified.export_hash());
        out.extend(verified.certificate_hash());
    }
    human_encode_list_len(&mut out, document.imported_source_interfaces.len());
    for interface in &document.imported_source_interfaces {
        human_encode_imported_source_interface(&mut out, interface);
    }
    human_encode_list_len(&mut out, collection.active_imports.len());
    for interface in &collection.active_imports {
        human_encode_imported_source_interface(&mut out, interface);
    }
    human_sha256(&out)
}

fn human_document_source_decl_hash(
    document: &HumanDocumentSnapshot,
    decl: &npa_frontend::HumanSourceDeclarationMetadata,
) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.document-source-decl.v1");
    human_encode_string(&mut out, human_source_declaration_kind_str(decl.kind));
    human_encode_human_name(&mut out, &decl.name);
    human_encode_span(&mut out, decl.span);
    match human_document_source_prefix_slice(document, decl.span) {
        Some(source_prefix) => {
            out.push(0x01);
            human_encode_string(&mut out, source_prefix);
        }
        None => {
            out.push(0x00);
            human_encode_source_decl_metadata(&mut out, decl, true);
        }
    }
    human_sha256(&out)
}

fn human_document_resolved_decl_hash(
    import_interface_hash: Hash,
    source_decl_hash: Hash,
    decl: &npa_frontend::HumanSourceDeclarationMetadata,
) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.document-resolved-decl.v1");
    out.extend(import_interface_hash);
    out.extend(source_decl_hash);
    human_encode_source_decl_metadata(&mut out, decl, false);
    human_sha256(&out)
}

fn human_document_core_decl_hash(
    resolved_decl_hash: Hash,
    decl: &npa_frontend::HumanSourceDeclarationMetadata,
) -> Hash {
    let mut out = Vec::new();
    human_encode_string(&mut out, "npa.human-api.document-core-decl.v1");
    out.extend(resolved_decl_hash);
    human_encode_option_hash(&mut out, decl.decl_interface_hash.as_ref());
    human_sha256(&out)
}

fn human_document_source_prefix_slice(
    document: &HumanDocumentSnapshot,
    span: npa_frontend::Span,
) -> Option<&str> {
    if span.file_id != document.file_id {
        return None;
    }
    let end = usize::try_from(span.end.0).ok()?;
    document.source.get(..end)
}

fn human_encode_human_api_options(out: &mut Vec<u8>, options: &HumanApiCompileOptions) {
    human_encode_string(out, "npa.human-api.compile-options.v2");
    human_encode_uvar(out, options.max_notation_candidates as u64);
    human_encode_string(out, options.kernel_profile.as_str());
    let tactic = &options.tactic_options;
    human_encode_list_len(out, tactic.simp_rules.len());
    for rule in &tactic.simp_rules {
        human_encode_name(out, &rule.name);
        out.extend(rule.decl_interface_hash);
        human_encode_string(
            out,
            match rule.direction {
                npa_tactic::RewriteDirection::Forward => "forward",
                npa_tactic::RewriteDirection::Backward => "backward",
            },
        );
    }
    human_encode_uvar(out, tactic.max_simp_rewrite_steps);
    human_encode_uvar(out, tactic.max_open_goals as u64);
    human_encode_uvar(out, tactic.max_metas as u64);
    human_encode_option_eq_family_ref(out, tactic.eq_family.as_ref());
    human_encode_option_nat_family_ref(out, tactic.nat_family.as_ref());
}

fn human_encode_option_eq_family_ref(out: &mut Vec<u8>, value: Option<&npa_tactic::EqFamilyRef>) {
    match value {
        Some(value) => {
            out.push(0x01);
            human_encode_name(out, &value.eq_name);
            out.extend(value.eq_interface_hash);
            human_encode_name(out, &value.refl_name);
            out.extend(value.refl_interface_hash);
            human_encode_name(out, &value.rec_name);
            out.extend(value.rec_interface_hash);
        }
        None => out.push(0x00),
    }
}

fn human_encode_option_nat_family_ref(out: &mut Vec<u8>, value: Option<&npa_tactic::NatFamilyRef>) {
    match value {
        Some(value) => {
            out.push(0x01);
            human_encode_name(out, &value.nat_name);
            out.extend(value.nat_interface_hash);
            human_encode_name(out, &value.zero_name);
            out.extend(value.zero_interface_hash);
            human_encode_name(out, &value.succ_name);
            out.extend(value.succ_interface_hash);
            human_encode_name(out, &value.rec_name);
            out.extend(value.rec_interface_hash);
        }
        None => out.push(0x00),
    }
}

fn human_encode_imported_source_interface(
    out: &mut Vec<u8>,
    interface: &npa_frontend::HumanImportedSourceInterface,
) {
    human_encode_name(out, &interface.module);
    out.extend(interface.export_hash);
    human_encode_option_hash(out, interface.certificate_hash.as_ref());
    human_encode_source_interface_metadata(out, &interface.source_interface);
}

fn human_encode_source_interface_metadata(
    out: &mut Vec<u8>,
    interface: &npa_frontend::HumanSourceInterface,
) {
    human_encode_name(out, &interface.module);
    human_encode_list_len(out, interface.declarations.len());
    for decl in &interface.declarations {
        human_encode_source_decl_metadata(out, decl, false);
    }
    human_encode_list_len(out, interface.notations.len());
    for notation in &interface.notations {
        human_encode_string(out, human_notation_kind_str(notation.kind));
        human_encode_string(
            out,
            human_notation_associativity_str(notation.associativity),
        );
        human_encode_uvar(out, notation.precedence as u64);
        human_encode_string(out, &notation.token);
        human_encode_human_name(out, &notation.target);
        human_encode_list_len(out, notation.namespace.len());
        for component in &notation.namespace {
            human_encode_string(out, component);
        }
    }
    human_encode_list_len(out, interface.generated_declarations.len());
    for generated in &interface.generated_declarations {
        human_encode_string(
            out,
            match generated.kind {
                npa_frontend::HumanGeneratedDeclarationKind::Constructor => "constructor",
                npa_frontend::HumanGeneratedDeclarationKind::Recursor => "recursor",
            },
        );
        human_encode_human_name(out, &generated.parent);
        human_encode_human_name(out, &generated.name);
        human_encode_option_hash(out, generated.decl_interface_hash.as_ref());
    }
    human_encode_list_len(out, interface.typeclass_classes.len());
    for class in &interface.typeclass_classes {
        human_encode_human_name(out, &class.name);
        human_encode_human_name(out, &class.constructor);
        human_encode_list_len(out, class.fields.len());
        for field in &class.fields {
            human_encode_human_name(out, &field.name);
            human_encode_human_name(out, &field.projection);
            human_encode_option_hash(out, field.decl_interface_hash.as_ref());
        }
        human_encode_option_hash(out, class.decl_interface_hash.as_ref());
    }
    human_encode_list_len(out, interface.typeclass_instances.len());
    for instance in &interface.typeclass_instances {
        human_encode_human_name(out, &instance.name);
        match &instance.class {
            Some(class) => {
                out.push(0x01);
                human_encode_human_name(out, class);
            }
            None => out.push(0x00),
        }
        human_encode_uvar(out, instance.priority as u64);
        human_encode_option_hash(out, instance.decl_interface_hash.as_ref());
    }
}

fn human_encode_source_decl_metadata(
    out: &mut Vec<u8>,
    decl: &npa_frontend::HumanSourceDeclarationMetadata,
    include_span: bool,
) {
    human_encode_string(out, human_source_declaration_kind_str(decl.kind));
    human_encode_human_name(out, &decl.name);
    human_encode_list_len(out, decl.universe_params.len());
    for param in &decl.universe_params {
        human_encode_string(out, &param.name);
        if include_span {
            human_encode_span(out, param.span);
        }
    }
    human_encode_list_len(out, decl.binders.len());
    for binder in &decl.binders {
        match &binder.name {
            Some(name) => {
                out.push(0x01);
                human_encode_human_name(out, name);
            }
            None => out.push(0x00),
        }
        human_encode_string(out, human_binder_info_str(binder.binder_info));
        if include_span {
            human_encode_span(out, binder.span);
        }
    }
    human_encode_option_hash(out, decl.decl_interface_hash.as_ref());
    if include_span {
        human_encode_span(out, decl.span);
    }
}

fn human_encode_human_name(out: &mut Vec<u8>, name: &npa_frontend::HumanName) {
    human_encode_list_len(out, name.parts.len());
    for component in &name.parts {
        human_encode_string(out, component);
    }
}

fn human_encode_span(out: &mut Vec<u8>, span: npa_frontend::Span) {
    human_encode_uvar(out, span.file_id.0 as u64);
    human_encode_uvar(out, span.start.0 as u64);
    human_encode_uvar(out, span.end.0 as u64);
}

fn human_source_declaration_kind_str(
    kind: npa_frontend::HumanSourceDeclarationKind,
) -> &'static str {
    match kind {
        npa_frontend::HumanSourceDeclarationKind::Def => "def",
        npa_frontend::HumanSourceDeclarationKind::Theorem => "theorem",
        npa_frontend::HumanSourceDeclarationKind::Axiom => "axiom",
        npa_frontend::HumanSourceDeclarationKind::Inductive => "inductive",
        npa_frontend::HumanSourceDeclarationKind::Class => "class",
        npa_frontend::HumanSourceDeclarationKind::ClassField => "class-field",
        npa_frontend::HumanSourceDeclarationKind::Instance => "instance",
        npa_frontend::HumanSourceDeclarationKind::Imported => "imported",
    }
}

fn human_binder_info_str(info: npa_frontend::HumanBinderInfo) -> &'static str {
    match info {
        npa_frontend::HumanBinderInfo::Explicit => "explicit",
        npa_frontend::HumanBinderInfo::Implicit => "implicit",
    }
}

fn human_notation_kind_str(kind: npa_frontend::HumanNotationKind) -> &'static str {
    match kind {
        npa_frontend::HumanNotationKind::Notation => "notation",
        npa_frontend::HumanNotationKind::Prefix => "prefix",
        npa_frontend::HumanNotationKind::Postfix => "postfix",
        npa_frontend::HumanNotationKind::Infix => "infix",
        npa_frontend::HumanNotationKind::Infixl => "infixl",
        npa_frontend::HumanNotationKind::Infixr => "infixr",
    }
}

fn human_notation_associativity_str(
    associativity: npa_frontend::HumanNotationAssociativity,
) -> &'static str {
    match associativity {
        npa_frontend::HumanNotationAssociativity::Left => "left",
        npa_frontend::HumanNotationAssociativity::Right => "right",
        npa_frontend::HumanNotationAssociativity::NonAssoc => "non_assoc",
    }
}

#[derive(Clone, Debug)]
struct HumanSessionDocumentCollection {
    source_interface: Option<npa_frontend::HumanSourceInterface>,
    active_imports: Vec<npa_frontend::HumanImportedSourceInterface>,
    messages: Vec<npa_frontend::HumanDiagnostic>,
}

fn collect_human_session_document(
    document: &HumanDocumentSnapshot,
) -> HumanSessionDocumentCollection {
    let frontend_options = npa_frontend::HumanCompileOptions::from(&document.options);
    let verified_imports: Vec<_> = document
        .verified_modules
        .iter()
        .map(npa_frontend::VerifiedImport::from)
        .collect();
    match npa_frontend::collect_human_by_proof_targets_with_source_interfaces(
        document.file_id,
        document.current_module.clone(),
        &document.source,
        &verified_imports,
        &document.imported_source_interfaces,
        &frontend_options,
    ) {
        Ok(output) => HumanSessionDocumentCollection {
            source_interface: Some(output.source_interface),
            active_imports: output.active_imports,
            messages: Vec::new(),
        },
        Err(diagnostic) => HumanSessionDocumentCollection {
            source_interface: None,
            active_imports: Vec::new(),
            messages: vec![diagnostic],
        },
    }
}

#[derive(Clone, Debug)]
struct HumanCompileCoreWithTacticProofsOk {
    core_module: npa_cert::CoreModule,
    source_interface: npa_frontend::HumanSourceInterface,
    active_imports: Vec<npa_frontend::HumanImportedSourceInterface>,
}

fn compile_human_source_to_core_with_tactic_proofs(
    current_module: npa_cert::ModuleName,
    current_source: HumanCurrentModuleSource<'_>,
    verified_modules: &[npa_cert::VerifiedModule],
    imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
    options: HumanApiCompileOptions,
) -> Result<HumanCompileCoreWithTacticProofsOk, HumanCompileError> {
    let frontend_options = npa_frontend::HumanCompileOptions::from(&options);
    let verified_imports: Vec<_> = verified_modules
        .iter()
        .map(npa_frontend::VerifiedImport::from)
        .collect();
    let by_targets = npa_frontend::collect_human_by_proof_targets_with_source_interfaces(
        current_source.file_id,
        current_module.clone(),
        current_source.source,
        &verified_imports,
        imported_source_interfaces,
        &frontend_options,
    )?;

    if by_targets.targets.is_empty() {
        let output = npa_frontend::compile_human_source_to_core_output_with_source_interfaces(
            current_source.file_id,
            current_module,
            current_source.source,
            &verified_imports,
            imported_source_interfaces,
            &frontend_options,
        )?;
        return Ok(HumanCompileCoreWithTacticProofsOk {
            core_module: output.core_module,
            source_interface: output.source_interface,
            active_imports: Vec::new(),
        });
    }

    let mut by_proofs = Vec::with_capacity(by_targets.targets.len());
    for target in &by_targets.targets {
        let prepared =
            npa_frontend::prepare_human_proof_start_core_with_source_interfaces_and_by_proofs(
                npa_frontend::HumanProofStartCoreWithProofsRequest {
                    file_id: current_source.file_id,
                    module_name: current_module.clone(),
                    theorem_name: target.theorem_name.clone(),
                    source: current_source.source,
                    verified_imports: &verified_imports,
                    imported_source_interfaces,
                    prior_by_proofs: &by_proofs,
                    options: &frontend_options,
                },
            )?;
        let started = start_human_proof_from_prepared(prepared, verified_modules, options.clone())
            .map_err(human_compile_start_error)?;
        let run = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &target.script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces,
            options: options.clone(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .map_err(|error| human_compile_script_error(error, target.script.span))?;
        by_proofs.push(npa_frontend::HumanByProofCore {
            source_index: target.source_index,
            proof: run.proof,
        });
    }

    let output =
        npa_frontend::compile_human_source_to_core_output_with_source_interfaces_and_by_proofs(
            current_source.file_id,
            current_module,
            current_source.source,
            &verified_imports,
            imported_source_interfaces,
            &by_proofs,
            &frontend_options,
        )?;

    Ok(HumanCompileCoreWithTacticProofsOk {
        core_module: output.core_module,
        source_interface: output.source_interface,
        active_imports: by_targets.active_imports,
    })
}

fn start_human_proof_from_prepared(
    prepared: npa_frontend::HumanProofStartCoreOutput,
    verified_modules: &[npa_cert::VerifiedModule],
    options: HumanApiCompileOptions,
) -> Result<HumanStartProofOk, HumanStartProofError> {
    let machine_tactic_imports =
        active_human_verified_import_refs(verified_modules, &prepared.active_imports)?;
    let mut checked_current_decls = Vec::with_capacity(prepared.proof.prior_declarations.len());
    for (source_index, decl) in prepared
        .proof
        .prior_declarations
        .iter()
        .cloned()
        .enumerate()
    {
        let checked =
            npa_tactic::check_current_decl_for_machine_tactic_from_verified_imports_with_kernel_profile(
                options.kernel_profile,
                &machine_tactic_imports,
                &checked_current_decls,
                source_index as u64,
                decl,
            )?;
        checked_current_decls.push(checked);
    }

    let state = npa_tactic::start_machine_proof_with_kernel_profile(
        options.kernel_profile,
        npa_tactic::MachineProofSpec {
            module: prepared.proof.module,
            theorem_name: prepared.proof.theorem_name,
            source_index: prepared.proof.source_index,
            universe_params: prepared.proof.universe_params,
            theorem_type: prepared.proof.theorem_type,
        },
        machine_tactic_imports,
        checked_current_decls,
        options.tactic_options.clone(),
    )?;
    npa_tactic::validate_machine_proof_state(&state)?;

    Ok(HumanStartProofOk {
        state,
        source_interface: prepared.source_interface,
    })
}

fn human_build_and_verify_certificate(
    core_module: npa_cert::CoreModule,
    certificate_imports: &[npa_cert::VerifiedModule],
    source: HumanCurrentModuleSource<'_>,
) -> Result<npa_cert::ModuleCert, HumanCompileError> {
    let certificate =
        npa_cert::build_module_cert(core_module, certificate_imports).map_err(|err| {
            npa_frontend::HumanDiagnostic::error(
                npa_frontend::HumanDiagnosticKind::KernelRejected,
                human_source_span(source),
                format!("certificate certificate handoff rejected Human by proof source: {err:?}"),
            )
            .with_phase(npa_frontend::HumanDiagnosticPhase::CertificateHandoff)
        })?;
    let bytes = npa_cert::encode_module_cert(&certificate).map_err(|err| {
        npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::KernelRejected,
            human_source_span(source),
            format!("certificate certificate encoding rejected Human by proof source: {err:?}"),
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::CertificateHandoff)
    })?;
    let mut session = npa_cert::VerifierSession::new();
    for import in certificate_imports {
        session.register_verified_module(import.clone());
    }
    npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal()).map_err(
        |err| {
            npa_frontend::HumanDiagnostic::error(
                npa_frontend::HumanDiagnosticKind::KernelRejected,
                human_source_span(source),
                format!(
                    "certificate certificate verification rejected Human by proof source: {err:?}"
                ),
            )
            .with_phase(npa_frontend::HumanDiagnosticPhase::CertificateHandoff)
        },
    )?;
    Ok(certificate)
}

fn human_compile_start_error(error: HumanStartProofError) -> HumanCompileError {
    match error {
        HumanStartProofError::Human(error) => error,
        HumanStartProofError::Machine(diagnostic) => human_compile_machine_tactic_diagnostic(
            diagnostic,
            npa_frontend::Span::empty(npa_frontend::FileId(0)),
        ),
    }
}

fn human_compile_script_error(
    error: HumanTacticScriptError,
    span: npa_frontend::Span,
) -> HumanCompileError {
    match error {
        HumanTacticScriptError::Human(error) => error,
        HumanTacticScriptError::Machine(diagnostic) => {
            human_compile_machine_tactic_diagnostic(diagnostic, span)
        }
    }
}

fn human_compile_machine_tactic_diagnostic(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    span: npa_frontend::Span,
) -> HumanCompileError {
    human_tactic_machine_diagnostic(
        &diagnostic,
        span,
        None,
        None,
        format!(
            "Human by proof tactic execution failed before certificate handoff: {:?}: {}",
            &diagnostic.kind, diagnostic.message
        ),
    )
    .into()
}

fn human_source_span(source: HumanCurrentModuleSource<'_>) -> npa_frontend::Span {
    npa_frontend::Span::new(source.file_id, 0, source.source.len() as u32)
}

fn human_source_interface_with_certificate_hashes(
    mut source_interface: npa_frontend::HumanSourceInterface,
    cert: &npa_cert::ModuleCert,
) -> npa_frontend::HumanSourceInterface {
    let module_name = source_interface.module.clone();
    let export_hashes: BTreeMap<_, _> = cert
        .export_block
        .iter()
        .map(|entry| {
            (
                cert.name_table[entry.name].clone(),
                entry.decl_interface_hash,
            )
        })
        .collect();

    for decl in &mut source_interface.declarations {
        let name = npa_cert::Name(decl.name.parts.clone());
        if let Some(hash) = export_hashes
            .get(&name)
            .or_else(|| export_hashes.get(&human_prefixed_current_name(&module_name, &name)))
        {
            decl.decl_interface_hash = Some(*hash);
        }
    }

    for generated in &mut source_interface.generated_declarations {
        let name = npa_cert::Name(generated.name.parts.clone());
        if let Some(hash) = export_hashes
            .get(&name)
            .or_else(|| export_hashes.get(&human_prefixed_current_name(&module_name, &name)))
        {
            generated.decl_interface_hash = Some(*hash);
        }
    }

    for class in &mut source_interface.typeclass_classes {
        let name = npa_cert::Name(class.name.parts.clone());
        if let Some(hash) = export_hashes
            .get(&name)
            .or_else(|| export_hashes.get(&human_prefixed_current_name(&module_name, &name)))
        {
            class.decl_interface_hash = Some(*hash);
        }
        for field in &mut class.fields {
            let name = npa_cert::Name(field.projection.parts.clone());
            if let Some(hash) = export_hashes
                .get(&name)
                .or_else(|| export_hashes.get(&human_prefixed_current_name(&module_name, &name)))
            {
                field.decl_interface_hash = Some(*hash);
            }
        }
    }

    for instance in &mut source_interface.typeclass_instances {
        let name = npa_cert::Name(instance.name.parts.clone());
        if let Some(hash) = export_hashes
            .get(&name)
            .or_else(|| export_hashes.get(&human_prefixed_current_name(&module_name, &name)))
        {
            instance.decl_interface_hash = Some(*hash);
        }
    }

    source_interface
}

fn human_prefixed_current_name(
    module_name: &npa_cert::ModuleName,
    name: &npa_cert::Name,
) -> npa_cert::Name {
    if name.0.len() > module_name.0.len() && name.0.starts_with(&module_name.0) {
        return name.clone();
    }

    let mut parts = module_name.0.clone();
    parts.extend(name.0.iter().cloned());
    npa_cert::Name(parts)
}

fn human_tactic_goal_payload(
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> npa_frontend::HumanDiagnosticPayload {
    npa_frontend::HumanDiagnosticPayload {
        hole_goals: vec![human_tactic_goal_display(goal, span)],
        ..npa_frontend::HumanDiagnosticPayload::default()
    }
}

fn human_tactic_goal_display(
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> npa_frontend::HumanHoleGoal {
    let mut local_names = Vec::with_capacity(goal.context.len());
    let mut context = Vec::with_capacity(goal.context.len());
    for local in &goal.context {
        let ty = human_render_core_expr(&local.ty, &local_names);
        let value = local
            .value
            .as_ref()
            .map(|value| human_render_core_expr(value, &local_names));
        context.push(npa_frontend::HumanHoleGoalLocal {
            name: local.name.clone(),
            ty,
            value,
        });
        local_names.push(local.name.clone());
    }

    npa_frontend::HumanHoleGoal {
        hole: Some(format!("g{}", goal.id.0)),
        context,
        target: Some(human_render_core_expr(&goal.target, &local_names)),
        source_span: span,
    }
}

fn human_render_core_expr(expr: &Expr, local_names: &[String]) -> String {
    let mut names = local_names.to_vec();
    human_render_core_expr_with_names(expr, &mut names, 0)
}

fn human_structured_expr_pretty(expr: &Expr, local_names: &[String]) -> String {
    if let Some((lhs, rhs)) = human_eq_app_sides(expr) {
        return format!(
            "{} = {}",
            human_render_core_expr(lhs, local_names),
            human_render_core_expr(rhs, local_names)
        );
    }
    human_render_core_expr(expr, local_names)
}

fn human_eq_app_sides(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let (head, args) = human_app_head_and_args(expr);
    let Expr::Const { name, .. } = head else {
        return None;
    };
    if name != "Eq" || args.len() != 3 {
        return None;
    }
    Some((args[1], args[2]))
}

fn human_app_head_and_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(func, arg) = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}

fn human_render_core_expr_with_names(
    expr: &Expr,
    local_names: &mut Vec<String>,
    parent_prec: u8,
) -> String {
    const PREC_BINDER: u8 = 10;
    const PREC_APP: u8 = 80;
    const PREC_ATOM: u8 = 100;

    let (rendered, prec) = match expr {
        Expr::Sort(level) => (human_render_sort(level), PREC_ATOM),
        Expr::BVar(index) => {
            let index = *index as usize;
            let name = local_names
                .len()
                .checked_sub(index + 1)
                .and_then(|local_index| local_names.get(local_index))
                .cloned()
                .unwrap_or_else(|| format!("#{index}"));
            (name, PREC_ATOM)
        }
        Expr::Const { name, levels } => {
            let rendered = if levels.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}.{{{}}}",
                    name,
                    levels
                        .iter()
                        .map(human_render_level)
                        .collect::<Vec<_>>()
                        .join(",")
                )
            };
            (rendered, PREC_ATOM)
        }
        Expr::App(_, _) => {
            let mut parts = Vec::new();
            human_collect_app_parts(expr, local_names, &mut parts);
            (parts.join(" "), PREC_APP)
        }
        Expr::Lam { binder, ty, body } => {
            let binder = human_fresh_binder_name(binder, local_names);
            let ty = human_render_core_expr_with_names(ty, local_names, 0);
            local_names.push(binder.clone());
            let body = human_render_core_expr_with_names(body, local_names, 0);
            local_names.pop();
            (format!("fun ({binder} : {ty}) => {body}"), PREC_BINDER)
        }
        Expr::Pi { binder, ty, body } => {
            let binder = human_fresh_binder_name(binder, local_names);
            let ty = human_render_core_expr_with_names(ty, local_names, 0);
            local_names.push(binder.clone());
            let body = human_render_core_expr_with_names(body, local_names, 0);
            local_names.pop();
            (format!("forall ({binder} : {ty}), {body}"), PREC_BINDER)
        }
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => {
            let binder = human_fresh_binder_name(binder, local_names);
            let ty = human_render_core_expr_with_names(ty, local_names, 0);
            let value = human_render_core_expr_with_names(value, local_names, 0);
            local_names.push(binder.clone());
            let body = human_render_core_expr_with_names(body, local_names, 0);
            local_names.pop();
            (
                format!("let {binder} : {ty} := {value} in {body}"),
                PREC_BINDER,
            )
        }
    };

    if prec < parent_prec {
        format!("({rendered})")
    } else {
        rendered
    }
}

fn human_collect_app_parts(expr: &Expr, local_names: &mut Vec<String>, parts: &mut Vec<String>) {
    match expr {
        Expr::App(func, arg) => {
            human_collect_app_parts(func, local_names, parts);
            parts.push(human_render_core_expr_with_names(arg, local_names, 100));
        }
        _ => parts.push(human_render_core_expr_with_names(expr, local_names, 80)),
    }
}

fn human_fresh_binder_name(base: &str, local_names: &[String]) -> String {
    let candidate = if base.is_empty() || base == "_" {
        "x".to_owned()
    } else {
        base.to_owned()
    };
    if !local_names.iter().any(|name| name == &candidate) {
        return candidate;
    }
    for index in 1.. {
        let fresh = format!("{candidate}{index}");
        if !local_names.iter().any(|name| name == &fresh) {
            return fresh;
        }
    }
    unreachable!("unbounded fresh-name search should return");
}

fn human_render_sort(level: &Level) -> String {
    match level {
        Level::Zero => "Prop".to_owned(),
        Level::Succ(inner) if matches!(inner.as_ref(), Level::Zero) => "Type".to_owned(),
        Level::Succ(inner) => format!("Type {}", human_render_level(inner)),
        _ => format!("Sort {}", human_render_level(level)),
    }
}

fn human_render_level(level: &Level) -> String {
    match level {
        Level::Zero => "0".to_owned(),
        Level::Succ(inner) => format!("succ {}", human_render_level(inner)),
        Level::Max(lhs, rhs) => {
            format!(
                "max {} {}",
                human_render_level(lhs),
                human_render_level(rhs)
            )
        }
        Level::IMax(lhs, rhs) => {
            format!(
                "imax {} {}",
                human_render_level(lhs),
                human_render_level(rhs)
            )
        }
        Level::Param(name) => name.clone(),
    }
}

fn human_tactic_machine_kind(
    diagnostic: &npa_tactic::MachineTacticDiagnostic,
) -> npa_frontend::HumanDiagnosticKind {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::AmbiguousApplyArgument
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousRewriteRule
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedEqTarget
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedFunctionType
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedPiTarget
        | npa_tactic::MachineTacticDiagnosticKind::InvalidMetaDependency
        | npa_tactic::MachineTacticDiagnosticKind::MissingExplicitArgument
        | npa_tactic::MachineTacticDiagnosticKind::ProofExprTypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::SubgoalDataArgument
        | npa_tactic::MachineTacticDiagnosticKind::TooFewApplyArguments
        | npa_tactic::MachineTacticDiagnosticKind::TooManyApplyArguments
        | npa_tactic::MachineTacticDiagnosticKind::TypeMismatch => {
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        }
        npa_tactic::MachineTacticDiagnosticKind::AmbiguousLocalName
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousTacticHead => {
            npa_frontend::HumanDiagnosticKind::AmbiguousName
        }
        npa_tactic::MachineTacticDiagnosticKind::UnknownLocalName
        | npa_tactic::MachineTacticDiagnosticKind::UnknownName
        | npa_tactic::MachineTacticDiagnosticKind::UnknownTacticHead => {
            npa_frontend::HumanDiagnosticKind::UnknownIdentifier
        }
        npa_tactic::MachineTacticDiagnosticKind::InvalidInductionTarget
        | npa_tactic::MachineTacticDiagnosticKind::InvalidLocalHead
        | npa_tactic::MachineTacticDiagnosticKind::InvalidMachineTactic
        | npa_tactic::MachineTacticDiagnosticKind::TacticPrimitiveUnavailable
        | npa_tactic::MachineTacticDiagnosticKind::UnsupportedMachineTactic => {
            npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        }
        npa_tactic::MachineTacticDiagnosticKind::UnresolvedGoal => {
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal
        }
        npa_tactic::MachineTacticDiagnosticKind::KernelRejected => {
            npa_frontend::HumanDiagnosticKind::KernelRejected
        }
        _ => npa_frontend::HumanDiagnosticKind::MachineElaborationError,
    }
}

fn human_tactic_machine_diagnostic(
    diagnostic: &npa_tactic::MachineTacticDiagnostic,
    span: npa_frontend::Span,
    goal: Option<&npa_tactic::MachineGoal>,
    kind: Option<npa_frontend::HumanDiagnosticKind>,
    message: impl Into<String>,
) -> npa_frontend::HumanDiagnostic {
    let kind = kind.unwrap_or_else(|| human_tactic_machine_kind(diagnostic));
    let mut human = npa_frontend::HumanDiagnostic::error(kind, span, message)
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticExecution);
    if let Some(goal) = goal {
        human = human.with_payload(human_tactic_goal_payload(goal, span));
    }
    human
}

fn human_tactic_validation_diagnostic_with_goal(
    mut diagnostic: npa_frontend::HumanDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> npa_frontend::HumanDiagnostic {
    diagnostic = diagnostic.with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation);
    diagnostic.with_payload(human_tactic_goal_payload(goal, span))
}

pub fn check_human_tactic_term(
    request: HumanTacticTermCheckRequest<'_, '_>,
) -> Result<HumanTacticTermCheckOk, HumanTacticTermError> {
    let frontend_options = npa_frontend::HumanCompileOptions::from(&request.options);
    let goal = request.state.goal(request.goal_id)?;
    let direct_imports = request
        .state
        .env
        .imports
        .iter()
        .filter(|import| import.is_visible())
        .map(frontend_import_from_tactic_ref)
        .collect::<Vec<_>>();
    let available_imports = request
        .state
        .env
        .imports
        .iter()
        .map(|import| npa_frontend::VerifiedImport::from(import.verified_module()))
        .collect::<Vec<_>>();
    let checked_current_decls = request
        .state
        .env
        .checked_current_decls
        .iter()
        .map(|decl| npa_frontend::MachineCheckedCurrentDecl {
            name: decl.signature().name().clone(),
            source_index: decl.source_index(),
            decl_interface_hash: decl.signature().decl_interface_hash(),
            decl: decl.core_decl().clone(),
        })
        .collect::<Vec<_>>();
    let current_generated_decls =
        human_tactic_current_generated_decls(&request.state.env.checked_current_decls);
    let local_context = goal
        .context
        .iter()
        .map(|local| npa_frontend::MachineLocalDecl {
            name: local.name.clone(),
            ty: local.ty.clone(),
            value: local.value.clone(),
        })
        .collect::<Vec<_>>();
    let context = npa_frontend::HumanTacticTermElabContext::from_request(
        npa_frontend::HumanTacticTermElabContextRequest {
            direct_imports: &direct_imports,
            available_imports: &available_imports,
            current_module: request.state.root.module.clone(),
            checked_current_decls: &checked_current_decls,
            current_generated_decls: &current_generated_decls,
            local_context,
            universe_params: request.state.root.universe_params.clone(),
            current_source_interface: Some(request.current_source_interface),
            imported_source_interfaces: request.imported_source_interfaces,
        },
    )?;
    let output = npa_frontend::elaborate_human_tactic_term_check(
        &context,
        request.term,
        &goal.target,
        &frontend_options,
    )?;

    Ok(HumanTacticTermCheckOk {
        expr: output.expr,
        inferred_type: output.inferred_type,
    })
}

pub fn run_human_exact_tactic(
    request: HumanExactTacticRequest<'_, '_>,
) -> Result<HumanExactTacticOk, HumanTacticTermError> {
    let goal = request.state.goal(request.goal_id)?;
    let checked = check_human_tactic_term(HumanTacticTermCheckRequest {
        state: request.state,
        goal_id: request.goal_id,
        term: request.term,
        current_source_interface: request.current_source_interface,
        imported_source_interfaces: request.imported_source_interfaces,
        options: request.options,
    })
    .map_err(|error| human_exact_check_error(error, &goal, request.term.span()))?;
    let (state, delta) = npa_tactic::assign_goal(
        request.state,
        request.goal_id,
        npa_tactic::ProofExpr::Core(checked.expr.clone()),
        Vec::new(),
    )
    .map_err(|diagnostic| {
        human_tactic_machine_diagnostic(
            &diagnostic,
            request.term.span(),
            Some(&goal),
            Some(npa_frontend::HumanDiagnosticKind::TypeMismatch),
            format!(
                "`exact` could not assign the proof term: {}",
                diagnostic.message
            ),
        )
    })?;
    npa_tactic::validate_machine_proof_state(&state)?;

    Ok(HumanExactTacticOk {
        state,
        delta,
        expr: checked.expr,
        inferred_type: checked.inferred_type,
    })
}

pub fn run_human_intro_tactic(
    request: HumanIntroTacticRequest<'_, '_>,
) -> Result<HumanIntroTacticOk, HumanIntroTacticError> {
    let name = human_intro_name(request.name)?;
    let before_goal = request.state.goal(request.goal_id)?;
    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
        request.state,
        npa_tactic::MachineTactic::Intro {
            goal_id: request.goal_id,
            name,
        },
        request.budget,
    )
    .map_err(|diagnostic| human_intro_machine_error(diagnostic, &before_goal, request.name.span))?;
    npa_tactic::validate_machine_proof_state(&state)?;

    Ok(HumanIntroTacticOk { state, delta })
}

pub fn run_human_apply_tactic(
    request: HumanApplyTacticRequest<'_, '_>,
) -> Result<HumanApplyTacticOk, HumanApplyTacticError> {
    let goal = request.state.goal(request.goal_id)?;
    let resolved = human_apply_resolve(
        request.state,
        &goal,
        request.term,
        request.current_source_interface,
        request.imported_source_interfaces,
    )?;
    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
        request.state,
        npa_tactic::MachineTactic::Apply {
            goal_id: request.goal_id,
            head: resolved.head.clone(),
            universe_args: resolved.universe_args.clone(),
            args: resolved.args.clone(),
        },
        request.budget,
    )
    .map_err(|diagnostic| human_apply_machine_error(diagnostic, &goal, &resolved))?;
    npa_tactic::validate_machine_proof_state(&state)?;

    Ok(HumanApplyTacticOk { state, delta })
}

pub fn run_human_rewrite_tactic(
    request: HumanRewriteTacticRequest<'_, '_>,
) -> Result<HumanRewriteTacticOk, HumanRewriteTacticError> {
    if request.rules.is_empty() {
        return Err(human_rewrite_unsupported_diagnostic(
            request.span,
            "rw requires at least one rewrite rule",
        )
        .into());
    }

    let mut state = request.state.clone();
    let mut deltas = Vec::new();
    let mut current_goal_id = request.goal_id;

    for rule in request.rules {
        let resolved = human_rewrite_resolve_rule(
            &state,
            current_goal_id,
            rule,
            request.current_source_interface,
            request.imported_source_interfaces,
        )?;
        let mut rule_rewrote = false;
        let mut last_error = None;

        for site in [
            npa_tactic::RewriteSite::EqTargetLeft,
            npa_tactic::RewriteSite::EqTargetRight,
        ] {
            let before_goal = state.goal(current_goal_id)?;
            match npa_tactic::run_machine_tactic_with_budget(
                &state,
                npa_tactic::MachineTactic::Rewrite {
                    goal_id: current_goal_id,
                    rule: npa_tactic::RewriteRuleRef {
                        head: resolved.head.clone(),
                        universe_args: resolved.universe_args.clone(),
                        args: resolved.args.clone(),
                    },
                    direction: resolved.direction,
                    site,
                },
                request.budget,
            ) {
                Ok((next_state, delta)) => {
                    state = next_state;
                    current_goal_id = *delta.added_goals.last().ok_or_else(|| {
                        human_rewrite_unsupported_diagnostic(
                            resolved.span,
                            "Human rw expected Machine rewrite to create a rewritten target goal",
                        )
                    })?;
                    deltas.push(delta);
                    rule_rewrote = true;
                    npa_tactic::validate_machine_proof_state(&state)?;
                }
                Err(diagnostic) => {
                    last_error = Some(human_rewrite_machine_error(
                        diagnostic,
                        &before_goal,
                        &resolved,
                        site,
                    ));
                }
            }
        }

        if !rule_rewrote {
            return Err(last_error.unwrap_or_else(|| {
                human_rewrite_unsupported_diagnostic(
                    resolved.span,
                    format!(
                        "rewrite rule `{}` did not match the target",
                        resolved.head_label
                    ),
                )
                .into()
            }));
        }
    }

    Ok(HumanRewriteTacticOk { state, deltas })
}

pub fn run_human_simp_lite_tactic(
    request: HumanSimpLiteTacticRequest<'_>,
) -> Result<HumanSimpLiteTacticOk, HumanSimpLiteTacticError> {
    let before_goal = request.state.goal(request.goal_id)?;
    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
        request.state,
        npa_tactic::MachineTactic::SimpLite {
            goal_id: request.goal_id,
            rules: Vec::new(),
        },
        request.budget,
    )
    .map_err(|diagnostic| human_simp_lite_machine_error(diagnostic, &before_goal, request.span))?;

    if !delta.added_goals.is_empty() || state.open_goals.contains(&request.goal_id) {
        let residual_target = delta
            .added_goals
            .last()
            .and_then(|goal_id| state.goal(*goal_id).ok())
            .map(|goal| goal.target);
        return Err(human_simp_lite_not_closed_diagnostic(
            request.span,
            &before_goal,
            residual_target.as_ref(),
        )
        .into());
    }

    npa_tactic::validate_machine_proof_state(&state)?;
    Ok(HumanSimpLiteTacticOk { state, delta })
}

pub fn run_human_induction_tactic(
    request: HumanInductionTacticRequest<'_, '_>,
) -> Result<HumanInductionTacticOk, HumanInductionTacticError> {
    let local_name = human_induction_name(request.name)?;
    let before_goal = request.state.goal(request.goal_id)?;
    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
        request.state,
        npa_tactic::MachineTactic::InductionNat {
            goal_id: request.goal_id,
            local_name,
        },
        request.budget,
    )
    .map_err(|diagnostic| human_induction_machine_error(diagnostic, &before_goal, request.span))?;
    npa_tactic::validate_machine_proof_state(&state)?;
    Ok(HumanInductionTacticOk { state, delta })
}

pub fn run_human_smt_tactic(
    request: HumanSmtTacticRequest<'_, '_>,
) -> Result<HumanSmtTacticOk, HumanApplyTacticError> {
    let goal = request.state.goal(request.goal_id)?;
    let mut lemmas = Vec::with_capacity(request.lemmas.len());
    for lemma in request.lemmas {
        let resolved = human_apply_resolve(
            request.state,
            &goal,
            lemma,
            request.current_source_interface,
            request.imported_source_interfaces,
        )?;
        if !resolved.args.is_empty() {
            return Err(human_apply_unsupported_diagnostic(
                resolved.span,
                format!(
                    "smt lemma `{}` must resolve to a closed proof head in the Human SMT MVP",
                    resolved.head_label
                ),
            )
            .into());
        }
        lemmas.push(npa_tactic::SmtLemmaRef {
            head: resolved.head,
            universe_args: resolved.universe_args,
        });
    }

    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
        request.state,
        npa_tactic::MachineTactic::Smt {
            goal_id: request.goal_id,
            lemmas,
        },
        request.budget,
    )
    .map_err(|diagnostic| human_smt_machine_error(diagnostic, &goal, request.span))?;
    npa_tactic::validate_machine_proof_state(&state)?;
    Ok(HumanSmtTacticOk { state, delta })
}

fn run_human_solver_tactic(
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    tactic: npa_tactic::MachineTactic,
    span: npa_frontend::Span,
    budget: npa_tactic::TacticBudget,
) -> Result<HumanTacticRunExecutionOk, HumanTacticScriptError> {
    let goal = state.goal(goal_id)?;
    let tactic_kind = npa_tactic::machine_tactic_kind(&tactic).unwrap_or("solver");
    let (state, delta) = npa_tactic::run_machine_tactic_with_budget(state, tactic, budget)
        .map_err(|diagnostic| human_solver_machine_error(diagnostic, &goal, span, tactic_kind))?;
    npa_tactic::validate_machine_proof_state(&state)?;
    Ok(HumanTacticRunExecutionOk {
        state,
        deltas: vec![delta],
    })
}

fn human_solver_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
    tactic_kind: &'static str,
) -> HumanTacticScriptError {
    let human_kind = match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::TypeMismatch => {
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        }
        _ => npa_frontend::HumanDiagnosticKind::UnsupportedTactic,
    };
    human_tactic_machine_diagnostic(
        &diagnostic,
        span,
        Some(goal),
        Some(human_kind),
        format!(
            "{tactic_kind} could not produce a checked proof for this goal\n\ntarget:\n  {:?}\n\n{}",
            goal.target, diagnostic.message
        ),
    )
    .into()
}

pub fn run_human_smt_prove(request: HumanSmtProveRequest<'_, '_>) -> HumanSmtProveResponse {
    if !request.require_certificate {
        let candidate_hash =
            crate::advanced_ai::advanced_ai_candidate_hash(request.request_canonical_bytes);
        let error = crate::AdvancedAiValidationError::UnsupportedFeature;
        let feature_error = Some(crate::AdvancedAiFeatureError::SmtCertificate(
            crate::AdvancedSmtCertificateError::SolverResultOnly,
        ));
        let validation_result_hash = crate::advanced_ai_validation_result_hash_for_rejection(
            candidate_hash,
            error,
            feature_error,
        );
        return HumanSmtProveResponse::Diagnostic(crate::AdvancedAiEndpointResponse::Rejected {
            candidate_hash,
            validation_result_hash,
            error,
            feature_error,
        });
    }

    match crate::advanced_ai_smt_prove_hashes_from_request(
        request.request_canonical_bytes,
        request.verified_imports,
        request.workspace_root,
    ) {
        Ok(hashes) => HumanSmtProveResponse::Success(hashes.into()),
        Err(response) => HumanSmtProveResponse::Diagnostic(response),
    }
}

pub fn run_human_formalize(request: HumanFormalizeRequest<'_>) -> HumanFormalizeOk {
    let candidates = request
        .candidates
        .into_iter()
        .map(|candidate| {
            human_formalize_candidate(candidate, request.verified_imports, request.workspace_root)
        })
        .collect();
    HumanFormalizeOk { candidates }
}

fn human_formalize_candidate(
    candidate: HumanFormalizeCandidateRequest,
    verified_imports: &[npa_tactic::VerifiedImportRef],
    workspace_root: &std::path::Path,
) -> HumanFormalizeCandidateReport {
    let fallback_candidate_hash =
        crate::advanced_ai::advanced_ai_candidate_hash(&candidate.request_canonical_bytes);
    let metadata = match crate::advanced_ai_formalization_request_metadata(
        &candidate.request_canonical_bytes,
        verified_imports,
        workspace_root,
    ) {
        Ok(metadata) => metadata,
        Err(response) => {
            return HumanFormalizeCandidateReport {
                candidate_hash: fallback_candidate_hash,
                candidate_statement_hash: None,
                formal_statement_hash: None,
                accepted_statement_hash: None,
                reverse_translation: candidate.reverse_translation,
                ambiguity_report: candidate.ambiguity_report,
                confidence_microunits: candidate.confidence_microunits,
                review_status: HumanFormalizationReviewStatus::MalformedRequest,
                proof_search_status: HumanFormalizationProofSearchStatus::NotRequested,
                intent_certificate: None,
                validation_kind: None,
                validation_response: response,
                verified: false,
            };
        }
    };

    let review_status = human_formalization_review_status(metadata.payload.intent_record.as_ref());
    let proof_requested = metadata
        .payload
        .candidate
        .optional_proof_candidate
        .is_some();
    let statement_validation_request = if proof_requested {
        metadata
            .request_without_proof_candidate_canonical_bytes
            .as_slice()
    } else {
        candidate.request_canonical_bytes.as_slice()
    };
    let statement_validation_response = crate::run_advanced_ai_formalize_check_request(
        statement_validation_request,
        verified_imports,
        workspace_root,
    );
    let (statement_validation_kind, statement_accepted_statement_hash) =
        human_formalization_validation_summary(&statement_validation_response);
    let formal_statement_hash =
        human_confirmed_formal_statement_hash(&review_status, statement_accepted_statement_hash);
    let intent_record_validated = matches!(
        statement_validation_response,
        crate::AdvancedAiEndpointResponse::Success { .. }
    );
    let (proof_search_status, validation_kind, accepted_statement_hash, validation_response) =
        if !proof_requested {
            (
                HumanFormalizationProofSearchStatus::NotRequested,
                statement_validation_kind,
                statement_accepted_statement_hash,
                statement_validation_response,
            )
        } else if formal_statement_hash.is_none() {
            (
                HumanFormalizationProofSearchStatus::BlockedUntilConfirmed,
                statement_validation_kind,
                statement_accepted_statement_hash,
                statement_validation_response,
            )
        } else {
            let proof_validation_response = crate::run_advanced_ai_formalize_check_request(
                candidate.request_canonical_bytes.as_slice(),
                verified_imports,
                workspace_root,
            );
            let (proof_validation_kind, proof_accepted_statement_hash) =
                human_formalization_validation_summary(&proof_validation_response);
            let proof_search_status = if matches!(
                proof_validation_kind,
                Some(crate::AdvancedFormalizationSuccessKind::ProofBridgeChecked)
            ) {
                HumanFormalizationProofSearchStatus::Checked
            } else {
                HumanFormalizationProofSearchStatus::Rejected
            };
            (
                proof_search_status,
                proof_validation_kind,
                proof_accepted_statement_hash.or(statement_accepted_statement_hash),
                proof_validation_response,
            )
        };
    let verified = matches!(
        proof_search_status,
        HumanFormalizationProofSearchStatus::Checked
    ) && formal_statement_hash.is_some();
    let intent_certificate = intent_record_validated
        .then(|| {
            metadata.payload.intent_record.as_ref().map(|intent| {
                human_formalization_intent_certificate(
                    intent,
                    &review_status,
                    &candidate.reverse_translation,
                    &candidate.ambiguity_report,
                    candidate.confidence_microunits,
                )
            })
        })
        .flatten();

    HumanFormalizeCandidateReport {
        candidate_hash: metadata.candidate_hash,
        candidate_statement_hash: Some(metadata.candidate_statement_hash),
        formal_statement_hash,
        accepted_statement_hash,
        reverse_translation: candidate.reverse_translation,
        ambiguity_report: candidate.ambiguity_report,
        confidence_microunits: candidate.confidence_microunits,
        review_status,
        proof_search_status,
        intent_certificate,
        validation_kind,
        validation_response,
        verified,
    }
}

fn human_formalization_review_status(
    intent: Option<&crate::AdvancedFormalizationIntentRecord>,
) -> HumanFormalizationReviewStatus {
    match intent.map(|record| &record.status) {
        None => HumanFormalizationReviewStatus::MissingIntent,
        Some(crate::AdvancedFormalizationIntentStatus::Unreviewed) => {
            HumanFormalizationReviewStatus::Unreviewed
        }
        Some(crate::AdvancedFormalizationIntentStatus::Reviewed {
            reviewer,
            accepted_statement_hash,
        }) => HumanFormalizationReviewStatus::Reviewed {
            reviewer: reviewer.clone(),
            accepted_statement_hash: *accepted_statement_hash,
        },
        Some(crate::AdvancedFormalizationIntentStatus::Rejected {
            reviewer,
            rejection_reason_hash,
            ..
        }) => HumanFormalizationReviewStatus::Rejected {
            reviewer: reviewer.clone(),
            rejection_reason_hash: *rejection_reason_hash,
        },
    }
}

fn human_formalization_validation_summary(
    response: &crate::AdvancedAiEndpointResponse,
) -> (
    Option<crate::AdvancedFormalizationSuccessKind>,
    Option<Hash>,
) {
    match response {
        crate::AdvancedAiEndpointResponse::Success { payload, .. } => match payload.as_ref() {
            crate::AdvancedAiSuccessPayload::NaturalLanguageFormalization {
                kind,
                accepted_statement_hash,
                ..
            } => (Some(*kind), *accepted_statement_hash),
            _ => (None, None),
        },
        _ => (None, None),
    }
}

fn human_confirmed_formal_statement_hash(
    review_status: &HumanFormalizationReviewStatus,
    accepted_statement_hash: Option<Hash>,
) -> Option<Hash> {
    match review_status {
        HumanFormalizationReviewStatus::Reviewed {
            accepted_statement_hash: reviewed,
            ..
        } if Some(*reviewed) == accepted_statement_hash => Some(*reviewed),
        _ => None,
    }
}

fn human_formalization_intent_certificate(
    intent: &crate::AdvancedFormalizationIntentRecord,
    status: &HumanFormalizationReviewStatus,
    reverse_translation: &str,
    ambiguity_report: &[String],
    confidence_microunits: Option<u32>,
) -> HumanFormalizationIntentCertificate {
    let reverse_translation_hash = human_formalization_text_hash(
        "npa.human-api.formalization.reverse-translation.v1",
        reverse_translation,
    );
    let ambiguity_report_hash = human_formalization_text_list_hash(
        "npa.human-api.formalization.ambiguity-report.v1",
        ambiguity_report,
    );
    let mut out = Vec::new();
    human_encode_string(
        &mut out,
        "npa.human-api.formalization.intent-certificate.v1",
    );
    out.extend(intent.source_document_hash);
    out.extend(intent.claim_span_hash);
    out.extend(intent.candidate_statement_hash);
    out.extend(reverse_translation_hash);
    out.extend(ambiguity_report_hash);
    human_encode_option_u32(&mut out, confidence_microunits);
    human_encode_formalization_review_status(&mut out, status);
    HumanFormalizationIntentCertificate {
        intent_certificate_hash: human_sha256(&out),
        source_document_hash: intent.source_document_hash,
        claim_span_hash: intent.claim_span_hash,
        candidate_statement_hash: intent.candidate_statement_hash,
        reverse_translation_hash,
        ambiguity_report_hash,
        confidence_microunits,
        status: status.clone(),
    }
}

pub fn run_human_tactic_script(
    request: HumanTacticScriptRunRequest<'_, '_>,
) -> Result<HumanTacticScriptRunOk, HumanTacticScriptError> {
    let mut state = request.state.clone();
    let mut deltas = Vec::with_capacity(request.script.tactics.len());

    for tactic in &request.script.tactics {
        let Some(goal_id) = state.open_goals.first().copied() else {
            return Err(human_script_no_goals_diagnostic(tactic.span()).into());
        };

        match tactic {
            npa_frontend::HumanTacticSyntax::Intro { name, .. } => {
                let ok = run_human_intro_tactic(HumanIntroTacticRequest {
                    state: &state,
                    goal_id,
                    name,
                    budget: request.budget,
                })
                .map_err(human_script_intro_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
            npa_frontend::HumanTacticSyntax::Exact { term, .. } => {
                let ok = run_human_exact_tactic(HumanExactTacticRequest {
                    state: &state,
                    goal_id,
                    term,
                    current_source_interface: request.current_source_interface,
                    imported_source_interfaces: request.imported_source_interfaces,
                    options: request.options.clone(),
                })
                .map_err(human_script_term_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
            npa_frontend::HumanTacticSyntax::Apply { term, .. } => {
                let ok = run_human_apply_tactic(HumanApplyTacticRequest {
                    state: &state,
                    goal_id,
                    term,
                    current_source_interface: request.current_source_interface,
                    imported_source_interfaces: request.imported_source_interfaces,
                    budget: request.budget,
                })
                .map_err(human_script_apply_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
            npa_frontend::HumanTacticSyntax::Rewrite { rules, span } => {
                let ok = run_human_rewrite_tactic(HumanRewriteTacticRequest {
                    state: &state,
                    goal_id,
                    rules,
                    span: *span,
                    current_source_interface: request.current_source_interface,
                    imported_source_interfaces: request.imported_source_interfaces,
                    budget: request.budget,
                })
                .map_err(human_script_rewrite_error)?;
                state = ok.state;
                deltas.extend(ok.deltas);
            }
            npa_frontend::HumanTacticSyntax::SimpLite { span } => {
                let ok = run_human_simp_lite_tactic(HumanSimpLiteTacticRequest {
                    state: &state,
                    goal_id,
                    span: *span,
                    budget: request.budget,
                })
                .map_err(human_script_simp_lite_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
            npa_frontend::HumanTacticSyntax::Smt { lemmas, span } => {
                let ok = run_human_smt_tactic(HumanSmtTacticRequest {
                    state: &state,
                    goal_id,
                    lemmas,
                    span: *span,
                    current_source_interface: request.current_source_interface,
                    imported_source_interfaces: request.imported_source_interfaces,
                    budget: request.budget,
                })
                .map_err(human_script_apply_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
            npa_frontend::HumanTacticSyntax::FiniteDecide { span } => {
                let ok = run_human_solver_tactic(
                    &state,
                    goal_id,
                    npa_tactic::MachineTactic::FiniteDecide { goal_id },
                    *span,
                    request.budget,
                )?;
                state = ok.state;
                deltas.extend(ok.deltas);
            }
            npa_frontend::HumanTacticSyntax::Omega { span } => {
                let ok = run_human_solver_tactic(
                    &state,
                    goal_id,
                    npa_tactic::MachineTactic::Omega { goal_id },
                    *span,
                    request.budget,
                )?;
                state = ok.state;
                deltas.extend(ok.deltas);
            }
            npa_frontend::HumanTacticSyntax::RingNf { span } => {
                let ok = run_human_solver_tactic(
                    &state,
                    goal_id,
                    npa_tactic::MachineTactic::Ring { goal_id },
                    *span,
                    request.budget,
                )?;
                state = ok.state;
                deltas.extend(ok.deltas);
            }
            npa_frontend::HumanTacticSyntax::Bitblast { span } => {
                let ok = run_human_solver_tactic(
                    &state,
                    goal_id,
                    npa_tactic::MachineTactic::Bitblast { goal_id },
                    *span,
                    request.budget,
                )?;
                state = ok.state;
                deltas.extend(ok.deltas);
            }
            npa_frontend::HumanTacticSyntax::Induction { name, span } => {
                let ok = run_human_induction_tactic(HumanInductionTacticRequest {
                    state: &state,
                    goal_id,
                    name,
                    span: *span,
                    budget: request.budget,
                })
                .map_err(human_script_induction_error)?;
                state = ok.state;
                deltas.push(ok.delta);
            }
        }
    }

    if !state.open_goals.is_empty() {
        return Err(human_script_unresolved_goal_diagnostic(request.script.span, &state).into());
    }

    let proof = npa_tactic::extract_closed_machine_proof(&state)?;
    Ok(HumanTacticScriptRunOk {
        state,
        deltas,
        proof,
    })
}

pub fn human_api_default_compile_options() -> HumanApiCompileOptions {
    HumanApiCompileOptions::default()
}

fn human_intro_name(name: &npa_frontend::HumanName) -> Result<String, HumanIntroTacticError> {
    if name.parts.len() != 1 {
        return Err(human_intro_invalid_diagnostic(
            name.span,
            format!(
                "intro binder name must be a single identifier, got {}",
                name.as_dotted()
            ),
        )
        .into());
    }
    Ok(name.parts[0].clone())
}

fn human_exact_check_error(
    error: HumanTacticTermError,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> HumanTacticTermError {
    match error {
        HumanTacticTermError::Human(HumanCompileError { diagnostic }) => {
            human_tactic_validation_diagnostic_with_goal(diagnostic, goal, span).into()
        }
        HumanTacticTermError::Machine(diagnostic) => human_tactic_machine_diagnostic(
            &diagnostic,
            span,
            Some(goal),
            Some(npa_frontend::HumanDiagnosticKind::MachineElaborationError),
            format!("`exact` term validation failed: {}", diagnostic.message),
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
        .into(),
    }
}

fn human_intro_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> HumanIntroTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::TypeMismatch => human_tactic_machine_diagnostic(
            &diagnostic,
            span,
            Some(goal),
            Some(npa_frontend::HumanDiagnosticKind::ExpectedFunctionType),
            "`intro` can only be used when the target is a function type or forall.",
        )
        .into(),
        npa_tactic::MachineTacticDiagnosticKind::InvalidMachineTactic => {
            human_intro_invalid_diagnostic(span, diagnostic.message.to_string()).into()
        }
        _ => diagnostic.into(),
    }
}

fn human_intro_invalid_diagnostic(
    span: npa_frontend::Span,
    message: impl Into<String>,
) -> npa_frontend::HumanDiagnostic {
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic,
        span,
        message,
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
}

fn human_induction_name(
    name: &npa_frontend::HumanName,
) -> Result<String, HumanInductionTacticError> {
    if name.parts.len() != 1 {
        return Err(human_induction_unsupported_diagnostic(
            name.span,
            format!(
                "induction target name must be a single local identifier, got {}",
                name.as_dotted()
            ),
        )
        .into());
    }
    Ok(name.parts[0].clone())
}

#[derive(Clone, Debug)]
struct HumanApplyResolved {
    head: npa_tactic::TacticHead,
    universe_args: Vec<Level>,
    args: Vec<npa_tactic::ApplyArg>,
    head_label: String,
    head_type: Expr,
    span: npa_frontend::Span,
}

#[derive(Clone, Debug)]
struct HumanRewriteResolved {
    head: npa_tactic::TacticHead,
    universe_args: Vec<Level>,
    args: Vec<npa_tactic::ApplyArg>,
    direction: npa_tactic::RewriteDirection,
    head_label: String,
    head_type: Expr,
    span: npa_frontend::Span,
}

#[derive(Clone, Debug)]
enum HumanApplyGlobalCandidate {
    Imported {
        module: npa_cert::ModuleName,
        export_hash: npa_cert::Hash,
        certificate_hash: npa_cert::Hash,
        name: npa_cert::Name,
        decl_interface_hash: npa_cert::Hash,
    },
    Current {
        name: npa_cert::Name,
        decl_interface_hash: npa_cert::Hash,
    },
}

impl HumanApplyGlobalCandidate {
    fn name(&self) -> &npa_cert::Name {
        match self {
            Self::Imported { name, .. } | Self::Current { name, .. } => name,
        }
    }

    fn sort_key(&self) -> String {
        match self {
            Self::Imported {
                module,
                export_hash,
                certificate_hash,
                name,
                decl_interface_hash,
            } => format!(
                "imported:{}:{}:{}:{}:{}",
                module.as_dotted(),
                human_apply_hash_hex(export_hash),
                human_apply_hash_hex(certificate_hash),
                name.as_dotted(),
                human_apply_hash_hex(decl_interface_hash)
            ),
            Self::Current {
                name,
                decl_interface_hash,
            } => format!(
                "current:{}:{}",
                name.as_dotted(),
                human_apply_hash_hex(decl_interface_hash)
            ),
        }
    }

    fn tactic_head(&self) -> npa_tactic::TacticHead {
        match self {
            Self::Imported {
                name,
                decl_interface_hash,
                ..
            } => npa_tactic::TacticHead::Imported {
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            Self::Current {
                name,
                decl_interface_hash,
            } => npa_tactic::TacticHead::CurrentModule {
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
        }
    }
}

fn human_apply_resolve(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    term: &npa_frontend::HumanExpr,
    current_source_interface: &npa_frontend::HumanSourceInterface,
    imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
) -> Result<HumanApplyResolved, HumanApplyTacticError> {
    let npa_frontend::HumanExpr::Ident {
        name,
        universe_args,
        span,
        ..
    } = term
    else {
        return Err(human_apply_unsupported_head_diagnostic(term.span()).into());
    };

    let explicit_universe_args = human_apply_universe_args(universe_args.as_deref());
    if let Some(local_name) = human_apply_local_head(goal, name, *span)? {
        if !explicit_universe_args.is_empty() {
            return Err(human_apply_unsupported_diagnostic(
                *span,
                "local apply heads do not accept universe arguments",
            )
            .into());
        }
        let local_index = goal
            .context
            .iter()
            .position(|local| local.name == local_name)
            .expect("resolved local apply head should exist");
        let local = &goal.context[local_index];
        let ctx = human_apply_goal_ctx(state, goal, *span)?;
        let head_bvar = Expr::bvar((goal.context.len() - 1 - local_index) as u32);
        let head_type = state
            .env
            .kernel_env()
            .infer(&ctx, &state.root.universe_params, &head_bvar)
            .map_err(|err| {
                human_apply_unsupported_diagnostic(
                    *span,
                    format!("cannot infer local apply head {} type: {err:?}", local.name),
                )
            })?;
        let args = human_apply_args_for_type(
            state,
            goal,
            &head_type,
            &[],
            *span,
            &format!("local {}", local.name),
        )?;
        return Ok(HumanApplyResolved {
            head: npa_tactic::TacticHead::Local {
                name: local.name.clone(),
            },
            universe_args: Vec::new(),
            args,
            head_label: local.name.clone(),
            head_type,
            span: *span,
        });
    }

    let candidate = human_apply_global_head(state, goal, name, *span)?;
    let decl = state
        .env
        .kernel_env()
        .decl(&candidate.name().as_dotted())
        .ok_or_else(|| {
            human_apply_unsupported_diagnostic(
                *span,
                format!(
                    "apply head {} is not present in the kernel environment",
                    candidate.name().as_dotted()
                ),
            )
        })?;
    let universe_params = decl.universe_params();
    let universe_args = if let Some(args) = universe_args {
        let args = human_apply_universe_args(Some(args));
        if args.len() != universe_params.len() {
            return Err(human_apply_unsupported_diagnostic(
                *span,
                format!(
                    "apply head {} expects {} universe argument(s), got {}",
                    candidate.name().as_dotted(),
                    universe_params.len(),
                    args.len()
                ),
            )
            .into());
        }
        args
    } else if universe_params.is_empty() {
        Vec::new()
    } else if let Some(args) = human_infer_universe_args_from_eq_goal(goal, universe_params.len()) {
        args
    } else {
        return Err(human_apply_unsupported_diagnostic(
            *span,
            format!(
                "apply head {} requires explicit universe arguments in the Human apply MVP",
                candidate.name().as_dotted()
            ),
        )
        .into());
    };
    let head_type =
        npa_kernel::subst::subst_levels_expr(decl.ty(), universe_params, &universe_args);
    let implicit_profile = human_apply_global_implicit_profile(
        &candidate,
        current_source_interface,
        imported_source_interfaces,
    );
    let args = human_apply_args_for_type(
        state,
        goal,
        &head_type,
        &implicit_profile,
        *span,
        &candidate.name().as_dotted(),
    )?;
    Ok(HumanApplyResolved {
        head: candidate.tactic_head(),
        universe_args,
        args,
        head_label: candidate.name().as_dotted(),
        head_type,
        span: *span,
    })
}

fn human_rewrite_resolve_rule(
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    rule: &npa_frontend::HumanRewriteRuleSyntax,
    _current_source_interface: &npa_frontend::HumanSourceInterface,
    _imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
) -> Result<HumanRewriteResolved, HumanRewriteTacticError> {
    let goal = state.goal(goal_id)?;
    let npa_frontend::HumanExpr::Ident {
        name,
        universe_args,
        span,
        ..
    } = &rule.term
    else {
        return Err(human_rewrite_unsupported_head_diagnostic(rule.term.span()).into());
    };

    let explicit_universe_args = human_apply_universe_args(universe_args.as_deref());
    if let Some(local_name) =
        human_apply_local_head(&goal, name, *span).map_err(human_rewrite_from_apply_error)?
    {
        if !explicit_universe_args.is_empty() {
            return Err(human_rewrite_unsupported_diagnostic(
                *span,
                "local rw rule heads do not accept universe arguments",
            )
            .into());
        }
        let local_index = goal
            .context
            .iter()
            .position(|local| local.name == local_name)
            .expect("resolved local rewrite head should exist");
        let local = &goal.context[local_index];
        let ctx =
            human_apply_goal_ctx(state, &goal, *span).map_err(human_rewrite_from_apply_error)?;
        let head_bvar = Expr::bvar((goal.context.len() - 1 - local_index) as u32);
        let head_type = state
            .env
            .kernel_env()
            .infer(&ctx, &state.root.universe_params, &head_bvar)
            .map_err(|err| {
                human_rewrite_unsupported_diagnostic(
                    *span,
                    format!("cannot infer local rw rule {} type: {err:?}", local.name),
                )
            })?;
        let args = human_rewrite_args_for_type(state, &goal, &head_type, *span, &local.name)?;
        return Ok(HumanRewriteResolved {
            head: npa_tactic::TacticHead::Local {
                name: local.name.clone(),
            },
            universe_args: Vec::new(),
            args,
            direction: human_rewrite_direction(rule.direction),
            head_label: local.name.clone(),
            head_type,
            span: *span,
        });
    }

    let candidate = human_apply_global_head(state, &goal, name, *span)
        .map_err(human_rewrite_from_apply_error)?;
    let decl = state
        .env
        .kernel_env()
        .decl(&candidate.name().as_dotted())
        .ok_or_else(|| {
            human_rewrite_unsupported_diagnostic(
                *span,
                format!(
                    "rw rule {} is not present in the kernel environment",
                    candidate.name().as_dotted()
                ),
            )
        })?;
    let universe_params = decl.universe_params();
    let universe_args = if let Some(args) = universe_args {
        let args = human_apply_universe_args(Some(args));
        if args.len() != universe_params.len() {
            return Err(human_rewrite_unsupported_diagnostic(
                *span,
                format!(
                    "rw rule {} expects {} universe argument(s), got {}",
                    candidate.name().as_dotted(),
                    universe_params.len(),
                    args.len()
                ),
            )
            .into());
        }
        args
    } else if universe_params.is_empty() {
        Vec::new()
    } else if let Some(args) = human_infer_universe_args_from_eq_goal(&goal, universe_params.len())
    {
        args
    } else {
        return Err(human_rewrite_unsupported_diagnostic(
            *span,
            format!(
                "rw rule {} requires explicit universe arguments in the Human rw MVP",
                candidate.name().as_dotted()
            ),
        )
        .into());
    };
    let head_type =
        npa_kernel::subst::subst_levels_expr(decl.ty(), universe_params, &universe_args);
    let args = human_rewrite_args_for_type(
        state,
        &goal,
        &head_type,
        *span,
        &candidate.name().as_dotted(),
    )?;
    Ok(HumanRewriteResolved {
        head: candidate.tactic_head(),
        universe_args,
        args,
        direction: human_rewrite_direction(rule.direction),
        head_label: candidate.name().as_dotted(),
        head_type,
        span: *span,
    })
}

fn human_infer_universe_args_from_eq_goal(
    goal: &npa_tactic::MachineGoal,
    universe_param_count: usize,
) -> Option<Vec<Level>> {
    if universe_param_count != 1 {
        return None;
    }
    let (head, _) = npa_kernel::expr::collect_apps(&goal.target);
    match head {
        Expr::Const { name, levels } if name == "Eq" && levels.len() == 1 => Some(levels),
        _ => None,
    }
}

fn human_rewrite_args_for_type(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    head_type: &Expr,
    span: npa_frontend::Span,
    head_label: &str,
) -> Result<Vec<npa_tactic::ApplyArg>, HumanRewriteTacticError> {
    let ctx = human_apply_goal_ctx(state, goal, span).map_err(human_rewrite_from_apply_error)?;
    let env = state.env.kernel_env();
    let delta = &state.root.universe_params;
    let mut current = head_type.clone();
    let mut args = Vec::new();

    loop {
        let whnf = env.whnf(&ctx, delta, &current).map_err(|err| {
            human_rewrite_unsupported_diagnostic(
                span,
                format!("cannot inspect rw rule {head_label} type: {err:?}"),
            )
        })?;
        let Expr::Pi { body, .. } = whnf else {
            break;
        };
        let arg = npa_tactic::ApplyArg::InferFromTarget;
        let placeholder = human_apply_placeholder(&arg, goal);
        current = instantiate(&body, &placeholder).map_err(|err| {
            human_rewrite_unsupported_diagnostic(
                span,
                format!("cannot instantiate rw rule {head_label} type: {err:?}"),
            )
        })?;
        args.push(arg);
    }

    Ok(args)
}

fn human_rewrite_direction(
    direction: npa_frontend::HumanRewriteDirection,
) -> npa_tactic::RewriteDirection {
    match direction {
        npa_frontend::HumanRewriteDirection::Forward => npa_tactic::RewriteDirection::Forward,
        npa_frontend::HumanRewriteDirection::Backward => npa_tactic::RewriteDirection::Backward,
    }
}

fn human_rewrite_from_apply_error(error: HumanApplyTacticError) -> HumanRewriteTacticError {
    match error {
        HumanApplyTacticError::Human(error) => HumanRewriteTacticError::Human(error),
        HumanApplyTacticError::Machine(diagnostic) => HumanRewriteTacticError::Machine(diagnostic),
    }
}

fn human_apply_local_head(
    goal: &npa_tactic::MachineGoal,
    name: &npa_frontend::HumanName,
    span: npa_frontend::Span,
) -> Result<Option<String>, HumanApplyTacticError> {
    if name.parts.len() != 1 {
        return Ok(None);
    }
    let matches = goal
        .context
        .iter()
        .filter(|local| local.name == name.parts[0])
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Ok(None),
        [local] => Ok(Some(local.name.clone())),
        _ => Err(npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::AmbiguousName,
            span,
            format!("ambiguous local apply head {}", name.as_dotted()),
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
        .with_payload(human_tactic_goal_payload(goal, span))
        .into()),
    }
}

fn human_apply_global_head(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    name: &npa_frontend::HumanName,
    span: npa_frontend::Span,
) -> Result<HumanApplyGlobalCandidate, HumanApplyTacticError> {
    for candidates in human_apply_global_candidate_levels(state, name) {
        let candidates = human_apply_dedupe_candidates(candidates);
        if candidates.is_empty() {
            continue;
        }
        if candidates.len() == 1 {
            return Ok(candidates[0].clone());
        }
        return Err(npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::AmbiguousName,
            span,
            format!("ambiguous apply head {}", name.as_dotted()),
        )
        .with_payload(npa_frontend::HumanDiagnosticPayload {
            candidates: candidates
                .into_iter()
                .map(|candidate| candidate.sort_key())
                .collect(),
            hole_goals: vec![human_tactic_goal_display(goal, span)],
            ..npa_frontend::HumanDiagnosticPayload::default()
        })
        .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
        .into());
    }

    Err(npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnknownIdentifier,
        span,
        format!("unknown apply head {}", name.as_dotted()),
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
    .with_payload(human_tactic_goal_payload(goal, span))
    .into())
}

fn human_apply_global_candidate_levels(
    state: &npa_tactic::MachineProofState,
    name: &npa_frontend::HumanName,
) -> Vec<Vec<HumanApplyGlobalCandidate>> {
    let exact = npa_cert::Name(name.parts.clone());
    if name.parts.len() == 1 {
        vec![
            human_apply_exact_candidates(state, &exact),
            human_apply_short_name_candidates(state, &name.parts[0]),
        ]
    } else {
        vec![
            human_apply_exact_candidates(state, &exact),
            human_apply_suffix_candidates(state, &name.parts),
        ]
    }
}

fn human_apply_exact_candidates(
    state: &npa_tactic::MachineProofState,
    name: &npa_cert::Name,
) -> Vec<HumanApplyGlobalCandidate> {
    let current = state
        .env
        .checked_current_decls
        .iter()
        .filter(|decl| decl.signature().name() == name)
        .map(|decl| HumanApplyGlobalCandidate::Current {
            name: decl.signature().name().clone(),
            decl_interface_hash: decl.signature().decl_interface_hash(),
        })
        .collect::<Vec<_>>();
    if !current.is_empty() {
        return current;
    }

    human_apply_imported_candidates(state, |export| &export.name == name)
}

fn human_apply_short_name_candidates(
    state: &npa_tactic::MachineProofState,
    short_name: &str,
) -> Vec<HumanApplyGlobalCandidate> {
    let current = state
        .env
        .checked_current_decls
        .iter()
        .filter(|decl| {
            decl.signature()
                .name()
                .0
                .last()
                .is_some_and(|part| part == short_name)
        })
        .map(|decl| HumanApplyGlobalCandidate::Current {
            name: decl.signature().name().clone(),
            decl_interface_hash: decl.signature().decl_interface_hash(),
        })
        .collect::<Vec<_>>();
    if !current.is_empty() {
        return current;
    }

    human_apply_imported_candidates(state, |export| {
        export.name.0.last().is_some_and(|part| part == short_name)
    })
}

fn human_apply_suffix_candidates(
    state: &npa_tactic::MachineProofState,
    suffix: &[String],
) -> Vec<HumanApplyGlobalCandidate> {
    let current = state
        .env
        .checked_current_decls
        .iter()
        .filter(|decl| human_apply_name_has_suffix(&decl.signature().name().0, suffix))
        .map(|decl| HumanApplyGlobalCandidate::Current {
            name: decl.signature().name().clone(),
            decl_interface_hash: decl.signature().decl_interface_hash(),
        })
        .collect::<Vec<_>>();
    if !current.is_empty() {
        return current;
    }

    human_apply_imported_candidates(state, |export| {
        human_apply_name_has_suffix(&export.name.0, suffix)
    })
}

fn human_apply_imported_candidates(
    state: &npa_tactic::MachineProofState,
    mut is_match: impl FnMut(&npa_tactic::VerifiedExportSignature) -> bool,
) -> Vec<HumanApplyGlobalCandidate> {
    let mut candidates = Vec::new();
    for import in state
        .env
        .imports
        .iter()
        .filter(|import| import.is_visible())
    {
        for export in import.exports().iter().filter(|export| is_match(export)) {
            candidates.push(HumanApplyGlobalCandidate::Imported {
                module: import.module().clone(),
                export_hash: import.export_hash(),
                certificate_hash: import.certificate_hash(),
                name: export.name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            });
        }
    }
    candidates
}

fn human_apply_dedupe_candidates(
    candidates: Vec<HumanApplyGlobalCandidate>,
) -> Vec<HumanApplyGlobalCandidate> {
    let mut deduped = BTreeMap::new();
    for candidate in candidates {
        deduped
            .entry(candidate.sort_key())
            .or_insert_with(|| candidate);
    }
    deduped.into_values().collect()
}

fn human_apply_global_implicit_profile(
    candidate: &HumanApplyGlobalCandidate,
    current_source_interface: &npa_frontend::HumanSourceInterface,
    imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
) -> Vec<npa_frontend::MachineCallableBinderVisibility> {
    match candidate {
        HumanApplyGlobalCandidate::Current {
            name,
            decl_interface_hash,
        } => current_source_interface
            .declarations
            .iter()
            .find(|decl| {
                npa_cert::Name(decl.name.parts.clone()) == *name
                    && decl.decl_interface_hash == Some(*decl_interface_hash)
            })
            .map(|decl| npa_frontend::machine_callable_profile_from_human_binders(&decl.binders))
            .unwrap_or_default(),
        HumanApplyGlobalCandidate::Imported {
            module,
            export_hash,
            certificate_hash,
            name,
            decl_interface_hash,
        } => imported_source_interfaces
            .iter()
            .filter(|interface| {
                interface.module == *module
                    && interface.export_hash == *export_hash
                    && interface.certificate_hash == Some(*certificate_hash)
            })
            .flat_map(|interface| interface.source_interface.declarations.iter())
            .find(|decl| {
                npa_cert::Name(decl.name.parts.clone()) == *name
                    && decl.decl_interface_hash == Some(*decl_interface_hash)
            })
            .map(|decl| npa_frontend::machine_callable_profile_from_human_binders(&decl.binders))
            .or_else(|| {
                if npa_cert::builtin_decl_interface_hash(name) == Some(*decl_interface_hash) {
                    npa_frontend::builtin_machine_callable_profile(name)
                } else {
                    None
                }
            })
            .unwrap_or_default(),
    }
}

fn human_apply_args_for_type(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    head_type: &Expr,
    implicit_profile: &[npa_frontend::MachineCallableBinderVisibility],
    span: npa_frontend::Span,
    head_label: &str,
) -> Result<Vec<npa_tactic::ApplyArg>, HumanApplyTacticError> {
    let ctx = human_apply_goal_ctx(state, goal, span)?;
    let env = state.env.kernel_env();
    let delta = &state.root.universe_params;
    let mut current = head_type.clone();
    let mut args = Vec::new();

    loop {
        let whnf = env.whnf(&ctx, delta, &current).map_err(|err| {
            human_apply_unsupported_diagnostic(
                span,
                format!("cannot inspect apply head {head_label} type: {err:?}"),
            )
        })?;
        if env
            .is_defeq(&ctx, delta, &whnf, &goal.target)
            .map_err(|err| {
                human_apply_unsupported_diagnostic(
                    span,
                    format!("cannot compare apply head {head_label} with target: {err:?}"),
                )
            })?
        {
            break;
        }

        let Expr::Pi { ty, body, .. } = whnf else {
            break;
        };
        let domain = Arc::unwrap_or_clone(ty);
        let is_implicit = implicit_profile.get(args.len()).is_some_and(|visibility| {
            *visibility == npa_frontend::MachineCallableBinderVisibility::Implicit
        });
        let is_proof_relevant = human_apply_domain_is_proof_relevant(
            state, goal, &ctx, &domain, span,
        )
        .or_else(|error| {
            human_apply_eq_premise_fallback(&domain)
                .then_some(true)
                .ok_or(error)
        })?;
        let arg = if !is_proof_relevant {
            if human_apply_body_returns_current_binder(body.as_ref()) {
                human_apply_nonproof_arg_from_target(goal)
                    .unwrap_or(npa_tactic::ApplyArg::InferFromTarget)
            } else {
                npa_tactic::ApplyArg::InferFromTarget
            }
        } else if is_implicit {
            npa_tactic::ApplyArg::InferFromTarget
        } else {
            npa_tactic::ApplyArg::Subgoal { name_hint: None }
        };
        let placeholder = human_apply_placeholder(&arg, goal);
        current = instantiate(&body, &placeholder).map_err(|err| {
            human_apply_unsupported_diagnostic(
                span,
                format!("cannot instantiate apply head {head_label} type: {err:?}"),
            )
        })?;
        args.push(arg);
    }

    Ok(args)
}

fn human_apply_goal_ctx(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> Result<Ctx, HumanApplyTacticError> {
    let mut ctx = Ctx::new();
    let env = state.env.kernel_env();
    for local in &goal.context {
        env.check(
            &ctx,
            &state.root.universe_params,
            &local.ty,
            &Expr::sort(npa_kernel::type0()),
        )
        .or_else(|_| {
            env.infer(&ctx, &state.root.universe_params, &local.ty)
                .map(|_| ())
        })
        .map_err(|err| {
            human_apply_unsupported_diagnostic(
                span,
                format!("cannot inspect local context for apply: {err:?}"),
            )
        })?;
        match &local.value {
            Some(value) => ctx.push_definition(local.name.clone(), local.ty.clone(), value.clone()),
            None => ctx.push_assumption(local.name.clone(), local.ty.clone()),
        }
    }
    Ok(ctx)
}

fn human_apply_domain_is_proof_relevant(
    state: &npa_tactic::MachineProofState,
    goal: &npa_tactic::MachineGoal,
    ctx: &Ctx,
    domain: &Expr,
    span: npa_frontend::Span,
) -> Result<bool, HumanApplyTacticError> {
    let sort = state
        .env
        .kernel_env()
        .infer(ctx, &state.root.universe_params, domain)
        .map_err(|err| {
            human_apply_unsupported_diagnostic(
                span,
                format!(
                    "cannot infer apply premise type for goal {}: {err:?}",
                    goal.id.0
                ),
            )
        })?;
    Ok(matches!(sort, Expr::Sort(level) if level == npa_kernel::prop()))
}

fn human_apply_eq_premise_fallback(domain: &Expr) -> bool {
    let (head, _) = human_app_head_and_args(domain);
    matches!(head, Expr::Const { name, .. } if name == "Eq")
}

fn human_apply_placeholder(arg: &npa_tactic::ApplyArg, goal: &npa_tactic::MachineGoal) -> Expr {
    match arg {
        npa_tactic::ApplyArg::InferFromTarget => goal.target.clone(),
        npa_tactic::ApplyArg::Term(_) => goal.target.clone(),
        npa_tactic::ApplyArg::Subgoal { .. } => Expr::bvar(0),
    }
}

fn human_apply_body_returns_current_binder(body: &Expr) -> bool {
    let mut depth = 0;
    let mut current = body;
    while let Expr::Pi { body, .. } = current {
        depth += 1;
        current = body;
    }
    matches!(current, Expr::BVar(index) if *index as usize == depth)
}

fn human_apply_nonproof_arg_from_target(
    goal: &npa_tactic::MachineGoal,
) -> Option<npa_tactic::ApplyArg> {
    let source = human_apply_render_target_arg(&goal.target, goal)?;
    Some(npa_tactic::ApplyArg::Term(
        npa_tactic::MachineTermSource::new_checked(source).ok()?,
    ))
}

fn human_apply_render_target_arg(expr: &Expr, goal: &npa_tactic::MachineGoal) -> Option<String> {
    match expr {
        Expr::BVar(index) => {
            let index = *index as usize;
            if index >= goal.context.len() {
                return None;
            }
            Some(goal.context[goal.context.len() - 1 - index].name.clone())
        }
        Expr::Const { name, levels } if levels.is_empty() => Some(name.clone()),
        Expr::Sort(level) if *level == npa_kernel::prop() => Some("Prop".to_owned()),
        Expr::Sort(level) if *level == npa_kernel::type0() => Some("Type".to_owned()),
        _ => None,
    }
}

fn human_apply_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    resolved: &HumanApplyResolved,
) -> HumanApplyTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::TypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::TooFewApplyArguments
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousApplyArgument
        | npa_tactic::MachineTacticDiagnosticKind::MissingExplicitArgument
        | npa_tactic::MachineTacticDiagnosticKind::SubgoalDataArgument => {
            human_tactic_machine_diagnostic(
                &diagnostic,
                resolved.span,
                Some(goal),
                Some(npa_frontend::HumanDiagnosticKind::TypeMismatch),
                format!(
                    "cannot apply `{}`\n\ntarget:\n  {:?}\n\nhead type:\n  {:?}\n\n{}",
                    resolved.head_label, goal.target, resolved.head_type, diagnostic.message
                ),
            )
            .into()
        }
        _ => diagnostic.into(),
    }
}

fn human_smt_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> HumanApplyTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::TypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::UnknownTacticHead
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousTacticHead
        | npa_tactic::MachineTacticDiagnosticKind::UnknownLocalName
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousLocalName => {
            human_tactic_machine_diagnostic(
                &diagnostic,
                span,
                Some(goal),
                Some(npa_frontend::HumanDiagnosticKind::TypeMismatch),
                format!("smt could not close the goal: {}", diagnostic.message),
            )
            .into()
        }
        _ => diagnostic.into(),
    }
}

fn human_rewrite_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    resolved: &HumanRewriteResolved,
    site: npa_tactic::RewriteSite,
) -> HumanRewriteTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::AmbiguousRewriteRule
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedEqTarget
        | npa_tactic::MachineTacticDiagnosticKind::InvalidMetaDependency
        | npa_tactic::MachineTacticDiagnosticKind::MissingExplicitArgument
        | npa_tactic::MachineTacticDiagnosticKind::TacticPrimitiveUnavailable
        | npa_tactic::MachineTacticDiagnosticKind::TooManyApplyArguments
        | npa_tactic::MachineTacticDiagnosticKind::TypeMismatch => {
            human_tactic_machine_diagnostic(
                &diagnostic,
                resolved.span,
                Some(goal),
                Some(npa_frontend::HumanDiagnosticKind::TypeMismatch),
                format!(
                    "cannot rewrite with `{}`\n\ndirection:\n  {:?}\n\nsite:\n  {:?}\n\ntarget:\n  {:?}\n\nrule type:\n  {:?}\n\n{}",
                    resolved.head_label,
                    resolved.direction,
                    site,
                    goal.target,
                    resolved.head_type,
                    diagnostic.message
                ),
            )
            .into()
        }
        _ => diagnostic.into(),
    }
}

fn human_simp_lite_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> HumanSimpLiteTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::AmbiguousRewriteRule
        | npa_tactic::MachineTacticDiagnosticKind::AmbiguousSimpRule
        | npa_tactic::MachineTacticDiagnosticKind::ExpectedEqTarget
        | npa_tactic::MachineTacticDiagnosticKind::InvalidSimpRule
        | npa_tactic::MachineTacticDiagnosticKind::SimpNoProgress
        | npa_tactic::MachineTacticDiagnosticKind::TacticPrimitiveUnavailable
        | npa_tactic::MachineTacticDiagnosticKind::TypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::UnknownSimpRule => {
            human_tactic_machine_diagnostic(
                &diagnostic,
                span,
                Some(goal),
                Some(npa_frontend::HumanDiagnosticKind::TypeMismatch),
                format!(
                    "simp-lite could not close the target\n\ntarget:\n  {:?}\n\n{}",
                    goal.target, diagnostic.message
                ),
            )
            .into()
        }
        _ => diagnostic.into(),
    }
}

fn human_simp_lite_not_closed_diagnostic(
    span: npa_frontend::Span,
    goal: &npa_tactic::MachineGoal,
    residual_target: Option<&Expr>,
) -> npa_frontend::HumanDiagnostic {
    let mut message = format!(
        "simp-lite simplified the target but did not close it in the Human MVP\n\noriginal target:\n  {:?}",
        goal.target
    );
    if let Some(target) = residual_target {
        message.push_str(&format!("\n\nresidual target:\n  {target:?}"));
    }
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::TypeMismatch,
        span,
        message,
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticExecution)
    .with_payload(human_tactic_goal_payload(goal, span))
}

fn human_induction_machine_error(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    goal: &npa_tactic::MachineGoal,
    span: npa_frontend::Span,
) -> HumanInductionTacticError {
    match &diagnostic.kind {
        npa_tactic::MachineTacticDiagnosticKind::AmbiguousLocalName
        | npa_tactic::MachineTacticDiagnosticKind::InvalidInductionTarget
        | npa_tactic::MachineTacticDiagnosticKind::InvalidMachineTactic
        | npa_tactic::MachineTacticDiagnosticKind::TacticPrimitiveUnavailable
        | npa_tactic::MachineTacticDiagnosticKind::TypeMismatch
        | npa_tactic::MachineTacticDiagnosticKind::UnknownLocalName => {
            human_tactic_machine_diagnostic(
                &diagnostic,
                span,
                Some(goal),
                Some(npa_frontend::HumanDiagnosticKind::UnsupportedTactic),
                format!(
                    "cannot perform simple induction in the Human MVP\n\ntarget:\n  {:?}\n\n{}",
                    goal.target, diagnostic.message
                ),
            )
            .into()
        }
        _ => diagnostic.into(),
    }
}

fn human_induction_unsupported_diagnostic(
    span: npa_frontend::Span,
    message: impl Into<String>,
) -> npa_frontend::HumanDiagnostic {
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic,
        span,
        message,
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
}

fn human_rewrite_unsupported_head_diagnostic(
    span: npa_frontend::Span,
) -> npa_frontend::HumanDiagnostic {
    human_rewrite_unsupported_diagnostic(
        span,
        "Human rw MVP only supports a resolved local or global name as the rule head",
    )
}

fn human_rewrite_unsupported_diagnostic(
    span: npa_frontend::Span,
    message: impl Into<String>,
) -> npa_frontend::HumanDiagnostic {
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic,
        span,
        message,
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
}

fn human_apply_unsupported_head_diagnostic(
    span: npa_frontend::Span,
) -> npa_frontend::HumanDiagnostic {
    human_apply_unsupported_diagnostic(
        span,
        "Human apply MVP only supports a resolved local or global name as the head",
    )
}

fn human_apply_unsupported_diagnostic(
    span: npa_frontend::Span,
    message: impl Into<String>,
) -> npa_frontend::HumanDiagnostic {
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnsupportedTactic,
        span,
        message,
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticValidation)
}

fn human_apply_universe_args(levels: Option<&[npa_frontend::HumanLevel]>) -> Vec<Level> {
    levels
        .unwrap_or_default()
        .iter()
        .map(human_apply_level)
        .collect()
}

fn human_apply_level(level: &npa_frontend::HumanLevel) -> Level {
    match level {
        npa_frontend::HumanLevel::Nat { value, .. } => {
            let mut level = Level::zero();
            for _ in 0..*value {
                level = Level::succ(level);
            }
            level
        }
        npa_frontend::HumanLevel::Param { name, .. } => Level::param(name.clone()),
        npa_frontend::HumanLevel::Succ { level, .. } => Level::succ(human_apply_level(level)),
        npa_frontend::HumanLevel::Max { lhs, rhs, .. } => {
            Level::max(human_apply_level(lhs), human_apply_level(rhs))
        }
        npa_frontend::HumanLevel::IMax { lhs, rhs, .. } => {
            Level::imax(human_apply_level(lhs), human_apply_level(rhs))
        }
    }
}

fn human_apply_name_has_suffix(name: &[String], suffix: &[String]) -> bool {
    name.len() >= suffix.len() && &name[(name.len() - suffix.len())..] == suffix
}

fn human_apply_hash_hex(hash: &npa_cert::Hash) -> String {
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn human_script_intro_error(error: HumanIntroTacticError) -> HumanTacticScriptError {
    match error {
        HumanIntroTacticError::Human(error) => HumanTacticScriptError::Human(error),
        HumanIntroTacticError::Machine(diagnostic) => HumanTacticScriptError::Machine(diagnostic),
    }
}

fn human_script_apply_error(error: HumanApplyTacticError) -> HumanTacticScriptError {
    match error {
        HumanApplyTacticError::Human(error) => HumanTacticScriptError::Human(error),
        HumanApplyTacticError::Machine(diagnostic) => HumanTacticScriptError::Machine(diagnostic),
    }
}

fn human_script_rewrite_error(error: HumanRewriteTacticError) -> HumanTacticScriptError {
    match error {
        HumanRewriteTacticError::Human(error) => HumanTacticScriptError::Human(error),
        HumanRewriteTacticError::Machine(diagnostic) => HumanTacticScriptError::Machine(diagnostic),
    }
}

fn human_script_simp_lite_error(error: HumanSimpLiteTacticError) -> HumanTacticScriptError {
    match error {
        HumanSimpLiteTacticError::Human(error) => HumanTacticScriptError::Human(error),
        HumanSimpLiteTacticError::Machine(diagnostic) => {
            HumanTacticScriptError::Machine(diagnostic)
        }
    }
}

fn human_script_induction_error(error: HumanInductionTacticError) -> HumanTacticScriptError {
    match error {
        HumanInductionTacticError::Human(error) => HumanTacticScriptError::Human(error),
        HumanInductionTacticError::Machine(diagnostic) => {
            HumanTacticScriptError::Machine(diagnostic)
        }
    }
}

fn human_script_term_error(error: HumanTacticTermError) -> HumanTacticScriptError {
    match error {
        HumanTacticTermError::Human(error) => HumanTacticScriptError::Human(error),
        HumanTacticTermError::Machine(diagnostic) => HumanTacticScriptError::Machine(diagnostic),
    }
}

fn human_script_no_goals_diagnostic(span: npa_frontend::Span) -> npa_frontend::HumanDiagnostic {
    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::NoGoalsButTacticRemaining,
        span,
        "Human tactic script has a remaining tactic after all goals were closed",
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticExecution)
}

fn human_script_unresolved_goal_diagnostic(
    span: npa_frontend::Span,
    state: &npa_tactic::MachineProofState,
) -> npa_frontend::HumanDiagnostic {
    let open_goal_count = state.open_goals.len();
    let hole_goals = state
        .open_goals
        .iter()
        .filter_map(|goal_id| state.goal(*goal_id).ok())
        .map(|goal| human_tactic_goal_display(&goal, span))
        .collect::<Vec<_>>();

    npa_frontend::HumanDiagnostic::error(
        npa_frontend::HumanDiagnosticKind::UnresolvedGoal,
        span,
        format!("Human tactic script finished with {open_goal_count} open goal(s)"),
    )
    .with_phase(npa_frontend::HumanDiagnosticPhase::TacticUnresolvedGoal)
    .with_payload(npa_frontend::HumanDiagnosticPayload {
        hole_goals,
        ..npa_frontend::HumanDiagnosticPayload::default()
    })
}

fn frontend_import_from_tactic_ref(
    import: &npa_tactic::VerifiedImportRef,
) -> npa_frontend::VerifiedImport {
    let mut frontend = npa_frontend::VerifiedImport::from(import.verified_module());
    let visible_exports = import
        .exports()
        .iter()
        .map(|export| (export.name.clone(), export.decl_interface_hash))
        .collect::<std::collections::BTreeSet<_>>();
    frontend.exports.retain(|export| {
        visible_exports.contains(&(export.name.clone(), export.decl_interface_hash))
    });
    frontend
}

fn human_tactic_current_generated_decls(
    checked_current_decls: &[npa_tactic::CheckedCurrentDecl],
) -> Vec<npa_frontend::MachineCheckedCurrentGeneratedDecl> {
    let mut generated = Vec::new();
    for decl in checked_current_decls {
        if let Decl::Inductive { data, .. } = decl.core_decl() {
            for constructor in &data.constructors {
                generated.push(npa_frontend::MachineCheckedCurrentGeneratedDecl {
                    name: npa_cert::Name::from_dotted(&constructor.name),
                    parent_source_index: decl.source_index(),
                    decl_interface_hash: decl.signature().decl_interface_hash(),
                });
            }
            if let Some(recursor) = &data.recursor {
                generated.push(npa_frontend::MachineCheckedCurrentGeneratedDecl {
                    name: npa_cert::Name::from_dotted(&recursor.name),
                    parent_source_index: decl.source_index(),
                    decl_interface_hash: decl.signature().decl_interface_hash(),
                });
            }
        }
    }
    generated
}

fn active_human_verified_import_refs(
    verified_modules: &[npa_cert::VerifiedModule],
    active_imports: &[npa_frontend::HumanImportedSourceInterface],
) -> Result<Vec<npa_tactic::VerifiedImportRef>, HumanStartProofError> {
    active_imports
        .iter()
        .map(|active| {
            let verified = verified_modules
                .iter()
                .find(|module| {
                    let import = npa_frontend::VerifiedImport::from(*module);
                    import.module == active.module
                        && import.export_hash == active.export_hash
                        && import.certificate_hash == active.certificate_hash
                })
                .ok_or_else(|| {
                    npa_tactic::MachineTacticDiagnostic::new(
                        npa_tactic::MachineTacticDiagnosticKind::InvalidVerifiedImport,
                        format!(
                            "active Human import {} is not present in verified modules",
                            active.module.as_dotted()
                        ),
                    )
                })?;
            npa_tactic::VerifiedImportRef::from_verified_module(verified)
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(HumanStartProofError::from)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        create_machine_session, get_human_proof_state, HumanCurrentModuleSource,
        HumanDocumentVersion, HumanProofSessionStore, HumanProofStateStartRequest,
        HumanStateRequestHeader, HumanTacticStateRecordRequest,
    };

    fn human_payload(
        diagnostic: &npa_frontend::HumanDiagnostic,
    ) -> &npa_frontend::HumanDiagnosticPayload {
        diagnostic
            .payload
            .as_deref()
            .expect("Human diagnostic should carry a structured payload")
    }

    fn human_formalize_workspace_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|path| path.parent())
            .expect("npa-api should live under crates/")
            .to_path_buf()
    }

    fn human_formalize_options_bytes() -> Vec<u8> {
        let options = crate::AdvancedAiOptions {
            formalization: Some(crate::AdvancedFormalizationOptions {
                tactic_options_canonical_bytes: npa_tactic::machine_tactic_options_canonical_bytes(
                    &npa_tactic::MachineTacticOptions::default(),
                ),
                tactic_budget_canonical_bytes: npa_tactic::tactic_budget_canonical_bytes(
                    npa_tactic::TacticBudget::default(),
                ),
            }),
            ..Default::default()
        };
        crate::advanced_ai_options_canonical_bytes(&options).unwrap()
    }

    fn human_formalize_statement(source: &str) -> crate::AdvancedMachineSurfaceTerm {
        crate::AdvancedMachineSurfaceTerm {
            universe_params: Vec::new(),
            term_canonical_bytes: npa_frontend::canonicalize_machine_term_source(source)
                .unwrap()
                .canonical_bytes,
        }
    }

    fn human_formalize_source(
        source_text: &str,
    ) -> (
        crate::AdvancedMachineFormalizationSourceDocumentRef,
        crate::AdvancedMachineFormalizationClaimSpan,
        Hash,
        Hash,
    ) {
        let bytes = source_text.as_bytes();
        let source_document_hash = crate::advanced_ai_formalization_source_document_hash(bytes);
        let claim_span_hash = crate::advanced_ai_formalization_claim_span_hash(
            source_document_hash,
            0,
            bytes.len() as u64,
            bytes,
        );
        (
            crate::AdvancedMachineFormalizationSourceDocumentRef::Inline {
                source_document_hash,
                raw_utf8_bytes: bytes.to_vec(),
            },
            crate::AdvancedMachineFormalizationClaimSpan {
                start_byte: 0,
                end_byte: bytes.len() as u64,
                claim_span_hash,
            },
            source_document_hash,
            claim_span_hash,
        )
    }

    fn human_formalize_payload_with(
        source_text: &str,
        statement_source: &str,
        intent_record: Option<crate::AdvancedFormalizationIntentRecord>,
        optional_proof_candidate: Option<crate::AdvancedMachineFormalizationProofCandidate>,
    ) -> crate::AdvancedMachineFormalizationCheckPayload {
        let (source_document, claim_span, _, _) = human_formalize_source(source_text);
        crate::AdvancedMachineFormalizationCheckPayload {
            candidate: crate::AdvancedMachineFormalizationCandidate {
                source_document,
                claim_span,
                statement: human_formalize_statement(statement_source),
                optional_proof_candidate,
            },
            intent_record,
        }
    }

    fn human_formalize_request(
        payload: crate::AdvancedMachineFormalizationCheckPayload,
        options_bytes: Vec<u8>,
    ) -> Vec<u8> {
        let options_hash = crate::advanced_ai_options_hash(&options_bytes);
        let imports = Vec::new();
        let env_fingerprint = crate::advanced_ai_env_fingerprint(
            crate::AdvancedAiProfileVersion::MvpV1,
            crate::AdvancedAiTaskKind::NaturalLanguageFormalization,
            &imports,
            options_hash,
        )
        .unwrap();
        let envelope = crate::AdvancedAiCandidateEnvelope {
            profile_version: crate::AdvancedAiProfileVersion::MvpV1,
            task_kind: crate::AdvancedAiTaskKind::NaturalLanguageFormalization,
            target: crate::AdvancedAiTarget {
                env_fingerprint,
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports,
            options: crate::AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: crate::advanced_ai_formalization_payload_canonical_bytes(&payload).unwrap(),
        };
        crate::advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn human_formalize_accepted_statement_hash_for_options(
        options_bytes: &[u8],
        statement_source: &str,
    ) -> Hash {
        let imports = Vec::new();
        let options_hash = crate::advanced_ai_options_hash(options_bytes);
        let env_fingerprint = crate::advanced_ai_env_fingerprint(
            crate::AdvancedAiProfileVersion::MvpV1,
            crate::AdvancedAiTaskKind::NaturalLanguageFormalization,
            &imports,
            options_hash,
        )
        .unwrap();
        let statement = human_formalize_statement(statement_source);
        let ast =
            npa_frontend::decode_machine_term_source_canonical(&statement.term_canonical_bytes)
                .unwrap();
        let context = npa_frontend::MachineTermElabContext::from_verified_modules(
            &[],
            &[],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let options = npa_frontend::MachineCompileOptions {
            mode: npa_frontend::MachineSurfaceMode::Complete,
            allow_universe_meta: false,
        };
        let (accepted, _) =
            npa_frontend::elaborate_machine_term_infer_from_ast(&ast, &context, &options).unwrap();
        crate::advanced_ai_formalization_accepted_statement_hash(env_fingerprint, &[], &accepted)
    }

    fn human_formalize_intent_record_for(
        source_text: &str,
        statement: &crate::AdvancedMachineSurfaceTerm,
        status: crate::AdvancedFormalizationIntentStatus,
    ) -> crate::AdvancedFormalizationIntentRecord {
        let (_, _, source_document_hash, claim_span_hash) = human_formalize_source(source_text);
        crate::AdvancedFormalizationIntentRecord {
            source_document_hash,
            claim_span_hash,
            candidate_statement_hash: crate::advanced_ai_formalization_candidate_statement_hash(
                statement,
            ),
            status,
        }
    }

    fn human_formalize_exact_proof_candidate(
        statement: &crate::AdvancedMachineSurfaceTerm,
        proof_source: &str,
    ) -> crate::AdvancedMachineFormalizationProofCandidate {
        crate::AdvancedMachineFormalizationProofCandidate {
            candidate_statement_hash: crate::advanced_ai_formalization_candidate_statement_hash(
                statement,
            ),
            tactic: npa_tactic::MachineTacticCandidate::Exact {
                term: npa_tactic::RawMachineTerm::new(proof_source),
            },
        }
    }

    fn human_formalize_success_payload(
        report: &HumanFormalizeCandidateReport,
    ) -> (
        crate::AdvancedFormalizationSuccessKind,
        Option<Hash>,
        Option<Hash>,
    ) {
        let crate::AdvancedAiEndpointResponse::Success { payload, .. } =
            &report.validation_response
        else {
            panic!("expected Human formalize validation success");
        };
        let crate::AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind,
            accepted_statement_hash,
            formalization_proof_root_hash,
        } = payload.as_ref()
        else {
            panic!("expected Human formalize payload");
        };
        (
            *kind,
            *accepted_statement_hash,
            *formalization_proof_root_hash,
        )
    }

    #[test]
    fn human_formalize_returns_multiple_candidates_without_verifying_unconfirmed() {
        let options_bytes = human_formalize_options_bytes();
        let first_request = human_formalize_request(
            human_formalize_payload_with("claim: proposition", "Prop", None, None),
            options_bytes.clone(),
        );
        let second_request = human_formalize_request(
            human_formalize_payload_with("claim: universe", "Type", None, None),
            options_bytes,
        );
        let workspace_root = human_formalize_workspace_root();

        let ok = run_human_formalize(HumanFormalizeRequest {
            candidates: vec![
                HumanFormalizeCandidateRequest {
                    request_canonical_bytes: first_request,
                    reverse_translation: "the claim is a proposition".to_owned(),
                    ambiguity_report: vec!["source does not name a theorem".to_owned()],
                    confidence_microunits: Some(250_000),
                },
                HumanFormalizeCandidateRequest {
                    request_canonical_bytes: second_request,
                    reverse_translation: "the claim is a universe-level statement".to_owned(),
                    ambiguity_report: vec![
                        "source uses informal universe wording".to_owned(),
                        "candidate must be reviewed before proof search".to_owned(),
                    ],
                    confidence_microunits: Some(900_000),
                },
            ],
            verified_imports: &[],
            workspace_root: &workspace_root,
        });

        assert_eq!(crate::HUMAN_FORMALIZE_ENDPOINT, "/formalize");
        assert_eq!(ok.candidates.len(), 2);
        let first = &ok.candidates[0];
        assert_eq!(first.reverse_translation, "the claim is a proposition");
        assert_eq!(
            first.ambiguity_report,
            vec!["source does not name a theorem".to_owned()]
        );
        assert_eq!(first.confidence_microunits, Some(250_000));
        assert!(first.candidate_statement_hash.is_some());
        assert!(first.accepted_statement_hash.is_some());
        assert_eq!(first.formal_statement_hash, None);
        assert_eq!(
            first.review_status,
            HumanFormalizationReviewStatus::MissingIntent
        );
        assert_eq!(
            first.proof_search_status,
            HumanFormalizationProofSearchStatus::NotRequested
        );
        assert_eq!(
            first.validation_kind,
            Some(crate::AdvancedFormalizationSuccessKind::CandidateStatementChecked)
        );
        assert!(!first.verified);

        let second = &ok.candidates[1];
        assert_eq!(
            second.ambiguity_report,
            vec![
                "source uses informal universe wording".to_owned(),
                "candidate must be reviewed before proof search".to_owned()
            ]
        );
        assert!(second.candidate_statement_hash.is_some());
        assert!(second.accepted_statement_hash.is_some());
        assert_eq!(second.formal_statement_hash, None);
        assert_eq!(
            second.review_status,
            HumanFormalizationReviewStatus::MissingIntent
        );
        assert_eq!(
            second.proof_search_status,
            HumanFormalizationProofSearchStatus::NotRequested
        );
        assert!(!second.verified);
    }

    #[test]
    fn human_formalize_blocks_unconfirmed_proof_search_until_reviewed() {
        let statement = human_formalize_statement("Type");
        let request = human_formalize_request(
            human_formalize_payload_with(
                "claim: Type",
                "Type",
                None,
                Some(human_formalize_exact_proof_candidate(&statement, "Prop")),
            ),
            human_formalize_options_bytes(),
        );
        let workspace_root = human_formalize_workspace_root();

        let ok = run_human_formalize(HumanFormalizeRequest {
            candidates: vec![HumanFormalizeCandidateRequest {
                request_canonical_bytes: request,
                reverse_translation: "the informal claim maps to Type".to_owned(),
                ambiguity_report: vec!["review is required before proof search".to_owned()],
                confidence_microunits: Some(990_000),
            }],
            verified_imports: &[],
            workspace_root: &workspace_root,
        });

        let report = &ok.candidates[0];
        assert_eq!(
            report.review_status,
            HumanFormalizationReviewStatus::MissingIntent
        );
        assert_eq!(
            report.proof_search_status,
            HumanFormalizationProofSearchStatus::BlockedUntilConfirmed
        );
        assert_eq!(
            report.validation_kind,
            Some(crate::AdvancedFormalizationSuccessKind::CandidateStatementChecked)
        );
        assert!(report.accepted_statement_hash.is_some());
        assert_eq!(report.formal_statement_hash, None);
        assert!(!report.verified);

        let (kind, accepted_statement_hash, proof_root_hash) =
            human_formalize_success_payload(report);
        assert_eq!(
            kind,
            crate::AdvancedFormalizationSuccessKind::CandidateStatementChecked
        );
        assert!(accepted_statement_hash.is_some());
        assert_eq!(proof_root_hash, None);
    }

    #[test]
    fn human_formalize_blocks_proof_search_when_reviewed_hash_is_not_confirmed() {
        let options_bytes = human_formalize_options_bytes();
        let statement = human_formalize_statement("Type");
        let wrong_reviewed_hash =
            human_formalize_accepted_statement_hash_for_options(&options_bytes, "Prop");
        let intent = human_formalize_intent_record_for(
            "claim: Type",
            &statement,
            crate::AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: crate::AdvancedReviewerId::Human {
                    stable_id_ascii: b"reviewer-1".to_vec(),
                },
                accepted_statement_hash: wrong_reviewed_hash,
            },
        );
        let request = human_formalize_request(
            human_formalize_payload_with(
                "claim: Type",
                "Type",
                Some(intent),
                Some(human_formalize_exact_proof_candidate(&statement, "Prop")),
            ),
            options_bytes,
        );
        let workspace_root = human_formalize_workspace_root();

        let ok = run_human_formalize(HumanFormalizeRequest {
            candidates: vec![HumanFormalizeCandidateRequest {
                request_canonical_bytes: request,
                reverse_translation: "the reviewer hash does not match this statement".to_owned(),
                ambiguity_report: Vec::new(),
                confidence_microunits: None,
            }],
            verified_imports: &[],
            workspace_root: &workspace_root,
        });

        let report = &ok.candidates[0];
        assert_eq!(
            report.proof_search_status,
            HumanFormalizationProofSearchStatus::BlockedUntilConfirmed
        );
        assert_eq!(
            report.validation_kind,
            Some(crate::AdvancedFormalizationSuccessKind::IntentRecordOnly)
        );
        assert_eq!(report.accepted_statement_hash, None);
        assert_eq!(report.formal_statement_hash, None);
        assert!(!report.verified);

        let (kind, _, proof_root_hash) = human_formalize_success_payload(report);
        assert_eq!(
            kind,
            crate::AdvancedFormalizationSuccessKind::IntentRecordOnly
        );
        assert_eq!(proof_root_hash, None);
    }

    #[test]
    fn human_formalize_reviewed_proof_separates_intent_certificate_from_proof_certificate() {
        let options_bytes = human_formalize_options_bytes();
        let statement = human_formalize_statement("Type");
        let accepted_hash =
            human_formalize_accepted_statement_hash_for_options(&options_bytes, "Type");
        let intent = human_formalize_intent_record_for(
            "claim: Type",
            &statement,
            crate::AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: crate::AdvancedReviewerId::System {
                    system_id_ascii: b"review-ui".to_vec(),
                    actor_id_ascii: b"user-123".to_vec(),
                },
                accepted_statement_hash: accepted_hash,
            },
        );
        let request = human_formalize_request(
            human_formalize_payload_with(
                "claim: Type",
                "Type",
                Some(intent),
                Some(human_formalize_exact_proof_candidate(&statement, "Prop")),
            ),
            options_bytes,
        );
        let workspace_root = human_formalize_workspace_root();

        let ok = run_human_formalize(HumanFormalizeRequest {
            candidates: vec![
                HumanFormalizeCandidateRequest {
                    request_canonical_bytes: request.clone(),
                    reverse_translation: "the claim is Type".to_owned(),
                    ambiguity_report: Vec::new(),
                    confidence_microunits: Some(100_000),
                },
                HumanFormalizeCandidateRequest {
                    request_canonical_bytes: request,
                    reverse_translation: "same formal claim with different explanation".to_owned(),
                    ambiguity_report: vec!["wording changed after review".to_owned()],
                    confidence_microunits: Some(950_000),
                },
            ],
            verified_imports: &[],
            workspace_root: &workspace_root,
        });

        let first = &ok.candidates[0];
        let second = &ok.candidates[1];
        assert_eq!(
            first.proof_search_status,
            HumanFormalizationProofSearchStatus::Checked
        );
        assert_eq!(
            second.proof_search_status,
            HumanFormalizationProofSearchStatus::Checked
        );
        assert!(first.verified);
        assert!(second.verified);
        assert_eq!(first.formal_statement_hash, Some(accepted_hash));
        assert_eq!(second.formal_statement_hash, Some(accepted_hash));
        assert_eq!(first.accepted_statement_hash, Some(accepted_hash));
        assert_eq!(second.accepted_statement_hash, Some(accepted_hash));
        assert_eq!(
            first.candidate_statement_hash,
            second.candidate_statement_hash
        );

        let first_intent = first.intent_certificate.as_ref().unwrap();
        let second_intent = second.intent_certificate.as_ref().unwrap();
        assert_ne!(
            first_intent.intent_certificate_hash,
            second_intent.intent_certificate_hash
        );
        assert_eq!(
            first_intent.candidate_statement_hash,
            second_intent.candidate_statement_hash
        );

        let (first_kind, first_accepted, first_proof_root) = human_formalize_success_payload(first);
        let (second_kind, second_accepted, second_proof_root) =
            human_formalize_success_payload(second);
        assert_eq!(
            first_kind,
            crate::AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(
            second_kind,
            crate::AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(first_accepted, Some(accepted_hash));
        assert_eq!(second_accepted, Some(accepted_hash));
        assert_eq!(first_proof_root, second_proof_root);
        assert!(first_proof_root.is_some());
    }

    #[test]
    fn human_formalize_intent_status_fixtures_are_deterministic() {
        let options_bytes = human_formalize_options_bytes();
        let reviewed_statement = human_formalize_statement("Prop");
        let reviewed_hash =
            human_formalize_accepted_statement_hash_for_options(&options_bytes, "Prop");
        let rejected_statement = human_formalize_statement("MissingFormalizationName");
        let rejection_reason = b"not the intended theorem".to_vec();
        let rejection_reason_hash =
            crate::advanced_ai_formalization_rejection_reason_hash(&rejection_reason);

        let unreviewed = human_formalize_intent_record_for(
            "claim: unreviewed",
            &reviewed_statement,
            crate::AdvancedFormalizationIntentStatus::Unreviewed,
        );
        let reviewed = human_formalize_intent_record_for(
            "claim: reviewed",
            &reviewed_statement,
            crate::AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: crate::AdvancedReviewerId::Human {
                    stable_id_ascii: b"reviewer-1".to_vec(),
                },
                accepted_statement_hash: reviewed_hash,
            },
        );
        let rejected = human_formalize_intent_record_for(
            "claim: rejected",
            &rejected_statement,
            crate::AdvancedFormalizationIntentStatus::Rejected {
                reviewer: crate::AdvancedReviewerId::Human {
                    stable_id_ascii: b"reviewer-2".to_vec(),
                },
                rejection_reason: crate::AdvancedMachineFormalizationRejectionReasonRef::Inline {
                    rejection_reason_hash,
                    raw_utf8_bytes: rejection_reason,
                },
                rejection_reason_hash,
            },
        );
        let requests = vec![
            HumanFormalizeCandidateRequest {
                request_canonical_bytes: human_formalize_request(
                    human_formalize_payload_with(
                        "claim: unreviewed",
                        "Prop",
                        Some(unreviewed),
                        None,
                    ),
                    options_bytes.clone(),
                ),
                reverse_translation: "unreviewed candidate".to_owned(),
                ambiguity_report: vec!["pending reviewer".to_owned()],
                confidence_microunits: Some(500_000),
            },
            HumanFormalizeCandidateRequest {
                request_canonical_bytes: human_formalize_request(
                    human_formalize_payload_with("claim: reviewed", "Prop", Some(reviewed), None),
                    options_bytes.clone(),
                ),
                reverse_translation: "reviewed candidate".to_owned(),
                ambiguity_report: Vec::new(),
                confidence_microunits: Some(600_000),
            },
            HumanFormalizeCandidateRequest {
                request_canonical_bytes: human_formalize_request(
                    human_formalize_payload_with(
                        "claim: rejected",
                        "MissingFormalizationName",
                        Some(rejected),
                        None,
                    ),
                    options_bytes,
                ),
                reverse_translation: "rejected candidate".to_owned(),
                ambiguity_report: vec!["reviewer rejected this mapping".to_owned()],
                confidence_microunits: Some(700_000),
            },
        ];
        let workspace_root = human_formalize_workspace_root();

        let first = run_human_formalize(HumanFormalizeRequest {
            candidates: requests.clone(),
            verified_imports: &[],
            workspace_root: &workspace_root,
        });
        let second = run_human_formalize(HumanFormalizeRequest {
            candidates: requests,
            verified_imports: &[],
            workspace_root: &workspace_root,
        });

        assert_eq!(first, second);
        let unreviewed = &first.candidates[0];
        assert_eq!(
            unreviewed.review_status,
            HumanFormalizationReviewStatus::Unreviewed
        );
        assert_eq!(
            unreviewed.validation_kind,
            Some(crate::AdvancedFormalizationSuccessKind::CandidateStatementChecked)
        );
        assert_eq!(unreviewed.formal_statement_hash, None);
        assert!(unreviewed.intent_certificate.is_some());
        assert!(!unreviewed.verified);

        let reviewed = &first.candidates[1];
        assert!(matches!(
            reviewed.review_status,
            HumanFormalizationReviewStatus::Reviewed { .. }
        ));
        assert_eq!(reviewed.formal_statement_hash, Some(reviewed_hash));
        assert_eq!(reviewed.accepted_statement_hash, Some(reviewed_hash));
        assert!(reviewed.intent_certificate.is_some());
        assert!(!reviewed.verified);

        let rejected = &first.candidates[2];
        assert!(matches!(
            rejected.review_status,
            HumanFormalizationReviewStatus::Rejected { .. }
        ));
        assert_eq!(
            rejected.validation_kind,
            Some(crate::AdvancedFormalizationSuccessKind::IntentRecordOnly)
        );
        assert_eq!(rejected.accepted_statement_hash, None);
        assert_eq!(rejected.formal_statement_hash, None);
        assert!(rejected.intent_certificate.is_some());
        assert!(!rejected.verified);
    }

    #[test]
    fn human_api_compiles_source_to_certificate_without_machine_session() {
        let request = HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.Human"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "axiom P : Prop",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        };

        let ok = compile_human_source_to_certificate(request)
            .expect("Human API should compile source to a certificate certificate");
        assert_eq!(ok.source_interface.declarations.len(), 1);
        let bytes = npa_cert::encode_module_cert(&ok.certificate)
            .expect("Human API certificate should encode");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("Human API certificate should verify with normal axiom policy");

        assert_eq!(verified.module(), &npa_cert::Name::from_dotted("Api.Human"));
    }

    #[test]
    fn human_inductive_check_returns_diagnostic_metadata_for_indexed_vec() {
        let data = vec_inductive();
        let generated = npa_cert::generate_inductive_artifacts_v1(&data).unwrap();
        let expected_hashes = npa_cert::inductive_generated_artifact_hashes_v1(&generated).unwrap();

        let response = check_human_inductive(HumanInductiveCheckRequest { declaration: &data });

        assert_eq!(
            response.status,
            HumanInductiveCheckStatus::AcceptedByKernelAndCertificate
        );
        assert_eq!(response.constructors, ["Vec.nil", "Vec.cons"]);
        assert_eq!(response.recursor.as_deref(), Some("Vec.rec"));
        assert_eq!(response.positivity, HumanInductivePositivityStatus::Passed);
        assert_eq!(
            response.recursor_signature_hash,
            expected_hashes.recursor_signature_hash
        );
        assert_eq!(response.iota_rules_hash, expected_hashes.iota_rules_hash);
        assert!(response.diagnostic_only);
        assert!(response.error.is_none());
        assert_eq!(crate::HUMAN_INDUCTIVE_CHECK_ENDPOINT, "/inductive/check");
    }

    #[test]
    fn human_inductive_check_reports_negative_occurrence_as_diagnostic_only_rejection() {
        let data = negative_indexed_inductive();

        let response = check_human_inductive(HumanInductiveCheckRequest { declaration: &data });

        assert_eq!(response.status, HumanInductiveCheckStatus::Rejected);
        assert_eq!(response.constructors, ["BadVec.mk"]);
        assert_eq!(response.recursor, None);
        assert_eq!(response.positivity, HumanInductivePositivityStatus::Failed);
        assert_eq!(response.recursor_signature_hash, None);
        assert_eq!(response.iota_rules_hash, None);
        assert!(response.diagnostic_only);
        assert!(matches!(
            response.error,
            Some(HumanInductiveCheckError::Kernel(
                npa_kernel::Error::NonPositiveOccurrence { .. }
            ))
        ));
    }

    #[test]
    fn human_session_create_returns_open_session_with_initial_document_version() {
        let mut store = HumanProofSessionStore::new();

        let ok = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.Session"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(11),
                    source: "axiom P : Prop",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session id allocation should succeed");

        assert_eq!(ok.document_version, HumanDocumentVersion::initial());
        assert_eq!(ok.status, HumanProofSessionStatus::Open);
        assert!(ok.messages.is_empty());
        let session = store
            .session(&ok.session_id)
            .expect("created Human session should be stored");
        assert_eq!(session.session_id, ok.session_id);
        assert_eq!(session.document.document_id, ok.document_id);
        assert_eq!(session.document.document_version, ok.document_version);
        assert_eq!(session.document.file_id, npa_frontend::FileId(11));
        assert_eq!(session.document.source, "axiom P : Prop");
        assert_eq!(
            session.document.current_module,
            npa_cert::Name::from_dotted("Api.Session")
        );
        assert!(session.source_interface.is_some());
        assert!(session.active_imported_source_interfaces.is_empty());
        assert_eq!(session.current_state_id, None);
        assert!(session.messages.is_empty());
    }

    #[test]
    fn human_session_create_returns_initial_parse_messages_without_closing_session() {
        let mut store = HumanProofSessionStore::new();

        let ok = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.SessionDiagnostics"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(15),
                    source: "def bad : Type :=",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should still open with source diagnostics");

        assert_eq!(ok.status, HumanProofSessionStatus::Open);
        assert_eq!(ok.messages.len(), 1);
        assert_eq!(store.session_count(), 1);
        let session = store
            .session(&ok.session_id)
            .expect("diagnostic session should be stored");
        assert_eq!(session.messages, ok.messages);
        assert!(session.source_interface.is_none());
    }

    #[test]
    fn human_session_document_update_increments_version_and_rejects_stale_state_request() {
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.Update"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(12),
                    source: "axiom P : Prop",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");

        let updated = update_human_document(
            &mut store,
            HumanDocumentUpdateRequest {
                session_id: created.session_id.clone(),
                current_module: npa_cert::Name::from_dotted("Api.Update"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(12),
                    source: "axiom P : Prop\naxiom q : P",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human document update should succeed");

        assert_eq!(updated.document_id, created.document_id);
        assert_eq!(updated.document_version.as_u64(), 2);
        let err = validate_human_state_request_document(
            &store,
            HumanStateRequestHeader {
                session_id: created.session_id.clone(),
                document_id: created.document_id.clone(),
                document_version: created.document_version,
            },
        )
        .expect_err("old document version should be stale after update");
        assert_eq!(
            err,
            HumanStateRequestError::StaleDocumentVersion {
                session_id: created.session_id.clone(),
                document_id: created.document_id.clone(),
                requested: HumanDocumentVersion::initial(),
                current: updated.document_version,
            }
        );

        validate_human_state_request_document(
            &store,
            HumanStateRequestHeader {
                session_id: updated.session_id,
                document_id: updated.document_id,
                document_version: updated.document_version,
            },
        )
        .expect("current document version should validate");
    }

    #[test]
    fn human_incremental_reuses_prefix_and_rejects_old_state_request() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanIncrementalStale",
            "\
axiom P : Prop
axiom hp : P",
        );
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalStale"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(52),
                    source: "\
import Lib.HumanIncrementalStale
def keep : Prop := P
theorem target : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental session should be created");
        let initial_cache = created.incremental_cache.clone();
        assert_eq!(initial_cache.declarations.len(), 2);
        assert_eq!(initial_cache.recomputed_from, Some(0));
        assert!(initial_cache
            .declarations
            .iter()
            .all(|entry| entry.reuse == HumanDocumentIncrementalDeclReuse::Fresh));
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanIncrementalStale.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human incremental proof should start");
        let old_header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };

        let updated = update_human_document(
            &mut store,
            HumanDocumentUpdateRequest {
                session_id: created.session_id.clone(),
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalStale"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(52),
                    source: "\
import Lib.HumanIncrementalStale
def keep : Prop := P

theorem target_changed : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental document update should succeed");

        let err = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: old_header,
                state_id: started.state_id,
            },
        )
        .expect_err("old state request should be stale after a document edit");
        assert!(matches!(
            err,
            HumanStateApiError::StaleDocumentVersion { .. }
        ));
        assert_eq!(updated.document_version.as_u64(), 2);
        assert_eq!(
            updated.incremental_cache.prior_document_version,
            Some(created.document_version)
        );
        assert_eq!(
            updated.incremental_cache.prior_import_interface_hash,
            Some(initial_cache.import_interface_hash)
        );
        assert_eq!(
            updated.incremental_cache.import_interface_hash,
            initial_cache.import_interface_hash
        );
        assert_eq!(updated.incremental_cache.reused_prefix_len, 1);
        assert_eq!(updated.incremental_cache.recomputed_from, Some(1));
        assert_eq!(
            updated.incremental_cache.declarations[0].reuse,
            HumanDocumentIncrementalDeclReuse::Reused
        );
        assert_eq!(
            updated.incremental_cache.declarations[1].reuse,
            HumanDocumentIncrementalDeclReuse::Fresh
        );
        assert_eq!(
            updated.incremental_cache.declarations[0].source_decl_hash,
            initial_cache.declarations[0].source_decl_hash
        );
        assert_eq!(
            updated.incremental_cache.declarations[0].resolved_decl_hash,
            initial_cache.declarations[0].resolved_decl_hash
        );
        assert_eq!(
            updated.incremental_cache.declarations[0].core_decl_hash,
            initial_cache.declarations[0].core_decl_hash
        );
        assert_ne!(
            updated.incremental_cache.declarations[1].source_decl_hash,
            initial_cache.declarations[1].source_decl_hash
        );
    }

    #[test]
    fn human_incremental_import_interface_hash_invalidates_prefix() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanIncrementalImport",
            "\
axiom P : Prop",
        );
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalImport"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(53),
                    source: "axiom keep : Prop",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental import session should be created");

        let updated = update_human_document(
            &mut store,
            HumanDocumentUpdateRequest {
                session_id: created.session_id.clone(),
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalImport"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(53),
                    source: "axiom keep : Prop",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental import update should succeed");

        assert_ne!(
            updated.incremental_cache.import_interface_hash,
            created.incremental_cache.import_interface_hash
        );
        assert_eq!(updated.incremental_cache.reused_prefix_len, 0);
        assert_eq!(updated.incremental_cache.recomputed_from, Some(0));
        assert_eq!(
            updated.incremental_cache.declarations[0].reuse,
            HumanDocumentIncrementalDeclReuse::Fresh
        );
    }

    #[test]
    fn human_incremental_reused_prefix_still_verifies_via_certificate() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanIncrementalVerify",
            "\
axiom P : Prop
axiom hp : P",
        );
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalVerify"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(54),
                    source: "\
import Lib.HumanIncrementalVerify
def keep : Prop := P
theorem target : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental verify session should be created");
        let updated = update_human_document(
            &mut store,
            HumanDocumentUpdateRequest {
                session_id: created.session_id.clone(),
                current_module: npa_cert::Name::from_dotted("Api.HumanIncrementalVerify"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(54),
                    source: "\
import Lib.HumanIncrementalVerify
def keep : Prop := P

theorem target : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human incremental verify update should succeed");
        assert_eq!(updated.incremental_cache.reused_prefix_len, 1);
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: updated.document_version,
        };
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanIncrementalVerify.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human incremental verify proof should start after update");
        let state_fingerprint = store
            .session(&created.session_id)
            .expect("Human incremental verify session should remain stored")
            .proof_states
            .state(&started.state_id)
            .expect("started Human state should be stored")
            .state
            .fingerprint;
        assert_ne!(
            updated.incremental_cache.declarations[0].source_decl_hash,
            state_fingerprint
        );
        assert_ne!(
            updated.incremental_cache.declarations[0].resolved_decl_hash,
            state_fingerprint
        );
        assert_ne!(
            updated.incremental_cache.declarations[0].core_decl_hash,
            state_fingerprint
        );

        let exact = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "exact hp".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(exact.status, HumanTacticRunStatus::Closed);
        assert!(exact.error.is_none());
        let closed_state_id = exact
            .new_state_id
            .expect("closed tactic should record state");
        let ok = verify_human_session(
            &store,
            HumanSessionVerifyRequest {
                header,
                state_id: closed_state_id,
            },
        )
        .expect("reused Human prefix must still verify through certificate checker");

        assert_eq!(ok.status, HumanSessionVerifyStatus::Verified);
        assert_eq!(
            ok.theorem_name,
            npa_cert::Name::from_dotted("Api.HumanIncrementalVerify.target")
        );
        assert!(ok
            .axioms_used
            .iter()
            .any(|axiom| matches!(axiom, MachineAxiomRefWire::Imported { name, .. } if name.as_dotted() == "hp")));
    }

    #[test]
    fn human_lsp_diagnostic_span_converts_to_lsp_range() {
        let source = "first\nsecond line\nthird";
        let diagnostic = npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::TypeMismatch,
            npa_frontend::Span::new(npa_frontend::FileId(61), 6, 12),
            "expected Nat",
        )
        .with_phase(npa_frontend::HumanDiagnosticPhase::Elaborator);

        let lsp = human_lsp_diagnostic_from_human(
            HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(61),
                source,
            },
            &diagnostic,
        );

        assert_eq!(
            lsp.range,
            HumanLspRange {
                start: HumanLspPosition {
                    line: 1,
                    character: 0
                },
                end: HumanLspPosition {
                    line: 1,
                    character: 6
                },
            }
        );
        assert_eq!(lsp.severity, HumanLspDiagnosticSeverity::Error);
        assert_eq!(lsp.code, "type_mismatch");
        assert_eq!(lsp.data.phase.as_deref(), Some("elaborator"));
        assert_eq!(lsp.data.detail.as_deref(), Some("expected Nat"));
    }

    #[test]
    fn human_lsp_diagnostic_kind_codes_include_equation_coverage() {
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::NonExhaustivePatterns
            ),
            "non_exhaustive_patterns"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(&npa_frontend::HumanDiagnosticKind::RedundantEquation),
            "redundant_equation"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::ImpossibleBranchNotProvable
            ),
            "impossible_branch_not_provable"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::RecursiveCallNotDecreasing
            ),
            "recursive_call_not_decreasing"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::MutualCycleWithoutDecrease
            ),
            "mutual_cycle_without_decrease"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::TerminationMeasureNotNat
            ),
            "termination_measure_not_nat"
        );
        assert_eq!(
            human_lsp_diagnostic_kind_code(
                &npa_frontend::HumanDiagnosticKind::MeasureDecreaseProofMissing
            ),
            "measure_decrease_proof_missing"
        );
    }

    #[test]
    fn human_lsp_hover_returns_nat_add_zero_statement_and_axioms() {
        let (store, header, state_id, _goal_id) = human_search_nat_add_zero_fixture();

        let ok = human_lsp_hover(
            &store,
            HumanLspHoverRequest {
                header,
                state_id,
                name: npa_cert::Name::from_dotted("Nat.add_zero"),
            },
        )
        .expect("Human LSP hover should build from theorem index");
        let hover = ok.hover.expect("Nat.add_zero hover should be present");

        assert_eq!(
            hover.theorem.name,
            npa_cert::Name::from_dotted("Nat.add_zero")
        );
        assert_eq!(hover.theorem.kind, HumanTheoremIndexKind::Theorem);
        assert!(!hover.theorem.statement_pretty.is_empty());
        assert!(hover.contents.contains(&hover.theorem.statement_pretty));
        assert!(!hover.theorem.axiom_info.uses_axioms);
        assert!(hover.theorem.axiom_info.axiom_dependencies.is_empty());
        assert!(hover.contents.contains("Nat.add_zero"));
        assert!(hover.contents.contains("axioms: none"));
    }

    #[test]
    fn human_lsp_code_actions_include_tactics_and_search_command() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanLspActions"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(62),
                    source: "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) : Eq.{1} n n := by simp-lite",
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human LSP action session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanLspActions.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human LSP action proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        let state_id = intro.new_state_id.expect("intro should record state");
        let goal_id = intro.selected_goal.expect("intro should select body goal");

        let completions = human_lsp_completions(
            &store,
            HumanLspCompletionRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                max_results: 10,
                include_search_command: true,
            },
        );
        assert!(completions.error.is_none());
        assert!(completions
            .items
            .iter()
            .any(|item| item.insert_text.as_deref() == Some("exact Eq.refl n")));

        let actions = human_lsp_code_actions(
            &store,
            HumanLspCodeActionRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                max_tactic_suggestions: 10,
                include_search_command: true,
            },
        );
        assert!(actions.error.is_none());
        assert!(actions
            .actions
            .iter()
            .any(|action| action.tactic.as_deref() == Some("exact Eq.refl n")));
        assert!(actions
            .actions
            .iter()
            .any(|action| action.tactic.as_deref() == Some("simp-lite")));
        let search = actions
            .actions
            .iter()
            .find_map(|action| action.command.as_ref())
            .expect("Human LSP code actions should include theorem search command");
        assert_eq!(search.command, "npa.human.search.for_goal");
        assert_eq!(search.arguments[0], created.session_id.wire());
        assert_eq!(search.arguments[1], state_id.wire());
        assert_eq!(search.arguments[2], goal_id.wire());

        let goal_view = human_lsp_goal_view(
            &store,
            HumanLspGoalViewRequest {
                header,
                state_id,
                goal_id,
                mode: HumanDisplayMode::Pretty,
                context_options: HumanDisplayContextOptions::default(),
            },
        )
        .expect("Human LSP goal view should use state/goals and display/goal adapters");
        assert_eq!(goal_view.goals.len(), 1);
        assert!(goal_view.focused_goal.text.contains("n : Nat"));
        assert!(goal_view.focused_goal.text.contains("|- n = n"));
    }

    #[test]
    fn human_lsp_document_payloads_return_symbols_tokens_and_inlay_hints() {
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanLspDocument"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(63),
                    source: "theorem id (A : Type) (x : A) : A := by simp-lite",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human LSP document session should be created");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };

        let payloads = human_lsp_document_payloads(
            &store,
            HumanLspDocumentPayloadRequest {
                header: header.clone(),
            },
        )
        .expect("Human LSP document payloads should be available");

        assert!(payloads
            .document_symbols
            .iter()
            .any(|symbol| { symbol.name == "id" && symbol.kind == HumanLspSymbolKind::Theorem }));
        assert!(payloads
            .semantic_tokens
            .iter()
            .any(|token| token.token_type == HumanLspSemanticTokenType::Theorem));
        assert!(payloads
            .semantic_tokens
            .iter()
            .any(|token| token.token_type == HumanLspSemanticTokenType::Variable));
        assert!(payloads
            .inlay_hints
            .iter()
            .any(|hint| hint.label == "explicit binder"));
    }

    #[test]
    fn human_lsp_payloads_do_not_extend_machine_endpoint_envelopes() {
        let endpoints = [
            crate::MachineApiEndpoint::CreateSession,
            crate::MachineApiEndpoint::DeleteSession,
            crate::MachineApiEndpoint::SnapshotGet,
            crate::MachineApiEndpoint::TacticRun,
            crate::MachineApiEndpoint::TacticBatch,
            crate::MachineApiEndpoint::SearchForGoal,
            crate::MachineApiEndpoint::PromptPayload,
            crate::MachineApiEndpoint::Replay,
            crate::MachineApiEndpoint::Verify,
        ];
        let forbidden_machine_names = [
            "lsp",
            "hover",
            "completion",
            "code_action",
            "semantic_token",
            "document_symbol",
            "inlay_hint",
            "goal_view",
        ];

        for endpoint in endpoints {
            let spec = crate::machine_endpoint_envelope_spec(endpoint);
            assert!(forbidden_machine_names
                .iter()
                .all(|forbidden| !spec.endpoint.as_str().contains(forbidden)));
            assert!(spec.fields.iter().all(|field| {
                forbidden_machine_names
                    .iter()
                    .all(|forbidden| !field.name.contains(forbidden))
            }));
        }
    }

    #[test]
    fn human_assistant_payload_includes_goal_tactics_theorems_and_failed_diagnostics() {
        let (store, header, state_id, goal_id) = human_search_nat_add_zero_fixture();

        let ok = human_assistant_payload(
            &store,
            HumanAssistantPayloadRequest {
                header,
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                max_tactic_suggestions: 10,
                max_nearby_theorems: 10,
                failed_tactics: vec![crate::HumanAssistantFailedTacticRequest {
                    tactic: "exact Nat.zero".to_owned(),
                    budget: npa_tactic::TacticBudget::default(),
                }],
            },
        )
        .expect("Human assistant payload should gather UI-only proof context");

        assert_eq!(ok.state_id, state_id);
        assert_eq!(ok.goal_id, goal_id);
        assert_eq!(ok.structured_goal.goal_id, goal_id);
        assert_eq!(ok.goal_summary.goal_id, goal_id);
        assert!(ok.goal_summary.pretty.contains("|-"));
        assert!(ok
            .available_tactics
            .iter()
            .any(|available| available.tactic == "exact"));
        assert!(ok
            .available_tactics
            .iter()
            .any(|available| available.tactic == "simp-lite"));
        assert!(ok
            .tactic_suggestions
            .iter()
            .all(|candidate| !candidate.tactic.is_empty()
                && candidate.confidence <= 100
                && !candidate.reason.is_empty()));
        let nat_add_zero = ok
            .nearby_theorems
            .iter()
            .find(|theorem| theorem.name == npa_cert::Name::from_dotted("Nat.add_zero"))
            .expect("assistant payload should include nearby theorem search results");
        assert!(!nat_add_zero.suggested_tactic.is_empty());
        assert!(!nat_add_zero.axiom_info.uses_axioms);
        let failed = ok
            .failed_tactics
            .iter()
            .find(|failed| failed.tactic == "exact Nat.zero")
            .expect("assistant payload should include requested failed tactic diagnostics");
        assert!(failed.error.is_some());
    }

    #[test]
    fn human_assistant_payload_validates_candidates_with_tactic_run_before_adoption() {
        let (mut store, header, state_id, goal_id) = human_eq_refl_goal_fixture();
        let before = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: state_id.clone(),
            },
        )
        .expect("fixture state should materialize before candidate validation");
        assert_eq!(before.state.goals.len(), 1);

        let validation = validate_human_assistant_candidates(
            &store,
            HumanAssistantCandidateValidationRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                candidates: vec![
                    HumanAssistantCandidate {
                        tactic: "exact Eq.refl n".to_owned(),
                        confidence: 98,
                        reason: "target is reflexive equality".to_owned(),
                    },
                    HumanAssistantCandidate {
                        tactic: "exact Nat.zero".to_owned(),
                        confidence: 90,
                        reason: "bad assistant guess".to_owned(),
                    },
                ],
                budget: npa_tactic::TacticBudget::default(),
            },
        );

        assert_eq!(validation.accepted.len(), 1);
        assert_eq!(validation.accepted[0].candidate.tactic, "exact Eq.refl n");
        assert_eq!(validation.rejected.len(), 1);
        assert_eq!(validation.rejected[0].candidate.tactic, "exact Nat.zero");
        assert!(validation.rejected[0].error.is_some());
        let after_validation = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: state_id.clone(),
            },
        )
        .expect("candidate validation must not mutate the Human session store");
        assert_eq!(after_validation.state.goals.len(), 1);

        let adopted = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header,
                state_id,
                goal_id,
                tactic: validation.accepted[0].candidate.tactic.clone(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(adopted.status, HumanTacticRunStatus::Closed);
        assert!(adopted.error.is_none());
    }

    #[test]
    fn human_assistant_payload_prompt_schema_and_machine_fast_path_are_unchanged() {
        let prompt_spec =
            crate::machine_endpoint_envelope_spec(crate::MachineApiEndpoint::PromptPayload);
        let prompt_fields = prompt_spec
            .fields
            .iter()
            .map(|field| field.name)
            .collect::<Vec<_>>();
        assert_eq!(
            prompt_fields,
            vec![
                "session_id",
                "snapshot_id",
                "state_fingerprint",
                "goal_id",
                "include_pretty",
                "include_failed_candidates",
                "premise_selection",
                "failed_candidates",
            ]
        );
        assert_eq!(
            crate::MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA,
            "npa.machine_tactic_candidate.v1"
        );

        let endpoints = [
            crate::MachineApiEndpoint::CreateSession,
            crate::MachineApiEndpoint::DeleteSession,
            crate::MachineApiEndpoint::SnapshotGet,
            crate::MachineApiEndpoint::TacticRun,
            crate::MachineApiEndpoint::TacticBatch,
            crate::MachineApiEndpoint::SearchForGoal,
            crate::MachineApiEndpoint::PromptPayload,
            crate::MachineApiEndpoint::Replay,
            crate::MachineApiEndpoint::Verify,
        ];
        let forbidden = ["assistant", "confidence", "reason", "human_tactic"];
        for endpoint in endpoints {
            let spec = crate::machine_endpoint_envelope_spec(endpoint);
            assert!(forbidden
                .iter()
                .all(|name| !spec.endpoint.as_str().contains(name)));
            assert!(spec
                .fields
                .iter()
                .all(|field| { forbidden.iter().all(|name| !field.name.contains(name)) }));
        }
    }

    #[test]
    fn phase5_human_end_to_end_session_create_lookup_tactic_search_display_verify() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
infix:50 \" = \" => Eq
theorem t (n : Nat) : n = n := by exact Eq.refl n";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanEndToEnd"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(65),
                    source,
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human e2e session should be created");
        assert!(created.messages.is_empty());
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanEndToEnd.t"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human e2e proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };

        let initial = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: started.state_id.clone(),
            },
        )
        .expect("initial Human state lookup should work");
        assert_eq!(initial.state.goals.len(), 1);
        assert_eq!(initial.state.selected_goal, started.selected_goal);

        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        assert!(intro.error.is_none());
        let body_state_id = intro.new_state_id.expect("intro should record body state");
        let body_goal_id = intro.selected_goal.expect("intro should select body goal");
        let body = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: body_state_id.clone(),
            },
        )
        .expect("body Human state lookup should work");
        assert_eq!(body.state.goals.len(), 1);
        assert_eq!(body.state.goals[0].goal_id, body_goal_id);
        assert_eq!(body.state.goals[0].target.pretty, "n = n");

        let search = search_human_theorems_for_goal(
            &store,
            HumanTheoremGoalSearchRequest {
                header: header.clone(),
                state_id: body_state_id.clone(),
                goal_id: body_goal_id.clone(),
                modes: vec![HumanTheoremSearchMode::Exact],
                options: HumanTheoremSearchOptions {
                    limit: 10,
                    axiom_policy: HumanTheoremSearchAxiomPolicy::Allow,
                },
            },
        )
        .expect("Human e2e theorem search should work");
        assert!(search
            .results
            .iter()
            .any(|result| result.suggested_tactic == "exact Eq.refl n"));

        let display = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header: header.clone(),
                state_id: body_state_id.clone(),
                goal_id: body_goal_id.clone(),
                mode: HumanDisplayMode::Pretty,
                context_options: HumanDisplayContextOptions::default(),
            },
        )
        .expect("Human e2e goal display should work");
        assert!(display.text.contains("n : Nat"));
        assert!(display.text.contains("|- n = n"));

        let exact = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: body_state_id,
                goal_id: body_goal_id,
                tactic: "exact Eq.refl n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(exact.status, HumanTacticRunStatus::Closed);
        assert!(exact.error.is_none());
        let closed_state_id = exact
            .new_state_id
            .expect("exact should record closed proof state");

        let verified = verify_human_session(
            &store,
            HumanSessionVerifyRequest {
                header,
                state_id: closed_state_id,
            },
        )
        .expect("closed Human e2e state should verify");
        assert_eq!(verified.status, HumanSessionVerifyStatus::Verified);
        assert_eq!(
            verified.theorem_name,
            npa_cert::Name::from_dotted("Api.HumanEndToEnd.t")
        );
        assert!(verified.axioms_used.is_empty());
        assert!(!verified.contains_sorry);
    }

    #[test]
    fn phase5_human_end_to_end_type_mismatch_returns_structured_diagnostic() {
        let source = "\
theorem id (A : Type) (x : A) : A := by exact x";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanMismatch"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(66),
                    source,
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human mismatch session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanMismatch.id"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human mismatch proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id,
            document_id: created.document_id,
            document_version: created.document_version,
        };
        let intro_a = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro A".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro_a.status, HumanTacticRunStatus::Partial);
        let intro_x = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: intro_a.new_state_id.expect("intro A should record state"),
                goal_id: intro_a.selected_goal.expect("intro A should select goal"),
                tactic: "intro x".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro_x.status, HumanTacticRunStatus::Partial);
        let body_state_id = intro_x
            .new_state_id
            .clone()
            .expect("intro x should record state");
        let body_goal_id = intro_x
            .selected_goal
            .clone()
            .expect("intro x should select body goal");

        let bad_exact = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: body_state_id.clone(),
                goal_id: body_goal_id.clone(),
                tactic: "exact A".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(bad_exact.status, HumanTacticRunStatus::Error);
        let report = bad_exact
            .error
            .as_ref()
            .expect("bad exact should return structured run error");
        assert_eq!(report.kind, HumanTacticRunErrorKind::TypeMismatch);
        let diagnostic = report
            .diagnostic
            .as_ref()
            .expect("bad exact should include a Human diagnostic");
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        );
        let payload = human_payload(diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticValidation)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(
            payload.hole_goals[0]
                .context
                .iter()
                .map(|local| local.name.as_str())
                .collect::<Vec<_>>(),
            vec!["A", "x"]
        );
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("A"));

        let body = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header,
                state_id: body_state_id,
            },
        )
        .expect("failed tactic should leave the source state available");
        assert_eq!(body.state.goals.len(), 1);
        assert_eq!(body.state.goals[0].goal_id, body_goal_id);
        assert_eq!(body.state.goals[0].target.pretty, "A");
    }

    #[test]
    fn phase7_machine_api_identity_is_stable_around_phase5_human_integration_fixture() {
        let mut before = create_machine_session(&phase5_machine_minimal_session_json("Type 0"))
            .expect("baseline Machine session should be created")
            .session;
        let before_identity = phase7_machine_exact_prop_batch_identity(&mut before);

        phase5_human_end_to_end_session_create_lookup_tactic_search_display_verify();

        let mut after = create_machine_session(&phase5_machine_minimal_session_json("Type 0"))
            .expect("post-Human Machine session should be created")
            .session;
        let after_identity = phase7_machine_exact_prop_batch_identity(&mut after);

        assert_eq!(
            before.initial_snapshot.state_fingerprint,
            after.initial_snapshot.state_fingerprint
        );
        assert_eq!(before_identity, after_identity);
    }

    #[test]
    fn human_session_stores_explicit_imports_without_machine_session_integration() {
        let producer = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.SessionLib"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(13),
                source: "axiom A : Type",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("producer Human API request should compile");
        let bytes =
            npa_cert::encode_module_cert(&producer.certificate).expect("producer cert encodes");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("producer cert verifies");
        let import = npa_frontend::VerifiedImport::from(&verified);
        let source_interface = npa_frontend::HumanImportedSourceInterface {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            source_interface: producer.source_interface,
        };

        let mut store = HumanProofSessionStore::new();
        let ok = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.SessionUser"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(14),
                    source: "axiom B : Type",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should store explicit import inputs");
        let session = store
            .session(&ok.session_id)
            .expect("created session should be stored");

        assert_eq!(session.document.verified_modules, vec![verified]);
        assert_eq!(
            session.document.imported_source_interfaces,
            vec![source_interface]
        );
        assert_eq!(store.session_count(), 1);
    }

    #[test]
    fn human_state_store_starts_session_proof_and_retrieves_by_human_state_id() {
        let source = "\
theorem target : forall (P : Prop), forall (hp : P), P := by simp-lite";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StateStore"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(21),
                    source,
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let proof_span = npa_frontend::Span::new(npa_frontend::FileId(21), 0, 48);
        let start_message = npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal,
            proof_span,
            "state stored with message",
        );

        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StateStore.target"),
                source_span: Some(proof_span),
                selected_goal: None,
                messages: vec![start_message.clone()],
            },
        )
        .expect("Human session proof should start and store state");

        assert!(started.state_id.wire().starts_with("hst_"));
        assert_eq!(started.messages, vec![start_message.clone()]);
        let entry = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("stored Human state should be retrievable by state_id");
        assert_eq!(entry.document_version, HumanDocumentVersion::initial());
        assert_eq!(entry.source_span, Some(proof_span));
        assert_eq!(entry.messages, vec![start_message]);
        assert_eq!(entry.state.open_goals, vec![npa_tactic::GoalId(0)]);
        assert_ne!(entry.state_id.wire(), entry.state.state_id);
        assert_eq!(entry.goal_mappings.len(), 1);
        assert_eq!(
            entry.goal_mappings[0].machine_goal_id,
            npa_tactic::GoalId(0)
        );
        assert!(entry.goal_mappings[0]
            .human_goal_id
            .wire()
            .starts_with("hgoal_"));
        assert_eq!(
            entry.selected_goal.as_ref(),
            Some(&entry.goal_mappings[0].human_goal_id)
        );
    }

    #[test]
    fn human_state_store_records_tactic_transition_without_mutating_parent_state() {
        let source = "\
theorem target : forall (P : Prop), forall (hp : P), P := by simp-lite";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StateTransition"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(22),
                    source,
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StateTransition.target"),
                source_span: Some(npa_frontend::Span::new(npa_frontend::FileId(22), 0, 48)),
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human session proof should start");
        let parent_entry = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("parent state should be stored");
        let parent_state = parent_entry.state.clone();
        let parent_open_goals = parent_entry.state.open_goals.clone();
        let parent_fingerprint = parent_entry.state.fingerprint;
        let source_interface = store
            .session(&created.session_id)
            .and_then(|session| session.source_interface.clone())
            .expect("started proof should leave a source interface on the session");

        let bad_term = npa_frontend::parse_human_term(npa_frontend::FileId(22), "missing")
            .expect("bad exact term should still parse");
        run_human_exact_tactic(HumanExactTacticRequest {
            state: &parent_state,
            goal_id: npa_tactic::GoalId(0),
            term: &bad_term,
            current_source_interface: &source_interface,
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect_err("unknown exact term should fail without recording a new state");
        let parent_after_failure =
            get_human_proof_state(&store, &created.session_id, &started.state_id)
                .expect("parent state should remain stored after tactic failure");
        assert_eq!(parent_after_failure.state.open_goals, parent_open_goals);
        assert_eq!(parent_after_failure.state.fingerprint, parent_fingerprint);
        assert_eq!(
            store
                .session(&created.session_id)
                .expect("session should exist")
                .proof_states
                .state_count(),
            1
        );

        let intro_name = human_name("P", 0, 1);
        let intro = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &parent_state,
            goal_id: npa_tactic::GoalId(0),
            name: &intro_name,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro should produce a new Machine state");
        let tactic_span = npa_frontend::Span::new(npa_frontend::FileId(22), 49, 58);
        let tactic_message = npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal,
            tactic_span,
            "transition stored with message",
        );
        let recorded = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: intro.state.open_goals.first().copied(),
                state: intro.state,
                source_span: Some(tactic_span),
                messages: vec![tactic_message.clone()],
            },
        )
        .expect("successful tactic state should be recorded");
        assert_eq!(recorded.messages, vec![tactic_message.clone()]);

        let parent_after_success =
            get_human_proof_state(&store, &created.session_id, &started.state_id)
                .expect("parent state should remain stored after transition");
        assert_eq!(parent_after_success.state.open_goals, parent_open_goals);
        assert_eq!(parent_after_success.state.fingerprint, parent_fingerprint);
        let child = get_human_proof_state(&store, &created.session_id, &recorded.state_id)
            .expect("child state should be retrievable");
        assert_eq!(child.parent_state_id.as_ref(), Some(&started.state_id));
        assert_eq!(child.state.open_goals, vec![npa_tactic::GoalId(1)]);
        assert_eq!(child.document_version, created.document_version);
        assert_eq!(child.source_span, Some(tactic_span));
        assert_eq!(child.messages, vec![tactic_message]);
        assert_ne!(child.state_id.wire(), child.state.state_id);
        assert!(child.state_id.wire().starts_with("hst_"));
        assert_eq!(child.selected_goal, recorded.selected_goal);
        assert_eq!(
            store
                .session(&created.session_id)
                .expect("session should exist")
                .proof_states
                .state_count(),
            2
        );
    }

    #[test]
    fn human_state_api_by_id_goals_current_and_at_hole() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) : Eq.{1} n n := by exact _";
        let file_id = npa_frontend::FileId(25);
        let by_offset = source.find("by").expect("source should contain by") as u32;
        let hole_offset = source.find('_').expect("source should contain a hole") as u32;
        let proof_span = npa_frontend::Span::new(file_id, by_offset, source.len() as u32);
        let hole_span = npa_frontend::Span::new(file_id, hole_offset, hole_offset + 1);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StateApi"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StateApi.target"),
                source_span: Some(proof_span),
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        assert_eq!(
            store
                .session(&created.session_id)
                .expect("session should exist")
                .current_state_id,
            Some(started.state_id.clone())
        );

        let parent = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &parent,
            goal_id: npa_tactic::GoalId(0),
            name: &human_name("n", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro should expose the theorem parameter at the hole");
        let recorded = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: intro.state.open_goals.first().copied(),
                state: intro.state,
                source_span: Some(hole_span),
                messages: Vec::new(),
            },
        )
        .expect("hole state should be recorded");
        assert_eq!(
            store
                .session(&created.session_id)
                .expect("session should exist")
                .current_state_id,
            Some(recorded.state_id.clone())
        );

        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let by_id = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
            },
        )
        .expect("state/by_id should materialize the recorded state");
        assert_eq!(by_id.state.state_id, recorded.state_id);
        let current = get_current_human_state(
            &store,
            HumanStateCurrentRequest {
                header: header.clone(),
            },
        )
        .expect("state/current should follow the session cursor");
        assert_eq!(current.state.state_id, recorded.state_id);
        let at_hole = get_human_state_at(
            &store,
            HumanStateAtRequest {
                header: header.clone(),
                position: HumanSourcePosition::new(file_id, hole_offset),
            },
        )
        .expect("state/at should resolve the hole position to the recorded state");
        assert_eq!(at_hole.state.state_id, recorded.state_id);
        assert_eq!(at_hole.state.goals.len(), 1);
        let goal = &at_hole.state.goals[0];
        assert_eq!(goal.context.len(), 1);
        assert_eq!(goal.context[0].name, "n");
        assert_eq!(goal.context[0].ty.pretty, "Nat");
        assert_eq!(goal.target.pretty, "n = n");

        let goals = get_human_state_goals(
            &store,
            HumanStateGoalsRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
            },
        )
        .expect("state/goals should return lightweight goal displays");
        assert_eq!(goals.state_id, recorded.state_id);
        assert_eq!(goals.selected_goal, recorded.selected_goal.clone());
        assert_eq!(goals.goals.len(), 1);
        assert_eq!(
            goals.goals[0].goal_id,
            recorded.selected_goal.clone().unwrap()
        );
        assert!(goals.goals[0].pretty.contains("n : Nat"));
        assert!(goals.goals[0].pretty.contains("|- n = n"));

        let missing_state_id = crate::HumanStateId::new_unchecked("hst_missing");
        let missing = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: missing_state_id.clone(),
            },
        )
        .expect_err("unknown state ids should return a structured not-found error");
        assert_eq!(
            missing,
            HumanStateApiError::UnknownState {
                session_id: created.session_id.clone(),
                state_id: missing_state_id,
            }
        );

        let outside = get_human_state_at(
            &store,
            HumanStateAtRequest {
                header,
                position: HumanSourcePosition::new(file_id, 0),
            },
        )
        .expect_err("source position outside a proof state should be structured not-found");
        assert_eq!(
            outside,
            HumanStateApiError::NoProofStateAtPosition {
                session_id: created.session_id,
                document_version: created.document_version,
                position: HumanSourcePosition::new(file_id, 0),
            }
        );
    }

    #[test]
    fn human_state_api_rejects_stale_document_and_reports_no_current_state() {
        let source = "theorem target : Prop := by simp-lite";
        let file_id = npa_frontend::FileId(26);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StateApiStale"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StateApiStale.target"),
                source_span: Some(npa_frontend::Span::new(file_id, 0, source.len() as u32)),
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");

        let updated = update_human_document(
            &mut store,
            HumanDocumentUpdateRequest {
                session_id: created.session_id.clone(),
                current_module: npa_cert::Name::from_dotted("Api.StateApiStale"),
                current_source: HumanCurrentModuleSource {
                    file_id,
                    source: "axiom P : Prop",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("document update should clear the current proof cursor");

        let stale = get_current_human_state(
            &store,
            HumanStateCurrentRequest {
                header: HumanStateRequestHeader {
                    session_id: created.session_id.clone(),
                    document_id: created.document_id.clone(),
                    document_version: created.document_version,
                },
            },
        )
        .expect_err("old document versions should be stale for state/current");
        assert_eq!(
            stale,
            HumanStateApiError::StaleDocumentVersion {
                session_id: created.session_id.clone(),
                document_id: created.document_id.clone(),
                requested: created.document_version,
                current: updated.document_version,
            }
        );

        let no_current = get_current_human_state(
            &store,
            HumanStateCurrentRequest {
                header: HumanStateRequestHeader {
                    session_id: created.session_id.clone(),
                    document_id: updated.document_id,
                    document_version: updated.document_version,
                },
            },
        )
        .expect_err("updated document should not retain the old current proof state");
        assert_eq!(
            no_current,
            HumanStateApiError::NoCurrentState {
                session_id: created.session_id,
                document_version: updated.document_version,
            }
        );
    }

    #[test]
    fn human_structured_goal_materializes_context_target_and_metadata() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) : Eq.{1} n n := by simp-lite";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StructuredGoal"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(23),
                    source,
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StructuredGoal.target"),
                source_span: Some(npa_frontend::Span::new(npa_frontend::FileId(23), 38, 93)),
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        let parent = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &parent,
            goal_id: npa_tactic::GoalId(0),
            name: &human_name("n", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro should expose the Nat local");
        let recorded = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: intro.state.open_goals.first().copied(),
                state: intro.state,
                source_span: Some(npa_frontend::Span::new(npa_frontend::FileId(23), 83, 93)),
                messages: Vec::new(),
            },
        )
        .expect("introduced state should be recorded");

        let structured =
            materialize_human_proof_state(&store, &created.session_id, &recorded.state_id)
                .expect("Human state should materialize as structured goals");

        assert_eq!(structured.state_id, recorded.state_id);
        assert_eq!(structured.document_version, created.document_version);
        assert_eq!(structured.selected_goal, recorded.selected_goal);
        assert_eq!(structured.goals.len(), 1);
        let goal = &structured.goals[0];
        assert_eq!(goal.goal_id, recorded.selected_goal.clone().unwrap());
        assert_eq!(goal.machine_goal_id, npa_tactic::GoalId(1));
        assert_eq!(goal.status, crate::StructuredGoalStatus::Open);
        assert_eq!(goal.context.len(), 1);
        let local = &goal.context[0];
        assert_eq!(local.local_id, crate::LocalId(0));
        assert_eq!(local.name, "n");
        assert_eq!(local.ty.pretty, "Nat");
        assert_eq!(
            local.ty.head.as_ref().map(npa_cert::Name::as_dotted),
            Some("Nat".to_owned())
        );
        assert_eq!(local.ty.constants, vec![npa_cert::Name::from_dotted("Nat")]);
        assert!(local.ty.free_locals.is_empty());
        assert!(local.depends_on.is_empty());
        assert!(!local.is_local_def);
        assert!(!local.is_implicit);
        assert_eq!(goal.target.pretty, "n = n");
        assert_eq!(
            goal.target.head.as_ref().map(npa_cert::Name::as_dotted),
            Some("Eq".to_owned())
        );
        assert_eq!(
            goal.target.constants,
            vec![
                npa_cert::Name::from_dotted("Eq"),
                npa_cert::Name::from_dotted("Nat")
            ]
        );
        assert_eq!(goal.target.free_locals, vec![crate::LocalId(0)]);
        assert_eq!(goal.target_core_hash, goal.target.core_hash);
        assert!(goal.pretty.contains("n : Nat"));
        assert!(goal.pretty.contains("|- n = n"));

        let mut pretty_changed = goal.target.clone();
        let original_hash = pretty_changed.core_hash;
        pretty_changed.pretty = "display-only change".to_owned();
        assert_eq!(pretty_changed.core_hash, original_hash);
        assert_ne!(goal.target.core_hash, local.ty.core_hash);
    }

    #[test]
    fn human_structured_goal_dependency_order_is_deterministic() {
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![eq];
        let imported_source_interfaces = vec![eq_interface];
        let source = "\
import Std.Logic.Eq
theorem target : forall (A : Type), forall (x : A), forall (h : Eq.{1} x x), Prop := by simp-lite";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.StructuredDeps"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(24),
                    source,
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.StructuredDeps.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");

        let initial_state = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro_a = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &initial_state,
            goal_id: npa_tactic::GoalId(0),
            name: &human_name("A", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro A should succeed");
        let state_a = intro_a.state.clone();
        let recorded_a = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: state_a.open_goals.first().copied(),
                state: intro_a.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("A state should be recorded");
        let intro_x = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_a,
            goal_id: state_a.open_goals[0],
            name: &human_name("x", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro x should succeed");
        let state_x = intro_x.state.clone();
        let recorded_x = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_a.state_id.clone(),
                selected_goal: state_x.open_goals.first().copied(),
                state: intro_x.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("x state should be recorded");
        let intro_h = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_x,
            goal_id: state_x.open_goals[0],
            name: &human_name("h", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro h should succeed");
        let state_h = intro_h.state.clone();
        let recorded_h = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_x.state_id.clone(),
                selected_goal: state_h.open_goals.first().copied(),
                state: intro_h.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("h state should be recorded");

        let first =
            materialize_human_proof_state(&store, &created.session_id, &recorded_h.state_id)
                .expect("Human state should materialize");
        let second =
            materialize_human_proof_state(&store, &created.session_id, &recorded_h.state_id)
                .expect("Human state should rematerialize deterministically");
        assert_eq!(first, second);
        let goal = &first.goals[0];
        assert_eq!(goal.context.len(), 3);
        let h = &goal.context[2];
        assert_eq!(h.name, "h");
        assert_eq!(h.ty.pretty, "x = x");
        assert_eq!(h.ty.free_locals, vec![crate::LocalId(0), crate::LocalId(1)]);
        assert_eq!(h.depends_on, vec![crate::LocalId(0), crate::LocalId(1)]);
    }

    #[test]
    fn human_display_goal_modes_expr_and_context_folding() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) : Eq.{1} n n := by exact _";
        let file_id = npa_frontend::FileId(27);
        let by_offset = source.find("by").expect("source should contain by") as u32;
        let hole_offset = source.find('_').expect("source should contain a hole") as u32;
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanDisplayGoal"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanDisplayGoal.target"),
                source_span: Some(npa_frontend::Span::new(
                    file_id,
                    by_offset,
                    source.len() as u32,
                )),
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        let parent = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &parent,
            goal_id: npa_tactic::GoalId(0),
            name: &human_name("n", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro should expose Nat local");
        let recorded = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: intro.state.open_goals.first().copied(),
                state: intro.state,
                source_span: Some(npa_frontend::Span::new(
                    file_id,
                    hole_offset,
                    hole_offset + 1,
                )),
                messages: Vec::new(),
            },
        )
        .expect("hole state should be recorded");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let by_id = get_human_state_by_id(
            &store,
            HumanStateByIdRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
            },
        )
        .expect("state/by_id should materialize the recorded state");
        let goal_id = recorded
            .selected_goal
            .clone()
            .expect("recorded state should select the open goal");

        let pretty = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
                goal_id: goal_id.clone(),
                mode: HumanDisplayMode::Pretty,
                context_options: HumanDisplayContextOptions::default(),
            },
        )
        .expect("pretty display should render goal");
        assert_eq!(pretty.display_profile, HUMAN_DISPLAY_PROFILE_ID);
        assert!(pretty.text.contains("|- n = n"));
        assert!(!pretty.text.contains("Eq.{"));

        let explicit = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
                goal_id: goal_id.clone(),
                mode: HumanDisplayMode::Explicit,
                context_options: HumanDisplayContextOptions::default(),
            },
        )
        .expect("explicit display should render goal");
        assert!(explicit.text.contains("Eq.{succ 0}"));
        assert!(explicit.text.contains("Nat n n"));

        let core = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
                goal_id: goal_id.clone(),
                mode: HumanDisplayMode::Core,
                context_options: HumanDisplayContextOptions::default(),
            },
        )
        .expect("core display should render goal");
        assert!(core.text.contains("App("));
        assert!(core.text.contains("Const(Eq.{succ(0)})"));
        assert!(core.text.contains("BVar(0)"));

        let json = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header: header.clone(),
                state_id: recorded.state_id.clone(),
                goal_id,
                mode: HumanDisplayMode::Json,
                context_options: HumanDisplayContextOptions {
                    max_context_items: Some(0),
                    ..HumanDisplayContextOptions::default()
                },
            },
        )
        .expect("json display should render full StructuredGoal");
        assert!(json.text.contains("\"context\":["));
        assert!(json.text.contains("\"name\":\"n\""));
        assert!(json.text.contains("\"target\""));

        let target = by_id.state.goals[0].target.clone();
        let expr_core = display_human_expr(HumanDisplayExprRequest {
            expr: target.clone(),
            mode: HumanDisplayMode::Core,
        });
        assert!(expr_core.text.contains("core_hash:"));
        assert!(expr_core.text.contains("head: Eq"));
        let expr_json = display_human_expr(HumanDisplayExprRequest {
            expr: target,
            mode: HumanDisplayMode::Json,
        });
        assert!(expr_json.text.contains("\"core_hash\""));
        assert!(expr_json.text.contains("\"head\":\"Eq\""));
    }

    #[test]
    fn human_display_context_folds_without_removing_json_context() {
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![eq];
        let imported_source_interfaces = vec![eq_interface];
        let source = "\
import Std.Logic.Eq
theorem target : forall (A : Type), forall (x : A), forall (h : Eq.{1} x x), Eq.{1} x x := by simp-lite";
        let file_id = npa_frontend::FileId(28);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanDisplayContext"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanDisplayContext.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        let state_initial = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro_a = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_initial,
            goal_id: state_initial.open_goals[0],
            name: &human_name("A", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro A should succeed");
        let state_a = intro_a.state.clone();
        let recorded_a = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: state_a.open_goals.first().copied(),
                state: intro_a.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("A state should be recorded");
        let intro_x = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_a,
            goal_id: state_a.open_goals[0],
            name: &human_name("x", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro x should succeed");
        let state_x = intro_x.state.clone();
        let recorded_x = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_a.state_id.clone(),
                selected_goal: state_x.open_goals.first().copied(),
                state: intro_x.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("x state should be recorded");
        let intro_h = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_x,
            goal_id: state_x.open_goals[0],
            name: &human_name("h", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro h should succeed");
        let state_h = intro_h.state.clone();
        let recorded_h = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_x.state_id.clone(),
                selected_goal: state_h.open_goals.first().copied(),
                state: intro_h.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("h state should be recorded");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let goal_id = recorded_h
            .selected_goal
            .clone()
            .expect("recorded state should select the open goal");
        let folded = display_human_context(
            &store,
            HumanDisplayContextRequest {
                header: header.clone(),
                state_id: recorded_h.state_id.clone(),
                goal_id: goal_id.clone(),
                mode: HumanDisplayMode::Pretty,
                context_options: HumanDisplayContextOptions {
                    max_context_items: Some(2),
                    fold_local_def_values: false,
                    relevant_first: true,
                },
            },
        )
        .expect("context display should fold");

        assert_eq!(folded.shown_count, 2);
        assert_eq!(folded.folded_count, 1);
        assert!(folded
            .text
            .contains("Context contains 3 hypotheses. Showing 2 relevant hypotheses."));
        assert!(folded.text.contains("A : Type"));
        assert!(folded.text.contains("x : A"));
        assert!(!folded.text.contains("h : x = x"));

        let json_goal = display_human_goal(
            &store,
            HumanDisplayGoalRequest {
                header,
                state_id: recorded_h.state_id,
                goal_id,
                mode: HumanDisplayMode::Json,
                context_options: HumanDisplayContextOptions {
                    max_context_items: Some(1),
                    ..HumanDisplayContextOptions::default()
                },
            },
        )
        .expect("goal json display should preserve full context");
        assert!(json_goal.text.contains("\"name\":\"A\""));
        assert!(json_goal.text.contains("\"name\":\"x\""));
        assert!(json_goal.text.contains("\"name\":\"h\""));
    }

    #[test]
    fn human_display_diff_reports_replaced_and_closed_goals() {
        let source = "theorem target : forall (P : Prop), forall (hp : P), P := by simp-lite";
        let file_id = npa_frontend::FileId(29);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanDisplayDiff"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanDisplayDiff.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let initial_state = get_human_proof_state(&store, &created.session_id, &started.state_id)
            .expect("initial state should be stored")
            .state
            .clone();
        let intro_p = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &initial_state,
            goal_id: initial_state.open_goals[0],
            name: &human_name("P", 0, 1),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro P should succeed");
        let state_p = intro_p.state.clone();
        let recorded_p = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: started.state_id.clone(),
                selected_goal: state_p.open_goals.first().copied(),
                state: intro_p.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("P state should be recorded");
        let replaced = display_human_diff(
            &store,
            HumanDisplayDiffRequest {
                header: header.clone(),
                before_state_id: started.state_id.clone(),
                after_state_id: recorded_p.state_id.clone(),
                mode: HumanDisplayMode::Pretty,
            },
        )
        .expect("display diff should render intro replacement");
        assert_eq!(replaced.items.len(), 1);
        assert_eq!(
            replaced.items[0].kind,
            HumanGoalDisplayDiffKind::GoalReplaced
        );
        assert_eq!(replaced.items[0].old_goal, started.selected_goal.clone());
        assert_eq!(
            replaced.items[0].new_goals,
            vec![recorded_p.selected_goal.clone().unwrap()]
        );
        assert!(replaced.text.contains("before:"));
        assert!(replaced.text.contains("after:"));

        let intro_hp = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &state_p,
            goal_id: state_p.open_goals[0],
            name: &human_name("hp", 0, 2),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("intro hp should succeed");
        let state_hp = intro_hp.state.clone();
        let recorded_hp = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_p.state_id.clone(),
                selected_goal: state_hp.open_goals.first().copied(),
                state: intro_hp.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("hp state should be recorded");
        let source_interface = store
            .session(&created.session_id)
            .and_then(|session| session.source_interface.clone())
            .expect("started proof should leave a source interface on the session");
        let exact_term =
            npa_frontend::parse_human_term(file_id, "hp").expect("hp exact term should parse");
        let exact = run_human_exact_tactic(HumanExactTacticRequest {
            state: &state_hp,
            goal_id: state_hp.open_goals[0],
            term: &exact_term,
            current_source_interface: &source_interface,
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("exact hp should close the goal");
        let recorded_exact = record_human_tactic_state(
            &mut store,
            HumanTacticStateRecordRequest {
                session_id: created.session_id.clone(),
                parent_state_id: recorded_hp.state_id.clone(),
                selected_goal: exact.state.open_goals.first().copied(),
                state: exact.state,
                source_span: None,
                messages: Vec::new(),
            },
        )
        .expect("closed state should be recorded");

        let closed = display_human_diff(
            &store,
            HumanDisplayDiffRequest {
                header,
                before_state_id: recorded_hp.state_id,
                after_state_id: recorded_exact.state_id,
                mode: HumanDisplayMode::Pretty,
            },
        )
        .expect("display diff should render closed goal");
        assert_eq!(closed.items.len(), 1);
        assert_eq!(closed.items[0].kind, HumanGoalDisplayDiffKind::GoalClosed);
        assert_eq!(closed.items[0].old_goal, recorded_hp.selected_goal);
        assert!(closed.items[0].new_goals.is_empty());
        assert!(closed.text.contains("closed"));
    }

    #[test]
    fn human_theorem_index_indexes_direct_verified_import_kinds_and_axiom_deps() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanTheoremIndex",
            "\
inductive Nat : Type where
| zero : Nat
| succ : forall (n : Nat), Nat
axiom P : Prop
axiom hp : P
def p_def : P := hp
theorem p_thm : P := hp",
        );
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTheoremIndexUser"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanTheoremIndexUser.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(31),
                source: "\
import Lib.HumanTheoremIndex
theorem target : P := by simp-lite",
            },
            verified_modules: std::slice::from_ref(&verified),
            imported_source_interfaces: std::slice::from_ref(&source_interface),
            options: human_api_default_compile_options(),
        })
        .expect("Human proof should start with the verified import active");

        let index = build_human_theorem_index(&started.state)
            .expect("Human theorem index should build from verified imports");

        human_theorem_index_entry_by_suffix(&index, "hp", HumanTheoremIndexKind::Axiom);
        human_theorem_index_entry_by_suffix(&index, "p_def", HumanTheoremIndexKind::Def);
        let theorem =
            human_theorem_index_entry_by_suffix(&index, "p_thm", HumanTheoremIndexKind::Theorem);
        human_theorem_index_entry_by_suffix(&index, "Nat.zero", HumanTheoremIndexKind::Constructor);
        human_theorem_index_entry_by_suffix(&index, "Nat.rec", HumanTheoremIndexKind::Recursor);

        assert_eq!(theorem.export_hash, Some(verified.export_hash()));
        assert_eq!(theorem.certificate_hash, Some(verified.certificate_hash()));
        assert_eq!(theorem.statement_pretty, theorem.statement.pretty);
        assert_eq!(theorem.head_symbol, theorem.statement.head);
        assert_eq!(theorem.constants, theorem.statement.constants);
        assert!(theorem
            .dependencies
            .iter()
            .any(|dependency| dependency.name.as_dotted().ends_with("P")));
        assert!(theorem.axiom_dependencies.iter().any(|axiom| matches!(
            axiom,
            MachineAxiomRefWire::Imported { name, .. } if name.as_dotted().ends_with("hp")
        )));
    }

    #[test]
    fn human_theorem_index_uses_checked_current_prefix_and_ignores_unverified_metadata() {
        let (verified, mut source_interface) = verified_human_import(
            "Lib.HumanTheoremIndexMeta",
            "\
axiom P : Prop
axiom hp : P",
        );
        source_interface.source_interface.declarations.push(
            npa_frontend::HumanSourceDeclarationMetadata {
                kind: npa_frontend::HumanSourceDeclarationKind::Theorem,
                name: human_name("fake_external", 0, 13),
                universe_params: Vec::new(),
                binders: Vec::new(),
                decl_interface_hash: None,
                span: npa_frontend::Span::new(npa_frontend::FileId(31), 0, 13),
            },
        );
        let source = "\
import Lib.HumanTheoremIndexMeta
theorem prior : P := hp
theorem target : P := by simp-lite
theorem later : P := hp";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTheoremIndexPrefix"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanTheoremIndexPrefix.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(32),
                source,
            },
            verified_modules: std::slice::from_ref(&verified),
            imported_source_interfaces: std::slice::from_ref(&source_interface),
            options: human_api_default_compile_options(),
        })
        .expect("Human proof should start with a checked current prefix");

        let index = build_human_theorem_index(&started.state)
            .expect("Human theorem index should build from the checked prefix");
        let prior =
            human_theorem_index_entry_by_suffix(&index, ".prior", HumanTheoremIndexKind::Theorem);

        assert_eq!(
            prior.source,
            HumanTheoremIndexSource::CheckedCurrentDecl { source_index: 0 }
        );
        assert_eq!(prior.export_hash, None);
        assert_eq!(prior.certificate_hash, None);
        assert!(prior.axiom_dependencies.iter().any(|axiom| matches!(
            axiom,
            MachineAxiomRefWire::Imported { name, .. } if name.as_dotted().ends_with("hp")
        )));
        assert!(!index
            .entries
            .iter()
            .any(|entry| entry.name.as_dotted().ends_with(".later")));
        assert!(!index
            .entries
            .iter()
            .any(|entry| entry.name.as_dotted().ends_with("fake_external")));
    }

    #[test]
    fn human_search_name_and_type_find_nat_add_zero() {
        let (store, header, state_id, _goal_id) = human_search_nat_add_zero_fixture();

        let name = search_human_theorems_by_name(
            &store,
            HumanTheoremNameSearchRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                query: "add_zero".to_owned(),
                options: HumanTheoremSearchOptions::default(),
            },
        )
        .expect("name search should succeed");
        let name_result = name
            .results
            .iter()
            .find(|result| result.name == npa_cert::Name::from_dotted("Nat.add_zero"))
            .expect("name search should find Nat.add_zero");
        assert_eq!(name_result.mode, HumanTheoremSearchMode::Name);
        assert_eq!(name_result.suggested_tactic, "exact Nat.add_zero n");
        assert!(!name_result.axiom_info.uses_axioms);

        let by_type = search_human_theorems_by_type(
            &store,
            HumanTheoremTypeSearchRequest {
                header,
                state_id,
                pattern: "?x + 0 = ?x".to_owned(),
                options: HumanTheoremSearchOptions::default(),
            },
        )
        .expect("type search should parse and match the Nat.add_zero pattern");
        let type_result = by_type
            .results
            .iter()
            .find(|result| result.name == npa_cert::Name::from_dotted("Nat.add_zero"))
            .expect("type search should find Nat.add_zero");
        assert_eq!(type_result.mode, HumanTheoremSearchMode::ByType);
        assert_eq!(type_result.suggested_tactic, "exact Nat.add_zero n");
        assert!(type_result
            .match_info
            .iter()
            .any(|binding| binding.pattern == "?x" && binding.value == "n"));
    }

    #[test]
    fn human_search_for_goal_returns_checked_exact_and_rw_tactics() {
        let (store, header, state_id, goal_id) = human_search_nat_add_zero_fixture();

        let for_goal = search_human_theorems_for_goal(
            &store,
            HumanTheoremGoalSearchRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                modes: vec![
                    HumanTheoremSearchMode::Exact,
                    HumanTheoremSearchMode::Apply,
                    HumanTheoremSearchMode::Rw,
                    HumanTheoremSearchMode::Simp,
                ],
                options: HumanTheoremSearchOptions::default(),
            },
        )
        .expect("goal search should succeed");
        let exact = for_goal
            .results
            .iter()
            .find(|result| {
                result.name == npa_cert::Name::from_dotted("Nat.add_zero")
                    && result.mode == HumanTheoremSearchMode::Exact
            })
            .expect("goal search should suggest exact Nat.add_zero");
        assert_eq!(exact.suggested_tactic, "exact Nat.add_zero n");
        let rewrite = for_goal
            .results
            .iter()
            .find(|result| {
                result.name == npa_cert::Name::from_dotted("Nat.add_zero")
                    && result.mode == HumanTheoremSearchMode::Rw
            })
            .expect("goal search should suggest rw Nat.add_zero");
        assert_eq!(rewrite.suggested_tactic, "rw [Nat.add_zero]");

        let rewrite_only = search_human_theorems_for_rewrite(
            &store,
            HumanTheoremRewriteSearchRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                options: HumanTheoremSearchOptions::default(),
            },
        )
        .expect("rewrite search should succeed");
        assert!(rewrite_only
            .results
            .iter()
            .all(|result| result.mode == HumanTheoremSearchMode::Rw));
        assert!(rewrite_only
            .results
            .iter()
            .any(|result| result.suggested_tactic == "rw [Nat.add_zero]"));

        let mut exact_store = store.clone();
        let exact_run = run_human_tactic(
            &mut exact_store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                tactic: exact.suggested_tactic.clone(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(exact_run.status, HumanTacticRunStatus::Closed);
        assert!(exact_run.error.is_none());

        let mut rw_store = store.clone();
        let rw_run = run_human_tactic(
            &mut rw_store,
            HumanTacticRunRequest {
                header,
                state_id,
                goal_id,
                tactic: rewrite.suggested_tactic.clone(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(rw_run.status, HumanTacticRunStatus::Partial);
        assert!(rw_run.error.is_none());
    }

    #[test]
    fn human_search_simp_mode_requires_registered_simp_rule() {
        let (store, header, state_id, goal_id) = human_eq_refl_goal_fixture();

        let simp = search_human_theorems_for_goal(
            &store,
            HumanTheoremGoalSearchRequest {
                header,
                state_id,
                goal_id,
                modes: vec![HumanTheoremSearchMode::Simp],
                options: HumanTheoremSearchOptions::default(),
            },
        )
        .expect("simp theorem search should run");

        assert!(
            simp.results.is_empty(),
            "builtin reflexivity simp-lite success must not be attributed to unrelated theorem entries"
        );
    }

    #[test]
    fn human_search_simp_mode_recognizes_registered_simp_rule_entry() {
        let verified = verified_axiom_simp_close_module();
        let import = npa_tactic::VerifiedImportRef::from_verified_module(&verified)
            .expect("simp close module should become a tactic import");
        let rule_hash = export_interface_hash(&import, "Lib.succ_zero");
        let state = npa_tactic::start_machine_proof(
            human_simp_machine_spec(eq_nat(nat_succ(nat_zero()), nat_zero())),
            vec![import],
            Vec::new(),
            npa_tactic::MachineTacticOptions {
                simp_rules: vec![npa_tactic::SimpRuleRef {
                    name: npa_cert::Name::from_dotted("Lib.succ_zero"),
                    decl_interface_hash: rule_hash,
                    direction: npa_tactic::RewriteDirection::Forward,
                }],
                ..npa_tactic::MachineTacticOptions::default()
            },
        )
        .expect("Machine proof with registered simp rule should start");
        let index = build_human_theorem_index(&state).expect("Human theorem index should build");
        let registered_rule = index
            .entries
            .iter()
            .find(|entry| entry.name == npa_cert::Name::from_dotted("Lib.succ_zero"))
            .expect("registered simp theorem should be indexed");
        let axiom = index
            .entries
            .iter()
            .find(|entry| entry.name == npa_cert::Name::from_dotted("Lib.succ_zero_axiom"))
            .expect("supporting axiom should be indexed");

        assert!(human_theorem_has_simp_rule(&state, registered_rule));
        assert!(!human_theorem_has_simp_rule(&state, axiom));
    }

    #[test]
    fn human_search_high_trust_penalizes_and_filters_axiom_dependencies() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanSearchAxioms",
            "\
axiom P : Prop
axiom hp : P
theorem p_thm : P := hp",
        );
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanSearchAxioms"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(41),
                    source: "\
import Lib.HumanSearchAxioms
theorem target : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human axiom search session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanSearchAxioms.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human axiom search proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id,
            document_id: created.document_id,
            document_version: created.document_version,
        };

        let penalized = search_human_theorems_by_name(
            &store,
            HumanTheoremNameSearchRequest {
                header: header.clone(),
                state_id: started.state_id.clone(),
                query: "p_thm".to_owned(),
                options: HumanTheoremSearchOptions {
                    limit: 10,
                    axiom_policy: HumanTheoremSearchAxiomPolicy::Penalize,
                },
            },
        )
        .expect("penalized search should succeed");
        let p_thm = penalized
            .results
            .iter()
            .find(|result| result.name.as_dotted().ends_with("p_thm"))
            .expect("penalized search should retain the axiom-dependent theorem");
        assert!(p_thm.axiom_info.uses_axioms);
        assert!(p_thm.axiom_info.score_penalty > 0);

        let excluded = search_human_theorems_by_name(
            &store,
            HumanTheoremNameSearchRequest {
                header,
                state_id: started.state_id,
                query: "p_thm".to_owned(),
                options: HumanTheoremSearchOptions {
                    limit: 10,
                    axiom_policy: HumanTheoremSearchAxiomPolicy::Exclude,
                },
            },
        )
        .expect("exclude-axiom search should succeed");
        assert!(!excluded
            .results
            .iter()
            .any(|result| result.name.as_dotted().ends_with("p_thm")));
    }

    #[test]
    fn human_verify_rejects_open_goal_before_certificate_handoff() {
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanVerifyOpen"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(42),
                    source: "theorem target (A : Type) : A := by simp-lite",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human verify open-goal session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanVerifyOpen.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human verify open-goal proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };

        let err = verify_human_session(
            &store,
            HumanSessionVerifyRequest {
                header,
                state_id: started.state_id.clone(),
            },
        )
        .expect_err("Human verify must reject unresolved goals before certificate handoff");
        let HumanSessionVerifyError::OpenGoals {
            session_id,
            state_id,
            open_goals,
        } = err
        else {
            panic!("expected open-goal verification error");
        };
        assert_eq!(session_id, created.session_id);
        assert_eq!(state_id, started.state_id);
        assert_eq!(open_goals.len(), 1);
    }

    #[test]
    fn human_verify_closed_state_returns_verifier_hashes_and_axiom_report() {
        let (verified, source_interface) = verified_human_import(
            "Lib.HumanVerifyAxiom",
            "\
axiom P : Prop
axiom hp : P",
        );
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanVerifyClosed"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(43),
                    source: "\
import Lib.HumanVerifyAxiom
theorem target : P := by simp-lite",
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human verify closed session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanVerifyClosed.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human verify closed proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };
        let exact = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "exact hp".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(exact.status, HumanTacticRunStatus::Closed);
        assert!(exact.error.is_none());
        let closed_state_id = exact
            .new_state_id
            .expect("closed tactic should record state");

        let ok = verify_human_session(
            &store,
            HumanSessionVerifyRequest {
                header: header.clone(),
                state_id: closed_state_id.clone(),
            },
        )
        .expect("closed Human state should verify through certificate checker");
        assert_eq!(ok.status, HumanSessionVerifyStatus::Verified);
        assert_eq!(
            ok.theorem_name,
            npa_cert::Name::from_dotted("Api.HumanVerifyClosed.target")
        );
        assert_eq!(ok.certificate.encoding, HUMAN_CERTIFICATE_ENCODING);
        assert!(!ok.certificate.bytes.is_empty());
        assert!(!ok.contains_sorry);
        assert!(ok
            .axioms_used
            .iter()
            .any(|axiom| matches!(axiom, MachineAxiomRefWire::Imported { name, .. } if name.as_dotted() == "hp")));
        assert_eq!(ok.root_axioms_used, ok.axioms_used);

        let import = ok
            .imports
            .iter()
            .find(|import| import.module == npa_cert::Name::from_dotted("Lib.HumanVerifyAxiom"))
            .expect("Human verify response should retain import hash metadata");
        assert_eq!(import.export_hash, verified.export_hash());
        assert_eq!(import.certificate_hash, verified.certificate_hash());
        assert!(import
            .module_axioms
            .iter()
            .any(|axiom| axiom.name.as_dotted() == "hp"));

        let cert_bytes = human_verify_decode_hex_bytes(&ok.certificate.bytes);
        let decoded_certificate =
            npa_cert::decode_module_cert(&cert_bytes).expect("Human verify cert should decode");
        let mut verifier_session = npa_cert::VerifierSession::new();
        verifier_session.register_verified_module(verified);
        let verifier_output = npa_cert::verify_module_cert(
            &cert_bytes,
            &mut verifier_session,
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("Human verify certificate should re-verify");
        assert_eq!(ok.certificate_hash, verifier_output.certificate_hash());
        assert_eq!(ok.export_hash, verifier_output.export_hash());

        let entry = get_human_proof_state(&store, &header.session_id, &closed_state_id)
            .expect("closed Human proof state should still be stored");
        let error_context = HumanVerifyErrorContext {
            session_id: &header.session_id,
            state_id: &closed_state_id,
        };
        let root_index =
            human_verify_root_decl_index(&decoded_certificate, &entry.state, error_context)
                .expect("root declaration should be located in decoded certificate");
        let certificate_context =
            human_verify_certificate_context(&entry.state, &decoded_certificate, root_index);
        let verifier_axioms = human_verify_axiom_refs_to_wire(
            &certificate_context,
            &verifier_output.axiom_report().module_axioms,
            error_context,
        )
        .expect("verifier axiom report should project to Human response wire shape");
        assert_eq!(ok.axioms_used, verifier_axioms);
    }

    #[test]
    fn human_tactic_run_intro_exact_and_expected_pi_error_are_transactional() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem id_nat : forall (n : Nat), Nat := by simp-lite";
        let file_id = npa_frontend::FileId(30);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticRunIntroExact"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanTacticRunIntroExact.id_nat"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let root_goal = started
            .selected_goal
            .clone()
            .expect("initial state should select the root goal");

        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id.clone(),
                goal_id: root_goal.clone(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        assert_eq!(intro.parent_state_id, started.state_id);
        assert_eq!(intro.closed_goals, vec![root_goal]);
        assert_eq!(intro.new_goals.len(), 1);
        assert_eq!(intro.new_goals[0].context[0].name, "n");
        assert_eq!(intro.new_goals[0].target.pretty, "Nat");
        assert_eq!(intro.proof_deltas.len(), 1);
        assert!(intro.error.is_none());
        let intro_state_id = intro
            .new_state_id
            .clone()
            .expect("intro should record a new state");
        let intro_goal = intro
            .selected_goal
            .clone()
            .expect("intro response should select the new goal");
        let parent_after_intro =
            get_human_proof_state(&store, &created.session_id, &started.state_id)
                .expect("parent state should remain available after intro");
        assert_eq!(
            parent_after_intro.state.open_goals,
            vec![npa_tactic::GoalId(0)]
        );

        let exact = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: intro_state_id.clone(),
                goal_id: intro_goal.clone(),
                tactic: "exact n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(exact.status, HumanTacticRunStatus::Closed);
        assert_eq!(exact.closed_goals, vec![intro_goal]);
        assert!(exact.new_goals.is_empty());
        assert_eq!(exact.proof_deltas.len(), 1);
        assert!(exact.error.is_none());
        let exact_state_id = exact
            .new_state_id
            .clone()
            .expect("exact should record a closed state");
        let exact_entry = get_human_proof_state(&store, &created.session_id, &exact_state_id)
            .expect("exact state should be recorded");
        assert!(exact_entry.state.open_goals.is_empty());

        let eq_source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem self_eq (n : Nat) : Eq.{1} n n := by exact _";
        let eq_file_id = npa_frontend::FileId(31);
        let eq_created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticRunExpectedPi"),
                current_source: HumanCurrentModuleSource {
                    file_id: eq_file_id,
                    source: eq_source,
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human eq session should be created");
        let eq_started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: eq_created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanTacticRunExpectedPi.self_eq"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human eq proof should start");
        let eq_header = HumanStateRequestHeader {
            session_id: eq_created.session_id.clone(),
            document_id: eq_created.document_id.clone(),
            document_version: eq_created.document_version,
        };
        let eq_intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: eq_header.clone(),
                state_id: eq_started.state_id.clone(),
                goal_id: eq_started.selected_goal.clone().unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(eq_intro.status, HumanTacticRunStatus::Partial);
        let eq_state_id = eq_intro.new_state_id.clone().unwrap();
        let eq_goal_id = eq_intro.selected_goal.clone().unwrap();
        let state_count_before_error = store
            .session(&eq_created.session_id)
            .expect("eq session should exist")
            .proof_states
            .state_count();

        let bad_intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: eq_header,
                state_id: eq_state_id.clone(),
                goal_id: eq_goal_id.clone(),
                tactic: "intro h".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(bad_intro.status, HumanTacticRunStatus::Error);
        assert_eq!(bad_intro.new_state_id, None);
        let error = bad_intro
            .error
            .expect("bad intro should return an error report");
        assert_eq!(error.kind, HumanTacticRunErrorKind::ExpectedPiType);
        assert_eq!(error.old_state_id, eq_state_id);
        assert_eq!(error.goal_id, eq_goal_id);
        assert!(error.span.is_some());
        assert!(error
            .suggestions
            .iter()
            .any(|suggestion| suggestion.tactic == "simp-lite"));
        let state_count_after_error = store
            .session(&eq_created.session_id)
            .expect("eq session should exist")
            .proof_states
            .state_count();
        assert_eq!(state_count_after_error, state_count_before_error);
    }

    #[test]
    fn human_tactic_run_apply_eq_trans_returns_expected_subgoals() {
        let (eq, eq_interface) = verified_eq_trans_human_import();
        let verified_modules = vec![eq];
        let imported_source_interfaces = vec![eq_interface];
        let source = "\
import Std.Logic.Eq
theorem target (A : Type) (x y z : A) : Eq.{1} x z := by simp-lite";
        let file_id = npa_frontend::FileId(32);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticRunApply"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human apply session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanTacticRunApply.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human apply proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let mut state_id = started.state_id;
        let mut goal_id = started.selected_goal.unwrap();
        for tactic in ["intro A", "intro x", "intro y", "intro z"] {
            let response = run_human_tactic(
                &mut store,
                HumanTacticRunRequest {
                    header: header.clone(),
                    state_id: state_id.clone(),
                    goal_id,
                    tactic: tactic.to_owned(),
                    budget: npa_tactic::TacticBudget::default(),
                },
            );
            assert_eq!(response.status, HumanTacticRunStatus::Partial);
            state_id = response.new_state_id.expect("intro should record state");
            goal_id = response.selected_goal.expect("intro should select goal");
        }

        let applied = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header,
                state_id,
                goal_id,
                tactic: "apply Eq.trans".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(applied.status, HumanTacticRunStatus::Partial);
        assert_eq!(applied.new_goals.len(), 2);
        assert!(applied.error.is_none());
        assert_eq!(applied.proof_deltas.len(), 1);
        assert!(applied
            .new_goals
            .iter()
            .all(|goal| goal.target.pretty.contains('=')));
    }

    #[test]
    fn human_tactic_run_rw_nat_add_zero_and_simp_lite_use_proof_deltas() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem Nat.add_zero (n : Nat) : Eq.{1} n n := Eq.refl n
theorem target (n : Nat) : Eq.{1} n n := by simp-lite";
        let file_id = npa_frontend::FileId(33);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticRunRwSimp"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human rw/simp session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanTacticRunRwSimp.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human rw/simp proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        let intro_state_id = intro.new_state_id.clone().unwrap();
        let intro_goal_id = intro.selected_goal.clone().unwrap();

        let rewrite = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: intro_state_id.clone(),
                goal_id: intro_goal_id.clone(),
                tactic: "rw [Nat.add_zero]".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(rewrite.status, HumanTacticRunStatus::Partial);
        assert!(rewrite.error.is_none());
        assert!(!rewrite.proof_deltas.is_empty());
        assert_eq!(rewrite.closed_goals, vec![intro_goal_id.clone()]);
        assert_eq!(rewrite.new_goals.len(), 1);

        let simp = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header,
                state_id: intro_state_id,
                goal_id: intro_goal_id,
                tactic: "simp-lite".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(simp.status, HumanTacticRunStatus::Closed);
        assert!(simp.error.is_none());
        assert_eq!(simp.proof_deltas.len(), 1);
        assert!(simp.new_goals.is_empty());
    }

    #[test]
    fn human_tactic_suggest_builtin_intro_exact_refl_and_context_exact() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem id_nat : forall (n : Nat), Nat := by simp-lite";
        let file_id = npa_frontend::FileId(34);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticSuggestIntroExact"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human suggestion session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted(
                    "Api.HumanTacticSuggestIntroExact.id_nat",
                ),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human suggestion proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let root_goal = started.selected_goal.clone().unwrap();
        let state_count_before_suggest = store
            .session(&created.session_id)
            .unwrap()
            .proof_states
            .state_count();
        let suggestions = suggest_human_tactics(
            &store,
            HumanTacticSuggestRequest {
                header: header.clone(),
                state_id: started.state_id.clone(),
                goal_id: root_goal.clone(),
                max_results: 10,
            },
        );
        assert!(suggestions.error.is_none());
        let intro = suggestions
            .suggestions
            .iter()
            .find(|suggestion| suggestion.tactic == "intro n")
            .expect("Pi target should suggest intro n");
        assert_eq!(intro.source, HumanTacticSuggestionSource::Builtin);
        assert!(intro.confidence > 0);
        assert!(intro.reason.contains("Pi"));
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before_suggest
        );

        let check = check_human_tactic(
            &store,
            HumanTacticCheckRequest {
                header: header.clone(),
                state_id: started.state_id.clone(),
                goal_id: root_goal.clone(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(check.status, HumanTacticRunStatus::Partial);
        assert_eq!(check.state_id, started.state_id);
        assert_eq!(check.closed_goals, vec![root_goal.clone()]);
        assert_eq!(check.expected_goals.len(), 1);
        assert_eq!(check.expected_goals[0].context[0].name, "n");
        assert!(check.error.is_none());
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before_suggest
        );

        let intro_run = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: root_goal,
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro_run.status, HumanTacticRunStatus::Partial);
        let intro_state_id = intro_run.new_state_id.clone().unwrap();
        let intro_goal_id = intro_run.selected_goal.clone().unwrap();
        let state_count_before_context_suggest = store
            .session(&created.session_id)
            .unwrap()
            .proof_states
            .state_count();
        let context_suggestions = suggest_human_tactics(
            &store,
            HumanTacticSuggestRequest {
                header: header.clone(),
                state_id: intro_state_id.clone(),
                goal_id: intro_goal_id.clone(),
                max_results: 10,
            },
        );
        assert!(context_suggestions
            .suggestions
            .iter()
            .any(|suggestion| suggestion.tactic == "exact n"
                && suggestion.source == HumanTacticSuggestionSource::Builtin
                && suggestion.reason.contains("target type")));
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before_context_suggest
        );

        let eq_source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem self_eq (n : Nat) : Eq.{1} n n := by exact _";
        let eq_file_id = npa_frontend::FileId(35);
        let eq_created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticSuggestRefl"),
                current_source: HumanCurrentModuleSource {
                    file_id: eq_file_id,
                    source: eq_source,
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human equality suggestion session should be created");
        let eq_started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: eq_created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanTacticSuggestRefl.self_eq"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human equality suggestion proof should start");
        let eq_header = HumanStateRequestHeader {
            session_id: eq_created.session_id.clone(),
            document_id: eq_created.document_id.clone(),
            document_version: eq_created.document_version,
        };
        let eq_intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: eq_header.clone(),
                state_id: eq_started.state_id,
                goal_id: eq_started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        let eq_state_id = eq_intro.new_state_id.unwrap();
        let eq_goal_id = eq_intro.selected_goal.unwrap();
        let eq_state_count_before = store
            .session(&eq_created.session_id)
            .unwrap()
            .proof_states
            .state_count();
        let eq_suggestions = suggest_human_tactics(
            &store,
            HumanTacticSuggestRequest {
                header: eq_header,
                state_id: eq_state_id,
                goal_id: eq_goal_id,
                max_results: 10,
            },
        );
        assert!(eq_suggestions
            .suggestions
            .iter()
            .any(|suggestion| suggestion.tactic == "exact Eq.refl n"
                && suggestion.reason.contains("reflexive equality")));
        assert!(eq_suggestions
            .suggestions
            .iter()
            .any(|suggestion| suggestion.tactic == "simp-lite"));
        assert_eq!(
            store
                .session(&eq_created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            eq_state_count_before
        );
    }

    #[test]
    fn human_tactic_suggest_rw_induction_and_failures_do_not_mutate_state() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) (h : Eq.{1} n n) : Eq.{1} n n := by simp-lite";
        let file_id = npa_frontend::FileId(36);
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanTacticSuggestRwInduction"),
                current_source: HumanCurrentModuleSource { file_id, source },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human rw/induction suggestion session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted(
                    "Api.HumanTacticSuggestRwInduction.target",
                ),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human rw/induction suggestion proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id.clone(),
            document_version: created.document_version,
        };
        let mut state_id = started.state_id;
        let mut goal_id = started.selected_goal.unwrap();
        for tactic in ["intro n", "intro h"] {
            let response = run_human_tactic(
                &mut store,
                HumanTacticRunRequest {
                    header: header.clone(),
                    state_id: state_id.clone(),
                    goal_id,
                    tactic: tactic.to_owned(),
                    budget: npa_tactic::TacticBudget::default(),
                },
            );
            assert_eq!(response.status, HumanTacticRunStatus::Partial);
            state_id = response.new_state_id.unwrap();
            goal_id = response.selected_goal.unwrap();
        }

        let state_count_before = store
            .session(&created.session_id)
            .unwrap()
            .proof_states
            .state_count();
        let suggestions = suggest_human_tactics(
            &store,
            HumanTacticSuggestRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                max_results: 20,
            },
        );
        assert!(suggestions.error.is_none());
        for expected in ["exact h", "exact Eq.refl n", "rw [h]", "induction n"] {
            assert!(
                suggestions
                    .suggestions
                    .iter()
                    .any(|suggestion| suggestion.tactic == expected),
                "missing suggestion {expected}; got {:?}",
                suggestions
                    .suggestions
                    .iter()
                    .map(|suggestion| suggestion.tactic.as_str())
                    .collect::<Vec<_>>()
            );
        }
        assert!(suggestions
            .suggestions
            .iter()
            .all(
                |suggestion| suggestion.source == HumanTacticSuggestionSource::Builtin
                    && suggestion.confidence > 0
                    && !suggestion.reason.is_empty()
            ));
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before
        );

        let bad_check = check_human_tactic(
            &store,
            HumanTacticCheckRequest {
                header: header.clone(),
                state_id: state_id.clone(),
                goal_id: goal_id.clone(),
                tactic: "intro impossible".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(bad_check.status, HumanTacticRunStatus::Error);
        assert_eq!(
            bad_check.error.unwrap().kind,
            HumanTacticRunErrorKind::ExpectedPiType
        );
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before
        );

        let bad_suggest = suggest_human_tactics(
            &store,
            HumanTacticSuggestRequest {
                header,
                state_id,
                goal_id: HumanGoalId::new_unchecked("missing_goal"),
                max_results: 10,
            },
        );
        assert_eq!(
            bad_suggest.error.unwrap().kind,
            HumanTacticRunErrorKind::UnknownGoal
        );
        assert_eq!(
            store
                .session(&created.session_id)
                .unwrap()
                .proof_states
                .state_count(),
            state_count_before
        );
    }

    #[test]
    fn human_api_core_request_uses_explicit_verified_modules_and_current_source() {
        let request = HumanCompileCoreRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanCore"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(7),
                source: "def id : forall (A : Type), Type := fun A => A",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: HumanApiCompileOptions {
                max_notation_candidates: 4,
                ..human_api_default_compile_options()
            },
        };

        let ok = compile_human_source_to_core(request)
            .expect("Human API should compile explicit current source to core");

        assert_eq!(ok.core_module.declarations.len(), 1);
        assert_eq!(ok.source_interface.declarations.len(), 1);
    }

    #[test]
    fn human_typeclass_search_api_returns_core_dictionary_term_and_trace() {
        let source = "\
inductive Nat : Type where
| zero : Nat
axiom Nat.add : Nat -> Nat -> Nat
class Add (A : Type) where
  add : A -> A -> A
instance Nat.add_inst : Add Nat where
  add := Nat.add";
        let ok = search_human_typeclass(HumanTypeclassSearchRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTypeclass"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            goal_source: "Add Nat",
            options: human_api_default_compile_options(),
        })
        .expect("Human typeclass search API should return an OK response");

        assert_eq!(ok.status, npa_frontend::HumanTypeclassSearchStatus::Success);
        assert_eq!(
            ok.instance,
            Some(npa_cert::Name::from_dotted("Nat.add_inst"))
        );
        assert_eq!(
            ok.core_term,
            Some(npa_kernel::Expr::konst("Nat.add_inst", vec![]))
        );
        assert!(!ok.search_trace.is_empty());
        assert_eq!(crate::HUMAN_TYPECLASS_SEARCH_ENDPOINT, "/typeclass/search");

        compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTypeclassCheck"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(1),
                source: "\
inductive Nat : Type where
| zero : Nat
axiom Nat.add : Nat -> Nat -> Nat
class Add (A : Type) where
  add : A -> A -> A
instance Nat.add_inst : Add Nat where
  add := Nat.add
def Check : Add Nat := Nat.add_inst",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("returned dictionary term should be kernel-checkable for the goal");
    }

    #[test]
    fn human_typeclass_search_api_reports_ambiguity_without_score_selection() {
        let ok = search_human_typeclass(HumanTypeclassSearchRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTypeclassAmbiguous"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
inductive Nat : Type where
| zero : Nat
axiom Nat.add : Nat -> Nat -> Nat
axiom Nat.add_alt : Nat -> Nat -> Nat
class Add (A : Type) where
  add : A -> A -> A
instance Nat.add_inst : Add Nat where
  add := Nat.add
instance Nat.add_alt_inst : Add Nat where
  add := Nat.add_alt",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            goal_source: "Add Nat",
            options: human_api_default_compile_options(),
        })
        .expect("ambiguous Human typeclass search should still return structured output");

        assert_eq!(
            ok.status,
            npa_frontend::HumanTypeclassSearchStatus::Ambiguous
        );
        assert!(ok.instance.is_none());
        assert!(ok.core_term.is_none());
        assert!(ok
            .search_trace
            .iter()
            .any(|entry| entry.contains("Nat.add_inst")));
        assert!(ok
            .search_trace
            .iter()
            .any(|entry| entry.contains("Nat.add_alt_inst")));
    }

    #[test]
    fn human_api_returns_source_interface_for_downstream_human_imports() {
        let producer = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.Lib"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
axiom A : Type
def choose {B : Type} (x y : B) : B := x
infixl:65 \" ++ \" => choose",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("producer Human API request should compile");
        assert!(producer
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));
        let bytes =
            npa_cert::encode_module_cert(&producer.certificate).expect("producer cert encodes");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("producer cert verifies");
        let import = npa_frontend::VerifiedImport::from(&verified);
        let source_interface = npa_frontend::HumanImportedSourceInterface {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            source_interface: producer.source_interface,
        };

        let consumer = compile_human_source_to_core(HumanCompileCoreRequest {
            current_module: npa_cert::Name::from_dotted("Api.Consumer"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(1),
                source: "\
import Api.Lib
axiom a : A
def use : A := a ++ a",
            },
            verified_modules: std::slice::from_ref(&verified),
            imported_source_interfaces: &[source_interface],
            options: human_api_default_compile_options(),
        })
        .expect("consumer Human API request should use imported source metadata");

        assert_eq!(consumer.core_module.declarations.len(), 2);
    }

    #[test]
    fn human_api_compile_core_handoffs_by_proof_expr_before_later_decl() {
        let ok = compile_human_source_to_core(HumanCompileCoreRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanByCore"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
theorem id_prop : forall (P : Prop), Prop := by
  intro P
  exact P
def use (P : Prop) : Prop := id_prop P",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human API core path should replace by proof with extracted proof Expr");

        assert_eq!(ok.core_module.declarations.len(), 2);
        let Decl::Theorem {
            name, ty, proof, ..
        } = &ok.core_module.declarations[0]
        else {
            panic!("first declaration should be the by theorem");
        };
        assert_eq!(name, "Api.HumanByCore.id_prop");
        assert_eq!(
            ty,
            &Expr::pi(
                "P",
                Expr::sort(npa_kernel::Level::zero()),
                Expr::sort(npa_kernel::Level::zero())
            )
        );
        assert_eq!(
            proof,
            &Expr::lam("P", Expr::sort(npa_kernel::Level::zero()), Expr::bvar(0))
        );
        let Decl::Def { name, value, .. } = &ok.core_module.declarations[1] else {
            panic!("second declaration should use the by theorem");
        };
        assert_eq!(name, "Api.HumanByCore.use");
        assert_eq!(
            value,
            &Expr::lam(
                "P",
                Expr::sort(npa_kernel::Level::zero()),
                Expr::app(
                    Expr::konst("Api.HumanByCore.id_prop", Vec::new()),
                    Expr::bvar(0)
                )
            )
        );
        let cert = npa_cert::build_module_cert(ok.core_module, &[])
            .expect("by core module should certify");
        let bytes = npa_cert::encode_module_cert(&cert).expect("by core cert should encode");
        npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("by core cert should verify");
    }

    #[test]
    fn human_api_compile_certificate_verifies_by_proof_and_hashes_interface() {
        let ok = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanByCert"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
theorem id_type : forall (A : Type), Type := by
  intro A
  exact A",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human API certificate path should certify by proof theorem");

        assert!(ok
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));
        let bytes =
            npa_cert::encode_module_cert(&ok.certificate).expect("by proof cert should encode");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("by proof certificate should verify");
        assert_eq!(
            verified.module(),
            &npa_cert::Name::from_dotted("Api.HumanByCert")
        );
    }

    #[test]
    fn human_api_by_intro_exact_nat_certificate_verifies() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];

        let ok = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanByIntroExactNat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by
  intro n
  exact n",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human API should certify by intro n / exact n");

        assert!(ok
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));
        let bytes = npa_cert::encode_module_cert(&ok.certificate)
            .expect("intro/exact by proof cert should encode");
        let mut session = npa_cert::VerifierSession::new();
        session.register_verified_module(verified_modules[0].clone());
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .expect("intro/exact by proof cert should verify with Nat import");
        assert_eq!(
            verified.module(),
            &npa_cert::Name::from_dotted("Api.HumanByIntroExactNat")
        );
    }

    #[test]
    fn human_api_by_exact_eq_refl_uses_imported_source_interfaces() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];

        let ok = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanByExactEqRefl"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
import Std.Logic.Eq
def n : Nat := Nat.zero
theorem self_eq : Eq.{1} n n := by
  exact Eq.refl n",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human API should certify by exact Eq.refl n");

        assert!(ok
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));
        let bytes =
            npa_cert::encode_module_cert(&ok.certificate).expect("Eq.refl by cert should encode");
        let mut session = npa_cert::VerifierSession::new();
        for module in verified_modules {
            session.register_verified_module(module);
        }
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .expect("Eq.refl by proof cert should verify with Nat and Eq imports");
        assert_eq!(
            verified.module(),
            &npa_cert::Name::from_dotted("Api.HumanByExactEqRefl")
        );
    }

    #[test]
    fn machine_tactic_human_section13_minimal_certificate_fixtures_compile() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let default_options = human_api_default_compile_options();

        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticIntroExactFixture",
            "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by
  intro n
  exact n",
            &verified_modules,
            &imported_source_interfaces,
            default_options.clone(),
        );
        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticEqReflFixture",
            "\
import Std.Nat.Basic
import Std.Logic.Eq
def n : Nat := Nat.zero
theorem self_eq : Eq.{1} n n := by
  exact Eq.refl n",
            &verified_modules,
            &imported_source_interfaces,
            default_options.clone(),
        );
        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticApplyFixture",
            "\
theorem id_prop {q : Prop} (hq : q) : q := hq
theorem use_id (q : Prop) (hq : q) : q := by
  intro q
  intro hq
  apply id_prop
  exact hq",
            &[],
            &[],
            default_options.clone(),
        );
        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticSimpLiteFixture",
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem self_eq (n : Nat) : Eq.{1} n n := by
  intro n
  simp-lite",
            &verified_modules,
            &imported_source_interfaces,
            default_options,
        );
    }

    #[test]
    fn machine_tactic_human_section13_rw_and_induction_certificate_fixtures_compile() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];

        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticRwFixture",
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem rw_local (a b : Nat) (h : Eq.{1} a b) : Eq.{1} a a := by
  intro a
  intro b
  intro h
  rw [h]
  exact Eq.refl b",
            &verified_modules,
            &imported_source_interfaces,
            human_api_default_compile_options(),
        );
        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticPriorRwFixture",
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem rw_local (a b : Nat) (h : Eq.{1} a b) : Eq.{1} a a := by
  intro a
  intro b
  intro h
  rw [h]
  exact Eq.refl b
theorem use_rw_local (a b : Nat) (h : Eq.{1} a b) : Eq.{1} a a := by
  intro a
  intro b
  intro h
  exact rw_local a b h",
            &verified_modules,
            &imported_source_interfaces,
            human_api_default_compile_options(),
        );
        assert_human_fixture_certificate_verifies(
            "Api.HumanTacticInductionFixture",
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem ind_self (n : Nat) : Eq.{1} n n := by
  intro n
  induction n
  exact Eq.refl Nat.zero
  simp-lite",
            &verified_modules,
            &imported_source_interfaces,
            human_nat_compile_options(&verified_modules[0]),
        );
    }

    #[test]
    fn machine_tactic_human_section14_typeclass_driven_apply_is_rejected_by_diagnostic() {
        let source = "\
theorem no_typeclass_apply (p : Prop) : p := by
  intro p
  apply inferInstance";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTacticUnsupportedTypeclassApply"),
            theorem_name: npa_cert::Name::from_dotted(
                "Api.HumanTacticUnsupportedTypeclassApply.no_typeclass_apply",
            ),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("unsupported typeclass apply fixture should still start proof state");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("typeclass-driven apply is outside Human tactic MVP");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("typeclass-driven apply should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnknownIdentifier
        );
        assert!(diagnostic.message.contains("unknown apply head"));
    }

    #[test]
    fn human_api_compile_certificate_rejects_unresolved_by_goal_before_certificate() {
        let err = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanByOpenGoal"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
theorem open_goal : forall (A : Type), Type := by
  intro A",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect_err("unresolved Human by proof goal should stop before certificate construction");

        assert_eq!(
            err.diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal
        );
        assert_eq!(
            err.diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.phase),
            Some(npa_frontend::HumanDiagnosticPhase::TacticUnresolvedGoal)
        );
        let payload = human_payload(&err.diagnostic);
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(payload.hole_goals[0].context[0].name, "A");
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("Type"));
    }

    #[test]
    fn human_api_by_proof_certificate_uses_verified_imports() {
        let producer = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.ByImportLib"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
axiom ImportedP : Prop
axiom imported_p : ImportedP",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("producer Human API request should compile");
        let bytes =
            npa_cert::encode_module_cert(&producer.certificate).expect("producer cert encodes");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("producer cert verifies");
        let import = npa_frontend::VerifiedImport::from(&verified);
        let source_interface = npa_frontend::HumanImportedSourceInterface {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            source_interface: producer.source_interface,
        };

        let ok = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.ByImportUser"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(1),
                source: "\
import Api.ByImportLib
theorem target : ImportedP := by
  exact imported_p",
            },
            verified_modules: std::slice::from_ref(&verified),
            imported_source_interfaces: &[source_interface],
            options: human_api_default_compile_options(),
        })
        .expect("by proof certificate path should use verified imports");
        let bytes = npa_cert::encode_module_cert(&ok.certificate).expect("consumer cert encodes");
        let mut session = npa_cert::VerifierSession::new();
        session.register_verified_module(verified);
        npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
            .expect("consumer by proof cert verifies with import");
    }

    #[test]
    fn human_proof_bridge_starts_machine_state_for_by_theorem() {
        let ok = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanProof"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanProof.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
def choose {A : Type} (x y : A) : A := x
infixl:65 \" ++ \" => choose
def use (A : Type) (x : A) : A := x ++ x
theorem target : Prop := by simp-lite",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human bridge should start a deterministic Machine proof state");

        assert_eq!(
            ok.state.root.module,
            npa_cert::Name::from_dotted("Api.HumanProof")
        );
        assert_eq!(
            ok.state.root.theorem_name,
            npa_cert::Name::from_dotted("Api.HumanProof.target")
        );
        assert_eq!(ok.state.root.source_index, 2);
        assert_eq!(ok.state.env.checked_current_decls.len(), 2);
        assert_eq!(ok.state.open_goals.len(), 1);
        assert_eq!(
            ok.state.root.theorem_type,
            npa_kernel::Expr::sort(npa_kernel::Level::zero())
        );
        npa_tactic::validate_machine_proof_state(&ok.state)
            .expect("Human-started state must pass Machine state validation");
    }

    #[test]
    fn human_proof_bridge_uses_verified_imports_and_source_interfaces() {
        let producer = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted("Api.ProofLib"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "axiom ImportedP : Prop",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("producer Human API request should compile");
        let bytes =
            npa_cert::encode_module_cert(&producer.certificate).expect("producer cert encodes");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("producer cert verifies");
        let import = npa_frontend::VerifiedImport::from(&verified);
        let source_interface = npa_frontend::HumanImportedSourceInterface {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            source_interface: producer.source_interface,
        };

        let ok = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanImportProof"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanImportProof.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(1),
                source: "\
import Api.ProofLib
theorem target : ImportedP := by simp-lite",
            },
            verified_modules: &[verified],
            imported_source_interfaces: &[source_interface],
            options: human_api_default_compile_options(),
        })
        .expect("Human bridge should start a state with active verified imports");

        assert_eq!(ok.state.env.imports.len(), 1);
        assert_eq!(ok.state.root.source_index, 0);
        npa_tactic::validate_machine_proof_state(&ok.state)
            .expect("import-backed Human-started state must validate");
    }

    #[test]
    fn human_tactic_term_bridge_checks_goal_local_without_machine_hot_path_dependency() {
        let ok = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanTactic"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanTactic.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "theorem target : forall (A : Type), Type := by simp-lite",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start a theorem with a Pi target");
        let (state, _) = npa_tactic::run_machine_tactic(
            &ok.state,
            npa_tactic::MachineTactic::Intro {
                goal_id: npa_tactic::GoalId(0),
                name: "A".to_owned(),
            },
        )
        .expect("Machine intro should create a local A goal");
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "A")
            .expect("Human tactic term should parse");
        let checked = check_human_tactic_term(HumanTacticTermCheckRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(1),
            term: &term,
            current_source_interface: &ok.source_interface,
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human tactic bridge should check exact local A");

        assert_eq!(checked.expr, npa_kernel::Expr::bvar(0));
        assert_eq!(
            checked.inferred_type,
            npa_kernel::Expr::sort(npa_kernel::type0())
        );
    }

    #[test]
    fn human_exact_closes_nat_identity_goal_with_local() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanExactNat"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanExactNat.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let (state, _) = npa_tactic::run_machine_tactic(
            &started.state,
            npa_tactic::MachineTactic::Intro {
                goal_id: npa_tactic::GoalId(0),
                name: "n".to_owned(),
            },
        )
        .expect("intro should expose the Nat local");
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "n")
            .expect("Human exact term should parse");

        let ok = run_human_exact_tactic(HumanExactTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(1),
            term: &term,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human exact should check the local and close the goal");

        assert!(ok.state.open_goals.is_empty());
        assert!(ok.delta.added_goals.is_empty());
        assert_eq!(ok.expr, npa_kernel::Expr::bvar(0));
        assert_eq!(ok.inferred_type, npa_kernel::nat());
        let proof = npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("closed Human exact proof should extract");
        assert_eq!(
            proof,
            npa_kernel::Expr::lam("n", npa_kernel::nat(), npa_kernel::Expr::bvar(0))
        );
    }

    #[test]
    fn human_exact_inserts_eq_refl_implicit_and_closes_goal() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanExactEq"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanExactEq.self_eq"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem self_eq (n : Nat) : Eq.{1} n n := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start self_eq");
        let (state, _) = npa_tactic::run_machine_tactic(
            &started.state,
            npa_tactic::MachineTactic::Intro {
                goal_id: npa_tactic::GoalId(0),
                name: "n".to_owned(),
            },
        )
        .expect("intro should expose the Nat local");
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "Eq.refl n")
            .expect("Human exact term should parse");
        let expected = npa_kernel::eq(
            npa_kernel::type0(),
            npa_kernel::nat(),
            npa_kernel::Expr::bvar(0),
            npa_kernel::Expr::bvar(0),
        );

        let ok = run_human_exact_tactic(HumanExactTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(1),
            term: &term,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human exact should elaborate Eq.refl n and close the goal");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(
            ok.expr,
            npa_kernel::eq_refl(
                npa_kernel::type0(),
                npa_kernel::nat(),
                npa_kernel::Expr::bvar(0)
            )
        );
        assert_eq!(ok.inferred_type, expected);
        let proof = npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("closed Human exact proof should extract");
        assert_eq!(
            proof,
            npa_kernel::Expr::lam(
                "n",
                npa_kernel::nat(),
                npa_kernel::eq_refl(
                    npa_kernel::type0(),
                    npa_kernel::nat(),
                    npa_kernel::Expr::bvar(0)
                )
            )
        );
    }

    #[test]
    fn human_exact_rejects_unresolved_hole_without_mutating_state() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanExactHole"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanExactHole.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let (state, _) = npa_tactic::run_machine_tactic(
            &started.state,
            npa_tactic::MachineTactic::Intro {
                goal_id: npa_tactic::GoalId(0),
                name: "n".to_owned(),
            },
        )
        .expect("intro should expose the Nat local");
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "_")
            .expect("Human hole should parse");

        let err = run_human_exact_tactic(HumanExactTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(1),
            term: &term,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect_err("Human exact must reject unresolved holes conservatively");

        assert!(matches!(
            err,
            HumanTacticTermError::Human(HumanCompileError {
                diagnostic: npa_frontend::HumanDiagnostic {
                    kind: npa_frontend::HumanDiagnosticKind::UnsolvedHole,
                    ..
                }
            })
        ));
        assert_eq!(state.open_goals, vec![npa_tactic::GoalId(1)]);
        assert!(
            npa_tactic::extract_closed_machine_proof(&state).is_err(),
            "rejected Human exact must leave the original goal open"
        );
    }

    #[test]
    fn human_exact_type_mismatch_returns_goal_payload() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanExactMismatch"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanExactMismatch.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem target : Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start Nat target");
        let original_fingerprint = started.state.fingerprint;
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "Prop")
            .expect("Prop should parse as a Human term");

        let err = run_human_exact_tactic(HumanExactTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            term: &term,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect_err("exact Prop should not prove Nat");

        let HumanTacticTermError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("exact mismatch should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        );
        let payload = human_payload(&diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticValidation)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("Nat"));
        assert_eq!(started.state.fingerprint, original_fingerprint);
    }

    #[test]
    fn human_intro_creates_nat_body_goal_via_machine_intro() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanIntroNat"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanIntroNat.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let name = human_name("n", 0, 1);
        let budget = npa_tactic::TacticBudget::default();

        let human = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            name: &name,
            budget,
        })
        .expect("Human intro should create a Nat body goal");
        let direct_machine = npa_tactic::run_machine_tactic_with_budget(
            &started.state,
            npa_tactic::MachineTactic::Intro {
                goal_id: npa_tactic::GoalId(0),
                name: "n".to_owned(),
            },
            budget,
        )
        .expect("direct Machine intro should match Human intro");

        assert_eq!(human.delta, direct_machine.1);
        assert_eq!(human.state.fingerprint, direct_machine.0.fingerprint);
        assert_eq!(human.state.open_goals, vec![npa_tactic::GoalId(1)]);
        let goal = human
            .state
            .goal(npa_tactic::GoalId(1))
            .expect("intro should create goal 1");
        assert_eq!(goal.context.len(), 1);
        assert_eq!(goal.context[0].name, "n");
        assert_eq!(goal.context[0].ty, npa_kernel::nat());
        assert_eq!(goal.target, npa_kernel::nat());
    }

    #[test]
    fn human_intro_non_pi_returns_human_expected_function_diagnostic() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanIntroNonPi"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanIntroNonPi.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem target : Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start a non-Pi theorem");
        let name = human_name("n", 0, 1);
        let budget = npa_tactic::TacticBudget::default();
        let intro_tactic = npa_tactic::MachineTactic::Intro {
            goal_id: npa_tactic::GoalId(0),
            name: "n".to_owned(),
        };
        let cache_key_before = npa_tactic::machine_tactic_cache_key_hash(
            &npa_tactic::machine_tactic_cache_key(&started.state, &intro_tactic, budget),
        );

        let err = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            name: &name,
            budget,
        })
        .expect_err("intro should reject non-Pi targets as a Human diagnostic");

        let HumanIntroTacticError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("non-Pi intro should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::ExpectedFunctionType
        );
        assert_eq!(
            diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.phase),
            Some(npa_frontend::HumanDiagnosticPhase::TacticExecution)
        );
        let payload = human_payload(&diagnostic);
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(payload.hole_goals[0].hole.as_deref(), Some("g0"));
        assert!(payload.hole_goals[0].context.is_empty());
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("Nat"));
        let cache_key_after = npa_tactic::machine_tactic_cache_key_hash(
            &npa_tactic::machine_tactic_cache_key(&started.state, &intro_tactic, budget),
        );
        assert_eq!(cache_key_after, cache_key_before);
        assert_eq!(started.state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_intro_rejects_shadowing_name_deterministically() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanIntroShadow"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanIntroShadow.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem target : forall (n : Nat), forall (m : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start a two-argument theorem");
        let name = human_name("n", 0, 1);
        let first = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            name: &name,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("first intro should succeed");

        let err = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &first.state,
            goal_id: npa_tactic::GoalId(1),
            name: &name,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("second intro should reject local shadowing deterministically");

        let HumanIntroTacticError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("intro shadowing should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        );
        assert_eq!(first.state.open_goals, vec![npa_tactic::GoalId(1)]);
    }

    #[test]
    fn human_intro_rejects_invalid_binder_name_deterministically() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanIntroInvalidName"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanIntroInvalidName.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let name = human_name_parts(&["Nat", "x"], 0, 5);

        let err = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            name: &name,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("intro should reject non-local binder names deterministically");

        let HumanIntroTacticError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("invalid intro binder should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        );
        assert_eq!(started.state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_intro_then_exact_closes_id_nat() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanIntroExact"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanIntroExact.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by simp-lite",
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let name = human_name("n", 0, 1);
        let intro = run_human_intro_tactic(HumanIntroTacticRequest {
            state: &started.state,
            goal_id: npa_tactic::GoalId(0),
            name: &name,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human intro should create the body goal");
        let term = npa_frontend::parse_human_term(npa_frontend::FileId(0), "n")
            .expect("Human exact local should parse");
        let exact = run_human_exact_tactic(HumanExactTacticRequest {
            state: &intro.state,
            goal_id: npa_tactic::GoalId(1),
            term: &term,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human exact should close the body goal after intro");

        assert!(exact.state.open_goals.is_empty());
        let proof = npa_tactic::extract_closed_machine_proof(&exact.state)
            .expect("intro + exact proof should extract");
        assert_eq!(
            proof,
            npa_kernel::Expr::lam("n", npa_kernel::nat(), npa_kernel::Expr::bvar(0))
        );
    }

    #[test]
    fn human_tactic_script_executor_closes_intro_exact_script() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let source = "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by
  intro n
  exact n";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanScriptIntroExact"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanScriptIntroExact.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human script executor should close intro + exact");

        assert_eq!(ok.deltas.len(), 2);
        assert!(ok.state.open_goals.is_empty());
        assert_eq!(
            ok.proof,
            npa_kernel::Expr::lam("n", npa_kernel::nat(), npa_kernel::Expr::bvar(0))
        );
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("extracted script proof should pass kernel check");
    }

    #[test]
    fn human_smt_tactic_closes_from_local_hypothesis() {
        let core = compile_human_source_to_core(HumanCompileCoreRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanSmt"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source: "\
theorem target : forall (P : Prop), forall (h : P), P := by
  intro P
  intro h
  smt",
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("Human smt should compile through checked Machine tactic path");

        assert_eq!(core.core_module.declarations.len(), 1);
        let npa_kernel::Decl::Theorem { proof, .. } = &core.core_module.declarations[0] else {
            panic!("expected theorem");
        };
        assert!(matches!(proof, Expr::Lam { .. }));
    }

    #[test]
    fn human_tactic_script_executor_rejects_extra_tactic_after_close() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let source = "\
import Std.Nat.Basic
theorem zero : Nat := by
  exact Nat.zero
  exact Nat.zero";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanScriptExtra"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanScriptExtra.zero"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start zero");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("extra tactic after closed goal should be rejected");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("extra tactic should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::NoGoalsButTacticRemaining
        );
        assert_eq!(
            human_payload(&diagnostic).phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticExecution)
        );
        assert_eq!(started.state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_tactic_script_executor_applies_tactic_to_first_open_goal() {
        let verified_modules = Vec::new();
        let imported_source_interfaces = Vec::new();
        let source = "\
theorem target : Prop := by
  exact fun (p : Prop) => p";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanScriptFirstGoal"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanScriptFirstGoal.target"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start target");
        let budget = npa_tactic::TacticBudget::default();
        let (state, _) = npa_tactic::assign_goal(
            &started.state,
            npa_tactic::GoalId(0),
            npa_tactic::ProofExpr::app(
                npa_tactic::ProofExpr::meta(npa_tactic::MetaVarId(1)),
                npa_tactic::ProofExpr::meta(npa_tactic::MetaVarId(2)),
            ),
            vec![
                npa_tactic::MachineNewGoalSpec::new(
                    Vec::new(),
                    npa_kernel::Expr::pi(
                        "p",
                        npa_kernel::Expr::sort(npa_kernel::prop()),
                        npa_kernel::Expr::sort(npa_kernel::prop()),
                    ),
                ),
                npa_tactic::MachineNewGoalSpec::new(
                    Vec::new(),
                    npa_kernel::Expr::sort(npa_kernel::prop()),
                ),
            ],
        )
        .expect("Machine setup should split root into two goals");
        assert_eq!(
            state.open_goals,
            vec![npa_tactic::GoalId(1), npa_tactic::GoalId(2)]
        );
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget,
        })
        .expect_err("one exact should close the first goal and leave the step goal open");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("remaining second goal should be a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal
        );
        let payload = human_payload(&diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticUnresolvedGoal)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(payload.hole_goals[0].hole.as_deref(), Some("g2"));
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("Prop"));
    }

    #[test]
    fn human_tactic_script_executor_reports_unresolved_goal_at_end() {
        let (nat, nat_interface) = verified_nat_human_import();
        let verified_modules = vec![nat];
        let imported_source_interfaces = vec![nat_interface];
        let source = "\
import Std.Nat.Basic
theorem id_nat : forall (n : Nat), Nat := by
  intro n";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanScriptUnresolved"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanScriptUnresolved.id_nat"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start id_nat");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("script with remaining body goal should be rejected");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("unresolved goal should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal
        );
        assert_ne!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::NoGoalsButTacticRemaining
        );
        let payload = human_payload(&diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticUnresolvedGoal)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(payload.hole_goals[0].context[0].name, "n");
        assert_eq!(payload.hole_goals[0].context[0].ty, "Nat");
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("Nat"));
        assert_eq!(started.state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_apply_local_assumption_creates_subgoal_closed_by_exact() {
        let verified_modules = Vec::new();
        let imported_source_interfaces = Vec::new();
        let source = "\
theorem use_local (p q : Prop) (h : forall (hp : p), q) (hp : p) : q := by
  intro p
  intro q
  intro h
  intro hp
  apply h
  exact hp";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanApplyLocal"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanApplyLocal.use_local"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start use_local");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human apply local script should close");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 6);
        assert_eq!(ok.deltas[4].added_goals.len(), 1);
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human apply local proof should pass kernel check");
    }

    #[test]
    fn human_apply_checked_current_theorem_creates_subgoal_closed_by_exact() {
        let verified_modules = Vec::new();
        let imported_source_interfaces = Vec::new();
        let source = "\
theorem id_prop {q : Prop} (hq : q) : q := hq
theorem use_id (q : Prop) (hq : q) : q := by
  intro q
  intro hq
  apply id_prop
  exact hq";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanApplyCurrent"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanApplyCurrent.use_id"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start use_id with checked current id_prop");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human apply checked current script should close");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 4);
        assert_eq!(ok.deltas[2].added_goals.len(), 1);
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human apply checked current proof should pass kernel check");
    }

    #[test]
    fn human_apply_mismatch_reports_target_and_head_type() {
        let verified_modules = Vec::new();
        let imported_source_interfaces = Vec::new();
        let source = "\
theorem bad_apply (p q : Prop) (hp : p) : q := by
  intro p
  intro q
  intro hp
  apply hp";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanApplyMismatch"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanApplyMismatch.bad_apply"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start bad_apply");
        let script = first_theorem_script(source);
        let original_fingerprint = started.state.fingerprint;

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("Human apply mismatch should be a Human diagnostic");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("apply mismatch should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        );
        assert!(diagnostic.message.contains("cannot apply `hp`"));
        assert!(diagnostic.message.contains("target:"));
        assert!(diagnostic.message.contains("head type:"));
        let payload = human_payload(&diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticExecution)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(
            payload.hole_goals[0]
                .context
                .iter()
                .map(|local| local.name.as_str())
                .collect::<Vec<_>>(),
            vec!["p", "q", "hp"]
        );
        assert_eq!(payload.hole_goals[0].target.as_deref(), Some("q"));
        assert_eq!(started.state.fingerprint, original_fingerprint);
    }

    #[test]
    fn human_rw_local_forward_rewrites_eq_sides_and_exact_closes() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem rw_local (a b : Nat) (h : Eq.{1} a b) : Eq.{1} a a := by
  intro a
  intro b
  intro h
  rw [h]
  exact Eq.refl b";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanRewriteLocal"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanRewriteLocal.rw_local"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start rw_local");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human rw local script should close");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 6);
        assert_eq!(ok.deltas[3].added_goals.len(), 1);
        assert_eq!(ok.deltas[4].added_goals.len(), 1);
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human rw local proof should pass kernel check");
    }

    #[test]
    fn human_rw_local_backward_rewrites_deterministically() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem rw_backward (a b : Nat) (h : Eq.{1} a b) : Eq.{1} b b := by
  intro a
  intro b
  intro h
  rw [<- h]
  exact Eq.refl a";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanRewriteBackward"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanRewriteBackward.rw_backward"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start rw_backward");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human reverse rw local script should close");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 6);
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human reverse rw proof should pass kernel check");
    }

    #[test]
    fn human_rw_checked_current_theorem_rule_runs_through_machine_rewrite() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem refl_rule (x : Nat) : Eq.{1} x x := Eq.refl x
theorem use_refl_rule (a : Nat) : Eq.{1} a a := by
  intro a
  rw [refl_rule]
  exact Eq.refl a";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanRewriteCurrent"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanRewriteCurrent.use_refl_rule"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start use_refl_rule");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human rw checked current theorem script should close");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 4);
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human rw checked current proof should pass kernel check");
    }

    #[test]
    fn human_rw_rejects_complex_rule_head_as_unsupported() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem bad_rw (a : Nat) : Eq.{1} a a := by
  intro a
  rw [Eq.refl a]";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanRewriteUnsupported"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanRewriteUnsupported.bad_rw"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start bad_rw");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("complex rw rule head should be rejected");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("complex rw rule should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        );
        assert!(diagnostic.message.contains("Human rw MVP"));
    }

    #[test]
    fn human_rw_conditional_rule_fails_as_human_diagnostic() {
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![eq];
        let imported_source_interfaces = vec![eq_interface];
        let source = "\
import Std.Logic.Eq
theorem bad_conditional_rw (p q : Prop) (h : forall (hp : p), Eq.{1} p q) : Eq.{1} p p := by
  intro p
  intro q
  intro h
  rw [h]";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanRewriteConditional"),
            theorem_name: npa_cert::Name::from_dotted(
                "Api.HumanRewriteConditional.bad_conditional_rw",
            ),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start bad_conditional_rw");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("conditional rw should fail deterministically");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("conditional rw should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        );
        assert!(diagnostic.message.contains("cannot rewrite with `h`"));
        assert!(diagnostic.message.contains("rule type:"));
    }

    #[test]
    fn human_simp_lite_closes_reflexive_eq_target() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem self_eq (n : Nat) : Eq.{1} n n := by
  intro n
  simp-lite";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanSimpRefl"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanSimpRefl.self_eq"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
        })
        .expect("Human proof bridge should start self_eq");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options: human_api_default_compile_options(),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human simp-lite should close reflexive Eq target");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 2);
        assert!(ok.deltas[1].added_goals.is_empty());
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human simp-lite proof should pass kernel check");
    }

    #[test]
    fn human_simp_lite_uses_registered_rule_and_closes() {
        let import = npa_tactic::VerifiedImportRef::from_verified_module(
            &verified_axiom_simp_close_module(),
        )
        .expect("simp close module should become a tactic import");
        let rule_hash = export_interface_hash(&import, "Lib.succ_zero");
        let state = npa_tactic::start_machine_proof(
            human_simp_machine_spec(eq_nat(nat_succ(nat_zero()), nat_zero())),
            vec![import],
            Vec::new(),
            npa_tactic::MachineTacticOptions {
                simp_rules: vec![npa_tactic::SimpRuleRef {
                    name: npa_cert::Name::from_dotted("Lib.succ_zero"),
                    decl_interface_hash: rule_hash,
                    direction: npa_tactic::RewriteDirection::Forward,
                }],
                ..npa_tactic::MachineTacticOptions::default()
            },
        )
        .expect("Machine proof with registered simp rule should start");

        let ok = run_human_simp_lite_tactic(HumanSimpLiteTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(0),
            span: npa_frontend::Span::empty(npa_frontend::FileId(0)),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human simp-lite should reuse the registered Machine simp rule");

        assert!(ok.state.open_goals.is_empty());
        assert!(ok.delta.added_goals.is_empty());
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("registered-rule simp-lite proof should pass kernel check");
    }

    #[test]
    fn human_simp_lite_rejects_residual_goal_after_progress() {
        let import =
            npa_tactic::VerifiedImportRef::from_verified_module(&verified_one_unfold_simp_module())
                .expect("one_unfold module should become a tactic import");
        let rule_hash = export_interface_hash(&import, "Lib.one_unfold");
        let state = npa_tactic::start_machine_proof(
            human_simp_machine_spec(eq_nat(
                npa_kernel::Expr::konst("Lib.one", Vec::new()),
                nat_zero(),
            )),
            vec![import],
            Vec::new(),
            npa_tactic::MachineTacticOptions {
                simp_rules: vec![npa_tactic::SimpRuleRef {
                    name: npa_cert::Name::from_dotted("Lib.one_unfold"),
                    decl_interface_hash: rule_hash,
                    direction: npa_tactic::RewriteDirection::Forward,
                }],
                ..npa_tactic::MachineTacticOptions::default()
            },
        )
        .expect("Machine proof with registered simp rule should start");

        let err = run_human_simp_lite_tactic(HumanSimpLiteTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(0),
            span: npa_frontend::Span::empty(npa_frontend::FileId(0)),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("Human simp-lite MVP should reject residual goals");

        let HumanSimpLiteTacticError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("residual simp-lite goal should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::TypeMismatch
        );
        assert!(diagnostic.message.contains("did not close"));
        assert_eq!(state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_simp_lite_preserves_machine_step_limit_failure() {
        let import = npa_tactic::VerifiedImportRef::from_verified_module(
            &verified_axiom_simp_chain_module(),
        )
        .expect("simp chain module should become a tactic import");
        let first_rule_hash = export_interface_hash(&import, "Lib.a_two_one");
        let second_rule_hash = export_interface_hash(&import, "Lib.b_one_zero");
        let state = npa_tactic::start_machine_proof(
            human_simp_machine_spec(eq_nat(nat_succ(nat_succ(nat_zero())), nat_zero())),
            vec![import],
            Vec::new(),
            npa_tactic::MachineTacticOptions {
                simp_rules: vec![
                    npa_tactic::SimpRuleRef {
                        name: npa_cert::Name::from_dotted("Lib.a_two_one"),
                        decl_interface_hash: first_rule_hash,
                        direction: npa_tactic::RewriteDirection::Forward,
                    },
                    npa_tactic::SimpRuleRef {
                        name: npa_cert::Name::from_dotted("Lib.b_one_zero"),
                        decl_interface_hash: second_rule_hash,
                        direction: npa_tactic::RewriteDirection::Forward,
                    },
                ],
                max_simp_rewrite_steps: 1,
                ..npa_tactic::MachineTacticOptions::default()
            },
        )
        .expect("Machine proof with registered simp rule should start");

        let err = run_human_simp_lite_tactic(HumanSimpLiteTacticRequest {
            state: &state,
            goal_id: npa_tactic::GoalId(0),
            span: npa_frontend::Span::empty(npa_frontend::FileId(0)),
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("Human simp-lite should preserve Machine step-limit failures");

        let HumanSimpLiteTacticError::Machine(diagnostic) = err else {
            panic!("max_simp_rewrite_steps failure should stay a Machine diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_tactic::MachineTacticDiagnosticKind::SimpStepLimitExceeded
        );
        assert_eq!(state.open_goals, vec![npa_tactic::GoalId(0)]);
    }

    #[test]
    fn human_induction_nat_creates_base_step_and_closes_with_exact_simp() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let options = human_nat_compile_options(&nat);
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem ind_self (n : Nat) : Eq.{1} n n := by
  intro n
  induction n
  exact Eq.refl Nat.zero
  simp-lite";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanInductionNat"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanInductionNat.ind_self"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: options.clone(),
        })
        .expect("Human proof bridge should start ind_self");
        let script = first_theorem_script(source);

        let ok = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect("Human induction script should close base and step goals");

        assert!(ok.state.open_goals.is_empty());
        assert_eq!(ok.deltas.len(), 4);
        assert_eq!(
            ok.deltas[1].added_goals,
            vec![npa_tactic::GoalId(2), npa_tactic::GoalId(3)]
        );
        npa_tactic::extract_closed_machine_proof(&ok.state)
            .expect("Human induction proof should pass kernel check");
    }

    #[test]
    fn human_induction_rejects_dependent_later_hypothesis_as_human_diagnostic() {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let options = human_nat_compile_options(&nat);
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let source = "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem bad_induction (n : Nat) (h : Eq.{1} n n) : Eq.{1} n n := by
  intro n
  intro h
  induction n";
        let started = start_human_proof(HumanStartProofRequest {
            current_module: npa_cert::Name::from_dotted("Api.HumanInductionBad"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanInductionBad.bad_induction"),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &verified_modules,
            imported_source_interfaces: &imported_source_interfaces,
            options: options.clone(),
        })
        .expect("Human proof bridge should start bad_induction");
        let script = first_theorem_script(source);

        let err = run_human_tactic_script(HumanTacticScriptRunRequest {
            state: &started.state,
            script: &script,
            current_source_interface: &started.source_interface,
            imported_source_interfaces: &imported_source_interfaces,
            options,
            budget: npa_tactic::TacticBudget::default(),
        })
        .expect_err("dependent later hypothesis should be rejected by Human induction");

        let HumanTacticScriptError::Human(HumanCompileError { diagnostic }) = err else {
            panic!("dependent induction rejection should map to a Human diagnostic");
        };
        assert_eq!(
            diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::UnsupportedTactic
        );
        let payload = human_payload(&diagnostic);
        assert_eq!(
            payload.phase,
            Some(npa_frontend::HumanDiagnosticPhase::TacticExecution)
        );
        assert_eq!(payload.hole_goals.len(), 1);
        assert_eq!(
            payload.hole_goals[0]
                .context
                .iter()
                .map(|local| local.name.as_str())
                .collect::<Vec<_>>(),
            vec!["n", "h"]
        );
        assert!(diagnostic
            .message
            .contains("cannot perform simple induction"));
    }

    fn workspace_manifest(crate_name: &str) -> String {
        let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|path| path.parent())
            .expect("npa-api should live under crates/");
        let manifest_path = workspace_root
            .join("crates")
            .join(crate_name)
            .join("Cargo.toml");
        std::fs::read_to_string(&manifest_path).unwrap_or_else(|err| {
            panic!("failed to read {}: {err}", manifest_path.display());
        })
    }

    fn manifest_declares_dependency(manifest: &str, dependency: &str) -> bool {
        let prefix = format!("{dependency} = ");
        let dotted_prefix = format!("{dependency}.");
        let quoted_prefix = format!("\"{dependency}\" = ");
        let quoted_dotted_prefix = format!("\"{dependency}\".");
        let dependency_tables = [
            format!("[dependencies.{dependency}]"),
            format!("[dev-dependencies.{dependency}]"),
            format!("[build-dependencies.{dependency}]"),
        ];
        let target_dependency_kinds = [
            ".dependencies.",
            ".dev-dependencies.",
            ".build-dependencies.",
        ];
        let dependency_table_suffix = format!(".{dependency}]");
        manifest.lines().map(str::trim_start).any(|line| {
            line.starts_with(&prefix)
                || line.starts_with(&dotted_prefix)
                || line.starts_with(&quoted_prefix)
                || line.starts_with(&quoted_dotted_prefix)
                || dependency_tables.iter().any(|table| line == table)
                || (line.starts_with("[target.")
                    && target_dependency_kinds
                        .iter()
                        .any(|dependency_kind| line.contains(dependency_kind))
                    && line.ends_with(&dependency_table_suffix))
        })
    }

    #[test]
    fn human_tactic_bridge_boundary_avoids_frontend_tactic_cycle() {
        let frontend_manifest = workspace_manifest("npa-frontend");
        let tactic_manifest = workspace_manifest("npa-tactic");
        let api_manifest = workspace_manifest("npa-api");

        assert!(
            !manifest_declares_dependency(&frontend_manifest, "npa-tactic"),
            "Human tactic bridge must not live in npa-frontend; use npa-api or another adapter crate"
        );
        assert!(
            manifest_declares_dependency(&tactic_manifest, "npa-frontend"),
            "npa-tactic may consume Machine Surface helpers from npa-frontend"
        );
        assert!(
            manifest_declares_dependency(&api_manifest, "npa-frontend")
                && manifest_declares_dependency(&api_manifest, "npa-tactic"),
            "npa-api is the current adapter layer that can bridge Human frontend data to tactic execution"
        );
    }

    #[test]
    fn machine_session_api_stays_machine_surface_only() {
        let body = r#"{
            "protocol_version": "npa.machine-api.v1",
            "root": {
                "module": "Api.Machine",
                "theorem_name": "Api.Machine.thm",
                "source_index": 0,
                "universe_params": [],
                "theorem_type": {
                    "format": "machine_surface_v1",
                    "source": "by exact ("
                }
            },
            "import_closure": [],
            "imports": [],
            "checked_current_decls": [],
            "options": {
                "kernel_check_profile": "npa.kernel.v0.1.builtin-nat-eq-rec",
                "allow_axioms": [],
                "tactic_options": {
                    "simp_rules": [],
                    "eq_family": null,
                    "nat_family": null,
                    "max_simp_rewrite_steps": 100,
                    "max_open_goals": 32,
                    "max_metas": 64
                }
            }
        }"#;

        let err = create_machine_session(body)
            .expect_err("Machine session theorem_type must remain Machine Surface");

        assert_eq!(
            err.diagnostic.kind,
            crate::MachineApiErrorKind::MachineTermParseError
        );
    }

    fn human_theorem_index_entry_by_suffix<'a>(
        index: &'a HumanTheoremIndex,
        suffix: &str,
        kind: HumanTheoremIndexKind,
    ) -> &'a HumanTheoremIndexEntry {
        index
            .entries
            .iter()
            .find(|entry| entry.kind == kind && entry.name.as_dotted().ends_with(suffix))
            .unwrap_or_else(|| {
                panic!("Human theorem index should contain {kind:?} entry ending with {suffix}")
            })
    }

    fn human_name(value: &str, start: u32, end: u32) -> npa_frontend::HumanName {
        human_name_parts(&[value], start, end)
    }

    fn human_name_parts(parts: &[&str], start: u32, end: u32) -> npa_frontend::HumanName {
        npa_frontend::HumanName::new(
            parts.iter().map(|part| (*part).to_owned()).collect(),
            npa_frontend::Span::new(npa_frontend::FileId(0), start, end),
        )
    }

    fn first_theorem_script(source: &str) -> npa_frontend::HumanTacticScript {
        nth_theorem_script(source, 0)
    }

    fn assert_human_fixture_certificate_verifies(
        module: &str,
        source: &str,
        verified_modules: &[npa_cert::VerifiedModule],
        imported_source_interfaces: &[npa_frontend::HumanImportedSourceInterface],
        options: HumanApiCompileOptions,
    ) {
        let ok = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted(module),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules,
            imported_source_interfaces,
            options,
        })
        .expect("Human tactic fixture should compile to a certificate");
        assert!(ok
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));
        let bytes =
            npa_cert::encode_module_cert(&ok.certificate).expect("fixture certificate encodes");
        let mut session = npa_cert::VerifierSession::new();
        for verified in verified_modules {
            session.register_verified_module(verified.clone());
        }
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .expect("fixture certificate verifies");
        assert_eq!(verified.module(), &npa_cert::Name::from_dotted(module));
    }

    fn nth_theorem_script(source: &str, theorem_index: usize) -> npa_frontend::HumanTacticScript {
        let module = npa_frontend::parse_human_module(npa_frontend::FileId(0), source)
            .expect("Human source should parse");
        module
            .items
            .into_iter()
            .filter_map(|item| {
                let npa_frontend::HumanItem::Theorem(decl) = item else {
                    return None;
                };
                let npa_frontend::HumanDeclValue::ProofBlock(block) = decl.value else {
                    return None;
                };
                Some(block.script)
            })
            .nth(theorem_index)
            .expect("source should contain a theorem proof block")
    }

    fn verified_human_import(
        module: &str,
        source: &str,
    ) -> (
        npa_cert::VerifiedModule,
        npa_frontend::HumanImportedSourceInterface,
    ) {
        let producer = compile_human_source_to_certificate(HumanCompileCertificateRequest {
            current_module: npa_cert::Name::from_dotted(module),
            current_source: HumanCurrentModuleSource {
                file_id: npa_frontend::FileId(0),
                source,
            },
            verified_modules: &[],
            imported_source_interfaces: &[],
            options: human_api_default_compile_options(),
        })
        .expect("producer Human import source should compile");
        let bytes =
            npa_cert::encode_module_cert(&producer.certificate).expect("certificate should encode");
        let verified = npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("certificate should verify");
        let import = npa_frontend::VerifiedImport::from(&verified);
        let source_interface = npa_frontend::HumanImportedSourceInterface {
            module: import.module,
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            source_interface: producer.source_interface,
        };

        (verified, source_interface)
    }

    fn verified_nat_human_import() -> (
        npa_cert::VerifiedModule,
        npa_frontend::HumanImportedSourceInterface,
    ) {
        verified_human_import(
            "Std.Nat.Basic",
            "\
inductive Nat : Type where
| zero : Nat
| succ : forall (n : Nat), Nat",
        )
    }

    fn verified_eq_human_import() -> (
        npa_cert::VerifiedModule,
        npa_frontend::HumanImportedSourceInterface,
    ) {
        verified_human_import(
            "Std.Logic.Eq",
            "\
inductive Eq.{u} {A : Sort u} (a : A) : forall (b : A), Prop where
| refl : Eq.{u} a a",
        )
    }

    fn phase5_machine_minimal_session_json(theorem_type: &str) -> String {
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"{theorem_type}"}}
              }},
              "import_closure":[],
              "imports":[],
              "checked_current_decls":[],
              "options":{{
                "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
                "allow_axioms":[],
                "tactic_options":{{
                  "simp_rules":[],
                  "eq_family":null,
                  "nat_family":null,
                  "max_simp_rewrite_steps":100,
                  "max_open_goals":32,
                  "max_metas":64
                }}
              }}
            }}"#,
        )
    }

    fn phase5_machine_budget_json() -> &'static str {
        r#"{
          "max_tactic_steps":100,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#
    }

    fn phase7_machine_batch_json(
        session: &crate::MachineProofSession,
        state_fingerprint: Hash,
        candidates: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":{},
              "deterministic_budget":{},
              "batch_policy":{{
                "max_evaluated_candidates":256,
                "stop_after_successes":256,
                "stop_after_failures":256
              }}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            crate::format_hash_string(&state_fingerprint),
            candidates,
            phase5_machine_budget_json(),
        )
    }

    fn phase7_machine_exact_prop_batch_identity(
        session: &mut crate::MachineProofSession,
    ) -> (Hash, Hash, crate::SnapshotId, Hash) {
        let request = phase7_machine_batch_json(
            session,
            session.initial_snapshot.state_fingerprint,
            r#"[{"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}}]"#,
        );
        let response = crate::run_machine_tactic_batch_request(&request, session)
            .expect("Machine batch fixture should run");
        let crate::MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("Machine batch fixture should return ok response");
        };
        assert_eq!(ok.status, crate::MachineApiResponseStatus::Ok);
        assert_eq!(ok.endpoint_fields.results.len(), 1);
        let crate::MachineTacticBatchItemResponse::Success {
            candidate_hash,
            next_snapshot_id,
            next_state_fingerprint,
            ..
        } = ok.endpoint_fields.results[0]
        else {
            panic!("Machine exact Prop candidate should close");
        };
        (
            ok.endpoint_fields.previous_state_fingerprint,
            candidate_hash,
            next_snapshot_id,
            next_state_fingerprint,
        )
    }

    fn human_eq_refl_goal_fixture() -> (
        HumanProofSessionStore,
        HumanStateRequestHeader,
        crate::HumanStateId,
        HumanGoalId,
    ) {
        let (nat, nat_interface) = verified_nat_human_import();
        let (eq, eq_interface) = verified_eq_human_import();
        let verified_modules = vec![nat, eq];
        let imported_source_interfaces = vec![nat_interface, eq_interface];
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanAssistantEq"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(64),
                    source: "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem target (n : Nat) : Eq.{1} n n := by simp-lite",
                },
                verified_modules: &verified_modules,
                imported_source_interfaces: &imported_source_interfaces,
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human assistant equality session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanAssistantEq.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human assistant equality proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };
        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        (
            store,
            header,
            intro.new_state_id.expect("intro should record a new state"),
            intro
                .selected_goal
                .expect("intro should select the reflexive equality goal"),
        )
    }

    fn human_search_nat_add_zero_fixture() -> (
        HumanProofSessionStore,
        HumanStateRequestHeader,
        crate::HumanStateId,
        HumanGoalId,
    ) {
        let (verified, source_interface) = verified_human_import(
            "Std.Nat.Search",
            "\
inductive Nat : Type where
| zero : Nat
| succ : forall (n : Nat), Nat
inductive Eq.{u} {A : Sort u} (a : A) : forall (b : A), Prop where
| refl : Eq.{u} a a
def Nat.add (n : Nat) (m : Nat) : Nat := n
theorem Nat.add_zero (n : Nat) : Eq.{1} (Nat.add n Nat.zero) n := Eq.refl n",
        );
        let source = "\
import Std.Nat.Search
theorem target (n : Nat) : Eq.{1} (Nat.add n Nat.zero) n := by simp-lite";
        let mut store = HumanProofSessionStore::new();
        let created = create_human_session(
            &mut store,
            HumanSessionCreateRequest {
                current_module: npa_cert::Name::from_dotted("Api.HumanSearchNat"),
                current_source: HumanCurrentModuleSource {
                    file_id: npa_frontend::FileId(40),
                    source,
                },
                verified_modules: std::slice::from_ref(&verified),
                imported_source_interfaces: std::slice::from_ref(&source_interface),
                options: human_api_default_compile_options(),
            },
        )
        .expect("Human search session should be created");
        let started = start_human_session_proof(
            &mut store,
            HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: npa_cert::Name::from_dotted("Api.HumanSearchNat.target"),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human search proof should start");
        let header = HumanStateRequestHeader {
            session_id: created.session_id.clone(),
            document_id: created.document_id,
            document_version: created.document_version,
        };
        let intro = run_human_tactic(
            &mut store,
            HumanTacticRunRequest {
                header: header.clone(),
                state_id: started.state_id,
                goal_id: started.selected_goal.unwrap(),
                tactic: "intro n".to_owned(),
                budget: npa_tactic::TacticBudget::default(),
            },
        );
        assert_eq!(intro.status, HumanTacticRunStatus::Partial);
        (
            store,
            header,
            intro.new_state_id.expect("intro should record a new state"),
            intro
                .selected_goal
                .expect("intro should select the body goal"),
        )
    }

    fn human_verify_decode_hex_bytes(value: &str) -> Vec<u8> {
        assert!(value.len().is_multiple_of(2));
        value
            .as_bytes()
            .chunks_exact(2)
            .map(|chunk| (human_verify_hex_value(chunk[0]) << 4) | human_verify_hex_value(chunk[1]))
            .collect()
    }

    fn human_verify_hex_value(byte: u8) -> u8 {
        match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            _ => panic!("invalid lowercase hex digit"),
        }
    }

    fn verified_eq_trans_human_import() -> (
        npa_cert::VerifiedModule,
        npa_frontend::HumanImportedSourceInterface,
    ) {
        verified_human_import(
            "Std.Logic.Eq",
            "\
inductive Eq.{u} {A : Sort u} (a : A) : forall (b : A), Prop where
| refl : Eq.{u} a a
axiom Eq.trans {A : Type} {x : A} {z : A} (h1 : Eq.{1} x z) (h2 : Eq.{1} x z) : Eq.{1} x z",
        )
    }

    fn verified_core_module(module: npa_cert::CoreModule) -> npa_cert::VerifiedModule {
        let cert = npa_cert::build_module_cert(module, &[]).expect("core module cert builds");
        let bytes = npa_cert::encode_module_cert(&cert).expect("core module cert encodes");
        npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("core module cert verifies")
    }

    fn verified_one_unfold_simp_module() -> npa_cert::VerifiedModule {
        let one = npa_kernel::Expr::konst("Lib.one", Vec::new());
        verified_core_module(npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Lib.Simp"),
            declarations: vec![
                Decl::Def {
                    name: "Lib.one".to_owned(),
                    universe_params: Vec::new(),
                    ty: nat(),
                    value: nat_succ(nat_zero()),
                    reducibility: npa_kernel::Reducibility::Reducible,
                },
                Decl::Theorem {
                    name: "Lib.one_unfold".to_owned(),
                    universe_params: Vec::new(),
                    ty: eq_nat(one, nat_succ(nat_zero())),
                    proof: eq_refl_nat(nat_succ(nat_zero())),
                },
            ],
        })
    }

    fn verified_axiom_simp_close_module() -> npa_cert::VerifiedModule {
        let ty = eq_nat(nat_succ(nat_zero()), nat_zero());
        verified_core_module(npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Lib.SimpClose"),
            declarations: vec![
                Decl::Axiom {
                    name: "Lib.succ_zero_axiom".to_owned(),
                    universe_params: Vec::new(),
                    ty: ty.clone(),
                },
                Decl::Theorem {
                    name: "Lib.succ_zero".to_owned(),
                    universe_params: Vec::new(),
                    ty,
                    proof: npa_kernel::Expr::konst("Lib.succ_zero_axiom", Vec::new()),
                },
            ],
        })
    }

    fn verified_axiom_simp_chain_module() -> npa_cert::VerifiedModule {
        let two = nat_succ(nat_succ(nat_zero()));
        let one = nat_succ(nat_zero());
        let zero = nat_zero();
        let first_ty = eq_nat(two, one.clone());
        let second_ty = eq_nat(one, zero);
        verified_core_module(npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Lib.SimpChain"),
            declarations: vec![
                Decl::Axiom {
                    name: "Lib.a_two_one_axiom".to_owned(),
                    universe_params: Vec::new(),
                    ty: first_ty.clone(),
                },
                Decl::Theorem {
                    name: "Lib.a_two_one".to_owned(),
                    universe_params: Vec::new(),
                    ty: first_ty,
                    proof: npa_kernel::Expr::konst("Lib.a_two_one_axiom", Vec::new()),
                },
                Decl::Axiom {
                    name: "Lib.b_one_zero_axiom".to_owned(),
                    universe_params: Vec::new(),
                    ty: second_ty.clone(),
                },
                Decl::Theorem {
                    name: "Lib.b_one_zero".to_owned(),
                    universe_params: Vec::new(),
                    ty: second_ty,
                    proof: npa_kernel::Expr::konst("Lib.b_one_zero_axiom", Vec::new()),
                },
            ],
        })
    }

    fn export_interface_hash(import: &npa_tactic::VerifiedImportRef, name: &str) -> npa_cert::Hash {
        import
            .exports()
            .iter()
            .find(|export| export.name == npa_cert::Name::from_dotted(name))
            .expect("test export should exist")
            .decl_interface_hash
    }

    fn human_nat_compile_options(
        verified_nat: &npa_cert::VerifiedModule,
    ) -> HumanApiCompileOptions {
        let nat_import = npa_tactic::VerifiedImportRef::from_verified_module(verified_nat)
            .expect("verified Nat module should become a tactic import");
        HumanApiCompileOptions {
            tactic_options: npa_tactic::MachineTacticOptions {
                nat_family: Some(nat_family_ref(&nat_import)),
                ..npa_tactic::MachineTacticOptions::default()
            },
            ..human_api_default_compile_options()
        }
    }

    fn nat_family_ref(import: &npa_tactic::VerifiedImportRef) -> npa_tactic::NatFamilyRef {
        npa_tactic::NatFamilyRef {
            nat_name: npa_cert::Name::from_dotted("Nat"),
            nat_interface_hash: export_interface_hash(import, "Nat"),
            zero_name: npa_cert::Name::from_dotted("Nat.zero"),
            zero_interface_hash: export_interface_hash(import, "Nat.zero"),
            succ_name: npa_cert::Name::from_dotted("Nat.succ"),
            succ_interface_hash: export_interface_hash(import, "Nat.succ"),
            rec_name: npa_cert::Name::from_dotted("Nat.rec"),
            rec_interface_hash: export_interface_hash(import, "Nat.rec"),
        }
    }

    fn human_simp_machine_spec(theorem_type: Expr) -> npa_tactic::MachineProofSpec {
        npa_tactic::MachineProofSpec {
            module: npa_cert::Name::from_dotted("Api.HumanSimpMachine"),
            theorem_name: npa_cert::Name::from_dotted("Api.HumanSimpMachine.target"),
            source_index: 0,
            universe_params: Vec::new(),
            theorem_type,
        }
    }

    fn nat() -> Expr {
        npa_kernel::nat()
    }

    fn nat_zero() -> Expr {
        npa_kernel::nat_zero()
    }

    fn nat_succ(arg: Expr) -> Expr {
        npa_kernel::nat_succ(arg)
    }

    fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
        npa_kernel::eq(npa_kernel::type0(), nat(), lhs, rhs)
    }

    fn eq_refl_nat(value: Expr) -> Expr {
        npa_kernel::eq_refl(npa_kernel::type0(), nat(), value)
    }

    fn vec_type(level: Level, a: Expr, n: Expr) -> Expr {
        Expr::apps(Expr::konst("Vec", vec![level]), vec![a, n])
    }

    fn vec_inductive() -> npa_kernel::InductiveDecl {
        let u = Level::param("u");
        npa_kernel::InductiveDecl::new(
            "Vec",
            vec!["u".to_owned()],
            vec![npa_kernel::Binder::new("A", Expr::sort(u.clone()))],
            vec![npa_kernel::Binder::new("n", nat())],
            u.clone(),
            vec![
                npa_kernel::ConstructorDecl::new(
                    "Vec.nil",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        vec_type(u.clone(), Expr::bvar(0), nat_zero()),
                    ),
                ),
                npa_kernel::ConstructorDecl::new(
                    "Vec.cons",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "n",
                            nat(),
                            Expr::pi(
                                "x",
                                Expr::bvar(1),
                                Expr::pi(
                                    "xs",
                                    vec_type(u.clone(), Expr::bvar(2), Expr::bvar(1)),
                                    vec_type(u.clone(), Expr::bvar(3), nat_succ(Expr::bvar(2))),
                                ),
                            ),
                        ),
                    ),
                ),
            ],
            None,
        )
    }

    fn negative_indexed_inductive() -> npa_kernel::InductiveDecl {
        npa_kernel::InductiveDecl::new(
            "BadVec",
            vec![],
            vec![],
            vec![npa_kernel::Binder::new("n", nat())],
            npa_kernel::type0(),
            vec![npa_kernel::ConstructorDecl::new(
                "BadVec.mk",
                Expr::pi(
                    "f",
                    Expr::pi(
                        "_",
                        Expr::app(Expr::konst("BadVec", vec![]), nat_zero()),
                        nat(),
                    ),
                    Expr::app(Expr::konst("BadVec", vec![]), nat_zero()),
                ),
            )],
            None,
        )
    }
}
