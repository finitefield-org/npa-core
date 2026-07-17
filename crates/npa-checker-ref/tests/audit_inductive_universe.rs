use npa_checker_ref::{
    check_certificate, ReferenceCertificateSection, ReferenceCheckErrorKind, ReferenceCheckReason,
    ReferenceCheckResult, ReferenceCheckerPolicy, ReferenceImportStore, ReferenceTrustMode,
};

const SMALL_UNIVERSE_CERTIFICATE: &[u8] = include_bytes!(
    "../../../testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert"
);
const MUTUAL_SMALL_UNIVERSE_CERTIFICATE: &[u8] = include_bytes!(
    "../../../testdata/certificates/security/mutual-inductive-constructor-universe-bound-v0.2.npcert"
);

#[test]
fn reference_checker_rejects_single_and_mutual_small_universe_fixtures() {
    for (fixture_name, certificate) in [
        ("single", SMALL_UNIVERSE_CERTIFICATE),
        ("mutual", MUTUAL_SMALL_UNIVERSE_CERTIFICATE),
    ] {
        for trust_mode in [ReferenceTrustMode::Normal, ReferenceTrustMode::HighTrust] {
            let policy = ReferenceCheckerPolicy {
                trust_mode,
                ..ReferenceCheckerPolicy::default()
            };
            let result = check_certificate(certificate, &ReferenceImportStore::default(), &policy);

            let ReferenceCheckResult::Rejected(error) = result else {
                panic!(
                    "reference checker accepted the {fixture_name} universe-bound fixture in \
                     {trust_mode:?}"
                );
            };
            assert_eq!(error.kind, ReferenceCheckErrorKind::TypeCheck);
            assert_eq!(error.section, ReferenceCertificateSection::Declarations);
            assert_eq!(
                error.reason,
                Some(ReferenceCheckReason::ConstructorUniverseBoundViolation)
            );
        }
    }
}
