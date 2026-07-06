/// Return whether a canonical dotted global declaration name component is valid.
///
/// Components are ASCII-only and follow `[A-Za-z_][A-Za-z0-9_']*`.
pub fn is_canonical_name_component(component: &str) -> bool {
    let mut bytes = component.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    is_name_component_start(first) && bytes.all(is_name_component_continue)
}

/// Return whether a canonical dotted global declaration name is valid.
///
/// Names are one or more canonical components separated by `.`.
pub fn is_canonical_dotted_name(name: &str) -> bool {
    !name.is_empty() && name.split('.').all(is_canonical_name_component)
}

const fn is_name_component_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

const fn is_name_component_continue(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\''
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_name_component_grammar_allows_ascii_prime() {
        for name in [
            "Nat",
            "Nat.add",
            "Eq.trans'",
            "Foo.Bar.baz''",
            "_Private._helper2'",
        ] {
            assert!(is_canonical_dotted_name(name), "{name}");
        }
    }

    #[test]
    fn canonical_name_component_grammar_rejects_non_identifier_syntax() {
        for name in [
            "",
            ".Nat",
            "Nat.",
            "Nat..add",
            "2Nat",
            "Nat.2add",
            "Nat.+",
            "Nat.mul*",
            "Nat.add-prime",
            "Nat.add′",
            "'Nat",
        ] {
            assert!(!is_canonical_dotted_name(name), "{name}");
        }
    }
}
