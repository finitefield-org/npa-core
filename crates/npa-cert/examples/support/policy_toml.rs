use std::collections::BTreeSet;

const POLICY_FORMAT: &str = "npa.independent-checker.axiom_policy.v1";

struct Assignment {
    key: String,
    value: String,
}

pub fn parse(source: &str) -> Result<Vec<String>, ()> {
    if source.as_bytes().starts_with(&[0xef, 0xbb, 0xbf]) {
        return Err(());
    }
    let assignments = collect_assignments(source)?;
    let mut seen = BTreeSet::new();
    for assignment in &assignments {
        if !seen.insert(assignment.key.as_str()) {
            return Err(());
        }
    }
    let format = assignments
        .iter()
        .find(|assignment| assignment.key == "format")
        .ok_or(())?;
    if parse_string_value(&format.value)?.as_deref() != Some(POLICY_FORMAT) {
        return Err(());
    }
    let allowed = assignments
        .iter()
        .find(|assignment| assignment.key == "allowed_axioms")
        .ok_or(())?;
    let entries = parse_string_array_value(&allowed.value)?.ok_or(())?;
    let mut names = Vec::with_capacity(entries.len());
    for entry in entries {
        let name = entry?;
        if !valid_dotted_name(&name) {
            return Err(());
        }
        names.push(name);
    }
    for pair in names.windows(2) {
        if canonical_name_bytes(&pair[0]) >= canonical_name_bytes(&pair[1]) {
            return Err(());
        }
    }
    if assignments
        .iter()
        .any(|assignment| !matches!(assignment.key.as_str(), "format" | "allowed_axioms"))
    {
        return Err(());
    }
    Ok(names)
}

fn collect_assignments(source: &str) -> Result<Vec<Assignment>, ()> {
    let lines = source.lines().collect::<Vec<_>>();
    let mut assignments = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let line = strip_comment(lines[index])?;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            index += 1;
            continue;
        }
        if trimmed.starts_with('[') {
            let end = trimmed.find(']').ok_or(())?;
            if !trimmed[end + 1..].trim().is_empty() {
                return Err(());
            }
            let key = trimmed[1..end].trim();
            if key.is_empty() {
                return Err(());
            }
            assignments.push(Assignment {
                key: key.to_owned(),
                value: "{table}".to_owned(),
            });
            index += 1;
            continue;
        }
        let eq_index = trimmed.find('=').ok_or(())?;
        let key = trimmed[..eq_index].trim();
        if key.is_empty() || !key.split('.').all(valid_key_component) {
            return Err(());
        }
        let mut value = trimmed[eq_index + 1..].trim().to_owned();
        while value.trim_start().starts_with('[') && !array_closed(&value)? {
            index += 1;
            if index >= lines.len() {
                return Err(());
            }
            value.push('\n');
            value.push_str(strip_comment(lines[index])?.trim());
        }
        assignments.push(Assignment {
            key: key.to_owned(),
            value,
        });
        index += 1;
    }
    Ok(assignments)
}

fn strip_comment(line: &str) -> Result<&str, ()> {
    let mut in_string = false;
    let mut escaped = false;
    for (index, ch) in line.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {}
            }
        } else {
            match ch {
                '"' => in_string = true,
                '#' => return Ok(&line[..index]),
                _ => {}
            }
        }
    }
    if in_string || escaped {
        Err(())
    } else {
        Ok(line)
    }
}

fn array_closed(value: &str) -> Result<bool, ()> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for ch in value.chars() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {}
            }
        } else {
            match ch {
                '"' => in_string = true,
                '[' => depth = depth.saturating_add(1),
                ']' => {
                    if depth == 0 {
                        return Err(());
                    }
                    depth -= 1;
                    if depth == 0 {
                        return Ok(true);
                    }
                }
                _ => {}
            }
        }
    }
    if in_string || escaped {
        Err(())
    } else {
        Ok(false)
    }
}

fn parse_string_value(value: &str) -> Result<Option<String>, ()> {
    let trimmed = value.trim();
    if trimmed == "null" {
        return Err(());
    }
    if !trimmed.starts_with('"') {
        return Ok(None);
    }
    let (string, next) = parse_basic_string_at(trimmed, 0)?;
    if !trimmed[next..].trim().is_empty() {
        return Err(());
    }
    Ok(Some(string))
}

fn parse_string_array_value(value: &str) -> Result<Option<Vec<Result<String, ()>>>, ()> {
    let trimmed = value.trim();
    if trimmed == "null" {
        return Err(());
    }
    if !trimmed.starts_with('[') {
        return Ok(None);
    }
    let mut out = Vec::new();
    let mut index = 1;
    loop {
        index = skip_ws(trimmed, index);
        if index >= trimmed.len() {
            return Err(());
        }
        if trimmed[index..].starts_with(']') {
            index += 1;
            if !trimmed[index..].trim().is_empty() {
                return Err(());
            }
            return Ok(Some(out));
        }
        if trimmed[index..].starts_with('"') {
            let (string, next) = parse_basic_string_at(trimmed, index)?;
            out.push(Ok(string));
            index = skip_ws(trimmed, next);
        } else {
            let start = index;
            while index < trimmed.len() && !matches!(trimmed.as_bytes()[index], b',' | b']') {
                index += 1;
            }
            if trimmed[start..index].trim() == "null" {
                return Err(());
            }
            out.push(Err(()));
            index = skip_ws(trimmed, index);
        }
        if index >= trimmed.len() {
            return Err(());
        }
        if trimmed[index..].starts_with(',') {
            index += 1;
        } else if !trimmed[index..].starts_with(']') {
            return Err(());
        }
    }
}

fn parse_basic_string_at(value: &str, mut index: usize) -> Result<(String, usize), ()> {
    if !value[index..].starts_with('"') {
        return Err(());
    }
    index += 1;
    let mut out = String::new();
    while index < value.len() {
        let ch = value[index..].chars().next().ok_or(())?;
        index += ch.len_utf8();
        match ch {
            '"' => return Ok((out, index)),
            '\\' => {
                let escaped = value[index..].chars().next().ok_or(())?;
                index += escaped.len_utf8();
                match escaped {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    'b' => out.push('\u{0008}'),
                    't' => out.push('\t'),
                    'n' => out.push('\n'),
                    'f' => out.push('\u{000c}'),
                    'r' => out.push('\r'),
                    _ => return Err(()),
                }
            }
            '\u{0000}'..='\u{001f}' => return Err(()),
            _ => out.push(ch),
        }
    }
    Err(())
}

fn skip_ws(value: &str, mut index: usize) -> usize {
    while index < value.len() {
        let ch = value[index..].chars().next().expect("index is in bounds");
        if ch.is_whitespace() {
            index += ch.len_utf8();
        } else {
            break;
        }
    }
    index
}

fn valid_key_component(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}

fn valid_dotted_name(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(valid_name_component)
}

fn valid_name_component(value: &str) -> bool {
    let mut bytes = value.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\''))
}

fn canonical_name_bytes(value: &str) -> Vec<u8> {
    let components = value.split('.').collect::<Vec<_>>();
    let mut out = Vec::new();
    encode_uvar_to(&mut out, components.len());
    for component in components {
        encode_uvar_to(&mut out, component.len());
        out.extend_from_slice(component.as_bytes());
    }
    out
}

fn encode_uvar_to(out: &mut Vec<u8>, mut value: usize) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_only_the_canonical_runner_schema() {
        assert_eq!(
            parse(
                r#"format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = [
  "B",
  "AA",
]"#,
            )
            .unwrap(),
            ["B", "AA"]
        );
        for invalid in [
            "",
            "format = 'npa.independent-checker.axiom_policy.v1'\nallowed_axioms = []",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = []\ndeny_custom_axioms = false",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = [\"AA\", \"B\"]",
        ] {
            assert!(parse(invalid).is_err(), "unexpected acceptance: {invalid}");
        }
    }
}
