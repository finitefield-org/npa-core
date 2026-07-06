use std::fs;
use std::path::{Path, PathBuf};

#[test]
fn rust_string_literals_do_not_use_numbered_phase_labels() {
    let root = workspace_root();
    let mut files = Vec::new();
    collect_rust_files(&root.join("crates"), &mut files);
    files.sort();

    let mut findings = Vec::new();
    for file in files {
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", file.display()));
        for hit in scan_string_literals(&source) {
            if has_numbered_label(&hit.body) {
                let rel = file.strip_prefix(&root).unwrap_or(&file);
                findings.push(format!("{}:{}: {}", rel.display(), hit.line, hit.body));
            }
        }
    }

    assert!(
        findings.is_empty(),
        "numbered roadmap labels found in Rust string literals:\n{}",
        findings.join("\n")
    );
}

fn workspace_root() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("npa-api crate should be under workspace crates directory")
        .to_path_buf()
}

fn collect_rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries =
        fs::read_dir(dir).unwrap_or_else(|err| panic!("failed to read {}: {err}", dir.display()));
    for entry in entries {
        let entry = entry.unwrap_or_else(|err| panic!("failed to read directory entry: {err}"));
        let path = entry.path();
        if path.is_dir() {
            collect_rust_files(&path, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

struct StringLiteralHit {
    line: usize,
    body: String,
}

fn scan_string_literals(source: &str) -> Vec<StringLiteralHit> {
    let bytes = source.as_bytes();
    let mut hits = Vec::new();
    let mut i = 0;
    let mut line = 1;

    while i < bytes.len() {
        match bytes[i] {
            b'\n' => {
                line += 1;
                i += 1;
            }
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                i += 2;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                i = skip_block_comment(bytes, i + 2, &mut line);
            }
            b'\'' if looks_like_char_literal(bytes, i) => {
                i = skip_char_literal(bytes, i);
            }
            b'r' => {
                if let Some(next) = scan_raw_string(bytes, i, line, &mut hits) {
                    line += count_newlines(&source[i..next]);
                    i = next;
                } else {
                    i += 1;
                }
            }
            b'b' | b'c' if bytes.get(i + 1) == Some(&b'r') => {
                if let Some(next) = scan_raw_string(bytes, i, line, &mut hits) {
                    line += count_newlines(&source[i..next]);
                    i = next;
                } else if bytes.get(i + 1) == Some(&b'"') {
                    let next = scan_quoted_string(bytes, i + 1, line, &mut hits);
                    line += count_newlines(&source[i..next]);
                    i = next;
                } else {
                    i += 1;
                }
            }
            b'b' | b'c' if bytes.get(i + 1) == Some(&b'"') => {
                let next = scan_quoted_string(bytes, i + 1, line, &mut hits);
                line += count_newlines(&source[i..next]);
                i = next;
            }
            b'"' => {
                let next = scan_quoted_string(bytes, i, line, &mut hits);
                line += count_newlines(&source[i..next]);
                i = next;
            }
            _ => {
                i += 1;
            }
        }
    }

    hits
}

fn skip_block_comment(bytes: &[u8], mut i: usize, line: &mut usize) -> usize {
    let mut depth = 1;
    while i < bytes.len() && depth > 0 {
        match bytes[i] {
            b'\n' => {
                *line += 1;
                i += 1;
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                depth += 1;
                i += 2;
            }
            b'*' if bytes.get(i + 1) == Some(&b'/') => {
                depth -= 1;
                i += 2;
            }
            _ => i += 1,
        }
    }
    i
}

fn looks_like_char_literal(bytes: &[u8], i: usize) -> bool {
    let Some(mut j) = i.checked_add(1) else {
        return false;
    };
    if bytes.get(j) == Some(&b'\\') {
        j += 2;
    } else {
        j += 1;
    }
    bytes.get(j) == Some(&b'\'')
}

fn skip_char_literal(bytes: &[u8], i: usize) -> usize {
    let mut j = i + 1;
    if bytes.get(j) == Some(&b'\\') {
        j += 2;
    } else {
        j += 1;
    }
    if bytes.get(j) == Some(&b'\'') {
        j + 1
    } else {
        i + 1
    }
}

fn scan_raw_string(
    bytes: &[u8],
    start: usize,
    line: usize,
    hits: &mut Vec<StringLiteralHit>,
) -> Option<usize> {
    let r_pos = if bytes.get(start) == Some(&b'r') {
        start
    } else if bytes.get(start + 1) == Some(&b'r') {
        start + 1
    } else {
        return None;
    };

    let mut i = r_pos + 1;
    let mut hashes = 0;
    while bytes.get(i) == Some(&b'#') {
        hashes += 1;
        i += 1;
    }
    if bytes.get(i) != Some(&b'"') {
        return None;
    }

    let body_start = i + 1;
    let mut body_end = body_start;
    while body_end < bytes.len() {
        if bytes[body_end] == b'"'
            && (0..hashes).all(|offset| bytes.get(body_end + 1 + offset) == Some(&b'#'))
        {
            let body = String::from_utf8_lossy(&bytes[body_start..body_end]).into_owned();
            hits.push(StringLiteralHit { line, body });
            return Some(body_end + 1 + hashes);
        }
        body_end += 1;
    }
    None
}

fn scan_quoted_string(
    bytes: &[u8],
    quote: usize,
    line: usize,
    hits: &mut Vec<StringLiteralHit>,
) -> usize {
    let mut i = quote + 1;
    let mut body = Vec::new();
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => {
                if let Some(next) = bytes.get(i + 1) {
                    body.push(bytes[i]);
                    body.push(*next);
                    i += 2;
                } else {
                    i += 1;
                }
            }
            b'"' => {
                hits.push(StringLiteralHit {
                    line,
                    body: String::from_utf8_lossy(&body).into_owned(),
                });
                return i + 1;
            }
            byte => {
                body.push(byte);
                i += 1;
            }
        }
    }
    i
}

fn count_newlines(source: &str) -> usize {
    source.bytes().filter(|byte| *byte == b'\n').count()
}

fn has_numbered_label(body: &str) -> bool {
    let lower = body.to_ascii_lowercase();
    let bytes = lower.as_bytes();
    let needle = ["pha", "se"].concat();
    let needle = needle.as_bytes();
    let mut index = 0;
    while let Some(relative) = find_bytes(&bytes[index..], needle) {
        let mut cursor = index + relative + needle.len();
        while matches!(bytes.get(cursor), Some(b' ' | b'_' | b'.' | b'-')) {
            cursor += 1;
        }
        if matches!(bytes.get(cursor), Some(b'0'..=b'9')) {
            return true;
        }
        index = cursor;
    }
    false
}

fn find_bytes(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}
