//! Shared projection of Human source diagnostics into CLI source coordinates.

use npa_frontend::{FileId, HumanDelimiterDiagnostic, Span};
use npa_package::PackagePath;

use crate::diagnostic::{CommandDiagnosticDelimiterContext, CommandDiagnosticSourceContext};
use crate::fs::render_package_path;

pub(crate) fn command_source_context(
    source_path: &PackagePath,
    file_id: FileId,
    source: &str,
    span: Span,
) -> Option<CommandDiagnosticSourceContext> {
    if span.file_id != file_id || span.start.0 > span.end.0 {
        return None;
    }
    let start = usize::try_from(span.start.0).ok()?;
    let end = usize::try_from(span.end.0).ok()?;
    if end > source.len() {
        return None;
    }

    let mut context = CommandDiagnosticSourceContext::new(
        render_package_path(source_path),
        span.start.0,
        span.end.0,
    )?;
    if source.is_char_boundary(start) {
        let prefix = &source[..start];
        let line_usize = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
        let column_usize = source[line_start..start].chars().count() + 1;
        if let (Ok(line), Ok(column)) = (u32::try_from(line_usize), u32::try_from(column_usize)) {
            context = context.with_display_location(line, column);
        }
    }
    if start < end
        && source.is_char_boundary(start)
        && source.is_char_boundary(end)
        && end - start <= 64
    {
        let token = &source[start..end];
        if !token.chars().any(char::is_control) && !token.chars().all(char::is_whitespace) {
            context = context.with_token(token);
        }
    }
    Some(context)
}

pub(crate) fn command_delimiter_context(
    source_path: &PackagePath,
    file_id: FileId,
    source: &str,
    delimiter: &HumanDelimiterDiagnostic,
) -> Option<CommandDiagnosticDelimiterContext> {
    let mut context = CommandDiagnosticDelimiterContext::new(delimiter.kind.as_str())?;
    if let Some(expected) = &delimiter.expected_closing {
        context = context.with_expected_closing(expected);
    }
    if let Some(actual) = &delimiter.actual_closing {
        context = context.with_actual_closing(actual);
    }
    if let Some(opening_span) = delimiter.opening_span {
        if let Some(opening) = command_source_context(source_path, file_id, source, opening_span) {
            context = context.with_opening_source(opening);
        }
    }
    Some(context)
}
