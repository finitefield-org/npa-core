use std::process::ExitCode;

use npa_cli::agent_adapter::{
    is_agent_adapter_invocation, run_agent_adapter_process, AgentAdapterExecutable,
};
use npa_cli::args::{parse_cli_args, render_help, CliAction};
use npa_cli::diagnostic::CommandResult;
use npa_cli::package::run_package_command;

fn main() -> ExitCode {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args == ["--build-provenance-json"] {
        return render_build_provenance(build_provenance_json_v1());
    }
    if args == ["--build-provenance-json-v2"] {
        return render_build_provenance(build_provenance_json_v2());
    }
    if is_agent_adapter_invocation(&args) {
        return run_agent_adapter_process(AgentAdapterExecutable::Npa);
    }
    let wants_json = args.iter().any(|arg| arg == "--json");
    match parse_cli_args(args) {
        Ok(CliAction::Help(topic)) => {
            println!("{}", render_help(topic));
            ExitCode::SUCCESS
        }
        Ok(CliAction::Version) => {
            println!("npa {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Ok(CliAction::Run(command)) => {
            let json = match &command {
                npa_cli::args::CliCommand::Package(command) => command.common_options().json,
            };
            let result = match command {
                npa_cli::args::CliCommand::Package(command) => run_package_command(command),
            };
            render_result(&result, json);
            ExitCode::from(result.exit_code().as_u8())
        }
        Err(error) => {
            let command = error.command.clone().unwrap_or_else(|| "npa".to_owned());
            let result = CommandResult::usage_error(command, ".", &error);
            render_result(&result, wants_json);
            ExitCode::from(result.exit_code().as_u8())
        }
    }
}

fn render_build_provenance(result: Result<String, &'static str>) -> ExitCode {
    match result {
        Ok(json) => {
            println!("{json}");
            ExitCode::SUCCESS
        }
        Err(reason) => {
            eprintln!("npa: build provenance unavailable: {reason}");
            ExitCode::from(2)
        }
    }
}

fn build_provenance_json_v1() -> Result<String, &'static str> {
    let rustc_vv = decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?;
    let rustflags = decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?;
    let features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"npa.cli.build_provenance.v1\",\"source_revision\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"cargo_features\":[{}],\"rustflags\":\"{}\",\"npa_main_source_sha256\":\"{}\"}}",
        json_escape(env!("NPA_CLI_BUILD_SOURCE_REVISION")),
        env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256"),
        json_escape(&rustc_vv),
        json_escape(env!("NPA_CLI_BUILD_CARGO_PROFILE")),
        json_escape(env!("NPA_CLI_BUILD_TARGET")),
        features,
        json_escape(&rustflags),
        env!("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256"),
    ))
}

fn build_provenance_json_v2() -> Result<String, &'static str> {
    let rustc_vv = decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?;
    let rustflags = decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?;
    let features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"npa.cli.build_provenance.v2\",\"source_revision\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"cargo_features\":[{}],\"rustflags\":\"{}\",\"npa_main_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\"}}",
        json_escape(env!("NPA_CLI_BUILD_SOURCE_REVISION")),
        env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256"),
        json_escape(&rustc_vv),
        json_escape(env!("NPA_CLI_BUILD_CARGO_PROFILE")),
        json_escape(env!("NPA_CLI_BUILD_TARGET")),
        features,
        json_escape(&rustflags),
        env!("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256"),
        env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256"),
    ))
}

fn decode_build_hex(encoded: &str) -> Result<String, &'static str> {
    if !encoded.len().is_multiple_of(2) {
        return Err("embedded hexadecimal metadata has odd length");
    }
    let bytes = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok((hex_digit(pair[0])? << 4) | hex_digit(pair[1])?))
        .collect::<Result<Vec<_>, _>>()?;
    String::from_utf8(bytes).map_err(|_| "embedded build metadata is not UTF-8")
}

fn hex_digit(value: u8) -> Result<u8, &'static str> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("embedded build metadata contains invalid hexadecimal"),
    }
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\u{0008}' => escaped.push_str("\\b"),
            '\u{0009}' => escaped.push_str("\\t"),
            '\u{000A}' => escaped.push_str("\\n"),
            '\u{000C}' => escaped.push_str("\\f"),
            '\u{000D}' => escaped.push_str("\\r"),
            '\u{0000}'..='\u{001F}' => {
                use std::fmt::Write as _;
                let _ = write!(escaped, "\\u{:04x}", character as u32);
            }
            _ => escaped.push(character),
        }
    }
    escaped
}

fn render_result(result: &CommandResult, json: bool) {
    if json {
        println!("{}", result.render_json());
    } else if result.exit_code().as_u8() == 0 {
        println!("{}", result.render_human());
    } else {
        eprintln!("{}", result.render_human());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_provenance_json_escape_covers_every_control_character() {
        let controls = (0_u8..=0x1f).map(char::from).collect::<String>();
        let escaped = json_escape(&controls);
        for byte in 0_u8..=0x1f {
            let expected = match byte {
                8 => "\\b".to_owned(),
                9 => "\\t".to_owned(),
                10 => "\\n".to_owned(),
                12 => "\\f".to_owned(),
                13 => "\\r".to_owned(),
                _ => format!("\\u{byte:04x}"),
            };
            assert!(
                escaped.contains(&expected),
                "missing escape for {byte:#04x}"
            );
        }
        assert!(!escaped.contains('\u{001f}'));
    }

    #[test]
    fn embedded_build_hex_decode_is_fallible_and_exact() {
        assert_eq!(decode_build_hex("6100621f").unwrap(), "a\0b\u{001f}");
        assert!(decode_build_hex("0").is_err());
        assert!(decode_build_hex("gg").is_err());
        assert!(decode_build_hex("ff").is_err());
        assert!(build_provenance_json_v1().is_ok());
        assert!(build_provenance_json_v2().is_ok());
    }
}
