use std::process::ExitCode;

use npa_cli::args::{parse_cli_args, render_help, CliAction};
use npa_cli::diagnostic::CommandResult;
use npa_cli::package::run_package_command;

fn main() -> ExitCode {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
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

fn render_result(result: &CommandResult, json: bool) {
    if json {
        println!("{}", result.render_json());
    } else if result.exit_code().as_u8() == 0 {
        println!("{}", result.render_human());
    } else {
        eprintln!("{}", result.render_human());
    }
}
