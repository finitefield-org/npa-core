use std::process::ExitCode;

use npa_cli::agent_adapter::{run_agent_adapter_process, AgentAdapterExecutable};

fn main() -> ExitCode {
    run_agent_adapter_process(AgentAdapterExecutable::Cert)
}
