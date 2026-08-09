use std::env;
use std::fs::File;
use std::io;
use std::mem::MaybeUninit;
use std::process::{Command, Stdio};
use std::time::Instant;

fn main() {
    if let Err(error) = run() {
        eprintln!("measure-process: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = env::args().skip(1);
    let output_flag = arguments.next();
    let output_path = arguments.next();
    let stderr_flag = arguments.next();
    let stderr_path = arguments.next();
    let separator = arguments.next();
    let executable = arguments.next();
    let command_arguments = arguments.collect::<Vec<_>>();
    if output_flag.as_deref() != Some("--output")
        || stderr_flag.as_deref() != Some("--stderr")
        || separator.as_deref() != Some("--")
        || executable.is_none()
    {
        return Err(
            "usage: measure_process --output PATH --stderr PATH -- COMMAND [ARG ...]".to_owned(),
        );
    }

    let stdout = File::create(output_path.expect("validated output path"))
        .map_err(|error| format!("create output: {error}"))?;
    let stderr = File::create(stderr_path.expect("validated stderr path"))
        .map_err(|error| format!("create stderr: {error}"))?;
    let started = Instant::now();
    let mut child = Command::new(executable.expect("validated executable"))
        .args(command_arguments)
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .map_err(|error| format!("spawn measured command: {error}"))?;
    let child_pid = i32::try_from(child.id()).map_err(|_| "child PID exceeds pid_t".to_owned())?;
    let (wait_status, usage) =
        wait_for_child(child_pid).map_err(|error| format!("wait for measured command: {error}"))?;
    let elapsed = started.elapsed().as_secs_f64();
    let _ = child.try_wait();

    let exit_code = decoded_exit_code(wait_status);
    let peak_rss_kib = peak_rss_kib(&usage)?;
    println!("{elapsed:.9}\t{peak_rss_kib}\t{exit_code}");
    Ok(())
}

fn wait_for_child(pid: libc::pid_t) -> io::Result<(libc::c_int, libc::rusage)> {
    let mut wait_status = 0;
    let mut usage = MaybeUninit::<libc::rusage>::zeroed();
    loop {
        // SAFETY: `wait_status` and `usage` are valid writable objects, `pid`
        // is the child just spawned above, and no other code waits for it.
        let waited = unsafe { libc::wait4(pid, &mut wait_status, 0, usage.as_mut_ptr()) };
        if waited == pid {
            // SAFETY: a successful wait4 call initializes the complete rusage.
            return Ok((wait_status, unsafe { usage.assume_init() }));
        }
        if waited == -1 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
    }
}

fn decoded_exit_code(wait_status: libc::c_int) -> i32 {
    if libc::WIFEXITED(wait_status) {
        libc::WEXITSTATUS(wait_status)
    } else if libc::WIFSIGNALED(wait_status) {
        128 + libc::WTERMSIG(wait_status)
    } else {
        255
    }
}

fn peak_rss_kib(usage: &libc::rusage) -> Result<u64, String> {
    let peak = u64::try_from(usage.ru_maxrss).map_err(|_| "negative peak RSS".to_owned())?;
    #[cfg(target_os = "macos")]
    {
        Ok(peak.saturating_add(1023) / 1024)
    }
    #[cfg(not(target_os = "macos"))]
    {
        Ok(peak)
    }
}
