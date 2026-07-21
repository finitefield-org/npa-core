use std::{env, process::Command};

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");

    let profile = env::var("PROFILE").expect("Cargo supplies PROFILE to build scripts");
    let cargo_profile = match profile.as_str() {
        "debug" => "dev",
        profile => profile,
    };
    println!("cargo:rustc-env=NPA_BUILD_CARGO_PROFILE={cargo_profile}");

    let mut features = env::vars()
        .filter_map(|(name, _)| name.strip_prefix("CARGO_FEATURE_").map(str::to_owned))
        .map(|name| name.to_ascii_lowercase())
        .collect::<Vec<_>>();
    features.sort();
    features.dedup();
    println!(
        "cargo:rustc-env=NPA_BUILD_CARGO_FEATURES={}",
        features.join(",")
    );

    let rustc = env::var_os("RUSTC").expect("Cargo supplies RUSTC to build scripts");
    let output = Command::new(rustc)
        .arg("-Vv")
        .output()
        .expect("build compiler must support rustc -Vv");
    assert!(output.status.success(), "build compiler rustc -Vv failed");
    let rustc_vv = String::from_utf8(output.stdout).expect("rustc -Vv output is UTF-8");
    println!(
        "cargo:rustc-env=NPA_BUILD_RUSTC_VV_HEX={}",
        hex(rustc_vv.trim_end().as_bytes())
    );
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}
