use rustc_version::Version;

fn main() {
    let version = rustc_version::version().unwrap();

    if version >= Version::parse("1.60.0").unwrap() {
        // `cfg_target_has_atomic` feature (`cfg(target_has_atomic = ...)`)
        // Stabilized by <https://github.com/rust-lang/rust/pull/93824>
        println!("cargo:rustc-cfg=compiler_has_cfg_target_has_atomic");
    }
}
