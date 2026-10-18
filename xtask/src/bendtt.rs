//! `cargo xtask bendtt-kernel`: export the pinned Bend's compiled BendTT
//! kernel, so a host without Lean can run the kernel recheck (SPEC.md
//! §22.13).
//!
//! Bend compiles its kernel from `bendtt.lean` with Lean v4.34.0 on first
//! use and keeps it at `~/.bend/bendtt/<key>/bendtt`. This task builds it
//! there through Bend's own recipe, so the exported binary is the one Bend
//! would build, and copies it out with its digest. A host of the same
//! platform that installs it at the same path needs no Lean for the recheck.

use std::path::{Path, PathBuf};
use std::process::Command;

use lexlean::artifact::content_id::Sha256Digest;

use crate::Fail;

/// The Lean release Bend compiles its kernel with: the prefix of the key.
const KERNEL_LEAN_VERSION: &str = "4.34.0";

fn bend(arguments: &[&str], cwd: &Path) -> Result<std::process::Output, Fail> {
    Command::new("bend")
        .args(arguments)
        .current_dir(cwd)
        .env("BEND_NO_TELEMETRY", "1")
        .output()
        .map_err(|error| format!("`bend` on PATH: {error}").into())
}

/// The `bendtt.lean` the `bend` on `PATH` compiles.
fn kernel_source() -> Result<PathBuf, Fail> {
    let path = std::env::var_os("PATH").unwrap_or_default();
    let executable = std::env::split_paths(&path)
        .map(|dir| dir.join("bend"))
        .find(|candidate| candidate.is_file())
        .ok_or("no `bend` on PATH")?;
    let resolved = std::fs::canonicalize(&executable)?;
    let bin = resolved.parent().ok_or("`bend` has no directory")?;
    Ok(bin.join("..").join("bend2").join("bendtt.lean"))
}

pub fn export(root: &Path, arguments: &[String]) -> Result<(), Fail> {
    let out = match arguments {
        [] => root.join("target").join("bendtt"),
        [flag, dir] if flag == "--out" => PathBuf::from(dir),
        _ => return Err("usage: cargo xtask bendtt-kernel [--out DIR]".into()),
    };
    let version = bend(&["version"], root)?;
    let version = String::from_utf8_lossy(&version.stdout)
        .trim_end()
        .to_owned();
    if version != lexlean::BEND_VERSION_LINE {
        return Err(format!(
            "`bend version` prints `{version}`, not the pinned `{}`",
            lexlean::BEND_VERSION_LINE
        )
        .into());
    }
    let home = PathBuf::from(std::env::var_os("HOME").ok_or("HOME is not set")?);
    // Bend derives the key from its kernel source, which it reads from
    // `../bend2` beside its resolved executable; a key other than the pinned
    // one is another kernel than the one verification records.
    let source_path = kernel_source()?;
    let source = std::fs::read(&source_path)
        .map_err(|error| format!("{}: {error}", source_path.display()))?;
    let keyed = [KERNEL_LEAN_VERSION.as_bytes(), b"\0", &source].concat();
    let key = Sha256Digest::of(&keyed).to_hex()[..16].to_owned();
    if key != lexlean::BENDTT_KERNEL_KEY {
        return Err(format!(
            "the installed Bend's kernel key is `{key}`, not the pinned `{}`",
            lexlean::BENDTT_KERNEL_KEY
        )
        .into());
    }
    let kernel = home.join(".bend/bendtt").join(&key).join("bendtt");
    if !kernel.exists() {
        let probe = tempfile::Builder::new()
            .prefix("bendtt-kernel-")
            .tempdir()?;
        std::fs::write(probe.path().join("P.bend"), "import Base\n")?;
        let built = bend(&["P.bend", "--verdict"], probe.path())?;
        if !kernel.exists() {
            return Err(format!(
                "Bend did not build its kernel: {}{}",
                String::from_utf8_lossy(&built.stdout),
                String::from_utf8_lossy(&built.stderr)
            )
            .into());
        }
    }
    let bytes = std::fs::read(&kernel)?;
    let digest = Sha256Digest::of(&bytes).to_hex();
    let name = format!(
        "bendtt-{key}-{}-{}",
        std::env::consts::OS,
        std::env::consts::ARCH
    );
    std::fs::create_dir_all(&out)?;
    std::fs::write(out.join(&name), &bytes)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(out.join(&name), std::fs::Permissions::from_mode(0o755))?;
    }
    std::fs::write(
        out.join(format!("{name}.sha256")),
        format!("{digest}  {name}\n"),
    )?;
    println!(
        "bendtt-kernel: wrote {} ({digest})",
        out.join(&name).display()
    );
    println!(
        "bendtt-kernel: install on a {}-{} host as ~/.bend/bendtt/{key}/bendtt",
        std::env::consts::OS,
        std::env::consts::ARCH
    );
    Ok(())
}
