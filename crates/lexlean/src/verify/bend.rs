//! Bend verification (SPEC.md §22.13): the pinned Bend checks every
//! generated module, and the proved BendTT kernel rechecks the whole
//! program.
//!
//! Bend is located on `PATH` and must report exactly the pinned version;
//! its executable digest is recorded. Every Bend child runs with
//! `BEND_NO_TELEMETRY=1`: an installed Bend otherwise asks its website once a
//! day for a newer release, and verification makes no hidden network
//! request (I15).

use camino::{Utf8Path, Utf8PathBuf};

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::config::Limits;
use crate::diagnostic::Diagnostic;
use crate::verify::child::{resolve_on_path, run, ChildHome, ChildRecord, ChildSpec, Normalizer};

/// The exact output of a module Bend accepts under `--check-only`.
pub const CHECK_SUCCESS: &str = "ALL PROOFS CHECK\nUse --verdict for mathematical validity.\n";

/// The exact output of a program the BendTT kernel accepts under
/// `--verdict`.
pub const VERDICT_SUCCESS: &str = "ALL PROOFS CHECK\n";

/// The build-relative directory of the verification-generated root that
/// imports every generated module for the kernel recheck.
pub const VERDICT_DIR: &str = "bend-verdict";

/// The preflighted Bend executable.
#[derive(Debug, Clone)]
pub struct Bend {
    /// The absolute executable path.
    pub path: Utf8PathBuf,
    /// Its directory, prepended to the children's `PATH`.
    pub bin: Utf8PathBuf,
    /// SHA-256 of the executable bytes.
    pub sha256: Sha256Digest,
    /// The recorded version output.
    pub version_output: String,
    /// SHA-256 of the BendTT kernel that accepted the program, once the
    /// kernel recheck has.
    pub kernel_sha256: Option<Sha256Digest>,
}

fn spec<'a>(
    bend: &'a Bend,
    module: Option<String>,
    argv: Vec<String>,
    cwd: &'a Utf8Path,
) -> ChildSpec<'a> {
    ChildSpec {
        tool: "bend",
        module,
        program: &bend.path,
        executable_sha256: bend.sha256,
        argv,
        cwd,
        extra_env: vec![("BEND_NO_TELEMETRY".to_owned(), "1".to_owned())],
        home: ChildHome::Toolchain {
            toolchain_bin: &bend.bin,
        },
    }
}

/// Locate the pinned Bend and require its exact version (`LLV7019`).
///
/// # Errors
///
/// `LLV7019` when no `bend` is on `PATH`, it cannot be read, or it reports
/// another version.
pub fn preflight(limits: &Limits) -> Result<Bend, Diagnostic> {
    let mismatch = |message: String| Diagnostic::new(code!("LLV7019"), message);
    let path = resolve_on_path("bend").map_err(|_| {
        mismatch(format!(
            "no `bend` is on PATH; language 2.0 verifies with {}",
            crate::BEND_TOOLCHAIN
        ))
    })?;
    let bytes = std::fs::read(path.as_std_path())
        .map_err(|io_error| mismatch(format!("{path}: {io_error}")))?;
    let bin = path
        .parent()
        .map(Utf8Path::to_path_buf)
        .ok_or_else(|| mismatch(format!("{path} has no directory")))?;
    let mut bend = Bend {
        path,
        bin,
        sha256: Sha256Digest::of(&bytes),
        version_output: String::new(),
        kernel_sha256: None,
    };
    let cwd = bend.bin.clone();
    let record = run(
        &spec(&bend, None, vec!["version".to_owned()], &cwd),
        limits,
        &Normalizer::default(),
    )?;
    let version = record.stdout.trim_end().to_owned();
    if record.exit_code != 0 || version != crate::BEND_VERSION_LINE {
        return Err(mismatch(format!(
            "`{}` reports `{version}`, not the pinned `{}`",
            bend.path,
            crate::BEND_VERSION_LINE
        )));
    }
    bend.version_output = version;
    Ok(bend)
}

/// Check one staged module with `--check-only` from its own directory, so
/// its relative imports resolve. Success is exit 0 and exactly
/// [`CHECK_SUCCESS`] with nothing on stderr; anything else is returned as
/// the refusal's record for remapping.
///
/// # Errors
///
/// A child failure (timeout, output bound, start failure).
pub fn check(
    bend: &Bend,
    module: &str,
    file: &Utf8Path,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<(ChildRecord, bool), Diagnostic> {
    let cwd = file
        .parent()
        .map(Utf8Path::to_path_buf)
        .unwrap_or_else(|| Utf8PathBuf::from("."));
    let name = file.file_name().unwrap_or_default().to_owned();
    let record = run(
        &spec(
            bend,
            Some(module.to_owned()),
            vec![name, "--check-only".to_owned()],
            &cwd,
        ),
        limits,
        normalizer,
    )?;
    let accepted =
        record.exit_code == 0 && record.stdout == CHECK_SUCCESS && record.stderr.trim().is_empty();
    Ok((record, accepted))
}

/// The kernel-recheck root: one import per generated module, in module
/// order, under positional aliases, and nothing else.
#[must_use]
pub fn verdict_root(module_paths: &[String]) -> String {
    let mut out = String::from("import Base\n");
    for (index, path) in module_paths.iter().enumerate() {
        out.push_str(&format!("import ../{path} as M{index}\n"));
    }
    out
}

/// Recheck the staged program with the proved BendTT kernel through the
/// verification-generated root. Success is exit 0 and exactly
/// [`VERDICT_SUCCESS`] with nothing on stderr.
///
/// # Errors
///
/// A child failure (timeout, output bound, start failure).
pub fn verdict(
    bend: &Bend,
    root_dir: &Utf8Path,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<(ChildRecord, bool), Diagnostic> {
    let record = run(
        &spec(
            bend,
            None,
            vec!["Root.bend".to_owned(), "--verdict".to_owned()],
            root_dir,
        ),
        limits,
        normalizer,
    )?;
    let accepted = record.exit_code == 0
        && record.stdout == VERDICT_SUCCESS
        && record.stderr.trim().is_empty();
    Ok((record, accepted))
}

/// The SHA-256 of the BendTT kernel the pinned Bend ran: the one it keeps,
/// or a prebuilt one placed there, at the pinned key under the home the
/// Bend children share (§22.13). The children never receive `$BENDTT`
/// (§25.4), so this is the only kernel a recheck can have run.
///
/// # Errors
///
/// `LLV7019` when no kernel can be read there.
pub fn kernel_digest() -> Result<Sha256Digest, Diagnostic> {
    let home = std::env::var_os("HOME").unwrap_or_else(|| "/".into());
    let path = std::path::Path::new(&home)
        .join(".bend")
        .join("bendtt")
        .join(crate::BENDTT_KERNEL_KEY)
        .join("bendtt");
    std::fs::read(&path)
        .map(|bytes| Sha256Digest::of(&bytes))
        .map_err(|io_error| {
            Diagnostic::new(
                code!("LLV7019"),
                format!(
                    "the BendTT kernel recheck accepted, but no kernel is at `~/.bend/bendtt/{}/bendtt` to record: {io_error}",
                    crate::BENDTT_KERNEL_KEY
                ),
            )
        })
}

/// The generated line Bend's refusal points at: the `N>|` marker of its
/// excerpt.
#[must_use]
pub fn refusal_line(output: &str) -> Option<usize> {
    output.lines().find_map(|line| {
        let (number, _) = line.split_once(">|")?;
        number.trim().parse().ok()
    })
}

/// The byte offset of the first non-blank byte of one-based `line` of
/// `text`.
#[must_use]
pub fn line_offset(text: &str, line: usize) -> Option<usize> {
    let mut offset = 0usize;
    for (index, content) in text.split_inclusive('\n').enumerate() {
        if index + 1 == line {
            let indent = content.len() - content.trim_start().len();
            return Some(offset + indent);
        }
        offset += content.len();
    }
    None
}
