//! The Bend half of the `verification` suite: VR-24..VR-29 (SPEC.md
//! §22.13). The Bend stages run before any Lean process, and a project Bend
//! verifies alone runs none, so each case reaches its stage on every host; a
//! case that needs the pinned Bend (or, for the kernel recheck, the Lean that
//! builds the kernel) gates that half.

use lexlean::{Selection, VerifyRequest};

use crate::support::{self, P};

/// A directory holding one executable `bend` script.
fn fake_bend(script: &str) -> tempfile::TempDir {
    let dir = tempfile::Builder::new()
        .prefix("lexlean-fake-bend-")
        .tempdir()
        .expect("tempdir");
    let path = dir.path().join("bend");
    std::fs::write(&path, script).expect("fake bend");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    }
    dir
}

/// `PATH` with `dir` first. Read under the shared lock: a case beside this
/// one may hold a stand-in `bend` first on `PATH` (VR-29).
fn path_with(dir: &std::path::Path) -> String {
    let existing = {
        let _environment = support::env_shared();
        std::env::var("PATH").unwrap_or_default()
    };
    format!("{}:{existing}", dir.display())
}

/// Verify a project with `PATH` set, returning the error.
fn verify_err_with_path(project: &P, path: &str) -> lexlean::LexLeanError {
    support::with_env(&[("PATH", Some(path))], || {
        project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .err()
            .expect("verification fails")
    })
}

/// A Bend that accepts every check and the kernel recheck: what the Lean-free
/// pipeline does around Bend's answers, on a host without the pinned Bend.
fn accepting_bend() -> tempfile::TempDir {
    fake_bend(
        "#!/bin/sh\ncase \"$*\" in\n  version) echo 'bend 2.0.37' ;;\n  *--check-only*) printf 'ALL PROOFS CHECK\\nUse --verdict for mathematical validity.\\n' ;;\n  *--verdict*) printf 'ALL PROOFS CHECK\\n' ;;\nesac\n",
    )
}

/// A home whose `.bend` holds a stand-in BendTT kernel at the pinned key:
/// what an accepting stand-in Bend's recheck is recorded as having run
/// (§22.13).
fn stand_in_home() -> tempfile::TempDir {
    let home = tempfile::Builder::new()
        .prefix("lexlean-kernel-home-")
        .tempdir()
        .expect("tempdir");
    let kernel = home
        .path()
        .join(".bend/bendtt")
        .join(lexlean::BENDTT_KERNEL_KEY);
    std::fs::create_dir_all(&kernel).expect("kernel directory");
    std::fs::write(kernel.join("bendtt"), b"a stand-in BendTT kernel\n").expect("kernel");
    home
}

/// Verify a project with `PATH` set, returning the published attestation.
fn verified_attestation(project: &P, path: &str) -> (serde_json::Value, camino::Utf8PathBuf) {
    verified_attestation_with(project, &[("PATH", Some(path))])
}

/// Verify a project with environment overrides, returning the published
/// attestation.
fn verified_attestation_with(
    project: &P,
    environment: &[(&str, Option<&str>)],
) -> (serde_json::Value, camino::Utf8PathBuf) {
    let verified = support::with_env(environment, || {
        project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .unwrap_or_else(|error| panic!("the project verifies: {error}"))
    });
    let path = verified.root.join("attestation.json");
    let attestation =
        serde_json::from_slice(&std::fs::read(path.as_std_path()).expect("attestation"))
            .expect("JSON");
    (attestation, verified.root)
}

/// Give a Lean-free project the Lean workspace a production root needs
/// (§10.4, §10.6): the configuration fields and the Lake files `init` writes.
fn carry_lean(project: &P) {
    let config = project.read_raw("lexlean.toml").replacen(
        "bend_toolchain = ",
        &format!(
            "lean_workspace = \".\"\nlean_toolchain = \"{}\"\nbend_toolchain = ",
            lexlean::LEAN_TOOLCHAIN
        ),
        1,
    );
    project.write("lexlean.toml", &config);
    project.write("lean-toolchain", &format!("{}\n", lexlean::LEAN_TOOLCHAIN));
    project.write(
        "lakefile.toml",
        "name = \"language_twelve_host\"\nversion = \"0.1.0\"\n",
    );
    project.write(
        "lake-manifest.json",
        "{\"version\": \"1.2.0\",\n \"packagesDir\": \".lake/packages\",\n \"packages\": [],\n \"name\": \"language_twelve_host\",\n \"lakeDir\": \".lake\",\n \"fixedToolchain\": false}\n",
    );
}

/// The language-2.2 semantic example with a production root, and the Lean
/// the root needs: the one thing that keeps a project whose modules all
/// lower to Bend on the Lean stages.
fn rooted_semantic() -> P {
    let project = P::copy_example("bend-semantic");
    carry_lean(&project);
    let main = project.read_raw("src/Main.lex.tex");
    let rooted = main.replacen(
        "  body: (let doubled : Nat := (n + n); (doubled + 1))\n}",
        "  body: (let doubled : Nat := (n + n); (doubled + 1)),\n  executable: true,\n  production: {effects: [overflow], targets: [rust-std]}\n}",
        1,
    );
    assert_ne!(rooted, main, "`doubledSuccessor` becomes a production root");
    project.write("src/Main.lex.tex", &rooted);
    project.relock();
    project
}

/// A Bend-only attestation: schema v3, the Bend toolchain, and nothing
/// that only a Lean run could have produced.
fn assert_bend_only(attestation: &serde_json::Value, root: &camino::Utf8Path, what: &str) {
    support::assert_json_file_schema("attestation-v3", &root.join("attestation.json"));
    assert_eq!(attestation["spec"], "lexlean/attestation/3", "{what}");
    assert_eq!(
        attestation["bend"]["version_output"],
        lexlean::BEND_VERSION_LINE,
        "{what}"
    );
    for field in ["toolchain", "oleans", "lake_workspace"] {
        assert!(attestation.get(field).is_none(), "{what} records `{field}`");
    }
    let processes = attestation["processes"].as_array().expect("processes");
    assert!(!processes.is_empty(), "{what} records its Bend processes");
    assert!(
        processes.iter().all(|record| record["tool"] == "bend"),
        "{what} ran only Bend: {:?}",
        processes
            .iter()
            .map(|record| &record["tool"])
            .collect::<Vec<_>>()
    );
    for directory in [
        "oleans",
        "probe",
        "audit",
        "process/lean",
        "process/leanchecker",
    ] {
        assert!(
            !root.join(directory).as_std_path().exists(),
            "{what} published `{directory}`"
        );
    }
}

/// The directory of the pinned Bend, when installed, found under the shared
/// lock, as [`support::bend_backed`] finds it, so never a case's stand-in.
fn bend_dir() -> Option<std::path::PathBuf> {
    let _environment = support::env_shared();
    support::bend_program().and_then(|program| program.parent().map(std::path::Path::to_path_buf))
}

/// Does `bend --verdict` work here: the pinned Bend and the Lean that
/// builds its kernel? On the normative host it must (§22.13).
fn verdict_available(id: &str) -> bool {
    let Some(dir) = bend_dir() else {
        return false;
    };
    let probe = tempfile::Builder::new()
        .prefix("lexlean-verdict-probe-")
        .tempdir()
        .expect("tempdir");
    std::fs::write(probe.path().join("P.bend"), "import Base\n").expect("probe");
    let output = std::process::Command::new(dir.join("bend"))
        .args(["P.bend", "--verdict"])
        .current_dir(probe.path())
        .env("BEND_NO_TELEMETRY", "1")
        .output()
        .expect("bend runs");
    let available = String::from_utf8_lossy(&output.stdout) == "ALL PROOFS CHECK\n";
    if !available {
        assert!(
            !support::normative_host(),
            "{id}: the normative host must build the BendTT kernel (Lean leanprover/lean4:v4.34.0, §22.13)"
        );
        eprintln!(
            "{id}: this host cannot build the BendTT kernel; the kernel half did not run (§22.13)"
        );
    }
    available
}

/// The Lake files a Lean workspace pins (§10.4).
const LAKE_FILES: [&str; 4] = [
    "lean-toolchain",
    "lakefile.toml",
    "lakefile.lean",
    "lake-manifest.json",
];

/// A copy of a committed Bend example with no Lean workspace, toolchain, or
/// Lake file, relocked.
fn lean_free_copy(example: &str) -> P {
    let project = P::copy_example(example);
    let config: String = project
        .read_raw("lexlean.toml")
        .lines()
        .filter(|line| {
            !line.starts_with("lean_workspace = ") && !line.starts_with("lean_toolchain = ")
        })
        .map(|line| format!("{line}\n"))
        .collect();
    project.write("lexlean.toml", &config);
    for file in lean_workspace_files(&project.root) {
        std::fs::remove_file(project.root.join(file).as_std_path()).expect("remove a Lean file");
    }
    project.relock();
    project
}

/// A file of a rendered build, as text.
fn build_text(build: &lexlean::api::RenderedBuild, path: &str) -> Option<String> {
    build
        .files
        .iter()
        .find(|(candidate, _)| candidate == path)
        .map(|(_, bytes)| String::from_utf8_lossy(bytes).into_owned())
}

/// The Lake files and Lean host modules at the root of a project.
fn lean_workspace_files(root: &camino::Utf8Path) -> Vec<String> {
    std::fs::read_dir(root.as_std_path())
        .expect("project root")
        .filter_map(Result::ok)
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .filter(|name| LAKE_FILES.contains(&name.as_str()) || name.ends_with(".lean"))
        .collect()
}

/// Whether a committed example's sources declare a production root.
fn declares_production_root(example: &camino::Utf8Path) -> bool {
    walkdir::WalkDir::new(example.join("src").as_std_path())
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().to_string_lossy().ends_with(".lex.tex"))
        .any(|entry| {
            std::fs::read_to_string(entry.path()).is_ok_and(|text| text.contains("production: {"))
        })
}

/// BN-24 (§10.6): a Bend project with no Lean configuration carries no Lean.
pub(crate) fn lean_free(id: &str) {
    for (example, module) in [
        ("bend-nat-add-zero", "LexLeanExample/Main"),
        ("bend-semantic", "LanguageTwelve/Main"),
    ] {
        let project = lean_free_copy(example);
        let lock = project.read_raw("lexlean.lock");
        assert!(!lock.contains("lean_toolchain"), "{example}: {lock}");
        assert!(!lock.contains("workspace_file"), "{example}: {lock}");
        let build = support::rendered(&project);
        let lean: Vec<&String> = build
            .files
            .iter()
            .map(|(path, _)| path)
            .filter(|path| path.ends_with(".lean"))
            .collect();
        assert!(lean.is_empty(), "{example} publishes Lean: {lean:?}");
        assert!(
            build_text(&build, &format!("modules/{module}.bend")).is_some(),
            "{example} publishes its Bend"
        );
        let manifest = build_text(&build, "manifest.json").expect("manifest");
        assert!(
            !manifest.contains("lean_toolchain"),
            "{example}: {manifest}"
        );
        let coverage =
            build_text(&build, &format!("coverage/{module}.coverage.json")).expect("coverage");
        let coverage: serde_json::Value = serde_json::from_str(&coverage).expect("JSON");
        assert!(
            coverage.get("lean").is_none(),
            "{example} records Lean coverage"
        );
        let map = build_text(&build, &format!("maps/{module}.map.json")).expect("map");
        assert!(
            !map.contains("\"kind\":\"lean\""),
            "{example} maps Lean: {map}"
        );
        // The pinned Bend where it can recheck in its kernel, a stand-in
        // that accepts where it cannot: the routing is what is under test.
        let (attestation, root) = match bend_dir().filter(|_| verdict_available(id)) {
            Some(dir) => verified_attestation(&project, &path_with(&dir)),
            None if support::posix_shell_backed(id) => {
                let stand_in = accepting_bend();
                let home = stand_in_home();
                let path = path_with(stand_in.path());
                let home = home.path().display().to_string();
                verified_attestation_with(
                    &project,
                    &[("PATH", Some(path.as_str())), ("HOME", Some(home.as_str()))],
                )
            }
            None => continue,
        };
        assert_bend_only(&attestation, &root, example);
    }
    // Half a Lean configuration names a workspace with no toolchain, or the
    // reverse.
    for kept in [
        "lean_workspace = \".\"\n",
        "lean_toolchain = \"leanprover/lean4:v4.32.1\"\n",
    ] {
        let project = lean_free_copy("bend-semantic");
        let config = project.read_raw("lexlean.toml").replacen(
            "bend_toolchain = ",
            &format!("{kept}bend_toolchain = "),
            1,
        );
        project.write("lexlean.toml", &config);
        let error = lexlean::project::Project::load(&project.root.join("lexlean.toml"))
            .err()
            .unwrap_or_else(|| panic!("`{}` alone is refused", kept.trim_end()));
        support::expect_code(&error, "LLC0101");
    }
    // A production root needs the Lean that extracts and certifies it.
    let project = lean_free_copy("bend-semantic");
    project.write(
        "src/Main.lex.tex",
        &rooted_semantic().read_raw("src/Main.lex.tex"),
    );
    let error = project.check_err();
    support::expect_code(&error, "LLC0101");
    assert!(error.to_string().contains("doubledSuccessor"), "{error}");
    // Every committed Bend example a production root does not hold to Lean
    // is Lean-free.
    let mut lean_free = 0usize;
    for entry in std::fs::read_dir(support::repo_root().join("examples").as_std_path())
        .expect("examples")
        .filter_map(Result::ok)
    {
        let example = camino::Utf8PathBuf::from_path_buf(entry.path()).expect("utf8");
        let Ok(config) = std::fs::read_to_string(example.join("lexlean.toml").as_std_path()) else {
            continue;
        };
        if !(config.contains("language = \"2.0\"") || config.contains("language = \"2.2\"")) {
            continue;
        }
        if declares_production_root(&example) {
            assert!(
                config.contains("lean_toolchain = "),
                "{example} keeps Lean for its roots"
            );
            continue;
        }
        assert!(
            !config.contains("lean_toolchain = "),
            "{example} names a Lean toolchain"
        );
        let lean = lean_workspace_files(&example);
        assert!(lean.is_empty(), "{example} holds {lean:?}");
        lean_free += 1;
    }
    assert!(lean_free > 0, "the Bend examples include Lean-free ones");
}

pub(crate) fn run(id: &str) {
    match id {
        // §22.13 stage 2: exactly the pinned Bend, its version and digest.
        "VR-24" => {
            let project = P::copy_example("bend-nat-add-zero");
            let empty = tempfile::Builder::new()
                .prefix("lexlean-no-bend-")
                .tempdir()
                .expect("tempdir");
            let error = verify_err_with_path(&project, &empty.path().display().to_string());
            support::expect_code(&error, "LLV7019");
            if support::posix_shell_backed(id) {
                let other = fake_bend("#!/bin/sh\necho 'bend 2.0.36'\n");
                let error = verify_err_with_path(&project, &path_with(other.path()));
                support::expect_code(&error, "LLV7019");
                assert!(error.to_string().contains("bend 2.0.36"), "{error}");
                // A kernel the pinned Bend cannot build is the
                // environment's failure.
                let kernel = fake_bend(
                    "#!/bin/sh\ncase \"$*\" in\n  version) echo 'bend 2.0.37' ;;\n  *--check-only*) printf 'ALL PROOFS CHECK\\nUse --verdict for mathematical validity.\\n' ;;\n  *--verdict*) echo 'Error: BendTT infrastructure: the kernel did not build'; exit 1 ;;\nesac\n",
                );
                let error = verify_err_with_path(&project, &path_with(kernel.path()));
                support::expect_code(&error, "LLV7019");
            }
            if support::bend_backed(id) {
                let dir = bend_dir().expect("the pinned Bend");
                let limits = lexlean::project::Project::load(&project.root.join("lexlean.toml"))
                    .expect("project")
                    .config
                    .limits;
                let tool = support::with_env(&[("PATH", Some(&path_with(&dir)))], || {
                    lexlean::verify::bend::preflight(&limits).expect("the pinned Bend preflights")
                });
                assert_eq!(tool.version_output, lexlean::BEND_VERSION_LINE);
                let bytes = std::fs::read(tool.path.as_std_path()).expect("bend");
                assert_eq!(
                    tool.sha256,
                    lexlean::Sha256Digest::of(&bytes),
                    "the recorded digest"
                );
            }
        }
        // §22.13 stage 3: every module checked before any Lean process; a
        // refusal remapped to its source.
        "VR-25" => {
            let project = P::copy_example("propositional-logic");
            project.to_language_2_0();
            if support::posix_shell_backed(id) {
                // A refusal on a known generated line maps to the source.
                let refusing = fake_bend(
                    "#!/bin/sh\ncase \"$*\" in\n  version) echo 'bend 2.0.37' ;;\n  *) printf 'SOME PROOFS FAIL\\nError:\\n- expected : llh0\\n- observed : llh0 (consumed more than once)\\nLocation: and_comm.c0\\n5>|   match llh0:\\n' ;;\nesac\n",
                );
                let error = verify_err_with_path(&project, &path_with(refusing.path()));
                support::expect_code(&error, "LLV7020");
                let diagnostic = error
                    .diagnostics
                    .iter()
                    .find(|diagnostic| diagnostic.code.as_str() == "LLV7020")
                    .expect("the refusal");
                let span = diagnostic.primary.as_ref().expect("a remapped source span");
                assert_eq!(
                    span.path, "src/Main.lex.tex",
                    "the refusal points at the source"
                );
                assert!(
                    diagnostic.notes.iter().any(|note| note.message
                        == "generated location: modules/PropositionalLogic/Main.bend:5"),
                    "{:?}",
                    diagnostic.notes
                );
            }
            if support::bend_backed(id) {
                let dir = bend_dir().expect("the pinned Bend");
                let error = verify_err_with_path(&project, &path_with(&dir));
                support::expect_code(&error, "LLV7020");
                assert!(
                    error.to_string().contains("consumed more than once"),
                    "{error}"
                );
                assert!(error.to_string().contains("de_morgan"), "{error}");
            }
        }
        // §22.13 stage 4: the kernel recheck's exact verdict.
        "VR-26" => {
            let root = lexlean::verify::bend::verdict_root(&[
                "modules/A/Main.bend".to_owned(),
                "modules/A/B.bend".to_owned(),
            ]);
            assert_eq!(
                root,
                "import Base\nimport ../modules/A/Main.bend as M0\nimport ../modules/A/B.bend as M1\n"
            );
            let project = P::copy_example("bend-nat-add-zero");
            if support::posix_shell_backed(id) {
                let mismatch = fake_bend(
                    "#!/bin/sh\ncase \"$*\" in\n  version) echo 'bend 2.0.37' ;;\n  *--check-only*) printf 'ALL PROOFS CHECK\\nUse --verdict for mathematical validity.\\n' ;;\n  *--verdict*) printf 'SOME PROOFS FAIL\\nSorry - this is a mismatch\\n' ;;\nesac\n",
                );
                let error = verify_err_with_path(&project, &path_with(mismatch.path()));
                support::expect_code(&error, "LLV7021");
            }
            if support::bend_backed(id) && verdict_available(id) {
                // The real kernel accepts the generated program: the run
                // passes the Bend stages and proceeds to the Lean ones.
                let dir = bend_dir().expect("the pinned Bend");
                let build = support::rendered(&project);
                let staged = support::materialize(&build);
                let verdict_dir = staged.path().join(lexlean::verify::bend::VERDICT_DIR);
                std::fs::create_dir_all(&verdict_dir).expect("verdict dir");
                std::fs::write(
                    verdict_dir.join("Root.bend"),
                    lexlean::verify::bend::verdict_root(&[
                        "modules/LexLeanExample/Main.bend".to_owned()
                    ]),
                )
                .expect("root");
                let output = std::process::Command::new(dir.join("bend"))
                    .args(["Root.bend", "--verdict"])
                    .current_dir(&verdict_dir)
                    .env("BEND_NO_TELEMETRY", "1")
                    .output()
                    .expect("bend runs");
                assert_eq!(
                    String::from_utf8_lossy(&output.stdout),
                    lexlean::verify::bend::VERDICT_SUCCESS,
                    "the BendTT kernel accepts the generated program"
                );
            }
        }
        // §22.13 stage 1 and the attestation: premises against policies.
        "VR-27" => {
            let project = P::copy_example("bend-peano-arithmetic");
            let main = project.read_raw("src/Main.lex.tex");
            let strict = main.replacen(
                "\\exactaxioms{Classical.choice;Quot.sound;propext}\n  For every natural number \\(n\\), \\(n\\) is even or not \\(n\\) is even.",
                "\\noaxioms\n  For every natural number \\(n\\), \\(n\\) is even or not \\(n\\) is even.",
                1,
            );
            assert_ne!(
                strict, main,
                "the excluded-middle theorem's policy is tightened"
            );
            project.write("src/Main.lex.tex", &strict);
            let error = support::with_env(&[], || {
                project
                    .engine()
                    .verify(VerifyRequest {
                        selection: Selection::Entrypoints,
                    })
                    .err()
                    .expect("verification fails")
            });
            support::expect_code(&error, "LLV7022");
            assert!(error.to_string().contains("excluded-middle"), "{error}");
            let schema = support::schema("attestation-v3");
            assert_eq!(
                schema["properties"]["spec"]["const"],
                "lexlean/attestation/3"
            );
            assert!(
                schema["required"]
                    .as_array()
                    .expect("required")
                    .iter()
                    .any(|field| field == "bend"),
                "a version-3 attestation records the Bend toolchain"
            );
            assert!(
                schema["properties"]["declarations"]["items"]["required"]
                    .as_array()
                    .expect("required")
                    .iter()
                    .any(|field| field == "premises"),
                "and each declaration's premises"
            );
            // The committed verification of the language-2.0 example holds
            // a Bend record per module and the kernel recheck's, each
            // accepted.
            let verify =
                support::repo_root().join("examples/bend-peano-arithmetic/expected/verify");
            for module in ["Addition", "Divisibility", "Doubling", "Main", "Order"] {
                let path = verify.join(format!("process/bend/PeanoArithmetic.{module}.json"));
                let record: serde_json::Value = serde_json::from_slice(
                    &std::fs::read(path.as_std_path())
                        .unwrap_or_else(|_| panic!("{path} is committed")),
                )
                .expect("JSON");
                assert_eq!(
                    record["stdout"],
                    lexlean::verify::bend::CHECK_SUCCESS,
                    "{module}"
                );
                assert_eq!(record["exit_code"], 0, "{module}");
            }
            let verdict: serde_json::Value = serde_json::from_slice(
                &std::fs::read(verify.join("process/bend/verdict.json").as_std_path())
                    .expect("the kernel recheck's record is committed"),
            )
            .expect("JSON");
            assert_eq!(verdict["stdout"], lexlean::verify::bend::VERDICT_SUCCESS);
            let root = std::fs::read_to_string(verify.join("bend-verdict/Root.bend").as_std_path())
                .expect("the kernel-recheck root is committed");
            assert_eq!(root.lines().count(), 6, "Base and the five modules");
            // A live verification records each theorem's premises.
            if support::lean_backed(id) && support::bend_backed(id) {
                let fresh = P::copy_example("bend-peano-arithmetic");
                let path = path_with(&bend_dir().expect("the pinned Bend"));
                let verified = support::with_env(&[("PATH", Some(&path))], || {
                    fresh
                        .engine()
                        .verify(VerifyRequest {
                            selection: Selection::Entrypoints,
                        })
                        .expect("the example verifies")
                });
                let attestation_path = verified.root.join("attestation.json");
                support::assert_json_file_schema("attestation-v3", &attestation_path);
                let attestation: serde_json::Value = serde_json::from_slice(
                    &std::fs::read(attestation_path.as_std_path()).expect("attestation"),
                )
                .expect("JSON");
                assert_eq!(attestation["spec"], "lexlean/attestation/3");
                assert_eq!(
                    attestation["bend"]["version_output"],
                    lexlean::BEND_VERSION_LINE
                );
                let row = attestation["declarations"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .find(|row| row["name"] == "PeanoArithmetic.Main.even_or_not")
                    .expect("the theorem's row");
                assert_eq!(row["premises"], serde_json::json!(["excluded-middle"]));
            }
        }
        // §22.13: a language-2.2 project with a production root is verified
        // by Bend first, then by the language-1.2 Lean stages, under
        // attestation schema v4.
        "VR-28" => {
            let schema = support::schema("attestation-v4");
            assert_eq!(
                schema["properties"]["spec"]["const"],
                "lexlean/attestation/4"
            );
            let required = schema["required"].as_array().expect("required");
            assert!(
                required.iter().any(|field| field == "bend"),
                "a version-4 attestation records the Bend toolchain"
            );
            for record in ["compiler_input", "preservation"] {
                assert!(
                    schema["properties"].get(record).is_some(),
                    "and may carry the language-1.2 `{record}` record"
                );
            }
            assert!(
                schema["properties"]["declarations"]["items"]["required"]
                    .as_array()
                    .expect("required")
                    .iter()
                    .any(|field| field == "premises"),
                "and each declaration's premises"
            );
            // The Bend stages run before any Lean process: a false theorem
            // is refused by Bend whether or not Lean is installed.
            if support::bend_backed(id) {
                let project = P::copy_example("bend-reflection");
                let main = project.read_raw("src/Main.lex.tex");
                project.write(
                    "src/Main.lex.tex",
                    &main.replace(
                        "\\end{semanticmodule}",
                        "theorem{\n  name: off_by_one,\n  parameters: [value : Nat],\n  statement: ((value + 1) = value),\n  proof: reflexivity{}\n}\n\\end{semanticmodule}",
                    ),
                );
                let path = path_with(&bend_dir().expect("the pinned Bend"));
                let error = verify_err_with_path(&project, &path);
                support::expect_code(&error, "LLV7020");
            }
            // The committed verification of the language-2.2 example holds an
            // accepted Bend record for its module and the kernel recheck's.
            let verify = support::repo_root().join("examples/bend-semantic/expected/verify");
            let record: serde_json::Value = serde_json::from_slice(
                &std::fs::read(
                    verify
                        .join("process/bend/LanguageTwelve.Main.json")
                        .as_std_path(),
                )
                .expect("the module's Bend record is committed"),
            )
            .expect("JSON");
            assert_eq!(record["stdout"], lexlean::verify::bend::CHECK_SUCCESS);
            assert_eq!(record["exit_code"], 0);
            let verdict: serde_json::Value = serde_json::from_slice(
                &std::fs::read(verify.join("process/bend/verdict.json").as_std_path())
                    .expect("the kernel recheck's record is committed"),
            )
            .expect("JSON");
            assert_eq!(verdict["stdout"], lexlean::verify::bend::VERDICT_SUCCESS);
            if support::lean_backed(id) && support::bend_backed(id) && verdict_available(id) {
                let path = path_with(&bend_dir().expect("the pinned Bend"));
                // The project outlives the reads of its verified directory.
                let rooted = rooted_semantic();
                let (attestation, root) = verified_attestation(&rooted, &path);
                support::assert_json_file_schema("attestation-v4", &root.join("attestation.json"));
                assert_eq!(attestation["spec"], "lexlean/attestation/4");
                for field in ["toolchain", "oleans", "compiler_input", "preservation"] {
                    assert!(
                        attestation.get(field).is_some(),
                        "the Lean stages record `{field}`"
                    );
                }
                // The published kernel-recheck root is the one the kernel
                // ran, importing the module, though the Lean stages release
                // the build's buffers before it is staged.
                let published = std::fs::read_to_string(
                    root.join(lexlean::verify::bend::VERDICT_DIR)
                        .join("Root.bend")
                        .as_std_path(),
                )
                .expect("the kernel-recheck root is published");
                assert_eq!(
                    published,
                    lexlean::verify::bend::verdict_root(&[
                        "modules/LanguageTwelve/Main.bend".to_owned()
                    ])
                );
                assert_eq!(
                    attestation["bend"]["version_output"],
                    lexlean::BEND_VERSION_LINE
                );
                assert!(
                    attestation["declarations"]
                        .as_array()
                        .expect("rows")
                        .iter()
                        .all(|row| row["premises"].is_array()),
                    "every row records its premises"
                );
            }
        }
        // §22.13: a project whose modules all lower to Bend and that declares
        // no production root is verified by Bend alone.
        "VR-29" => {
            if support::posix_shell_backed(id) {
                // An accepting Bend first on PATH and an empty elan home: the
                // pinned Lean toolchain is resolved from the elan home alone
                // (§22.2), so none is there to be found, and a run that
                // reached a Lean stage fails on a host with Lean installed
                // too. The rest of PATH stays, for the cases running beside
                // this one.
                let accepting = accepting_bend();
                let bend_first = path_with(accepting.path());
                let no_elan = tempfile::Builder::new()
                    .prefix("lexlean-no-elan-")
                    .tempdir()
                    .expect("tempdir");
                let no_elan = no_elan.path().display().to_string();
                let home = stand_in_home();
                let home = home.path().display().to_string();
                let without_lean = [
                    ("PATH", Some(bend_first.as_str())),
                    ("ELAN_HOME", Some(no_elan.as_str())),
                    ("HOME", Some(home.as_str())),
                ];
                let peano = P::copy_example("bend-peano-arithmetic");
                let (attestation, root) = verified_attestation_with(&peano, &without_lean);
                assert_bend_only(&attestation, &root, "the language-2.0 example");
                let row = attestation["declarations"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .find(|row| row["name"] == "PeanoArithmetic.Main.even_or_not")
                    .expect("the theorem's row");
                assert_eq!(row["premises"], serde_json::json!(["excluded-middle"]));
                assert_eq!(
                    row["observed"],
                    serde_json::json!(["Classical.choice", "Quot.sound", "propext"]),
                    "a premise is observed as the axioms it stands for"
                );
                let semantic = P::copy_example("bend-semantic");
                let (attestation, root) = verified_attestation_with(&semantic, &without_lean);
                assert_bend_only(&attestation, &root, "the language-2.2 example");
                let names: Vec<&str> = attestation["declarations"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .filter_map(|row| row["name"].as_str())
                    .collect();
                for name in [
                    "LanguageTwelve.Main.doubledSuccessor",
                    "LanguageTwelve.Main.doubled_successor_two",
                    "LanguageTwelve.Main.let_statement_unfolds",
                ] {
                    assert!(names.contains(&name), "{name} has a row: {names:?}");
                }
                // A production root's certificates are Lean proofs, so that
                // project still needs the Lean toolchain.
                let rooted = rooted_semantic();
                let error = support::with_env(&without_lean, || {
                    rooted
                        .engine()
                        .verify(VerifyRequest {
                            selection: Selection::Entrypoints,
                        })
                        .err()
                        .expect("verification fails")
                });
                support::expect_code(&error, "LLV7001");
            }
            if support::bend_backed(id) && verdict_available(id) {
                let path = path_with(&bend_dir().expect("the pinned Bend"));
                let peano = P::copy_example("bend-peano-arithmetic");
                let (attestation, root) = verified_attestation(&peano, &path);
                assert_bend_only(&attestation, &root, "the live language-2.0 verification");
            }
        }
        // §22.13: an accepting recheck names the kernel that accepted.
        "VR-30" => {
            let kernel_in = |home: &std::path::Path| {
                home.join(".bend/bendtt")
                    .join(lexlean::BENDTT_KERNEL_KEY)
                    .join("bendtt")
            };
            if support::posix_shell_backed(id) {
                let accepting = accepting_bend();
                let bend_first = path_with(accepting.path());
                let home = stand_in_home();
                let bytes = std::fs::read(kernel_in(home.path())).expect("the stand-in kernel");
                let home_text = home.path().display().to_string();
                let semantic = P::copy_example("bend-semantic");
                let (attestation, _) = verified_attestation_with(
                    &semantic,
                    &[
                        ("PATH", Some(bend_first.as_str())),
                        ("HOME", Some(home_text.as_str())),
                    ],
                );
                assert_eq!(
                    attestation["bend"]["kernel_sha256"],
                    lexlean::artifact::content_id::Sha256Digest::of(&bytes).to_hex(),
                    "the attestation names the kernel at the pinned key"
                );
                let empty = tempfile::Builder::new()
                    .prefix("lexlean-kernel-empty-")
                    .tempdir()
                    .expect("tempdir");
                let empty_text = empty.path().display().to_string();
                let error = support::with_env(
                    &[
                        ("PATH", Some(bend_first.as_str())),
                        ("HOME", Some(empty_text.as_str())),
                    ],
                    || {
                        semantic
                            .engine()
                            .verify(VerifyRequest {
                                selection: Selection::Entrypoints,
                            })
                            .err()
                            .expect("verification fails")
                    },
                );
                support::expect_code(&error, "LLV7019");
                assert!(
                    error.to_string().contains(lexlean::BENDTT_KERNEL_KEY),
                    "the refusal names where the kernel belongs: {error}"
                );
            }
            if support::bend_backed(id) && verdict_available(id) {
                let home = std::path::PathBuf::from(std::env::var_os("HOME").expect("HOME"));
                // The key Bend derives from its own kernel source, read from
                // `../bend2` beside its resolved executable.
                let bend = std::fs::canonicalize(bend_dir().expect("the pinned Bend").join("bend"))
                    .expect("the pinned Bend resolves");
                let source = std::fs::read(
                    bend.parent()
                        .expect("its directory")
                        .join("../bend2/bendtt.lean"),
                )
                .expect("the pinned Bend's kernel source");
                let keyed = [b"4.34.0\0".as_slice(), &source].concat();
                assert_eq!(
                    &lexlean::artifact::content_id::Sha256Digest::of(&keyed).to_hex()[..16],
                    lexlean::BENDTT_KERNEL_KEY,
                    "the pinned key is the one the pinned Bend derives"
                );
                let path = path_with(&bend_dir().expect("the pinned Bend"));
                let semantic = P::copy_example("bend-semantic");
                let (attestation, _) = verified_attestation(&semantic, &path);
                let kernel = std::fs::read(kernel_in(&home)).expect("the installed kernel");
                assert_eq!(
                    attestation["bend"]["kernel_sha256"],
                    lexlean::artifact::content_id::Sha256Digest::of(&kernel).to_hex(),
                    "the live attestation names the installed kernel"
                );
            }
        }
        other => panic!("no Bend verification case is wired for {other}"),
    }
}
