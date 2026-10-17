//! The `bend-backend` suite: BN-01..BN-09 (SPEC.md §18.10); the language-2.2
//! rows are `bend_semantic`'s.

use std::collections::BTreeSet;

use crate::support::{self, P};

/// The generated Bend of the language-2.0 copy of the §29 literal example,
/// byte for byte.
const EXAMPLE_BEND: &str = "import Base\nimport ../LexLeanPrelude.bend as L\n\nlaw add_zero:\n  for +llv0: Nat\n  {L.Lean.Nat.add(llv0, 0n) == llv0 : Nat}\n\ndef add_zero(llv0):\n  {==}\n";

/// The language-2.0 examples (§18.10), each with its generated modules.
const EXAMPLES: [(&str, &[&str]); 4] = [
    ("bend-nat-add-zero", &["LexLeanExample/Main"]),
    (
        "bend-peano-arithmetic",
        &[
            "PeanoArithmetic/Addition",
            "PeanoArithmetic/Divisibility",
            "PeanoArithmetic/Doubling",
            "PeanoArithmetic/Main",
            "PeanoArithmetic/Order",
        ],
    ),
    ("bend-propositional-logic", &["PropositionalLogic/Main"]),
    ("bend-list-induction", &["ListInduction/Main"]),
];

fn example_build(name: &str) -> lexlean::api::RenderedBuild {
    support::rendered(&P::copy_example(name))
}

fn module_bend(build: &lexlean::api::RenderedBuild, module: &str) -> String {
    support::bend_file(build, &format!("modules/{module}.bend"))
        .unwrap_or_else(|| panic!("`{module}` has a generated Bend file"))
}

/// The language-2.0 copy of the nat-add-zero example with `Main` replaced.
fn project_with(module: &str) -> P {
    let project = P::example();
    project.to_language_2_0();
    project.write("src/Main.lex.tex", module);
    project
}

fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{main-goal}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// Render a project's build, expecting a `LLB6008` refusal naming `phrase`.
fn refused(project: &P, phrase: &str) {
    let inner =
        lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("project loads");
    let (lock, packages) = lexlean::lock::read_current_lock(&inner).expect("lock current");
    let checked =
        lexlean::link::check_project(&inner, &lexlean::Selection::Entrypoints, &lock, packages)
            .expect("the project checks: the refusal is the Bend backend's");
    let Err(error) = lexlean::api::render_build(&inner, &checked) else {
        panic!("the build is refused");
    };
    support::expect_code(&error, "LLB6008");
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains(phrase)),
        "the refusal names `{phrase}`: {:#?}",
        error.diagnostics
    );
}

/// Check every generated module of a build with the pinned Bend.
fn check_build(build: &lexlean::api::RenderedBuild) -> Vec<(String, bool, String)> {
    let dir = support::materialize(build);
    let mut out = Vec::new();
    for (path, _) in &build.files {
        if path.starts_with("modules/")
            && path.ends_with(".bend")
            && !path.ends_with("LexLeanPrelude.bend")
        {
            let (accepted, text) = support::bend_check(&dir.path().join(path));
            out.push((path.clone(), accepted, text));
        }
    }
    out
}

pub(crate) fn run(id: &str) {
    match id {
        // §18.10.1: one deterministic `.bend` beside the `.lean` and `.tex`
        // of each language-2.0 document module, and none for 1.x.
        "BN-01" => {
            let build = example_build("bend-nat-add-zero");
            assert_eq!(
                module_bend(&build, "LexLeanExample/Main"),
                EXAMPLE_BEND,
                "§18.10 bytes"
            );
            for path in [
                "modules/LexLeanExample/Main.lean",
                "modules/LexLeanExample/Main.tex",
                "modules/LexLeanPrelude.bend",
            ] {
                assert!(
                    build.files.iter().any(|(candidate, _)| candidate == path),
                    "the build holds `{path}`"
                );
            }
            let again = example_build("bend-nat-add-zero");
            assert_eq!(build.files, again.files, "rendering is byte-deterministic");
            let legacy = support::rendered(&P::example());
            assert!(
                !legacy.files.iter().any(|(path, _)| path.ends_with(".bend")),
                "a language-1.0 build has no Bend file"
            );
            // Imports: Base, the prelude, then the referenced modules in
            // sorted order, each by relative path under its alias.
            let peano = example_build("bend-peano-arithmetic");
            let main = module_bend(&peano, "PeanoArithmetic/Main");
            let imports: Vec<&str> = main
                .lines()
                .take_while(|line| line.starts_with("import "))
                .collect();
            assert_eq!(
                imports,
                [
                    "import Base",
                    "import ../LexLeanPrelude.bend as L",
                    "import ./Addition.bend as PeanoArithmetic_Addition",
                    "import ./Divisibility.bend as PeanoArithmetic_Divisibility",
                    "import ./Doubling.bend as PeanoArithmetic_Doubling",
                    "import ./Order.bend as PeanoArithmetic_Order",
                ]
            );
            assert!(
                main.ends_with('\n') && !main.ends_with("\n\n"),
                "one final LF"
            );
        }
        // §18.10.2: externals only through the registry, every binder
        // passed; an unregistered constant and an undetermined implicit
        // argument are refused.
        "BN-02" => {
            let build = example_build("bend-list-induction");
            let main = module_bend(&build, "ListInduction/Main");
            assert!(
                main.contains("L.Lean.List.append(llv0, L.Lean.List.nil(llv0), llv1)"),
                "the implicit element type is passed to every list constant"
            );
            // Every Lean denotation of the language-1.0 builtin packages has
            // a registry row under its exact signature.
            let registry =
                lexlean::backend::bend::prelude::registry().expect("the registry parses");
            let checked = support::checked_project(&P::example());
            let mut rows = 0usize;
            for package in &checked.closure.packages {
                for entry in package.entries.values() {
                    if let lexlean::lexicon::entry::Denotation::Lean { name, .. } =
                        &entry.denotation
                    {
                        let canonical = entry.signature_canonical.as_deref().expect("a signature");
                        assert!(
                            registry.constant(name, canonical).is_some()
                                || registry.assumption_for(name).is_some(),
                            "`{name}` of `{}` has a prelude registry row",
                            package.id
                        );
                        rows += 1;
                    }
                }
            }
            assert!(
                rows > 0,
                "the builtin closure has Lean denotations to check"
            );
            // A glossary constant the registry does not hold is refused.
            let unknown = P::copy_example("bend-nat-add-zero");
            unknown.add_package(
                "lexicons/test-unknown",
                "test.unknown",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[(
                    "nzz.toml",
                    "spec = \"lexlean/entry/1\"\nid = \"nzz\"\ncategory = \"proof-constant\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::lnot) (app (const lexlean.std.nat::ne) (local n) (local n))))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.this_constant_does_not_exist\"\n\n[[form]]\nid = \"nzz\"\nchannel = \"math\"\nsurface = \"nzz\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name nzz) (paren (slot 0)))\"\n",
                )],
            );
            unknown.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.unknown@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{not-ne}\n\\noaxioms\nNot \\(0 \u{2260} 0\\).\n\\begin{proof}\nClose the goal with \\(nzz(0)\\).\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            unknown.relock();
            refused(&unknown, "has no Bend prelude definition");
            // An implicit argument nothing determines is refused rather than
            // guessed.
            let project = lexlean::backend::bend::engine::ProjectIndex {
                closure: &checked.closure,
                declarations: std::collections::BTreeMap::new(),
                generated_modules: std::collections::BTreeMap::new(),
            };
            let mut engine =
                lexlean::backend::bend::engine::Engine::new(&project, registry, "Main");
            let zero = checked
                .closure
                .packages
                .iter()
                .flat_map(|package| package.entries.iter().map(move |(id, entry)| (package, id, entry)))
                .find(|(_, _, entry)| {
                    matches!(&entry.denotation, lexlean::lexicon::entry::Denotation::Lean { name, .. } if name == "Nat.zero")
                })
                .map(|(package, id, entry)| lexlean::ir::term::ExternalConstRef {
                    package: package.id.clone(),
                    entry: format!("{}::{id}", package.id),
                    lean_module: "Init".to_owned(),
                    lean_name: "Nat.zero".to_owned(),
                    signature_hash: entry.signature_hash.expect("hash"),
                })
                .expect("the builtin closure denotes Nat.zero");
            assert!(
                engine
                    .lower(
                        &Vec::new(),
                        &lexlean::ir::term::Term::Global(
                            lexlean::ir::term::GlobalRef::External(zero),
                            Vec::new()
                        ),
                        None
                    )
                    .is_ok(),
                "a constant with no implicit binder lowers"
            );
            let alpha = lexlean::ir::term::LocalId(7);
            let pi = lexlean::ir::term::Term::Pi {
                binders: vec![lexlean::ir::term::Binder {
                    id: alpha,
                    mode: lexlean::lexicon::lse::BinderMode::Implicit,
                    ty: lexlean::ir::term::Term::Sort(lexlean::ir::term::Universe::Num(1)),
                    spelling: "a".to_owned(),
                }],
                body: Box::new(lexlean::ir::term::Term::Local(alpha)),
            };
            let error = engine
                .instantiate(&Vec::new(), &pi, &[], None)
                .expect_err("an implicit binder with nothing to solve it is refused");
            assert_eq!(error.code.as_str(), "LLB6008");
            assert!(
                error.message.contains("cannot be determined"),
                "{}",
                error.message
            );
        }
        // §18.10.3: the closed, prose-free output.
        "BN-03" => {
            let forbidden = ["#", "@unsafe", "?", "import \"", "import 0x", "!(", "IO"];
            for (example, modules) in EXAMPLES {
                let build = example_build(example);
                for module in modules {
                    let text = module_bend(&build, module);
                    for token in forbidden {
                        assert!(
                            !text.contains(token),
                            "{module}: generated Bend contains `{token}`"
                        );
                    }
                    assert!(
                        !text
                            .lines()
                            .any(|line| line.starts_with("import ") && line.contains('@')),
                        "{module}: no hub import"
                    );
                    // Every law has its proof definition.
                    let laws: Vec<&str> = text
                        .lines()
                        .filter_map(|line| {
                            line.strip_prefix("law ")
                                .and_then(|rest| rest.strip_suffix(':'))
                        })
                        .collect();
                    assert!(!laws.is_empty(), "{module}: has laws");
                    for law in laws {
                        assert!(
                            text.contains(&format!("\ndef {law}(")),
                            "{module}: `{law}` is a filled law"
                        );
                    }
                }
            }
        }
        // §18.10.4: theorems as laws, proofs as terms, auxiliaries first;
        // every form of the proof corpus, `simp only` included, checks.
        "BN-04" => {
            let logic = example_build("bend-propositional-logic");
            let main = module_bend(&logic, "PropositionalLogic/Main");
            let aux = main
                .find("def and_comm.c0(")
                .expect("the case split is an auxiliary");
            let law = main.find("law and_comm:").expect("the theorem is a law");
            assert!(aux < law, "the auxiliary definition precedes its law");
            assert!(
                main.contains("def and_comm(llv0, llv1, llh0):\n  and_comm.c0(llv0, llv1, llh0)\n")
            );
            let peano = example_build("bend-peano-arithmetic");
            let order = module_bend(&peano, "PeanoArithmetic/Order");
            assert!(
                order.contains("llh1 = zero_le.i0(llh0)"),
                "the induction hypothesis is the auxiliary's recursive call"
            );
            let addition = module_bend(&peano, "PeanoArithmetic/Addition");
            assert!(addition.contains("\n  %"), "a rewrite lowers to `%`");
            let doubling = module_bend(&peano, "PeanoArithmetic/Doubling");
            assert!(
                doubling.contains("Equal.trans("),
                "a calculation lowers to a transitivity chain"
            );
            // Every form of the shared proof corpus lowers and checks.
            let corpus = support::corpus_project();
            corpus.to_language_2_0();
            let build = support::rendered(&corpus);
            assert!(support::bend_file(&build, "modules/LexLeanExample/Main.bend").is_some());
            if support::bend_backed(id) {
                for (path, accepted, text) in check_build(&build) {
                    assert!(
                        accepted,
                        "{path}: the proof corpus checks under Bend:\n{text}"
                    );
                }
            }
        }
        // §18.10.5: no template; a function-typed hypothesis used twice on
        // one branch is refused by Bend.
        "BN-05" => {
            for (example, modules) in EXAMPLES {
                let build = example_build(example);
                for module in modules {
                    let text = module_bend(&build, module);
                    assert!(
                        !text.contains('~'),
                        "{module}: no generated declaration takes a template"
                    );
                }
            }
            let moved = P::copy_example("propositional-logic");
            moved.to_language_2_0();
            let build = support::rendered(&moved);
            let main = module_bend(&build, "PropositionalLogic/Main");
            assert!(
                main.contains("law de_morgan:\n  for -llv0: Type\n  for -llv1: Type\n  for llh0: Either<&1, &1, llv0, llv1> -> Empty\n"),
                "the negated hypothesis is affine"
            );
            if support::bend_backed(id) {
                let results = check_build(&build);
                let (_, accepted, text) = results.first().expect("one module");
                assert!(!accepted, "the twice-used hypothesis is refused");
                assert!(text.contains("llh0 (consumed more than once)"), "{text}");
                assert!(text.contains("Location: de_morgan"), "{text}");
            }
        }
        // §18.10.6: the prelude.
        "BN-06" => {
            let root = support::repo_root();
            let prelude = std::fs::read_to_string(
                root.join("language/bend-prelude/LexLean.bend")
                    .as_std_path(),
            )
            .expect("the prelude");
            assert_eq!(
                prelude.lines().find(|line| line.starts_with("import ")),
                Some("import Base"),
                "the prelude imports Base"
            );
            assert_eq!(
                prelude
                    .lines()
                    .filter(|line| line.starts_with("import "))
                    .count(),
                1,
                "the prelude imports only Base"
            );
            // The open-hole marker is spelled in halves so this gate does not
            // match its own source (R4).
            let hole = concat!("?TO", "DO");
            for token in ["@unsafe", hole, "import \"", "!("] {
                assert!(!prelude.contains(token), "the prelude contains `{token}`");
            }
            let registry_text = std::fs::read_to_string(
                root.join("language/bend-prelude/registry.toml")
                    .as_std_path(),
            )
            .expect("the registry");
            let registry: toml::Value = registry_text.parse().expect("registry TOML");
            let mut defined = BTreeSet::new();
            for line in prelude.lines() {
                for prefix in ["def ", "law ", "type "] {
                    if let Some(rest) = line.strip_prefix(prefix) {
                        let name: String = rest
                            .chars()
                            .take_while(|c| c.is_alphanumeric() || *c == '.' || *c == '_')
                            .collect();
                        defined.insert(name);
                    }
                }
            }
            let rows = registry["constant"].as_array().expect("constant rows");
            for row in rows {
                let bend = row["bend"].as_str().expect("bend");
                let base = row.get("origin").and_then(toml::Value::as_str) == Some("base");
                let kind = row["kind"].as_str().expect("kind");
                if kind != "constructor" && kind != "assumption" && !base {
                    assert!(
                        defined.contains(bend),
                        "registry row `{bend}` is defined in the prelude"
                    );
                }
            }
            for law in prelude.lines().filter_map(|line| {
                line.strip_prefix("law ")
                    .and_then(|rest| rest.strip_suffix(':'))
            }) {
                assert!(
                    prelude.contains(&format!("\ndef {law}(")),
                    "the prelude law `{law}` is proved"
                );
            }
            if support::bend_backed(id) {
                let dir = tempfile::Builder::new()
                    .prefix("lexlean-bend-prelude-")
                    .tempdir()
                    .expect("tempdir");
                std::fs::write(dir.path().join("LexLeanPrelude.bend"), &prelude).expect("prelude");
                let (accepted, text) = support::bend_check(&dir.path().join("LexLeanPrelude.bend"));
                assert!(accepted, "the prelude checks: {text}");
                // Definitional fidelity: Lean's `n + 0 = n` is `rfl`, and
                // Lean's `0 + n = n` is not.
                std::fs::write(
                    dir.path().join("Fidelity.bend"),
                    "import Base\nimport ./LexLeanPrelude.bend as L\n\nlaw right:\n  for +x: Nat\n  {L.Lean.Nat.add(x, 0n) == x : Nat}\n\ndef right(x):\n  {==}\n",
                )
                .expect("probe");
                let (accepted, text) = support::bend_check(&dir.path().join("Fidelity.bend"));
                assert!(accepted, "`n + 0 = n` is definitional: {text}");
                std::fs::write(
                    dir.path().join("Unfaithful.bend"),
                    "import Base\nimport ./LexLeanPrelude.bend as L\n\nlaw left:\n  for +x: Nat\n  {L.Lean.Nat.add(0n, x) == x : Nat}\n\ndef left(x):\n  {==}\n",
                )
                .expect("probe");
                let (accepted, _) = support::bend_check(&dir.path().join("Unfaithful.bend"));
                assert!(!accepted, "`0 + n = n` is not definitional, as in Lean");
            }
        }
        // §18.10.7: an assumption is a leading premise, inherited by citing
        // theorems.
        "BN-07" => {
            let project = P::copy_example("bend-peano-arithmetic");
            let main = project.read("src/Main.lex.tex");
            let cited = main.replace(
                "\\end{section}\n\\end{lexlean}",
                "  \\begin{theorem}{even-or-not-again}\n  \\exactaxioms{Classical.choice;Quot.sound;propext}\n  For every natural number \\(n\\), \\(n\\) is even or not \\(n\\) is even.\n  \\begin{proof}\n  Close the goal with \\(\\reference{Main::even-or-not}(n)\\).\n  \\end{proof}\n  \\end{theorem}\n\\end{section}\n\\end{lexlean}",
            );
            assert_ne!(
                cited, main,
                "the citing theorem is appended to the last section"
            );
            project.write("src/Main.lex.tex", &cited);
            let build = support::rendered(&project);
            let text = module_bend(&build, "PeanoArithmetic/Main");
            assert!(text.contains(
                "law even_or_not:\n  for ll_excluded_middle: L.Lean.Assume.excluded_middle()\n  for +llv0: Nat\n"
            ));
            assert!(text.contains(
                "law even_or_not_again:\n  for ll_excluded_middle: L.Lean.Assume.excluded_middle()\n  for +llv0: Nat\n"
            ), "a citing theorem inherits the premise");
            assert!(
                text.contains("even_or_not(ll_excluded_middle, llv0)"),
                "and passes it on"
            );
            assert!(!text.contains("Classical"), "no axiom is named");
            if support::bend_backed(id) {
                for (path, accepted, output) in check_build(&build) {
                    assert!(accepted, "{path}: {output}");
                }
            }
        }
        // §18.10.1, §20.3: coverage and mappings for every Bend token.
        "BN-08" => {
            for (example, modules) in EXAMPLES {
                let build = example_build(example);
                for rendered in &build.modules {
                    let coverage = rendered.coverage.bend.as_ref().expect("Bend coverage rows");
                    let module = modules
                        .iter()
                        .find(|module| module.ends_with(&format!("/{}", rendered.module)))
                        .expect("a listed module");
                    let text = module_bend(&build, module);
                    lexlean::backend::check_output_closure(&text, coverage)
                        .unwrap_or_else(|reason| panic!("{module}: {reason}"));
                    let bend_artifact = rendered
                        .map
                        .artifacts
                        .iter()
                        .find(|artifact| {
                            artifact.kind == lexlean::artifact::source_map::ArtifactKind::Bend
                        })
                        .expect("a Bend artifact row");
                    let mapped: BTreeSet<(usize, usize)> = rendered
                        .map
                        .mappings
                        .iter()
                        .filter(|mapping| mapping.artifact == bend_artifact.id)
                        .map(|mapping| (mapping.gen_start, mapping.gen_end))
                        .collect();
                    for row in coverage {
                        assert!(
                            mapped.contains(&(row.byte_start, row.byte_end)),
                            "{module}: covered bytes {}..{} are mapped",
                            row.byte_start,
                            row.byte_end
                        );
                    }
                    assert_eq!(
                        mapped.len(),
                        coverage.len(),
                        "{module}: one mapping per row"
                    );
                    let map_json =
                        String::from_utf8(rendered.map.to_json().to_file_bytes()).expect("utf8");
                    assert!(map_json.contains("\"spec\":\"lexlean/source-map/2\""));
                    assert!(
                        String::from_utf8(rendered.coverage.to_json().to_file_bytes())
                            .expect("utf8")
                            .contains("\"spec\":\"lexlean/coverage/2\"")
                    );
                }
            }
        }
        // §18.10: every language-2.0 example module checks; a false
        // theorem is refused, so the gate can fail.
        "BN-09" => {
            let mut checked = 0usize;
            for (example, modules) in EXAMPLES {
                let build = example_build(example);
                for module in modules {
                    assert!(
                        support::bend_file(&build, &format!("modules/{module}.bend")).is_some()
                    );
                }
                if support::bend_backed(id) {
                    let results = check_build(&build);
                    assert_eq!(
                        results.len(),
                        modules.len(),
                        "{example}: every module is checked"
                    );
                    for (path, accepted, text) in results {
                        assert!(accepted, "{example} {path}: {text}");
                        checked += 1;
                    }
                }
            }
            if support::bend_backed(id) {
                assert_eq!(checked, 8, "eight generated modules check");
                let false_theorem = project_with(&theorem_module(
                    "For every natural number \\(n\\), \\(n + 1 = n\\).",
                    "Close the goal by reflexivity.",
                ));
                false_theorem.check_ok();
                let build = support::rendered(&false_theorem);
                let results = check_build(&build);
                assert_eq!(results.len(), 1);
                assert!(!results[0].1, "a false theorem is refused by Bend");
                assert!(
                    results[0].2.starts_with("SOME PROOFS FAIL"),
                    "{}",
                    results[0].2
                );
            }
        }
        other => super::bend_semantic::run(other),
    }
}
