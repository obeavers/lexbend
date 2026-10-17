//! The language-2.2 half of the `bend-backend` suite: BN-10..BN-18 (SPEC.md
//! §18.11). Generation is platform-independent and asserted everywhere; a
//! claim that the pinned Bend accepts or refuses a text gates that half on
//! [`support::bend_backed`].

use std::collections::BTreeSet;

use crate::support::{self, P};

/// The committed language-2.2 examples, each with its generated modules.
const EXAMPLES: [(&str, &[&str]); 4] = [
    ("bend-semantic", &["LanguageTwelve/Main"]),
    ("bend-recursion", &["Recursion/Main", "Recursion/Syntax"]),
    (
        "bend-models",
        &[
            "Models/Flows",
            "Models/Glyphs",
            "Models/Ledger",
            "Models/Main",
            "Models/Pipeline",
            "Models/Policy",
            "Models/Recognizer",
            "Models/Session",
            "Models/Triage",
        ],
    ),
    ("bend-reflection", &["Reflection/Main"]),
];

/// Language-1.2 examples that lower whole under language 2.2, each with its
/// generated modules; the cases move a copy rather than commit a duplicate.
const MOVED: [(&str, &[&str]); 3] = [
    (
        "recursive-data",
        &["RecursiveData/Main", "RecursiveData/Types"],
    ),
    (
        "higher-order",
        &["HigherOrder/Combinators", "HigherOrder/Main"],
    ),
    (
        "collections",
        &[
            "Collections/Main",
            "Collections/Measure",
            "Collections/Tables",
        ],
    ),
];

fn example_build(name: &str) -> lexlean::api::RenderedBuild {
    support::rendered(&P::copy_example(name))
}

fn moved(name: &str) -> P {
    let project = P::copy_example(name);
    project.to_language_2_2();
    project
}

fn module_bend(build: &lexlean::api::RenderedBuild, module: &str) -> String {
    support::bend_file(build, &format!("modules/{module}.bend"))
        .unwrap_or_else(|| panic!("`{module}` has a generated Bend file"))
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

/// Every generated module of a build, written out with the files it
/// imports: `(path, directory holding the build)`.
fn generated_modules(build: &lexlean::api::RenderedBuild) -> (tempfile::TempDir, Vec<String>) {
    let dir = support::materialize(build);
    let modules = build
        .files
        .iter()
        .map(|(path, _)| path)
        .filter(|path| {
            path.starts_with("modules/") && path.ends_with(".bend") && path.matches('/').count() > 1
        })
        .cloned()
        .collect();
    (dir, modules)
}

/// Check one module text, altered by `plant`, in place of the generated
/// one: whether the pinned Bend accepts it, and what it printed.
fn check_planted(
    build: &lexlean::api::RenderedBuild,
    module: &str,
    plant: &dyn Fn(&str) -> String,
) -> (bool, String) {
    let dir = support::materialize(build);
    let path = dir.path().join(format!("modules/{module}.bend"));
    let original = std::fs::read_to_string(&path).expect("generated module");
    let planted = plant(&original);
    assert_ne!(planted, original, "{module}: the plant applies");
    std::fs::write(&path, planted).expect("planted module");
    support::bend_check(&path)
}

/// Replace exactly one occurrence of `from`, asserting it is there.
fn replace_one(text: &str, from: &str, to: &str) -> String {
    assert_eq!(
        text.matches(from).count(),
        1,
        "the generated text holds `{from}` exactly once"
    );
    text.replacen(from, to, 1)
}

pub(crate) fn run(id: &str) {
    match id {
        // §18.11.1: one deterministic `.bend` per semantic module, with the
        // exact import structure, every token covered and mapped.
        "BN-10" => {
            let build = example_build("bend-semantic");
            let again = example_build("bend-semantic");
            assert_eq!(build.files, again.files, "the build is byte-deterministic");
            for extension in ["bend", "lean", "tex"] {
                assert!(
                    build.files.iter().any(
                        |(path, _)| path == &format!("modules/LanguageTwelve/Main.{extension}")
                    ),
                    "the module renders its `.{extension}`"
                );
            }
            assert!(module_bend(&build, "LanguageTwelve/Main")
                .starts_with("import Base\nimport ../LexLeanPrelude.bend as L\n\n"));
            let models = example_build("bend-models");
            let main = module_bend(&models, "Models/Main");
            assert!(
                main.starts_with(
                    "import Base\nimport ../LexLeanPrelude.bend as L\nimport ../LexLeanSemantic.bend as S\nimport ../LexLeanRuntime.bend as R\nimport ./Flows.bend as Models_Flows\nimport ./Glyphs.bend as Models_Glyphs\nimport ./Ledger.bend as Models_Ledger\nimport ./Pipeline.bend as Models_Pipeline\nimport ./Recognizer.bend as Models_Recognizer\nimport ./Session.bend as Models_Session\nimport ./Triage.bend as Models_Triage\n\n"
                ),
                "Base, the prelude, the support modules, then the imports by path"
            );
            // A build publishes exactly the support modules its modules
            // import.
            for (example, modules) in EXAMPLES {
                let build = example_build(example);
                let mut imported = BTreeSet::new();
                for module in modules {
                    for line in module_bend(&build, module).lines() {
                        if let Some(rest) = line.strip_prefix("import ../") {
                            imported.insert(format!(
                                "modules/{}",
                                rest.split(' ').next().expect("a path")
                            ));
                        }
                    }
                }
                let published: BTreeSet<String> = build
                    .files
                    .iter()
                    .map(|(path, _)| path.clone())
                    .filter(|path| path.starts_with("modules/LexLean") && path.ends_with(".bend"))
                    .collect();
                assert_eq!(
                    published, imported,
                    "{example}: exactly the imported support"
                );
                for rendered in &build.modules {
                    let coverage = rendered.coverage.bend.as_ref().expect("Bend coverage rows");
                    let module = modules
                        .iter()
                        .find(|module| module.ends_with(&format!("/{}", rendered.module)))
                        .expect("a listed module");
                    let text = module_bend(&build, module);
                    lexlean::backend::check_output_closure(&text, coverage)
                        .unwrap_or_else(|reason| panic!("{module}: {reason}"));
                    let artifact = rendered
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
                        .filter(|mapping| mapping.artifact == artifact.id)
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
                }
            }
        }
        // §18.11.2: templates and closure conversion.
        "BN-11" => {
            let project = moved("higher-order");
            let build = support::rendered(&project);
            let combinators = module_bend(&build, "HigherOrder/Combinators");
            assert!(combinators.contains(
                "def mapList(~Input: Data, ~Output: Data, ~ll_E_transform: Data, ~transform: @+ll_e: ll_E_transform -> @+x: Input -> Output, +values: List<&2, Input>, +ll_env_transform: ll_E_transform) -> List<&2, Output>:\n"
            ), "type parameters are templates; the function parameter is a code template over its environment");
            let main = module_bend(&build, "HigherOrder/Main");
            assert!(main.contains(
                "  HigherOrder_Combinators.mapList(~Nat, ~Nat, ~Nat, ~(+ll_e => +value => (\n    +offset = ll_e\n    L.Lean.Nat.add(value, offset)\n  )), values, offset)\n"
            ), "a capturing lambda passes its captures as the environment");
            assert!(main.contains(
                "HigherOrder_Combinators.mapList(~Nat, ~Nat, ~Unit, ~(+ll_e => +ll_x1 => HigherOrder_Combinators.increment(ll_x1)), values, Unit{})"
            ), "a function reference is a closed template with the unit environment");
            assert!(main.contains("def map_identity.ll_ind1(~Input: Data, "));
            if support::bend_backed(id) {
                let (dir, modules) = generated_modules(&build);
                for path in modules {
                    let (accepted, text) = support::bend_check(&dir.path().join(&path));
                    assert!(accepted, "{path}: {text}");
                }
            }
            let main = project.read_raw("src/Main.lex.tex");
            let higher = main.replace(
                "theorem{\n  name: add_all,",
                "definition{\n  name: twiceOf,\n  parameters: [f : (Fn (Nat) Nat), value : Nat],\n  result: Nat,\n  body: (apply f (apply f value))\n}\n\ndefinition{\n  name: applyHigher,\n  parameters: [h : (Fn ((Fn (Nat) Nat) Nat) Nat), value : Nat],\n  result: Nat,\n  body: (apply h (ref Combinators::increment) value)\n}\n\ndefinition{\n  name: passesHigher,\n  parameters: [values : (List Nat)],\n  result: (List Nat),\n  body: (Combinators::mapList [Nat, Nat] (fun (value : Nat) => (applyHigher (ref twiceOf) value)) values)\n}\n\ntheorem{\n  name: add_all,",
            );
            assert_ne!(higher, main, "the definitions are inserted");
            project.write("src/Main.lex.tex", &higher);
            refused(
                &project,
                "the higher-order function `twiceOf` is passed as a value",
            );
        }
        // §18.11.3: inlining, and the simultaneous-recursion refusal.
        "BN-12" => {
            let build = example_build("bend-recursion");
            let main = module_bend(&build, "Recursion/Main");
            let forest = main
                .find("def forestSize(")
                .expect("forestSize keeps its name");
            let rose = main.find("def roseSize(").expect("roseSize keeps its name");
            assert!(
                forest < rose,
                "the self-recursive member precedes its caller"
            );
            assert!(
                main.contains("        case Recursion_Syntax.Rose.node{label, children}:\n          L.Lean.Nat.add(L.Lean.Nat.add(1n, forestSize(~Item, children)), forestSize(~Item, tail))\n"),
                "`roseSize` is inlined into `forestSize`"
            );
            assert!(
                main.contains("def isEven(+number: Nat) -> Bool:\n  match number:\n    case 0n:\n      True{}\n    case 1n+previous:\n      match previous:\n        case 0n:\n          False{}\n        case 1n+previous:\n          isEven(previous)\n"),
                "`isOdd` is inlined into `isEven`"
            );
            assert!(main.contains("def isOdd(+number: Nat) -> Bool:\n"));
            refused(
                &moved("recursion"),
                "the mutual group `SyntaxSize` recurses simultaneously through `exprSize`, `statementsSize`, `statementSize`",
            );
        }
        // §18.11.4: proof-carrying fuel; Bend refuses a planted defect.
        "BN-13" => {
            let build = example_build("bend-recursion");
            let main = module_bend(&build, "Recursion/Main");
            assert!(main.contains(
                "def countdown.ll_go(+ll_fuel1: Nat, +number: Nat, +steps: Nat, +ll_bound3: S.Sem.lt(number, ll_fuel1)) -> Nat:\n"
            ), "the helper takes fuel and a bound on the measure");
            assert!(main.contains(
                "countdown.ll_go(ll_fuel2, L.Lean.Nat.sub(number, 2n), L.Lean.Nat.add(steps, 1n), S.Sem.lt_fuel(L.Lean.Nat.sub(number, 2n), number, ll_fuel2, countdown_decreases(number, steps, ll_w5), ll_bound3))"
            ), "the recursive call consumes fuel and carries the decrease evidence");
            assert!(main.contains(
                "def countdown(+number: Nat, +steps: Nat) -> Nat:\n  countdown.ll_go(1n+number, number, steps, S.Sem.lt_succ(number))\n"
            ), "the wrapper supplies one more fuel than the measure");
            if support::bend_backed(id) {
                let (dir, modules) = generated_modules(&build);
                for path in modules {
                    let (accepted, text) = support::bend_check(&dir.path().join(&path));
                    assert!(accepted, "{path}: {text}");
                }
                let (accepted, _) = check_planted(&build, "Recursion/Main", &|text| {
                    replace_one(
                        text,
                        "countdown.ll_go(ll_fuel2, L.Lean.Nat.sub(number, 2n)",
                        "countdown.ll_go(ll_fuel1, L.Lean.Nat.sub(number, 2n)",
                    )
                });
                assert!(!accepted, "a call that consumes no fuel is refused");
                let (accepted, _) = check_planted(&build, "Recursion/Main", &|text| {
                    replace_one(
                        text,
                        "countdown_decreases(number, steps, ll_w5)",
                        "S.Sem.lt_succ(number)",
                    )
                });
                assert!(!accepted, "evidence of another decrease is refused");
            }
        }
        // §18.11.5: explicit proof terms for every lowered tactic.
        "BN-14" => {
            let build = example_build("bend-reflection");
            let main = module_bend(&build, "Reflection/Main");
            assert!(
                main.contains("def pair_reflects(pair):\n  ((\n    +ll_h0 => (\n      (LA.sound("),
                "a record reflection is linear arithmetic each way"
            );
            assert!(main.contains(
                "def counts_reflects(start, values):\n  ((+ll_reflected => counts_reflects.ll_reflect1.forward(values, start, ll_reflected)), (ll_reflected => counts_reflects.ll_reflect1.backward(values, start, ll_reflected)))\n"
            ), "a list reflection is one induction per direction");
            assert!(main.contains(
                "def counts_reflects.ll_reflect1.backward(+ll_values: List<&2, Nat>, +ll_p: Nat, ll_h: CountsFrom(ll_values, ll_p))"
            ), "the proposition's proof is affine");
            let recursion = example_build("bend-recursion");
            let text = module_bend(&recursion, "Recursion/Main");
            assert!(
                text.contains("law ten_is_even:\n  {isEven(10n) == True{} : Bool}\n\ndef ten_is_even():\n  {==}\n"),
                "`decide` on a closed goal is evaluation"
            );
            if support::bend_backed(id) {
                let (dir, modules) = generated_modules(&build);
                for path in modules {
                    let (accepted, text) = support::bend_check(&dir.path().join(&path));
                    assert!(accepted, "{path}: {text}");
                }
                let (accepted, _) = check_planted(&build, "Reflection/Main", &|text| {
                    replace_one(
                        text,
                        "counts_reflects.ll_reflect1.forward(ll_rest, L.Lean.Nat.add(ll_p, 1n)",
                        "counts_reflects.ll_reflect1.forward(ll_rest, L.Lean.Nat.add(ll_p, 2n)",
                    )
                });
                assert!(
                    !accepted,
                    "an induction stepping the wrong successor is refused"
                );
            }
        }
        // §18.11.7: cross-checks against the runtime's fixed semantics.
        "BN-15" => {
            let build = example_build("bend-models");
            let flows = module_bend(&build, "Models/Flows");
            assert!(flows.contains(
                "law FlowContract.invariant_sound:\n  R.LexLeanModels.Sound1(Nat, (+ll_x1 => Models_Ledger.cappedCheck(ll_x1)), (+ll_x2 => Models_Ledger.Capped(ll_x2)))\n\ndef FlowContract.invariant_sound():\n  ll_a3 => ll_a4 => flow_capped_sound(ll_a3, ll_a4)\n"
            ), "a contract obligation is restated against LexLeanModels and proved by its theorem");
            let triage = module_bend(&build, "Models/Triage");
            assert!(
                triage.contains("{L.Lean.Bool.and(R.LexLeanModels.tensorMatches(2n, True{}, triageBias(), triageBias.bytes()), L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, triageBias()), 3n)) == True{} : Bool}"),
                "a tensor's values decode from its bytes, with its shape"
            );
            if support::bend_backed(id) {
                let (dir, modules) = generated_modules(&build);
                for path in modules {
                    let (accepted, text) = support::bend_check(&dir.path().join(&path));
                    assert!(accepted, "{path}: {text}");
                }
                let (accepted, _) = check_planted(&build, "Models/Flows", &|text| {
                    replace_one(
                        text,
                        "R.LexLeanModels.Sound1(Nat, (+ll_x1 => Models_Ledger.cappedCheck(ll_x1)), (+ll_x2 => Models_Ledger.Capped(ll_x2)))",
                        "R.LexLeanModels.Sound1(Nat, (+ll_x1 => Models_Ledger.cappedCheck(ll_x1)), (+ll_x2 => Models_Ledger.Within(ll_x2)))",
                    )
                });
                assert!(
                    !accepted,
                    "a restatement drifted to another invariant is refused"
                );
                let (accepted, _) = check_planted(&build, "Models/Triage", &|text| {
                    replace_one(
                        text,
                        "L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, triageBias()), 3n)",
                        "L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, triageBias()), 4n)",
                    )
                });
                assert!(!accepted, "a tensor of another shape is refused");
            }
        }
        // §18.11.6: the shipped support modules and the runtime registry.
        "BN-16" => {
            use lexlean::backend::bend::semantic::support::Support;
            let root = support::repo_root();
            let supports = [Support::Semantic, Support::Runtime, Support::LinArith];
            for module in supports {
                let text = std::fs::read_to_string(root.join(module.source_path()).as_std_path())
                    .expect("the support module is committed");
                let imports: Vec<&str> = text
                    .lines()
                    .filter(|line| line.starts_with("import "))
                    .collect();
                assert_eq!(
                    imports,
                    ["import Base", "import ./LexLean.bend as L"],
                    "{}: only Base and the prelude",
                    module.source_path()
                );
            }
            let registry: toml::Value = toml::from_str(
                &std::fs::read_to_string(
                    root.join("language/bend-prelude/runtime-registry.toml")
                        .as_std_path(),
                )
                .expect("the runtime registry is committed"),
            )
            .expect("the runtime registry parses");
            let runtime =
                std::fs::read_to_string(root.join(Support::Runtime.source_path()).as_std_path())
                    .expect("runtime");
            let mut defined = BTreeSet::new();
            for line in runtime.lines() {
                for keyword in ["def ", "law ", "type "] {
                    if let Some(rest) = line.strip_prefix(keyword) {
                        let name: String = rest
                            .chars()
                            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                            .collect();
                        defined.insert(name);
                    }
                }
                // A constructor is a line of its type's body: `  Name{..}`.
                if let Some(rest) = line.strip_prefix("  ") {
                    if let Some((name, _)) = rest.split_once('{') {
                        if !name.is_empty()
                            && name
                                .chars()
                                .all(|c| c.is_alphanumeric() || c == '_' || c == '.')
                        {
                            defined.insert(name.to_owned());
                        }
                    }
                }
            }
            let rows = registry["constant"].as_array().expect("constant rows");
            assert!(!rows.is_empty(), "the registry has rows");
            for row in rows {
                let bend = row["bend"].as_str().expect("bend name");
                // A name with no namespace is one of Base's own types.
                assert!(
                    defined.contains(bend) || !bend.contains('.'),
                    "registry row `{bend}` is defined by the runtime"
                );
            }
            if support::bend_backed(id) {
                let dir = tempfile::Builder::new()
                    .prefix("lexlean-bend-support-")
                    .tempdir()
                    .expect("tempdir");
                let prelude = std::fs::read(
                    root.join("language/bend-prelude/LexLean.bend")
                        .as_std_path(),
                )
                .expect("prelude");
                std::fs::create_dir_all(dir.path().join("modules")).expect("modules");
                std::fs::write(dir.path().join("modules/LexLeanPrelude.bend"), prelude)
                    .expect("prelude");
                for module in supports {
                    let (path, bytes) = module.artifact().expect("embedded");
                    let target = dir.path().join(path);
                    std::fs::write(&target, bytes).expect("support module");
                    let (accepted, text) = support::bend_check(&target);
                    assert!(accepted, "{path}: {text}");
                }
            }
        }
        // §18.11.8: reasoning declarations are refused.
        "BN-17" => {
            refused(
                &moved("reasoning"),
                "the reasoning declaration generates `Tick.apply_sound`, whose proof has no Bend lowering",
            );
        }
        // §18.11: every language-2.2 example module checks and exports.
        "BN-18" => {
            let mut builds = Vec::new();
            for (example, modules) in EXAMPLES {
                builds.push((example.to_owned(), modules, example_build(example)));
            }
            for (example, modules) in MOVED {
                builds.push((
                    format!("{example} (moved)"),
                    modules,
                    support::rendered(&moved(example)),
                ));
            }
            for (example, modules, build) in &builds {
                for module in *modules {
                    assert!(
                        support::bend_file(build, &format!("modules/{module}.bend")).is_some(),
                        "{example}: `{module}` is generated"
                    );
                }
            }
            if support::bend_backed(id) {
                let mut checked = 0usize;
                for (example, modules, build) in &builds {
                    let (dir, generated) = generated_modules(build);
                    assert_eq!(generated.len(), modules.len(), "{example}: every module");
                    for path in generated {
                        let file = dir.path().join(&path);
                        let (accepted, text) = support::bend_check(&file);
                        assert!(accepted, "{example} {path}: {text}");
                        let (exported, text) = support::bend_export(&file);
                        assert!(exported, "{example} {path} exports: {text}");
                        checked += 1;
                    }
                }
                assert_eq!(checked, 20, "twenty generated modules check and export");
                let project = P::copy_example("bend-reflection");
                let main = project.read_raw("src/Main.lex.tex");
                let false_theorem = main.replace(
                    "\\end{semanticmodule}",
                    "theorem{\n  name: off_by_one,\n  parameters: [value : Nat],\n  statement: ((value + 1) = value),\n  proof: reflexivity{}\n}\n\\end{semanticmodule}",
                );
                project.write("src/Main.lex.tex", &false_theorem);
                let build = support::rendered(&project);
                let (dir, generated) = generated_modules(&build);
                let (accepted, text) = support::bend_check(&dir.path().join(&generated[0]));
                assert!(!accepted, "a false theorem is refused by Bend");
                assert!(text.starts_with("SOME PROOFS FAIL"), "{text}");
            }
        }
        other => panic!("no language-2.2 bend-backend case is wired for {other}"),
    }
}
