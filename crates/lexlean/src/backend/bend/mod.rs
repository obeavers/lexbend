//! The Bend 2 backend: prose-free Bend generated from the same linked IR as
//! the Lean and LaTeX outputs (I7, R8).
//!
//! A theorem lowers to a Bend `law` and the `def` that proves it; a
//! document definition to a typed `def`. Proofs are explicit terms
//! (`proof.rs`), since Bend has no tactics, and every argument Lean
//! inferred is computed by the engine (`engine.rs`), since Bend infers
//! almost nothing. The closed syntax of `syntax.rs` is the only thing the
//! backend can print.
//!
//! Disclosed lowering decisions:
//!
//! - **Sorts.** `Prop` lowers to Bend `Type` and `Type` to Bend `Data`:
//!   LexLean's value types are first-order data, which Bend lets a proof
//!   reuse only at kind `Data`.
//! - **Quantities.** A binder whose type is `Data` is marked `+`, a sort
//!   binder `-`, every other binder is affine. Bend's kernel is affine by
//!   construction (its consistency rests on it), so a function-typed
//!   hypothesis may be used once per branch; a proof that needs it twice
//!   is refused by the Bend checker and remapped to its source.
//! - **Assumptions.** An external constant the prelude registers as an
//!   assumption (`Classical.em`) is not an axiom: the theorem using it takes
//!   the assumption as a leading template premise (`~ll_excluded_middle`),
//!   visible in its statement, and every theorem citing it inherits the
//!   premise.
//! - **Leading introductions.** `intro` steps at the head of a proof become
//!   further `for` clauses of the law: a curried statement is the same
//!   proposition, and a Bend `match` may inspect only a parameter.

pub mod engine;
pub mod linarith;
pub mod prelude;
pub mod proof;
pub mod semantic;
pub mod syntax;

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::engine::{fail, module_alias, premise_name, Ctx, Engine, ProjectIndex};
use crate::backend::bend::prelude::{registry, PRELUDE_ALIAS, PRELUDE_BUILD_PATH};
use crate::backend::bend::proof::{flatten, index_spans, ProofLowering};
use crate::backend::bend::syntax::{
    print_module, BTerm, Body, Import, Item, Module, Name, Param, Quantity, Tail,
};
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::subst;
use crate::ir::declaration::{DeclBody, Declaration};
use crate::ir::proof::Proof;
use crate::ir::term::{LocalId, Term};
use crate::link::CheckedModule;
use crate::source::coverage::Origin;

/// Bend's reserved words: a generated name equal to one cannot be a
/// definition name.
const RESERVED: &[&str] = &[
    "as", "case", "def", "do", "exs", "for", "import", "is", "law", "match", "return", "type",
    "where",
];

/// Assumption premises every theorem needs, by `(module, component)`, as
/// `(name, Bend type)` in name order. Filled in module dependency order,
/// so a theorem's premises are known before any citing theorem lowers.
pub type AssumptionTable = BTreeMap<(String, String), Vec<(String, String)>>;

/// Whether a module lowers to Bend: language-1.0 document modules.
#[must_use]
pub fn lowers(checked: &CheckedModule) -> bool {
    let document = &checked.document;
    document.core.is_none() && document.semantic.is_none() && document.tooling.is_none()
}

/// The build-relative path of a generated module's `.bend`.
#[must_use]
pub fn module_path(generated: &str) -> String {
    format!("modules/{}.bend", generated.replace('.', "/"))
}

/// The relative import path from one build-relative file to another.
pub(crate) fn relative(from: &str, to: &str) -> String {
    let from_dir: Vec<&str> = {
        let mut parts: Vec<&str> = from.split('/').collect();
        parts.pop();
        parts
    };
    let to_parts: Vec<&str> = to.split('/').collect();
    let common = from_dir
        .iter()
        .zip(&to_parts)
        .take_while(|(a, b)| a == b)
        .count();
    let ups = from_dir.len() - common;
    let rest = to_parts[common..].join("/");
    if ups == 0 {
        format!("./{rest}")
    } else {
        format!("{}{rest}", "../".repeat(ups))
    }
}

fn origin_source(range: (usize, usize)) -> EmitSource {
    EmitSource::File(range.0, range.1)
}

/// The stack a semantic module's lowering runs on. The lowering and the
/// normalizer recurse over terms and certificates whose depth the source,
/// not the host, decides, so they do not run on whatever stack the caller
/// happens to have (a test thread has 2 MiB); the reservation is virtual.
const LOWERING_STACK: usize = 256 << 20;

/// Run `work` on a thread with [`LOWERING_STACK`] bytes of stack.
fn on_lowering_stack<T: Send>(work: impl FnOnce() -> T + Send) -> Result<T, Diagnostic> {
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .stack_size(LOWERING_STACK)
            .spawn_scoped(scope, work)
            .map_err(|error| {
                Diagnostic::new(
                    code!("LLS8002"),
                    format!(
                        "a stack of {LOWERING_STACK} bytes for lowering a semantic module to Bend could not be reserved: {error}"
                    ),
                )
            })?;
        handle.join().map_err(|_| {
            Diagnostic::new(
                code!("LLI9001"),
                "phase render: the Bend lowering of a semantic module panicked",
            )
        })
    })
}

/// Render one language-1.0 module's canonical `.bend` (§18 as amended for
/// Bend) through a tracing emitter, recording the assumption premises of
/// its theorems in `table`.
///
/// # Errors
///
/// `LLB6008` when a construct has no Bend lowering.
pub fn render_module(
    checked: &CheckedModule,
    project: &ProjectIndex<'_>,
    table: &mut AssumptionTable,
) -> Result<(Emitter, bool), Diagnostic> {
    let registry = registry()?;
    let document = &checked.document;
    let mut engine = Engine::new(project, registry, &document.name);
    engine.assumption_table = std::mem::take(table);
    let mut items = Vec::new();
    for declaration in document.declarations() {
        if RESERVED.contains(&declaration.lean_name.as_str()) {
            return Err(fail(format!(
                "the declaration name `{}` is a Bend reserved word",
                declaration.lean_name
            )));
        }
        let origin = checked
            .decl_origins
            .get(&declaration.component)
            .ok_or_else(|| {
                fail(format!(
                    "declaration `{}` has no source origin",
                    declaration.component
                ))
            })?;
        engine.start_declaration();
        match &declaration.body {
            DeclBody::TheoremLike { statement, proof } => {
                let mut lowered = theorem(&mut engine, declaration, statement, proof, origin)?;
                items.append(&mut lowered);
                let premises: Vec<(String, String)> = engine
                    .assumptions
                    .iter()
                    .map(|(name, ty)| (name.clone(), ty.clone()))
                    .collect();
                engine.assumption_table.insert(
                    (document.name.clone(), declaration.component.clone()),
                    premises,
                );
            }
            DeclBody::Definition { ty, value, .. } => {
                items.push(definition(&mut engine, declaration, ty, value, origin)?);
            }
        }
    }
    *table = std::mem::take(&mut engine.assumption_table);
    let own_path = module_path(&document.lean_module);
    let mut imports = Vec::new();
    let uses_prelude = engine.uses_prelude;
    if uses_prelude {
        imports.push(Import {
            path: relative(&own_path, PRELUDE_BUILD_PATH),
            alias: PRELUDE_ALIAS.to_owned(),
        });
    }
    let mut aliases = BTreeSet::new();
    let referenced: BTreeSet<String> = document
        .imports
        .iter()
        .cloned()
        .chain(engine.referenced_modules.iter().cloned())
        .collect();
    for module in referenced {
        let generated = project
            .generated_modules
            .get(&module)
            .cloned()
            .ok_or_else(|| fail(format!("imported module `{module}` is not linked")))?;
        let alias = module_alias(&generated);
        if !aliases.insert(alias.clone()) || alias == PRELUDE_ALIAS {
            return Err(fail(format!(
                "the import alias `{alias}` of `{generated}` collides with another import"
            )));
        }
        imports.push(Import {
            path: relative(&own_path, &module_path(&generated)),
            alias,
        });
    }
    let module = Module { imports, items };
    let mut emitter = Emitter::new();
    print_module(&module, &mut emitter);
    Ok((emitter, uses_prelude))
}

/// Lower a theorem to its auxiliary definitions and its law.
fn theorem(
    engine: &mut Engine<'_>,
    declaration: &Declaration,
    statement: &Term,
    proof: &Proof,
    origin: &crate::link::DeclOrigin,
) -> Result<Vec<Item>, Diagnostic> {
    let mut ctx: Ctx = Vec::new();
    let mut binders: Vec<(LocalId, Term, EmitSource)> = Vec::new();
    for binder in &declaration.params {
        engine.term_binder(binder.id);
        ctx.push((binder.id, binder.ty.clone()));
        binders.push((binder.id, binder.ty.clone(), origin_source(origin.sentence)));
    }
    // Lifted leading universal binders, exactly as the Lean lowering lifts
    // them (§18.5).
    let mut goal = statement.clone();
    while let Term::Pi {
        binders: group,
        body,
    } = &goal
    {
        if !group.iter().all(|binder| !binder.spelling.is_empty()) {
            break;
        }
        for binder in group {
            engine.term_binder(binder.id);
            ctx.push((binder.id, binder.ty.clone()));
            binders.push((binder.id, binder.ty.clone(), origin_source(origin.sentence)));
        }
        goal = (**body).clone();
    }
    let mut spans = BTreeMap::new();
    index_spans(proof, &origin.steps, &mut spans);
    let mut steps = flatten(proof);
    // Leading introductions become law clauses.
    while let Some(Proof::Intro(ids)) = steps.first().copied() {
        let step_source = spans
            .get(&(std::ptr::from_ref(steps[0]) as usize))
            .copied()
            .unwrap_or(origin.whole);
        let mut lifted = true;
        let mut probe = goal.clone();
        let mut peeled = Vec::new();
        for id in ids {
            let normal = match &probe {
                Term::Pi { .. } => probe.clone(),
                other => engine.whnf(other)?,
            };
            let Term::Pi {
                binders: group,
                body,
            } = normal
            else {
                lifted = false;
                break;
            };
            let mut group = group.into_iter();
            let Some(first) = group.next() else {
                lifted = false;
                break;
            };
            let remaining: Vec<_> = group.collect();
            let rest = if remaining.is_empty() {
                *body
            } else {
                Term::Pi {
                    binders: remaining,
                    body,
                }
            };
            let mut map = BTreeMap::new();
            map.insert(first.id, Term::Local(*id));
            probe = subst(&rest, &map);
            peeled.push((*id, first.ty));
        }
        if !lifted {
            break;
        }
        for (id, ty) in peeled {
            engine.proof_binder(id);
            ctx.push((id, ty.clone()));
            binders.push((id, ty, origin_source(step_source)));
        }
        goal = probe;
        steps.remove(0);
    }
    let owner = declaration.lean_name.clone();
    let mut lowering =
        ProofLowering::new(engine, owner, spans, origin.proof.unwrap_or(origin.whole));
    let body = lowering.prove(&ctx, &goal, &steps)?;
    let mut auxiliary = std::mem::take(&mut lowering.auxiliary);
    let mut params = Vec::new();
    for (index, (id, ty, source)) in binders.iter().enumerate() {
        let prefix: Ctx = ctx[..index].to_vec();
        let mut param = lowering.param(&prefix, *id, ty)?;
        param.source = source.clone();
        params.push(param);
    }
    let claim = engine.lower(&ctx, &goal, None)?;
    // Assumption premises lead the law's clauses.
    let premises: Vec<(String, String)> = engine
        .assumptions
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect();
    let mut body = body;
    if !premises.is_empty() {
        let premise_params: Vec<Param> = premises
            .iter()
            .map(|(name, ty)| Param {
                quantity: Quantity::Affine,
                name: Name::synthetic(premise_name(name)),
                ty: BTerm::Call(
                    Name::synthetic(format!("{PRELUDE_ALIAS}.{}", ty.trim_end_matches("()"))),
                    Vec::new(),
                ),
                source: origin_source(origin.sentence),
            })
            .collect();
        engine.uses_prelude = true;
        // A premise reaches exactly the auxiliaries that use it, directly or
        // through a call: it is affine, so passing it to one that does not
        // would spend it twice.
        let premise_texts: BTreeSet<String> = premises
            .iter()
            .map(|(name, _)| premise_name(name))
            .collect();
        let mut needing: BTreeSet<String> = BTreeSet::new();
        loop {
            let before = needing.len();
            for item in &auxiliary {
                if let Item::Def { name, body, .. } = item {
                    if !needing.contains(&name.text)
                        && (body_names(body)
                            .iter()
                            .any(|used| premise_texts.contains(used))
                            || body_names(body).iter().any(|used| needing.contains(used)))
                    {
                        needing.insert(name.text.clone());
                    }
                }
            }
            if needing.len() == before {
                break;
            }
        }
        let premise_args: Vec<BTerm> = premises
            .iter()
            .map(|(name, _)| BTerm::Name(Name::synthetic(premise_name(name))))
            .collect();
        for item in &mut auxiliary {
            if let Item::Def {
                name, params, body, ..
            } = item
            {
                if needing.contains(&name.text) {
                    let mut with = premise_params.clone();
                    with.append(params);
                    *params = with;
                }
                thread_body(body, &needing, &premise_args);
            }
        }
        thread_body(&mut body, &needing, &premise_args);
        let mut with = premise_params;
        with.append(&mut params);
        params = with;
    }
    let mut items = auxiliary;
    items.push(Item::Law {
        name: Name::new(
            declaration.lean_name.clone(),
            Origin::Reference {
                module: engine.module.clone(),
                component: declaration.component.clone(),
            },
        ),
        params,
        claim,
        claim_source: origin_source(origin.sentence),
        proof: body,
        source: origin_source(origin.whole),
    });
    Ok(items)
}

/// Every name a body mentions in live position: variables and call heads.
fn body_names(body: &Body) -> BTreeSet<String> {
    fn term(t: &BTerm, out: &mut BTreeSet<String>) {
        match t {
            BTerm::Name(name) => {
                out.insert(name.text.clone());
            }
            BTerm::Call(head, args) => {
                out.insert(head.text.clone());
                for arg in args {
                    term(arg, out);
                }
            }
            BTerm::Lam(_, inner) | BTerm::Succ(inner) => term(inner, out),
            BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
                term(a, out);
                term(b, out);
            }
            BTerm::Constructor(_, fields) => {
                for field in fields {
                    term(field, out);
                }
            }
            BTerm::Block(inner) => out.extend(body_names(inner)),
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    for stmt in &body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, .. } => term(proof, &mut out),
            syntax::Stmt::Let { value, .. } | syntax::Stmt::Share { value, .. } => {
                term(value, &mut out);
            }
        }
    }
    match &body.tail {
        Tail::Term(t, _) => term(t, &mut out),
        Tail::Match { cases, .. } => {
            for (_, case) in cases {
                out.extend(body_names(case));
            }
        }
    }
    out
}

/// Pass the assumption premises to every call of an auxiliary definition
/// that takes them.
fn thread_body(body: &mut Body, aux: &BTreeSet<String>, premises_args: &[BTerm]) {
    for stmt in &mut body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, motive, .. } => {
                thread_term(proof, aux, premises_args);
                thread_term(motive, aux, premises_args);
            }
            syntax::Stmt::Let { value, .. } | syntax::Stmt::Share { value, .. } => {
                thread_term(value, aux, premises_args);
            }
        }
    }
    match &mut body.tail {
        Tail::Term(term, _) => thread_term(term, aux, premises_args),
        Tail::Match { cases, .. } => {
            for (_, case) in cases {
                thread_body(case, aux, premises_args);
            }
        }
    }
}

fn thread_term(term: &mut BTerm, aux: &BTreeSet<String>, premises_args: &[BTerm]) {
    match term {
        BTerm::Call(head, args) => {
            for arg in args.iter_mut() {
                thread_term(arg, aux, premises_args);
            }
            if aux.contains(&head.text) {
                let mut with = premises_args.to_vec();
                with.append(args);
                *args = with;
            }
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) | BTerm::Template(body) => {
            thread_term(body, aux, premises_args);
        }
        BTerm::Apply(function, args) => {
            thread_term(function, aux, premises_args);
            for arg in args {
                thread_term(arg, aux, premises_args);
            }
        }
        BTerm::Pi {
            domain, codomain, ..
        }
        | BTerm::Sigma {
            domain, codomain, ..
        } => {
            thread_term(domain, aux, premises_args);
            thread_term(codomain, aux, premises_args);
        }
        BTerm::Product(a, b) | BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
            thread_term(a, aux, premises_args);
            thread_term(b, aux, premises_args);
        }
        BTerm::Equal(a, b, t) => {
            thread_term(a, aux, premises_args);
            thread_term(b, aux, premises_args);
            thread_term(t, aux, premises_args);
        }
        BTerm::Datatype(_, _, args) | BTerm::Constructor(_, args) => {
            for arg in args {
                thread_term(arg, aux, premises_args);
            }
        }
        BTerm::Block(body) => thread_body(body, aux, premises_args),
        BTerm::Name(_)
        | BTerm::Refl
        | BTerm::U32(_)
        | BTerm::Nat(_)
        | BTerm::Kind(_)
        | BTerm::Hole
        | BTerm::Str(_) => {}
    }
}

/// Lower a document definition to a typed Bend `def`.
fn definition(
    engine: &mut Engine<'_>,
    declaration: &Declaration,
    ty: &Term,
    value: &Term,
    origin: &crate::link::DeclOrigin,
) -> Result<Item, Diagnostic> {
    let mut ctx: Ctx = Vec::new();
    let mut binders = Vec::new();
    for binder in &declaration.params {
        engine.term_binder(binder.id);
        ctx.push((binder.id, binder.ty.clone()));
        binders.push((binder.id, binder.ty.clone()));
    }
    // Lift lambda binders that mirror the signature's leading binders
    // (§18.6), renaming the type's binders to the value's.
    let (result_ty, body) = match (ty, value) {
        (
            Term::Pi {
                binders: type_binders,
                body: type_body,
            },
            Term::Lambda {
                binders: value_binders,
                body: value_body,
            },
        ) if value_binders.len() == type_binders.len() => {
            let map: BTreeMap<LocalId, Term> = type_binders
                .iter()
                .zip(value_binders)
                .map(|(from, to)| (from.id, Term::Local(to.id)))
                .collect();
            for binder in value_binders {
                engine.term_binder(binder.id);
                ctx.push((binder.id, binder.ty.clone()));
                binders.push((binder.id, binder.ty.clone()));
            }
            (subst(type_body, &map), (**value_body).clone())
        }
        _ => (ty.clone(), value.clone()),
    };
    let mut lowering = ProofLowering::new(
        engine,
        declaration.lean_name.clone(),
        BTreeMap::new(),
        origin.whole,
    );
    let mut params = Vec::new();
    for (index, (id, binder_ty)) in binders.iter().enumerate() {
        let prefix: Ctx = ctx[..index].to_vec();
        let mut param = lowering.param(&prefix, *id, binder_ty)?;
        param.source = origin_source(origin.sentence);
        params.push(param);
    }
    // A predicate whose proposition is `Data` (built from equations)
    // returns `Data`, so its proofs stay reusable where it is used.
    let result_normal = engine.whnf(&result_ty)?;
    let result = if matches!(result_normal, Term::Sort(crate::ir::term::Universe::Num(0)))
        && engine.is_data(&ctx, &body)
    {
        BTerm::Kind("Data")
    } else {
        engine.lower(&ctx, &result_ty, None)?
    };
    let lowered = engine.lower(&ctx, &body, Some(&result_ty))?;
    if !engine.assumptions.is_empty() {
        return Err(fail(
            "a definition uses an assumption, which only a theorem may take as a premise",
        ));
    }
    Ok(Item::Def {
        name: Name::new(
            declaration.lean_name.clone(),
            Origin::Reference {
                module: engine.module.clone(),
                component: declaration.component.clone(),
            },
        ),
        params,
        result,
        result_source: origin_source(origin.sentence),
        body: Body::term(lowered, origin_source(origin.sentence)),
        source: origin_source(origin.whole),
    })
}

/// The prelude bytes and their build path, for a build whose modules
/// import it.
///
/// # Errors
///
/// An internal diagnostic when the prelude is not embedded.
pub fn prelude_artifact() -> Result<(&'static str, &'static [u8]), Diagnostic> {
    Ok((PRELUDE_BUILD_PATH, prelude::prelude_bytes()?))
}

/// Every lowering module's Bend emitter, in name order, rendered in
/// import order so cited theorems' assumption premises are known first;
/// and whether any of them imports the prelude.
///
/// # Errors
///
/// `LLB6008` when a construct has no Bend lowering.
pub fn render_project(
    language: &str,
    modules: &BTreeMap<String, CheckedModule>,
    closure: &crate::lexicon::resolve::Closure,
) -> Result<RenderedBend, Diagnostic> {
    if !crate::lowers_to_bend(language) {
        return Ok(RenderedBend::default());
    }
    let mut declarations = BTreeMap::new();
    let mut generated_modules = BTreeMap::new();
    for (name, checked) in modules {
        generated_modules.insert(name.clone(), checked.document.lean_module.clone());
        for declaration in checked.document.declarations() {
            declarations.insert((name.clone(), declaration.component.clone()), declaration);
        }
    }
    let project = ProjectIndex {
        closure,
        declarations,
        generated_modules,
    };
    // Import order: a module after every module it imports.
    let mut order: Vec<&String> = Vec::new();
    let mut placed: BTreeSet<&String> = BTreeSet::new();
    while order.len() < modules.len() {
        let before = order.len();
        for (name, checked) in modules {
            if placed.contains(name) {
                continue;
            }
            if checked
                .document
                .imports
                .iter()
                .all(|import| placed.contains(import) || !modules.contains_key(import))
            {
                order.push(name);
                placed.insert(name);
            }
        }
        if order.len() == before {
            return Err(fail("the module import graph has a cycle"));
        }
    }
    let mut table = AssumptionTable::new();
    let mut out = BTreeMap::new();
    let mut any_prelude = false;
    let mut supports = BTreeSet::new();
    let semantic_project = semantic::SemanticProject::new(modules);
    for name in order {
        let checked = &modules[name];
        // Language 2.2 lowers each semantic module through its own
        // lowering (§18.11); a document module lowers as in language 2.0.
        if let Some(module) = &checked.document.semantic {
            if crate::is_surface_1_2(language) {
                let (emitter, uses_prelude, used) = on_lowering_stack(|| {
                    semantic::render_module(checked, module, &semantic_project, name)
                })??;
                any_prelude |= uses_prelude;
                supports.extend(used);
                out.insert(name.clone(), emitter);
            }
            continue;
        }
        if !lowers(checked) {
            continue;
        }
        let (emitter, uses_prelude) = render_module(checked, &project, &mut table)?;
        any_prelude |= uses_prelude;
        out.insert(name.clone(), emitter);
    }
    let mut premises = BTreeMap::new();
    for ((module, component), names) in table {
        let declaration = project
            .declarations
            .get(&(module.clone(), component.clone()));
        let generated = project.generated_modules.get(&module);
        if let (Some(declaration), Some(generated)) = (declaration, generated) {
            premises.insert(
                format!("{generated}.{}", declaration.lean_name),
                names.into_iter().map(|(name, _)| name).collect(),
            );
        }
    }
    Ok(RenderedBend {
        emitters: out,
        uses_prelude: any_prelude,
        supports,
        premises,
    })
}

/// The Bend side of one rendered build.
#[derive(Debug, Default)]
pub struct RenderedBend {
    /// Each lowering module's emitter, by source module name.
    pub emitters: BTreeMap<String, Emitter>,
    /// Whether any module imports the prelude.
    pub uses_prelude: bool,
    /// Language 2.2: the support modules any module imports.
    pub supports: BTreeSet<semantic::support::Support>,
    /// The assumption premises of every theorem, by full generated name.
    pub premises: BTreeMap<String, Vec<String>>,
}
