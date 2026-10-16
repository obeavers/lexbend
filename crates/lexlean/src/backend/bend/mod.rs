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
pub mod prelude;
pub mod proof;
pub mod syntax;

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::engine::{fail, module_alias, premise_name, Ctx, Engine, ProjectIndex};
use crate::backend::bend::prelude::{registry, PRELUDE_ALIAS, PRELUDE_BUILD_PATH};
use crate::backend::bend::proof::{flatten, index_spans, ProofLowering};
use crate::backend::bend::syntax::{
    print_module, BTerm, Body, Import, Item, Module, Name, Param, Quantity, Tail,
};
use crate::backend::{EmitSource, Emitter};
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

/// Which leading parameters of each generated definition are templates,
/// by `Alias.name` (the alias is the generated module's import alias).
pub type TemplateTable = BTreeMap<String, Vec<bool>>;

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
fn relative(from: &str, to: &str) -> String {
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

/// Render one language-1.0 module's canonical `.bend` (§18 as amended for
/// Bend) through a tracing emitter, recording the assumption premises of
/// its theorems in `table`.
///
/// # Errors
///
/// `LLB6001` when a construct has no Bend lowering.
pub fn render_module(
    checked: &CheckedModule,
    project: &ProjectIndex<'_>,
    table: &mut AssumptionTable,
    templates: &mut TemplateTable,
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
        let origin = checked.decl_origins.get(&declaration.component).ok_or_else(|| {
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
                engine
                    .assumption_table
                    .insert((document.name.clone(), declaration.component.clone()), premises);
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
    let own_alias = module_alias(&document.lean_module);
    templatize(&mut items, &own_alias, templates);
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
    let mut lowering = ProofLowering::new(engine, owner, spans, origin.proof.unwrap_or(origin.whole));
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
    // Assumption premises lead, as Bend requires of template clauses.
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
                quantity: Quantity::Template,
                name: Name::synthetic(premise_name(name)),
                ty: BTerm::Call(
                    Name::synthetic(format!(
                        "{PRELUDE_ALIAS}.{}",
                        ty.trim_end_matches("()")
                    )),
                    Vec::new(),
                ),
                source: origin_source(origin.sentence),
            })
            .collect();
        engine.uses_prelude = true;
        let aux_names: BTreeSet<String> = auxiliary
            .iter()
            .map(|item| match item {
                Item::Def { name, .. } | Item::Law { name, .. } => name.text.clone(),
            })
            .collect();
        let template_args: Vec<(bool, BTerm)> = premises
            .iter()
            .map(|(name, _)| (true, BTerm::Name(Name::synthetic(premise_name(name)))))
            .collect();
        for item in &mut auxiliary {
            if let Item::Def { params, body, .. } = item {
                let mut with = premise_params.clone();
                with.append(params);
                *params = with;
                thread_body(body, &aux_names, &template_args);
            }
        }
        thread_body(&mut body, &aux_names, &template_args);
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

/// Pass the assumption premises to every call of an auxiliary definition.
fn thread_body(body: &mut Body, aux: &BTreeSet<String>, templates: &[(bool, BTerm)]) {
    for stmt in &mut body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, motive, .. } => {
                thread_term(proof, aux, templates);
                thread_term(motive, aux, templates);
            }
            syntax::Stmt::Let { value, .. } => thread_term(value, aux, templates),
        }
    }
    match &mut body.tail {
        Tail::Term(term, _) => thread_term(term, aux, templates),
        Tail::Match { cases, .. } => {
            for (_, case) in cases {
                thread_body(case, aux, templates);
            }
        }
    }
}

fn thread_term(term: &mut BTerm, aux: &BTreeSet<String>, templates: &[(bool, BTerm)]) {
    match term {
        BTerm::Call(head, args) => {
            for (_, arg) in args.iter_mut() {
                thread_term(arg, aux, templates);
            }
            if aux.contains(&head.text) {
                let mut with = templates.to_vec();
                with.append(args);
                *args = with;
            }
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) => thread_term(body, aux, templates),
        BTerm::Pi {
            domain, codomain, ..
        }
        | BTerm::Sigma {
            domain, codomain, ..
        } => {
            thread_term(domain, aux, templates);
            thread_term(codomain, aux, templates);
        }
        BTerm::Product(a, b) | BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
            thread_term(a, aux, templates);
            thread_term(b, aux, templates);
        }
        BTerm::Equal(a, b, t) => {
            thread_term(a, aux, templates);
            thread_term(b, aux, templates);
            thread_term(t, aux, templates);
        }
        BTerm::Datatype(_, _, args) | BTerm::Constructor(_, args) => {
            for arg in args {
                thread_term(arg, aux, templates);
            }
        }
        BTerm::Block(body) => thread_body(body, aux, templates),
        BTerm::Name(_) | BTerm::Refl | BTerm::Nat(_) | BTerm::Kind(_) | BTerm::Hole => {}
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
    let mut lowering = ProofLowering::new(engine, declaration.lean_name.clone(), BTreeMap::new(), origin.whole);
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
/// `LLB6001` when a construct has no Bend lowering.
pub fn render_project(
    modules: &BTreeMap<String, CheckedModule>,
    closure: &crate::lexicon::resolve::Closure,
) -> Result<(BTreeMap<String, Emitter>, bool), Diagnostic> {
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
    let mut templates = TemplateTable::new();
    let mut out = BTreeMap::new();
    let mut any_prelude = false;
    for name in order {
        let checked = &modules[name];
        if !lowers(checked) {
            continue;
        }
        let (emitter, uses_prelude) = render_module(checked, &project, &mut table, &mut templates)?;
        any_prelude |= uses_prelude;
        out.insert(name.clone(), emitter);
    }
    Ok((out, any_prelude))
}

/// Bend's kernel is affine: a function-typed parameter may be used once
/// per branch. A parameter a definition uses more than once is made a
/// template (`~`), which Bend substitutes at compile time and so may copy;
/// Bend requires templates to lead, so every parameter before it becomes
/// one too, and a caller passes those arguments as templates, which makes
/// the caller's own parameter a template in turn. Iterated to a fixpoint
/// over the module, against the masks of modules lowered before it.
fn templatize(items: &mut [Item], own_alias: &str, table: &mut TemplateTable) {
    loop {
        let mut changed = false;
        for index in 0..items.len() {
            let (name, params, body) = match &items[index] {
                Item::Law {
                    name, params, proof, ..
                } => (name.text.clone(), params.clone(), proof.clone()),
                Item::Def {
                    name, params, body, ..
                } => (name.text.clone(), params.clone(), body.clone()),
            };
            let mut need = vec![false; params.len()];
            for (position, param) in params.iter().enumerate() {
                if param.quantity == Quantity::Affine && count_body(&body, &param.name.text) > 1 {
                    need[position] = true;
                }
            }
            let mut passed = BTreeSet::new();
            calls_body(&body, own_alias, table, &mut passed);
            for (position, param) in params.iter().enumerate() {
                if passed.contains(&param.name.text) {
                    need[position] = true;
                }
            }
            let Some(last) = need.iter().rposition(|flag| *flag) else {
                continue;
            };
            let mask: Vec<bool> = (0..params.len()).map(|position| position <= last).collect();
            let key = format!("{own_alias}.{name}");
            if table.get(&key) != Some(&mask) {
                table.insert(key, mask.clone());
                changed = true;
            }
            let params = match &mut items[index] {
                Item::Law { params, .. } | Item::Def { params, .. } => params,
            };
            for (param, template) in params.iter_mut().zip(&mask) {
                if *template && param.quantity != Quantity::Template {
                    param.quantity = Quantity::Template;
                    changed = true;
                }
            }
        }
        // Mark template arguments at every call site.
        for item in items.iter_mut() {
            let body = match item {
                Item::Law { proof, .. } => proof,
                Item::Def { body, .. } => body,
            };
            changed |= mark_body(body, own_alias, table);
        }
        if !changed {
            return;
        }
    }
}

fn mask_for<'t>(head: &str, own_alias: &str, table: &'t TemplateTable) -> Option<&'t Vec<bool>> {
    table
        .get(head)
        .or_else(|| table.get(&format!("{own_alias}.{head}")))
}

fn count_body(body: &Body, name: &str) -> usize {
    let mut count = 0;
    for stmt in &body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, motive, .. } => {
                count += count_term(proof, name) + count_term(motive, name);
            }
            syntax::Stmt::Let { value, .. } => count += count_term(value, name),
        }
    }
    match &body.tail {
        Tail::Term(term, _) => count += count_term(term, name),
        // Arms are alternatives: a name used once in each arm is used once.
        Tail::Match { cases, .. } => {
            count += cases
                .iter()
                .map(|(_, case)| count_body(case, name))
                .max()
                .unwrap_or(0);
        }
    }
    count
}

fn count_term(term: &BTerm, name: &str) -> usize {
    match term {
        BTerm::Name(found) => usize::from(found.text == name),
        BTerm::Call(head, args) => {
            usize::from(head.text == name)
                + args.iter().map(|(_, arg)| count_term(arg, name)).sum::<usize>()
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) => count_term(body, name),
        // Types are dead: a use there is not a use.
        BTerm::Pi { .. } | BTerm::Sigma { .. } | BTerm::Product(..) | BTerm::Datatype(..) | BTerm::Equal(..) | BTerm::Kind(_) => 0,
        BTerm::Pair(a, b) => count_term(a, name) + count_term(b, name),
        BTerm::Ann(value, _) => count_term(value, name),
        BTerm::Constructor(_, fields) => fields.iter().map(|field| count_term(field, name)).sum(),
        BTerm::Block(body) => count_body(body, name),
        BTerm::Refl | BTerm::Nat(_) | BTerm::Hole => 0,
    }
}

fn calls_body(body: &Body, own_alias: &str, table: &TemplateTable, out: &mut BTreeSet<String>) {
    for stmt in &body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, .. } => calls_term(proof, own_alias, table, out),
            syntax::Stmt::Let { value, .. } => calls_term(value, own_alias, table, out),
        }
    }
    match &body.tail {
        Tail::Term(term, _) => calls_term(term, own_alias, table, out),
        Tail::Match { cases, .. } => {
            for (_, case) in cases {
                calls_body(case, own_alias, table, out);
            }
        }
    }
}

fn calls_term(term: &BTerm, own_alias: &str, table: &TemplateTable, out: &mut BTreeSet<String>) {
    match term {
        BTerm::Call(head, args) => {
            if let Some(mask) = mask_for(&head.text, own_alias, table) {
                // Assumption premises lead a call; the mask covers the
                // parameters after them only when the counts agree.
                let offset = args.iter().take_while(|(template, _)| *template).count();
                let offset = if args.len() == mask.len() { 0 } else { offset };
                for (position, template) in mask.iter().enumerate() {
                    if *template {
                        if let Some((_, BTerm::Name(name))) = args.get(position + offset) {
                            out.insert(name.text.clone());
                        }
                    }
                }
            }
            for (_, arg) in args {
                calls_term(arg, own_alias, table, out);
            }
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) => calls_term(body, own_alias, table, out),
        BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
            calls_term(a, own_alias, table, out);
            calls_term(b, own_alias, table, out);
        }
        BTerm::Constructor(_, fields) => {
            for field in fields {
                calls_term(field, own_alias, table, out);
            }
        }
        BTerm::Block(body) => calls_body(body, own_alias, table, out),
        _ => {}
    }
}

fn mark_body(body: &mut Body, own_alias: &str, table: &TemplateTable) -> bool {
    let mut changed = false;
    for stmt in &mut body.stmts {
        match stmt {
            syntax::Stmt::Rewrite { proof, .. } => changed |= mark_term(proof, own_alias, table),
            syntax::Stmt::Let { value, .. } => changed |= mark_term(value, own_alias, table),
        }
    }
    match &mut body.tail {
        Tail::Term(term, _) => changed |= mark_term(term, own_alias, table),
        Tail::Match { cases, .. } => {
            for (_, case) in cases {
                changed |= mark_body(case, own_alias, table);
            }
        }
    }
    changed
}

fn mark_term(term: &mut BTerm, own_alias: &str, table: &TemplateTable) -> bool {
    let mut changed = false;
    match term {
        BTerm::Call(head, args) => {
            if let Some(mask) = mask_for(&head.text, own_alias, table).cloned() {
                let leading = args.iter().take_while(|(template, _)| *template).count();
                let offset = if args.len() == mask.len() { 0 } else { leading };
                for (position, template) in mask.iter().enumerate() {
                    if *template {
                        if let Some(slot) = args.get_mut(position + offset) {
                            if !slot.0 {
                                slot.0 = true;
                                changed = true;
                            }
                        }
                    }
                }
            }
            for (_, arg) in args.iter_mut() {
                changed |= mark_term(arg, own_alias, table);
            }
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) => changed |= mark_term(body, own_alias, table),
        BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
            changed |= mark_term(a, own_alias, table);
            changed |= mark_term(b, own_alias, table);
        }
        BTerm::Constructor(_, fields) => {
            for field in fields {
                changed |= mark_term(field, own_alias, table);
            }
        }
        BTerm::Block(body) => changed |= mark_body(body, own_alias, table),
        _ => {}
    }
    changed
}
