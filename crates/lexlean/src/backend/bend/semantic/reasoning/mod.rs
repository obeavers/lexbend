//! Bend lowering of the theorems a reasoning declaration generates
//! (§17.12, *Reasoning machines* rule 9; §18.11.8).
//!
//! Each generated theorem becomes a `law` whose `for` clauses are its type
//! parameters, its parameters, and the premises of its statement, as an
//! ordinary theorem's are (see `proof`). Its proof is the Bend counterpart
//! of the fixed Lean template that proves it: a proof term instantiating
//! one of `Reasoning.bend`'s generic laws, or a case analysis over the
//! definitions the declaration elaborated to (see `engine`). Bend's kernel
//! checks every one, as Lean's checks the Lean templates.
//!
//! A generic law takes its step, predicate, and hypothesis as closed
//! templates, which the kernel types only through named heads. So a fold
//! or loop step is the code definition the elaborated definition already
//! folds with (see `closure`), and each predicate and hypothesis a proof
//! term passes is a definition below the theorem, generic in its type
//! parameters, taking the theorem's parameters as one environment.

mod engine;
mod folds;
mod generate;
mod lemmas;
mod search;
mod templates;

use std::collections::BTreeMap;

use super::proof::peel;
use super::support::Support;
use super::{here, names, synthetic, var, Lower, Scope};
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Item, Name, Param, Quantity};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::reasoning::{Formula, GeneratedTheorem, Helper};
use crate::ir::semantic::{SemanticParameter, SemanticTerm, SemanticType};
use crate::source::coverage::Origin;

use engine::{plain, Engine, Entry, State};

pub(super) use engine::plain_item;

/// Lower the theorems one reasoning declaration generates.
///
/// # Errors
///
/// `LLB6008` naming the theorem whose proof has no Bend lowering.
pub(super) fn theorems(
    lower: &mut Lower<'_, '_>,
    theorems: &[GeneratedTheorem],
) -> Result<Vec<Item>, Diagnostic> {
    if theorems.is_empty() {
        return Ok(Vec::new());
    }
    lower.supports.insert(Support::Reasoning);
    for required in Support::Reasoning.requires() {
        lower.supports.insert(*required);
    }
    lower.uses_prelude = true;
    let mut items = Vec::new();
    for theorem in theorems {
        let lowered = theorem_items(lower, theorem, theorems).map_err(|mut diagnostic| {
            diagnostic.message = format!(
                "the generated theorem `{}` has no Bend proof: {}",
                theorem.name, diagnostic.message
            );
            diagnostic
        })?;
        for item in &lowered {
            lower.know(item);
        }
        items.extend(lowered);
    }
    Ok(items)
}

/// What a generated theorem's proof may name: the theorem, its scope, and
/// the Bend names of its parameters and premises.
pub(super) struct Context<'t> {
    pub theorem: &'t GeneratedTheorem,
    /// The theorems the same declaration generates, which a template may
    /// introduce as hypotheses.
    pub siblings: &'t [GeneratedTheorem],
    pub scope: Scope,
    /// The value parameters, as spelled, with their Bend types.
    pub values: Vec<(String, BTerm)>,
    /// The premises' Bend names.
    pub premises: Vec<String>,
}

fn theorem_items(
    lower: &mut Lower<'_, '_>,
    theorem: &GeneratedTheorem,
    siblings: &[GeneratedTheorem],
) -> Result<Vec<Item>, Diagnostic> {
    let spelled = names::global(&theorem.name)?;
    let mut params = lower.type_params(&theorem.type_parameters)?;
    let type_params = theorem
        .type_parameters
        .iter()
        .map(|name| names::local(name))
        .collect::<Result<Vec<_>, _>>()?;
    let (binders, premises, claim) = peel_formula(&theorem.statement);
    let all: Vec<SemanticParameter> = theorem.parameters.iter().chain(&binders).cloned().collect();
    let order: Vec<usize> = (0..all.len()).collect();
    let (values, scope) = lower.value_params(&all, &order)?;
    let mut state = State::new(var("Unit"));
    let mut value_names = Vec::new();
    for param in &values {
        let ty = plain(&param.ty);
        state.entries.push(Entry {
            name: param.name.text.clone(),
            ty: ty.clone(),
            value: true,
        });
        value_names.push((param.name.text.clone(), ty));
    }
    params.extend(values);
    let mut premise_names = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        let name = format!("ll_h{index}");
        let ty = plain(&formula_type(lower, premise, &scope)?);
        params.push(Param {
            quantity: if lower.prop_is_data(&ty) {
                Quantity::Reusable
            } else {
                Quantity::Affine
            },
            name: synthetic(name.clone()),
            ty: ty.clone(),
            source: here(),
        });
        state.push_hypothesis(&name, ty);
        premise_names.push(name);
    }
    let claim_type = plain(&formula_type(lower, &claim, &scope)?);
    state.goal = claim_type.clone();
    let context = Context {
        theorem,
        siblings,
        scope,
        values: value_names,
        premises: premise_names,
    };
    let mut engine = Engine::new(lower, spelled.clone(), type_params);
    let proof = templates::prove(&mut engine, &context, &state, &claim)?;
    engine.flush();
    let mut items = std::mem::take(&mut engine.items);
    items.push(Item::Law {
        name: Name::new(
            spelled,
            Origin::Synthetic(crate::backend::bend::syntax::SYNTAX_ORIGIN.to_owned()),
        ),
        params,
        claim: claim_type,
        claim_source: here(),
        proof,
        source: here(),
    });
    Ok(items)
}

/// A statement split into the universal binders before its first premise,
/// its premises in order, and the claim after them.
pub(super) fn peel_formula(statement: &Formula) -> (Vec<SemanticParameter>, Vec<Formula>, Formula) {
    let mut binders = Vec::new();
    let mut premises = Vec::new();
    let mut current = statement.clone();
    loop {
        match current {
            Formula::Implies {
                premise,
                conclusion,
            } => {
                premises.push(*premise);
                current = *conclusion;
            }
            Formula::Term { term } => {
                // A binder after a premise stays in the claim: moving it
                // before the premise would change the arguments a citation
                // passes.
                if !premises.is_empty() && matches!(term, SemanticTerm::Forall { .. }) {
                    return (binders, premises, Formula::Term { term });
                }
                let peeled = peel(&term);
                binders.extend(peeled.binders);
                premises.extend(
                    peeled
                        .premises
                        .into_iter()
                        .map(|premise| Formula::Term { term: premise }),
                );
                return (binders, premises, Formula::Term { term: peeled.claim });
            }
            other => return (binders, premises, other),
        }
    }
}

/// The Bend proposition a generated statement denotes.
pub(super) fn formula_type(
    lower: &mut Lower<'_, '_>,
    formula: &Formula,
    scope: &Scope,
) -> Result<BTerm, Diagnostic> {
    match formula {
        Formula::Term { term } => lower.term(term, scope),
        Formula::Helper { helper, arguments } => helper_type(lower, *helper, arguments, scope),
        Formula::Implies {
            premise,
            conclusion,
        } => Ok(BTerm::Pi {
            name: None,
            erased: false,
            domain: Box::new(formula_type(lower, premise, scope)?),
            codomain: Box::new(formula_type(lower, conclusion, scope)?),
        }),
        Formula::True => Ok(var("Unit")),
    }
}

/// A runtime name, which makes the module import the runtime.
fn runtime(lower: &mut Lower<'_, '_>, name: &str) -> String {
    lower.uses_prelude = true;
    lower.supports.insert(Support::Runtime);
    format!("{}.LexLeanReasoning.{name}", Support::Runtime.alias())
}

/// The Bend type a `LexLeanReasoning` predicate denotes: the runtime's, or
/// `Reasoning.bend`'s `SearchOk`, whose `Found` projects pairs the way the
/// semantic lowering does.
fn helper_type(
    lower: &mut Lower<'_, '_>,
    helper: Helper,
    arguments: &[SemanticTerm],
    scope: &Scope,
) -> Result<BTerm, Diagnostic> {
    let mut lowered = Vec::new();
    for argument in arguments {
        lowered.push(lower.term(argument, scope)?);
    }
    let type_of = |lower: &mut Lower<'_, '_>, index: usize| -> Result<SemanticType, Diagnostic> {
        let argument = arguments
            .get(index)
            .ok_or_else(|| fail(format!("`{}` lost an argument", helper.lean())))?;
        Ok(lower.canonical(&lower.infer(argument, scope)?))
    };
    let function_domain = |ty: &SemanticType, index: usize| match ty {
        SemanticType::Function { parameters, .. } => parameters.get(index).cloned(),
        _ => None,
    };
    let missing = || {
        fail(format!(
            "`{}` has arguments of an unexpected type",
            helper.lean()
        ))
    };
    match helper {
        Helper::Star => {
            let state = type_of(lower, 1)?;
            let state = lower.ty(&state)?;
            let mut args = vec![state];
            args.extend(lowered);
            Ok(BTerm::Datatype(
                synthetic(runtime(lower, "Star")),
                Vec::new(),
                args,
            ))
        }
        Helper::Reaches => {
            let state = type_of(lower, 1)?;
            let state = lower.ty(&state)?;
            let held = type_of(lower, 2)?;
            let SemanticType::Result { error, .. } = held else {
                return Err(missing());
            };
            let error = lower.ty(&error)?;
            let mut args = vec![state, error];
            args.extend(lowered);
            Ok(super::call(runtime(lower, "Reaches"), args))
        }
        Helper::All => {
            let SemanticType::List { element } = type_of(lower, 1)? else {
                return Err(missing());
            };
            let element = lower.ty(&element)?;
            let mut args = vec![element];
            args.extend(lowered);
            Ok(super::call(runtime(lower, "All"), args))
        }
        Helper::Preserves => {
            let relation = type_of(lower, 0)?;
            let state = function_domain(&relation, 0).ok_or_else(missing)?;
            let state = lower.ty(&state)?;
            let mut args = vec![state];
            args.extend(lowered);
            Ok(super::call(runtime(lower, "Preserves"), args))
        }
        Helper::Sound | Helper::Complete => {
            let check = type_of(lower, 0)?;
            let subject = function_domain(&check, 0).ok_or_else(missing)?;
            let candidate = function_domain(&check, 1).ok_or_else(missing)?;
            let mut args = vec![lower.ty(&subject)?, lower.ty(&candidate)?];
            args.extend(lowered);
            let name = if helper == Helper::Sound {
                "Sound"
            } else {
                "Complete"
            };
            Ok(super::call(runtime(lower, name), args))
        }
        Helper::SearchOk => {
            let SemanticType::List { element } = type_of(lower, 2)? else {
                return Err(missing());
            };
            let accept = type_of(lower, 1)?;
            let SemanticType::Function { result, .. } = accept else {
                return Err(missing());
            };
            let SemanticType::Option { value } = *result else {
                return Err(missing());
            };
            let mut args = vec![lower.ty(&element)?, lower.ty(&value)?];
            args.extend(lowered);
            Ok(super::call("RS.SearchOk", args))
        }
    }
}

/// A theorem's parameters as one environment value, its type, and the
/// statements rebinding each parameter from `env`: what a predicate or
/// hypothesis definition below the theorem takes as `k`.
pub(super) fn environment(
    lower: &mut Lower<'_, '_>,
    context: &Context<'_>,
    env: &BTerm,
) -> (BTerm, BTerm, Vec<crate::backend::bend::syntax::Stmt>) {
    let captured: Vec<(String, BTerm, BTerm)> = context
        .values
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone(), var(name.clone())))
        .collect();
    let (ty, value) = lower.tuple(&captured);
    let stmts = lower.rebinding(&captured, env);
    (plain(&ty), plain(&value), stmts)
}

/// The theorem's parameters as one environment value and its type, with
/// each parameter's projection from `env`: the substitution a definition
/// below the theorem applies to what it states. Substituting, rather than
/// rebinding each parameter by name, keeps one name for each parameter in
/// the definitions a split detaches from it.
pub(super) fn projections(
    lower: &mut Lower<'_, '_>,
    context: &Context<'_>,
    skip: Option<&str>,
    env: &BTerm,
) -> (BTerm, BTerm, BTreeMap<String, BTerm>) {
    let captured: Vec<(String, BTerm, BTerm)> = context
        .values
        .iter()
        .filter(|(name, _)| Some(name.as_str()) != skip)
        .map(|(name, ty)| (name.clone(), ty.clone(), var(name.clone())))
        .collect();
    let (ty, value) = lower.tuple(&captured);
    let map = lower
        .rebinding(&captured, env)
        .into_iter()
        .filter_map(|stmt| match stmt {
            crate::backend::bend::syntax::Stmt::Share { name, value, .. } => {
                Some((name.text, value))
            }
            _ => None,
        })
        .collect();
    (plain(&ty), plain(&value), map)
}

/// A map from one name.
pub(super) fn one(name: &str, value: BTerm) -> BTreeMap<String, BTerm> {
    let mut map = BTreeMap::new();
    map.insert(name.to_owned(), value);
    map
}
