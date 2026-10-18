//! Case analysis over the emitted Bend definitions: the Bend counterpart of
//! the Lean templates' `dsimp only [f] at h; split at h; cases h`.
//!
//! A proof under construction is a [`State`]: the locals and hypotheses it
//! may use, each with its Bend type, and the goal. [`Engine::whnf`] unfolds
//! exactly the definitions a template names, the auxiliaries their
//! lowering introduced (`ll_match`, code definitions, continuations), and
//! `if`, pair projections, and matches on known constructors, so a
//! hypothesis's left side either becomes a constructor or sticks on a
//! match or `if` over some term. [`Engine::split`] proves the goal in a
//! fresh definition that takes that term as a parameter (with the equation
//! naming it), so the definition's `match` refines every hypothesis and the
//! goal, as Lean's `split` does. [`Engine::auto`] splits a hypothesis until
//! its left side is a constructor, refuting each branch whose constructor
//! clashes with the right side and reading the payload off the others.

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Name, Param, Pattern, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::source::coverage::Origin;

use super::super::{call, here, synthetic, var, Lower};

/// How far one normalization unfolds before it gives up: a bound, so a
/// definition the engine should not have unfolded cannot loop.
const LIMIT: usize = 512;

/// How many nested splits one proof makes before it gives up: a template's
/// case analysis is a few levels deep, so more is a split that refines
/// nothing.
const DEPTH: usize = 32;

/// One local or hypothesis of a proof under construction.
#[derive(Clone, Debug)]
pub(super) struct Entry {
    pub name: String,
    pub ty: BTerm,
    /// A local value, rather than a proof.
    pub value: bool,
}

/// One split a proof passed through, outermost first.
#[derive(Clone, Debug)]
pub(super) struct Taken {
    /// The term split on, as it stood before the split.
    pub scrutinee: BTerm,
    /// The constructor of the branch taken.
    pub constructor: String,
    /// Its payload's locals.
    pub binders: Vec<String>,
    /// The equation `scrutinee == constructor{binders}`, when the
    /// scrutinee was generalized.
    pub en: Option<String>,
}

/// A proof under construction.
#[derive(Clone, Debug)]
pub(super) struct State {
    /// Values first, then hypotheses, so a `match` on a value refines every
    /// hypothesis after it.
    pub entries: Vec<Entry>,
    pub goal: BTerm,
    pub path: Vec<Taken>,
    /// The terms entries not yet bound stand for: a hypothesis a template
    /// introduces (Lean's `have`) is passed to the next definition the
    /// proof opens, which binds it.
    pub given: BTreeMap<String, BTerm>,
}

impl State {
    pub(super) fn new(goal: BTerm) -> Self {
        Self {
            entries: Vec::new(),
            goal,
            path: Vec::new(),
            given: BTreeMap::new(),
        }
    }

    /// Add a hypothesis proved by `proof`, bound by the next definition.
    pub(super) fn have(&mut self, name: &str, ty: BTerm, proof: BTerm) {
        self.push_hypothesis(name, ty);
        self.given.insert(name.to_owned(), proof);
    }

    /// The type of the entry `name`.
    pub(super) fn type_of(&self, name: &str) -> Result<BTerm, Diagnostic> {
        Ok(self.entry(name)?.ty.clone())
    }

    /// The entry's type replaced, as conversion allows.
    pub(super) fn retype(&mut self, name: &str, ty: BTerm) {
        for entry in &mut self.entries {
            if entry.name == name {
                entry.ty = ty.clone();
            }
        }
    }
    pub(super) fn entry(&self, name: &str) -> Result<&Entry, Diagnostic> {
        self.entries
            .iter()
            .find(|entry| entry.name == name)
            .ok_or_else(|| fail(format!("a proof lost its local `{name}`")))
    }

    /// Add a local value before the hypotheses.
    pub(super) fn push_value(&mut self, name: &str, ty: BTerm) {
        let at = self
            .entries
            .iter()
            .position(|entry| !entry.value)
            .unwrap_or(self.entries.len());
        self.entries.insert(
            at,
            Entry {
                name: name.to_owned(),
                ty,
                value: true,
            },
        );
    }

    pub(super) fn push_hypothesis(&mut self, name: &str, ty: BTerm) {
        self.entries.push(Entry {
            name: name.to_owned(),
            ty,
            value: false,
        });
    }

    /// Every occurrence of `from` in the goal and the types of the entries
    /// `targets` names (every entry when it names none) replaced by `to`.
    fn replaced_in(&self, from: &BTerm, to: &BTerm, targets: Option<&[String]>) -> Self {
        let mut out = self.replaced(from, to);
        if let Some(targets) = targets {
            for (entry, old) in out.entries.iter_mut().zip(&self.entries) {
                if !entry.value && !targets.contains(&entry.name) {
                    entry.ty = old.ty.clone();
                }
            }
        }
        out
    }

    /// Every occurrence of `from` in a type or the goal replaced by `to`.
    fn replaced(&self, from: &BTerm, to: &BTerm) -> Self {
        Self {
            entries: self
                .entries
                .iter()
                .map(|entry| Entry {
                    name: entry.name.clone(),
                    ty: replace(&entry.ty, from, to),
                    value: entry.value,
                })
                .collect(),
            goal: replace(&self.goal, from, to),
            path: self.path.clone(),
            given: self.given.clone(),
        }
    }

    /// The state inside a definition that binds every entry.
    fn bound(&self) -> Self {
        let mut inner = self.clone();
        inner.given.clear();
        inner
    }
}

/// What normalizing a term reached.
#[derive(Clone, Debug)]
// Each value is matched where it is made and never stored, so boxing its
// large variant would buy nothing.
#[allow(clippy::large_enum_variant)]
pub(super) enum Whnf {
    /// A constructor, literal, or pair.
    Value(BTerm),
    /// A `match` or `if` on `scrutinee`, which reaches no constructor; `term`
    /// is the reduced term it stands in, and `ty` the scrutinee's type.
    Stuck {
        term: BTerm,
        scrutinee: BTerm,
        ty: BTerm,
    },
    /// Anything else, reduced as far as it goes.
    Opaque(BTerm),
}

impl Whnf {
    pub(super) fn term(&self) -> &BTerm {
        match self {
            Self::Value(term) | Self::Opaque(term) | Self::Stuck { term, .. } => term,
        }
    }
}

/// What [`Engine::auto`] hands a leaf.
pub(super) enum Leaf {
    /// The hypothesis's left side reached the right side's constructor; the
    /// goal already has the right side's payload replaced by the left's,
    /// which is given.
    Value(Vec<BTerm>),
    /// The left side reached a term no unfolding reduces further.
    Opaque(BTerm),
}

#[allow(clippy::large_enum_variant)]
enum Step {
    Reduced(BTerm),
    /// A match on `scrutinee` reaches no constructor. When the match is on
    /// a term that itself reduced to a stuck match, `inner` replaces that
    /// term by its reduct, so the stuck term names the scrutinee.
    Stuck {
        scrutinee: BTerm,
        ty: BTerm,
        inner: Option<(BTerm, BTerm)>,
    },
    Normal,
}

/// The split engine of one generated theorem.
pub(super) struct Engine<'x, 'p, 'a> {
    pub lower: &'x mut Lower<'p, 'a>,
    /// The theorem's Bend name: every definition it adds is below it.
    pub owner: String,
    /// The theorem's type parameters, as spelled.
    pub type_params: Vec<String>,
    /// The definitions besides auxiliaries that normalization unfolds.
    pub unfold: BTreeSet<String>,
    /// Whether a goal equation is normalized before each split, so the
    /// split generalizes its scrutinee there too (Lean's `dsimp` of the
    /// goal before a `rw`).
    pub normalize_goal: bool,
    /// The definitions the proof adds, in dependency order.
    pub items: Vec<Item>,
    /// The types of the hypotheses lambdas the proof builds bind, by their
    /// Bend names, which a lemma reading its hypothesis's type looks up.
    pub hyp_types: BTreeMap<String, BTerm>,
    /// Whether normalization unfolds every emitted definition: a lemma
    /// reading the fold its argument computes looks through the
    /// definitions the elaboration wraps it in.
    pub unfold_all: bool,
    count: usize,
}

impl<'x, 'p, 'a> Engine<'x, 'p, 'a> {
    pub(super) fn new(
        lower: &'x mut Lower<'p, 'a>,
        owner: String,
        type_params: Vec<String>,
    ) -> Self {
        Self {
            lower,
            owner,
            type_params,
            unfold: BTreeSet::new(),
            normalize_goal: false,
            items: Vec::new(),
            hyp_types: BTreeMap::new(),
            unfold_all: false,
            count: 0,
        }
    }

    /// A fresh definition name below the theorem.
    pub(super) fn below(&mut self, stem: &str) -> String {
        let name = format!("{}.ll_{stem}{}", self.owner, self.count);
        self.count += 1;
        name
    }

    /// A fresh local name.
    pub(super) fn fresh(&mut self, stem: &str) -> String {
        self.lower.fresh(stem)
    }

    /// The theorem's type parameters as template arguments.
    pub(super) fn templates(&self) -> Vec<BTerm> {
        self.type_params
            .iter()
            .map(|name| BTerm::Template(Box::new(var(name.clone()))))
            .collect()
    }

    /// The theorem's type parameters as `~T: Data` binders.
    pub(super) fn template_params(&self) -> Vec<Param> {
        self.type_params
            .iter()
            .map(|name| Param {
                quantity: Quantity::Template,
                name: synthetic(name.clone()),
                ty: BTerm::Kind("Data"),
                source: here(),
            })
            .collect()
    }

    /// Whether normalization unfolds `name`: a definition the template
    /// names, or an auxiliary the lowering introduced inside one.
    fn unfoldable(&self, name: &str) -> bool {
        if self.unfold_all || self.unfold.contains(name) {
            return true;
        }
        let last = name.rsplit('.').next().unwrap_or(name);
        let numbered = |stem: &str| {
            last.strip_prefix(stem)
                .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
        };
        if numbered("ll_match") || numbered("ll_code") || numbered("ll_k") || last == "ll_code" {
            return true;
        }
        // A record's field accessor: `Type.field` below a record type.
        name.rsplit_once('.').is_some_and(|(owner, _)| {
            matches!(
                self.lower.emitted.get(owner),
                Some(Item::Type { constructors, .. }) if constructors.len() == 1
            )
        })
    }

    fn definition(&self, name: &str) -> Option<&Item> {
        self.lower
            .emitted
            .get(name)
            .filter(|item| matches!(item, Item::Def { .. }))
    }

    /// Normalize `term` to a constructor, a stuck match, or an opaque head.
    pub(super) fn whnf(&self, term: &BTerm) -> Whnf {
        let mut current = term.clone();
        for _ in 0..LIMIT {
            match self.step(&current) {
                Step::Reduced(next) => current = next,
                Step::Stuck {
                    scrutinee,
                    ty,
                    inner,
                } => {
                    let term = match inner {
                        Some((from, to)) => replace(&current, &from, &to),
                        None => current,
                    };
                    return Whnf::Stuck {
                        term,
                        scrutinee,
                        ty,
                    };
                }
                Step::Normal => {
                    return match current {
                        BTerm::Constructor(..)
                        | BTerm::Nat(_)
                        | BTerm::Succ(_)
                        | BTerm::Pair(..)
                        | BTerm::Refl => Whnf::Value(current),
                        other => Whnf::Opaque(other),
                    }
                }
            }
        }
        Whnf::Opaque(current)
    }

    fn step(&self, term: &BTerm) -> Step {
        match term {
            BTerm::Ann(inner, _) => Step::Reduced((**inner).clone()),
            BTerm::Call(head, args) => self.step_call(&head.text, args),
            BTerm::Apply(function, args) => match &**function {
                BTerm::Lam(binder, body) if !args.is_empty() => {
                    let mut map = BTreeMap::new();
                    map.insert(bound(&binder.text), args[0].clone());
                    let reduced = subst(body, &map);
                    if args.len() == 1 {
                        Step::Reduced(reduced)
                    } else {
                        Step::Reduced(BTerm::Apply(Box::new(reduced), args[1..].to_vec()))
                    }
                }
                _ => Step::Normal,
            },
            BTerm::Block(body) => self.evaluate(body, BTreeMap::new(), BTreeMap::new()),
            _ => Step::Normal,
        }
    }

    fn step_call(&self, head: &str, args: &[BTerm]) -> Step {
        let semantic = |name: &str| head == format!("S.Sem.{name}");
        if semantic("ite") && args.len() == 4 {
            return match self.whnf(&args[1]) {
                Whnf::Value(BTerm::Constructor(name, _)) if name.text == "True" => {
                    Step::Reduced(args[2].clone())
                }
                Whnf::Value(BTerm::Constructor(name, _)) if name.text == "False" => {
                    Step::Reduced(args[3].clone())
                }
                Whnf::Stuck {
                    term,
                    scrutinee,
                    ty,
                } => Step::Stuck {
                    scrutinee,
                    ty,
                    inner: Some((args[1].clone(), term)),
                },
                other => Step::Stuck {
                    scrutinee: other.term().clone(),
                    ty: var("Bool"),
                    inner: Some((args[1].clone(), other.term().clone())),
                },
            };
        }
        if (semantic("fst") || semantic("snd")) && args.len() == 3 {
            return match self.whnf(&args[2]) {
                Whnf::Value(BTerm::Pair(first, second)) => {
                    Step::Reduced(if semantic("fst") { *first } else { *second })
                }
                Whnf::Stuck {
                    term,
                    scrutinee,
                    ty,
                } => Step::Stuck {
                    scrutinee,
                    ty,
                    inner: Some((args[2].clone(), term)),
                },
                _ => Step::Normal,
            };
        }
        if !self.unfoldable(head) {
            return Step::Normal;
        }
        let Some(Item::Def { params, body, .. }) = self.definition(head) else {
            return Step::Normal;
        };
        if params.len() != args.len() {
            return Step::Normal;
        }
        let mut map = BTreeMap::new();
        let mut types = BTreeMap::new();
        for (param, arg) in params.iter().zip(args) {
            let value = match arg {
                BTerm::Template(inner) => (**inner).clone(),
                other => other.clone(),
            };
            map.insert(param.name.text.clone(), value);
        }
        for param in params {
            types.insert(param.name.text.clone(), subst(&param.ty, &map));
        }
        self.evaluate(body, map, types)
    }

    /// Run a definition body under `map`, the values of its parameters and
    /// locals, whose types `types` records.
    fn evaluate(
        &self,
        body: &Body,
        mut map: BTreeMap<String, BTerm>,
        mut types: BTreeMap<String, BTerm>,
    ) -> Step {
        for stmt in &body.stmts {
            match stmt {
                Stmt::Share { name, value, .. } | Stmt::Let { name, value, .. } => {
                    let value = subst(value, &map);
                    map.insert(bound(&name.text), value);
                }
                Stmt::Rewrite { .. } => return Step::Normal,
            }
        }
        match &body.tail {
            Tail::Term(term, _) => Step::Reduced(subst(term, &map)),
            Tail::Match {
                scrutinee, cases, ..
            } => {
                let value = map
                    .get(&scrutinee.text)
                    .cloned()
                    .unwrap_or_else(|| var(scrutinee.text.clone()));
                let ty = types
                    .get(&scrutinee.text)
                    .cloned()
                    .unwrap_or_else(|| var("ll_unknown"));
                let reached = match self.whnf(&value) {
                    Whnf::Value(reached) => reached,
                    Whnf::Stuck {
                        term,
                        scrutinee,
                        ty,
                    } => {
                        return Step::Stuck {
                            scrutinee,
                            ty,
                            inner: Some((value, term)),
                        }
                    }
                    // A record or pair has one constructor: a match on an
                    // opaque one projects it, which splitting cannot refine,
                    // so the term stays as it is (Lean's `split` does not
                    // split a structure either).
                    Whnf::Opaque(_) if self.single(&ty) => return Step::Normal,
                    Whnf::Opaque(reached) => {
                        return Step::Stuck {
                            scrutinee: reached.clone(),
                            ty,
                            inner: Some((value, reached)),
                        }
                    }
                };
                for (pattern, case) in cases {
                    let Some(bindings) = select(pattern, &reached) else {
                        continue;
                    };
                    let fields = self.fields(&ty, pattern);
                    for (index, (name, value)) in bindings.into_iter().enumerate() {
                        if let Some(field) = fields.as_ref().and_then(|fields| fields.get(index)) {
                            types.insert(name.clone(), field.clone());
                        }
                        map.insert(name, value);
                    }
                    return self.evaluate(case, map, types);
                }
                Step::Normal
            }
        }
    }

    /// The constructors of `ty` with the types of their fields: Base's
    /// `Maybe`, `Result`, `List`, `Bool`, `Nat`, the prelude's pairs, and
    /// the module's own types.
    pub(super) fn constructors(
        &self,
        ty: &BTerm,
    ) -> Result<Vec<(Pattern, Vec<BTerm>)>, Diagnostic> {
        let plain = |name: &str, fields: Vec<BTerm>| {
            let binders = (0..fields.len())
                .map(|i| synthetic(format!("ll_f{i}")))
                .collect();
            (Pattern::Constructor(synthetic(name), binders), fields)
        };
        match ty {
            BTerm::Name(name) if name.text == "Bool" => {
                Ok(vec![plain("True", Vec::new()), plain("False", Vec::new())])
            }
            BTerm::Name(name) if name.text == "Nat" => Ok(vec![
                (Pattern::Zero, Vec::new()),
                (Pattern::Succ(synthetic("ll_f0")), vec![var("Nat")]),
            ]),
            BTerm::Datatype(name, _, args) if name.text == "Maybe" && args.len() == 1 => Ok(vec![
                plain("None", Vec::new()),
                plain("Some", vec![args[0].clone()]),
            ]),
            BTerm::Datatype(name, _, args) if name.text == "Result" && args.len() == 2 => Ok(vec![
                plain("Fail", vec![args[0].clone()]),
                plain("Done", vec![args[1].clone()]),
            ]),
            BTerm::Datatype(name, _, args) if name.text == "List" && args.len() == 1 => Ok(vec![
                plain("Nil", Vec::new()),
                plain("Con", vec![args[0].clone(), ty.clone()]),
            ]),
            BTerm::Call(name, args) if name.text == "L.Lean.Prod" && args.len() == 2 => Ok(vec![(
                Pattern::Pair(synthetic("ll_f0"), synthetic("ll_f1")),
                args.clone(),
            )]),
            BTerm::Datatype(name, _, _) | BTerm::Name(name)
                if self
                    .lower
                    .emitted
                    .get(&name.text)
                    .is_some_and(|item| matches!(item, Item::Type { .. })) =>
            {
                let args = match ty {
                    BTerm::Datatype(_, _, args) => args.clone(),
                    _ => Vec::new(),
                };
                let Some(Item::Type {
                    parameters,
                    index: None,
                    constructors,
                    ..
                }) = self.lower.emitted.get(&name.text)
                else {
                    return Err(fail(format!(
                        "a generated proof splits a value of `{}`, whose constructors it does not know",
                        name.text
                    )));
                };
                let map: BTreeMap<String, BTerm> = parameters
                    .iter()
                    .map(|parameter| parameter.text.clone())
                    .zip(args.iter().cloned())
                    .collect();
                Ok(constructors
                    .iter()
                    .map(|(constructor, fields)| {
                        plain(
                            &constructor.text,
                            fields.iter().map(|(_, ty)| subst(ty, &map)).collect(),
                        )
                    })
                    .collect())
            }
            other => Err(fail(format!(
                "a generated proof splits a value of a type it cannot read: {other:?}"
            ))),
        }
    }

    /// Whether `ty` has exactly one constructor: a record or a pair.
    fn single(&self, ty: &BTerm) -> bool {
        self.constructors(ty)
            .is_ok_and(|constructors| constructors.len() == 1)
    }

    fn fields(&self, ty: &BTerm, pattern: &Pattern) -> Option<Vec<BTerm>> {
        let constructors = self.constructors(ty).ok()?;
        constructors
            .into_iter()
            .find(|(candidate, _)| same_constructor(candidate, pattern))
            .map(|(_, fields)| fields)
    }

    /// Prove `state.goal` by a `match` on `scrutinee`, of type `ty`, in a
    /// fresh definition. The scrutinee is generalized to a parameter, with
    /// the equation naming it, unless it is a local already. Returns the
    /// call proving the goal.
    pub(super) fn split(
        &mut self,
        state: &State,
        scrutinee: &BTerm,
        ty: &BTerm,
        branch: &mut dyn FnMut(&mut Self, State) -> Result<Body, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        self.split_at(state, scrutinee, ty, None, branch)
    }

    /// [`Engine::split`], generalizing the scrutinee only in the goal and
    /// the hypotheses `targets` names, when it names any: Lean's `split at
    /// h` restates `h` alone, and a hypothesis left stated over the
    /// scrutinee is still what it was.
    pub(super) fn split_at(
        &mut self,
        state: &State,
        scrutinee: &BTerm,
        ty: &BTerm,
        targets: Option<&[String]>,
        branch: &mut dyn FnMut(&mut Self, State) -> Result<Body, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let name = self.below("split");
        let local = match scrutinee {
            BTerm::Name(local)
                if state
                    .entries
                    .iter()
                    .any(|e| e.value && e.name == local.text) =>
            {
                Some(local.text.clone())
            }
            _ => None,
        };
        let (inner, matched, en, mut arguments) = match local {
            Some(local) => (state.bound(), local, None, BTreeMap::new()),
            None => {
                let m = self.fresh("m");
                let en = self.fresh("en");
                let mut inner = state
                    .replaced_in(scrutinee, &var(m.clone()), targets)
                    .bound();
                inner.push_value(&m, ty.clone());
                inner.push_hypothesis(
                    &en,
                    BTerm::Equal(
                        Box::new(scrutinee.clone()),
                        Box::new(var(m.clone())),
                        Box::new(ty.clone()),
                    ),
                );
                let mut arguments = BTreeMap::new();
                arguments.insert(m.clone(), scrutinee.clone());
                arguments.insert(en.clone(), BTerm::Refl);
                (inner, m, Some(en), arguments)
            }
        };
        for (name, proof) in &state.given {
            arguments
                .entry(name.clone())
                .or_insert_with(|| proof.clone());
        }
        let mut cases = Vec::new();
        for (pattern, fields) in self.constructors(ty)? {
            let mut binders = Vec::new();
            let (pattern, value) = match pattern {
                Pattern::Zero => (Pattern::Zero, BTerm::Nat("0".to_owned())),
                Pattern::Succ(_) => {
                    let b = self.fresh("b");
                    binders.push(b.clone());
                    (
                        Pattern::Succ(synthetic(b.clone())),
                        BTerm::Succ(Box::new(var(b))),
                    )
                }
                Pattern::Pair(..) => {
                    let first = self.fresh("b");
                    let second = self.fresh("b");
                    binders.push(first.clone());
                    binders.push(second.clone());
                    (
                        Pattern::Pair(synthetic(first.clone()), synthetic(second.clone())),
                        BTerm::Pair(Box::new(var(first)), Box::new(var(second))),
                    )
                }
                Pattern::Constructor(constructor, names) => {
                    for _ in &names {
                        binders.push(self.fresh("b"));
                    }
                    (
                        Pattern::Constructor(
                            constructor.clone(),
                            binders.iter().map(|b| synthetic(b.clone())).collect(),
                        ),
                        BTerm::Constructor(
                            constructor.clone(),
                            binders.iter().map(|b| var(b.clone())).collect(),
                        ),
                    )
                }
            };
            let mut taken = inner.replaced(&var(matched.clone()), &value);
            // The matched local is its constructor now, everywhere.
            taken.entries.retain(|entry| entry.name != matched);
            for (binder, field) in binders.iter().zip(fields) {
                taken.push_value(binder, field);
            }
            taken.path.push(Taken {
                scrutinee: scrutinee.clone(),
                constructor: constructor_name(&pattern),
                binders: binders.clone(),
                en: en.clone(),
            });
            let body = branch(self, taken)?;
            cases.push((pattern, body));
        }
        let mut params = self.template_params();
        let mut args = self.templates();
        for entry in &inner.entries {
            params.push(Param {
                quantity: self.quantity(entry),
                name: synthetic(entry.name.clone()),
                ty: entry.ty.clone(),
                source: here(),
            });
            args.push(
                arguments
                    .get(&entry.name)
                    .cloned()
                    .unwrap_or_else(|| var(entry.name.clone())),
            );
        }
        self.push(Item::Def {
            name: synthetic(name.clone()),
            params,
            result: inner.goal.clone(),
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic(matched),
                    cases,
                    source: here(),
                },
            },
            source: here(),
        });
        Ok(call(name, args))
    }

    /// Add a definition the proof needs, after the auxiliaries lowering
    /// its terms introduced, which it may name.
    pub(super) fn push(&mut self, item: Item) {
        self.flush();
        self.items.push(item);
    }

    /// Move the auxiliaries lowering introduced into the proof's items.
    pub(super) fn flush(&mut self) {
        let aux = std::mem::take(&mut self.lower.aux);
        for item in &aux {
            self.lower.know(item);
        }
        self.items.extend(aux);
    }

    /// A definition binding every entry of `state` and proving `goal` by
    /// `body`; returns its call.
    pub(super) fn detached(&mut self, stem: &str, state: &State, goal: BTerm, body: Body) -> BTerm {
        let name = self.below(stem);
        let mut params = self.template_params();
        let mut args = self.templates();
        // An affine hypothesis the body does not use stays with the caller,
        // which may still need it.
        let whole = BTerm::Block(Box::new(body.clone()));
        let unused = |entry: &Entry| {
            matches!(body.tail, Tail::Term(..)) && !mentions(&whole, &var(entry.name.clone()))
        };
        for entry in &state.entries {
            if self.quantity(entry) == Quantity::Affine && unused(entry) {
                continue;
            }
            params.push(Param {
                quantity: self.quantity(entry),
                name: synthetic(entry.name.clone()),
                ty: entry.ty.clone(),
                source: here(),
            });
            args.push(
                state
                    .given
                    .get(&entry.name)
                    .cloned()
                    .unwrap_or_else(|| var(entry.name.clone())),
            );
        }
        self.push(Item::Def {
            name: synthetic(name.clone()),
            params,
            result: goal,
            result_source: here(),
            body,
            source: here(),
        });
        call(name, args)
    }

    /// Prove the goal with `term`, of type `ty`, replaced everywhere by a
    /// fresh local (Lean's `generalize ... at`), in a definition that takes
    /// the local; `body` proves the goal over it. Returns the call.
    pub(super) fn generalize(
        &mut self,
        state: &State,
        term: &BTerm,
        ty: &BTerm,
        body: &mut dyn FnMut(&mut Self, State) -> Result<Body, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let local = self.fresh("g");
        let mut inner = state.replaced(term, &var(local.clone()));
        inner.push_value(&local, ty.clone());
        inner.given.insert(local.clone(), term.clone());
        let goal = inner.goal.clone();
        let mut bound = inner.bound();
        bound.path = state.path.clone();
        let proved = body(self, bound)?;
        Ok(self.detached("gen", &inner, goal, proved))
    }

    /// The result type of a call of a known definition or law.
    pub(super) fn result_type(&self, term: &BTerm) -> Result<BTerm, Diagnostic> {
        let BTerm::Call(head, args) = term else {
            return Err(fail(format!(
                "a generated proof needs the type of {term:?}"
            )));
        };
        let (params, result) = match self.lower.emitted.get(&head.text) {
            Some(Item::Def { params, result, .. }) => (params, result),
            Some(Item::Law { params, claim, .. }) => (params, claim),
            _ => {
                return Err(fail(format!(
                    "a generated proof needs the type of `{}`, which it does not know",
                    head.text
                )))
            }
        };
        let mut map = BTreeMap::new();
        for (param, arg) in params.iter().zip(args) {
            let value = match arg {
                BTerm::Template(inner) => (**inner).clone(),
                other => other.clone(),
            };
            map.insert(param.name.text.clone(), value);
        }
        Ok(subst(result, &map))
    }

    /// A citation that over-applies a law whose claim is a function: the
    /// law's own parameters, then the rest as an application.
    pub(super) fn applied_law(&self, head: &str, args: Vec<BTerm>) -> BTerm {
        match self.arity(head) {
            Some(arity) if arity < args.len() => {
                let (first, rest) = args.split_at(arity);
                BTerm::Apply(Box::new(call(head, first.to_vec())), rest.to_vec())
            }
            _ => call(head, args),
        }
    }

    /// Whether `name` is a known law, and how many parameters it takes.
    pub(super) fn arity(&self, name: &str) -> Option<usize> {
        match self.lower.emitted.get(name) {
            Some(Item::Law { params, .. } | Item::Def { params, .. }) => Some(params.len()),
            _ => None,
        }
    }

    /// The quantity a local or hypothesis is bound at.
    pub(super) fn quantity(&self, entry: &Entry) -> Quantity {
        if entry.value || self.lower.prop_is_data(&entry.ty) {
            Quantity::Reusable
        } else {
            Quantity::Affine
        }
    }

    /// The goal with each side of an equation normalized, so the term a
    /// split generalizes is visible there.
    fn normalized(&self, state: &State) -> State {
        let mut state = state.clone();
        if let BTerm::Equal(left, right, ty) = &state.goal {
            state.goal = BTerm::Equal(
                Box::new(self.whnf(left).term().clone()),
                Box::new(self.whnf(right).term().clone()),
                ty.clone(),
            );
        }
        state
    }

    /// Prove the goal from the hypothesis `subject`, an equation whose
    /// right side is a constructor: split its left side until it is a
    /// constructor or opaque, refute every clash, and hand each other
    /// branch to `leaf`.
    pub(super) fn auto(
        &mut self,
        state: &State,
        subject: &str,
        leaf: &mut dyn FnMut(&mut Self, &State, Leaf) -> Result<Body, Diagnostic>,
    ) -> Result<Body, Diagnostic> {
        let state = if self.normalize_goal {
            self.normalized(state)
        } else {
            state.clone()
        };
        if state.path.len() > DEPTH {
            return Err(fail(format!(
                "a generated proof splits `{subject}` more than {DEPTH} times"
            )));
        }
        let BTerm::Equal(left, right, ty) = state.entry(subject)?.ty.clone() else {
            return Err(fail(format!("`{subject}` is not an equation")));
        };
        match self.whnf(&left) {
            Whnf::Stuck {
                term: stuck,
                scrutinee,
                ty: scrutinee_type,
            } => {
                // The split generalizes the scrutinee where it occurs, so the
                // hypothesis is first restated over the term it reduced to,
                // which names it; conversion admits the restatement.
                if !mentions(&stuck, &scrutinee) {
                    return Err(fail(format!(
                        "a generated proof cannot split on {scrutinee:?}, which its hypothesis does not name"
                    )));
                }
                let mut state = state;
                state.retype(
                    subject,
                    BTerm::Equal(Box::new(stuck), right.clone(), ty.clone()),
                );
                let targets = [subject.to_owned()];
                let proof = self.split_at(
                    &state,
                    &scrutinee,
                    &scrutinee_type,
                    Some(&targets),
                    &mut |engine, taken| engine.auto(&taken, subject, &mut *leaf),
                )?;
                Ok(Body::term(proof, here()))
            }
            Whnf::Opaque(reached) => leaf(self, &state, Leaf::Opaque(reached)),
            Whnf::Value(reached) => {
                let target = self.whnf(&right).term().clone();
                if constructor_of(&reached) != constructor_of(&target) {
                    let proof = self.refute(&state.goal, &left, &target, &ty, subject)?;
                    return Ok(Body::term(proof, here()));
                }
                self.transport(&state, subject, &left, &reached, &target, &ty, leaf)
            }
        }
    }

    /// The proof of `goal` from the hypothesis `subject : {left == target}`
    /// whose left side reduces to another constructor than `target`'s.
    pub(super) fn refute(
        &mut self,
        goal: &BTerm,
        left: &BTerm,
        target: &BTerm,
        ty: &BTerm,
        subject: &str,
    ) -> Result<BTerm, Diagnostic> {
        let rs = |name: &str| format!("RS.{name}");
        let e = var(subject);
        let unit = BTerm::Constructor(synthetic("Unit"), Vec::new());
        let args = |head: &[BTerm], tail: &[BTerm]| {
            let mut out = head.to_vec();
            out.push(goal.clone());
            out.push(left.clone());
            out.extend_from_slice(tail);
            out.push(e.clone());
            out.push(unit.clone());
            out
        };
        match (ty, target) {
            (BTerm::Datatype(name, _, types), BTerm::Constructor(constructor, payload))
                if name.text == "Maybe" =>
            {
                if constructor.text == "Some" {
                    Ok(call(rs("notSome"), args(types, payload)))
                } else {
                    Ok(call(rs("notNone"), args(types, &[])))
                }
            }
            (BTerm::Datatype(name, _, types), BTerm::Constructor(constructor, payload))
                if name.text == "Result" =>
            {
                if constructor.text == "Done" {
                    Ok(call(rs("notDone"), args(types, payload)))
                } else {
                    Ok(call(rs("notFail"), args(types, payload)))
                }
            }
            (BTerm::Name(name), BTerm::Constructor(constructor, _)) if name.text == "Bool" => {
                if constructor.text == "True" {
                    Ok(call(rs("notTrue"), args(&[], &[])))
                } else {
                    Ok(call(rs("notFalse"), args(&[], &[])))
                }
            }
            _ => Err(fail(format!(
                "a generated proof cannot refute an equation onto {target:?} at {ty:?}"
            ))),
        }
    }

    /// Read the payload of `subject : {left == target}` off `reached`, the
    /// same constructor: the goal over the right side's payload becomes the
    /// goal over the left's, which `leaf` proves.
    #[allow(clippy::too_many_arguments)]
    fn transport(
        &mut self,
        state: &State,
        subject: &str,
        left: &BTerm,
        reached: &BTerm,
        target: &BTerm,
        ty: &BTerm,
        leaf: &mut dyn FnMut(&mut Self, &State, Leaf) -> Result<Body, Diagnostic>,
    ) -> Result<Body, Diagnostic> {
        let payload = payload_of(reached);
        let wanted = payload_of(target);
        if payload == wanted || wanted.is_empty() {
            return leaf(self, state, Leaf::Value(payload));
        }
        let (case, types) = match ty {
            BTerm::Datatype(name, _, types) if name.text == "Maybe" => ("someCase", types),
            BTerm::Datatype(name, _, types) if name.text == "Result" => ("doneCase", types),
            _ => {
                return Err(fail(format!(
                    "a generated proof cannot read a payload of {ty:?}"
                )))
            }
        };
        let element = types.last().cloned().unwrap_or_else(|| var("Unit"));
        let z = self.fresh("z");
        let motive = abstracted(&state.goal, &wanted[0], &var(z.clone()), &element);
        if motive == state.goal {
            return leaf(self, state, Leaf::Value(payload));
        }
        let mut inner = state.clone();
        let mut map = BTreeMap::new();
        map.insert(z.clone(), payload[0].clone());
        inner.goal = projected(&subst(&motive, &map));
        let body = leaf(self, &inner, Leaf::Value(payload))?;
        let mut args = types.clone();
        args.push(BTerm::Lam(synthetic(format!("+{z}")), Box::new(motive)));
        args.push(left.clone());
        args.push(wanted[0].clone());
        args.push(var(subject));
        args.push(block(body));
        Ok(Body::term(call(format!("RS.{case}"), args), here()))
    }

    /// Rewrite the goal's occurrences of `from` to `to`, given `proof :
    /// {from == to : ty}`: a rewrite turns `P(R)` into `P(L)` for
    /// `{L == R}`, so it rewrites with the flipped equation.
    pub(super) fn rewrite(
        &self,
        state: &mut State,
        stmts: &mut Vec<Stmt>,
        from: &BTerm,
        to: &BTerm,
        proof: BTerm,
        ty: &BTerm,
    ) {
        let motive = replace(&state.goal, from, &BTerm::Hole);
        stmts.push(Stmt::Rewrite {
            proof: call(
                "L.Lean.Eq.symm",
                vec![ty.clone(), from.clone(), to.clone(), proof],
            ),
            motive,
            source: here(),
        });
        state.goal = replace(&state.goal, from, to);
    }

    /// Split the goal equation's left side on the match it sticks at,
    /// handing each branch to `branch`.
    pub(super) fn split_goal(
        &mut self,
        state: &State,
        branch: &mut dyn FnMut(&mut Self, State) -> Result<Body, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let state = self.normalized(state);
        let BTerm::Equal(left, _, _) = &state.goal else {
            return Err(fail("a goal split needs an equation"));
        };
        match self.whnf(left) {
            Whnf::Stuck { scrutinee, ty, .. } => self.split(&state, &scrutinee, &ty, branch),
            other => Err(fail(format!(
                "a goal split found no match to split: {:?}",
                other.term()
            ))),
        }
    }
}

/// The two sides of a conjunction: the prelude's `Prod`, or Bend's own
/// product when both sides are data.
pub(super) fn conjuncts(ty: &BTerm) -> Option<(BTerm, BTerm)> {
    match ty {
        BTerm::Call(head, args) if head.text == "L.Lean.Prod" && args.len() == 2 => {
            Some((args[0].clone(), args[1].clone()))
        }
        BTerm::Product(left, right) => Some(((**left).clone(), (**right).clone())),
        _ => None,
    }
}

/// A term as Bend prints it, for a refusal naming it.
pub(super) fn show(term: &BTerm) -> String {
    let item = Item::Def {
        name: synthetic("ll_shown"),
        params: Vec::new(),
        result: var("Unit"),
        result_source: here(),
        body: Body::term(term.clone(), here()),
        source: here(),
    };
    let printed = crate::backend::bend::syntax::print_items(&[item]).join("");
    printed
        .split_once(":\n")
        .map_or(printed.clone(), |(_, body)| body.trim().to_owned())
}

/// A body as a term.
pub(super) fn block(body: Body) -> BTerm {
    if body.stmts.is_empty() {
        if let Tail::Term(term, _) = body.tail {
            return term;
        }
    }
    BTerm::Block(Box::new(body))
}

/// The variable a binder name binds, without its quantity mark.
pub(super) fn bound(text: &str) -> String {
    text.trim_start_matches(['+', '-', '~', '&']).to_owned()
}

fn constructor_name(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Zero => "0n".to_owned(),
        Pattern::Succ(_) => "1n+".to_owned(),
        Pattern::Pair(..) => "(,)".to_owned(),
        Pattern::Constructor(name, _) => name.text.clone(),
    }
}

fn same_constructor(a: &Pattern, b: &Pattern) -> bool {
    constructor_name(a) == constructor_name(b)
}

/// The value a branch's constructor and binders denote.
pub(super) fn constructed(constructor: &str, binders: &[String]) -> BTerm {
    match constructor {
        "0n" => BTerm::Nat("0".to_owned()),
        "1n+" => BTerm::Succ(Box::new(var(binders.first().cloned().unwrap_or_default()))),
        "(,)" => BTerm::Pair(
            Box::new(var(binders.first().cloned().unwrap_or_default())),
            Box::new(var(binders.get(1).cloned().unwrap_or_default())),
        ),
        name => BTerm::Constructor(
            synthetic(name),
            binders.iter().map(|binder| var(binder.clone())).collect(),
        ),
    }
}

/// The constructor a value's head is, as a pattern would name it.
fn constructor_of(term: &BTerm) -> String {
    match term {
        BTerm::Constructor(name, _) => name.text.clone(),
        BTerm::Nat(value) if value == "0" => "0n".to_owned(),
        BTerm::Nat(_) | BTerm::Succ(_) => "1n+".to_owned(),
        BTerm::Pair(..) => "(,)".to_owned(),
        BTerm::Refl => "{==}".to_owned(),
        other => format!("{other:?}"),
    }
}

/// A value's payload.
fn payload_of(term: &BTerm) -> Vec<BTerm> {
    match term {
        BTerm::Constructor(_, args) => args.clone(),
        BTerm::Succ(inner) => vec![(**inner).clone()],
        BTerm::Nat(value) => match value.parse::<u64>() {
            Ok(n) if n > 0 => vec![BTerm::Nat((n - 1).to_string())],
            _ => Vec::new(),
        },
        BTerm::Pair(first, second) => vec![(**first).clone(), (**second).clone()],
        _ => Vec::new(),
    }
}

/// The bindings a pattern makes on a value, when it matches.
fn select(pattern: &Pattern, value: &BTerm) -> Option<Vec<(String, BTerm)>> {
    match (pattern, value) {
        (Pattern::Constructor(name, names), BTerm::Constructor(constructor, args))
            if name.text == constructor.text && names.len() == args.len() =>
        {
            Some(
                names
                    .iter()
                    .map(|name| name.text.clone())
                    .zip(args.iter().cloned())
                    .collect(),
            )
        }
        (Pattern::Zero, BTerm::Nat(value)) if value == "0" => Some(Vec::new()),
        (Pattern::Succ(name), BTerm::Succ(inner)) => {
            Some(vec![(name.text.clone(), (**inner).clone())])
        }
        (Pattern::Succ(name), BTerm::Nat(value)) => match value.parse::<u64>() {
            Ok(n) if n > 0 => Some(vec![(name.text.clone(), BTerm::Nat((n - 1).to_string()))]),
            _ => None,
        },
        (Pattern::Pair(first, second), BTerm::Pair(a, b)) => Some(vec![
            (first.text.clone(), (**a).clone()),
            (second.text.clone(), (**b).clone()),
        ]),
        _ => None,
    }
}

/// The goal as a function of `wanted`, the payload the hypothesis names:
/// each variable of it replaced by its projection out of `z`.
fn abstracted(goal: &BTerm, wanted: &BTerm, z: &BTerm, ty: &BTerm) -> BTerm {
    match (wanted, ty) {
        (BTerm::Name(name), _) => {
            let mut map = BTreeMap::new();
            map.insert(name.text.clone(), z.clone());
            subst(goal, &map)
        }
        (BTerm::Pair(first, second), BTerm::Call(prod, types))
            if prod.text == "L.Lean.Prod" && types.len() == 2 =>
        {
            let projection = |which: &str| {
                call(
                    format!("S.Sem.{which}"),
                    vec![types[0].clone(), types[1].clone(), z.clone()],
                )
            };
            let goal = abstracted(goal, first, &projection("fst"), &types[0]);
            abstracted(&goal, second, &projection("snd"), &types[1])
        }
        _ => replace(goal, wanted, z),
    }
}

/// Every projection out of a literal pair reduced.
pub(super) fn projected(term: &BTerm) -> BTerm {
    let term = map_children(term, &mut projected);
    if let BTerm::Call(head, args) = &term {
        if args.len() == 3 {
            if let BTerm::Pair(first, second) = &args[2] {
                if head.text == "S.Sem.fst" {
                    return (**first).clone();
                }
                if head.text == "S.Sem.snd" {
                    return (**second).clone();
                }
            }
        }
    }
    term
}

/// The arguments of a call that are not templates.
pub(super) fn values_of(term: &BTerm) -> Vec<BTerm> {
    match term {
        BTerm::Call(_, args) => args
            .iter()
            .filter(|arg| !matches!(arg, BTerm::Template(_)))
            .cloned()
            .collect(),
        _ => Vec::new(),
    }
}

/// Whether `term` contains `part`.
pub(super) fn mentions(term: &BTerm, part: &BTerm) -> bool {
    if term == part {
        return true;
    }
    let mut found = false;
    for_each_child(term, &mut |child| found = found || mentions(child, part));
    found
}

/// Every occurrence of `from` in `term` replaced by `to`.
pub(super) fn replace(term: &BTerm, from: &BTerm, to: &BTerm) -> BTerm {
    if term == from {
        return to.clone();
    }
    map_children(term, &mut |child| replace(child, from, to))
}

fn for_each_child(term: &BTerm, f: &mut dyn FnMut(&BTerm)) {
    match term {
        BTerm::Name(_)
        | BTerm::Refl
        | BTerm::Nat(_)
        | BTerm::Kind(_)
        | BTerm::Hole
        | BTerm::Str(_)
        | BTerm::U32(_) => {}
        BTerm::Call(_, args) | BTerm::Constructor(_, args) | BTerm::Datatype(_, _, args) => {
            args.iter().for_each(f);
        }
        BTerm::Lam(_, body) | BTerm::Succ(body) | BTerm::Template(body) => f(body),
        BTerm::Pi {
            domain, codomain, ..
        }
        | BTerm::Sigma {
            domain, codomain, ..
        } => {
            f(domain);
            f(codomain);
        }
        BTerm::Product(a, b) | BTerm::Pair(a, b) | BTerm::Ann(a, b) => {
            f(a);
            f(b);
        }
        BTerm::Equal(a, b, c) => {
            f(a);
            f(b);
            f(c);
        }
        BTerm::Apply(function, args) => {
            f(function);
            args.iter().for_each(f);
        }
        BTerm::Block(body) => {
            for stmt in &body.stmts {
                match stmt {
                    Stmt::Rewrite { proof, motive, .. } => {
                        f(proof);
                        f(motive);
                    }
                    Stmt::Let { value, .. } | Stmt::Share { value, .. } => f(value),
                }
            }
            if let Tail::Term(term, _) = &body.tail {
                f(term);
            }
        }
    }
}

fn map_children(term: &BTerm, f: &mut dyn FnMut(&BTerm) -> BTerm) -> BTerm {
    let boxed = |t: &BTerm, f: &mut dyn FnMut(&BTerm) -> BTerm| Box::new(f(t));
    match term {
        BTerm::Name(_)
        | BTerm::Refl
        | BTerm::Nat(_)
        | BTerm::Kind(_)
        | BTerm::Hole
        | BTerm::Str(_)
        | BTerm::U32(_) => term.clone(),
        BTerm::Call(head, args) => BTerm::Call(head.clone(), args.iter().map(&mut *f).collect()),
        BTerm::Constructor(head, args) => {
            BTerm::Constructor(head.clone(), args.iter().map(&mut *f).collect())
        }
        BTerm::Datatype(head, quantities, args) => BTerm::Datatype(
            head.clone(),
            quantities.clone(),
            args.iter().map(&mut *f).collect(),
        ),
        BTerm::Lam(binder, body) => BTerm::Lam(binder.clone(), boxed(body, f)),
        BTerm::Succ(body) => BTerm::Succ(boxed(body, f)),
        BTerm::Template(body) => BTerm::Template(boxed(body, f)),
        BTerm::Pi {
            name,
            erased,
            domain,
            codomain,
        } => BTerm::Pi {
            name: name.clone(),
            erased: *erased,
            domain: boxed(domain, f),
            codomain: boxed(codomain, f),
        },
        BTerm::Sigma {
            name,
            domain,
            codomain,
        } => BTerm::Sigma {
            name: name.clone(),
            domain: boxed(domain, f),
            codomain: boxed(codomain, f),
        },
        BTerm::Product(a, b) => BTerm::Product(boxed(a, f), boxed(b, f)),
        BTerm::Pair(a, b) => BTerm::Pair(boxed(a, f), boxed(b, f)),
        BTerm::Ann(a, b) => BTerm::Ann(boxed(a, f), boxed(b, f)),
        BTerm::Equal(a, b, c) => BTerm::Equal(boxed(a, f), boxed(b, f), boxed(c, f)),
        BTerm::Apply(function, args) => {
            BTerm::Apply(boxed(function, f), args.iter().map(&mut *f).collect())
        }
        BTerm::Block(body) => {
            let stmts = body
                .stmts
                .iter()
                .map(|stmt| match stmt {
                    Stmt::Rewrite {
                        proof,
                        motive,
                        source,
                    } => Stmt::Rewrite {
                        proof: f(proof),
                        motive: f(motive),
                        source: source.clone(),
                    },
                    Stmt::Let {
                        name,
                        value,
                        source,
                    } => Stmt::Let {
                        name: name.clone(),
                        value: f(value),
                        source: source.clone(),
                    },
                    Stmt::Share {
                        name,
                        value,
                        source,
                    } => Stmt::Share {
                        name: name.clone(),
                        value: f(value),
                        source: source.clone(),
                    },
                })
                .collect();
            let tail = match &body.tail {
                Tail::Term(term, source) => Tail::Term(f(term), source.clone()),
                other => other.clone(),
            };
            BTerm::Block(Box::new(Body { stmts, tail }))
        }
    }
}

/// The free variable names of `term`.
pub(super) fn free_names(term: &BTerm) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_free(term, &mut BTreeSet::new(), &mut out);
    out
}

fn collect_free(term: &BTerm, bound_names: &mut BTreeSet<String>, out: &mut BTreeSet<String>) {
    match term {
        BTerm::Name(name) => {
            if !bound_names.contains(&name.text) {
                out.insert(name.text.clone());
            }
        }
        BTerm::Lam(binder, body) => {
            let name = bound(&binder.text);
            let fresh = bound_names.insert(name.clone());
            collect_free(body, bound_names, out);
            if fresh {
                bound_names.remove(&name);
            }
        }
        BTerm::Pi {
            name: Some(binder),
            domain,
            codomain,
            ..
        }
        | BTerm::Sigma {
            name: binder,
            domain,
            codomain,
        } => {
            collect_free(domain, bound_names, out);
            let name = bound(&binder.text);
            let fresh = bound_names.insert(name.clone());
            collect_free(codomain, bound_names, out);
            if fresh {
                bound_names.remove(&name);
            }
        }
        BTerm::Block(body) => {
            let mut added = Vec::new();
            for stmt in &body.stmts {
                match stmt {
                    Stmt::Rewrite { proof, motive, .. } => {
                        collect_free(proof, bound_names, out);
                        collect_free(motive, bound_names, out);
                    }
                    Stmt::Let { name, value, .. } | Stmt::Share { name, value, .. } => {
                        collect_free(value, bound_names, out);
                        let name = bound(&name.text);
                        if bound_names.insert(name.clone()) {
                            added.push(name);
                        }
                    }
                }
            }
            if let Tail::Term(term, _) = &body.tail {
                collect_free(term, bound_names, out);
            }
            for name in added {
                bound_names.remove(&name);
            }
        }
        other => for_each_child(other, &mut |child| collect_free(child, bound_names, out)),
    }
}

/// Capture-avoiding substitution of free variables.
pub(super) fn subst(term: &BTerm, map: &BTreeMap<String, BTerm>) -> BTerm {
    if map.is_empty() {
        return term.clone();
    }
    match term {
        BTerm::Name(name) => map.get(&name.text).cloned().unwrap_or_else(|| term.clone()),
        BTerm::Lam(binder, body) => {
            let (binder, inner) = enter(binder, map);
            BTerm::Lam(binder, Box::new(subst(body, &inner)))
        }
        BTerm::Pi {
            name: Some(binder),
            erased,
            domain,
            codomain,
        } => {
            let domain = Box::new(subst(domain, map));
            let (binder, inner) = enter(binder, map);
            BTerm::Pi {
                name: Some(binder),
                erased: *erased,
                domain,
                codomain: Box::new(subst(codomain, &inner)),
            }
        }
        BTerm::Sigma {
            name,
            domain,
            codomain,
        } => {
            let domain = Box::new(subst(domain, map));
            let (binder, inner) = enter(name, map);
            BTerm::Sigma {
                name: binder,
                domain,
                codomain: Box::new(subst(codomain, &inner)),
            }
        }
        BTerm::Block(body) => {
            let mut inner = map.clone();
            let mut stmts = Vec::new();
            for stmt in &body.stmts {
                stmts.push(match stmt {
                    Stmt::Rewrite {
                        proof,
                        motive,
                        source,
                    } => Stmt::Rewrite {
                        proof: subst(proof, &inner),
                        motive: subst(motive, &inner),
                        source: source.clone(),
                    },
                    Stmt::Let {
                        name,
                        value,
                        source,
                    } => {
                        let value = subst(value, &inner);
                        let (name, next) = enter(name, &inner);
                        inner = next;
                        Stmt::Let {
                            name,
                            value,
                            source: source.clone(),
                        }
                    }
                    Stmt::Share {
                        name,
                        value,
                        source,
                    } => {
                        let value = subst(value, &inner);
                        let (name, next) = enter(name, &inner);
                        inner = next;
                        Stmt::Share {
                            name,
                            value,
                            source: source.clone(),
                        }
                    }
                });
            }
            let tail = match &body.tail {
                Tail::Term(term, source) => Tail::Term(subst(term, &inner), source.clone()),
                other => other.clone(),
            };
            BTerm::Block(Box::new(Body { stmts, tail }))
        }
        other => map_children(other, &mut |child| subst(child, map)),
    }
}

/// Enter a binder under a substitution: drop the variable it shadows, and
/// rename it when a substituted value mentions it.
fn enter(binder: &Name, map: &BTreeMap<String, BTerm>) -> (Name, BTreeMap<String, BTerm>) {
    let name = bound(&binder.text);
    let mut inner = map.clone();
    inner.remove(&name);
    let captured = inner
        .values()
        .any(|value| free_names(value).contains(&name));
    if !captured {
        return (binder.clone(), inner);
    }
    let mark = &binder.text[..binder.text.len() - name.len()];
    let mut fresh = format!("{name}_r");
    let mut index = 0;
    while inner
        .values()
        .any(|value| free_names(value).contains(&fresh))
    {
        index += 1;
        fresh = format!("{name}_r{index}");
    }
    inner.insert(name, var(fresh.clone()));
    (
        Name::new(format!("{mark}{fresh}"), binder.origin.clone()),
        inner,
    )
}

/// The term with every name's origin made synthetic, so terms from the
/// emitted items and terms the proof builds compare by their text.
pub(super) fn plain(term: &BTerm) -> BTerm {
    let name = |name: &Name| Name::new(name.text.clone(), synthetic_origin());
    match term {
        BTerm::Name(n) => BTerm::Name(name(n)),
        BTerm::Call(head, args) => BTerm::Call(name(head), args.iter().map(plain).collect()),
        BTerm::Constructor(head, args) => {
            BTerm::Constructor(name(head), args.iter().map(plain).collect())
        }
        BTerm::Datatype(head, quantities, args) => BTerm::Datatype(
            name(head),
            quantities.clone(),
            args.iter().map(plain).collect(),
        ),
        BTerm::Lam(binder, body) => BTerm::Lam(name(binder), Box::new(plain(body))),
        BTerm::Pi {
            name: binder,
            erased,
            domain,
            codomain,
        } => BTerm::Pi {
            name: binder.as_ref().map(name),
            erased: *erased,
            domain: Box::new(plain(domain)),
            codomain: Box::new(plain(codomain)),
        },
        BTerm::Sigma {
            name: binder,
            domain,
            codomain,
        } => BTerm::Sigma {
            name: name(binder),
            domain: Box::new(plain(domain)),
            codomain: Box::new(plain(codomain)),
        },
        BTerm::Block(body) => BTerm::Block(Box::new(plain_body(body))),
        other => map_children(other, &mut plain),
    }
}

pub(super) fn plain_body(body: &Body) -> Body {
    let name = |name: &Name| Name::new(name.text.clone(), synthetic_origin());
    let stmts = body
        .stmts
        .iter()
        .map(|stmt| match stmt {
            Stmt::Rewrite {
                proof,
                motive,
                source,
            } => Stmt::Rewrite {
                proof: plain(proof),
                motive: plain(motive),
                source: source.clone(),
            },
            Stmt::Let {
                name: n,
                value,
                source,
            } => Stmt::Let {
                name: name(n),
                value: plain(value),
                source: source.clone(),
            },
            Stmt::Share {
                name: n,
                value,
                source,
            } => Stmt::Share {
                name: name(n),
                value: plain(value),
                source: source.clone(),
            },
        })
        .collect();
    let tail = match &body.tail {
        Tail::Term(term, source) => Tail::Term(plain(term), source.clone()),
        Tail::Match {
            scrutinee,
            cases,
            source,
        } => Tail::Match {
            scrutinee: name(scrutinee),
            cases: cases
                .iter()
                .map(|(pattern, body)| {
                    let pattern = match pattern {
                        Pattern::Zero => Pattern::Zero,
                        Pattern::Succ(n) => Pattern::Succ(name(n)),
                        Pattern::Pair(a, b) => Pattern::Pair(name(a), name(b)),
                        Pattern::Constructor(c, names) => {
                            Pattern::Constructor(name(c), names.iter().map(name).collect())
                        }
                    };
                    (pattern, plain_body(body))
                })
                .collect(),
            source: source.clone(),
        },
    };
    Body { stmts, tail }
}

fn synthetic_origin() -> Origin {
    synthetic("").origin
}

/// An item with every name's origin made synthetic.
pub(in crate::backend::bend::semantic) fn plain_item(item: &Item) -> Item {
    let name = |name: &Name| Name::new(name.text.clone(), synthetic_origin());
    let params = |params: &[Param]| {
        params
            .iter()
            .map(|param| Param {
                quantity: param.quantity,
                name: name(&param.name),
                ty: plain(&param.ty),
                source: param.source.clone(),
            })
            .collect::<Vec<_>>()
    };
    match item {
        Item::Def {
            name: n,
            params: p,
            result,
            result_source,
            body,
            source,
        } => Item::Def {
            name: name(n),
            params: params(p),
            result: plain(result),
            result_source: result_source.clone(),
            body: plain_body(body),
            source: source.clone(),
        },
        Item::Law {
            name: n,
            params: p,
            claim,
            claim_source,
            proof,
            source,
        } => Item::Law {
            name: name(n),
            params: params(p),
            claim: plain(claim),
            claim_source: claim_source.clone(),
            proof: proof.clone(),
            source: source.clone(),
        },
        Item::Type {
            name: n,
            parameters,
            index,
            kind,
            constructors,
            source,
        } => Item::Type {
            name: name(n),
            parameters: parameters.iter().map(name).collect(),
            index: index.as_ref().map(|(n, t)| (name(n), plain(t))),
            kind,
            constructors: constructors
                .iter()
                .map(|(c, fields)| {
                    (
                        name(c),
                        fields.iter().map(|(f, t)| (name(f), plain(t))).collect(),
                    )
                })
                .collect(),
            source: source.clone(),
        },
    }
}
