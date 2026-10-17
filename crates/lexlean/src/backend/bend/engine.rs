//! The Bend backend's term engine: types of linked terms, the implicit
//! arguments Lean used to infer, and the lowering of terms to Bend.
//!
//! Lean inferred implicit arguments and goals at elaboration time; Bend
//! infers almost nothing, so every argument the generated Bend passes must
//! be known here. The engine is not a second proof checker (§13.7): it
//! computes types syntactically, with definitional unfolding of document
//! definitions, and the Bend checker is final. A term whose implicit
//! arguments the engine cannot determine is refused with `LLB6008` rather
//! than emitted with a guess.

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::numeral;
use crate::backend::bend::prelude::{ConstantKind, Registry, TypeForm, PRELUDE_ALIAS};
use crate::backend::bend::syntax::{BTerm, Name};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::{flatten_pi, subst};
use crate::ir::declaration::{DeclBody, Declaration};
use crate::ir::term::{
    Binder, CoreRef, DefinedLexiconRef, DocumentDeclRef, ExternalConstRef, GlobalRef, LocalId,
    Term, Universe,
};
use crate::lexicon::entry::Denotation;
use crate::lexicon::lse::{BinderMode, Lse, QualifiedId};
use crate::lexicon::resolve::Closure;
use crate::source::coverage::Origin;

pub(crate) fn fail(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLB6008"), message.into())
}

/// Every document declaration of the linked project, so a module can type
/// a reference to a declaration of a module it imports.
pub struct ProjectIndex<'a> {
    /// The glossary closure.
    pub closure: &'a Closure,
    /// Declarations by `(source module, component)`.
    pub declarations: BTreeMap<(String, String), &'a Declaration>,
    /// Full generated module names by source module.
    pub generated_modules: BTreeMap<String, String>,
}

/// The type a global has, or why it has none.
fn core_type(core: CoreRef, fresh: &mut Fresh) -> Term {
    let prop = Term::Sort(Universe::Num(0));
    let binder = |id: LocalId, mode: BinderMode, ty: Term| Binder {
        id,
        mode,
        ty,
        spelling: String::new(),
    };
    match core {
        CoreRef::Eq => {
            let alpha = fresh.local();
            let x = fresh.local();
            let y = fresh.local();
            Term::Pi {
                binders: vec![
                    binder(alpha, BinderMode::Implicit, Term::Sort(Universe::Num(1))),
                    binder(x, BinderMode::Explicit, Term::Local(alpha)),
                    binder(y, BinderMode::Explicit, Term::Local(alpha)),
                ],
                body: Box::new(prop),
            }
        }
        CoreRef::And | CoreRef::Or | CoreRef::Iff => {
            let a = fresh.local();
            let b = fresh.local();
            Term::Pi {
                binders: vec![
                    binder(a, BinderMode::Explicit, prop.clone()),
                    binder(b, BinderMode::Explicit, prop.clone()),
                ],
                body: Box::new(prop),
            }
        }
        CoreRef::Not => {
            let a = fresh.local();
            Term::Pi {
                binders: vec![binder(a, BinderMode::Explicit, prop.clone())],
                body: Box::new(prop),
            }
        }
        CoreRef::Exists | CoreRef::ExistsUnique => {
            let alpha = fresh.local();
            let p = fresh.local();
            let x = fresh.local();
            Term::Pi {
                binders: vec![
                    binder(alpha, BinderMode::Implicit, Term::Sort(Universe::Num(1))),
                    binder(
                        p,
                        BinderMode::Explicit,
                        Term::Pi {
                            binders: vec![binder(x, BinderMode::Explicit, Term::Local(alpha))],
                            body: Box::new(prop.clone()),
                        },
                    ),
                ],
                body: Box::new(prop),
            }
        }
    }
}

/// Fresh synthetic local identities, disjoint from elaborated ones
/// (elaboration allocates upward from zero).
#[derive(Debug, Default)]
pub struct Fresh {
    count: u64,
}

impl Fresh {
    /// The next identity.
    pub fn local(&mut self) -> LocalId {
        self.count += 1;
        LocalId(u64::MAX / 2 + self.count)
    }
}

/// The universe-variable spelling the engine uses for `False`, which the
/// term IR has no constant for: `Not P` unfolds to `P → False` (§18.4)
/// and only the engine ever builds or reads this sort.
const FALSE_SORT: &str = "\u{22a5}";

/// `False`, the codomain of an unfolded negation.
#[must_use]
pub fn false_term() -> Term {
    Term::Sort(Universe::Var(FALSE_SORT.to_owned()))
}

/// Is `term` the engine's `False`?
#[must_use]
pub fn is_false(term: &Term) -> bool {
    matches!(term, Term::Sort(Universe::Var(name)) if name == FALSE_SORT)
}

/// Does `term` mention `id` free?
pub fn mentions(term: &Term, id: LocalId) -> bool {
    match term {
        Term::Local(other) => *other == id,
        Term::Sort(_) | Term::Global(..) => false,
        Term::App {
            function,
            explicit_args,
            ..
        } => mentions(function, id) || explicit_args.iter().any(|arg| mentions(arg, id)),
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            binders.iter().any(|binder| mentions(&binder.ty, id)) || mentions(body, id)
        }
        Term::Let {
            binder,
            value,
            body,
        } => mentions(&binder.ty, id) || mentions(value, id) || mentions(body, id),
        Term::NatLiteral { expected_type, .. } => mentions(expected_type, id),
    }
}

fn same_global(a: &GlobalRef, b: &GlobalRef) -> bool {
    match (a, b) {
        (GlobalRef::Core(x), GlobalRef::Core(y)) => x == y,
        (GlobalRef::External(x), GlobalRef::External(y)) => x.lean_name == y.lean_name,
        (GlobalRef::Document(x), GlobalRef::Document(y)) => {
            x.module == y.module && x.component == y.component
        }
        (GlobalRef::DefinedLexicon(x), GlobalRef::DefinedLexicon(y)) => x.entry == y.entry,
        _ => false,
    }
}

/// A store of metavariables: binder identities awaiting a value.
#[derive(Debug, Default, Clone)]
pub struct Metas {
    open: BTreeSet<LocalId>,
    solved: BTreeMap<LocalId, Term>,
}

impl Metas {
    /// Register a metavariable.
    pub fn open(&mut self, id: LocalId) {
        self.open.insert(id);
    }

    /// The value of a metavariable, if solved.
    #[must_use]
    pub fn get(&self, id: LocalId) -> Option<&Term> {
        self.solved.get(&id)
    }

    /// Replace every solved metavariable in `term`.
    #[must_use]
    pub fn zonk(&self, term: &Term) -> Term {
        let mut current = term.clone();
        // Values may mention metas solved later; substitute to a fixpoint,
        // bounded by the store size.
        for _ in 0..=self.solved.len() {
            let next = subst(&current, &self.solved);
            if next == current {
                break;
            }
            current = next;
        }
        current
    }

    /// Is any open metavariable still unsolved in `term`?
    #[must_use]
    pub fn unsolved_in(&self, term: &Term) -> bool {
        let zonked = self.zonk(term);
        self.open
            .iter()
            .any(|id| !self.solved.contains_key(id) && mentions(&zonked, *id))
    }
}

/// The engine for one module.
pub struct Engine<'a> {
    /// The project.
    pub project: &'a ProjectIndex<'a>,
    /// The prelude registry.
    pub registry: &'static Registry,
    /// The current source module.
    pub module: String,
    /// Fresh synthetic identities.
    pub fresh: Fresh,
    /// The Bend name of every named local.
    pub names: BTreeMap<LocalId, String>,
    term_count: usize,
    proof_count: usize,
    /// The other generated modules this module references, by source name.
    pub referenced_modules: BTreeSet<String>,
    /// Whether this module references the prelude.
    pub uses_prelude: bool,
    /// The assumption premises the current declaration needs, by name,
    /// with their Bend types.
    pub assumptions: BTreeMap<String, String>,
    /// Memoized signatures of external entries.
    signatures: BTreeMap<String, Term>,
    /// The assumption premises of every theorem lowered so far.
    pub assumption_table: BTreeMap<(String, String), Vec<(String, String)>>,
}

/// A typing context: locals in scope order with their types.
pub type Ctx = Vec<(LocalId, Term)>;

fn ctx_type(ctx: &Ctx, id: LocalId) -> Option<&Term> {
    ctx.iter()
        .rev()
        .find(|(local, _)| *local == id)
        .map(|(_, ty)| ty)
}

/// The import alias of a generated module.
#[must_use]
pub fn module_alias(generated: &str) -> String {
    generated.replace('.', "_")
}

impl<'a> Engine<'a> {
    /// An engine for one module.
    #[must_use]
    pub fn new(project: &'a ProjectIndex<'a>, registry: &'static Registry, module: &str) -> Self {
        Self {
            project,
            registry,
            module: module.to_owned(),
            fresh: Fresh::default(),
            names: BTreeMap::new(),
            term_count: 0,
            proof_count: 0,
            referenced_modules: BTreeSet::new(),
            uses_prelude: false,
            assumptions: BTreeMap::new(),
            signatures: BTreeMap::new(),
            assumption_table: BTreeMap::new(),
        }
    }

    /// Reset per-declaration naming (§17.8: names restart per declaration).
    pub fn start_declaration(&mut self) {
        self.names.clear();
        self.term_count = 0;
        self.proof_count = 0;
        self.assumptions.clear();
    }

    /// The Bend name of a term binder, allocated on first use.
    pub fn term_binder(&mut self, id: LocalId) -> String {
        if let Some(name) = self.names.get(&id) {
            return name.clone();
        }
        let name = format!("llv{}", self.term_count);
        self.term_count += 1;
        self.names.insert(id, name.clone());
        name
    }

    /// The Bend name of a proof-introduced local, allocated on first use.
    pub fn proof_binder(&mut self, id: LocalId) -> String {
        if let Some(name) = self.names.get(&id) {
            return name.clone();
        }
        let name = format!("llh{}", self.proof_count);
        self.proof_count += 1;
        self.names.insert(id, name.clone());
        name
    }

    fn local_name(&mut self, id: LocalId) -> Name {
        let text = self
            .names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.term_binder(id));
        Name::new(
            text,
            Origin::Local(usize::try_from(id.0).unwrap_or(usize::MAX)),
        )
    }

    fn prelude(&mut self, bend: &str, origin: Origin) -> Name {
        self.uses_prelude = true;
        Name::new(format!("{PRELUDE_ALIAS}.{bend}"), origin)
    }

    // -----------------------------------------------------------------
    // Signatures
    // -----------------------------------------------------------------

    /// The declared type of a document declaration: its parameters, then
    /// its statement or definition type.
    pub fn declaration_type(declaration: &Declaration) -> Term {
        let inner = match &declaration.body {
            DeclBody::TheoremLike { statement, .. } => statement.clone(),
            DeclBody::Definition { ty, .. } => ty.clone(),
        };
        if declaration.params.is_empty() {
            inner
        } else {
            Term::Pi {
                binders: declaration.params.clone(),
                body: Box::new(inner),
            }
        }
    }

    fn document(&self, reference: &DocumentDeclRef) -> Result<&'a Declaration, Diagnostic> {
        self.project
            .declarations
            .get(&(reference.module.clone(), reference.component.clone()))
            .copied()
            .ok_or_else(|| {
                fail(format!(
                    "document declaration `{}::{}` is not in the linked project",
                    reference.module, reference.component
                ))
            })
    }

    /// The signature of an external entry as a term.
    fn external_signature(&mut self, external: &ExternalConstRef) -> Result<Term, Diagnostic> {
        if let Some(found) = self.signatures.get(&external.entry) {
            return Ok(found.clone());
        }
        let id = QualifiedId::parse(&external.entry)
            .map_err(|error| fail(format!("`{}`: {error}", external.entry)))?;
        let entry = self
            .project
            .closure
            .entry(&id)
            .ok_or_else(|| fail(format!("`{id}` is not in the glossary closure")))?;
        let signature = entry
            .signature
            .as_ref()
            .ok_or_else(|| fail(format!("`{id}` has no signature")))?;
        let mut scope = Vec::new();
        let term = self.lse_term(signature, &mut scope)?;
        self.signatures.insert(external.entry.clone(), term.clone());
        Ok(term)
    }

    fn entry_global(&self, id: &QualifiedId) -> Result<GlobalRef, Diagnostic> {
        let entry = self
            .project
            .closure
            .entry(id)
            .ok_or_else(|| fail(format!("`{id}` is not in the glossary closure")))?;
        Ok(match &entry.denotation {
            Denotation::Core { constructor } => {
                GlobalRef::Core(CoreRef::from_constructor(constructor).ok_or_else(|| {
                    fail(format!("core constructor `{constructor}` in a signature"))
                })?)
            }
            Denotation::Lean { module, name } => GlobalRef::External(ExternalConstRef {
                package: id.package.clone(),
                entry: id.to_string(),
                lean_module: module.clone(),
                lean_name: name.clone(),
                signature_hash: entry
                    .signature_hash
                    .ok_or_else(|| fail(format!("`{id}` has no signature")))?,
            }),
            Denotation::Document { module, component } => {
                let declaration = self
                    .project
                    .declarations
                    .get(&(module.clone(), component.clone()))
                    .ok_or_else(|| fail(format!("`{module}::{component}` is not linked")))?;
                let generated = self
                    .project
                    .generated_modules
                    .get(module)
                    .cloned()
                    .unwrap_or_default();
                GlobalRef::Document(DocumentDeclRef {
                    module: module.clone(),
                    component: component.clone(),
                    lean_name: format!("{generated}.{}", declaration.lean_name),
                })
            }
            Denotation::Defined { .. } => GlobalRef::DefinedLexicon(DefinedLexiconRef {
                package: id.package.clone(),
                entry: id.to_string(),
                signature_hash: entry
                    .signature_hash
                    .ok_or_else(|| fail(format!("`{id}` has no signature")))?,
            }),
        })
    }

    /// Convert LSE (a signature or a defined value) to a term with fresh
    /// binder identities.
    pub fn lse_term(
        &mut self,
        lse: &Lse,
        scope: &mut Vec<(String, LocalId)>,
    ) -> Result<Term, Diagnostic> {
        Ok(match lse {
            Lse::SortProp => Term::Sort(Universe::Num(0)),
            Lse::SortType(_) => Term::Sort(Universe::Num(1)),
            Lse::Const(id, _) => Term::Global(self.entry_global(id)?, Vec::new()),
            Lse::Local(name) => Term::Local(
                scope
                    .iter()
                    .rev()
                    .find(|(bound, _)| bound == name)
                    .map(|(_, id)| *id)
                    .ok_or_else(|| fail(format!("unbound LSE local `{name}`")))?,
            ),
            Lse::App(function, arguments) => {
                let function_term = self.lse_term(function, scope)?;
                let mut explicit_args = Vec::new();
                for argument in arguments {
                    explicit_args.push(self.lse_term(argument, scope)?);
                }
                // A literal argument takes the type of the explicit binder
                // it fills, as the elaborator types it (§15.5).
                let binder_types = self.explicit_binder_types(&function_term)?;
                for (index, argument) in explicit_args.iter_mut().enumerate() {
                    if let Term::NatLiteral { expected_type, .. } = argument {
                        if let Some(Some(ty)) = binder_types.get(index) {
                            **expected_type = ty.clone();
                        }
                    }
                }
                Term::App {
                    function: Box::new(function_term),
                    explicit_args,
                    omitted_implicit_binders: Vec::new(),
                }
            }
            Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                let depth = scope.len();
                let mut out = Vec::new();
                for binder in binders {
                    let ty = self.lse_term(&binder.ty, scope)?;
                    let id = self.fresh.local();
                    scope.push((binder.name.clone(), id));
                    out.push(Binder {
                        id,
                        mode: binder.mode,
                        ty,
                        spelling: binder.name.clone(),
                    });
                }
                let body_term = self.lse_term(body, scope)?;
                scope.truncate(depth);
                if matches!(lse, Lse::Pi(..)) {
                    Term::Pi {
                        binders: out,
                        body: Box::new(body_term),
                    }
                } else {
                    Term::Lambda {
                        binders: out,
                        body: Box::new(body_term),
                    }
                }
            }
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => {
                let ty_term = self.lse_term(ty, scope)?;
                let value_term = self.lse_term(value, scope)?;
                let id = self.fresh.local();
                scope.push((name.clone(), id));
                let body_term = self.lse_term(body, scope)?;
                scope.pop();
                Term::Let {
                    binder: Box::new(Binder {
                        id,
                        mode: BinderMode::Explicit,
                        ty: ty_term,
                        spelling: name.clone(),
                    }),
                    value: Box::new(value_term),
                    body: Box::new(body_term),
                }
            }
            Lse::Nat(decimal) => Term::NatLiteral {
                decimal: decimal.clone(),
                // Replaced by the enclosing application's binder type.
                expected_type: Box::new(Term::Sort(Universe::Num(1))),
            },
        })
    }

    /// The explicit binder types of a function term's type, where known.
    fn explicit_binder_types(&mut self, function: &Term) -> Result<Vec<Option<Term>>, Diagnostic> {
        let Term::Global(global, _) = function else {
            return Ok(Vec::new());
        };
        let ty = match global {
            GlobalRef::External(external) => self.external_signature(external)?,
            GlobalRef::Core(core) => core_type(*core, &mut self.fresh),
            GlobalRef::Document(reference) => Self::declaration_type(self.document(reference)?),
            GlobalRef::DefinedLexicon(_) => return Ok(Vec::new()),
        };
        let (binders, _) = flatten_pi(&ty);
        Ok(binders
            .iter()
            .filter(|binder| binder.mode == BinderMode::Explicit)
            .map(|binder| {
                if binders.iter().any(|other| mentions(&binder.ty, other.id)) {
                    None
                } else {
                    Some(binder.ty.clone())
                }
            })
            .collect())
    }

    /// The type of a global.
    pub fn global_type(&mut self, global: &GlobalRef) -> Result<Term, Diagnostic> {
        match global {
            GlobalRef::Core(core) => Ok(core_type(*core, &mut self.fresh)),
            GlobalRef::External(external) => self.external_signature(external),
            GlobalRef::Document(reference) => Ok(Self::declaration_type(self.document(reference)?)),
            GlobalRef::DefinedLexicon(defined) => {
                let id = QualifiedId::parse(&defined.entry)
                    .map_err(|error| fail(format!("`{}`: {error}", defined.entry)))?;
                let entry = self
                    .project
                    .closure
                    .entry(&id)
                    .ok_or_else(|| fail(format!("`{id}` is not in the glossary closure")))?;
                let signature = entry
                    .signature
                    .clone()
                    .ok_or_else(|| fail(format!("`{id}` has no signature")))?;
                self.lse_term(&signature, &mut Vec::new())
            }
        }
    }

    // -----------------------------------------------------------------
    // Reduction
    // -----------------------------------------------------------------

    /// The value of a defined lexicon entry, as a term.
    fn defined_value(&mut self, defined: &DefinedLexiconRef) -> Result<Term, Diagnostic> {
        let id = QualifiedId::parse(&defined.entry)
            .map_err(|error| fail(format!("`{}`: {error}", defined.entry)))?;
        let entry = self
            .project
            .closure
            .entry(&id)
            .ok_or_else(|| fail(format!("`{id}` is not in the glossary closure")))?;
        let Denotation::Defined { value, .. } = &entry.denotation else {
            return Err(fail(format!("`{id}` is not a defined value")));
        };
        let value = value.clone();
        self.lse_term(&value, &mut Vec::new())
    }

    /// The core connective an external constant is, when Lean's `Init`
    /// defines it as one and the entry offers it at that connective's
    /// shape: two propositions for `And`, `Or`, and `Iff`, one for `Not`.
    pub fn external_core(&mut self, external: &ExternalConstRef) -> Option<CoreRef> {
        let (core, arity) = match external.lean_name.as_str() {
            "And" => (CoreRef::And, 2),
            "Or" => (CoreRef::Or, 2),
            "Iff" => (CoreRef::Iff, 2),
            "Not" => (CoreRef::Not, 1),
            _ => return None,
        };
        let signature = self.external_signature(external).ok()?;
        let (binders, result) = flatten_pi(&signature);
        let props = binders.iter().all(|binder| {
            binder.mode == BinderMode::Explicit && matches!(binder.ty, Term::Sort(Universe::Num(0)))
        });
        (props && binders.len() == arity && matches!(result, Term::Sort(Universe::Num(0))))
            .then_some(core)
    }

    /// Unfold the head of a term once: a document definition applied to
    /// arguments, a defined lexicon value, a beta redex, or a let.
    pub fn unfold_head(&mut self, term: &Term) -> Result<Option<Term>, Diagnostic> {
        match term {
            Term::Global(GlobalRef::External(external), universes) => Ok(self
                .external_core(external)
                .map(|core| Term::Global(GlobalRef::Core(core), universes.clone()))),
            Term::Global(GlobalRef::Document(reference), _) => {
                let declaration = self.document(reference)?;
                match &declaration.body {
                    DeclBody::Definition { value, .. } if declaration.params.is_empty() => {
                        Ok(Some(value.clone()))
                    }
                    DeclBody::Definition { value, .. } => Ok(Some(Term::Lambda {
                        binders: declaration.params.clone(),
                        body: Box::new(value.clone()),
                    })),
                    DeclBody::TheoremLike { .. } => Ok(None),
                }
            }
            Term::Global(GlobalRef::DefinedLexicon(defined), _) => {
                Ok(Some(self.defined_value(defined)?))
            }
            Term::App {
                function,
                explicit_args,
                omitted_implicit_binders,
            } => {
                if let (Term::Global(GlobalRef::Core(CoreRef::Not), _), [inner]) =
                    (&**function, explicit_args.as_slice())
                {
                    return Ok(Some(Term::Pi {
                        binders: vec![Binder {
                            id: self.fresh.local(),
                            mode: BinderMode::Explicit,
                            ty: inner.clone(),
                            spelling: String::new(),
                        }],
                        body: Box::new(false_term()),
                    }));
                }
                if let Term::Lambda { binders, body } = &**function {
                    return Ok(Some(beta(binders, body, explicit_args)));
                }
                if let Term::App {
                    function: inner,
                    explicit_args: inner_args,
                    ..
                } = &**function
                {
                    let mut args = inner_args.clone();
                    args.extend(explicit_args.iter().cloned());
                    return Ok(Some(Term::App {
                        function: inner.clone(),
                        explicit_args: args,
                        omitted_implicit_binders: omitted_implicit_binders.clone(),
                    }));
                }
                Ok(self.unfold_head(function)?.map(|unfolded| Term::App {
                    function: Box::new(unfolded),
                    explicit_args: explicit_args.clone(),
                    omitted_implicit_binders: omitted_implicit_binders.clone(),
                }))
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                let mut map = BTreeMap::new();
                map.insert(binder.id, (**value).clone());
                Ok(Some(subst(body, &map)))
            }
            _ => Ok(None),
        }
    }

    /// Weak-head normalize through document definitions and beta.
    pub fn whnf(&mut self, term: &Term) -> Result<Term, Diagnostic> {
        let mut current = term.clone();
        for _ in 0..4096 {
            match self.unfold_head(&current)? {
                Some(next) => current = next,
                None => return Ok(current),
            }
        }
        Err(fail(
            "a term did not reach weak-head normal form within 4096 unfoldings",
        ))
    }

    // -----------------------------------------------------------------
    // Unification
    // -----------------------------------------------------------------

    /// First-order unification of `pattern` (holding metas) against
    /// `target`, unfolding document definitions on a head mismatch.
    pub fn unify(&mut self, pattern: &Term, target: &Term, metas: &mut Metas) -> bool {
        self.unify_at(pattern, target, metas, &mut Vec::new(), 0)
    }

    fn unify_at(
        &mut self,
        pattern: &Term,
        target: &Term,
        metas: &mut Metas,
        bound: &mut Vec<(LocalId, LocalId)>,
        depth: usize,
    ) -> bool {
        if depth > 256 {
            return false;
        }
        if let Term::Local(id) = pattern {
            if metas.open.contains(id) {
                if let Some(value) = metas.solved.get(id).cloned() {
                    return self.unify_at(&value, target, metas, bound, depth + 1);
                }
                if bound.iter().any(|(_, right)| mentions(target, *right)) {
                    return false;
                }
                if mentions(target, *id) {
                    return false;
                }
                metas.solved.insert(*id, target.clone());
                return true;
            }
        }
        if let Term::Local(id) = target {
            if metas.open.contains(id) {
                if let Some(value) = metas.solved.get(id).cloned() {
                    return self.unify_at(pattern, &value, metas, bound, depth + 1);
                }
                if !mentions(pattern, *id)
                    && !bound.iter().any(|(left, _)| mentions(pattern, *left))
                {
                    metas.solved.insert(*id, pattern.clone());
                    return true;
                }
                return false;
            }
        }
        if self.unify_structural(pattern, target, metas, bound, depth) {
            return true;
        }
        // Unfold one side's head and retry.
        if let Ok(Some(unfolded)) = self.unfold_head(target) {
            if self.unify_at(pattern, &unfolded, metas, bound, depth + 1) {
                return true;
            }
        }
        if let Ok(Some(unfolded)) = self.unfold_head(pattern) {
            return self.unify_at(&unfolded, target, metas, bound, depth + 1);
        }
        false
    }

    fn unify_structural(
        &mut self,
        pattern: &Term,
        target: &Term,
        metas: &mut Metas,
        bound: &mut Vec<(LocalId, LocalId)>,
        depth: usize,
    ) -> bool {
        match (pattern, target) {
            (Term::Local(a), Term::Local(b)) => {
                a == b || bound.iter().any(|(left, right)| left == a && right == b)
            }
            (Term::Sort(a), Term::Sort(b)) => {
                matches!((a, b), (Universe::Num(0), Universe::Num(0)))
                    || (!matches!(a, Universe::Num(0)) && !matches!(b, Universe::Num(0)))
            }
            (Term::Global(a, _), Term::Global(b, _)) => same_global(a, b),
            (
                Term::App {
                    function: f1,
                    explicit_args: a1,
                    ..
                },
                Term::App {
                    function: f2,
                    explicit_args: a2,
                    ..
                },
            ) => {
                if a1.len() != a2.len() {
                    return false;
                }
                let saved = metas.clone();
                let ok = self.unify_at(f1, f2, metas, bound, depth + 1)
                    && a1
                        .iter()
                        .zip(a2)
                        .all(|(x, y)| self.unify_at(x, y, metas, bound, depth + 1));
                if !ok {
                    *metas = saved;
                }
                ok
            }
            (
                Term::Pi {
                    binders: b1,
                    body: x1,
                },
                Term::Pi {
                    binders: b2,
                    body: x2,
                },
            )
            | (
                Term::Lambda {
                    binders: b1,
                    body: x1,
                },
                Term::Lambda {
                    binders: b2,
                    body: x2,
                },
            ) => {
                let (left, left_body) = split_binders(b1, x1, pattern);
                let (right, right_body) = split_binders(b2, x2, target);
                let count = left.len().min(right.len());
                if count == 0 {
                    return false;
                }
                let saved = metas.clone();
                let depth_before = bound.len();
                let mut ok = true;
                for (l, r) in left.iter().zip(&right).take(count) {
                    if !self.unify_at(&l.ty, &r.ty, metas, bound, depth + 1) {
                        ok = false;
                        break;
                    }
                    bound.push((l.id, r.id));
                }
                if ok {
                    let rest_left = rebuild(&left[count..], &left_body, pattern);
                    let rest_right = rebuild(&right[count..], &right_body, target);
                    ok = self.unify_at(&rest_left, &rest_right, metas, bound, depth + 1);
                }
                bound.truncate(depth_before);
                if !ok {
                    *metas = saved;
                }
                ok
            }
            (Term::NatLiteral { decimal: a, .. }, Term::NatLiteral { decimal: b, .. }) => a == b,
            _ => false,
        }
    }

    // -----------------------------------------------------------------
    // Inference
    // -----------------------------------------------------------------

    /// Instantiate a function type against explicit arguments and an
    /// optional expected result: every binder's value, in binder order, and
    /// the result type. Implicit and instance binders must all be solved.
    pub fn instantiate(
        &mut self,
        ctx: &Ctx,
        function_type: &Term,
        explicit_args: &[Term],
        expected: Option<&Term>,
    ) -> Result<(Vec<(Binder, Term)>, Term), Diagnostic> {
        let (binders, result) = self.telescope(function_type, explicit_args.len())?;
        let mut metas = Metas::default();
        let mut explicit = explicit_args.iter();
        let mut assigned: Vec<(Binder, Option<Term>)> = Vec::new();
        let mut map: BTreeMap<LocalId, Term> = BTreeMap::new();
        for binder in &binders {
            let binder = Binder {
                ty: subst(&binder.ty, &map),
                ..binder.clone()
            };
            if binder.mode == BinderMode::Explicit {
                let argument = explicit.next().cloned().ok_or_else(|| {
                    fail("an application supplies fewer explicit arguments than its telescope")
                })?;
                map.insert(binder.id, argument.clone());
                assigned.push((binder, Some(argument)));
            } else {
                metas.open(binder.id);
                assigned.push((binder, None));
            }
        }
        let result = subst(&result, &map);
        // Unify explicit binder types with the arguments' types, and the
        // result with the expected type, until nothing changes.
        for _ in 0..4 {
            for (binder, value) in &assigned {
                if let Some(argument) = value {
                    if metas.unsolved_in(&binder.ty) {
                        if let Ok(argument_type) = self.infer(ctx, argument) {
                            let pattern = metas.zonk(&binder.ty);
                            self.unify(&pattern, &argument_type, &mut metas);
                        }
                    }
                }
            }
            if let Some(expected) = expected {
                if metas.unsolved_in(&result) {
                    let pattern = metas.zonk(&result);
                    self.unify(&pattern, expected, &mut metas);
                }
            }
            // A solved implicit whose own type still has metas fixes them.
            for (binder, value) in &assigned {
                if value.is_none() && metas.unsolved_in(&binder.ty) {
                    if let Some(solution) = metas.get(binder.id).cloned() {
                        if let Ok(solution_type) = self.infer(ctx, &solution) {
                            let pattern = metas.zonk(&binder.ty);
                            self.unify(&pattern, &solution_type, &mut metas);
                        }
                    }
                }
            }
        }
        let mut out = Vec::new();
        for (binder, value) in assigned {
            let value = match value {
                Some(argument) => argument,
                None => metas.get(binder.id).map(|term| metas.zonk(term)).ok_or_else(|| {
                    fail(format!(
                        "the implicit argument `{}` of an application cannot be determined for Bend, which infers no implicit argument",
                        if binder.spelling.is_empty() { "_" } else { &binder.spelling }
                    ))
                })?,
            };
            if metas.unsolved_in(&value) {
                return Err(fail("an implicit argument is only partly determined"));
            }
            out.push((
                Binder {
                    ty: metas.zonk(&binder.ty),
                    ..binder
                },
                value,
            ));
        }
        Ok((out, metas.zonk(&result)))
    }

    /// The leading binders of a function type that `explicit` explicit
    /// arguments reach (with every implicit binder before the last of
    /// them, and trailing implicits up to the next explicit binder only
    /// when all explicit arguments are consumed), unfolding definitions
    /// when the type is not syntactically a `Pi`.
    fn telescope(&mut self, ty: &Term, explicit: usize) -> Result<(Vec<Binder>, Term), Diagnostic> {
        let mut binders = Vec::new();
        let mut rest = ty.clone();
        let mut seen = 0;
        loop {
            let normalized = match &rest {
                Term::Pi { .. } => rest.clone(),
                other => self.whnf(other)?,
            };
            let Term::Pi {
                binders: group,
                body,
            } = normalized
            else {
                return Ok((binders, rest));
            };
            let mut taken = Vec::new();
            let mut remaining = Vec::new();
            let mut done = false;
            for binder in group {
                if done {
                    remaining.push(binder);
                    continue;
                }
                if binder.mode == BinderMode::Explicit {
                    if seen == explicit {
                        done = true;
                        remaining.push(binder);
                        continue;
                    }
                    seen += 1;
                }
                taken.push(binder);
            }
            binders.extend(taken);
            if !remaining.is_empty() {
                return Ok((
                    binders,
                    Term::Pi {
                        binders: remaining,
                        body,
                    },
                ));
            }
            rest = *body;
            if seen == explicit && !matches!(rest, Term::Pi { .. }) {
                // Trailing implicit binders after the last explicit
                // argument belong to the result only when the result is
                // itself a function type; leave a non-Pi result as is.
                return Ok((binders, rest));
            }
        }
    }

    /// The type of a term in a context.
    pub fn infer(&mut self, ctx: &Ctx, term: &Term) -> Result<Term, Diagnostic> {
        match term {
            Term::Local(id) => ctx_type(ctx, *id)
                .cloned()
                .ok_or_else(|| fail("a local has no type in the Bend lowering context")),
            Term::Sort(Universe::Var(name)) if name == FALSE_SORT => {
                Ok(Term::Sort(Universe::Num(0)))
            }
            Term::Sort(Universe::Num(0)) => Ok(Term::Sort(Universe::Num(1))),
            Term::Sort(_) => Ok(Term::Sort(Universe::Num(2))),
            Term::Global(global, _) => {
                let ty = self.global_type(global)?;
                // A bare global with implicit binders is an application of
                // none of its explicit arguments.
                let (binders, _) = flatten_pi(&ty);
                if binders
                    .first()
                    .is_some_and(|binder| binder.mode != BinderMode::Explicit)
                {
                    let (_, result) = self.instantiate(ctx, &ty, &[], None)?;
                    return Ok(result);
                }
                Ok(ty)
            }
            Term::App {
                function,
                explicit_args,
                ..
            } => {
                if let Term::Global(GlobalRef::DefinedLexicon(_), _) = &**function {
                    if let Some(reduced) = self.unfold_head(term)? {
                        return self.infer(ctx, &reduced);
                    }
                }
                let function_type = match &**function {
                    Term::Global(global, _) => self.global_type(global)?,
                    other => self.infer(ctx, other)?,
                };
                let (_, result) = self.instantiate(ctx, &function_type, explicit_args, None)?;
                Ok(result)
            }
            Term::Pi { .. } => Ok(Term::Sort(Universe::Num(0))),
            Term::Lambda { binders, body } => {
                let mut inner = ctx.clone();
                for binder in binders {
                    inner.push((binder.id, binder.ty.clone()));
                }
                let body_type = self.infer(&inner, body)?;
                Ok(Term::Pi {
                    binders: binders.clone(),
                    body: Box::new(body_type),
                })
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                let mut map = BTreeMap::new();
                map.insert(binder.id, (**value).clone());
                self.infer(ctx, &subst(body, &map))
            }
            Term::NatLiteral { expected_type, .. } => Ok((**expected_type).clone()),
        }
    }

    // -----------------------------------------------------------------
    // Kinds
    // -----------------------------------------------------------------

    /// Is a value of this (Lean) type Bend `Data`, so its binder may be
    /// reused? Conservative: an unknown type is not.
    pub fn is_data(&mut self, ctx: &Ctx, ty: &Term) -> bool {
        self.is_data_at(ctx, ty, 0)
    }

    fn is_data_at(&mut self, ctx: &Ctx, ty: &Term, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        let Ok(normal) = self.whnf(ty) else {
            return false;
        };
        let (head, args) = spine(&normal);
        match head {
            Term::Global(GlobalRef::Core(core), _) => match core {
                CoreRef::Eq => true,
                CoreRef::And => args.iter().all(|arg| self.is_data_at(ctx, arg, depth + 1)),
                CoreRef::Or => false,
                CoreRef::Exists => match args.first() {
                    Some(Term::Lambda { binders, body }) => {
                        let mut inner = ctx.clone();
                        for binder in binders {
                            inner.push((binder.id, binder.ty.clone()));
                        }
                        binders
                            .iter()
                            .all(|binder| self.is_data_at(ctx, &binder.ty, depth + 1))
                            && self.is_data_at(&inner, body, depth + 1)
                    }
                    _ => false,
                },
                // A negation, a biconditional and a unique existence hold
                // functions, which Bend never copies.
                CoreRef::Not | CoreRef::Iff | CoreRef::ExistsUnique => false,
            },
            Term::Global(GlobalRef::External(external), _) => {
                let Some(row) = self.external_row(external) else {
                    return false;
                };
                match row.kind {
                    ConstantKind::Type => match row.form {
                        None => true,
                        Some(TypeForm::List | TypeForm::Pair) => {
                            args.iter().all(|arg| self.is_data_at(ctx, arg, depth + 1))
                        }
                    },
                    _ => row.data.unwrap_or(false),
                }
            }
            Term::Local(id) => {
                // A type variable bound at sort `Type` lowers to a `Data`
                // binder; one at `Prop` lowers to `Type`.
                let Some(ty) = ctx_type(ctx, *id).cloned() else {
                    return false;
                };
                matches!(self.whnf(&ty), Ok(Term::Sort(Universe::Num(n))) if n >= 1)
            }
            _ => false,
        }
    }

    fn external_row(
        &self,
        external: &ExternalConstRef,
    ) -> Option<&'static crate::backend::bend::prelude::Constant> {
        let id = QualifiedId::parse(&external.entry).ok()?;
        let entry = self.project.closure.entry(&id)?;
        let canonical = entry.signature_canonical.as_ref()?;
        self.registry.constant(&external.lean_name, canonical)
    }

    fn require_row(
        &self,
        external: &ExternalConstRef,
    ) -> Result<&'static crate::backend::bend::prelude::Constant, Diagnostic> {
        self.external_row(external).ok_or_else(|| {
            fail(format!(
                "the Lean constant `{}` of `{}` has no Bend prelude definition under its signature",
                external.lean_name, external.entry
            ))
        })
    }

    /// The Bend quantity of a proposition's or type's values: `&2` for
    /// `Data`, else `&1`.
    pub fn quantity_of(&mut self, ctx: &Ctx, ty: &Term) -> String {
        if self.is_data(ctx, ty) {
            "&2".to_owned()
        } else {
            "&1".to_owned()
        }
    }

    // -----------------------------------------------------------------
    // Lowering terms
    // -----------------------------------------------------------------

    /// Lower a type of binders: `Prop` to `Type`, `Type` to `Data`.
    pub fn lower_sort(universe: &Universe) -> BTerm {
        if matches!(universe, Universe::Var(name) if name == FALSE_SORT) {
            BTerm::Name(Name::synthetic("Empty"))
        } else if matches!(universe, Universe::Num(0)) {
            BTerm::Kind("Type")
        } else {
            BTerm::Kind("Data")
        }
    }

    /// Lower a term against an optional expected type.
    #[allow(clippy::too_many_lines)]
    pub fn lower(
        &mut self,
        ctx: &Ctx,
        term: &Term,
        expected: Option<&Term>,
    ) -> Result<BTerm, Diagnostic> {
        match term {
            Term::Local(id) => Ok(BTerm::Name(self.local_name(*id))),
            Term::Sort(universe) => Ok(Self::lower_sort(universe)),
            Term::NatLiteral {
                decimal,
                expected_type,
            } => self.lower_numeral(decimal, expected_type),
            Term::Global(..) => self.lower_application(ctx, term, &[], expected),
            Term::App {
                function,
                explicit_args,
                ..
            } => self.lower_application(ctx, function, explicit_args, expected),
            Term::Pi { binders, body } => {
                let mut inner = ctx.clone();
                let mut lowered = Vec::new();
                for binder in binders {
                    let domain = self.lower(&inner, &binder.ty, None)?;
                    inner.push((binder.id, binder.ty.clone()));
                    lowered.push((binder.clone(), domain));
                }
                let mut out = self.lower(&inner, body, None)?;
                for (binder, domain) in lowered.into_iter().rev() {
                    let dependent = mentions(&rebuild_tail(binders, &binder, body), binder.id);
                    let erased = matches!(self.whnf(&binder.ty)?, Term::Sort(Universe::Num(_)));
                    out = BTerm::Pi {
                        name: if dependent || erased {
                            Some(self.local_name(binder.id))
                        } else {
                            None
                        },
                        erased,
                        domain: Box::new(domain),
                        codomain: Box::new(out),
                    };
                }
                Ok(out)
            }
            Term::Lambda { binders, body } => {
                let mut inner = ctx.clone();
                for binder in binders {
                    inner.push((binder.id, binder.ty.clone()));
                }
                let expected_body = match expected {
                    Some(ty) => self.pi_codomain(ty, binders)?,
                    None => None,
                };
                let mut out = self.lower(&inner, body, expected_body.as_ref())?;
                for binder in binders.iter().rev() {
                    out = BTerm::Lam(self.local_name(binder.id), Box::new(out));
                }
                Ok(out)
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                let mut map = BTreeMap::new();
                map.insert(binder.id, (**value).clone());
                self.lower(ctx, &subst(body, &map), expected)
            }
        }
    }

    /// The codomain of a function type after `binders`, renamed to them.
    fn pi_codomain(&mut self, ty: &Term, binders: &[Binder]) -> Result<Option<Term>, Diagnostic> {
        let mut rest = ty.clone();
        let mut map = BTreeMap::new();
        for binder in binders {
            let normal = self.whnf(&rest)?;
            let Term::Pi {
                binders: group,
                body,
            } = normal
            else {
                return Ok(None);
            };
            let mut group = group.into_iter();
            let Some(first) = group.next() else {
                return Ok(None);
            };
            map.insert(first.id, Term::Local(binder.id));
            let remaining: Vec<Binder> = group.collect();
            rest = if remaining.is_empty() {
                *body
            } else {
                Term::Pi {
                    binders: remaining,
                    body,
                }
            };
        }
        Ok(Some(subst(&rest, &map)))
    }

    fn lower_numeral(&mut self, decimal: &str, expected_type: &Term) -> Result<BTerm, Diagnostic> {
        let normal = self.whnf(expected_type)?;
        let (head, _) = spine(&normal);
        if let Term::Global(GlobalRef::External(external), _) = head {
            let kind = self.require_row(external)?.bend.clone();
            let magnitude = numeral::term(decimal, |bend| self.prelude(bend, Origin::Numeral))
                .ok_or_else(|| fail(format!("the numeral `{decimal}` is not a natural number")));
            return match kind.as_str() {
                "Nat" => magnitude,
                "Lean.Int" => {
                    let magnitude = magnitude?;
                    let head = self.prelude("ofNat", Origin::Numeral);
                    Ok(BTerm::Constructor(head, vec![magnitude]))
                }
                other => Err(fail(format!(
                    "a numeral of type `{other}` has no Bend lowering"
                ))),
            };
        }
        Err(fail(
            "a numeral's expected type is not a prelude number type",
        ))
    }

    /// Lower `function(explicit_args)` with every implicit argument.
    #[allow(clippy::too_many_lines)]
    fn lower_application(
        &mut self,
        ctx: &Ctx,
        function: &Term,
        explicit_args: &[Term],
        expected: Option<&Term>,
    ) -> Result<BTerm, Diagnostic> {
        let applied = Term::App {
            function: Box::new(function.clone()),
            explicit_args: explicit_args.to_vec(),
            omitted_implicit_binders: Vec::new(),
        };
        match function {
            Term::Global(GlobalRef::DefinedLexicon(defined), _) => {
                let value = self.defined_value(defined)?;
                let reduced = if explicit_args.is_empty() {
                    value
                } else {
                    self.whnf_once_beta(&value, explicit_args)
                };
                self.lower(ctx, &reduced, expected)
            }
            Term::Global(GlobalRef::Core(core), _) => self.lower_core(ctx, *core, explicit_args),
            Term::Global(GlobalRef::External(external), _) => {
                if let Some(core) = self.external_core(external) {
                    return self.lower_core(ctx, core, explicit_args);
                }
                if let Some(assumption) = self.registry.assumption_for(&external.lean_name) {
                    let name = assumption.name.clone();
                    let premise = premise_name(&name);
                    self.assumptions.insert(name, assumption.bend_type.clone());
                    let ty = self.global_type(&GlobalRef::External(external.clone()))?;
                    let (values, _) = self.instantiate(ctx, &ty, explicit_args, expected)?;
                    let mut args = Vec::new();
                    for (binder, value) in values {
                        args.push(self.lower(ctx, &value, Some(&binder.ty))?);
                    }
                    let head = Name::synthetic(premise);
                    return Ok(if args.is_empty() {
                        BTerm::Name(head)
                    } else {
                        BTerm::Call(head, args)
                    });
                }
                if let Some(lowered) =
                    self.lower_logic_constructor(ctx, external, explicit_args, expected)?
                {
                    return Ok(lowered);
                }
                let row = self.require_row(external)?;
                let origin = Origin::Form {
                    package: external.package.clone(),
                    entry: external
                        .entry
                        .split("::")
                        .nth(1)
                        .unwrap_or(&external.entry)
                        .to_owned(),
                    form: "denotation".to_owned(),
                };
                let ty = self.global_type(&GlobalRef::External(external.clone()))?;
                let (values, _) = self.instantiate(ctx, &ty, explicit_args, expected)?;
                let mut args = Vec::new();
                for prefix in &row.prefix {
                    args.push(self.prelude_type_name(prefix));
                }
                for (binder, value) in &values {
                    args.push(self.lower(ctx, value, Some(&binder.ty))?);
                }
                match row.kind {
                    ConstantKind::Constructor => {
                        if !args.is_empty() {
                            return Err(fail(format!(
                                "the constructor `{}` is applied, but its Bend form is a literal",
                                external.lean_name
                            )));
                        }
                        Ok(match row.bend.as_str() {
                            "0n" => BTerm::Nat("0".to_owned()),
                            literal => {
                                let head = literal.trim_end_matches("{}");
                                BTerm::Constructor(Name::new(head, origin), Vec::new())
                            }
                        })
                    }
                    ConstantKind::Type => match row.form {
                        Some(TypeForm::List) => {
                            let [element] = args.as_slice() else {
                                return Err(fail("`List` takes exactly one type argument"));
                            };
                            Ok(BTerm::Datatype(
                                Name::new("List", origin),
                                vec!["&2".to_owned()],
                                vec![element.clone()],
                            ))
                        }
                        Some(TypeForm::Pair) | None => {
                            let name = if row.base {
                                Name::new(row.bend.clone(), origin)
                            } else {
                                self.prelude(&row.bend, origin)
                            };
                            Ok(if args.is_empty() {
                                BTerm::Name(name)
                            } else {
                                BTerm::Call(name, args)
                            })
                        }
                    },
                    ConstantKind::Def | ConstantKind::Law => {
                        let name = if row.base {
                            Name::new(row.bend.clone(), origin)
                        } else {
                            self.prelude(&row.bend, origin)
                        };
                        Ok(BTerm::Call(name, args))
                    }
                    ConstantKind::Assumption => Err(fail(format!(
                        "`{}` is an assumption the registry does not list",
                        external.lean_name
                    ))),
                }
            }
            Term::Global(GlobalRef::Document(reference), _) => {
                let declaration = self.document(reference)?;
                let origin = Origin::Reference {
                    module: reference.module.clone(),
                    component: reference.component.clone(),
                };
                let text = if reference.module == self.module {
                    declaration.lean_name.clone()
                } else {
                    self.referenced_modules.insert(reference.module.clone());
                    let generated = self
                        .project
                        .generated_modules
                        .get(&reference.module)
                        .cloned()
                        .unwrap_or_default();
                    format!("{}.{}", module_alias(&generated), declaration.lean_name)
                };
                let ty = Self::declaration_type(declaration);
                let (values, _) = self.instantiate(ctx, &ty, explicit_args, expected)?;
                let mut args = Vec::new();
                // A cited theorem's assumption premises are this theorem's
                // too, passed on as its leading arguments.
                let premises = self
                    .assumption_table
                    .get(&(reference.module.clone(), reference.component.clone()))
                    .cloned()
                    .unwrap_or_default();
                for (premise, premise_type) in premises {
                    args.push(BTerm::Name(Name::synthetic(premise_name(&premise))));
                    self.assumptions.insert(premise, premise_type);
                }
                for (binder, value) in &values {
                    args.push(self.lower(ctx, value, Some(&binder.ty))?);
                }
                let name = Name::new(text, origin);
                Ok(BTerm::Call(name, args))
            }
            Term::Local(id) => {
                let name = self.local_name(*id);
                if explicit_args.is_empty() {
                    return Ok(BTerm::Name(name));
                }
                let ty = self.infer(ctx, function)?;
                let (values, _) = self.instantiate(ctx, &ty, explicit_args, expected)?;
                let mut args = Vec::new();
                for (binder, value) in &values {
                    if binder.mode != BinderMode::Explicit {
                        return Err(fail(
                            "a local function with implicit binders has no Bend call form",
                        ));
                    }
                    args.push(self.lower(ctx, value, Some(&binder.ty))?);
                }
                Ok(BTerm::Call(name, args))
            }
            Term::Lambda { .. } | Term::App { .. } | Term::Let { .. } => {
                let reduced = self.whnf(&applied)?;
                if reduced == applied {
                    return Err(fail(
                        "an application of a compound function has no Bend form",
                    ));
                }
                self.lower(ctx, &reduced, expected)
            }
            Term::Pi { .. } | Term::Sort(_) | Term::NatLiteral { .. } => {
                Err(fail("an application of a non-function has no Bend form"))
            }
        }
    }

    /// The logic introduction rules lower to Bend's own value forms, so
    /// their types carry the quantities `lower_core` gives the
    /// propositions they build: a pair, `Inl`/`Inr`, a dependent pair.
    fn lower_logic_constructor(
        &mut self,
        ctx: &Ctx,
        external: &ExternalConstRef,
        explicit_args: &[Term],
        expected: Option<&Term>,
    ) -> Result<Option<BTerm>, Diagnostic> {
        let origin = Origin::Form {
            package: external.package.clone(),
            entry: external
                .entry
                .split("::")
                .nth(1)
                .unwrap_or(&external.entry)
                .to_owned(),
            form: "denotation".to_owned(),
        };
        let shape = match external.lean_name.as_str() {
            "And.intro" | "Iff.intro" | "Exists.intro" => "pair",
            "Or.inl" => "Inl",
            "Or.inr" => "Inr",
            _ => return Ok(None),
        };
        let ty = self.global_type(&GlobalRef::External(external.clone()))?;
        let (values, _) = self.instantiate(ctx, &ty, explicit_args, expected)?;
        let explicit: Vec<(Binder, Term)> = values
            .into_iter()
            .filter(|(binder, _)| binder.mode == BinderMode::Explicit)
            .collect();
        let mut lowered = Vec::new();
        for (binder, value) in &explicit {
            lowered.push(self.lower(ctx, value, Some(&binder.ty))?);
        }
        Ok(Some(match (shape, lowered.as_slice()) {
            ("pair", [a, b]) => BTerm::Pair(Box::new(a.clone()), Box::new(b.clone())),
            ("Inl" | "Inr", [h]) => BTerm::Constructor(Name::new(shape, origin), vec![h.clone()]),
            _ => {
                return Err(fail(format!(
                    "`{}` is applied to {} explicit argument(s), which has no Bend value form",
                    external.lean_name,
                    lowered.len()
                )))
            }
        }))
    }

    fn whnf_once_beta(&mut self, value: &Term, args: &[Term]) -> Term {
        match value {
            Term::Lambda { binders, body } => beta(binders, body, args),
            other => Term::App {
                function: Box::new(other.clone()),
                explicit_args: args.to_vec(),
                omitted_implicit_binders: Vec::new(),
            },
        }
    }

    fn prelude_type_name(&mut self, bend: &str) -> BTerm {
        if bend.starts_with("Lean.") {
            BTerm::Name(self.prelude(
                bend,
                Origin::Synthetic(super::syntax::SYNTAX_ORIGIN.to_owned()),
            ))
        } else {
            BTerm::Name(Name::synthetic(bend))
        }
    }

    /// Lower a core connective.
    fn lower_core(&mut self, ctx: &Ctx, core: CoreRef, args: &[Term]) -> Result<BTerm, Diagnostic> {
        let origin = core_origin(core);
        match (core, args) {
            (CoreRef::Eq, [left, right]) => {
                let ty = match self.infer(ctx, left) {
                    Ok(ty) => ty,
                    Err(_) => self.infer(ctx, right)?,
                };
                let left_b = self.lower(ctx, left, Some(&ty))?;
                let right_b = self.lower(ctx, right, Some(&ty))?;
                let ty_b = self.lower(ctx, &ty, None)?;
                Ok(BTerm::Equal(
                    Box::new(left_b),
                    Box::new(right_b),
                    Box::new(ty_b),
                ))
            }
            // Conjunction, disjunction and existence carry the quantities
            // of their parts, so a proposition built from equations is
            // `Data` and its proofs reusable (`Sigma<&2, &2, ..>`); Bend's
            // `A & B` and `&x: A -> B` sugars are quantity 1.
            (CoreRef::And, [left, right]) => {
                let (qa, qb) = (self.quantity_of(ctx, left), self.quantity_of(ctx, right));
                let left_b = self.lower(ctx, left, None)?;
                let right_b = self.lower(ctx, right, None)?;
                let dummy = self.fresh.local();
                self.names.insert(dummy, "llx".to_owned());
                Ok(BTerm::Datatype(
                    Name::new("Sigma", origin.clone()),
                    vec![qa, qb],
                    vec![
                        left_b,
                        BTerm::Lam(Name::new("llx", origin), Box::new(right_b)),
                    ],
                ))
            }
            // A disjunction stays affine: the prelude's assumption types
            // (excluded middle) state it at `&1`, and a case split consumes
            // it once.
            (CoreRef::Or, [left, right]) => Ok(BTerm::Datatype(
                Name::new("Either", origin),
                vec!["&1".to_owned(), "&1".to_owned()],
                vec![self.lower(ctx, left, None)?, self.lower(ctx, right, None)?],
            )),
            (CoreRef::Not, [inner]) => Ok(BTerm::Pi {
                name: None,
                erased: false,
                domain: Box::new(self.lower(ctx, inner, None)?),
                codomain: Box::new(BTerm::Name(Name::new("Empty", origin))),
            }),
            (CoreRef::Iff, [left, right]) => {
                let l = self.lower(ctx, left, None)?;
                let r = self.lower(ctx, right, None)?;
                Ok(BTerm::Product(
                    Box::new(BTerm::Pi {
                        name: None,
                        erased: false,
                        domain: Box::new(l.clone()),
                        codomain: Box::new(r.clone()),
                    }),
                    Box::new(BTerm::Pi {
                        name: None,
                        erased: false,
                        domain: Box::new(r),
                        codomain: Box::new(l),
                    }),
                ))
            }
            (CoreRef::Exists, [predicate]) => {
                let predicate = self.whnf(predicate)?;
                let Term::Lambda { binders, body } = &predicate else {
                    return Err(fail("an existential's predicate is not a lambda"));
                };
                let [binder, rest @ ..] = binders.as_slice() else {
                    return Err(fail("an existential's predicate binds nothing"));
                };
                let body_term = if rest.is_empty() {
                    (**body).clone()
                } else {
                    Term::App {
                        function: Box::new(Term::Global(
                            GlobalRef::Core(CoreRef::Exists),
                            Vec::new(),
                        )),
                        explicit_args: vec![Term::Lambda {
                            binders: rest.to_vec(),
                            body: body.clone(),
                        }],
                        omitted_implicit_binders: Vec::new(),
                    }
                };
                let domain = self.lower(ctx, &binder.ty, None)?;
                let mut inner = ctx.clone();
                inner.push((binder.id, binder.ty.clone()));
                let qa = self.quantity_of(ctx, &binder.ty);
                let qb = self.quantity_of(&inner, &body_term);
                let codomain = self.lower(&inner, &body_term, None)?;
                Ok(BTerm::Datatype(
                    Name::new("Sigma", origin),
                    vec![qa, qb],
                    vec![
                        domain,
                        BTerm::Lam(self.local_name(binder.id), Box::new(codomain)),
                    ],
                ))
            }
            (CoreRef::ExistsUnique, [predicate]) => {
                let expanded = self.expand_exists_unique(predicate)?;
                self.lower(ctx, &expanded, None)
            }
            _ => Err(fail(format!(
                "the core connective `{}` is applied to {} argument(s), which has no Bend form",
                core.lean_name(),
                args.len()
            ))),
        }
    }

    /// `ExistsUnique (fun x => P)` as `Exists (fun x => And P (∀ y, P[y] → y = x))`.
    pub fn expand_exists_unique(&mut self, predicate: &Term) -> Result<Term, Diagnostic> {
        let predicate = self.whnf(predicate)?;
        let Term::Lambda { binders, body } = &predicate else {
            return Err(fail("a unique existential's predicate is not a lambda"));
        };
        let [binder] = binders.as_slice() else {
            return Err(fail("a unique existential binds exactly one variable"));
        };
        let y = self.fresh.local();
        let mut map = BTreeMap::new();
        map.insert(binder.id, Term::Local(y));
        let renamed = subst(body, &map);
        let core = |core: CoreRef| Term::Global(GlobalRef::Core(core), Vec::new());
        let app = |function: Term, args: Vec<Term>| Term::App {
            function: Box::new(function),
            explicit_args: args,
            omitted_implicit_binders: Vec::new(),
        };
        let hypothesis = self.fresh.local();
        let uniqueness = Term::Pi {
            binders: vec![
                Binder {
                    id: y,
                    mode: BinderMode::Explicit,
                    ty: binder.ty.clone(),
                    spelling: binder.spelling.clone(),
                },
                Binder {
                    id: hypothesis,
                    mode: BinderMode::Explicit,
                    ty: renamed,
                    spelling: String::new(),
                },
            ],
            body: Box::new(app(
                core(CoreRef::Eq),
                vec![Term::Local(y), Term::Local(binder.id)],
            )),
        };
        Ok(app(
            core(CoreRef::Exists),
            vec![Term::Lambda {
                binders: binders.clone(),
                body: Box::new(app(core(CoreRef::And), vec![(**body).clone(), uniqueness])),
            }],
        ))
    }
}

/// Syntactic first-order matching of `pattern` (holding `metas`) against
/// `target`, without unfolding: Lean's `rw` finds instances by keyed
/// syntactic matching, not by definitional unfolding.
pub fn syntactic_match(pattern: &Term, target: &Term, metas: &mut Metas) -> bool {
    if let Term::Local(id) = pattern {
        if metas.open.contains(id) {
            if let Some(value) = metas.solved.get(id).cloned() {
                return crate::elaborate::expressions::unify_closed(&value, target);
            }
            metas.solved.insert(*id, target.clone());
            return true;
        }
    }
    match (pattern, target) {
        (Term::Local(a), Term::Local(b)) => a == b,
        (Term::Global(a, _), Term::Global(b, _)) => same_global(a, b),
        (
            Term::App {
                function: f1,
                explicit_args: a1,
                ..
            },
            Term::App {
                function: f2,
                explicit_args: a2,
                ..
            },
        ) => {
            a1.len() == a2.len()
                && syntactic_match(f1, f2, metas)
                && a1.iter().zip(a2).all(|(x, y)| syntactic_match(x, y, metas))
        }
        (Term::NatLiteral { decimal: a, .. }, Term::NatLiteral { decimal: b, .. }) => a == b,
        (Term::Sort(_), Term::Sort(_)) => true,
        _ => false,
    }
}

/// The premise name an assumption takes in a generated statement.
#[must_use]
pub fn premise_name(assumption: &str) -> String {
    format!("ll_{}", assumption.replace('-', "_"))
}

fn core_origin(core: CoreRef) -> Origin {
    let entry = match core {
        CoreRef::Eq => "eq",
        CoreRef::And => "land",
        CoreRef::Or => "lor",
        CoreRef::Not => "lnot",
        CoreRef::Iff => "iff",
        CoreRef::Exists | CoreRef::ExistsUnique => "exists",
    };
    Origin::Form {
        package: "lexlean.core".to_owned(),
        entry: entry.to_owned(),
        form: "denotation".to_owned(),
    }
}

/// Beta-reduce `(fun binders => body) args`, leaving extra arguments
/// applied and missing ones abstracted.
#[must_use]
pub fn beta(binders: &[Binder], body: &Term, args: &[Term]) -> Term {
    let mut map = BTreeMap::new();
    let count = binders.len().min(args.len());
    for (binder, argument) in binders.iter().zip(args).take(count) {
        map.insert(binder.id, argument.clone());
    }
    let rest_binders: Vec<Binder> = binders[count..]
        .iter()
        .map(|binder| Binder {
            ty: subst(&binder.ty, &map),
            ..binder.clone()
        })
        .collect();
    let reduced = subst(body, &map);
    let reduced = if rest_binders.is_empty() {
        reduced
    } else {
        Term::Lambda {
            binders: rest_binders,
            body: Box::new(reduced),
        }
    };
    if args.len() > count {
        Term::App {
            function: Box::new(reduced),
            explicit_args: args[count..].to_vec(),
            omitted_implicit_binders: Vec::new(),
        }
    } else {
        reduced
    }
}

/// The head and arguments of an application spine.
#[must_use]
pub fn spine(term: &Term) -> (&Term, Vec<Term>) {
    match term {
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            let (head, mut args) = spine(function);
            args.extend(explicit_args.iter().cloned());
            (head, args)
        }
        other => (other, Vec::new()),
    }
}

fn split_binders(binders: &[Binder], body: &Term, _whole: &Term) -> (Vec<Binder>, Term) {
    let mut all = binders.to_vec();
    let mut rest = body.clone();
    while let Term::Pi {
        binders: more,
        body: inner,
    } = &rest
    {
        if !matches!(_whole, Term::Pi { .. }) {
            break;
        }
        all.extend(more.iter().cloned());
        rest = (**inner).clone();
    }
    (all, rest)
}

fn rebuild(binders: &[Binder], body: &Term, whole: &Term) -> Term {
    if binders.is_empty() {
        return body.clone();
    }
    if matches!(whole, Term::Pi { .. }) {
        Term::Pi {
            binders: binders.to_vec(),
            body: Box::new(body.clone()),
        }
    } else {
        Term::Lambda {
            binders: binders.to_vec(),
            body: Box::new(body.clone()),
        }
    }
}

/// The part of a Pi after `binder`: later binders' types and the body.
fn rebuild_tail(binders: &[Binder], binder: &Binder, body: &Term) -> Term {
    let position = binders
        .iter()
        .position(|candidate| candidate.id == binder.id)
        .unwrap_or(binders.len());
    let later = &binders[position + 1..];
    if later.is_empty() {
        body.clone()
    } else {
        Term::Pi {
            binders: later.to_vec(),
            body: Box::new(body.clone()),
        }
    }
}
