//! The closed Bend 2 syntax the backend emits, and its printer.
//!
//! The lowering builds this tree and nothing else, so no generated module
//! holds a construct outside it: no `@unsafe`, no foreign import, no `?`
//! hole, no comment, no device call. The printer traces every
//! non-whitespace token to an origin (§20.3), as the Lean printer does.

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::source::coverage::Origin;

/// Bend syntax keywords and punctuation trace to this synthetic origin.
pub const SYNTAX_ORIGIN: &str = "core:bend-syntax/1";

/// Module boilerplate traces to this synthetic origin.
pub const PREAMBLE_ORIGIN: &str = "core:bend-preamble/1";

/// A named occurrence: a local, a global, or a constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    /// The printed text.
    pub text: String,
    /// What it traces to.
    pub origin: Origin,
}

impl Name {
    /// A name with an origin.
    pub fn new(text: impl Into<String>, origin: Origin) -> Self {
        Self {
            text: text.into(),
            origin,
        }
    }

    /// A name the backend itself introduces.
    pub fn synthetic(text: impl Into<String>) -> Self {
        Self::new(text, Origin::Synthetic(SYNTAX_ORIGIN.to_owned()))
    }
}

/// A binder quantity mark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantity {
    /// Affine, unmarked.
    Affine,
    /// `+`: reusable, the domain is `Data`.
    Reusable,
    /// `-`: erased, used only in types and proofs.
    Erased,
    /// `~`: a template, substituted by a closed argument where it is used.
    Template,
}

impl Quantity {
    const fn mark(self) -> &'static str {
        match self {
            Self::Affine => "",
            Self::Reusable => "+",
            Self::Erased => "-",
            Self::Template => "~",
        }
    }
}

/// A Bend term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BTerm {
    /// A variable or a global name.
    Name(Name),
    /// `f(a, b)`.
    Call(Name, Vec<BTerm>),
    /// `x => body`.
    Lam(Name, Box<BTerm>),
    /// `@x: A -> B`, `@-x: A -> B`, or `A -> B` when the name is absent.
    Pi {
        /// The bound name, absent for a non-dependent arrow.
        name: Option<Name>,
        /// Whether the binder is erased.
        erased: bool,
        /// The domain.
        domain: Box<BTerm>,
        /// The codomain.
        codomain: Box<BTerm>,
    },
    /// `&x: A -> B`.
    Sigma {
        /// The bound name.
        name: Name,
        /// The first component's type.
        domain: Box<BTerm>,
        /// The second component's type.
        codomain: Box<BTerm>,
    },
    /// `A & B`.
    Product(Box<BTerm>, Box<BTerm>),
    /// `Either<&1, &1, A, B>` style datatype application `D<args>`.
    Datatype(Name, Vec<String>, Vec<BTerm>),
    /// `(a, b)`.
    Pair(Box<BTerm>, Box<BTerm>),
    /// `K{a, b}`.
    Constructor(Name, Vec<BTerm>),
    /// `{a == b : T}`.
    Equal(Box<BTerm>, Box<BTerm>, Box<BTerm>),
    /// `{==}`.
    Refl,
    /// `3n`.
    Nat(String),
    /// `1n+t`.
    Succ(Box<BTerm>),
    /// `Type` or `Data`.
    Kind(&'static str),
    /// `{t : T}`.
    Ann(Box<BTerm>, Box<BTerm>),
    /// `_`, the rewrite motive's hole.
    Hole,
    /// A parenthesized body with statements.
    Block(Box<Body>),
    /// `"text"`, a Base `String` literal, already escaped for Bend.
    Str(String),
    /// `~t`, a closed argument to a template binder.
    Template(Box<BTerm>),
    /// `255`, a Base `U32` literal.
    U32(u32),
    /// `(f)(a, b)`, the application of a function-valued term.
    Apply(Box<BTerm>, Vec<BTerm>),
}

/// A statement before a body's tail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// `%e : P`, at a traced source range.
    Rewrite {
        /// The equation.
        proof: BTerm,
        /// The motive, `_` marking the rewritten position.
        motive: BTerm,
        /// The source step.
        source: EmitSource,
    },
    /// `x = v`.
    Let {
        /// The bound name.
        name: Name,
        /// The value.
        value: BTerm,
        /// The source step.
        source: EmitSource,
    },
    /// `+x = v`: a reusable let, whose value is `Data`.
    Share {
        /// The bound name.
        name: Name,
        /// The value.
        value: BTerm,
        /// The source step.
        source: EmitSource,
    },
}

/// A match pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// `0n`.
    Zero,
    /// `1n+p`.
    Succ(Name),
    /// `K{a, b}`.
    Constructor(Name, Vec<Name>),
    /// `(a, b)`.
    Pair(Name, Name),
}

/// The tail of a body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tail {
    /// A term, at a traced source range.
    Term(BTerm, EmitSource),
    /// `match x:` with its cases.
    Match {
        /// The matched parameter.
        scrutinee: Name,
        /// The cases, in order.
        cases: Vec<(Pattern, Body)>,
        /// The source step.
        source: EmitSource,
    },
}

/// A definition or case body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Body {
    /// Statements in order.
    pub stmts: Vec<Stmt>,
    /// The tail.
    pub tail: Tail,
}

impl Body {
    /// A body that is one term.
    #[must_use]
    pub fn term(term: BTerm, source: EmitSource) -> Self {
        Self {
            stmts: Vec::new(),
            tail: Tail::Term(term, source),
        }
    }
}

/// A typed parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    /// The quantity mark.
    pub quantity: Quantity,
    /// The name.
    pub name: Name,
    /// The type.
    pub ty: BTerm,
    /// Where it traces to.
    pub source: EmitSource,
}

/// A top-level item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// `law name:` with `for` clauses and a claim, then its proof def.
    Law {
        /// The law and proof name.
        name: Name,
        /// The `for` clauses.
        params: Vec<Param>,
        /// The claim.
        claim: BTerm,
        /// The claim's source.
        claim_source: EmitSource,
        /// The proof body.
        proof: Body,
        /// The whole declaration's source.
        source: EmitSource,
    },
    /// `type Name<-A: Data, ..> is Data:` with one constructor per line.
    Type {
        /// The type name.
        name: Name,
        /// The erased type parameters, each of kind `Data`.
        parameters: Vec<Name>,
        /// An erased index after them, with its type: an indexed family
        /// (SPEC.md §18.11.3).
        index: Option<(Name, BTerm)>,
        /// The type's own kind, `Data` or `Type`.
        kind: &'static str,
        /// The constructors, each with its named, typed fields.
        constructors: Vec<(Name, Vec<(Name, BTerm)>)>,
        /// The whole declaration's source.
        source: EmitSource,
    },
    /// `def name(params) -> T:` with its body.
    Def {
        /// The name.
        name: Name,
        /// The parameters.
        params: Vec<Param>,
        /// The result type.
        result: BTerm,
        /// The result type's source.
        result_source: EmitSource,
        /// The body.
        body: Body,
        /// The whole declaration's source.
        source: EmitSource,
    },
}

/// One import line: `import <path> as <alias>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    /// The relative path.
    pub path: String,
    /// The alias.
    pub alias: String,
}

/// A whole generated module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// Imports after `import Base`, in order.
    pub imports: Vec<Import>,
    /// Items in order.
    pub items: Vec<Item>,
}

struct Printer<'e> {
    emitter: &'e mut Emitter,
    source: EmitSource,
    role: MapRole,
    node: usize,
}

impl Printer<'_> {
    fn piece(&mut self, text: &str, kind: &str, origin: Origin) {
        self.emitter.piece(
            text,
            kind,
            origin,
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn kw(&mut self, text: &str) {
        self.piece(text, "keyword", Origin::Synthetic(SYNTAX_ORIGIN.to_owned()));
    }

    fn sym(&mut self, text: &str) {
        self.piece(text, "symbol", Origin::Synthetic(SYNTAX_ORIGIN.to_owned()));
    }

    fn name(&mut self, name: &Name) {
        self.piece(&name.text, "identifier", name.origin.clone());
    }

    fn ws(&mut self, text: &str) {
        self.emitter.ws(text);
    }

    fn pad(&mut self, depth: usize) {
        self.ws(&"  ".repeat(depth));
    }

    fn quantity(&mut self, quantity: Quantity) {
        let mark = quantity.mark();
        if !mark.is_empty() {
            self.sym(mark);
        }
    }

    /// Print a term; `atomic` asks for parentheses around a compound one.
    #[allow(clippy::too_many_lines)]
    fn term(&mut self, term: &BTerm, atomic: bool, depth: usize) {
        match term {
            BTerm::Name(name) => self.name(name),
            BTerm::Call(head, args) => {
                self.name(head);
                self.sym("(");
                for (index, argument) in args.iter().enumerate() {
                    if index > 0 {
                        self.sym(",");
                        self.ws(" ");
                    }
                    self.term(argument, matches!(argument, BTerm::Lam(..)), depth);
                }
                self.sym(")");
            }
            BTerm::Lam(name, body) => {
                if atomic {
                    self.sym("(");
                }
                self.name(name);
                self.ws(" ");
                self.sym("=>");
                self.ws(" ");
                self.term(body, false, depth);
                if atomic {
                    self.sym(")");
                }
            }
            BTerm::Pi {
                name,
                erased,
                domain,
                codomain,
            } => {
                if atomic {
                    self.sym("(");
                }
                match name {
                    Some(name) => {
                        self.sym("@");
                        if *erased {
                            self.sym("-");
                        }
                        self.name(name);
                        self.sym(":");
                        self.ws(" ");
                        self.term(domain, true, depth);
                    }
                    None => self.term(domain, true, depth),
                }
                self.ws(" ");
                self.sym("->");
                self.ws(" ");
                self.term(codomain, false, depth);
                if atomic {
                    self.sym(")");
                }
            }
            BTerm::Sigma {
                name,
                domain,
                codomain,
            } => {
                if atomic {
                    self.sym("(");
                }
                self.sym("&");
                self.name(name);
                self.sym(":");
                self.ws(" ");
                self.term(domain, true, depth);
                self.ws(" ");
                self.sym("->");
                self.ws(" ");
                self.term(codomain, false, depth);
                if atomic {
                    self.sym(")");
                }
            }
            BTerm::Product(left, right) => {
                if atomic {
                    self.sym("(");
                }
                self.term(left, true, depth);
                self.ws(" ");
                self.sym("&");
                self.ws(" ");
                self.term(right, true, depth);
                if atomic {
                    self.sym(")");
                }
            }
            BTerm::Datatype(head, quantities, args) => {
                self.name(head);
                self.sym("<");
                let mut first = true;
                for quantity in quantities {
                    if !first {
                        self.sym(",");
                        self.ws(" ");
                    }
                    first = false;
                    self.sym(quantity);
                }
                for argument in args {
                    if !first {
                        self.sym(",");
                        self.ws(" ");
                    }
                    first = false;
                    self.term(argument, false, depth);
                }
                self.sym(">");
            }
            BTerm::Pair(left, right) => {
                // A lambda component is parenthesized: `(x => a, y => b)`
                // would read the comma into the first body.
                self.sym("(");
                self.term(left, matches!(**left, BTerm::Lam(..)), depth);
                self.sym(",");
                self.ws(" ");
                self.term(right, matches!(**right, BTerm::Lam(..)), depth);
                self.sym(")");
            }
            BTerm::Constructor(name, fields) => {
                self.name(name);
                self.sym("{");
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        self.sym(",");
                        self.ws(" ");
                    }
                    self.term(field, false, depth);
                }
                self.sym("}");
            }
            BTerm::Equal(left, right, ty) => {
                self.sym("{");
                self.term(left, false, depth);
                self.ws(" ");
                self.sym("==");
                self.ws(" ");
                self.term(right, false, depth);
                self.ws(" ");
                self.sym(":");
                self.ws(" ");
                self.term(ty, false, depth);
                self.sym("}");
            }
            BTerm::Refl => self.sym("{==}"),
            BTerm::Nat(decimal) => {
                self.piece(&format!("{decimal}n"), "numeral", Origin::Numeral);
            }
            BTerm::Succ(inner) => {
                if atomic {
                    self.sym("(");
                }
                self.piece("1n", "numeral", Origin::Numeral);
                self.sym("+");
                self.term(inner, true, depth);
                if atomic {
                    self.sym(")");
                }
            }
            BTerm::Kind(kind) => self.kw(kind),
            BTerm::Ann(value, ty) => {
                self.sym("{");
                self.term(value, false, depth);
                self.ws(" ");
                self.sym(":");
                self.ws(" ");
                self.term(ty, false, depth);
                self.sym("}");
            }
            BTerm::Hole => self.sym("_"),
            BTerm::Str(text) => {
                self.piece(text, "string", Origin::Synthetic(SYNTAX_ORIGIN.to_owned()))
            }
            BTerm::U32(value) => self.piece(
                &value.to_string(),
                "literal",
                Origin::Synthetic(SYNTAX_ORIGIN.to_owned()),
            ),
            BTerm::Template(inner) => {
                self.sym("~");
                self.term(inner, true, depth);
            }
            BTerm::Apply(function, args) => {
                let bare = matches!(
                    function.as_ref(),
                    BTerm::Name(_) | BTerm::Call(..) | BTerm::Apply(..)
                );
                self.term(function, !bare, depth);
                self.sym("(");
                for (index, argument) in args.iter().enumerate() {
                    if index > 0 {
                        self.sym(",");
                        self.ws(" ");
                    }
                    self.term(argument, matches!(argument, BTerm::Lam(..)), depth);
                }
                self.sym(")");
            }
            BTerm::Block(body) => {
                self.sym("(");
                self.ws("\n");
                self.body(body, depth + 1);
                self.pad(depth);
                self.sym(")");
            }
        }
    }

    fn param(&mut self, param: &Param) {
        let saved = (self.source.clone(), self.role);
        self.source = param.source.clone();
        self.role = MapRole::Binder;
        self.quantity(param.quantity);
        self.name(&param.name);
        self.sym(":");
        self.ws(" ");
        self.term(&param.ty, false, 1);
        (self.source, self.role) = saved;
    }

    fn body(&mut self, body: &Body, depth: usize) {
        let saved = (self.source.clone(), self.role);
        self.role = MapRole::Proof;
        for stmt in &body.stmts {
            self.pad(depth);
            match stmt {
                Stmt::Rewrite {
                    proof,
                    motive,
                    source,
                } => {
                    self.source = source.clone();
                    self.sym("%");
                    self.term(proof, true, depth);
                    self.ws(" ");
                    self.sym(":");
                    self.ws(" ");
                    self.term(motive, false, depth);
                }
                Stmt::Let {
                    name,
                    value,
                    source,
                }
                | Stmt::Share {
                    name,
                    value,
                    source,
                } => {
                    self.source = source.clone();
                    if matches!(stmt, Stmt::Share { .. }) {
                        self.sym("+");
                    }
                    self.name(name);
                    self.ws(" ");
                    self.sym("=");
                    self.ws(" ");
                    self.term(value, false, depth);
                }
            }
            self.ws("\n");
        }
        match &body.tail {
            Tail::Term(term, source) => {
                self.source = source.clone();
                self.pad(depth);
                self.term(term, false, depth);
                self.ws("\n");
            }
            Tail::Match {
                scrutinee,
                cases,
                source,
            } => {
                self.source = source.clone();
                self.pad(depth);
                self.kw("match");
                self.ws(" ");
                self.name(scrutinee);
                self.sym(":");
                self.ws("\n");
                for (pattern, case_body) in cases {
                    self.source = source.clone();
                    self.pad(depth + 1);
                    self.kw("case");
                    self.ws(" ");
                    match pattern {
                        Pattern::Zero => self.piece("0n", "numeral", Origin::Numeral),
                        Pattern::Succ(name) => {
                            self.piece("1n", "numeral", Origin::Numeral);
                            self.sym("+");
                            self.name(name);
                        }
                        Pattern::Constructor(head, fields) => {
                            self.name(head);
                            self.sym("{");
                            for (index, field) in fields.iter().enumerate() {
                                if index > 0 {
                                    self.sym(",");
                                    self.ws(" ");
                                }
                                self.name(field);
                            }
                            self.sym("}");
                        }
                        Pattern::Pair(left, right) => {
                            self.sym("(");
                            self.name(left);
                            self.sym(",");
                            self.ws(" ");
                            self.name(right);
                            self.sym(")");
                        }
                    }
                    self.sym(":");
                    self.ws("\n");
                    self.body(case_body, depth + 2);
                }
            }
        }
        (self.source, self.role) = saved;
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Law {
                name,
                params,
                claim,
                claim_source,
                proof,
                source,
            } => {
                self.source = source.clone();
                self.role = MapRole::Declaration;
                self.kw("law");
                self.ws(" ");
                self.name(name);
                self.sym(":");
                self.ws("\n");
                for param in params {
                    self.source = source.clone();
                    self.role = MapRole::Declaration;
                    self.pad(1);
                    self.kw("for");
                    self.ws(" ");
                    self.param(param);
                    self.ws("\n");
                }
                self.source = claim_source.clone();
                self.role = MapRole::Term;
                self.pad(1);
                self.term(claim, false, 1);
                self.ws("\n\n");
                self.source = source.clone();
                self.role = MapRole::Declaration;
                self.kw("def");
                self.ws(" ");
                self.name(name);
                self.sym("(");
                for (index, param) in params.iter().enumerate() {
                    if index > 0 {
                        self.sym(",");
                        self.ws(" ");
                    }
                    let saved = (self.source.clone(), self.role);
                    self.source = param.source.clone();
                    self.role = MapRole::Binder;
                    self.name(&param.name);
                    (self.source, self.role) = saved;
                }
                self.sym(")");
                self.sym(":");
                self.ws("\n");
                self.body(proof, 1);
            }
            Item::Type {
                name,
                parameters,
                index,
                kind,
                constructors,
                source,
            } => {
                self.source = source.clone();
                self.role = MapRole::Declaration;
                self.kw("type");
                self.ws(" ");
                self.name(name);
                if !parameters.is_empty() || index.is_some() {
                    self.sym("<");
                    for (position, parameter) in parameters.iter().enumerate() {
                        if position > 0 {
                            self.sym(",");
                            self.ws(" ");
                        }
                        self.sym("-");
                        self.name(parameter);
                        self.sym(":");
                        self.ws(" ");
                        self.kw("Data");
                    }
                    if let Some((index_name, index_type)) = index {
                        if !parameters.is_empty() {
                            self.sym(",");
                            self.ws(" ");
                        }
                        self.sym("-");
                        self.name(index_name);
                        self.sym(":");
                        self.ws(" ");
                        self.term(index_type, false, 1);
                    }
                    self.sym(">");
                }
                self.ws(" ");
                self.kw("is");
                self.ws(" ");
                self.kw(kind);
                self.sym(":");
                self.ws("\n");
                for (constructor, fields) in constructors {
                    self.pad(1);
                    self.name(constructor);
                    self.sym("{");
                    for (index, (field, ty)) in fields.iter().enumerate() {
                        if index > 0 {
                            self.sym(",");
                            self.ws(" ");
                        }
                        self.name(field);
                        self.sym(":");
                        self.ws(" ");
                        self.term(ty, false, 1);
                    }
                    self.sym("}");
                    self.ws("\n");
                }
            }
            Item::Def {
                name,
                params,
                result,
                result_source,
                body,
                source,
            } => {
                self.source = source.clone();
                self.role = MapRole::Declaration;
                self.kw("def");
                self.ws(" ");
                self.name(name);
                self.sym("(");
                for (index, param) in params.iter().enumerate() {
                    if index > 0 {
                        self.sym(",");
                        self.ws(" ");
                    }
                    self.param(param);
                }
                self.sym(")");
                self.ws(" ");
                self.sym("->");
                self.ws(" ");
                self.source = result_source.clone();
                self.role = MapRole::Term;
                self.term(result, false, 1);
                self.source = source.clone();
                self.role = MapRole::Declaration;
                self.sym(":");
                self.ws("\n");
                self.body(body, 1);
            }
        }
    }
}

/// The text of each item, printed alone, in order: the semantic lowering
/// traces whole declarations rather than tokens, so it needs the bytes each
/// item contributes.
#[must_use]
pub fn print_items(items: &[Item]) -> Vec<String> {
    items
        .iter()
        .map(|item| {
            let mut emitter = Emitter::new();
            let node = emitter.node("declaration");
            let mut printer = Printer {
                emitter: &mut emitter,
                source: EmitSource::Synthetic(PREAMBLE_ORIGIN.to_owned()),
                role: MapRole::Synthetic,
                node,
            };
            printer.item(item);
            emitter.text().to_owned()
        })
        .collect()
}

/// Print a whole module through a tracing emitter.
pub fn print_module(module: &Module, emitter: &mut Emitter) {
    let node = emitter.node("bend-preamble");
    let mut printer = Printer {
        emitter,
        source: EmitSource::Synthetic(PREAMBLE_ORIGIN.to_owned()),
        role: MapRole::Synthetic,
        node,
    };
    printer.kw("import");
    printer.ws(" ");
    printer.piece(
        "Base",
        "identifier",
        Origin::Synthetic(PREAMBLE_ORIGIN.to_owned()),
    );
    printer.ws("\n");
    for import in &module.imports {
        printer.kw("import");
        printer.ws(" ");
        printer.piece(
            &import.path,
            "identifier",
            Origin::Synthetic(PREAMBLE_ORIGIN.to_owned()),
        );
        printer.ws(" ");
        printer.kw("as");
        printer.ws(" ");
        printer.piece(
            &import.alias,
            "identifier",
            Origin::Synthetic(PREAMBLE_ORIGIN.to_owned()),
        );
        printer.ws("\n");
    }
    for item in &module.items {
        printer.ws("\n");
        printer.node = printer.emitter.node("declaration");
        printer.item(item);
    }
}
