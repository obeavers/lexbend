//! Definitional unfolding of semantic terms.
//!
//! The Bend checker compares types up to unfolding, so a rewrite motive
//! need only be definitionally equal to the goal. The proof lowering must
//! still *see* the subterm a rule rewrites, which may appear only after
//! unfolding; this module computes such unfoldings. It is never trusted: a
//! wrong unfolding yields a motive Bend rejects, never a wrong proof.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::semantic::{
    MemberRef, SemanticBranch, SemanticDeclaration, SemanticTerm, SemanticType,
    BUILTIN_CONSTRUCTOR_OWNERS,
};

/// Replace the free occurrences of `name` in `term` by `value`.
#[must_use]
pub fn substitute(term: &SemanticTerm, name: &str, value: &SemanticTerm) -> SemanticTerm {
    let mut map = BTreeMap::new();
    map.insert(name.to_owned(), value.clone());
    substitute_all(term, &map)
}

/// Replace the free occurrences of every key of `map` in `term`.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn substitute_all(term: &SemanticTerm, map: &BTreeMap<String, SemanticTerm>) -> SemanticTerm {
    if map.is_empty() {
        return term.clone();
    }
    let go = |t: &SemanticTerm| Box::new(substitute_all(t, map));
    let without = |names: &[&str]| {
        let mut inner = map.clone();
        for name in names {
            inner.remove(*name);
        }
        inner
    };
    match term {
        SemanticTerm::Var { name } => map.get(name).cloned().unwrap_or_else(|| term.clone()),
        SemanticTerm::Primitive {
            operation,
            arguments,
            result,
        } => SemanticTerm::Primitive {
            operation: *operation,
            arguments: arguments.iter().map(|a| substitute_all(a, map)).collect(),
            result: result.clone(),
        },
        SemanticTerm::Cons { head, tail } => SemanticTerm::Cons {
            head: go(head),
            tail: go(tail),
        },
        SemanticTerm::Record {
            r#type,
            type_arguments,
            fields,
        } => SemanticTerm::Record {
            r#type: r#type.clone(),
            type_arguments: type_arguments.clone(),
            fields: fields
                .iter()
                .map(|field| crate::ir::semantic::SemanticAssignment {
                    field: field.field.clone(),
                    value: substitute_all(&field.value, map),
                })
                .collect(),
        },
        SemanticTerm::Constructor {
            constructor,
            type_arguments,
            arguments,
        } => SemanticTerm::Constructor {
            constructor: constructor.clone(),
            type_arguments: type_arguments.clone(),
            arguments: arguments.iter().map(|a| substitute_all(a, map)).collect(),
        },
        SemanticTerm::Project { value, field } => SemanticTerm::Project {
            value: go(value),
            field: field.clone(),
        },
        SemanticTerm::Call {
            function,
            type_arguments,
            arguments,
        } => SemanticTerm::Call {
            function: function.clone(),
            type_arguments: type_arguments.clone(),
            arguments: arguments.iter().map(|a| substitute_all(a, map)).collect(),
        },
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => SemanticTerm::If {
            condition: go(condition),
            then_value: go(then_value),
            else_value: go(else_value),
        },
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => SemanticTerm::Match {
            scrutinee: go(scrutinee),
            branches: branches
                .iter()
                .map(|branch| {
                    let bound: Vec<&str> = branch.binders.iter().map(String::as_str).collect();
                    SemanticBranch {
                        constructor: branch.constructor.clone(),
                        binders: branch.binders.clone(),
                        body: substitute_all(&branch.body, &without(&bound)),
                    }
                })
                .collect(),
        },
        SemanticTerm::Eq { left, right } => SemanticTerm::Eq {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Le { left, right } => SemanticTerm::Le {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Lt { left, right } => SemanticTerm::Lt {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Add { left, right } => SemanticTerm::Add {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Beq { left, right } => SemanticTerm::Beq {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Ble { left, right } => SemanticTerm::Ble {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Blt { left, right } => SemanticTerm::Blt {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::And { left, right } => SemanticTerm::And {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::PropAnd { left, right } => SemanticTerm::PropAnd {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Or { left, right } => SemanticTerm::Or {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Not { value } => SemanticTerm::Not { value: go(value) },
        SemanticTerm::Implies {
            premise,
            conclusion,
        } => SemanticTerm::Implies {
            premise: go(premise),
            conclusion: go(conclusion),
        },
        SemanticTerm::Iff { left, right } => SemanticTerm::Iff {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::Forall { binder, body } => SemanticTerm::Forall {
            binder: binder.clone(),
            body: Box::new(substitute_all(body, &without(&[binder.name.as_str()]))),
        },
        SemanticTerm::Let {
            binder,
            value,
            body,
        } => SemanticTerm::Let {
            binder: binder.clone(),
            value: go(value),
            body: Box::new(substitute_all(body, &without(&[binder.name.as_str()]))),
        },
        SemanticTerm::Pair { left, right } => SemanticTerm::Pair {
            left: go(left),
            right: go(right),
        },
        SemanticTerm::First { value } => SemanticTerm::First { value: go(value) },
        SemanticTerm::Second { value } => SemanticTerm::Second { value: go(value) },
        SemanticTerm::Lambda {
            parameters,
            captures,
            body,
        } => {
            let bound: Vec<&str> = parameters.iter().map(|p| p.name.as_str()).collect();
            SemanticTerm::Lambda {
                parameters: parameters.clone(),
                captures: captures.clone(),
                body: Box::new(substitute_all(body, &without(&bound))),
            }
        }
        SemanticTerm::Apply {
            function,
            arguments,
        } => SemanticTerm::Apply {
            function: go(function),
            arguments: arguments.iter().map(|a| substitute_all(a, map)).collect(),
        },
        SemanticTerm::MapLiteral {
            key,
            value,
            entries,
        } => SemanticTerm::MapLiteral {
            key: key.clone(),
            value: value.clone(),
            entries: entries
                .iter()
                .map(|entry| crate::ir::semantic::SemanticMapEntry {
                    key: substitute_all(&entry.key, map),
                    value: substitute_all(&entry.value, map),
                })
                .collect(),
        },
        SemanticTerm::SetLiteral { element, elements } => SemanticTerm::SetLiteral {
            element: element.clone(),
            elements: elements.iter().map(|e| substitute_all(e, map)).collect(),
        },
        other => other.clone(),
    }
}

/// Collect the free variables of `term` not in `bound`.
pub fn free_vars(term: &SemanticTerm, bound: &mut BTreeSet<String>, out: &mut BTreeSet<String>) {
    let mut visit = |t: &SemanticTerm, bound: &mut BTreeSet<String>| free_vars(t, bound, out);
    match term {
        SemanticTerm::Var { name } => {
            if !bound.contains(name) {
                visit_name(name, out);
            }
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            visit(scrutinee, bound);
            for branch in branches {
                let mut inner = bound.clone();
                inner.extend(branch.binders.iter().cloned());
                free_vars(&branch.body, &mut inner, out);
            }
        }
        SemanticTerm::Forall { binder, body } => {
            let mut inner = bound.clone();
            inner.insert(binder.name.clone());
            free_vars(body, &mut inner, out);
        }
        SemanticTerm::Let {
            binder,
            value,
            body,
        } => {
            visit(value, bound);
            let mut inner = bound.clone();
            inner.insert(binder.name.clone());
            free_vars(body, &mut inner, out);
        }
        SemanticTerm::Lambda {
            parameters, body, ..
        } => {
            let mut inner = bound.clone();
            inner.extend(parameters.iter().map(|p| p.name.clone()));
            free_vars(body, &mut inner, out);
        }
        other => {
            for child in children(other) {
                visit(child, bound);
            }
        }
    }
}

fn visit_name(name: &str, out: &mut BTreeSet<String>) {
    out.insert(name.to_owned());
}

/// The immediate subterms of a term that bind nothing.
#[must_use]
pub fn children(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    match term {
        SemanticTerm::Primitive { arguments, .. }
        | SemanticTerm::Constructor { arguments, .. }
        | SemanticTerm::Call { arguments, .. } => arguments.iter().collect(),
        SemanticTerm::Cons { head, tail } => vec![head, tail],
        SemanticTerm::Record { fields, .. } => fields.iter().map(|f| &f.value).collect(),
        SemanticTerm::Project { value, .. }
        | SemanticTerm::Not { value }
        | SemanticTerm::First { value }
        | SemanticTerm::Second { value } => vec![value],
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => vec![condition, then_value, else_value],
        SemanticTerm::Match { scrutinee, .. } => vec![scrutinee],
        SemanticTerm::Eq { left, right }
        | SemanticTerm::Le { left, right }
        | SemanticTerm::Lt { left, right }
        | SemanticTerm::Add { left, right }
        | SemanticTerm::Beq { left, right }
        | SemanticTerm::Ble { left, right }
        | SemanticTerm::Blt { left, right }
        | SemanticTerm::And { left, right }
        | SemanticTerm::PropAnd { left, right }
        | SemanticTerm::Or { left, right }
        | SemanticTerm::Iff { left, right }
        | SemanticTerm::Pair { left, right } => vec![left, right],
        SemanticTerm::Implies {
            premise,
            conclusion,
        } => vec![premise, conclusion],
        SemanticTerm::Apply {
            function,
            arguments,
        } => std::iter::once(function.as_ref())
            .chain(arguments)
            .collect(),
        SemanticTerm::MapLiteral { entries, .. } => entries
            .iter()
            .flat_map(|entry| [&entry.key, &entry.value])
            .collect(),
        SemanticTerm::SetLiteral { elements, .. } => elements.iter().collect(),
        _ => Vec::new(),
    }
}

/// Every subterm outside binders, with its path, in pre-order.
pub fn subterms(
    term: &SemanticTerm,
    path: &mut Vec<usize>,
    out: &mut Vec<(Vec<usize>, SemanticTerm)>,
) {
    out.push((path.clone(), term.clone()));
    if matches!(
        term,
        SemanticTerm::Forall { .. }
            | SemanticTerm::Lambda { .. }
            | SemanticTerm::Let { .. }
            | SemanticTerm::Match { .. }
    ) {
        return;
    }
    for (index, child) in children(term).into_iter().enumerate() {
        path.push(index);
        subterms(child, path, out);
        path.pop();
    }
}

/// `term` with the subterm at `path` replaced.
pub fn replace_at(term: &SemanticTerm, path: &[usize], with: &SemanticTerm) -> SemanticTerm {
    let Some((first, rest)) = path.split_first() else {
        return with.clone();
    };
    let mut out = term.clone();
    let mut index = 0;
    map_children(&mut out, &mut |child| {
        if index == *first {
            *child = replace_at(child, rest, with);
        }
        index += 1;
    });
    out
}

/// Qualify every module-relative member reference of a term read from
/// `home`, so it means the same inside another module.
#[must_use]
pub fn qualify_term(term: &SemanticTerm, home: &str) -> SemanticTerm {
    fn member(member: &MemberRef, home: &str) -> MemberRef {
        let builtin = member
            .name
            .split_once('.')
            .is_some_and(|(owner, _)| BUILTIN_CONSTRUCTOR_OWNERS.contains(&owner));
        if member.module.is_none() && !builtin {
            MemberRef {
                module: Some(home.to_owned()),
                name: member.name.clone(),
            }
        } else {
            member.clone()
        }
    }
    let ty = |t: &crate::ir::semantic::SemanticType| super::qualify(t, home);
    let go = |t: &SemanticTerm| qualify_term(t, home);
    let rebuilt = match term {
        SemanticTerm::Call {
            function,
            type_arguments,
            arguments,
        } => SemanticTerm::Call {
            function: member(function, home),
            type_arguments: type_arguments.iter().map(ty).collect(),
            arguments: arguments.iter().map(go).collect(),
        },
        SemanticTerm::FunctionRef {
            function,
            type_arguments,
        } => SemanticTerm::FunctionRef {
            function: member(function, home),
            type_arguments: type_arguments.iter().map(ty).collect(),
        },
        SemanticTerm::Constructor {
            constructor,
            type_arguments,
            arguments,
        } => SemanticTerm::Constructor {
            constructor: member(constructor, home),
            type_arguments: type_arguments.iter().map(ty).collect(),
            arguments: arguments.iter().map(go).collect(),
        },
        SemanticTerm::Record {
            r#type,
            type_arguments,
            fields,
        } => SemanticTerm::Record {
            r#type: member(r#type, home),
            type_arguments: type_arguments.iter().map(ty).collect(),
            fields: fields
                .iter()
                .map(|field| crate::ir::semantic::SemanticAssignment {
                    field: field.field.clone(),
                    value: go(&field.value),
                })
                .collect(),
        },
        SemanticTerm::InstanceValue {
            class,
            arguments,
            resolved,
        } => SemanticTerm::InstanceValue {
            class: member(class, home),
            arguments: arguments.iter().map(ty).collect(),
            resolved: member(resolved, home),
        },
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => SemanticTerm::Match {
            scrutinee: Box::new(go(scrutinee)),
            branches: branches
                .iter()
                .map(|branch| SemanticBranch {
                    constructor: member(&branch.constructor, home),
                    binders: branch.binders.clone(),
                    body: go(&branch.body),
                })
                .collect(),
        },
        SemanticTerm::Nil { element } => SemanticTerm::Nil {
            element: ty(element),
        },
        _ => {
            // Every other form carries no member reference of its own.
            let mut out = term.clone();
            map_children(&mut out, &mut |child| *child = go(child));
            return out;
        }
    };
    rebuilt
}

/// Apply `f` to every immediate subterm, binding forms included.
pub fn map_children(term: &mut SemanticTerm, f: &mut impl FnMut(&mut SemanticTerm)) {
    match term {
        SemanticTerm::Primitive { arguments, .. }
        | SemanticTerm::Constructor { arguments, .. }
        | SemanticTerm::Call { arguments, .. } => arguments.iter_mut().for_each(f),
        SemanticTerm::Cons { head, tail } => {
            f(head);
            f(tail);
        }
        SemanticTerm::Record { fields, .. } => fields.iter_mut().for_each(|x| f(&mut x.value)),
        SemanticTerm::Project { value, .. }
        | SemanticTerm::Not { value }
        | SemanticTerm::First { value }
        | SemanticTerm::Second { value } => f(value),
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => {
            f(condition);
            f(then_value);
            f(else_value);
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            f(scrutinee);
            for branch in branches {
                f(&mut branch.body);
            }
        }
        SemanticTerm::Eq { left, right }
        | SemanticTerm::Le { left, right }
        | SemanticTerm::Lt { left, right }
        | SemanticTerm::Add { left, right }
        | SemanticTerm::Beq { left, right }
        | SemanticTerm::Ble { left, right }
        | SemanticTerm::Blt { left, right }
        | SemanticTerm::And { left, right }
        | SemanticTerm::PropAnd { left, right }
        | SemanticTerm::Or { left, right }
        | SemanticTerm::Iff { left, right }
        | SemanticTerm::Pair { left, right } => {
            f(left);
            f(right);
        }
        SemanticTerm::Implies {
            premise,
            conclusion,
        } => {
            f(premise);
            f(conclusion);
        }
        SemanticTerm::Forall { body, .. } | SemanticTerm::Lambda { body, .. } => f(body),
        SemanticTerm::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        SemanticTerm::Apply {
            function,
            arguments,
        } => {
            f(function);
            arguments.iter_mut().for_each(f);
        }
        SemanticTerm::MapLiteral { entries, .. } => {
            for entry in entries {
                f(&mut entry.key);
                f(&mut entry.value);
            }
        }
        SemanticTerm::SetLiteral { elements, .. } => elements.iter_mut().for_each(f),
        _ => {}
    }
}

fn nat(term: &SemanticTerm) -> Option<u128> {
    match term {
        SemanticTerm::Nat { value } => value.parse().ok(),
        SemanticTerm::Constructor {
            constructor,
            arguments,
            ..
        } if constructor.module.is_none()
            && constructor.name == "Nat.zero"
            && arguments.is_empty() =>
        {
            Some(0)
        }
        _ => None,
    }
}

fn nat_term(value: u128) -> SemanticTerm {
    SemanticTerm::Nat {
        value: value.to_string(),
    }
}

fn boolean(term: &SemanticTerm) -> Option<bool> {
    match term {
        SemanticTerm::Bool { value } => Some(*value),
        _ => None,
    }
}

/// Whether a term is headed by a constructor, so a match on it reduces.
#[must_use]
pub fn constructor_headed(term: &SemanticTerm) -> bool {
    matches!(
        term,
        SemanticTerm::Nat { .. }
            | SemanticTerm::Bool { .. }
            | SemanticTerm::Unit
            | SemanticTerm::Nil { .. }
            | SemanticTerm::Cons { .. }
            | SemanticTerm::Record { .. }
            | SemanticTerm::Constructor { .. }
            | SemanticTerm::Pair { .. }
            | SemanticTerm::String { .. }
    )
}

/// The constructor a constructor-headed term is built by, by its last name
/// segment, and its fields.
fn head_of(term: &SemanticTerm) -> Option<(String, Vec<SemanticTerm>)> {
    Some(match term {
        SemanticTerm::Nat { .. } => match nat(term)? {
            0 => ("zero".to_owned(), Vec::new()),
            n => ("succ".to_owned(), vec![nat_term(n - 1)]),
        },
        SemanticTerm::Bool { value } => (
            (if *value { "true" } else { "false" }).to_owned(),
            Vec::new(),
        ),
        SemanticTerm::Nil { .. } => ("nil".to_owned(), Vec::new()),
        SemanticTerm::Cons { head, tail } => {
            ("cons".to_owned(), vec![(**head).clone(), (**tail).clone()])
        }
        SemanticTerm::Pair { left, right } => {
            ("mk".to_owned(), vec![(**left).clone(), (**right).clone()])
        }
        SemanticTerm::Record { fields, .. } => (
            "mk".to_owned(),
            fields.iter().map(|f| f.value.clone()).collect(),
        ),
        SemanticTerm::Constructor {
            constructor,
            arguments,
            ..
        } => (
            constructor
                .name
                .rsplit('.')
                .next()
                .unwrap_or(&constructor.name)
                .to_owned(),
            arguments.clone(),
        ),
        _ => return None,
    })
}

/// Whether `term` holds a `match` anywhere.
fn contains_match(term: &SemanticTerm) -> bool {
    if matches!(term, SemanticTerm::Match { .. }) {
        return true;
    }
    let mut found = false;
    for_each_child(term, &mut |child| found |= contains_match(child));
    found
}

/// Unfolds semantic terms against the declarations of a project.
pub struct Normalizer<'l, 'p, 'a> {
    lower: &'l super::Lower<'p, 'a>,
    fuel: usize,
}

impl<'l, 'p, 'a> Normalizer<'l, 'p, 'a> {
    /// A normalizer over `lower`'s project, bounded so a diverging unfolding
    /// stops instead of looping.
    #[must_use]
    pub fn new(lower: &'l super::Lower<'p, 'a>) -> Self {
        Self {
            lower,
            fuel: 20_000,
        }
    }

    /// The record declaration's field names, in order.
    fn record_field_names(&self, member: &MemberRef) -> Option<Vec<String>> {
        match self.lower.declaration(member).ok()? {
            SemanticDeclaration::Structure { fields, .. }
            | SemanticDeclaration::Class { fields, .. } => {
                Some(fields.iter().map(|f| f.name.clone()).collect())
            }
            _ => None,
        }
    }

    /// Unfold `term` as far as definitional reduction reaches.
    #[allow(clippy::too_many_lines)]
    pub fn normalize(&mut self, term: &SemanticTerm) -> SemanticTerm {
        if self.fuel == 0 {
            return term.clone();
        }
        self.fuel -= 1;
        match term {
            SemanticTerm::Let {
                value,
                body,
                binder,
            } => {
                let value = self.normalize(value);
                self.normalize(&substitute(body, &binder.name, &value))
            }
            SemanticTerm::Call {
                function,
                type_arguments,
                arguments,
            } => {
                let arguments: Vec<SemanticTerm> =
                    arguments.iter().map(|a| self.normalize(a)).collect();
                let stuck = SemanticTerm::Call {
                    function: function.clone(),
                    type_arguments: type_arguments.clone(),
                    arguments: arguments.clone(),
                };
                let Ok(SemanticDeclaration::Definition {
                    type_parameters,
                    parameters,
                    recursive_argument,
                    termination,
                    body,
                    ..
                }) = self.lower.declaration(function)
                else {
                    return stuck;
                };
                // A mutual member unfolds as any structural definition: its
                // Bend body is its own with its inlined members substituted,
                // which unfolds to the same terms.
                if termination.is_some() || parameters.len() != arguments.len() {
                    return stuck;
                }
                if let Some(argument) = recursive_argument {
                    let position = parameters.iter().position(|p| &p.name == argument);
                    if !position.is_some_and(|i| constructor_headed(&arguments[i])) {
                        return stuck;
                    }
                }
                let home = self.lower.home(function);
                let mut body = qualify_term(body, &home);
                let types: BTreeMap<String, SemanticType> = type_parameters
                    .iter()
                    .cloned()
                    .zip(type_arguments.iter().cloned())
                    .collect();
                map_term_types(&mut body, &mut |ty| {
                    *ty = super::substitute_type(ty, &types)
                });
                let map: BTreeMap<String, SemanticTerm> = parameters
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arguments)
                    .collect();
                let unfolded = self.normalize(&substitute_all(&body, &map));
                // A match left stuck would lower to a freshly lifted
                // function, which Bend does not identify with the one the
                // definition's own body lifts to; the call itself is what
                // Bend's evaluation leaves, so it is kept.
                if contains_match(&unfolded) {
                    return stuck;
                }
                unfolded
            }
            SemanticTerm::Apply {
                function,
                arguments,
            } => {
                let function = self.normalize(function);
                let arguments: Vec<SemanticTerm> =
                    arguments.iter().map(|a| self.normalize(a)).collect();
                match &function {
                    SemanticTerm::Lambda {
                        parameters, body, ..
                    } if parameters.len() == arguments.len() => {
                        let map: BTreeMap<String, SemanticTerm> = parameters
                            .iter()
                            .map(|p| p.name.clone())
                            .zip(arguments)
                            .collect();
                        self.normalize(&substitute_all(body, &map))
                    }
                    _ => SemanticTerm::Apply {
                        function: Box::new(function),
                        arguments,
                    },
                }
            }
            SemanticTerm::Match {
                scrutinee,
                branches,
            } => {
                let scrutinee = self.normalize(scrutinee);
                if let Some((head, fields)) = head_of(&scrutinee) {
                    if let Some(branch) = branches.iter().find(|branch| {
                        branch.constructor.name.rsplit('.').next() == Some(head.as_str())
                    }) {
                        let map: BTreeMap<String, SemanticTerm> =
                            branch.binders.iter().cloned().zip(fields).collect();
                        return self.normalize(&substitute_all(&branch.body, &map));
                    }
                }
                SemanticTerm::Match {
                    scrutinee: Box::new(scrutinee),
                    branches: branches.clone(),
                }
            }
            SemanticTerm::If {
                condition,
                then_value,
                else_value,
            } => {
                let condition = self.normalize(condition);
                match boolean(&condition) {
                    Some(true) => self.normalize(then_value),
                    Some(false) => self.normalize(else_value),
                    None => SemanticTerm::If {
                        condition: Box::new(condition),
                        then_value: Box::new(self.normalize(then_value)),
                        else_value: Box::new(self.normalize(else_value)),
                    },
                }
            }
            SemanticTerm::First { value } | SemanticTerm::Second { value } => {
                let value = self.normalize(value);
                if let SemanticTerm::Pair { left, right } = &value {
                    return if matches!(term, SemanticTerm::First { .. }) {
                        (**left).clone()
                    } else {
                        (**right).clone()
                    };
                }
                if matches!(term, SemanticTerm::First { .. }) {
                    SemanticTerm::First {
                        value: Box::new(value),
                    }
                } else {
                    SemanticTerm::Second {
                        value: Box::new(value),
                    }
                }
            }
            SemanticTerm::Project { value, field } => {
                let value = self.normalize(value);
                if let SemanticTerm::Record { fields, .. } = &value {
                    if let Some(found) = fields.iter().find(|f| &f.field == field) {
                        return found.value.clone();
                    }
                }
                if let SemanticTerm::Constructor {
                    constructor,
                    arguments,
                    ..
                } = &value
                {
                    if let Some((owner, "mk")) = constructor.name.rsplit_once('.') {
                        let owner = MemberRef {
                            module: constructor.module.clone(),
                            name: owner.to_owned(),
                        };
                        if let Some(names) = self.record_field_names(&owner) {
                            if let Some(index) = names.iter().position(|n| n == field) {
                                if let Some(found) = arguments.get(index) {
                                    return found.clone();
                                }
                            }
                        }
                    }
                }
                SemanticTerm::Project {
                    value: Box::new(value),
                    field: field.clone(),
                }
            }
            SemanticTerm::Add { left, right } => {
                let (left, right) = (self.normalize(left), self.normalize(right));
                match (nat(&left), nat(&right)) {
                    (Some(a), Some(b)) => nat_term(a + b),
                    (_, Some(0)) => left,
                    _ => SemanticTerm::Add {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            SemanticTerm::Beq { left, right }
            | SemanticTerm::Ble { left, right }
            | SemanticTerm::Blt { left, right } => {
                let (l, r) = (self.normalize(left), self.normalize(right));
                if let (Some(a), Some(b)) = (nat(&l), nat(&r)) {
                    let value = match term {
                        SemanticTerm::Beq { .. } => a == b,
                        SemanticTerm::Ble { .. } => a <= b,
                        _ => a < b,
                    };
                    return SemanticTerm::Bool { value };
                }
                let (left, right) = (Box::new(l), Box::new(r));
                match term {
                    SemanticTerm::Beq { .. } => SemanticTerm::Beq { left, right },
                    SemanticTerm::Ble { .. } => SemanticTerm::Ble { left, right },
                    _ => SemanticTerm::Blt { left, right },
                }
            }
            SemanticTerm::And { left, right } => {
                let left = self.normalize(left);
                match boolean(&left) {
                    Some(false) => left,
                    Some(true) => self.normalize(right),
                    None => SemanticTerm::And {
                        left: Box::new(left),
                        right: Box::new(self.normalize(right)),
                    },
                }
            }
            SemanticTerm::Or { left, right } => {
                let left = self.normalize(left);
                match boolean(&left) {
                    Some(true) => left,
                    Some(false) => self.normalize(right),
                    None => SemanticTerm::Or {
                        left: Box::new(left),
                        right: Box::new(self.normalize(right)),
                    },
                }
            }
            SemanticTerm::Not { value } => {
                let value = self.normalize(value);
                match boolean(&value) {
                    Some(b) => SemanticTerm::Bool { value: !b },
                    None => SemanticTerm::Not {
                        value: Box::new(value),
                    },
                }
            }
            SemanticTerm::Forall { .. } | SemanticTerm::Lambda { .. } => term.clone(),
            other => {
                let mut out = other.clone();
                map_children(&mut out, &mut |child| *child = self.normalize(child));
                out
            }
        }
    }

    /// Whether a closed proposition holds, when unfolding decides it.
    pub fn truth(&mut self, prop: &SemanticTerm) -> Option<bool> {
        let prop = self.normalize(prop);
        match &prop {
            SemanticTerm::Eq { left, right } => {
                if closed_value(left) && closed_value(right) {
                    Some(left == right)
                } else {
                    None
                }
            }
            SemanticTerm::Le { left, right } => Some(nat(left)? <= nat(right)?),
            SemanticTerm::Lt { left, right } => Some(nat(left)? < nat(right)?),
            SemanticTerm::PropAnd { left, right } => Some(self.truth(left)? && self.truth(right)?),
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => Some(!self.truth(premise)? || self.truth(conclusion)?),
            SemanticTerm::Iff { left, right } => Some(self.truth(left)? == self.truth(right)?),
            SemanticTerm::Call { .. } => None,
            _ => None,
        }
    }
}

/// Whether a term is a closed value built from constructors and literals,
/// so syntactic equality is equality.
#[must_use]
pub fn closed_value(term: &SemanticTerm) -> bool {
    constructor_headed(term) && children(term).into_iter().all(closed_value)
}

/// Apply `f` to every type `term` states, at every depth.
pub fn map_term_types(term: &mut SemanticTerm, f: &mut impl FnMut(&mut SemanticType)) {
    match term {
        SemanticTerm::Nil { element } | SemanticTerm::SetLiteral { element, .. } => f(element),
        SemanticTerm::Primitive { result, .. } => f(result),
        SemanticTerm::Record { type_arguments, .. }
        | SemanticTerm::Constructor { type_arguments, .. }
        | SemanticTerm::Call { type_arguments, .. }
        | SemanticTerm::FunctionRef { type_arguments, .. }
        | SemanticTerm::CheckedApply { type_arguments, .. } => {
            type_arguments.iter_mut().for_each(&mut *f);
        }
        SemanticTerm::InstanceValue { arguments, .. } => arguments.iter_mut().for_each(&mut *f),
        SemanticTerm::Forall { binder, .. } | SemanticTerm::Let { binder, .. } => {
            f(&mut binder.r#type);
        }
        SemanticTerm::Lambda { parameters, .. } => {
            for parameter in parameters {
                f(&mut parameter.r#type);
            }
        }
        SemanticTerm::MapLiteral { key, value, .. } => {
            f(key);
            f(value);
        }
        SemanticTerm::GraphLiteral { node, .. } => f(node),
        _ => {}
    }
    map_children(term, &mut |child| map_term_types(child, f));
}

/// Visit every immediate subterm, binding forms included (`children`
/// stops at binders).
pub fn for_each_child(term: &SemanticTerm, f: &mut impl FnMut(&SemanticTerm)) {
    let mut copy = term.clone();
    map_children(&mut copy, &mut |child| f(child));
}
