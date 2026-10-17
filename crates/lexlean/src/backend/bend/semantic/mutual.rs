//! Mutual recursion without mutual recursion.
//!
//! Bend admits a call only to a definition above it, so a mutual group has
//! no direct lowering. A group is lowered instead by inlining: a member that
//! never calls itself is substituted into its callers until every remaining
//! member calls, besides itself, only members already lowered. The inlined
//! members are then defined after the others as ordinary functions, so each
//! one keeps its name, its signature, and its definitional equations.
//!
//! Inlining keeps recursion structural: a call `g(x)` replaced by `g`'s body
//! matches on `x`, a pattern variable of the caller, and the calls that body
//! makes are on fields of `x`, which Bend reads as deeper subterms of the
//! caller's own decreasing parameter. A group in which several members call
//! themselves and each other (an expression, its statements, and a statement
//! list, say) needs simultaneous recursion, which Bend cannot state; it is
//! refused.

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::engine::fail;
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{SemanticDeclaration, SemanticTerm, SemanticType};

use super::normal;

/// How one mutual group is lowered.
pub struct Plan {
    /// Every member in emission order: the self-recursive members first,
    /// each after the members it calls, then the inlined members, each after
    /// the members it calls.
    pub order: Vec<String>,
    /// The body each member is lowered with: its own, with every inlined
    /// member substituted.
    pub bodies: BTreeMap<String, SemanticTerm>,
}

struct Member<'a> {
    type_parameters: &'a [String],
    parameters: Vec<String>,
    body: &'a SemanticTerm,
}

/// The group members a term calls, by name.
fn callees(
    term: &SemanticTerm,
    group: &BTreeSet<String>,
    module: &str,
    out: &mut BTreeSet<String>,
) {
    if let SemanticTerm::Call { function, .. } | SemanticTerm::FunctionRef { function, .. } = term {
        let local = function.module.as_deref().is_none_or(|home| home == module);
        if local && group.contains(&function.name) {
            out.insert(function.name.clone());
        }
    }
    normal::for_each_child(term, &mut |child| callees(child, group, module, out));
}

/// Whether the members of `within` call one another in a cycle (a call of
/// a member to itself excepted when `allow_self` holds).
fn first_cycle(
    within: &BTreeSet<String>,
    calls: &BTreeMap<String, BTreeSet<String>>,
    allow_self: bool,
) -> Option<Vec<String>> {
    fn visit(
        node: &str,
        within: &BTreeSet<String>,
        calls: &BTreeMap<String, BTreeSet<String>>,
        allow_self: bool,
        path: &mut Vec<String>,
        done: &mut BTreeSet<String>,
    ) -> Option<Vec<String>> {
        if let Some(start) = path.iter().position(|seen| seen == node) {
            return Some(path[start..].to_vec());
        }
        if done.contains(node) {
            return None;
        }
        path.push(node.to_owned());
        for next in calls.get(node).into_iter().flatten() {
            if !within.contains(next) || (allow_self && next == node) {
                continue;
            }
            if let Some(cycle) = visit(next, within, calls, allow_self, path, done) {
                return Some(cycle);
            }
        }
        path.pop();
        done.insert(node.to_owned());
        None
    }
    let mut done = BTreeSet::new();
    for node in within {
        if let Some(cycle) = visit(node, within, calls, allow_self, &mut Vec::new(), &mut done) {
            return Some(cycle);
        }
    }
    None
}

/// `within` ordered so every member follows the members of `within` it
/// calls; the caller has established that they call one another acyclically.
fn callees_first(
    names: &[String],
    within: &BTreeSet<String>,
    calls: &BTreeMap<String, BTreeSet<String>>,
) -> Vec<String> {
    let mut placed = Vec::new();
    let mut seen = BTreeSet::new();
    fn place(
        node: &str,
        within: &BTreeSet<String>,
        calls: &BTreeMap<String, BTreeSet<String>>,
        seen: &mut BTreeSet<String>,
        placed: &mut Vec<String>,
    ) {
        if !seen.insert(node.to_owned()) {
            return;
        }
        for next in calls.get(node).into_iter().flatten() {
            if within.contains(next) && next != node {
                place(next, within, calls, seen, placed);
            }
        }
        placed.push(node.to_owned());
    }
    for name in names {
        if within.contains(name) {
            place(name, within, calls, &mut seen, &mut placed);
        }
    }
    placed
}

/// Substitute every call of an inlined member in `term`. The inlined
/// members call one another acyclically, so this terminates.
fn expand(
    term: &SemanticTerm,
    inlined: &BTreeMap<String, Member<'_>>,
    module: &str,
) -> SemanticTerm {
    if let SemanticTerm::Call {
        function,
        type_arguments,
        arguments,
    } = term
    {
        let local = function.module.as_deref().is_none_or(|home| home == module);
        if let Some(member) = inlined.get(&function.name).filter(|_| local) {
            let mut body = member.body.clone();
            let types: BTreeMap<String, SemanticType> = member
                .type_parameters
                .iter()
                .cloned()
                .zip(type_arguments.iter().cloned())
                .collect();
            normal::map_term_types(&mut body, &mut |ty| {
                *ty = super::substitute_type(ty, &types);
            });
            let values: BTreeMap<String, SemanticTerm> = member
                .parameters
                .iter()
                .cloned()
                .zip(
                    arguments
                        .iter()
                        .map(|argument| expand(argument, inlined, module)),
                )
                .collect();
            return expand(&normal::substitute_all(&body, &values), inlined, module);
        }
    }
    let mut out = term.clone();
    normal::map_children(&mut out, &mut |child| {
        *child = expand(child, inlined, module)
    });
    out
}

/// Plan the lowering of the mutual group `members` (in source order) of
/// `module`.
///
/// # Errors
///
/// `LLB6008` when the group needs simultaneous recursion, or passes one of
/// its members as a value.
pub fn plan(members: &[&SemanticDeclaration], module: &str, key: &str) -> Result<Plan, Diagnostic> {
    let mut by_name = BTreeMap::new();
    let mut names = Vec::new();
    for declaration in members {
        let SemanticDeclaration::Definition {
            name,
            type_parameters,
            parameters,
            body,
            ..
        } = declaration
        else {
            return Err(fail(format!(
                "the mutual group `{key}` holds a non-definition"
            )));
        };
        names.push(name.clone());
        by_name.insert(
            name.clone(),
            Member {
                type_parameters,
                parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                body,
            },
        );
    }
    let group: BTreeSet<String> = names.iter().cloned().collect();
    let mut calls = BTreeMap::new();
    for (name, member) in &by_name {
        let mut out = BTreeSet::new();
        callees(member.body, &group, module, &mut out);
        calls.insert(name.clone(), out);
    }
    if by_name
        .values()
        .any(|member| refers_as_value(member.body, &group, module))
    {
        return Err(fail(format!(
            "the mutual group `{key}` passes one of its members as a value, which inlining cannot lower"
        )));
    }
    // The members kept as definitions: every member that calls itself, and,
    // while the others still call one another in a cycle, the first member
    // of that cycle in source order.
    let mut kept: BTreeSet<String> = names
        .iter()
        .filter(|name| calls[*name].contains(*name))
        .cloned()
        .collect();
    loop {
        let rest: BTreeSet<String> = group.difference(&kept).cloned().collect();
        let Some(cycle) = first_cycle(&rest, &calls, false) else {
            break;
        };
        let first = names
            .iter()
            .find(|name| cycle.contains(name))
            .cloned()
            .ok_or_else(|| fail("a call cycle names no member"))?;
        kept.insert(first);
    }
    let inlined: BTreeMap<String, Member<'_>> = by_name
        .into_iter()
        .filter(|(name, _)| !kept.contains(name))
        .collect();
    let mut bodies = BTreeMap::new();
    let mut kept_calls = BTreeMap::new();
    for name in &names {
        let body = if kept.contains(name) {
            let declaration = members
                .iter()
                .find(|d| d.name() == name)
                .ok_or_else(|| fail("a member vanished"))?;
            let SemanticDeclaration::Definition { body, .. } = declaration else {
                return Err(fail("a member is not a definition"));
            };
            let expanded = expand(body, &inlined, module);
            let mut out = BTreeSet::new();
            callees(&expanded, &group, module, &mut out);
            kept_calls.insert(name.clone(), out);
            expanded
        } else {
            inlined[name].body.clone()
        };
        bodies.insert(name.clone(), body);
    }
    if let Some(cycle) = first_cycle(&kept, &kept_calls, true) {
        return Err(fail(format!(
            "the mutual group `{key}` recurses simultaneously through `{}`; Bend admits only self-recursion, so language 2.2 lowers no such group",
            cycle.join("`, `")
        )));
    }
    let inlined_names: BTreeSet<String> = inlined.keys().cloned().collect();
    let mut order = callees_first(&names, &kept, &kept_calls);
    order.extend(callees_first(&names, &inlined_names, &calls));
    Ok(Plan { order, bodies })
}

/// Whether `term` names a group member other than as the head of a call.
fn refers_as_value(term: &SemanticTerm, group: &BTreeSet<String>, module: &str) -> bool {
    if let SemanticTerm::FunctionRef { function, .. } = term {
        let local = function.module.as_deref().is_none_or(|home| home == module);
        if local && group.contains(&function.name) {
            return true;
        }
    }
    let mut found = false;
    normal::for_each_child(term, &mut |child| {
        found |= refers_as_value(child, group, module)
    });
    found
}
