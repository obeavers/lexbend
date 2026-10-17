//! Simultaneous mutual groups as one definition (SPEC.md §18.11.3).
//!
//! A mutual group `mutual.rs` cannot inline, because two members call each
//! other on the same smaller value, has no Bend form as separate defs:
//! Bend has no forward reference. When every member recurses over one type
//! (its *carrier*), the group becomes one definition `go` over the carrier
//! and a *selector*, a generated datatype with one constructor per member
//! carrying that member's other arguments. `go` matches the carrier, then
//! the selector, and runs the selected member's body with its recursive
//! parameter known to be the matched constructor; a member call becomes a
//! call of `go` on a piece of the carrier, which Bend's termination check
//! and the kernel accept. Each member keeps its name and Lean's signature
//! as a def that calls `go`.
//!
//! The carrier is a plain type (`Nat`, a list, an inductive), or a nested
//! or mutual family (`family.rs`) when the members recurse over its
//! different index types; the selector is then indexed too, and a
//! selected member whose index the carrier's constructor contradicts is a
//! branch refuted from the two equations. The encoding is exploratory: it
//! is checked by the pinned Bend and its kernel, and its coverage of the
//! semantic surface is still being confirmed.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Name, Param, Pattern, Quantity, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{MemberRef, SemanticDeclaration, SemanticTerm, SemanticType};

use super::family::{list_local, Family, FamilyLocal, Goal, Shape};
use super::{bend_order, call, generated, here, names, normal, synthetic, var};
use super::{Lower, Scope};

/// The type a group's members recurse over.
#[derive(Clone)]
pub enum Carrier {
    /// A nested or mutual family at its type arguments.
    Family {
        family: Arc<Family>,
        arguments: Vec<SemanticType>,
    },
    /// Any other type, the same for every member.
    Plain(SemanticType),
}

impl Carrier {
    /// The family local a value of `ty` is over this carrier.
    fn list_local(&self, ty: &SemanticType) -> Option<FamilyLocal> {
        match self {
            Self::Family { family, arguments } => list_local(family, arguments, ty),
            Self::Plain(_) => None,
        }
    }
}

/// The mutual group being lowered as one definition.
#[derive(Clone)]
pub struct GroupContext {
    /// Whether every member returns the same type; otherwise `go`'s result
    /// is computed from the selector and each call is annotated with its
    /// member's.
    uniform: bool,
    carrier: Carrier,
    go: String,
    selector: String,
    members: BTreeMap<String, GroupMember>,
}

impl GroupContext {
    /// The recursive parameter's position of the member `name`.
    pub fn recursive_position(&self, name: &str) -> Option<usize> {
        self.members.get(name).map(|member| member.recursive)
    }
}

#[derive(Clone)]
struct GroupMember {
    /// The family index its recursive parameter has; 0 over a plain
    /// carrier.
    index: usize,
    /// The recursive parameter's position.
    recursive: usize,
    /// The other parameters' positions, in selector order.
    rest: Vec<usize>,
    /// Each parameter's type.
    types: Vec<SemanticType>,
    result: SemanticType,
}

/// One constructor of a carrier, as `go` matches it.
struct CarrierCase {
    /// The constructor's last name segment, as a branch names it.
    short: String,
    /// The family index it builds; 0 over a plain carrier.
    at: usize,
    fields: Vec<SemanticType>,
    /// The family local each field opens.
    locals: Vec<Option<FamilyLocal>>,
    /// The semantic constructor that rebuilds the matched value.
    constructor: MemberRef,
    type_arguments: Vec<SemanticType>,
    head: Head,
}

enum Head {
    Zero,
    Succ,
    Constructor(String),
}

impl Lower<'_, '_> {
    /// The family a mutual group recurses over, when its members'
    /// recursive parameters are of one.
    pub(super) fn group_family(
        &self,
        members: &[&SemanticDeclaration],
    ) -> Result<Option<Carrier>, Diagnostic> {
        let mut found: Option<(Arc<Family>, Vec<SemanticType>)> = None;
        let mut others = false;
        for declaration in members {
            let family = self.recursive_type(declaration).and_then(|ty| match &ty {
                SemanticType::Named { .. } => {
                    self.known(&ty).map(|known| (known.family, known.arguments))
                }
                SemanticType::List { element } => match element.as_ref() {
                    SemanticType::Named { member, arguments } => self
                        .family_of(member)
                        .filter(|(family, _)| family.list_index(arguments, element).is_some())
                        .map(|(family, _)| (family, arguments.clone())),
                    _ => None,
                },
                _ => None,
            });
            match (family, &found) {
                (Some(family), None) => found = Some(family),
                (Some(family), Some(existing)) => {
                    if !Arc::ptr_eq(&family.0, &existing.0) || family.1 != existing.1 {
                        return Err(fail("a mutual group recurses over two inductive families"));
                    }
                }
                (None, _) => others = true,
            }
        }
        if found.is_some() && others {
            return Err(fail(
                "a mutual group recurses over an inductive family and over another type",
            ));
        }
        Ok(found.map(|(family, arguments)| Carrier::Family { family, arguments }))
    }

    /// The plain carrier of a group every member of which recurses over the
    /// same `Nat`, list or inductive type.
    pub(super) fn plain_carrier(&self, members: &[&SemanticDeclaration]) -> Option<Carrier> {
        let mut types = members
            .iter()
            .map(|declaration| self.recursive_type(declaration));
        let first = types.next()??;
        if !types.all(|ty| ty.as_ref() == Some(&first)) {
            return None;
        }
        let carried = match &first {
            SemanticType::Nat | SemanticType::List { .. } => true,
            SemanticType::Named { member, .. } => matches!(
                self.declaration(member),
                Ok(SemanticDeclaration::Inductive { parameters, .. }) if parameters.is_empty()
            ),
            _ => false,
        };
        carried.then_some(Carrier::Plain(first))
    }

    fn recursive_type(&self, declaration: &SemanticDeclaration) -> Option<SemanticType> {
        let SemanticDeclaration::Definition {
            parameters,
            recursive_argument: Some(argument),
            termination: None,
            ..
        } = declaration
        else {
            return None;
        };
        parameters
            .iter()
            .find(|parameter| &parameter.name == argument)
            .map(|parameter| self.canonical(&parameter.r#type))
    }

    /// The index a member's recursive parameter type takes.
    fn member_index(&self, carrier: &Carrier, ty: &SemanticType) -> Option<usize> {
        let Carrier::Family { family, arguments } = carrier else {
            return Some(0);
        };
        match ty {
            SemanticType::Named { member, .. } => self
                .family_of(member)
                .filter(|(found, _)| Arc::ptr_eq(found, family))
                .map(|(_, index)| index),
            SemanticType::List { element } => family.list_index(arguments, element),
            _ => None,
        }
    }

    /// The constructors of a carrier.
    fn carrier_cases(&mut self, carrier: &Carrier) -> Result<Vec<CarrierCase>, Diagnostic> {
        let mut cases = Vec::new();
        match carrier {
            Carrier::Family { family, arguments } => {
                let home = family.home.clone();
                for (constructor, at, shape) in family.constructors() {
                    let head = Head::Constructor(self.spell(&home, &constructor)?);
                    let case = match shape {
                        Shape::Base(_) => {
                            let member = MemberRef {
                                module: Some(home.clone()),
                                name: constructor.clone(),
                            };
                            let (_, fields) = self.constructor(&member, arguments)?;
                            let locals = fields
                                .iter()
                                .map(|field| list_local(family, arguments, field))
                                .collect();
                            CarrierCase {
                                short: last_segment(&constructor).to_owned(),
                                at,
                                fields,
                                locals,
                                constructor: member,
                                type_arguments: arguments.clone(),
                                head,
                            }
                        }
                        Shape::Nil | Shape::Cons => {
                            let element = family
                                .element(at, arguments)
                                .ok_or_else(|| fail("a family list names no list"))?;
                            let list = SemanticType::List {
                                element: Box::new(element.clone()),
                            };
                            let local = FamilyLocal {
                                family: family.clone(),
                                arguments: arguments.clone(),
                                index: at,
                            };
                            let cons = shape == Shape::Cons;
                            CarrierCase {
                                short: if cons { "cons" } else { "nil" }.to_owned(),
                                at,
                                fields: if cons {
                                    vec![element.clone(), list]
                                } else {
                                    Vec::new()
                                },
                                locals: if cons {
                                    vec![None, Some(local)]
                                } else {
                                    Vec::new()
                                },
                                constructor: builtin(if cons { "List.cons" } else { "List.nil" }),
                                type_arguments: vec![element],
                                head,
                            }
                        }
                    };
                    cases.push(case);
                }
            }
            Carrier::Plain(SemanticType::Nat) => {
                cases.push(plain_case(
                    "zero",
                    Vec::new(),
                    builtin("Nat.zero"),
                    Vec::new(),
                    Head::Zero,
                ));
                cases.push(plain_case(
                    "succ",
                    vec![SemanticType::Nat],
                    builtin("Nat.succ"),
                    Vec::new(),
                    Head::Succ,
                ));
            }
            Carrier::Plain(list @ SemanticType::List { element }) => {
                let element = element.as_ref().clone();
                cases.push(plain_case(
                    "nil",
                    Vec::new(),
                    builtin("List.nil"),
                    vec![element.clone()],
                    Head::Constructor("Nil".to_owned()),
                ));
                cases.push(plain_case(
                    "cons",
                    vec![element.clone(), list.clone()],
                    builtin("List.cons"),
                    vec![element],
                    Head::Constructor("Con".to_owned()),
                ));
            }
            Carrier::Plain(SemanticType::Named { member, arguments }) => {
                let home = self.home(member);
                let SemanticDeclaration::Inductive { constructors, .. } =
                    self.declaration(member)?
                else {
                    return Err(fail(format!("`{}` is not an inductive", member.name)));
                };
                for constructor in constructors {
                    let full = MemberRef {
                        module: Some(home.clone()),
                        name: format!("{}.{}", member.name, constructor.name),
                    };
                    let (_, fields) = self.constructor(&full, arguments)?;
                    let head = Head::Constructor(self.member(&full)?);
                    cases.push(plain_case(
                        &constructor.name,
                        fields,
                        full,
                        arguments.clone(),
                        head,
                    ));
                }
            }
            Carrier::Plain(other) => {
                return Err(fail(format!(
                    "a mutual group recurses over `{other:?}`, which carries no merged definition"
                )))
            }
        }
        Ok(cases)
    }

    /// The Bend type of the carrier, at index `index` for a family.
    fn carrier_type(&mut self, carrier: &Carrier, index: BTerm) -> Result<BTerm, Diagnostic> {
        match carrier {
            Carrier::Family { family, arguments } => {
                let family = family.clone();
                self.family_type(&family, arguments, index)
            }
            Carrier::Plain(ty) => self.ty(ty),
        }
    }

    /// Lower a simultaneous mutual group as one definition over `carrier`.
    #[allow(clippy::too_many_lines)]
    pub(super) fn merged_group(
        &mut self,
        members: &[&SemanticDeclaration],
        carrier: Carrier,
    ) -> Result<Vec<Item>, Diagnostic> {
        let first = members
            .first()
            .ok_or_else(|| fail("an empty mutual group"))?;
        let SemanticDeclaration::Definition {
            type_parameters, ..
        } = first
        else {
            return Err(fail("a mutual group holds a non-definition"));
        };
        let type_parameters = type_parameters.clone();
        let go = names::global(&format!("{}.ll_go", first.name()))?;
        let selector = names::global(&format!("{}.ll_sel", first.name()))?;
        let family = match &carrier {
            Carrier::Family { family, arguments } => Some((family.clone(), arguments.clone())),
            Carrier::Plain(_) => None,
        };
        let mut group = BTreeMap::new();
        let mut results = Vec::new();
        for declaration in members {
            let SemanticDeclaration::Definition {
                name,
                type_parameters: own,
                parameters,
                result,
                recursive_argument,
                termination,
                ..
            } = declaration
            else {
                return Err(fail("a mutual group holds a non-definition"));
            };
            if own != &type_parameters {
                return Err(fail(format!(
                    "the members of the mutual group of `{name}` take different type parameters"
                )));
            }
            if termination.is_some() {
                return Err(fail(format!(
                    "`{name}` is well-founded inside a simultaneous mutual group"
                )));
            }
            let recursive = recursive_argument
                .as_ref()
                .and_then(|argument| parameters.iter().position(|p| &p.name == argument))
                .ok_or_else(|| fail(format!("`{name}` names no recursive parameter")))?;
            let types: Vec<SemanticType> = parameters
                .iter()
                .map(|p| self.canonical(&p.r#type))
                .collect();
            let index = self
                .member_index(&carrier, &types[recursive])
                .ok_or_else(|| fail(format!("`{name}` does not recurse over the group's type")))?;
            let rest = bend_order(declaration)
                .into_iter()
                .filter(|p| *p != recursive)
                .collect();
            group.insert(
                name.clone(),
                GroupMember {
                    index,
                    recursive,
                    rest,
                    types,
                    result: SemanticType::Unit,
                },
            );
            group
                .get_mut(name)
                .ok_or_else(|| fail("a member vanished"))?
                .result = self.canonical(result);
            results.push(self.canonical(result));
        }
        let uniform = results.windows(2).all(|pair| pair[0] == pair[1]);
        if !uniform && results.contains(&SemanticType::Prop) {
            return Err(fail(
                "a simultaneous mutual group mixes a proposition with other results",
            ));
        }
        let context = GroupContext {
            uniform,
            carrier: carrier.clone(),
            go: go.clone(),
            selector: selector.clone(),
            members: group.clone(),
        };
        let mut items = Vec::new();
        let template_params = self.type_params(&type_parameters)?;
        let index_type = match &family {
            Some((family, _)) => Some(self.index_type(family)?),
            None => None,
        };
        // The selector: one constructor per member, carrying its other
        // arguments and, over a family, the equation fixing its index.
        let mut selector_constructors = Vec::new();
        let mut all_data = true;
        for declaration in members {
            let member = &group[declaration.name()];
            let SemanticDeclaration::Definition { parameters, .. } = declaration else {
                return Err(fail("a mutual group holds a non-definition"));
            };
            let mut fields = Vec::new();
            for position in &member.rest {
                let ty = &member.types[*position];
                all_data &= self.is_data(ty);
                let lowered = match &family {
                    Some((family, arguments)) => self.field_type(family, arguments, ty)?,
                    None => self.ty(ty)?,
                };
                fields.push((
                    synthetic(names::local(&parameters[*position].name)?),
                    lowered,
                ));
            }
            if let Some((family, _)) = &family {
                let equation = self.equation(family, var("ll_i"), member.index)?;
                fields.push((synthetic("ll_e"), equation));
            }
            selector_constructors.push((
                synthetic(selector_constructor(&selector, declaration.name())?),
                fields,
            ));
        }
        items.push(Item::Type {
            name: synthetic(selector.clone()),
            parameters: type_parameters
                .iter()
                .map(|p| names::local(p).map(synthetic))
                .collect::<Result<_, _>>()?,
            index: index_type.clone().map(|ty| (synthetic("ll_i"), ty)),
            kind: if all_data { "Data" } else { "Type" },
            constructors: selector_constructors,
            source: here(),
        });
        let mut goals = BTreeMap::new();
        for (declaration, result) in members.iter().zip(&results) {
            let goal = if *result == SemanticType::Prop {
                Goal::Prop
            } else {
                Goal::Value(self.ty(result)?)
            };
            goals.insert(declaration.name().to_owned(), goal);
        }
        let result_of = |goal: &Goal| match goal {
            Goal::Value(ty) => ty.clone(),
            Goal::Prop => BTerm::Kind("Type"),
        };
        let parameter_types: Vec<SemanticType> = type_parameters
            .iter()
            .map(|name| SemanticType::Parameter { name: name.clone() })
            .collect();
        let mut params = template_params;
        if let Some(index_type) = &index_type {
            params.push(Param {
                quantity: Quantity::Erased,
                name: synthetic("ll_i"),
                ty: index_type.clone(),
                source: here(),
            });
        }
        let carried = match &carrier {
            Carrier::Family { family, arguments } => family
                .bases
                .first()
                .map(|(base, _)| SemanticType::Named {
                    member: MemberRef {
                        module: Some(family.home.clone()),
                        name: base.clone(),
                    },
                    arguments: arguments.clone(),
                })
                .ok_or_else(|| fail("a family has no base inductive"))?,
            Carrier::Plain(ty) => ty.clone(),
        };
        let carrier_here = self.carrier_type(&carrier, var("ll_i"))?;
        params.push(Param {
            quantity: quantity(self.is_data(&carried)),
            name: synthetic("ll_x"),
            ty: carrier_here,
            source: here(),
        });
        let mut selector_args: Vec<BTerm> = parameter_types
            .iter()
            .map(|t| self.ty(t))
            .collect::<Result<_, _>>()?;
        if index_type.is_some() {
            selector_args.push(var("ll_i"));
        }
        params.push(Param {
            quantity: quantity(all_data),
            name: synthetic("ll_s"),
            ty: if selector_args.is_empty() {
                var(selector.clone())
            } else {
                BTerm::Datatype(synthetic(selector.clone()), Vec::new(), selector_args)
            },
            source: here(),
        });
        // Members with different results share `go` through a result type
        // computed from the selector, which matching the selector refines.
        let go_result = if uniform {
            let first = members.first().ok_or_else(|| fail("an empty group"))?;
            result_of(&goals[first.name()])
        } else {
            let out = names::global(&format!("{}.ll_out", first.name()))?;
            items.push(self.out_item(
                &out,
                members,
                &group,
                &type_parameters,
                index_type.as_ref(),
                &selector,
                &goals,
            )?);
            let mut args: Vec<BTerm> = type_parameters
                .iter()
                .map(|name| Ok(BTerm::Template(Box::new(var(names::local(name)?)))))
                .collect::<Result<_, Diagnostic>>()?;
            if index_type.is_some() {
                args.push(var("ll_i"));
            }
            args.push(var("ll_s"));
            call(out, args)
        };
        let saved_group = self.group.replace(context.clone());
        let saved_goal = self.goal.take();
        let outcome = self.go_cases(members, &group, &carrier, &selector, &goals);
        self.group = saved_group;
        self.goal = saved_goal;
        let cases = outcome?;
        items.append(&mut self.aux);
        items.push(Item::Def {
            name: synthetic(go.clone()),
            params,
            result: go_result,
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic("ll_x"),
                    cases,
                    source: here(),
                },
            },
            source: here(),
        });
        // Each member keeps its name and Lean's signature.
        for declaration in members {
            let member = &group[declaration.name()];
            let SemanticDeclaration::Definition { parameters, .. } = declaration else {
                return Err(fail("a mutual group holds a non-definition"));
            };
            let mut params = self.type_params(&type_parameters)?;
            let mut scope = Scope::default();
            for position in bend_order(declaration) {
                let parameter = &parameters[position];
                let spelled = names::local(&parameter.name)?;
                params.push(self.param(&spelled, &member.types[position])?);
                scope = scope.with(&parameter.name, member.types[position].clone())?;
            }
            let arguments: Vec<SemanticTerm> = parameters
                .iter()
                .map(|p| SemanticTerm::Var {
                    name: p.name.clone(),
                })
                .collect();
            // The member's own result type already states what the
            // annotation would.
            let body = match self.group_call_with(
                &context,
                declaration.name(),
                &parameter_types,
                &arguments,
                &scope,
            )? {
                BTerm::Ann(call, _) => *call,
                call => call,
            };
            items.push(Item::Def {
                name: synthetic(names::global(declaration.name())?),
                params,
                result: result_of(&goals[declaration.name()]),
                result_source: here(),
                body: Body::term(body, here()),
                source: here(),
            });
        }
        self.type_parameters.clear();
        Ok(items)
    }

    /// The cases of `go`: per carrier constructor, a match on the selector
    /// whose every member runs its body with the constructor known.
    fn go_cases(
        &mut self,
        members: &[&SemanticDeclaration],
        group: &BTreeMap<String, GroupMember>,
        carrier: &Carrier,
        selector: &str,
        goals: &BTreeMap<String, Goal>,
    ) -> Result<Vec<(Pattern, Body)>, Diagnostic> {
        let family = match carrier {
            Carrier::Family { family, .. } => Some(family.clone()),
            Carrier::Plain(_) => None,
        };
        let mut cases = Vec::new();
        for case in self.carrier_cases(carrier)? {
            let spelled: Vec<String> = case.fields.iter().map(|_| self.fresh("f")).collect();
            let fresh: Vec<String> = spelled.iter().map(|name| generated(name)).collect();
            let binders: Vec<Name> = spelled.iter().map(synthetic).collect();
            let pattern = match &case.head {
                Head::Zero => Pattern::Zero,
                Head::Succ => Pattern::Succ(
                    binders
                        .first()
                        .cloned()
                        .ok_or_else(|| fail("a successor binds no predecessor"))?,
                ),
                Head::Constructor(head) => {
                    let mut binders = binders;
                    if family.is_some() {
                        binders.push(synthetic("ll_ex"));
                    }
                    Pattern::Constructor(synthetic(head.clone()), binders)
                }
            };
            let mut scope = Scope::default();
            for ((name, field), local) in spelled.iter().zip(&case.fields).zip(&case.locals) {
                scope = match local {
                    Some(local) => scope.with_generated_family(name, field.clone(), local.clone()),
                    None => scope.with_generated(name, field.clone()),
                };
            }
            let value = SemanticTerm::Constructor {
                constructor: case.constructor.clone(),
                type_arguments: case.type_arguments.clone(),
                arguments: fresh
                    .iter()
                    .map(|name| SemanticTerm::Var { name: name.clone() })
                    .collect(),
            };
            let mut member_cases = Vec::new();
            for declaration in members {
                let member = &group[declaration.name()];
                let SemanticDeclaration::Definition {
                    parameters, body, ..
                } = declaration
                else {
                    return Err(fail("a mutual group holds a non-definition"));
                };
                let mut selector_binders: Vec<Name> = member
                    .rest
                    .iter()
                    .map(|p| names::local(&parameters[*p].name).map(synthetic))
                    .collect::<Result<_, _>>()?;
                if family.is_some() {
                    selector_binders.push(synthetic("ll_es"));
                }
                let head = synthetic(selector_constructor(selector, declaration.name())?);
                let goal = goals[declaration.name()].clone();
                self.goal = Some(goal.clone());
                let body = match &family {
                    Some(family) if member.index != case.at => {
                        self.contradiction(family, case.at, member.index, &goal)?
                    }
                    _ => {
                        let mut inner = scope.clone();
                        for position in &member.rest {
                            let parameter = &parameters[*position];
                            let ty = member.types[*position].clone();
                            inner = match carrier.list_local(&ty) {
                                Some(local) => inner.with_family(&parameter.name, ty, local)?,
                                None => inner.with(&parameter.name, ty)?,
                            };
                        }
                        let recursive = &parameters[member.recursive].name;
                        let known = resolve(body, recursive, &case.short, &fresh, &value);
                        self.tail_body(&known, &inner)?
                    }
                };
                member_cases.push((Pattern::Constructor(head, selector_binders), body));
            }
            cases.push((
                pattern,
                Body {
                    stmts: Vec::new(),
                    tail: Tail::Match {
                        scrutinee: synthetic("ll_s"),
                        cases: member_cases,
                        source: here(),
                    },
                },
            ));
        }
        Ok(cases)
    }

    /// `out(ll_s)`: the result type of the member `ll_s` selects.
    #[allow(clippy::too_many_arguments)]
    fn out_item(
        &mut self,
        out: &str,
        members: &[&SemanticDeclaration],
        group: &BTreeMap<String, GroupMember>,
        type_parameters: &[String],
        index_type: Option<&BTerm>,
        selector: &str,
        goals: &BTreeMap<String, Goal>,
    ) -> Result<Item, Diagnostic> {
        let mut params = self.type_params(type_parameters)?;
        let mut selector_args: Vec<BTerm> = type_parameters
            .iter()
            .map(|name| names::local(name).map(var))
            .collect::<Result<_, _>>()?;
        if let Some(index_type) = index_type {
            params.push(Param {
                quantity: Quantity::Erased,
                name: synthetic("ll_i"),
                ty: index_type.clone(),
                source: here(),
            });
            selector_args.push(var("ll_i"));
        }
        params.push(Param {
            quantity: Quantity::Affine,
            name: synthetic("ll_s"),
            ty: if selector_args.is_empty() {
                var(selector)
            } else {
                BTerm::Datatype(synthetic(selector), Vec::new(), selector_args)
            },
            source: here(),
        });
        let mut cases = Vec::new();
        for declaration in members {
            let member = &group[declaration.name()];
            let count = member.rest.len() + usize::from(index_type.is_some());
            let Goal::Value(result) = &goals[declaration.name()] else {
                return Err(fail("a proposition in a group with a computed result"));
            };
            cases.push((
                Pattern::Constructor(
                    synthetic(selector_constructor(selector, declaration.name())?),
                    (0..count).map(|_| synthetic("_")).collect(),
                ),
                Body::term(result.clone(), here()),
            ));
        }
        Ok(Item::Def {
            name: synthetic(out),
            params,
            result: BTerm::Kind("Type"),
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic("ll_s"),
                    cases,
                    source: here(),
                },
            },
            source: here(),
        })
    }

    /// The branch for a carrier constructor at index `at` with a member
    /// selected at index `selected`: the carrier's equation `{ll_i == at}`
    /// and the selector's `{ll_i == selected}` make `{at == selected}`.
    fn contradiction(
        &mut self,
        family: &Family,
        at: usize,
        selected: usize,
        goal: &Goal,
    ) -> Result<Body, Diagnostic> {
        let index_type = self.index_type(family)?;
        let carried = self.index_term(family, at)?;
        let chosen = self.index_term(family, selected)?;
        let proof = call(
            "Equal.trans",
            vec![
                index_type.clone(),
                carried.clone(),
                var("ll_i"),
                chosen,
                call(
                    "Equal.sym",
                    vec![index_type, var("ll_i"), carried, var("ll_ex")],
                ),
                var("ll_es"),
            ],
        );
        self.refute(family, at, selected, proof, goal)
    }

    /// A call of a member of the group being lowered, as a call of its one
    /// definition; `None` for any other call.
    pub(super) fn group_call(
        &mut self,
        function: &MemberRef,
        type_arguments: &[SemanticType],
        arguments: &[SemanticTerm],
        scope: &Scope,
    ) -> Result<Option<BTerm>, Diagnostic> {
        let Some(context) = self.group.clone() else {
            return Ok(None);
        };
        let local = function
            .module
            .as_deref()
            .is_none_or(|home| home == self.module);
        if !local || !context.members.contains_key(&function.name) {
            return Ok(None);
        }
        let type_arguments: Vec<SemanticType> =
            type_arguments.iter().map(|t| self.canonical(t)).collect();
        self.group_call_with(&context, &function.name, &type_arguments, arguments, scope)
            .map(Some)
    }

    fn group_call_with(
        &mut self,
        context: &GroupContext,
        name: &str,
        type_arguments: &[SemanticType],
        arguments: &[SemanticTerm],
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        let member = context
            .members
            .get(name)
            .ok_or_else(|| fail(format!("`{name}` is not a member of the group")))?
            .clone();
        let lower_argument = |this: &mut Self, position: usize| -> Result<BTerm, Diagnostic> {
            let argument = arguments
                .get(position)
                .ok_or_else(|| fail("a group call misses an argument"))?;
            match context.carrier.list_local(&member.types[position]) {
                Some(target) => this.family_argument(&target, argument, scope),
                None => this.term(argument, scope),
            }
        };
        let mut args = self.templates(type_arguments)?;
        if let Carrier::Family { family, .. } = &context.carrier {
            let family = family.clone();
            args.push(self.index_term(&family, member.index)?);
        }
        args.push(lower_argument(self, member.recursive)?);
        let mut fields = Vec::new();
        for position in &member.rest {
            fields.push(lower_argument(self, *position)?);
        }
        if matches!(context.carrier, Carrier::Family { .. }) {
            fields.push(BTerm::Refl);
        }
        args.push(BTerm::Constructor(
            synthetic(selector_constructor(&context.selector, name)?),
            fields,
        ));
        let call = call(context.go.clone(), args);
        if context.uniform {
            return Ok(call);
        }
        // Bend reads `go`'s computed result only by reducing it; the
        // annotation states it, so a `let` of the call can be reusable.
        let result = self.ty(&member.result)?;
        Ok(BTerm::Ann(Box::new(call), Box::new(result)))
    }
}

fn quantity(data: bool) -> Quantity {
    if data {
        Quantity::Reusable
    } else {
        Quantity::Affine
    }
}

fn builtin(name: &str) -> MemberRef {
    MemberRef {
        module: None,
        name: name.to_owned(),
    }
}

fn plain_case(
    short: &str,
    fields: Vec<SemanticType>,
    constructor: MemberRef,
    type_arguments: Vec<SemanticType>,
    head: Head,
) -> CarrierCase {
    CarrierCase {
        short: short.to_owned(),
        at: 0,
        locals: fields.iter().map(|_| None).collect(),
        fields,
        constructor,
        type_arguments,
        head,
    }
}

fn last_segment(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn selector_constructor(selector: &str, member: &str) -> Result<String, Diagnostic> {
    Ok(format!("{selector}.{}", names::local(member)?))
}

/// `body` with its recursive parameter `parameter` known to be the
/// constructor named `short` with fields named `fresh`: each match on the
/// parameter takes that constructor's branch, and any other use reads the
/// rebuilt `value`.
fn resolve(
    body: &SemanticTerm,
    parameter: &str,
    short: &str,
    fresh: &[String],
    value: &SemanticTerm,
) -> SemanticTerm {
    fn walk(term: &SemanticTerm, parameter: &str, short: &str, fresh: &[String]) -> SemanticTerm {
        if let SemanticTerm::Match {
            scrutinee,
            branches,
        } = term
        {
            if matches!(scrutinee.as_ref(), SemanticTerm::Var { name } if name == parameter) {
                if let Some(branch) = branches
                    .iter()
                    .find(|branch| last_segment(&branch.constructor.name) == short)
                {
                    let renaming: BTreeMap<String, SemanticTerm> = branch
                        .binders
                        .iter()
                        .cloned()
                        .zip(
                            fresh
                                .iter()
                                .map(|name| SemanticTerm::Var { name: name.clone() }),
                        )
                        .collect();
                    let body = normal::substitute_all(&branch.body, &renaming);
                    return walk(&body, parameter, short, fresh);
                }
            }
        }
        let mut out = term.clone();
        normal::map_children(&mut out, &mut |child| {
            *child = walk(child, parameter, short, fresh);
        });
        out
    }
    let known = walk(body, parameter, short, fresh);
    normal::substitute(&known, parameter, value)
}
