//! Nested and mutual inductive families (SPEC.md §18.11.3).
//!
//! Bend's termination check accepts a recursive call only on a piece of the
//! parameter in the same position, and the BendTT kernel does not accept a
//! parameter rebuilt around a smaller piece. A definition over a type with
//! a `List T` field therefore cannot walk both the type and its lists when
//! they are two Bend types, and neither can a group over mutual types. The
//! lowering makes them one: an inductive with direct `List E` fields whose
//! element mentions it, or a mutual set of inductives, is one Bend type
//! indexed by a generated enumeration, with one index per base type and
//! one per such list. Each constructor carries the equation that fixes its
//! index, and each list gets a `nil`/`cons` pair of constructors, so the
//! type at a list's index holds exactly that list's values; an impossible
//! constructor is refuted from its equation. Only a set some simultaneous
//! group recurses over is encoded; the group itself is `group.rs`.
//!
//! A list bound from such a field keeps its family form while it is
//! matched or passed to a group member, and converts to a Bend `List` at
//! any other use, so every signature keeps Lean's types. Each list's
//! conversion carries a law that converting a Lean list in and back is the
//! identity (`list_round_trip`).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Param, Pattern, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticBranch, SemanticConstructor, SemanticDeclaration, SemanticTerm, SemanticType,
};

use super::{call, here, names, qualify, substitute_type, synthetic, var};
use super::{Lower, Scope};

/// One family: the base inductives and the nested lists they share a Bend
/// type with.
#[derive(Debug)]
pub struct Family {
    /// The module that declares it.
    pub home: String,
    /// The Bend type's name: the first base inductive's.
    pub name: String,
    pub type_parameters: Vec<String>,
    /// The base inductives in source order, each with its constructors
    /// (fields qualified to `home`).
    pub bases: Vec<(String, Vec<SemanticConstructor>)>,
    /// The element types of the nested lists, qualified to `home`, over
    /// the type parameters.
    pub lists: Vec<SemanticType>,
}

impl Family {
    /// The number of indices.
    pub fn size(&self) -> usize {
        self.bases.len() + self.lists.len()
    }

    /// The index of a base inductive.
    pub fn base_index(&self, name: &str) -> Option<usize> {
        self.bases.iter().position(|(base, _)| base == name)
    }

    /// The index of a nested list of `element` at `arguments`.
    pub(super) fn list_index(
        &self,
        arguments: &[SemanticType],
        element: &SemanticType,
    ) -> Option<usize> {
        let map = self.instantiation(arguments);
        self.lists
            .iter()
            .position(|candidate| &substitute_type(candidate, &map) == element)
            .map(|k| self.bases.len() + k)
    }

    fn instantiation(&self, arguments: &[SemanticType]) -> BTreeMap<String, SemanticType> {
        self.type_parameters
            .iter()
            .cloned()
            .zip(arguments.iter().cloned())
            .collect()
    }

    /// The element type of the list at `index`, at `arguments`.
    pub(super) fn element(&self, index: usize, arguments: &[SemanticType]) -> Option<SemanticType> {
        let k = index.checked_sub(self.bases.len())?;
        self.lists
            .get(k)
            .map(|element| substitute_type(element, &self.instantiation(arguments)))
    }

    /// Every constructor of the Bend type in order, as `(short name within
    /// the family, index, kind)`.
    pub(super) fn constructors(&self) -> Vec<(String, usize, Shape)> {
        let mut out = Vec::new();
        for (index, (base, constructors)) in self.bases.iter().enumerate() {
            for constructor in constructors {
                out.push((
                    format!("{base}.{}", constructor.name),
                    index,
                    Shape::Base(constructor.fields.len()),
                ));
            }
        }
        for k in 0..self.lists.len() {
            let index = self.bases.len() + k;
            out.push((format!("{}.ll_nil{index}", self.name), index, Shape::Nil));
            out.push((format!("{}.ll_cons{index}", self.name), index, Shape::Cons));
        }
        out
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Shape {
    Base(usize),
    Nil,
    Cons,
}

impl Shape {
    pub(super) const fn fields(self) -> usize {
        match self {
            Self::Base(count) => count,
            Self::Nil => 0,
            Self::Cons => 2,
        }
    }
}

/// A local whose Bend value is a family list rather than a Bend `List`.
#[derive(Debug, Clone)]
pub struct FamilyLocal {
    pub family: Arc<Family>,
    pub arguments: Vec<SemanticType>,
    pub index: usize,
}

/// What a branch Bend reads as impossible must produce.
#[derive(Debug, Clone)]
pub enum Goal {
    /// A value of this Bend type: `Empty.absurd` of the refutation.
    Value(BTerm),
    /// A proposition: `Empty`.
    Prop,
}

/// The family local a value of `field` is, when `field` is a list of
/// `family` at `arguments`.
pub fn list_local(
    family: &Arc<Family>,
    arguments: &[SemanticType],
    field: &SemanticType,
) -> Option<FamilyLocal> {
    let SemanticType::List { element } = field else {
        return None;
    };
    let index = family.list_index(arguments, element)?;
    Some(FamilyLocal {
        family: family.clone(),
        arguments: arguments.to_vec(),
        index,
    })
}

/// A value whose family index is known.
pub struct Known {
    pub family: Arc<Family>,
    pub arguments: Vec<SemanticType>,
    pub index: usize,
}

fn mentions(ty: &SemanticType, home: &str, bases: &BTreeSet<String>) -> bool {
    match ty {
        SemanticType::Named { member, arguments } => {
            (member.module.as_deref() == Some(home) && bases.contains(&member.name))
                || arguments.iter().any(|a| mentions(a, home, bases))
        }
        SemanticType::Option { value } => mentions(value, home, bases),
        SemanticType::Result { ok, error } => {
            mentions(ok, home, bases) || mentions(error, home, bases)
        }
        SemanticType::List { element } | SemanticType::Set { element } => {
            mentions(element, home, bases)
        }
        SemanticType::Product { left, right } => {
            mentions(left, home, bases) || mentions(right, home, bases)
        }
        SemanticType::Map { key, value } => {
            mentions(key, home, bases) || mentions(value, home, bases)
        }
        SemanticType::Function { parameters, result } => {
            parameters.iter().any(|p| mentions(p, home, bases)) || mentions(result, home, bases)
        }
        _ => false,
    }
}

fn list_mentions(ty: &SemanticType, home: &str, bases: &BTreeSet<String>) -> bool {
    match ty {
        SemanticType::List { element } | SemanticType::Set { element } => {
            mentions(element, home, bases) || list_mentions(element, home, bases)
        }
        SemanticType::Named { arguments, .. } => {
            arguments.iter().any(|a| list_mentions(a, home, bases))
        }
        SemanticType::Option { value } => list_mentions(value, home, bases),
        SemanticType::Result { ok, error } => {
            list_mentions(ok, home, bases) || list_mentions(error, home, bases)
        }
        SemanticType::Product { left, right } => {
            list_mentions(left, home, bases) || list_mentions(right, home, bases)
        }
        _ => false,
    }
}

/// Compute the family `name` of `home` belongs to, from its module's
/// declarations in source order.
pub fn detect(order: &[&SemanticDeclaration], home: &str, name: &str) -> Option<Family> {
    let declaration = order.iter().find(|d| d.name() == name)?;
    let SemanticDeclaration::Inductive {
        type_parameters,
        parameters,
        mutual,
        ..
    } = declaration
    else {
        return None;
    };
    if !parameters.is_empty() {
        return None;
    }
    let mut bases = Vec::new();
    for candidate in order {
        if let SemanticDeclaration::Inductive {
            name: other,
            constructors,
            mutual: other_mutual,
            ..
        } = candidate
        {
            let member = match mutual {
                Some(key) => other_mutual.as_deref() == Some(key.as_str()),
                None => other == name,
            };
            if member {
                let constructors: Vec<SemanticConstructor> = constructors
                    .iter()
                    .map(|c| SemanticConstructor {
                        name: c.name.clone(),
                        fields: c.fields.iter().map(|f| qualify(f, home)).collect(),
                    })
                    .collect();
                bases.push((other.clone(), constructors));
            }
        }
    }
    let base_names: BTreeSet<String> = bases.iter().map(|(n, _)| n.clone()).collect();
    let mut lists: Vec<SemanticType> = Vec::new();
    for (_, constructors) in &bases {
        for constructor in constructors {
            for field in &constructor.fields {
                if let SemanticType::List { element } = field {
                    let element = element.as_ref();
                    if mentions(element, home, &base_names)
                        && !list_mentions(element, home, &base_names)
                        && !lists.contains(element)
                    {
                        lists.push(element.clone());
                    }
                }
            }
        }
    }
    if lists.is_empty() && bases.len() < 2 {
        return None;
    }
    Some(Family {
        home: home.to_owned(),
        name: bases.first()?.0.clone(),
        type_parameters: type_parameters.clone(),
        bases,
        lists,
    })
}

impl Lower<'_, '_> {
    /// The family a named type belongs to, with its base index.
    pub(super) fn family_of(&self, member: &MemberRef) -> Option<(Arc<Family>, usize)> {
        let home = self.home(member);
        let key = (home.clone(), member.name.clone());
        if let Some(found) = self
            .project
            .families
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&key)
            .cloned()
        {
            return found.and_then(|family| family.base_index(&member.name).map(|i| (family, i)));
        }
        let simultaneous = self.simultaneous();
        let detected = self
            .project
            .units
            .get(&home)
            .and_then(|unit| detect(&unit.order, &home, &member.name))
            .filter(|family| {
                family
                    .bases
                    .iter()
                    .any(|(base, _)| simultaneous.contains(&(home.clone(), base.clone())))
            })
            .map(Arc::new);
        if let Some(family) = &detected {
            let mut cache = self
                .project
                .families
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            for (base, _) in &family.bases {
                cache.insert((home.clone(), base.clone()), Some(family.clone()));
            }
        }
        self.project
            .families
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(key, detected.clone());
        detected.and_then(|family| family.base_index(&member.name).map(|i| (family, i)))
    }

    /// The inductives, by `(module, name)`, that some mutual group in the
    /// project recurses over simultaneously (see `mutual`). Only these are
    /// encoded as families: every other inductive keeps its plain Bend type,
    /// which its inlined groups already walk.
    fn simultaneous(&self) -> BTreeSet<(String, String)> {
        if let Some(found) = self
            .project
            .simultaneous
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_ref()
        {
            return found.clone();
        }
        let mut found = BTreeSet::new();
        for (home, unit) in &self.project.units {
            let keys: BTreeSet<&String> = unit
                .order
                .iter()
                .filter_map(|declaration| match declaration {
                    SemanticDeclaration::Definition {
                        mutual: Some(key), ..
                    } => Some(key),
                    _ => None,
                })
                .collect();
            for key in keys {
                let members: Vec<&SemanticDeclaration> = unit
                    .order
                    .iter()
                    .copied()
                    .filter(|declaration| {
                        matches!(declaration, SemanticDeclaration::Definition { mutual: Some(other), .. } if other == key)
                    })
                    .collect();
                if super::mutual::plan(&members, home, key).is_ok() {
                    continue;
                }
                for declaration in &members {
                    let SemanticDeclaration::Definition {
                        parameters,
                        recursive_argument: Some(argument),
                        ..
                    } = declaration
                    else {
                        continue;
                    };
                    let Some(parameter) = parameters.iter().find(|p| &p.name == argument) else {
                        continue;
                    };
                    let ty = qualify(&parameter.r#type, home);
                    let named = match &ty {
                        SemanticType::List { element } => element.as_ref(),
                        other => other,
                    };
                    if let SemanticType::Named { member, .. } = named {
                        if let Some(module) = &member.module {
                            found.insert((module.clone(), member.name.clone()));
                        }
                    }
                }
            }
        }
        *self
            .project
            .simultaneous
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(found.clone());
        found
    }

    /// Refuse a split of a family value where no impossible branch can be
    /// stated: `site` names the construct, for the diagnostic.
    pub(super) fn refuse_family_split(
        &self,
        ty: &SemanticType,
        site: &str,
    ) -> Result<(), Diagnostic> {
        match (self.known(ty), ty) {
            (Some(known), SemanticType::Named { member, .. }) => Err(fail(format!(
                "{site} splits a value of `{}`, which language 2.2 lowers as the indexed family `{}` (§18.11.3) and splits only in a definition's body",
                member.name, known.family.name
            ))),
            _ => Ok(()),
        }
    }

    /// The family and index of a value of `ty`, when it is a base type of
    /// a family.
    pub(super) fn known(&self, ty: &SemanticType) -> Option<Known> {
        let SemanticType::Named { member, arguments } = ty else {
            return None;
        };
        let (family, index) = self.family_of(member)?;
        Some(Known {
            family,
            arguments: arguments.clone(),
            index,
        })
    }

    pub(super) fn family_name(
        &mut self,
        family: &Family,
        suffix: &str,
    ) -> Result<String, Diagnostic> {
        let home = family.home.clone();
        self.spell(&home, &format!("{}.{suffix}", family.name))
    }

    pub(super) fn index_type(&mut self, family: &Family) -> Result<BTerm, Diagnostic> {
        Ok(var(self.family_name(family, "ll_index")?))
    }

    pub(super) fn index_term(
        &mut self,
        family: &Family,
        index: usize,
    ) -> Result<BTerm, Diagnostic> {
        Ok(BTerm::Constructor(
            synthetic(self.family_name(family, &format!("ll_index.i{index}"))?),
            Vec::new(),
        ))
    }

    /// The Bend type of the family at `arguments` and `index`.
    pub(super) fn family_type(
        &mut self,
        family: &Family,
        arguments: &[SemanticType],
        index: BTerm,
    ) -> Result<BTerm, Diagnostic> {
        let home = family.home.clone();
        let head = self.spell(&home, &family.name)?;
        let mut args = arguments
            .iter()
            .map(|argument| self.ty(argument))
            .collect::<Result<Vec<_>, _>>()?;
        args.push(index);
        Ok(BTerm::Datatype(synthetic(head), Vec::new(), args))
    }

    pub(super) fn equation(
        &mut self,
        family: &Family,
        left: BTerm,
        index: usize,
    ) -> Result<BTerm, Diagnostic> {
        let right = self.index_term(family, index)?;
        let ty = self.index_type(family)?;
        Ok(BTerm::Equal(Box::new(left), Box::new(right), Box::new(ty)))
    }

    pub(super) fn templates(
        &mut self,
        arguments: &[SemanticType],
    ) -> Result<Vec<BTerm>, Diagnostic> {
        arguments
            .iter()
            .map(|argument| Ok(BTerm::Template(Box::new(self.ty(argument)?))))
            .collect()
    }

    /// `List E` at the index of one of the family's lists, as the family.
    pub(super) fn field_type(
        &mut self,
        family: &Family,
        arguments: &[SemanticType],
        field: &SemanticType,
    ) -> Result<BTerm, Diagnostic> {
        if let SemanticType::List { element } = field {
            if let Some(index) = family.list_index(arguments, element) {
                let index = self.index_term(family, index)?;
                return self.family_type(family, arguments, index);
            }
        }
        self.ty(field)
    }

    /// The items a family declares, emitted at its first base inductive.
    pub(super) fn family_items(&mut self, family: &Arc<Family>) -> Result<Vec<Item>, Diagnostic> {
        let parameters: Vec<SemanticType> = family
            .type_parameters
            .iter()
            .map(|name| SemanticType::Parameter { name: name.clone() })
            .collect();
        let mut items = Vec::new();
        let index_name = synthetic(names::global(&format!("{}.ll_index", family.name))?);
        items.push(Item::Type {
            name: index_name,
            parameters: Vec::new(),
            index: None,
            kind: "Data",
            constructors: (0..family.size())
                .map(|index| {
                    Ok((
                        synthetic(names::global(&format!(
                            "{}.ll_index.i{index}",
                            family.name
                        ))?),
                        Vec::new(),
                    ))
                })
                .collect::<Result<_, Diagnostic>>()?,
            source: here(),
        });
        let mut constructors = Vec::new();
        for (index, (base, base_constructors)) in family.bases.iter().enumerate() {
            for constructor in base_constructors {
                let mut fields = Vec::new();
                for (position, field) in constructor.fields.iter().enumerate() {
                    fields.push((
                        synthetic(format!("a{position}")),
                        self.field_type(family, &parameters, field)?,
                    ));
                }
                let equation = self.equation(family, var("ll_i"), index)?;
                fields.push((synthetic("ll_e"), equation));
                constructors.push((
                    synthetic(names::global(&format!("{base}.{}", constructor.name))?),
                    fields,
                ));
            }
        }
        for k in 0..family.lists.len() {
            let index = family.bases.len() + k;
            let element = family.lists[k].clone();
            let nil_equation = self.equation(family, var("ll_i"), index)?;
            constructors.push((
                synthetic(names::global(&format!("{}.ll_nil{index}", family.name))?),
                vec![(synthetic("ll_e"), nil_equation)],
            ));
            let head = self.ty(&element)?;
            let index_term = self.index_term(family, index)?;
            let tail = self.family_type(family, &parameters, index_term)?;
            let cons_equation = self.equation(family, var("ll_i"), index)?;
            constructors.push((
                synthetic(names::global(&format!("{}.ll_cons{index}", family.name))?),
                vec![
                    (synthetic("a0"), head),
                    (synthetic("a1"), tail),
                    (synthetic("ll_e"), cons_equation),
                ],
            ));
        }
        let kind = if family.bases.iter().all(|(base, _)| {
            self.is_data(&SemanticType::Named {
                member: MemberRef {
                    module: Some(family.home.clone()),
                    name: base.clone(),
                },
                arguments: parameters.clone(),
            })
        }) {
            "Data"
        } else {
            "Type"
        };
        let index_type = self.index_type(family)?;
        items.push(Item::Type {
            name: synthetic(names::global(&family.name)?),
            parameters: family
                .type_parameters
                .iter()
                .map(|p| names::local(p).map(synthetic))
                .collect::<Result<_, _>>()?,
            index: Some((synthetic("ll_i"), index_type)),
            kind,
            constructors,
            source: here(),
        });
        // `ll_not{c}` is `Empty` exactly at index `c`: the motive that
        // refutes an equation `{i_a == i_c}` for `a != c`.
        for c in 0..family.size() {
            let mut cases = Vec::new();
            for index in 0..family.size() {
                let head = self.index_term(family, index)?;
                let BTerm::Constructor(name, _) = head else {
                    return Err(fail("an index is not a constructor"));
                };
                cases.push((
                    Pattern::Constructor(name, Vec::new()),
                    Body::term(var(if index == c { "Empty" } else { "Unit" }), here()),
                ));
            }
            let index_type = self.index_type(family)?;
            items.push(Item::Def {
                name: synthetic(names::global(&format!("{}.ll_not{c}", family.name))?),
                params: vec![Param {
                    quantity: Quantity::Reusable,
                    name: synthetic("ll_k"),
                    ty: index_type,
                    source: here(),
                }],
                result: BTerm::Kind("Type"),
                result_source: here(),
                body: Body {
                    stmts: Vec::new(),
                    tail: Tail::Match {
                        scrutinee: synthetic("ll_k"),
                        cases,
                        source: here(),
                    },
                },
                source: here(),
            });
        }
        for a in 0..family.size() {
            for c in 0..family.size() {
                if a == c {
                    continue;
                }
                let left = self.index_term(family, a)?;
                let equation = self.equation(family, left, c)?;
                let motive = call(
                    names::global(&format!("{}.ll_not{c}", family.name))?,
                    vec![BTerm::Hole],
                );
                items.push(Item::Def {
                    name: synthetic(names::global(&format!("{}.ll_clash{a}_{c}", family.name))?),
                    params: vec![Param {
                        quantity: Quantity::Affine,
                        name: synthetic("ll_h"),
                        ty: equation,
                        source: here(),
                    }],
                    result: var("Empty"),
                    result_source: here(),
                    body: Body {
                        stmts: vec![Stmt::Rewrite {
                            proof: var("ll_h"),
                            motive,
                            source: here(),
                        }],
                        tail: Tail::Term(BTerm::Constructor(synthetic("Unit"), Vec::new()), here()),
                    },
                    source: here(),
                });
            }
        }
        for k in 0..family.lists.len() {
            let index = family.bases.len() + k;
            items.push(self.list_from_definition(family, &parameters, index)?);
            items.push(self.list_to_definition(family, &parameters, index)?);
            items.append(&mut self.list_round_trip(family, &parameters, index)?);
        }
        self.type_parameters.clear();
        Ok(items)
    }

    fn list_from_definition(
        &mut self,
        family: &Arc<Family>,
        parameters: &[SemanticType],
        index: usize,
    ) -> Result<Item, Diagnostic> {
        let element = family
            .element(index, parameters)
            .ok_or_else(|| fail("a list index names no list"))?;
        let mut params = self.type_params(&family.type_parameters)?;
        let list = SemanticType::List {
            element: Box::new(element),
        };
        params.push(self.param("ll_xs", &list)?);
        let index_term = self.index_term(family, index)?;
        let result = self.family_type(family, parameters, index_term)?;
        let name = names::global(&format!("{}.ll_from{index}", family.name))?;
        let mut recursive = self.templates(parameters)?;
        recursive.push(var("ll_t"));
        let nil = BTerm::Constructor(
            synthetic(names::global(&format!("{}.ll_nil{index}", family.name))?),
            vec![BTerm::Refl],
        );
        let cons = BTerm::Constructor(
            synthetic(names::global(&format!("{}.ll_cons{index}", family.name))?),
            vec![var("ll_h"), call(name.clone(), recursive), BTerm::Refl],
        );
        Ok(Item::Def {
            name: synthetic(name),
            params,
            result,
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic("ll_xs"),
                    cases: vec![
                        (
                            Pattern::Constructor(synthetic("Nil"), Vec::new()),
                            Body::term(nil, here()),
                        ),
                        (
                            Pattern::Constructor(
                                synthetic("Con"),
                                vec![synthetic("ll_h"), synthetic("ll_t")],
                            ),
                            Body::term(cons, here()),
                        ),
                    ],
                    source: here(),
                },
            },
            source: here(),
        })
    }

    fn list_to_definition(
        &mut self,
        family: &Arc<Family>,
        parameters: &[SemanticType],
        index: usize,
    ) -> Result<Item, Diagnostic> {
        let element = family
            .element(index, parameters)
            .ok_or_else(|| fail("a list index names no list"))?;
        let mut params = self.type_params(&family.type_parameters)?;
        let index_term = self.index_term(family, index)?;
        let family_list = self.family_type(family, parameters, index_term)?;
        params.push(Param {
            quantity: Quantity::Reusable,
            name: synthetic("ll_x"),
            ty: family_list,
            source: here(),
        });
        let list = SemanticType::List {
            element: Box::new(element),
        };
        let result = self.ty(&list)?;
        let name = names::global(&format!("{}.ll_to{index}", family.name))?;
        let mut cases = Vec::new();
        for (constructor, at, shape) in family.constructors() {
            let head = synthetic(names::global(&constructor)?);
            let mut binders: Vec<_> = (0..shape.fields()).map(|_| synthetic("_")).collect();
            if at == index {
                let body = match shape {
                    Shape::Nil => BTerm::Constructor(synthetic("Nil"), Vec::new()),
                    _ => {
                        binders = vec![synthetic("ll_h"), synthetic("ll_t")];
                        let mut recursive = self.templates(parameters)?;
                        recursive.push(var("ll_t"));
                        BTerm::Constructor(
                            synthetic("Con"),
                            vec![var("ll_h"), call(name.clone(), recursive)],
                        )
                    }
                };
                binders.push(synthetic("_"));
                cases.push((
                    Pattern::Constructor(head, binders),
                    Body::term(body, here()),
                ));
            } else {
                binders.push(synthetic("ll_e"));
                let refuted =
                    self.refute(family, index, at, var("ll_e"), &Goal::Value(result.clone()))?;
                cases.push((Pattern::Constructor(head, binders), refuted));
            }
        }
        Ok(Item::Def {
            name: synthetic(name),
            params,
            result,
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
        })
    }

    /// `Fam.ll_to_from{index}`: converting a Lean list into the family and
    /// back is the identity, by induction on the list (§18.11.3). The other
    /// direction holds only up to the index equations the family's
    /// constructors carry, which BendTT does not identify.
    fn list_round_trip(
        &mut self,
        family: &Arc<Family>,
        parameters: &[SemanticType],
        index: usize,
    ) -> Result<Vec<Item>, Diagnostic> {
        let element = family
            .element(index, parameters)
            .ok_or_else(|| fail("a list index names no list"))?;
        let list = SemanticType::List {
            element: Box::new(element),
        };
        let list_type = self.ty(&list)?;
        let name = names::global(&format!("{}.ll_to_from{index}", family.name))?;
        let helper = format!("{name}.i0");
        let from = names::global(&format!("{}.ll_from{index}", family.name))?;
        let to = names::global(&format!("{}.ll_to{index}", family.name))?;
        let templates = self.templates(parameters)?;
        let round = |lower_templates: &[BTerm], xs: BTerm| {
            let mut inner = lower_templates.to_vec();
            inner.push(xs);
            let mut outer = lower_templates.to_vec();
            outer.push(call(from.clone(), inner));
            call(to.clone(), outer)
        };
        let claim = |xs: BTerm, templates: &[BTerm]| {
            BTerm::Equal(
                Box::new(round(templates, xs.clone())),
                Box::new(xs),
                Box::new(list_type.clone()),
            )
        };
        let mut params = self.type_params(&family.type_parameters)?;
        params.push(self.param("ll_xs", &list)?);
        let mut recursive = templates.clone();
        recursive.push(var("ll_t"));
        // `Con{ll_h, to(from(ll_t))} == Con{ll_h, ll_t}`, rewritten by the
        // hypothesis on the tail.
        let motive = BTerm::Equal(
            Box::new(BTerm::Constructor(
                synthetic("Con"),
                vec![var("ll_h"), BTerm::Hole],
            )),
            Box::new(BTerm::Constructor(
                synthetic("Con"),
                vec![var("ll_h"), var("ll_t")],
            )),
            Box::new(list_type.clone()),
        );
        let symmetric = call(
            "Equal.sym".to_owned(),
            vec![
                list_type.clone(),
                round(&templates, var("ll_t")),
                var("ll_t"),
                var("ll_r"),
            ],
        );
        let cons = Body {
            stmts: vec![
                Stmt::Let {
                    name: synthetic("ll_r"),
                    value: call(helper.clone(), recursive),
                    source: here(),
                },
                Stmt::Rewrite {
                    proof: symmetric,
                    motive,
                    source: here(),
                },
            ],
            tail: Tail::Term(BTerm::Refl, here()),
        };
        let definition = Item::Def {
            name: synthetic(helper.clone()),
            params: params.clone(),
            result: claim(var("ll_xs"), &templates),
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic("ll_xs"),
                    cases: vec![
                        (
                            Pattern::Constructor(synthetic("Nil"), Vec::new()),
                            Body::term(BTerm::Refl, here()),
                        ),
                        (
                            Pattern::Constructor(
                                synthetic("Con"),
                                vec![synthetic("+ll_h"), synthetic("+ll_t")],
                            ),
                            cons,
                        ),
                    ],
                    source: here(),
                },
            },
            source: here(),
        };
        let mut arguments: Vec<BTerm> = family
            .type_parameters
            .iter()
            .map(|p| names::local(p).map(var))
            .collect::<Result<_, _>>()?;
        arguments.push(var("ll_xs"));
        let law = Item::Law {
            name: synthetic(name),
            params,
            claim: claim(var("ll_xs"), &templates),
            claim_source: here(),
            proof: Body::term(call(helper, arguments), here()),
            source: here(),
        };
        Ok(vec![definition, law])
    }

    /// The body of a branch Bend reads as impossible: `proof` equates index
    /// `actual` with index `claimed`.
    pub(super) fn refute(
        &mut self,
        family: &Family,
        actual: usize,
        claimed: usize,
        proof: BTerm,
        goal: &Goal,
    ) -> Result<Body, Diagnostic> {
        Ok(Body::term(
            match goal {
                Goal::Prop => var("Empty"),
                Goal::Value(ty) => {
                    let clash = self.family_name(family, &format!("ll_clash{actual}_{claimed}"))?;
                    call("Empty.absurd", vec![ty.clone(), call(clash, vec![proof])])
                }
            },
            here(),
        ))
    }

    /// The cases of a match on the local `name` of type `ty`, each branch
    /// body lowered by `lower`: when the local is a family value, its
    /// constructors at other indices are added, each refuted from its
    /// equation, and the cases follow the type's constructor order.
    pub(super) fn match_cases(
        &mut self,
        name: &str,
        ty: &SemanticType,
        branches: &[SemanticBranch],
        scope: &Scope,
        lower: &mut dyn FnMut(&mut Self, &SemanticTerm, &Scope) -> Result<Body, Diagnostic>,
    ) -> Result<Vec<(Pattern, Body)>, Diagnostic> {
        let local = scope.family(name).cloned();
        let known = match &local {
            Some(local) => Some(Known {
                family: local.family.clone(),
                arguments: local.arguments.clone(),
                index: local.index,
            }),
            None => self.known(ty),
        };
        let mut cases = Vec::new();
        for branch in branches {
            let (pattern, inner) = match &local {
                Some(local) => {
                    self.list_branch(local, &branch.constructor, &branch.binders, scope)?
                }
                None => (
                    self.pattern(ty, &branch.constructor, &branch.binders)?,
                    self.branch_scope(ty, branch, scope)?,
                ),
            };
            cases.push((pattern, lower(self, &branch.body, &inner)?));
        }
        let Some(known) = known else {
            return Ok(cases);
        };
        let goal = self.goal.clone().ok_or_else(|| {
            fail("a match on a nested or mutual inductive value lies where its result type is not known, which language 2.2 does not lower")
        })?;
        let home = known.family.home.clone();
        let mut ordered = Vec::new();
        for (constructor, at, shape) in known.family.constructors() {
            let head = self.spell(&home, &constructor)?;
            if at == known.index {
                let position = cases
                    .iter()
                    .position(|(pattern, _)| matches!(pattern, Pattern::Constructor(found, _) if found.text == head))
                    .ok_or_else(|| fail(format!("a match omits the constructor `{constructor}`")))?;
                ordered.push(cases.remove(position));
            } else {
                let mut binders: Vec<_> = (0..shape.fields()).map(|_| synthetic("_")).collect();
                binders.push(synthetic("ll_e"));
                let body = self.refute(&known.family, known.index, at, var("ll_e"), &goal)?;
                ordered.push((Pattern::Constructor(synthetic(head), binders), body));
            }
        }
        Ok(ordered)
    }

    /// The pattern and scope of a branch over a family list.
    pub(super) fn list_branch(
        &mut self,
        local: &FamilyLocal,
        constructor: &MemberRef,
        binders: &[String],
        scope: &Scope,
    ) -> Result<(Pattern, Scope), Diagnostic> {
        let family = &local.family;
        let home = family.home.clone();
        let element = family
            .element(local.index, &local.arguments)
            .ok_or_else(|| fail("a family list names no list"))?;
        let short = constructor
            .name
            .rsplit('.')
            .next()
            .unwrap_or(&constructor.name);
        match short {
            "nil" => Ok((
                Pattern::Constructor(
                    synthetic(
                        self.spell(&home, &format!("{}.ll_nil{}", family.name, local.index))?,
                    ),
                    vec![synthetic("_")],
                ),
                scope.clone(),
            )),
            "cons" => {
                let (head, tail) = match binders {
                    [head, tail] => (head, tail),
                    _ => return Err(fail("a list pattern binds other than head and tail")),
                };
                let inner = scope.with(head, element.clone())?;
                let inner = inner.with_family(
                    tail,
                    SemanticType::List {
                        element: Box::new(element),
                    },
                    local.clone(),
                )?;
                Ok((
                    Pattern::Constructor(
                        synthetic(
                            self.spell(&home, &format!("{}.ll_cons{}", family.name, local.index))?,
                        ),
                        vec![
                            synthetic(names::local(head)?),
                            synthetic(names::local(tail)?),
                            synthetic("_"),
                        ],
                    ),
                    inner,
                ))
            }
            other => Err(fail(format!("`{other}` is not a list constructor"))),
        }
    }

    /// The family local a field binder of a base constructor opens, when
    /// the field is one of the family's lists.
    /// A family list as a Bend `List`.
    pub(super) fn bend_list(
        &mut self,
        local: &FamilyLocal,
        value: BTerm,
    ) -> Result<BTerm, Diagnostic> {
        let name = self.family_name(&local.family, &format!("ll_to{}", local.index))?;
        let mut args = self.templates(&local.arguments)?;
        args.push(value);
        Ok(call(name, args))
    }

    pub(super) fn family_list(
        &mut self,
        local: &FamilyLocal,
        value: BTerm,
    ) -> Result<BTerm, Diagnostic> {
        let name = self.family_name(&local.family, &format!("ll_from{}", local.index))?;
        let mut args = self.templates(&local.arguments)?;
        args.push(value);
        Ok(call(name, args))
    }

    /// A family list from a term: the local itself when it already is one
    /// at that index, else the conversion of its value.
    pub(super) fn family_argument(
        &mut self,
        target: &FamilyLocal,
        argument: &SemanticTerm,
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        if let SemanticTerm::Var { name } = argument {
            if let Some(local) = scope.family(name) {
                if Arc::ptr_eq(&local.family, &target.family) && local.index == target.index {
                    return Ok(var(scope.get(name)?.0.clone()));
                }
            }
        }
        let value = self.term(argument, scope)?;
        self.family_list(target, value)
    }

    /// A constructor of a family's base inductive applied to its fields:
    /// list fields in family form, then the equation.
    pub(super) fn family_constructor(
        &mut self,
        constructor: &MemberRef,
        type_arguments: &[SemanticType],
        arguments: &[SemanticTerm],
        scope: &Scope,
    ) -> Result<Option<BTerm>, Diagnostic> {
        // A builtin constructor's owner (`List`, `Option`, ..) is no family.
        let Some((owner, _)) = constructor.name.rsplit_once('.') else {
            return Ok(None);
        };
        let owner = MemberRef {
            module: constructor.module.clone(),
            name: owner.to_owned(),
        };
        let Some((family, _)) = self.family_of(&owner) else {
            return Ok(None);
        };
        let type_arguments: Vec<SemanticType> =
            type_arguments.iter().map(|t| self.canonical(t)).collect();
        let (_, fields) = self.constructor(constructor, &type_arguments)?;
        let mut lowered = Vec::new();
        for (argument, field) in arguments.iter().zip(&fields) {
            lowered.push(match list_local(&family, &type_arguments, field) {
                Some(target) => self.family_argument(&target, argument, scope)?,
                None => self.term(argument, scope)?,
            });
        }
        lowered.push(BTerm::Refl);
        let head = self.document_constructor(constructor)?;
        Ok(Some(BTerm::Constructor(synthetic(head), lowered)))
    }
}
