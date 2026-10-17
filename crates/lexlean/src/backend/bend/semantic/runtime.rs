//! Runtime primitives and fixed-width literals over the ported runtime.
//!
//! The Lean backend calls a class-polymorphic runtime function and lets Lean
//! resolve the instance; Bend has no classes, so `Runtime.bend` holds one
//! definition per instance, `<constant>.<Instance>`, recorded in
//! `runtime-registry.toml`. A primitive is lowered to the definition its
//! operand types select, after checking the registry names it. A keyed
//! collection operation takes the key's instance: an atomic key type its own
//! definition, a pair of atomic keys the `.Prod` definition with the two
//! component codes, and any other pair of keys the generic `.Key` definition
//! with the key's code.
//!
//! The higher-order collection primitives are not in the runtime (Bend
//! cannot share a function value there); they are the closure-converted
//! folds of `Semantic.bend`.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use serde::Deserialize;

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::BTerm;
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{SemanticInteger, SemanticPrimitive as P, SemanticTerm, SemanticType};

use super::support::Support;
use super::{call, synthetic, Lower, Scope};

const REGISTRY_PATH: &str = "language/bend-prelude/runtime-registry.toml";

#[derive(Deserialize)]
struct RawRegistry {
    constant: Vec<RawConstant>,
}

#[derive(Deserialize)]
struct RawConstant {
    bend: String,
}

/// Every Bend name the runtime defines, parsed once per process.
fn defined() -> Result<&'static BTreeSet<String>, Diagnostic> {
    static NAMES: OnceLock<Result<BTreeSet<String>, String>> = OnceLock::new();
    NAMES
        .get_or_init(|| {
            let bytes = crate::embedded::FILES
                .iter()
                .find(|(path, _)| *path == REGISTRY_PATH)
                .map(|(_, bytes)| *bytes)
                .ok_or_else(|| format!("`{REGISTRY_PATH}` is not embedded"))?;
            let text = std::str::from_utf8(bytes).map_err(|error| error.to_string())?;
            let raw: RawRegistry = toml::from_str(text).map_err(|error| error.to_string())?;
            Ok(raw
                .constant
                .into_iter()
                .map(|constant| constant.bend)
                .collect())
        })
        .as_ref()
        .map_err(|message| fail(format!("the Bend runtime registry is unusable: {message}")))
}

/// The registry's instance name of a type, when it has one.
fn instance(ty: &SemanticType) -> Option<&'static str> {
    Some(match ty {
        SemanticType::Nat => "Nat",
        SemanticType::Int => "Int",
        SemanticType::Bool => "Bool",
        SemanticType::String => "String",
        SemanticType::Int8 => "Int8",
        SemanticType::Int16 => "Int16",
        SemanticType::Int32 => "Int32",
        SemanticType::Int64 => "Int64",
        SemanticType::UInt8 => "UInt8",
        SemanticType::UInt16 => "UInt16",
        SemanticType::UInt32 => "UInt32",
        SemanticType::UInt64 => "UInt64",
        SemanticType::Bytes => "ByteArray",
        SemanticType::Ordering => "Ordering",
        SemanticType::List { .. } => "List",
        _ => return None,
    })
}

/// The registry's instance name of a fixed-width type.
fn fixed(ty: &SemanticType) -> Option<&'static str> {
    match ty {
        SemanticType::Int8
        | SemanticType::Int16
        | SemanticType::Int32
        | SemanticType::Int64
        | SemanticType::UInt8
        | SemanticType::UInt16
        | SemanticType::UInt32
        | SemanticType::UInt64 => instance(ty),
        _ => None,
    }
}

fn option_value(ty: &SemanticType) -> Option<&SemanticType> {
    match ty {
        SemanticType::Option { value } => Some(value),
        _ => None,
    }
}

impl Lower<'_, '_> {
    pub(super) fn runtime(&mut self, name: &str) -> Result<String, Diagnostic> {
        if !defined()?.contains(name) {
            return Err(fail(format!(
                "the Bend runtime defines no `{name}`, so this primitive has no Bend lowering at these types"
            )));
        }
        self.uses_prelude = true;
        self.supports.insert(Support::Runtime);
        Ok(format!("{}.{name}", Support::Runtime.alias()))
    }

    /// The Bend type of a fixed-width integer or a byte string.
    pub(super) fn runtime_type(&mut self, ty: &SemanticType) -> Result<BTerm, Diagnostic> {
        match ty {
            // Lean's `UInt32` is Base's own `U32` (registry, representation).
            SemanticType::UInt32 => Ok(super::var("U32")),
            SemanticType::Bytes => Ok(super::var(self.runtime("Lean.ByteArray")?)),
            other => {
                let name = fixed(other).ok_or_else(|| fail("not a runtime type"))?;
                Ok(super::var(self.runtime(&format!("Lean.{name}"))?))
            }
        }
    }

    /// A fixed-width literal: `lit` of its magnitude modulo the width (and
    /// `lit2` past `U32`), negated as Lean elaborates a negative literal.
    pub(super) fn fixed_literal(
        &mut self,
        representation: SemanticInteger,
        value: &str,
    ) -> Result<BTerm, Diagnostic> {
        let ty = representation.semantic_type();
        let name = fixed(&ty).ok_or_else(|| fail("not a fixed-width literal"))?;
        let (negative, magnitude) = match value.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, value),
        };
        let magnitude: u64 = magnitude
            .parse()
            .map_err(|_| fail(format!("the literal `{value}` has no Bend spelling")))?;
        let literal = match u32::try_from(magnitude) {
            Ok(small) => call(
                self.runtime(&format!("Lean.{name}.lit"))?,
                vec![BTerm::U32(small)],
            ),
            Err(_) => {
                let high =
                    u32::try_from(magnitude >> 32).map_err(|_| fail("a literal overflows"))?;
                let low = u32::try_from(magnitude & 0xffff_ffff)
                    .map_err(|_| fail("a literal overflows"))?;
                call(
                    self.runtime(&format!("Lean.{name}.lit2"))?,
                    vec![BTerm::U32(high), BTerm::U32(low)],
                )
            }
        };
        if negative {
            Ok(call(
                self.runtime(&format!("Lean.{name}.neg"))?,
                vec![literal],
            ))
        } else {
            Ok(literal)
        }
    }

    /// A byte-string literal from its lowercase hexadecimal.
    pub(super) fn bytes_literal(&mut self, hex: &str) -> Result<BTerm, Diagnostic> {
        let mut bytes = Vec::new();
        for pair in hex.as_bytes().chunks(2) {
            let text =
                std::str::from_utf8(pair).map_err(|_| fail("a byte literal is not ASCII"))?;
            let value = u32::from_str_radix(text, 16)
                .map_err(|_| fail("a byte literal is not hexadecimal"))?;
            bytes.push(call(
                self.runtime("Lean.UInt8.lit")?,
                vec![BTerm::U32(value)],
            ));
        }
        let mut list = BTerm::Constructor(synthetic("Nil"), Vec::new());
        for byte in bytes.into_iter().rev() {
            list = BTerm::Constructor(synthetic("Con"), vec![byte, list]);
        }
        let constructor = self.runtime("Lean.ByteArray.mk")?;
        Ok(BTerm::Constructor(synthetic(constructor), vec![list]))
    }

    /// The code of a key type in the runtime's universe of keys.
    fn key_code(&mut self, key: &SemanticType) -> Result<BTerm, Diagnostic> {
        if let SemanticType::Product { left, right } = key {
            let (left, right) = (self.key_code(left)?, self.key_code(right)?);
            return Ok(BTerm::Constructor(
                synthetic(self.runtime("LexLeanCollections.Key.Prod")?),
                vec![left, right],
            ));
        }
        let name = instance(key)
            .filter(|name| !matches!(*name, "ByteArray" | "List"))
            .ok_or_else(|| {
                fail(format!(
                    "`{key:?}` is not an ordered key type of the Bend runtime"
                ))
            })?;
        Ok(BTerm::Constructor(
            synthetic(self.runtime(&format!("LexLeanCollections.Key.{name}"))?),
            Vec::new(),
        ))
    }

    /// A keyed collection call: the key's instance, then the remaining type
    /// arguments, then the arguments.
    fn keyed(
        &mut self,
        base: &str,
        key: &SemanticType,
        types: Vec<BTerm>,
        arguments: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        let mut args = Vec::new();
        let head = match key {
            SemanticType::Product { left, right }
                if instance(left).is_some() && instance(right).is_some() =>
            {
                args.push(self.key_code(left)?);
                args.push(self.key_code(right)?);
                self.runtime(&format!("{base}.Prod"))?
            }
            SemanticType::Product { .. } => {
                args.push(self.key_code(key)?);
                self.runtime(&format!("{base}.Key"))?
            }
            atomic => {
                let name = instance(atomic).ok_or_else(|| {
                    fail(format!(
                        "`{atomic:?}` is not an ordered key type of the Bend runtime"
                    ))
                })?;
                self.runtime(&format!("{base}.{name}"))?
            }
        };
        args.extend(types);
        args.extend(arguments);
        Ok(call(head, args))
    }

    /// Lower one primitive application.
    #[allow(clippy::too_many_lines)]
    pub(super) fn primitive(
        &mut self,
        operation: P,
        arguments: &[SemanticTerm],
        result: &SemanticType,
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        let result = self.canonical(result);
        let mut types = Vec::new();
        for argument in arguments {
            let ty = self.infer(argument, scope)?;
            types.push(self.canonical(&ty));
        }
        let first = types.first().cloned().unwrap_or(SemanticType::Unit);
        if let Some(fold) = self.fold(operation, arguments, &types, &result, scope)? {
            return Ok(fold);
        }
        let lowered = self.arguments(arguments, scope)?;
        let named = |what: Option<&'static str>| {
            what.ok_or_else(|| {
                fail(format!(
                    "the primitive `{operation:?}` has no Bend lowering at these types"
                ))
            })
        };
        let simple = |lower: &mut Self, name: String, types: Vec<BTerm>, lowered: Vec<BTerm>| {
            let head = lower.runtime(&name)?;
            let mut args = types;
            args.extend(lowered);
            Ok::<BTerm, Diagnostic>(call(head, args))
        };
        match operation {
            P::Subtract | P::Multiply | P::Negate | P::Quotient | P::Remainder => {
                let base = match operation {
                    P::Subtract => "subtract",
                    P::Multiply => "multiply",
                    P::Negate => "negate",
                    P::Quotient => "quotient",
                    _ => "remainder",
                };
                simple(
                    self,
                    format!("LexLeanRuntime.{base}.{}", named(instance(&result))?),
                    Vec::new(),
                    lowered,
                )
            }
            P::CheckedAdd
            | P::CheckedSubtract
            | P::CheckedMultiply
            | P::CheckedNegate
            | P::CheckedQuotient => {
                let base = match operation {
                    P::CheckedAdd => "checkedAdd",
                    P::CheckedSubtract => "checkedSubtract",
                    P::CheckedMultiply => "checkedMultiply",
                    P::CheckedNegate => "checkedNegate",
                    _ => "checkedQuotient",
                };
                let target = named(option_value(&result).and_then(fixed))?;
                simple(
                    self,
                    format!("LexLeanRuntime.{base}.{target}"),
                    Vec::new(),
                    lowered,
                )
            }
            P::CheckedConvert => {
                let source = named(instance(&first))?;
                let target = named(option_value(&result).and_then(instance))?;
                simple(
                    self,
                    format!("LexLeanRuntime.checkedConvert.{source}.{target}"),
                    Vec::new(),
                    lowered,
                )
            }
            P::BitAnd | P::BitOr | P::BitXor | P::BitNot | P::ShiftLeft | P::ShiftRight => {
                let base = match operation {
                    P::BitAnd => "bitAnd",
                    P::BitOr => "bitOr",
                    P::BitXor => "bitXor",
                    P::BitNot => "bitNot",
                    P::ShiftLeft => "shiftLeft",
                    _ => "shiftRight",
                };
                simple(
                    self,
                    format!("LexLeanRuntime.{base}.{}", named(fixed(&first))?),
                    Vec::new(),
                    lowered,
                )
            }
            P::Append | P::Length | P::Index | P::Slice => {
                let base = match operation {
                    P::Append => "append",
                    P::Length => "length",
                    P::Index => "index",
                    _ => "slice",
                };
                let generic = match &first {
                    SemanticType::List { element } => vec![self.ty(element)?],
                    _ => Vec::new(),
                };
                simple(
                    self,
                    format!("LexLeanRuntime.{base}.{}", named(instance(&first))?),
                    generic,
                    lowered,
                )
            }
            P::Utf8Encode | P::Utf8Decode | P::CompareBytes | P::SplitExact | P::Join => {
                let base = match operation {
                    P::Utf8Encode => "utf8Encode",
                    P::Utf8Decode => "utf8Decode",
                    P::CompareBytes => "compareBytes",
                    P::SplitExact => "splitExact",
                    _ => "join",
                };
                simple(self, format!("LexLeanRuntime.{base}"), Vec::new(), lowered)
            }
            P::Equal => simple(
                self,
                format!("LexLeanRuntime.equal.{}", named(instance(&first))?),
                Vec::new(),
                lowered,
            ),
            P::ParseDecimal => {
                let target = named(option_value(&result).and_then(instance))?;
                simple(
                    self,
                    format!("LexLeanRuntime.parseDecimal.{target}"),
                    Vec::new(),
                    lowered,
                )
            }
            P::FormatDecimal => simple(
                self,
                format!("LexLeanRuntime.formatDecimal.{}", named(instance(&first))?),
                Vec::new(),
                lowered,
            ),
            P::MapInsert | P::MapRemove | P::MapLookup | P::MapContains => {
                let SemanticType::Map { key, value } = &first else {
                    return Err(fail("a map primitive on a non-map"));
                };
                let base = match operation {
                    P::MapInsert => "mapInsert",
                    P::MapRemove => "mapRemove",
                    P::MapLookup => "mapLookup",
                    _ => "mapContains",
                };
                let value = self.ty(value)?;
                self.keyed(
                    &format!("LexLeanCollections.{base}"),
                    key,
                    vec![value],
                    lowered,
                )
            }
            P::MapSize | P::MapKeys | P::MapValues | P::MapEntries => {
                let SemanticType::Map { key, value } = &first else {
                    return Err(fail("a map primitive on a non-map"));
                };
                let base = match operation {
                    P::MapSize => "mapSize",
                    P::MapKeys => "mapKeys",
                    P::MapValues => "mapValues",
                    _ => "mapEntries",
                };
                let generic = vec![self.ty(key)?, self.ty(value)?];
                simple(self, format!("LexLeanCollections.{base}"), generic, lowered)
            }
            P::SetInsert
            | P::SetRemove
            | P::SetContains
            | P::SetUnion
            | P::SetIntersection
            | P::SetDifference => {
                let SemanticType::Set { element } = &first else {
                    return Err(fail("a set primitive on a non-set"));
                };
                let base = match operation {
                    P::SetInsert => "setInsert",
                    P::SetRemove => "setRemove",
                    P::SetContains => "setContains",
                    P::SetUnion => "setUnion",
                    P::SetIntersection => "setIntersection",
                    _ => "setDifference",
                };
                self.keyed(
                    &format!("LexLeanCollections.{base}"),
                    element,
                    Vec::new(),
                    lowered,
                )
            }
            P::SetSize | P::SetElements => {
                let SemanticType::Set { element } = &first else {
                    return Err(fail("a set primitive on a non-set"));
                };
                let base = if operation == P::SetSize {
                    "setSize"
                } else {
                    "setElements"
                };
                let generic = vec![self.ty(element)?];
                simple(self, format!("LexLeanCollections.{base}"), generic, lowered)
            }
            P::GraphSuccessors | P::GraphReachable | P::GraphTopological => {
                let SemanticType::Map { key, .. } = &first else {
                    return Err(fail("a graph primitive on a non-graph"));
                };
                let base = match operation {
                    P::GraphSuccessors => "graphSuccessors",
                    P::GraphReachable => "graphReachable",
                    _ => "graphTopological",
                };
                self.keyed(
                    &format!("LexLeanCollections.{base}"),
                    key,
                    Vec::new(),
                    lowered,
                )
            }
            P::LessThan => self.keyed("LexLeanCollections.lessThan", &first, Vec::new(), lowered),
            P::ListFold | P::SetFold | P::MapFold | P::Iterate | P::IterateUntil => {
                Err(fail("a fold reached the runtime lowering"))
            }
        }
    }

    /// A higher-order collection primitive, as a closure-converted fold of
    /// `Semantic.bend`; `None` for every other primitive.
    fn fold(
        &mut self,
        operation: P,
        arguments: &[SemanticTerm],
        types: &[SemanticType],
        result: &SemanticType,
        scope: &Scope,
    ) -> Result<Option<BTerm>, Diagnostic> {
        if !matches!(
            operation,
            P::ListFold | P::SetFold | P::MapFold | P::Iterate | P::IterateUntil
        ) {
            return Ok(None);
        }
        let [step, middle, last] = arguments else {
            return Err(fail(format!("`{operation:?}` takes three arguments")));
        };
        let converted = self.convert(step, scope)?;
        let template = |term: BTerm| BTerm::Template(Box::new(term));
        let state = match operation {
            P::IterateUntil => match result {
                SemanticType::Product { left, .. } => (**left).clone(),
                _ => return Err(fail("`iterate_until` returns a pair")),
            },
            _ => result.clone(),
        };
        let state = self.ty(&state)?;
        let mut args = Vec::new();
        let head = match operation {
            P::ListFold | P::SetFold => {
                let (SemanticType::List { element } | SemanticType::Set { element }) = &types[2]
                else {
                    return Err(fail("a fold over a non-list"));
                };
                args.push(template(self.ty(element)?));
                args.push(template(state));
                "listFold"
            }
            P::MapFold => {
                let SemanticType::Map { key, value } = &types[2] else {
                    return Err(fail("a map fold over a non-map"));
                };
                args.push(template(self.ty(key)?));
                args.push(template(self.ty(value)?));
                args.push(template(state));
                "mapFold"
            }
            P::Iterate => {
                args.push(template(state));
                "iterate"
            }
            _ => {
                args.push(template(state));
                "iterateUntil"
            }
        };
        args.push(template(converted.env_type));
        args.push(template(converted.code));
        args.push(converted.env);
        let (middle, last) = (self.term(middle, scope)?, self.term(last, scope)?);
        match operation {
            // (step, initial, collection): the collection is the decreasing
            // argument, so it comes first.
            P::ListFold | P::SetFold | P::MapFold => {
                args.push(last);
                args.push(middle);
            }
            // (step, count, state).
            _ => {
                args.push(middle);
                args.push(last);
            }
        }
        Ok(Some(call(self.support(head), args)))
    }
}
