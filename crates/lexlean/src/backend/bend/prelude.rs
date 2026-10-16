//! The Bend prelude registry (`language/bend-prelude/registry.toml`): the
//! closed map from each Lean denotation a glossary entry names to the Bend
//! definition of the shipped prelude that stands for it.
//!
//! A Lean name alone does not identify a row: one Lean constant can be
//! offered under two LexLean signatures (a polymorphic `List.append` and a
//! `Nat`-specialised one), and the Bend backend passes every binder of the
//! entry's own signature. A row is therefore keyed by the Lean name and the
//! canonical signature text, the same canonical form whose hash the entry
//! records (§13.7), so a registry row and a glossary entry agree exactly or
//! not at all.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use serde::Deserialize;

use crate::code;
use crate::diagnostic::Diagnostic;

/// The embedded registry path.
pub const REGISTRY_PATH: &str = "language/bend-prelude/registry.toml";

/// The embedded prelude module path.
pub const PRELUDE_PATH: &str = "language/bend-prelude/LexLean.bend";

/// The build-relative path the prelude is published at, beside the
/// generated modules that import it.
pub const PRELUDE_BUILD_PATH: &str = "modules/LexLeanPrelude.bend";

/// The import alias every generated module gives the prelude.
pub const PRELUDE_ALIAS: &str = "L";

/// What a registry row stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConstantKind {
    /// A computational or propositional definition, called with every
    /// binder of the entry signature.
    Def,
    /// A type former.
    Type,
    /// A constructor printed as a Bend literal or constructor form.
    Constructor,
    /// A proved law, called like a definition.
    Law,
    /// An assumption: a use becomes the theorem's template premise.
    Assumption,
}

/// How a type row prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TypeForm {
    /// `List<&2, A>`.
    List,
    /// `A & B`.
    Pair,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawConstant {
    lean: String,
    signature: String,
    bend: String,
    kind: ConstantKind,
    #[serde(default)]
    prefix: Vec<String>,
    #[serde(default)]
    form: Option<TypeForm>,
    #[serde(default)]
    data: Option<bool>,
    #[serde(default)]
    origin: Option<String>,
    #[serde(default)]
    template: Option<String>,
    #[serde(default)]
    live: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawAssumption {
    name: String,
    bend_type: String,
    lean: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawRegistry {
    spec: String,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    imports: Vec<String>,
    #[serde(default)]
    core: toml::Table,
    #[serde(default)]
    literal: toml::Table,
    #[serde(default)]
    constant: Vec<RawConstant>,
    #[serde(default)]
    assumption: Vec<RawAssumption>,
}

/// One registry row.
#[derive(Debug, Clone)]
pub struct Constant {
    /// The Bend name inside the prelude (`Lean.Nat.add`), or the literal
    /// form of a constructor (`0n`, `True{}`).
    pub bend: String,
    /// The row kind.
    pub kind: ConstantKind,
    /// Arguments the backend inserts before the entry's own.
    pub prefix: Vec<String>,
    /// How a type row prints.
    pub form: Option<TypeForm>,
    /// Whether values of a propositional row are Bend `Data` (reusable).
    pub data: Option<bool>,
    /// Whether the Bend name lives in Base (no import alias) rather than
    /// in the prelude.
    pub base: bool,
    /// Implicit binders the prelude takes live rather than erased.
    pub live: Vec<String>,
}

/// One assumption the backend may turn into a template premise (§15.9 as
/// amended for Bend: an assumption is a visible premise, never an axiom).
#[derive(Debug, Clone)]
pub struct Assumption {
    /// The policy name.
    pub name: String,
    /// The Bend type of the premise.
    pub bend_type: String,
}

/// The parsed registry.
#[derive(Debug)]
pub struct Registry {
    constants: BTreeMap<(String, String), Constant>,
    assumptions: BTreeMap<String, Assumption>,
}

impl Registry {
    /// The row for a Lean name under a canonical signature.
    #[must_use]
    pub fn constant(&self, lean: &str, canonical_signature: &str) -> Option<&Constant> {
        self.constants
            .get(&(lean.to_owned(), canonical_signature.to_owned()))
    }

    /// The assumption a Lean name stands for, if it is one.
    #[must_use]
    pub fn assumption_for(&self, lean: &str) -> Option<&Assumption> {
        self.assumptions.get(lean)
    }
}

fn parse(text: &str) -> Result<Registry, String> {
    let raw: RawRegistry = toml::from_str(text).map_err(|error| error.to_string())?;
    if raw.spec != "lexlean/bend-prelude/1" {
        return Err(format!("unknown registry spec `{}`", raw.spec));
    }
    let mut constants = BTreeMap::new();
    for row in raw.constant {
        let parsed = crate::lexicon::lse::parse(&row.signature, 1024)
            .map_err(|error| format!("`{}`: {error:?}", row.lean))?;
        let canonical = parsed.print(true);
        let key = (row.lean.clone(), canonical);
        let constant = Constant {
            bend: row.bend,
            kind: row.kind,
            prefix: row.prefix,
            form: row.form,
            data: row.data,
            base: row.origin.as_deref() == Some("base"),
            live: row.live,
        };
        let _ = row.template;
        if constants.insert(key, constant).is_some() {
            return Err(format!("`{}` is registered twice under one signature", row.lean));
        }
    }
    let mut assumptions = BTreeMap::new();
    for row in raw.assumption {
        for lean in &row.lean {
            assumptions.insert(
                lean.clone(),
                Assumption {
                    name: row.name.clone(),
                    bend_type: row.bend_type.clone(),
                },
            );
        }
    }
    let _ = (raw.module, raw.imports, raw.core, raw.literal);
    Ok(Registry {
        constants,
        assumptions,
    })
}

fn embedded(path: &str) -> Option<&'static [u8]> {
    crate::embedded::FILES
        .iter()
        .find(|(candidate, _)| *candidate == path)
        .map(|(_, bytes)| *bytes)
}

/// The embedded registry, parsed once per process.
///
/// # Errors
///
/// An internal diagnostic when the embedded registry is absent or malformed:
/// it is compiler data, so this is a build defect, never a user error.
pub fn registry() -> Result<&'static Registry, Diagnostic> {
    static REGISTRY: OnceLock<Result<Registry, String>> = OnceLock::new();
    REGISTRY
        .get_or_init(|| {
            let bytes = embedded(REGISTRY_PATH)
                .ok_or_else(|| format!("`{REGISTRY_PATH}` is not embedded"))?;
            let text = std::str::from_utf8(bytes).map_err(|error| error.to_string())?;
            parse(text)
        })
        .as_ref()
        .map_err(|message| {
            Diagnostic::new(
                code!("LLB6001"),
                format!("the Bend prelude registry is unusable: {message}"),
            )
        })
}

/// The embedded prelude module bytes.
///
/// # Errors
///
/// An internal diagnostic when the prelude is not embedded.
pub fn prelude_bytes() -> Result<&'static [u8], Diagnostic> {
    embedded(PRELUDE_PATH).ok_or_else(|| {
        Diagnostic::new(
            code!("LLB6001"),
            format!("`{PRELUDE_PATH}` is not embedded"),
        )
    })
}
