//! Bend spellings of semantic names.
//!
//! A generated module shares one namespace with Base, whose top-level names
//! all begin with one of a closed set of capitalized roots (`Map`, `Set`,
//! `Event`, ...). A semantic name may begin with the same root, so every name
//! that could collide is moved under the namespace `ll`, which Base never
//! uses. A name already beginning with `ll` is moved too, so the spelling is
//! injective.

use crate::backend::bend::engine::fail;
use crate::diagnostic::Diagnostic;

/// The root segment of every top-level Base name of the pinned Bend 2.0.37
/// (`bend base`), plus the aliases the backend's own imports use.
const TAKEN_ROOTS: &[&str] = &[
    "App", "Array", "Audio", "Bool", "Chan", "Char", "Cmp", "Either", "Empty", "Equal", "Event",
    "Exists", "F32", "File", "Image", "IO", "List", "Listener", "Map", "Maybe", "Nat", "Or",
    "Pair", "Poll", "Process", "Result", "Set", "Sigma", "Socket", "String", "TCP", "U32", "UDP",
    "Unit", "Window", "Word", "Sem", "L", "S", "R", "LA", "ll",
];

/// Bend's reserved words.
const RESERVED: &[&str] = &[
    "as", "case", "def", "do", "exs", "for", "import", "is", "law", "match", "return", "type",
    "where", "Type", "Data", "Kind", "Quant",
];

fn valid_segment(segment: &str) -> bool {
    let mut chars = segment.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// The Bend spelling of a module-level semantic name.
///
/// # Errors
///
/// `LLB6008` when a segment is not a Bend identifier.
pub fn global(name: &str) -> Result<String, Diagnostic> {
    if !name.split('.').all(valid_segment) {
        return Err(fail(format!("the name `{name}` has no Bend spelling")));
    }
    let root = name.split('.').next().unwrap_or(name);
    if TAKEN_ROOTS.contains(&root) || RESERVED.contains(&root) || root.starts_with("ll_") {
        Ok(format!("ll.{name}"))
    } else {
        Ok(name.to_owned())
    }
}

/// The Bend spelling of a local (a parameter, pattern or let binder). Names
/// the backend introduces begin with `ll_`, so a source local beginning
/// with it is moved aside.
///
/// # Errors
///
/// `LLB6008` when the name is not a Bend identifier.
pub fn local(name: &str) -> Result<String, Diagnostic> {
    // A local the lowering introduces carries its Bend spelling (see
    // `generated`), which no source name, spelled with its `ll_` escape,
    // can equal.
    if let Some(spelled) = name.strip_prefix('\u{1}') {
        return Ok(spelled.to_owned());
    }
    if !valid_segment(name) {
        return Err(fail(format!("the local `{name}` has no Bend spelling")));
    }
    if RESERVED.contains(&name) || name.starts_with("ll_") || TAKEN_ROOTS.contains(&name) {
        Ok(format!("ll_{name}"))
    } else {
        Ok(name.to_owned())
    }
}

/// A Bend string literal for a semantic string. Bend reads the escapes
/// `\\`, `\"`, `\n`, `\r`, `\t` and `\u{...}`.
#[must_use]
pub fn string_literal(value: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() || !c.is_ascii() => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colliding_names_move_under_ll_and_the_spelling_is_injective() {
        assert_eq!(global("treeSize").unwrap(), "treeSize");
        assert_eq!(global("Map").unwrap(), "ll.Map");
        assert_eq!(global("Event.key").unwrap(), "ll.Event.key");
        assert_eq!(global("ll").unwrap(), "ll.ll");
        assert_ne!(global("ll.Map").unwrap(), global("Map").unwrap());
        assert_eq!(local("match").unwrap(), "ll_match");
        assert_eq!(local("ll_x").unwrap(), "ll_ll_x");
        assert!(global("a-b").is_err());
    }
}
