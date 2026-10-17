//! Natural-number numerals in Bend (SPEC.md §18.10.6). Bend spells a `Nat`
//! literal up to `4294967295n`. A larger numeral is lowered to its base-65536
//! digits combined by the prelude's `Lean.Nat.add` and `Lean.Nat.mul` by
//! Horner's rule, which denotes the same number because those definitions
//! reproduce Lean's. A proof that never reduces the term checks and passes
//! the kernel recheck. One that reduces it is a closed evaluation as large
//! as the number: the BendTT kernel evaluates strictly within its step
//! budget and refuses it (`LLV7021`), even where Bend's lazy checker peels
//! only a few successors.

use super::syntax::{BTerm, Name};

/// The radix of the Horner form: its square is the first number with no
/// literal spelling, so every digit and the radix itself are literals.
const RADIX: u64 = 65_536;

/// The digits of a decimal numeral in base 65536, most significant first,
/// or `None` when it is not a decimal numeral.
fn digits(decimal: &str) -> Option<Vec<u64>> {
    if decimal.is_empty() || !decimal.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let mut number: Vec<u64> = decimal.bytes().map(|byte| u64::from(byte - b'0')).collect();
    let mut out = Vec::new();
    while number.iter().any(|digit| *digit != 0) {
        // Long division of the decimal digits by the radix.
        let mut quotient = Vec::with_capacity(number.len());
        let mut remainder = 0;
        for digit in &number {
            let current = remainder * 10 + digit;
            if !quotient.is_empty() || current >= RADIX {
                quotient.push(current / RADIX);
            }
            remainder = current % RADIX;
        }
        out.push(remainder);
        number = quotient;
    }
    if out.is_empty() {
        out.push(0);
    }
    out.reverse();
    Some(out)
}

/// The Bend literal of a decimal numeral Bend spells, or `None` when it
/// is larger than `4294967295` or not a decimal numeral.
#[must_use]
pub fn literal(decimal: &str) -> Option<BTerm> {
    match digits(decimal)?.as_slice() {
        [only] => Some(BTerm::Nat(only.to_string())),
        [high, low] => Some(BTerm::Nat((high * RADIX + low).to_string())),
        _ => None,
    }
}

/// The Bend term of a decimal numeral: the literal when Bend spells it,
/// else its Horner form over the prelude's `Lean.Nat.add` and
/// `Lean.Nat.mul`, whose names `prelude` supplies, or `None` when
/// `decimal` is not a decimal numeral. `prelude` is called only for a
/// Horner form, so a module whose numerals are all literals does not
/// import the prelude for them.
pub fn term(decimal: &str, mut prelude: impl FnMut(&str) -> Name) -> Option<BTerm> {
    if let Some(literal) = literal(decimal) {
        return Some(literal);
    }
    let (add, mul) = (prelude("Lean.Nat.add"), prelude("Lean.Nat.mul"));
    let mut digits = digits(decimal)?.into_iter();
    let mut horner = BTerm::Nat(digits.next()?.to_string());
    for digit in digits {
        horner = BTerm::Call(mul.clone(), vec![horner, BTerm::Nat(RADIX.to_string())]);
        if digit != 0 {
            horner = BTerm::Call(add.clone(), vec![horner, BTerm::Nat(digit.to_string())]);
        }
    }
    Some(horner)
}

/// The decimal numeral one less than a positive one, or `None` when
/// `decimal` is zero or not a decimal numeral: the magnitude a negative
/// integer's `negSucc` carries.
#[must_use]
pub fn predecessor(decimal: &str) -> Option<String> {
    if decimal.is_empty() || !decimal.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let mut bytes = decimal.trim_start_matches('0').as_bytes().to_vec();
    if bytes.is_empty() {
        return None;
    }
    for byte in bytes.iter_mut().rev() {
        if *byte == b'0' {
            *byte = b'9';
        } else {
            *byte -= 1;
            break;
        }
    }
    let text = String::from_utf8(bytes).ok()?;
    let trimmed = text.trim_start_matches('0');
    Some(if trimmed.is_empty() { "0" } else { trimmed }.to_owned())
}

#[cfg(test)]
mod tests {
    use super::{literal, predecessor, term};
    use crate::backend::bend::syntax::{BTerm, Name};

    fn show(term: &BTerm) -> String {
        match term {
            BTerm::Nat(value) => value.clone(),
            BTerm::Call(head, args) => format!(
                "{}({})",
                head.text,
                args.iter().map(show).collect::<Vec<_>>().join(", ")
            ),
            other => panic!("not a numeral term: {other:?}"),
        }
    }

    /// The boundary is exact: the largest literal stays one, and the next
    /// number is the radix squared, with zero digits left out of the sum.
    #[test]
    fn literals_end_where_bend_spelling_ends() {
        let prelude = |name: &str| Name::synthetic(name.trim_start_matches("Lean.Nat."));
        let at = |decimal: &str| show(&term(decimal, prelude).expect("a numeral"));
        assert_eq!(at("0"), "0");
        assert_eq!(at("65536"), "65536");
        assert_eq!(at("4294967295"), "4294967295");
        assert_eq!(at("4294967296"), "mul(mul(1, 65536), 65536)");
        assert_eq!(at("4294967297"), "add(mul(mul(1, 65536), 65536), 1)");
        // 2^64, past `u64`: four zero digits under a one.
        assert_eq!(
            at("18446744073709551616"),
            "mul(mul(mul(mul(1, 65536), 65536), 65536), 65536)"
        );
        // 2^64 - 1: every digit 65535.
        assert_eq!(
            at("18446744073709551615"),
            "add(mul(add(mul(add(mul(65535, 65536), 65535), 65536), 65535), 65536), 65535)"
        );
        assert!(term("12a", prelude).is_none());
        assert!(term("", prelude).is_none());
        // A literal never asks for the prelude.
        assert!(term("4294967295", |_: &str| -> Name { panic!("no prelude") }).is_some());
        assert!(literal("4294967296").is_none());
    }

    #[test]
    fn predecessors_borrow_across_digits() {
        assert_eq!(predecessor("1").as_deref(), Some("0"));
        assert_eq!(predecessor("1000").as_deref(), Some("999"));
        assert_eq!(
            predecessor("18446744073709551616").as_deref(),
            Some("18446744073709551615")
        );
        assert_eq!(predecessor("0"), None);
        assert_eq!(predecessor("-3"), None);
    }
}
