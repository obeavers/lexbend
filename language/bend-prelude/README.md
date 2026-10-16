# LexLean Bend prelude

`LexLean.bend` is the one Bend 2 module the Bend backend imports besides
`Base`. It holds the Lean 4 denotations a LexLean source may name, under
their Lean names with a `Lean.` prefix (`Lean.Nat.add`, `Lean.Int`,
`Lean.List.Mem`), the lemmas those denotations need, and the types of the
assumption premises. `registry.toml` is the closed map from a
(Lean name, LSE signature) pair to the Bend name the backend emits; a name
absent from it has no Bend denotation.

`bend LexLean.bend --check-only` must print `ALL PROOFS CHECK`. Every lemma
is a `law` with its paired `def`; nothing is left open, `@unsafe`, or foreign.

## The binder contract

The Bend def of a registry row takes exactly the row's LSE binders, in order,
and the backend passes every argument, implicit ones included.

- An `explicit` binder is an ordinary parameter; an `implicit` or `instance`
  binder is erased (`-x`).
- A `(sort (type 0))` or `(sort (type u))` binder is `-A: Data` where the def
  builds lists of `A`, and `-A: Type` elsewhere; `Type` accepts every `Data`
  type, so the call is the same either way. A `(sort prop)` binder is
  `-P: Type`, and a `(sort prop)` result is a def returning `Type`.
- A row with a `live` list names implicit binders the proof must case on.
  Bend refuses to match an erased variable in live code, so those binders are
  ordinary parameters and the backend must pass live terms for them.
- `prefix` lists Bend arguments inserted before the row's own, as `["Nat"]`
  for the `List Nat` specialisation of the polymorphic `List.append`.
- `origin = "prelude"` names are qualified by the import alias (`L.Lean.Nat.add`,
  `L.ofNat{3n}`); `origin = "base"` names (`Nat`, `Bool`, `List`, `0n`,
  `True{}`, `False{}`) are not.

Lean `List A` is `List<&2, A>` and Lean `Prod A B` is `Lean.Prod(A, B)`, the
pair type at quantity `&2`, so both are as reusable as Lean values are. The
`[core]` table gives the exact spelling of `Eq`, `And`, `Or`, `Not`, `Iff` and
`Exists`; the `[literal]` table gives Nat and Int literals. A Nat literal above
`4294967295n` has no Bend literal spelling.

## The fidelity rule

Each computational def reproduces the defining equations of Lean 4 Init,
including which argument it recurses on, so a goal Lean closes by `rfl` or
`decide` closes here by `{==}`. `Nat.add n 0 = n` is definitional and
`Nat.add 0 n = n` is not (it is the law `Lean.Nat.zero_add`); `Nat.mul` and
`Nat.sub` recurse on their second argument; `Int` is `ofNat`/`negSucc` with
`add`, `mul`, `neg`, `sub`, `sign`, `ediv` and `emod` written through
`subNatNat` and `negOfNat` exactly as Lean writes them. `Nat.le` and `Int.le`
are the Bool equations `Nat.ble a b = true` and `NonNeg (b - a)`, so closed
instances are decided by `{==}`.

## Assumption premises

Classical principles are not defs, because live code may not call an
unproved claim. `Lean.Assume.excluded_middle()`, `choice()`, `propext()` and
`funext()` are their types, and each `[[assumption]]` row names the Lean
constants it stands for. A statement that relies on one takes it as a
template premise, `for ~em: L.Lean.Assume.excluded_middle()`, so the
assumption is part of the statement's type and every caller must supply or
inherit it.
