# LexLean runtime for Bend 2

`Runtime.bend` is LexLean's Lean 4 runtime library (namespaces
`LexLeanRuntime`, `LexLeanCollections`, `LexLeanModels`, `LexLeanReasoning`)
ported to Bend 2 for the language-2.2 Bend backend. `runtime-registry.toml`
maps every ported Lean constant to its Bend name and records every declaration
that has no Bend counterpart. This file states the representation, naming and
fidelity contract the backend relies on. `README.md` and `LexLean.bend` belong
to the language-2.0 identity and are not changed by the runtime.

`Runtime.bend` imports `Base` and `./LexLean.bend as L`, and reuses
`L.Lean.Int` and `L.Lean.Prod` with Base `Nat`, `Bool` and `List`. A generated
module imports it as `import ./Runtime.bend as R`; every registry `bend` name
is then written `R.<name>`. Checked with bend 2.0.37:

```
$ bend Runtime.bend --check-only
ALL PROOFS CHECK
Use --verdict for mathematical validity.
```

`bend Runtime.bend -o Runtime.bendtt` writes a kernel file with no `opaque`
entry. The file uses no `~` template parameter, no `@unsafe`, no `def f?`, no
foreign import and no `?` hole, and every `law` has its proof `def`.

## Representations

| Lean | Bend | Note |
| --- | --- | --- |
| `Nat` | `Nat` | Base unary Nat. |
| `Int` | `L.Lean.Int` | `ofNat{n}` / `negSucc{n}`, Lean's own constructors. |
| `Bool` | `Bool` | |
| `Option α` | `Maybe<&2, α>` | `none` = `None{}`, `some x` = `Some{x}`. |
| `Except ε α` | `Result<&2, &2, ε, α>` | `.error e` = `Fail{e}`, `.ok x` = `Done{x}`. |
| `Ordering` | `Cmp` | `LT{}` / `EQ{}` / `GT{}`. |
| `Prod α β` | `L.Lean.Prod(α, β)` | a pair `(a, b)`. |
| `List α` | `List<&2, α>` | |
| `Char` | `Char` | `Chr{code: U32}`. |
| `String` | `String` | the character list (`String.data`). |
| `ByteArray` | `Lean.ByteArray` | `Lean.ByteArray.mk{data: List<&2, Lean.UInt8>}`. |
| `UInt8`, `UInt16`, `UInt64` | `Lean.UInt8`, `Lean.UInt16`, `Lean.UInt64` | `Lean.T.mk{bits: Word(w)}`. |
| `UInt32` | `U32` | Base `U32{data: Word(32n)}`. |
| `Int8` .. `Int64` | `Lean.Int8` .. `Lean.Int64` | `Lean.T.mk{bits: Word(w)}`, two's complement. |
| `Prop` | `Type` | `True` is `Unit`, `True.intro` is `Unit{}`, `a ∧ b` is `a & b`. |
| `[Key κ]` | `LexLeanCollections.Key` | a closed Data code, see below. |

Each fixed-width type has exactly 2^w values: its carrier is a `Word(w)`
(least significant bit first), never a Nat. Literals are written with
`Lean.T.lit(n)` for a `U32` literal `n` (the value `n mod 2^w`), and
`Lean.UInt64.lit2(hi, lo)` / `Lean.Int64.lit2(hi, lo)` for
`hi * 2^32 + lo`. A negative literal `(-k : IntN)` is
`Lean.IntN.neg(Lean.IntN.lit(k))`, the term Lean elaborates.

`Lean.T.ofNat`, `Lean.T.toNat`, `Lean.T.ofInt`, `Lean.T.toInt` and
`Lean.IntN.toNatClampNeg` convert through Nat/Int with Lean's modular
semantics. Operations that stay inside a width (`add`, `sub`, `mul`, `neg`,
`div`, `mod`, `land`, `lor`, `xor`, `complement`, `shiftLeft`, `shiftRight`,
`beq`, `cmp`, `decLt`, `decLe`) run on the bits alone. Shifts take the amount
modulo the width, and right shift is arithmetic on signed types. Signed
`div`/`mod` truncate, as `Int.tdiv`/`Int.tmod` do (`-128 / -1 = -128` on
`Int8`). Division by zero yields 0, and modulo by zero yields the dividend.

## Naming

- Every Lean declaration `N.f` becomes the Bend def `N.f`. Lean core
  operations become `Lean.T.<op>` (for example `Lean.UInt8.add`,
  `Lean.Int.tdiv`, `Lean.String.splitOn`).
- A class-polymorphic function is monomorphized into one def per instance,
  `<function>.<Instance>`: `LexLeanRuntime.checkedAdd.UInt8`,
  `LexLeanRuntime.equal.ByteArray`, `LexLeanRuntime.length.String`.
  `LexLeanRuntime.checkedConvert.<Source>.<Target>` has all 72 pairs over
  `Int` and the eight fixed-width types as source, and the eight fixed-width
  types as target.
- Class methods are `<Class>.<method>.<Instance>`, for example
  `LexLeanRuntime.Fixed.minimum.Int8` and
  `LexLeanRuntime.Quotient.quotient.Int`. A class has no Bend type; its
  instances exist only as these defs.
- Binders follow Lean's explicit binders in order. Implicit type binders that
  a Bend def needs are erased leading parameters (`-A: Data`). Instance
  binders disappear into the monomorphized name.
- Every constructor declared here is qualified with its type name, because
  Bend constructor names are module-global: `Lean.ByteArray.mk`,
  `LexLeanCollections.Key.Prod`, `LexLeanRuntime.Utf8.Step.emit`,
  `LexLeanReasoning.Star.tail.mk`.
- Helper defs with no Lean counterpart (`LexLeanRuntime.W.*`, `.fin`, `.go`
  and similar suffixes) are internal to `Runtime.bend` and are not listed in
  the registry.

## Key instances

The thirteen `Key` instances (`Nat`, `Int`, `Bool`, `Int8`..`Int64`,
`UInt8`..`UInt64`, `String`, `Prod`) form a closed universe, so the class is
defunctionalized into the Data code `LexLeanCollections.Key`:
`Key.Nat{}` .. `Key.String{}` and `Key.Prod{fst, snd}`.
`LexLeanCollections.Key.carrier(k)` is the carrier type of a code, and
`LexLeanCollections.Key.compare(k, a, b)` is the instance's `compare`, first
order. Each collection function has a generic def `<f>.Key(k, ...)` and the
monomorphized wrappers `<f>.Nat` .. `<f>.String`. `<f>.Prod(ka, kb, ...)`
takes the two component codes first, so a nested key such as
`Prod Int (Prod String Nat)` is
`<f>.Prod(Key.Int{}, Key.Prod{Key.String{}, Key.Nat{}}, ...)`.

## Conditionals

The backend lowers Lean `if c then a else b` (with `c : Bool`) to Base
`Bool.pick(T, c, a, b)`. `LexLeanReasoning.guarded`, `guardedRank` and
`checked` are stated over `Bool.pick`, so they apply to exactly the terms
that lowering produces.

## Laws

Fourteen Lean theorems are ported, each as a `law` with a proof `def` of the
same name: `reachesStart`, `guarded`, `guardedRank`, `checked`, `allAppend`,
`allSingle`, `allHead`, `allTail`, `lengthSnoc`, `searchStart`, `peakBound`,
`noneSome`, `zeroLe` and `bltSucc`. None needs a classical axiom.
`LexLeanReasoning.All` is a recursive Type def (`Unit` on `[]`, `p(h) & All(t)`
on `h :: t`). `LexLeanReasoning.Star` is an indexed type whose constructors
are produced by the defs `Star.refl` and `Star.tail`.

## Fidelity

Each def computes, on every input, the value of its Lean definition, so a
Lean `rfl`/`decide` fact about closed runtime values closes in Bend by
`{==}`. The fixed-width and decimal algorithms are not Lean's code
transcribed; they are bit-level algorithms that are value-equal to it.
Closed values were compared with Lean 4.32.1 `#eval` on 7625 generated cases
covering every ported function family, including width boundaries, signed
minimums, UTF-8 edge sequences and collection orders. All 7625 close by
`{==}`.

Checker limits that do not change any value:

- The checker evaluates Nat in unary. A closed Nat past roughly 30000
  overflows its stack, and many medium Nats in one file overflow it
  cumulatively. A fixed-width computation therefore never passes through
  Nat. Functions whose Lean type takes `Nat` or `Int` (`toNat`, `ofInt`,
  `LexLeanRuntime.Fixed.minimum.Int64`, `checkedFromInt.UInt64` on large
  inputs, and similar) are correct definitions, but they can be evaluated by
  the checker only on small magnitudes.
- At run time Bend's Nat is a 48-bit machine value. A Nat or Int result
  beyond 2^48 (for example `Lean.UInt64.toNat` of a large value) exceeds the
  runtime representation. The Word-based types are unaffected.

## Not expressible here

These declarations take or use a function argument more than once. A Bend
function value is affine (`+f` requires Data, and functions are Type), so
the only way to share one is a `~` template, which this file does not use.
Every call site still compiles: the backend lifts the step function to a
named code definition over an environment of its captured Data and passes
it as a template to Semantic.bend's folds and loops.

| Lean | Bend error |
| --- | --- |
| `LexLeanCollections.listFold`, `setFold`, `mapFold` | `step (consumed more than once)` |
| `LexLeanCollections.iterate`, `iterateUntil` | `step (consumed more than once)` |
| `LexLeanReasoning.starPreserves` | `h (consumed more than once)`; in Lean's binder order the recursion is also refused, `expected : a decreasing self-call` |
| `LexLeanReasoning.foldInvariant`, `foldSnoc`, `allFold`, `capAll`, `capBound`, `freshAll` | the statement names `listFold` |
| `LexLeanReasoning.iterateUntilInvariant`, `iterateUntilSimulate`, `iterateUntilCount`, `iterateUntilGrowth`, `iterateUntilStops`, `iterateUntilBound` | the statement names `iterateUntil` |

With `+step`, the error is `expected : Data / observed : Type` ("`+step` can be
used many times, so its type must be Data"). Wrapping the function in a Data
constructor fails the same way.

`Reasoning.bend` states and proves the laws of the last three rows with
templates, once each, over Semantic.bend's forms. The kernel checks a
template definition against a model that gives every template its default
value, so each law is proved for every instantiation, not only the ones a
build happens to make. That forces three rules on the laws and on the
theorems that instantiate them:

- A template hypothesis must hold in the default model, where a template
  predicate is `Unit`. It may conclude a template predicate, never an
  equation on Nat or a successor. The count, growth, and stopping laws are
  therefore one fuel law plus first-order arithmetic glue, and the bound
  law is the invariant law.
- Every template argument at an instantiation is a named definition,
  partially applied to template arguments. The kernel types a template's
  type only through named heads, so a lambda whose type applies another
  lambda template is refused ("no known head type").
- Templates are closed. The checker allows a template to capture a
  run-time local; the kernel refuses it.
- A fold or loop invariant reads the captured environment `k` and the
  step's own environment `e`. The hypothesis is proved for every `e`, so an
  invariant that read a parameter only through `k` would state a value the
  step, which reads `e`, need not use.

## Lean semantics to watch

- Lean's `Char` is a Unicode scalar value. Base `Char` admits every `U32`
  code, including surrogates and codes above U+10FFFF. The runtime applies
  Lean's formulas to such codes unchanged; Lean has no such value to compare
  with. `utf8Encode` on a non-scalar `Char` is therefore outside the tested
  domain.
- `utf8Decode` follows `String.fromUTF8?`: it rejects overlong forms,
  surrogates, codes above U+10FFFF and truncated sequences (the Table 3-7
  ranges of the Unicode standard). This was matched against Lean on the test
  sequences; it is not proved equal to Lean's validator.
- `compareBytes` is Lean's lexicographic `compare` on `List UInt8`, where a
  proper prefix is less.
- `Decimal.parse` accepts only the canonical decimal form: Lean's
  `String.toInt?` also accepts `_` separators, and the round-trip check in
  the Lean source rejects those.
- `String.splitOn` is Lean 4.32.1's leftmost, non-overlapping split.
