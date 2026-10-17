Feature: bend-backend

  Prose-free Bend 2 generation for language 2.0 (§18.10) and language 2.2 (§18.11).

  @BN-01 @build
  Scenario: Every language-1.0 document module renders one byte-deterministic Bend file from the same linked IR, beside its Lean and LaTeX, with the exact import structure.
    Given the language-2.0 copy of the nat-add-zero example rendered twice without Bend or publication
    When the build files are compared and the generated `Main` Bend is read
    Then both builds are byte-identical and hold `Main.lean`, `Main.tex`, `Main.bend`, and the prelude
    And the `Main` Bend equals the §18.10 literal bytes, while a language-1.0 build has no Bend file
    And the peano-arithmetic `Main` imports Base, the prelude as `L`, then its four imported modules in sorted order by relative path

  @BN-02 @build
  Scenario: Every external constant lowers only through the prelude registry with every signature binder, and an unregistered constant or undetermined implicit argument is a hard error.
    Given the language-2.0 list-induction example and the language-1.0 builtin glossary closure
    When the generated Bend is read and every Lean denotation of the closure is looked up in the registry
    Then each list constant receives its implicit element type and every denotation has a registry row
    And a project whose glossary denotes an unregistered Lean constant fails its build with LLB6008
    And an implicit binder that nothing determines is refused with LLB6008 rather than guessed

  @BN-03 @build
  Scenario: Generated Bend contains no comment, unsafe or foreign definition, hole, unfilled law, hub import, device call, or IO value.
    Given the generated Bend of every module of the four language-2.0 examples
    When each text is searched for the forbidden spellings
    Then none contains `#`, `@unsafe`, `?`, a foreign or hub import, `!(`, or `IO`
    And every `law` has its proof definition

  @BN-04 @build
  Scenario: Theorems lower to laws with proof definitions and every proof step to an explicit Bend term, with case analysis and induction as auxiliary definitions emitted first.
    Given the language-2.0 propositional-logic and peano-arithmetic examples and the shared proof corpus moved to language 2.0
    When their generated Bend is read and the corpus is checked by the pinned Bend
    Then a case split is an auxiliary definition preceding its law, the induction hypothesis is the auxiliary's recursive call, a rewrite is `%`, and a calculation is an `Equal.trans` chain
    And every module of the corpus, whose forms include `simplify` at the goal and at a hypothesis, checks

  @BN-05 @build
  Scenario: No generated declaration takes a template, a binder is reusable only at a Data type, and a proof that uses a function-typed hypothesis twice on one branch is refused by the pinned Bend.
    Given the four language-2.0 examples and the language-1.0 propositional-logic module moved to language 2.0
    When their generated Bend is read and the moved module is checked by the pinned Bend
    Then no generated text contains a template mark `~`, and every `+` binder has a Data type
    And the moved module, whose `de_morgan` applies its negated hypothesis in both components, is refused because `llh0` is consumed more than once

  @BN-06 @build
  Scenario: The shipped prelude reproduces the definitional equations of every registered Lean constant and checks under the pinned Bend.
    Given the shipped prelude and its registry
    When every registry row is resolved and the prelude and two fidelity probes are checked by the pinned Bend
    Then every registered definition, type, and law is defined, every law is proved, and the prelude imports only Base
    And the prelude checks, `n + 0 = n` closes by `{==}`, and `0 + n = n` does not, exactly as in Lean

  @BN-07 @build
  Scenario: A theorem that uses or cites an assumption takes it as a leading premise and passes it to every theorem it cites, and a definition that uses one is a hard error.
    Given the language-2.0 peano-arithmetic example with a theorem citing `even-or-not` appended
    When the generated `Main` Bend is read and checked by the pinned Bend
    Then `even_or_not` and the citing theorem both lead with the premise `ll_excluded_middle`
    And the citing theorem passes the premise on as its leading argument, no axiom is named, and the module checks

  @BN-08 @build
  Scenario: Every non-whitespace generated Bend token has exactly one coverage row and a source map mapping.
    Given every module of the four language-2.0 examples
    When its Bend coverage rows and source-map mappings are compared with the generated text
    Then the rows cover every non-whitespace byte exactly once, each row has one mapping, and the map and coverage use the version-2 schemas

  @BN-09 @build
  Scenario: The generated Bend of every language-1.0 example document module checks under the pinned Bend with every proof accepted.
    Given the four language-2.0 examples and a project whose theorem is false
    When every generated module is checked by the pinned Bend
    Then all eight example modules print exactly `ALL PROOFS CHECK`
    And the false theorem prints `SOME PROOFS FAIL`

  @BN-19 @build
  Scenario: A language-2.0 or 2.2 numeral above 4294967295 lowers to its base-65536 Horner form over the prelude's Lean.Nat.add and Lean.Nat.mul, and the pinned Bend accepts a proof that uses it without reducing it.
    Given a language-2.0 theorem and a language-2.2 module whose numerals include 4294967296 and 18446744073709551616 and the integer -18446744073709551616
    When they are built
    Then each numeral at or below 4294967295 is a Bend literal and each larger one is its Horner form over the prelude's Lean.Nat.add and Lean.Nat.mul
    And every generated module, including a theorem by reflexivity about a comparison with 2^64 that never reduces it, prints exactly `ALL PROOFS CHECK` under the pinned Bend

  @BN-10 @build
  Scenario: Every language-2.2 semantic module renders one byte-deterministic Bend file from the same linked IR, beside its Lean and LaTeX, importing Base, the prelude, the support modules it uses, and its imported modules, with every non-whitespace token covered and mapped.
    Given the four language-2.2 examples, the semantic example rendered twice
    When the build files are compared and every generated module, its imports, coverage, and mappings are read
    Then both builds are byte-identical and hold the module's `.bend`, `.lean`, and `.tex`
    And the models `Main` imports Base, the prelude as `L`, `S` and `R`, then its seven imported modules in sorted order by relative path
    And each build publishes exactly the support modules its modules import, and every covered Bend byte range is mapped

  @BN-11 @build
  Scenario: Language-2.2 type parameters lower to templates and function parameters are closure-converted, and a higher-order function passed as a value is a hard error.
    Given the language-1.2 higher-order example moved to language 2.2
    When its generated Bend is read and checked by the pinned Bend, and a definition passing `twiceOf` to a function parameter is added
    Then `mapList` takes its type parameters, its code, and its environment type as templates and its environment as data
    And a capturing lambda passes `offset` as its environment, a function reference passes `Unit{}`, and every module checks
    And the added definition fails its build with LLB6008 naming `twiceOf`

  @BN-12 @build
  Scenario: A language-2.2 mutual group lowers by inlining with every member's name kept, and a group that recurses simultaneously is a hard error.
    Given the language-2.2 recursion example and the language-1.2 recursion example moved to language 2.2
    When the generated `Main` Bend is read and the moved example is built
    Then `forestSize` precedes `roseSize` with `roseSize` inlined into it, and `isEven` holds `isOdd` inlined
    And the moved example fails its build with LLB6008 naming the group `SyntaxSize` and its three members

  @BN-13 @build
  Scenario: A language-2.2 well-founded definition lowers to proof-carrying fuel whose every recursive call carries its decrease evidence, and the pinned Bend refuses a call that consumes no fuel or whose evidence does not establish the decrease.
    Given the language-2.2 recursion example
    When its generated `Main` Bend is read, checked, and checked again with each of two planted defects
    Then `countdown.ll_go` takes fuel and a bound, its recursive call passes the predecessor fuel with `S.Sem.lt_fuel` over `countdown_decreases`, and the wrapper supplies `1n+number`
    And every module checks, while the call passing undiminished fuel and the call passing `S.Sem.lt_succ(number)` as evidence are each refused

  @BN-14 @build
  Scenario: Language-2.2 proofs lower to explicit Bend terms, including linear arithmetic, decide, congruence, and boolean reflection, and the pinned Bend refuses a reflection whose induction steps the wrong successor.
    Given the language-2.2 reflection and recursion examples
    When their generated Bend is read and the reflection module is checked, then checked with the forward induction stepping `ll_p + 2`
    Then the record reflection is `LA.sound` each way, the list reflection is a forward and a backward induction whose proposition proof is affine, and `decide` on `isEven 10` is `{==}`
    And the module checks, and the planted induction is refused

  @BN-15 @build
  Scenario: Every language-2.2 model cross-check restates its obligation against the Bend runtime's LexLeanModels and is proved by its discharging theorem or by evaluation, and a restatement that drifts is refused by the pinned Bend.
    Given the language-2.2 models example
    When its generated Bend is read and checked, then checked with the `FlowContract` invariant restated over `Within` and the `triageBias` shape changed to 4
    Then `FlowContract.invariant_sound` restates `LexLeanModels.Sound1` and is proved by `flow_capped_sound`, and the `triageBias` check decodes its values from its bytes with its shape
    And every module checks, and each planted restatement is refused

  @BN-16 @build
  Scenario: The language-2.2 support modules import only Base and the prelude and check under the pinned Bend, and every runtime registry row names a function, law, type, or constructor the runtime defines.
    Given the shipped `Semantic.bend`, `Runtime.bend`, and `LinArith.bend`, and the runtime registry
    When each module's imports are read, every registry row is resolved in the runtime, and each module is checked as a build publishes it
    Then each imports exactly `Base` and the prelude as `L`
    And every registry name is a definition, law, type, or constructor of the runtime, or one of Base's own types
    And each module checks under the pinned Bend

  @BN-17 @build
  Scenario: A language-2.2 reasoning declaration is a hard error naming the theorem it generates.
    Given the language-1.2 reasoning example moved to language 2.2
    When it is built
    Then the build fails with LLB6008 naming `Tick.apply_sound` as the theorem whose proof has no Bend lowering

  @BN-18 @build
  Scenario: The generated Bend of every language-2.2 example module checks and exports under the pinned Bend with every proof accepted.
    Given the four language-2.2 examples, the recursive-data, higher-order, and collections examples moved to language 2.2, and a reflection project with a false theorem
    When every generated module is checked and exported by the pinned Bend
    Then all twenty modules print exactly `ALL PROOFS CHECK` and export with no output
    And the false theorem prints `SOME PROOFS FAIL`

  @BN-20 @build
  Scenario: Language-2.2 equality of two orderings lowers to the Bend runtime's LexLeanRuntime.equal.Ordering, which is true exactly when both are the same ordering, as Lean's derived equality is.
    Given a language-2.2 module comparing orderings with `equal`, and a theorem by reflexivity for each of the nine pairs of orderings
    When it is built and its Bend is checked by the pinned Bend
    Then the comparison calls `LexLeanRuntime.equal.Ordering`
    And every generated module prints exactly `ALL PROOFS CHECK`, the three equal pairs `true` and the six others `false`
