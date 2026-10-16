Feature: bend-backend

  Prose-free Bend 2 generation for language 2.0 (§18.10).

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
