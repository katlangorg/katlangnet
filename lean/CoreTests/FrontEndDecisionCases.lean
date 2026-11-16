import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

Front-end decision differential: the Lean front-end specification functions of `lean/KatLang.lean`
against the decisions the C# front end made on every program of the two differential corpora
(tests/KatLang.Tests/SemanticExplorerCorpus.cs and
tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs). Lean has no front end: the other generated
corpora evaluate a tree C# already elaborated, so they take these decisions as INPUT. Here each
decision is an expectation, and a failing `#guard` is a Lean/C# divergence on that decision.

What is compared (generator: tests/KatLang.Tests/FrontEndDecisionCorpus.cs):
- `selectOwnedDeclaration` — C#'s owned-binding fact for the name in its scope (parameter or
  property, with the deciding level's position in the chain; the fact parameter detection's rewrite
  and `ElaboratedScopeLookup.SelectOwnedDeclaration` read);
- `elaboratesToParameter` — the node parameter detection left for the occurrence (`Expr.Param` or
  `Expr.Resolve`), which the complete pipeline's tree was checked to keep for every written name
  it still holds;
- `elaborateOpenHead` — the node detection left as the head of each static `open` target, over the
  chain of CALLABLE bindings (the never-called program root's inferred signature omitted);
- `familyLiftingSignature?` — `ImplicitArgumentResolver.DeriveFamilyLiftingSignature` on each clause
  family's heads;
- `liftingSlotRole` — `FormulaLiftingRoles.SlotRole` on every callee kind, positions 0..4,
  with and without a known position. This one is the whole table, not per occurrence: which kind a
  written call's callee has is implicit-argument resolution's private classification and is not
  recoverable from the elaborated tree without re-implementing it.

Each chain is rebuilt from the DETECTED tree's nesting (a body's stored parameter patterns and
property names, a clause body's head binders), innermost level first, ending in the prelude's
property level. `forwarded` lists the parameters automatic forwarding added afterwards (the resolved
signature minus the detected one); the owner walk never reads it. Identical guards of one program
are emitted once, with their multiplicity, and programs whose levels and guards are identical share
one block that names every one of them (634 blocks): nothing is sampled.

Partition:
- corpus programs: 3145
- skipped, the parser rejected the source: 42
- skipped, an unresolved `load` directive (module elaboration is async-only): 0
- skipped, parameter inference refused as circular: 0
- excluded by exact id, a reviewed Lean/C# disagreement (class and witness in
  `FrontEndDecisionCorpus.ReviewedDriftById`): 0
- guarded programs: 3103 (7584 scope levels, 49 with a forwarded parameter)
- name occurrences: 8259 (2632 parameters, 539 dot-edge fallback names)
- of those names and heads, the same node in the complete pipeline's tree (matched by source span):
  7296; with no source span to match by (names the parser synthesized, such as the plumbing of an
  assignment deconstruction): 1046; with no node of that span and name left there: 0
- open heads: 83 (4 parameter-owned)
- clause families: 58 (12 with no lifting signature); skipped, a head with no Lean spelling: 1

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_FRONT_END_DECISIONS = "1"
  dotnet test .\KatLang.slnx --filter FrontEndDecisionLeanArtifact
-/

namespace FrontEndDecisionCases
open KatLang

/-- The outermost level of every chain: the property names of C#'s semantic prelude, which owns no parameter. -/
def prelude : List OwnerLevel :=
  [{ parameters := [], properties := ["if", "while", "repeat", "atoms", "range", "filter", "map", "order", "orderDesc", "count", "contains", "first", "last", "distinct", "take", "skip", "min", "max", "sum", "avg", "reduce", "tick", "load", "Math", "pi", "exp", "abs", "ceil", "floor", "round", "sign", "sqrt", "ln", "lg", "sin", "asin", "cos", "acos", "tan", "atan", "atan2", "pow", "log", "random", "randomInt"] }]

/-- Every member of Lean's own prelude is a property of that level, so a name the Lean evaluator would find
    there is one the chains below end in as well. -/
def preludeMemberNames : List Ident :=
  match preludeAlg with
  | .mk _ _ _ properties _ _ => properties.map (·.name)
  | _ => []
#guard !preludeMemberNames.isEmpty
#guard preludeMemberNames.all (fun name => prelude.any (fun level => level.properties.contains name))

/-- What `elaborateOpenHead` produced, as comparable data (`Expr` has no `BEq`): whether the head is a
    parameter read, and its name. -/
def openHead? : Expr -> Option (Bool × Ident)
  | .param name => some (true, name)
  | .resolve name => some (false, name)
  | _ => none

/-- One clause of a family, by its head. `familyLiftingSignature?` reads the heads only, so every clause
    takes the same empty body. -/
def clause (head : Pattern) : CondBranch := ⟨head, alg [] [] [] []⟩

-- liftingSlotRole: every callee kind, supplied positions 0..4, position known (true) and after a spread (false).
#guard (List.range 5).map (fun position => liftingSlotRole .dynamic position true) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole .dynamic position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole .user position true) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole .user position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole .family position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole .family position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole .strictValue position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole .strictValue position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .ifBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .ifBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .whileBuiltin) position true) == [.callable, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .whileBuiltin) position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .repeatBuiltin) position true) == [.callable, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .repeatBuiltin) position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .atomsBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .atomsBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .rangeBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .rangeBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .filterBuiltin) position true) == [.value, .callable, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .filterBuiltin) position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .mapBuiltin) position true) == [.value, .callable, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .mapBuiltin) position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .orderBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .orderBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .orderDescBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .orderDescBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .countBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .countBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .containsBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .containsBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .firstBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .firstBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .lastBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .lastBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .distinctBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .distinctBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .takeBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .takeBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .skipBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .skipBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .minBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .minBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .maxBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .maxBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .sumBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .sumBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .avgBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .avgBuiltin) position false) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .reduceBuiltin) position true) == [.value, .callable, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .reduceBuiltin) position false) == [.callable, .callable, .callable, .callable, .callable]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .tickBuiltin) position true) == [.value, .value, .value, .value, .value]
#guard (List.range 5).map (fun position => liftingSlotRole (.builtin .tickBuiltin) position false) == [.value, .value, .value, .value, .value]
-- 26 callee kinds, 260 roles.

-- explorer/root__e: ()
-- the same levels and decisions, 307 more:
--   explorer/root__n0, explorer/root__n1, explorer/root__bt, explorer/root__bf, explorer/root__pbt
--   explorer/root__pbt_e, explorer/root__pbt_1, explorer/root__lbt, explorer/root__lbt_bf, explorer/root__lpbt_1
--   explorer/root__p1, explorer/root__p12, explorer/root__p123, explorer/root__pee, explorer/root__pe1
--   explorer/root__p1e, explorer/root__p12_3, explorer/root__p12_34, explorer/root__pe_12, explorer/root__ppe1_2
--   explorer/root__p12_e, explorer/root__ppe, explorer/root__pp1, explorer/root__ppp12, explorer/root__le
--   explorer/root__l7, explorer/root__l12, explorer/root__l12_3, explorer/root__lle, explorer/root__l_e
--   explorer/root__l_p12, explorer/root__p_l12, explorer/root__pl1, explorer/seqWrapPair__e
--   explorer/seqWrapPair__n0, explorer/seqWrapPair__n1, explorer/seqWrapPair__bt, explorer/seqWrapPair__bf
--   explorer/seqWrapPair__pbt, explorer/seqWrapPair__pbt_e, explorer/seqWrapPair__pbt_1, explorer/seqWrapPair__lbt
--   explorer/seqWrapPair__lbt_bf, explorer/seqWrapPair__lpbt_1, explorer/seqWrapPair__p1
--   explorer/seqWrapPair__p12, explorer/seqWrapPair__p123, explorer/seqWrapPair__pee, explorer/seqWrapPair__pe1
--   explorer/seqWrapPair__p1e, explorer/seqWrapPair__p12_3, explorer/seqWrapPair__p12_34
--   explorer/seqWrapPair__pe_12, explorer/seqWrapPair__ppe1_2, explorer/seqWrapPair__p12_e
--   explorer/seqWrapPair__ppe, explorer/seqWrapPair__pp1, explorer/seqWrapPair__ppp12, explorer/seqWrapPair__le
--   explorer/seqWrapPair__l7, explorer/seqWrapPair__l12, explorer/seqWrapPair__l12_3, explorer/seqWrapPair__lle
--   explorer/seqWrapPair__l_e, explorer/seqWrapPair__l_p12, explorer/seqWrapPair__p_l12, explorer/seqWrapPair__pl1
--   explorer/seqWrapSolo__e, explorer/seqWrapSolo__n0, explorer/seqWrapSolo__n1, explorer/seqWrapSolo__bt
--   explorer/seqWrapSolo__bf, explorer/seqWrapSolo__pbt, explorer/seqWrapSolo__pbt_e, explorer/seqWrapSolo__pbt_1
--   explorer/seqWrapSolo__lbt, explorer/seqWrapSolo__lbt_bf, explorer/seqWrapSolo__lpbt_1
--   explorer/seqWrapSolo__p1, explorer/seqWrapSolo__p12, explorer/seqWrapSolo__p123, explorer/seqWrapSolo__pee
--   explorer/seqWrapSolo__pe1, explorer/seqWrapSolo__p1e, explorer/seqWrapSolo__p12_3
--   explorer/seqWrapSolo__p12_34, explorer/seqWrapSolo__pe_12, explorer/seqWrapSolo__ppe1_2
--   explorer/seqWrapSolo__p12_e, explorer/seqWrapSolo__ppe, explorer/seqWrapSolo__pp1, explorer/seqWrapSolo__ppp12
--   explorer/seqWrapSolo__le, explorer/seqWrapSolo__l7, explorer/seqWrapSolo__l12, explorer/seqWrapSolo__l12_3
--   explorer/seqWrapSolo__lle, explorer/seqWrapSolo__l_e, explorer/seqWrapSolo__l_p12, explorer/seqWrapSolo__p_l12
--   explorer/seqWrapSolo__pl1, explorer/spreadRoot__e, explorer/spreadRoot__n0, explorer/spreadRoot__n1
--   explorer/spreadRoot__bt, explorer/spreadRoot__bf, explorer/spreadRoot__pbt, explorer/spreadRoot__pbt_e
--   explorer/spreadRoot__pbt_1, explorer/spreadRoot__lbt, explorer/spreadRoot__lbt_bf, explorer/spreadRoot__lpbt_1
--   explorer/spreadRoot__p1, explorer/spreadRoot__p12, explorer/spreadRoot__p123, explorer/spreadRoot__pee
--   explorer/spreadRoot__pe1, explorer/spreadRoot__p1e, explorer/spreadRoot__p12_3, explorer/spreadRoot__p12_34
--   explorer/spreadRoot__pe_12, explorer/spreadRoot__ppe1_2, explorer/spreadRoot__p12_e, explorer/spreadRoot__ppe
--   explorer/spreadRoot__pp1, explorer/spreadRoot__ppp12, explorer/spreadRoot__le, explorer/spreadRoot__l7
--   explorer/spreadRoot__l12, explorer/spreadRoot__l12_3, explorer/spreadRoot__lle, explorer/spreadRoot__l_e
--   explorer/spreadRoot__l_p12, explorer/spreadRoot__p_l12, explorer/spreadRoot__pl1, explorer/spreadInSeq__e
--   explorer/spreadInSeq__n0, explorer/spreadInSeq__n1, explorer/spreadInSeq__bt, explorer/spreadInSeq__bf
--   explorer/spreadInSeq__pbt, explorer/spreadInSeq__pbt_e, explorer/spreadInSeq__pbt_1, explorer/spreadInSeq__lbt
--   explorer/spreadInSeq__lbt_bf, explorer/spreadInSeq__lpbt_1, explorer/spreadInSeq__p1
--   explorer/spreadInSeq__p12, explorer/spreadInSeq__p123, explorer/spreadInSeq__pee, explorer/spreadInSeq__pe1
--   explorer/spreadInSeq__p1e, explorer/spreadInSeq__p12_3, explorer/spreadInSeq__p12_34
--   explorer/spreadInSeq__pe_12, explorer/spreadInSeq__ppe1_2, explorer/spreadInSeq__p12_e
--   explorer/spreadInSeq__ppe, explorer/spreadInSeq__pp1, explorer/spreadInSeq__ppp12, explorer/spreadInSeq__le
--   explorer/spreadInSeq__l7, explorer/spreadInSeq__l12, explorer/spreadInSeq__l12_3, explorer/spreadInSeq__lle
--   explorer/spreadInSeq__l_e, explorer/spreadInSeq__l_p12, explorer/spreadInSeq__p_l12, explorer/spreadInSeq__pl1
--   explorer/spreadRootStacked__e, explorer/spreadRootStacked__n0, explorer/spreadRootStacked__n1
--   explorer/spreadRootStacked__bt, explorer/spreadRootStacked__bf, explorer/spreadRootStacked__pbt
--   explorer/spreadRootStacked__pbt_e, explorer/spreadRootStacked__pbt_1, explorer/spreadRootStacked__lbt
--   explorer/spreadRootStacked__lbt_bf, explorer/spreadRootStacked__lpbt_1, explorer/spreadRootStacked__p1
--   explorer/spreadRootStacked__p12, explorer/spreadRootStacked__p123, explorer/spreadRootStacked__pee
--   explorer/spreadRootStacked__pe1, explorer/spreadRootStacked__p1e, explorer/spreadRootStacked__p12_3
--   explorer/spreadRootStacked__p12_34, explorer/spreadRootStacked__pe_12, explorer/spreadRootStacked__ppe1_2
--   explorer/spreadRootStacked__p12_e, explorer/spreadRootStacked__ppe, explorer/spreadRootStacked__pp1
--   explorer/spreadRootStacked__ppp12, explorer/spreadRootStacked__le, explorer/spreadRootStacked__l7
--   explorer/spreadRootStacked__l12, explorer/spreadRootStacked__l12_3, explorer/spreadRootStacked__lle
--   explorer/spreadRootStacked__l_e, explorer/spreadRootStacked__l_p12, explorer/spreadRootStacked__p_l12
--   explorer/spreadRootStacked__pl1, explorer/special__emptyOpGreater, explorer/special__emptyOpPlus
--   explorer/special__emptyOpPlusRight, explorer/special__emptyOpDivRight, explorer/special__emptyOpAnd
--   explorer/special__emptyOpString, explorer/special__emptyOpBoth, explorer/special__emptyUnaryMinus
--   explorer/special__emptyUnaryNot, explorer/special__emptyEqEmpty, explorer/special__emptyEqNestedEmpty
--   explorer/special__emptyNeNestedEmpty, explorer/special__rootEmptySlots, explorer/special__seqOfSpreadEmpty
--   explorer/special__listIndexSelectedKindEqFalse, explorer/special__spreadEmptyBetween
--   explorer/special__divZero, explorer/special__negativeResult, explorer/special__strEq
--   explorer/special__chainAllTrue, explorer/special__chainMixed, explorer/special__chainFalseMiddle
--   explorer/special__chainFalseLast, explorer/special__chainEqOnly, explorer/special__chainNeAdjacent
--   explorer/special__chainNeAdjacentFalse, explorer/special__chainEqThenLt, explorer/special__chainBoolEqMixed
--   explorer/special__chainSeqEq, explorer/special__chainStrEq, explorer/special__chainParenFirst
--   explorer/special__chainParenRight, explorer/special__chainParenBoth, explorer/special__chainUnderNot
--   explorer/special__chainUnderAnd, explorer/special__chainArithmeticOperands
--   explorer/special__chainInvalidLater, explorer/special__chainErrorFirstOperand
--   explorer/special__chainErrorAfterFalse, explorer/special__chainLtThenEq, explorer/special__chainLtThenGt
--   explorer/special__chainNeThenLt, explorer/special__chainFalseFirstThenEqFalse
--   explorer/special__chainGroupedNotOperand, explorer/special__chainParenLeftUnderOrdering
--   explorer/special__chainNegatedBasePower, explorer/special__chainNegatedPowerOperand
--   explorer/special__chainGroupedNegatedBasePowerOperand, explorer/special__chainArithmeticTiers
--   explorer/special__chainMiddleOperandError, explorer/special__chainGroupedSelectionReceiver
--   explorer/special__listEmptyListSpreadBetween, explorer/special__listEmptySeqSpreadBetween
--   explorer/special__listNeSeq, explorer/special__listEmptyNeEmptySeq, explorer/special__listSingletonNeItem
--   explorer/special__listWrapCanonicalizes, explorer/special__spreadOrdinaryFailureKept, spec/first-program
--   spec/power-unary-precedence, spec/not-binds-below-comparisons, spec/comparison-chains-compare-adjacent-pairs
--   spec/comparison-chain-boolean-and-arithmetic-operands, spec/comparison-chain-is-eager-after-false
--   spec/integer-division-truncates, spec/integer-division-beyond-consecutive-integers, spec/empty-literal
--   spec/empty-wrapped, spec/empty-wrapped-twice, spec/singleton-paren, spec/singleton-paren-deep
--   spec/supply-three-rows, spec/value-three-items, spec/spread-empty-in-sequence, spec/empty-visible-in-sequence
--   spec/empty-visible-at-root, spec/wrapped-pair-collapses, spec/pair-of-pairs-preserved
--   spec/pair-then-empty-preserved, spec/spread-empty-between-siblings, spec/spread-one-level-only
--   spec/spread-one-level-family, spec/variadic-selection-spread-forms-before-selection
--   spec/trailing-comma-continues-line, spec/comment-does-not-change-parse, spec/scalar-op-rejects-sequence
--   spec/empty-sequence-is-not-an-operator-identity, spec/division-by-zero, spec/kind-errors-are-type-mismatch
--   spec/string-equality-exact, spec/list-literal, spec/list-exactness, spec/list-vs-sequence-kind
--   spec/list-index-selects-element, spec/list-index-out-of-range, spec/list-redundant-parens-canonicalize
--   spec/list-empty-spread-neutral, spec/decimal-fraction-arithmetic, spec/division-decimal-quotient
--   spec/overflow-produces-infinity, spec/negative-zero-display, spec/pow-integer-exponent-inexact-accuracy
--   spec/pow-zero-base-negative-exponent, spec/string-single-quoted-text-is-raw
def p0_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude

-- explorer/capture__e: x = () \n x
-- the same levels and decisions, 247 more:
--   explorer/capture__n0, explorer/capture__n1, explorer/capture__bt, explorer/capture__bf, explorer/capture__pbt
--   explorer/capture__pbt_e, explorer/capture__pbt_1, explorer/capture__lbt, explorer/capture__lbt_bf
--   explorer/capture__lpbt_1, explorer/capture__p1, explorer/capture__p12, explorer/capture__p123
--   explorer/capture__pee, explorer/capture__pe1, explorer/capture__p1e, explorer/capture__p12_3
--   explorer/capture__p12_34, explorer/capture__pe_12, explorer/capture__ppe1_2, explorer/capture__p12_e
--   explorer/capture__ppe, explorer/capture__pp1, explorer/capture__ppp12, explorer/capture__le
--   explorer/capture__l7, explorer/capture__l12, explorer/capture__l12_3, explorer/capture__lle
--   explorer/capture__l_e, explorer/capture__l_p12, explorer/capture__p_l12, explorer/capture__pl1
--   explorer/captureCall__e, explorer/captureCall__n0, explorer/captureCall__n1, explorer/captureCall__bt
--   explorer/captureCall__bf, explorer/captureCall__pbt, explorer/captureCall__pbt_e, explorer/captureCall__pbt_1
--   explorer/captureCall__lbt, explorer/captureCall__lbt_bf, explorer/captureCall__lpbt_1
--   explorer/captureCall__p1, explorer/captureCall__p12, explorer/captureCall__p123, explorer/captureCall__pee
--   explorer/captureCall__pe1, explorer/captureCall__p1e, explorer/captureCall__p12_3
--   explorer/captureCall__p12_34, explorer/captureCall__pe_12, explorer/captureCall__ppe1_2
--   explorer/captureCall__p12_e, explorer/captureCall__ppe, explorer/captureCall__pp1, explorer/captureCall__ppp12
--   explorer/captureCall__le, explorer/captureCall__l7, explorer/captureCall__l12, explorer/captureCall__l12_3
--   explorer/captureCall__lle, explorer/captureCall__l_e, explorer/captureCall__l_p12, explorer/captureCall__p_l12
--   explorer/captureCall__pl1, explorer/index0__e, explorer/index0__n0, explorer/index0__n1, explorer/index0__bt
--   explorer/index0__bf, explorer/index0__pbt, explorer/index0__pbt_e, explorer/index0__pbt_1
--   explorer/index0__lbt, explorer/index0__lbt_bf, explorer/index0__lpbt_1, explorer/index0__p1
--   explorer/index0__p12, explorer/index0__p123, explorer/index0__pee, explorer/index0__pe1, explorer/index0__p1e
--   explorer/index0__p12_3, explorer/index0__p12_34, explorer/index0__pe_12, explorer/index0__ppe1_2
--   explorer/index0__p12_e, explorer/index0__ppe, explorer/index0__pp1, explorer/index0__ppp12
--   explorer/index0__le, explorer/index0__l7, explorer/index0__l12, explorer/index0__l12_3, explorer/index0__lle
--   explorer/index0__l_e, explorer/index0__l_p12, explorer/index0__p_l12, explorer/index0__pl1, explorer/index1__e
--   explorer/index1__n0, explorer/index1__n1, explorer/index1__bt, explorer/index1__bf, explorer/index1__pbt
--   explorer/index1__pbt_e, explorer/index1__pbt_1, explorer/index1__lbt, explorer/index1__lbt_bf
--   explorer/index1__lpbt_1, explorer/index1__p1, explorer/index1__p12, explorer/index1__p123
--   explorer/index1__pee, explorer/index1__pe1, explorer/index1__p1e, explorer/index1__p12_3
--   explorer/index1__p12_34, explorer/index1__pe_12, explorer/index1__ppe1_2, explorer/index1__p12_e
--   explorer/index1__ppe, explorer/index1__pp1, explorer/index1__ppp12, explorer/index1__le, explorer/index1__l7
--   explorer/index1__l12, explorer/index1__l12_3, explorer/index1__lle, explorer/index1__l_e
--   explorer/index1__l_p12, explorer/index1__p_l12, explorer/index1__pl1, explorer/indexBig__e
--   explorer/indexBig__n0, explorer/indexBig__n1, explorer/indexBig__bt, explorer/indexBig__bf
--   explorer/indexBig__pbt, explorer/indexBig__pbt_e, explorer/indexBig__pbt_1, explorer/indexBig__lbt
--   explorer/indexBig__lbt_bf, explorer/indexBig__lpbt_1, explorer/indexBig__p1, explorer/indexBig__p12
--   explorer/indexBig__p123, explorer/indexBig__pee, explorer/indexBig__pe1, explorer/indexBig__p1e
--   explorer/indexBig__p12_3, explorer/indexBig__p12_34, explorer/indexBig__pe_12, explorer/indexBig__ppe1_2
--   explorer/indexBig__p12_e, explorer/indexBig__ppe, explorer/indexBig__pp1, explorer/indexBig__ppp12
--   explorer/indexBig__le, explorer/indexBig__l7, explorer/indexBig__l12, explorer/indexBig__l12_3
--   explorer/indexBig__lle, explorer/indexBig__l_e, explorer/indexBig__l_p12, explorer/indexBig__p_l12
--   explorer/indexBig__pl1, explorer/indexNeg__e, explorer/indexNeg__n0, explorer/indexNeg__n1
--   explorer/indexNeg__bt, explorer/indexNeg__bf, explorer/indexNeg__pbt, explorer/indexNeg__pbt_e
--   explorer/indexNeg__pbt_1, explorer/indexNeg__lbt, explorer/indexNeg__lbt_bf, explorer/indexNeg__lpbt_1
--   explorer/indexNeg__p1, explorer/indexNeg__p12, explorer/indexNeg__p123, explorer/indexNeg__pee
--   explorer/indexNeg__pe1, explorer/indexNeg__p1e, explorer/indexNeg__p12_3, explorer/indexNeg__p12_34
--   explorer/indexNeg__pe_12, explorer/indexNeg__ppe1_2, explorer/indexNeg__p12_e, explorer/indexNeg__ppe
--   explorer/indexNeg__pp1, explorer/indexNeg__ppp12, explorer/indexNeg__le, explorer/indexNeg__l7
--   explorer/indexNeg__l12, explorer/indexNeg__l12_3, explorer/indexNeg__lle, explorer/indexNeg__l_e
--   explorer/indexNeg__l_p12, explorer/indexNeg__p_l12, explorer/indexNeg__pl1, explorer/captureStacked__e
--   explorer/captureStacked__n0, explorer/captureStacked__n1, explorer/captureStacked__bt
--   explorer/captureStacked__bf, explorer/captureStacked__pbt, explorer/captureStacked__pbt_e
--   explorer/captureStacked__pbt_1, explorer/captureStacked__lbt, explorer/captureStacked__lbt_bf
--   explorer/captureStacked__lpbt_1, explorer/captureStacked__p1, explorer/captureStacked__p12
--   explorer/captureStacked__p123, explorer/captureStacked__pee, explorer/captureStacked__pe1
--   explorer/captureStacked__p1e, explorer/captureStacked__p12_3, explorer/captureStacked__p12_34
--   explorer/captureStacked__pe_12, explorer/captureStacked__ppe1_2, explorer/captureStacked__p12_e
--   explorer/captureStacked__ppe, explorer/captureStacked__pp1, explorer/captureStacked__ppp12
--   explorer/captureStacked__le, explorer/captureStacked__l7, explorer/captureStacked__l12
--   explorer/captureStacked__l12_3, explorer/captureStacked__lle, explorer/captureStacked__l_e
--   explorer/captureStacked__l_p12, explorer/captureStacked__p_l12, explorer/captureStacked__pl1
--   explorer/special__indexPairInSeq, explorer/special__indexEmptyItemRoot, explorer/special__chainedListIndex
--   explorer/special__spreadWithSiblingSeqLiteral, explorer/special__strCapture, spec/spread-splices-into-sequence
--   spec/index-empty-item-visible, spec/index-out-of-range, spec/negative-index-selects-no-position
--   spec/string-displays-unquoted
def p1_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p1_1 : List OwnerLevel := { parameters := [], properties := [] } :: p1_0
#guard selectOwnedDeclaration p1_0 "x" == .property 0
#guard elaboratesToParameter p1_0 "x" == false

-- explorer/dotAccess__e: A = { \n     X = () \n } \n A.X
-- the same levels and decisions, 71 more:
--   explorer/dotAccess__n0, explorer/dotAccess__n1, explorer/dotAccess__bt, explorer/dotAccess__bf
--   explorer/dotAccess__pbt, explorer/dotAccess__pbt_e, explorer/dotAccess__pbt_1, explorer/dotAccess__lbt
--   explorer/dotAccess__lbt_bf, explorer/dotAccess__lpbt_1, explorer/dotAccess__p1, explorer/dotAccess__p12
--   explorer/dotAccess__p123, explorer/dotAccess__pee, explorer/dotAccess__pe1, explorer/dotAccess__p1e
--   explorer/dotAccess__p12_3, explorer/dotAccess__p12_34, explorer/dotAccess__pe_12, explorer/dotAccess__ppe1_2
--   explorer/dotAccess__p12_e, explorer/dotAccess__ppe, explorer/dotAccess__pp1, explorer/dotAccess__ppp12
--   explorer/dotAccess__le, explorer/dotAccess__l7, explorer/dotAccess__l12, explorer/dotAccess__l12_3
--   explorer/dotAccess__lle, explorer/dotAccess__l_e, explorer/dotAccess__l_p12, explorer/dotAccess__p_l12
--   explorer/dotAccess__pl1, explorer/dotAccessCall__e, explorer/dotAccessCall__n0, explorer/dotAccessCall__n1
--   explorer/dotAccessCall__bt, explorer/dotAccessCall__bf, explorer/dotAccessCall__pbt
--   explorer/dotAccessCall__pbt_e, explorer/dotAccessCall__pbt_1, explorer/dotAccessCall__lbt
--   explorer/dotAccessCall__lbt_bf, explorer/dotAccessCall__lpbt_1, explorer/dotAccessCall__p1
--   explorer/dotAccessCall__p12, explorer/dotAccessCall__p123, explorer/dotAccessCall__pee
--   explorer/dotAccessCall__pe1, explorer/dotAccessCall__p1e, explorer/dotAccessCall__p12_3
--   explorer/dotAccessCall__p12_34, explorer/dotAccessCall__pe_12, explorer/dotAccessCall__ppe1_2
--   explorer/dotAccessCall__p12_e, explorer/dotAccessCall__ppe, explorer/dotAccessCall__pp1
--   explorer/dotAccessCall__ppp12, explorer/dotAccessCall__le, explorer/dotAccessCall__l7
--   explorer/dotAccessCall__l12, explorer/dotAccessCall__l12_3, explorer/dotAccessCall__lle
--   explorer/dotAccessCall__l_e, explorer/dotAccessCall__l_p12, explorer/dotAccessCall__p_l12
--   explorer/dotAccessCall__pl1, explorer/special__multiPropDot, explorer/special__dotAccessPublicMember
--   explorer/special__dotAccessCallPublicMember, spec/dot-access-value-boundary
def p2_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p2_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p2_0
def p2_2 : List OwnerLevel := { parameters := [], properties := [] } :: p2_1
#guard selectOwnedDeclaration p2_0 "A" == .property 0
#guard elaboratesToParameter p2_0 "A" == false
#guard selectOwnedDeclaration p2_0 "X" == .none
#guard elaboratesToParameter p2_0 "X" == false

-- explorer/fixed__e: F(a) = a \n F(())
-- the same levels and decisions, 208 more:
--   explorer/fixed__n0, explorer/fixed__n1, explorer/fixed__bt, explorer/fixed__bf, explorer/fixed__pbt
--   explorer/fixed__pbt_e, explorer/fixed__pbt_1, explorer/fixed__lbt, explorer/fixed__lbt_bf
--   explorer/fixed__lpbt_1, explorer/fixed__p1, explorer/fixed__p12, explorer/fixed__p123, explorer/fixed__pee
--   explorer/fixed__pe1, explorer/fixed__p1e, explorer/fixed__p12_3, explorer/fixed__p12_34, explorer/fixed__pe_12
--   explorer/fixed__ppe1_2, explorer/fixed__p12_e, explorer/fixed__ppe, explorer/fixed__pp1, explorer/fixed__ppp12
--   explorer/fixed__le, explorer/fixed__l7, explorer/fixed__l12, explorer/fixed__l12_3, explorer/fixed__lle
--   explorer/fixed__l_e, explorer/fixed__l_p12, explorer/fixed__p_l12, explorer/fixed__pl1
--   explorer/fixedSpread__e, explorer/fixedSpread__n0, explorer/fixedSpread__n1, explorer/fixedSpread__bt
--   explorer/fixedSpread__bf, explorer/fixedSpread__pbt, explorer/fixedSpread__pbt_e, explorer/fixedSpread__pbt_1
--   explorer/fixedSpread__lbt, explorer/fixedSpread__lbt_bf, explorer/fixedSpread__lpbt_1
--   explorer/fixedSpread__p1, explorer/fixedSpread__p12, explorer/fixedSpread__p123, explorer/fixedSpread__pee
--   explorer/fixedSpread__pe1, explorer/fixedSpread__p1e, explorer/fixedSpread__p12_3
--   explorer/fixedSpread__p12_34, explorer/fixedSpread__pe_12, explorer/fixedSpread__ppe1_2
--   explorer/fixedSpread__p12_e, explorer/fixedSpread__ppe, explorer/fixedSpread__pp1, explorer/fixedSpread__ppp12
--   explorer/fixedSpread__le, explorer/fixedSpread__l7, explorer/fixedSpread__l12, explorer/fixedSpread__l12_3
--   explorer/fixedSpread__lle, explorer/fixedSpread__l_e, explorer/fixedSpread__l_p12, explorer/fixedSpread__p_l12
--   explorer/fixedSpread__pl1, explorer/collecting__e, explorer/collecting__n0, explorer/collecting__n1
--   explorer/collecting__bt, explorer/collecting__bf, explorer/collecting__pbt, explorer/collecting__pbt_e
--   explorer/collecting__pbt_1, explorer/collecting__lbt, explorer/collecting__lbt_bf, explorer/collecting__lpbt_1
--   explorer/collecting__p1, explorer/collecting__p12, explorer/collecting__p123, explorer/collecting__pee
--   explorer/collecting__pe1, explorer/collecting__p1e, explorer/collecting__p12_3, explorer/collecting__p12_34
--   explorer/collecting__pe_12, explorer/collecting__ppe1_2, explorer/collecting__p12_e, explorer/collecting__ppe
--   explorer/collecting__pp1, explorer/collecting__ppp12, explorer/collecting__le, explorer/collecting__l7
--   explorer/collecting__l12, explorer/collecting__l12_3, explorer/collecting__lle, explorer/collecting__l_e
--   explorer/collecting__l_p12, explorer/collecting__p_l12, explorer/collecting__pl1, explorer/collectingSpread__e
--   explorer/collectingSpread__n0, explorer/collectingSpread__n1, explorer/collectingSpread__bt
--   explorer/collectingSpread__bf, explorer/collectingSpread__pbt, explorer/collectingSpread__pbt_e
--   explorer/collectingSpread__pbt_1, explorer/collectingSpread__lbt, explorer/collectingSpread__lbt_bf
--   explorer/collectingSpread__lpbt_1, explorer/collectingSpread__p1, explorer/collectingSpread__p12
--   explorer/collectingSpread__p123, explorer/collectingSpread__pee, explorer/collectingSpread__pe1
--   explorer/collectingSpread__p1e, explorer/collectingSpread__p12_3, explorer/collectingSpread__p12_34
--   explorer/collectingSpread__pe_12, explorer/collectingSpread__ppe1_2, explorer/collectingSpread__p12_e
--   explorer/collectingSpread__ppe, explorer/collectingSpread__pp1, explorer/collectingSpread__ppp12
--   explorer/collectingSpread__le, explorer/collectingSpread__l7, explorer/collectingSpread__l12
--   explorer/collectingSpread__l12_3, explorer/collectingSpread__lle, explorer/collectingSpread__l_e
--   explorer/collectingSpread__l_p12, explorer/collectingSpread__p_l12, explorer/collectingSpread__pl1
--   explorer/literalDotCollecting__e, explorer/literalDotCollecting__n0, explorer/literalDotCollecting__n1
--   explorer/literalDotCollecting__bt, explorer/literalDotCollecting__bf, explorer/literalDotCollecting__pbt
--   explorer/literalDotCollecting__pbt_e, explorer/literalDotCollecting__pbt_1, explorer/literalDotCollecting__lbt
--   explorer/literalDotCollecting__lbt_bf, explorer/literalDotCollecting__lpbt_1
--   explorer/literalDotCollecting__p1, explorer/literalDotCollecting__p12, explorer/literalDotCollecting__p123
--   explorer/literalDotCollecting__pee, explorer/literalDotCollecting__pe1, explorer/literalDotCollecting__p1e
--   explorer/literalDotCollecting__p12_3, explorer/literalDotCollecting__p12_34
--   explorer/literalDotCollecting__pe_12, explorer/literalDotCollecting__ppe1_2
--   explorer/literalDotCollecting__p12_e, explorer/literalDotCollecting__ppe, explorer/literalDotCollecting__pp1
--   explorer/literalDotCollecting__ppp12, explorer/literalDotCollecting__le, explorer/literalDotCollecting__l7
--   explorer/literalDotCollecting__l12, explorer/literalDotCollecting__l12_3, explorer/literalDotCollecting__lle
--   explorer/literalDotCollecting__l_e, explorer/literalDotCollecting__l_p12, explorer/literalDotCollecting__p_l12
--   explorer/literalDotCollecting__pl1, explorer/collectingStacked__e, explorer/collectingStacked__n0
--   explorer/collectingStacked__n1, explorer/collectingStacked__bt, explorer/collectingStacked__bf
--   explorer/collectingStacked__pbt, explorer/collectingStacked__pbt_e, explorer/collectingStacked__pbt_1
--   explorer/collectingStacked__lbt, explorer/collectingStacked__lbt_bf, explorer/collectingStacked__lpbt_1
--   explorer/collectingStacked__p1, explorer/collectingStacked__p12, explorer/collectingStacked__p123
--   explorer/collectingStacked__pee, explorer/collectingStacked__pe1, explorer/collectingStacked__p1e
--   explorer/collectingStacked__p12_3, explorer/collectingStacked__p12_34, explorer/collectingStacked__pe_12
--   explorer/collectingStacked__ppe1_2, explorer/collectingStacked__p12_e, explorer/collectingStacked__ppe
--   explorer/collectingStacked__pp1, explorer/collectingStacked__ppp12, explorer/collectingStacked__le
--   explorer/collectingStacked__l7, explorer/collectingStacked__l12, explorer/collectingStacked__l12_3
--   explorer/collectingStacked__lle, explorer/collectingStacked__l_e, explorer/collectingStacked__l_p12
--   explorer/collectingStacked__p_l12, explorer/collectingStacked__pl1, explorer/special__multiCollecting
--   explorer/special__collectingEmptyCall, explorer/special__collectingJoin, spec/fixed-empty-arg-visible
--   spec/fixed-empty-spread-zero-items
def p3_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p3_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p3_0
#guard selectOwnedDeclaration p3_1 "a" == .parameter 0
#guard elaboratesToParameter p3_1 "a" == true
#guard selectOwnedDeclaration p3_0 "F" == .property 0
#guard elaboratesToParameter p3_0 "F" == false

-- explorer/collectingViaProp__e: F(*a) = a \n x = () \n F(x)
-- the same levels and decisions, 67 more:
--   explorer/collectingViaProp__n0, explorer/collectingViaProp__n1, explorer/collectingViaProp__bt
--   explorer/collectingViaProp__bf, explorer/collectingViaProp__pbt, explorer/collectingViaProp__pbt_e
--   explorer/collectingViaProp__pbt_1, explorer/collectingViaProp__lbt, explorer/collectingViaProp__lbt_bf
--   explorer/collectingViaProp__lpbt_1, explorer/collectingViaProp__p1, explorer/collectingViaProp__p12
--   explorer/collectingViaProp__p123, explorer/collectingViaProp__pee, explorer/collectingViaProp__pe1
--   explorer/collectingViaProp__p1e, explorer/collectingViaProp__p12_3, explorer/collectingViaProp__p12_34
--   explorer/collectingViaProp__pe_12, explorer/collectingViaProp__ppe1_2, explorer/collectingViaProp__p12_e
--   explorer/collectingViaProp__ppe, explorer/collectingViaProp__pp1, explorer/collectingViaProp__ppp12
--   explorer/collectingViaProp__le, explorer/collectingViaProp__l7, explorer/collectingViaProp__l12
--   explorer/collectingViaProp__l12_3, explorer/collectingViaProp__lle, explorer/collectingViaProp__l_e
--   explorer/collectingViaProp__l_p12, explorer/collectingViaProp__p_l12, explorer/collectingViaProp__pl1
--   explorer/fluentSpreadCollecting__e, explorer/fluentSpreadCollecting__n0, explorer/fluentSpreadCollecting__n1
--   explorer/fluentSpreadCollecting__bt, explorer/fluentSpreadCollecting__bf, explorer/fluentSpreadCollecting__pbt
--   explorer/fluentSpreadCollecting__pbt_e, explorer/fluentSpreadCollecting__pbt_1
--   explorer/fluentSpreadCollecting__lbt, explorer/fluentSpreadCollecting__lbt_bf
--   explorer/fluentSpreadCollecting__lpbt_1, explorer/fluentSpreadCollecting__p1
--   explorer/fluentSpreadCollecting__p12, explorer/fluentSpreadCollecting__p123
--   explorer/fluentSpreadCollecting__pee, explorer/fluentSpreadCollecting__pe1
--   explorer/fluentSpreadCollecting__p1e, explorer/fluentSpreadCollecting__p12_3
--   explorer/fluentSpreadCollecting__p12_34, explorer/fluentSpreadCollecting__pe_12
--   explorer/fluentSpreadCollecting__ppe1_2, explorer/fluentSpreadCollecting__p12_e
--   explorer/fluentSpreadCollecting__ppe, explorer/fluentSpreadCollecting__pp1
--   explorer/fluentSpreadCollecting__ppp12, explorer/fluentSpreadCollecting__le
--   explorer/fluentSpreadCollecting__l7, explorer/fluentSpreadCollecting__l12
--   explorer/fluentSpreadCollecting__l12_3, explorer/fluentSpreadCollecting__lle
--   explorer/fluentSpreadCollecting__l_e, explorer/fluentSpreadCollecting__l_p12
--   explorer/fluentSpreadCollecting__p_l12, explorer/fluentSpreadCollecting__pl1
def p4_0 : List OwnerLevel := { parameters := [], properties := ["x", "F"] } :: prelude
def p4_1 : List OwnerLevel := { parameters := [], properties := [] } :: p4_0
def p4_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p4_0
#guard selectOwnedDeclaration p4_2 "a" == .parameter 0
#guard elaboratesToParameter p4_2 "a" == true
#guard selectOwnedDeclaration p4_0 "F" == .property 0
#guard elaboratesToParameter p4_0 "F" == false
#guard selectOwnedDeclaration p4_0 "x" == .property 0
#guard elaboratesToParameter p4_0 "x" == false

-- explorer/dotCollectingViaProp__e: F(*a) = a \n x = () \n x.F
-- the same levels and decisions, 33 more:
--   explorer/dotCollectingViaProp__n0, explorer/dotCollectingViaProp__n1, explorer/dotCollectingViaProp__bt
--   explorer/dotCollectingViaProp__bf, explorer/dotCollectingViaProp__pbt, explorer/dotCollectingViaProp__pbt_e
--   explorer/dotCollectingViaProp__pbt_1, explorer/dotCollectingViaProp__lbt
--   explorer/dotCollectingViaProp__lbt_bf, explorer/dotCollectingViaProp__lpbt_1
--   explorer/dotCollectingViaProp__p1, explorer/dotCollectingViaProp__p12, explorer/dotCollectingViaProp__p123
--   explorer/dotCollectingViaProp__pee, explorer/dotCollectingViaProp__pe1, explorer/dotCollectingViaProp__p1e
--   explorer/dotCollectingViaProp__p12_3, explorer/dotCollectingViaProp__p12_34
--   explorer/dotCollectingViaProp__pe_12, explorer/dotCollectingViaProp__ppe1_2
--   explorer/dotCollectingViaProp__p12_e, explorer/dotCollectingViaProp__ppe, explorer/dotCollectingViaProp__pp1
--   explorer/dotCollectingViaProp__ppp12, explorer/dotCollectingViaProp__le, explorer/dotCollectingViaProp__l7
--   explorer/dotCollectingViaProp__l12, explorer/dotCollectingViaProp__l12_3, explorer/dotCollectingViaProp__lle
--   explorer/dotCollectingViaProp__l_e, explorer/dotCollectingViaProp__l_p12, explorer/dotCollectingViaProp__p_l12
--   explorer/dotCollectingViaProp__pl1
def p5_0 : List OwnerLevel := { parameters := [], properties := ["x", "F"] } :: prelude
def p5_1 : List OwnerLevel := { parameters := [], properties := [] } :: p5_0
def p5_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p5_0
#guard selectOwnedDeclaration p5_2 "a" == .parameter 0
#guard elaboratesToParameter p5_2 "a" == true
#guard selectOwnedDeclaration p5_0 "x" == .property 0
#guard elaboratesToParameter p5_0 "x" == false
#guard selectOwnedDeclaration p5_0 "F" == .property 0
#guard elaboratesToParameter p5_0 "F" == false

-- explorer/mixed_h__e: F(h, *t) = h \n F(()*)
-- the same levels and decisions, 33 more:
--   explorer/mixed_h__n0, explorer/mixed_h__n1, explorer/mixed_h__bt, explorer/mixed_h__bf, explorer/mixed_h__pbt
--   explorer/mixed_h__pbt_e, explorer/mixed_h__pbt_1, explorer/mixed_h__lbt, explorer/mixed_h__lbt_bf
--   explorer/mixed_h__lpbt_1, explorer/mixed_h__p1, explorer/mixed_h__p12, explorer/mixed_h__p123
--   explorer/mixed_h__pee, explorer/mixed_h__pe1, explorer/mixed_h__p1e, explorer/mixed_h__p12_3
--   explorer/mixed_h__p12_34, explorer/mixed_h__pe_12, explorer/mixed_h__ppe1_2, explorer/mixed_h__p12_e
--   explorer/mixed_h__ppe, explorer/mixed_h__pp1, explorer/mixed_h__ppp12, explorer/mixed_h__le
--   explorer/mixed_h__l7, explorer/mixed_h__l12, explorer/mixed_h__l12_3, explorer/mixed_h__lle
--   explorer/mixed_h__l_e, explorer/mixed_h__l_p12, explorer/mixed_h__p_l12, explorer/mixed_h__pl1
def p6_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p6_1 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p6_0
#guard selectOwnedDeclaration p6_1 "h" == .parameter 0
#guard elaboratesToParameter p6_1 "h" == true
#guard selectOwnedDeclaration p6_0 "F" == .property 0
#guard elaboratesToParameter p6_0 "F" == false

-- explorer/mixed_t__e: F(h, *t) = t \n F(()*)
-- the same levels and decisions, 33 more:
--   explorer/mixed_t__n0, explorer/mixed_t__n1, explorer/mixed_t__bt, explorer/mixed_t__bf, explorer/mixed_t__pbt
--   explorer/mixed_t__pbt_e, explorer/mixed_t__pbt_1, explorer/mixed_t__lbt, explorer/mixed_t__lbt_bf
--   explorer/mixed_t__lpbt_1, explorer/mixed_t__p1, explorer/mixed_t__p12, explorer/mixed_t__p123
--   explorer/mixed_t__pee, explorer/mixed_t__pe1, explorer/mixed_t__p1e, explorer/mixed_t__p12_3
--   explorer/mixed_t__p12_34, explorer/mixed_t__pe_12, explorer/mixed_t__ppe1_2, explorer/mixed_t__p12_e
--   explorer/mixed_t__ppe, explorer/mixed_t__pp1, explorer/mixed_t__ppp12, explorer/mixed_t__le
--   explorer/mixed_t__l7, explorer/mixed_t__l12, explorer/mixed_t__l12_3, explorer/mixed_t__lle
--   explorer/mixed_t__l_e, explorer/mixed_t__l_p12, explorer/mixed_t__p_l12, explorer/mixed_t__pl1
def p7_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p7_1 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p7_0
#guard selectOwnedDeclaration p7_1 "t" == .parameter 0
#guard elaboratesToParameter p7_1 "t" == true
#guard selectOwnedDeclaration p7_0 "F" == .property 0
#guard elaboratesToParameter p7_0 "F" == false

-- explorer/mixedBack_t__e: F(*t, z) = t \n F(()*)
-- the same levels and decisions, 33 more:
--   explorer/mixedBack_t__n0, explorer/mixedBack_t__n1, explorer/mixedBack_t__bt, explorer/mixedBack_t__bf
--   explorer/mixedBack_t__pbt, explorer/mixedBack_t__pbt_e, explorer/mixedBack_t__pbt_1, explorer/mixedBack_t__lbt
--   explorer/mixedBack_t__lbt_bf, explorer/mixedBack_t__lpbt_1, explorer/mixedBack_t__p1
--   explorer/mixedBack_t__p12, explorer/mixedBack_t__p123, explorer/mixedBack_t__pee, explorer/mixedBack_t__pe1
--   explorer/mixedBack_t__p1e, explorer/mixedBack_t__p12_3, explorer/mixedBack_t__p12_34
--   explorer/mixedBack_t__pe_12, explorer/mixedBack_t__ppe1_2, explorer/mixedBack_t__p12_e
--   explorer/mixedBack_t__ppe, explorer/mixedBack_t__pp1, explorer/mixedBack_t__ppp12, explorer/mixedBack_t__le
--   explorer/mixedBack_t__l7, explorer/mixedBack_t__l12, explorer/mixedBack_t__l12_3, explorer/mixedBack_t__lle
--   explorer/mixedBack_t__l_e, explorer/mixedBack_t__l_p12, explorer/mixedBack_t__p_l12, explorer/mixedBack_t__pl1
def p8_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p8_1 : List OwnerLevel := { parameters := ["t", "z"], properties := [] } :: p8_0
#guard selectOwnedDeclaration p8_1 "t" == .parameter 0
#guard elaboratesToParameter p8_1 "t" == true
#guard selectOwnedDeclaration p8_0 "F" == .property 0
#guard elaboratesToParameter p8_0 "F" == false

-- explorer/mixedBack_z__e: F(*t, z) = z \n F(()*)
-- the same levels and decisions, 33 more:
--   explorer/mixedBack_z__n0, explorer/mixedBack_z__n1, explorer/mixedBack_z__bt, explorer/mixedBack_z__bf
--   explorer/mixedBack_z__pbt, explorer/mixedBack_z__pbt_e, explorer/mixedBack_z__pbt_1, explorer/mixedBack_z__lbt
--   explorer/mixedBack_z__lbt_bf, explorer/mixedBack_z__lpbt_1, explorer/mixedBack_z__p1
--   explorer/mixedBack_z__p12, explorer/mixedBack_z__p123, explorer/mixedBack_z__pee, explorer/mixedBack_z__pe1
--   explorer/mixedBack_z__p1e, explorer/mixedBack_z__p12_3, explorer/mixedBack_z__p12_34
--   explorer/mixedBack_z__pe_12, explorer/mixedBack_z__ppe1_2, explorer/mixedBack_z__p12_e
--   explorer/mixedBack_z__ppe, explorer/mixedBack_z__pp1, explorer/mixedBack_z__ppp12, explorer/mixedBack_z__le
--   explorer/mixedBack_z__l7, explorer/mixedBack_z__l12, explorer/mixedBack_z__l12_3, explorer/mixedBack_z__lle
--   explorer/mixedBack_z__l_e, explorer/mixedBack_z__l_p12, explorer/mixedBack_z__p_l12, explorer/mixedBack_z__pl1
def p9_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p9_1 : List OwnerLevel := { parameters := ["t", "z"], properties := [] } :: p9_0
#guard selectOwnedDeclaration p9_1 "z" == .parameter 0
#guard elaboratesToParameter p9_1 "z" == true
#guard selectOwnedDeclaration p9_0 "F" == .property 0
#guard elaboratesToParameter p9_0 "F" == false

-- explorer/deconPair_x__e: x, y = () \n x
-- the same levels and decisions, 69 more:
--   explorer/deconPair_x__n0, explorer/deconPair_x__n1, explorer/deconPair_x__bt, explorer/deconPair_x__bf
--   explorer/deconPair_x__pbt, explorer/deconPair_x__pbt_e, explorer/deconPair_x__pbt_1, explorer/deconPair_x__lbt
--   explorer/deconPair_x__lbt_bf, explorer/deconPair_x__lpbt_1, explorer/deconPair_x__p1
--   explorer/deconPair_x__p12, explorer/deconPair_x__p123, explorer/deconPair_x__pee, explorer/deconPair_x__pe1
--   explorer/deconPair_x__p1e, explorer/deconPair_x__p12_3, explorer/deconPair_x__p12_34
--   explorer/deconPair_x__pe_12, explorer/deconPair_x__ppe1_2, explorer/deconPair_x__p12_e
--   explorer/deconPair_x__ppe, explorer/deconPair_x__pp1, explorer/deconPair_x__ppp12, explorer/deconPair_x__le
--   explorer/deconPair_x__l7, explorer/deconPair_x__l12, explorer/deconPair_x__l12_3, explorer/deconPair_x__lle
--   explorer/deconPair_x__l_e, explorer/deconPair_x__l_p12, explorer/deconPair_x__p_l12, explorer/deconPair_x__pl1
--   explorer/deconPairSpread_x__e, explorer/deconPairSpread_x__n0, explorer/deconPairSpread_x__n1
--   explorer/deconPairSpread_x__bt, explorer/deconPairSpread_x__bf, explorer/deconPairSpread_x__pbt
--   explorer/deconPairSpread_x__pbt_e, explorer/deconPairSpread_x__pbt_1, explorer/deconPairSpread_x__lbt
--   explorer/deconPairSpread_x__lbt_bf, explorer/deconPairSpread_x__lpbt_1, explorer/deconPairSpread_x__p1
--   explorer/deconPairSpread_x__p12, explorer/deconPairSpread_x__p123, explorer/deconPairSpread_x__pee
--   explorer/deconPairSpread_x__pe1, explorer/deconPairSpread_x__p1e, explorer/deconPairSpread_x__p12_3
--   explorer/deconPairSpread_x__p12_34, explorer/deconPairSpread_x__pe_12, explorer/deconPairSpread_x__ppe1_2
--   explorer/deconPairSpread_x__p12_e, explorer/deconPairSpread_x__ppe, explorer/deconPairSpread_x__pp1
--   explorer/deconPairSpread_x__ppp12, explorer/deconPairSpread_x__le, explorer/deconPairSpread_x__l7
--   explorer/deconPairSpread_x__l12, explorer/deconPairSpread_x__l12_3, explorer/deconPairSpread_x__lle
--   explorer/deconPairSpread_x__l_e, explorer/deconPairSpread_x__l_p12, explorer/deconPairSpread_x__p_l12
--   explorer/deconPairSpread_x__pl1, spec/decon-arity-under, spec/decon-arity-over
def p10_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "y"] } :: prelude
def p10_1 : List OwnerLevel := { parameters := [], properties := [] } :: p10_0
def p10_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p10_1
def p10_3 : List OwnerLevel := { parameters := [], properties := [] } :: p10_0
def p10_4 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p10_3
#guard selectOwnedDeclaration p10_2 "x" == .parameter 0
#guard elaboratesToParameter p10_2 "x" == true
#guard selectOwnedDeclaration p10_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p10_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p10_4 "y" == .parameter 0
#guard elaboratesToParameter p10_4 "y" == true
#guard selectOwnedDeclaration p10_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p10_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p10_0 "x" == .property 0
#guard elaboratesToParameter p10_0 "x" == false

-- explorer/deconPair_y__e: x, y = () \n y
-- the same levels and decisions, 33 more:
--   explorer/deconPair_y__n0, explorer/deconPair_y__n1, explorer/deconPair_y__bt, explorer/deconPair_y__bf
--   explorer/deconPair_y__pbt, explorer/deconPair_y__pbt_e, explorer/deconPair_y__pbt_1, explorer/deconPair_y__lbt
--   explorer/deconPair_y__lbt_bf, explorer/deconPair_y__lpbt_1, explorer/deconPair_y__p1
--   explorer/deconPair_y__p12, explorer/deconPair_y__p123, explorer/deconPair_y__pee, explorer/deconPair_y__pe1
--   explorer/deconPair_y__p1e, explorer/deconPair_y__p12_3, explorer/deconPair_y__p12_34
--   explorer/deconPair_y__pe_12, explorer/deconPair_y__ppe1_2, explorer/deconPair_y__p12_e
--   explorer/deconPair_y__ppe, explorer/deconPair_y__pp1, explorer/deconPair_y__ppp12, explorer/deconPair_y__le
--   explorer/deconPair_y__l7, explorer/deconPair_y__l12, explorer/deconPair_y__l12_3, explorer/deconPair_y__lle
--   explorer/deconPair_y__l_e, explorer/deconPair_y__l_p12, explorer/deconPair_y__p_l12, explorer/deconPair_y__pl1
def p11_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "y"] } :: prelude
def p11_1 : List OwnerLevel := { parameters := [], properties := [] } :: p11_0
def p11_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p11_1
def p11_3 : List OwnerLevel := { parameters := [], properties := [] } :: p11_0
def p11_4 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p11_3
#guard selectOwnedDeclaration p11_2 "x" == .parameter 0
#guard elaboratesToParameter p11_2 "x" == true
#guard selectOwnedDeclaration p11_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p11_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p11_4 "y" == .parameter 0
#guard elaboratesToParameter p11_4 "y" == true
#guard selectOwnedDeclaration p11_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p11_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p11_0 "y" == .property 0
#guard elaboratesToParameter p11_0 "y" == false

-- explorer/deconCollect_t__e: h, *t = () \n t
-- the same levels and decisions, 67 more:
--   explorer/deconCollect_t__n0, explorer/deconCollect_t__n1, explorer/deconCollect_t__bt
--   explorer/deconCollect_t__bf, explorer/deconCollect_t__pbt, explorer/deconCollect_t__pbt_e
--   explorer/deconCollect_t__pbt_1, explorer/deconCollect_t__lbt, explorer/deconCollect_t__lbt_bf
--   explorer/deconCollect_t__lpbt_1, explorer/deconCollect_t__p1, explorer/deconCollect_t__p12
--   explorer/deconCollect_t__p123, explorer/deconCollect_t__pee, explorer/deconCollect_t__pe1
--   explorer/deconCollect_t__p1e, explorer/deconCollect_t__p12_3, explorer/deconCollect_t__p12_34
--   explorer/deconCollect_t__pe_12, explorer/deconCollect_t__ppe1_2, explorer/deconCollect_t__p12_e
--   explorer/deconCollect_t__ppe, explorer/deconCollect_t__pp1, explorer/deconCollect_t__ppp12
--   explorer/deconCollect_t__le, explorer/deconCollect_t__l7, explorer/deconCollect_t__l12
--   explorer/deconCollect_t__l12_3, explorer/deconCollect_t__lle, explorer/deconCollect_t__l_e
--   explorer/deconCollect_t__l_p12, explorer/deconCollect_t__p_l12, explorer/deconCollect_t__pl1
--   explorer/deconCollectSpread_t__e, explorer/deconCollectSpread_t__n0, explorer/deconCollectSpread_t__n1
--   explorer/deconCollectSpread_t__bt, explorer/deconCollectSpread_t__bf, explorer/deconCollectSpread_t__pbt
--   explorer/deconCollectSpread_t__pbt_e, explorer/deconCollectSpread_t__pbt_1, explorer/deconCollectSpread_t__lbt
--   explorer/deconCollectSpread_t__lbt_bf, explorer/deconCollectSpread_t__lpbt_1
--   explorer/deconCollectSpread_t__p1, explorer/deconCollectSpread_t__p12, explorer/deconCollectSpread_t__p123
--   explorer/deconCollectSpread_t__pee, explorer/deconCollectSpread_t__pe1, explorer/deconCollectSpread_t__p1e
--   explorer/deconCollectSpread_t__p12_3, explorer/deconCollectSpread_t__p12_34
--   explorer/deconCollectSpread_t__pe_12, explorer/deconCollectSpread_t__ppe1_2
--   explorer/deconCollectSpread_t__p12_e, explorer/deconCollectSpread_t__ppe, explorer/deconCollectSpread_t__pp1
--   explorer/deconCollectSpread_t__ppp12, explorer/deconCollectSpread_t__le, explorer/deconCollectSpread_t__l7
--   explorer/deconCollectSpread_t__l12, explorer/deconCollectSpread_t__l12_3, explorer/deconCollectSpread_t__lle
--   explorer/deconCollectSpread_t__l_e, explorer/deconCollectSpread_t__l_p12, explorer/deconCollectSpread_t__p_l12
--   explorer/deconCollectSpread_t__pl1
def p12_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "h", "t"] } :: prelude
def p12_1 : List OwnerLevel := { parameters := [], properties := [] } :: p12_0
def p12_2 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p12_1
def p12_3 : List OwnerLevel := { parameters := [], properties := [] } :: p12_0
def p12_4 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p12_3
#guard selectOwnedDeclaration p12_2 "h" == .parameter 0
#guard elaboratesToParameter p12_2 "h" == true
#guard selectOwnedDeclaration p12_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p12_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p12_4 "t" == .parameter 0
#guard elaboratesToParameter p12_4 "t" == true
#guard selectOwnedDeclaration p12_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p12_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p12_0 "t" == .property 0
#guard elaboratesToParameter p12_0 "t" == false

-- explorer/deconPrefix_p__e: *p, z = () \n p
-- the same levels and decisions, 33 more:
--   explorer/deconPrefix_p__n0, explorer/deconPrefix_p__n1, explorer/deconPrefix_p__bt, explorer/deconPrefix_p__bf
--   explorer/deconPrefix_p__pbt, explorer/deconPrefix_p__pbt_e, explorer/deconPrefix_p__pbt_1
--   explorer/deconPrefix_p__lbt, explorer/deconPrefix_p__lbt_bf, explorer/deconPrefix_p__lpbt_1
--   explorer/deconPrefix_p__p1, explorer/deconPrefix_p__p12, explorer/deconPrefix_p__p123
--   explorer/deconPrefix_p__pee, explorer/deconPrefix_p__pe1, explorer/deconPrefix_p__p1e
--   explorer/deconPrefix_p__p12_3, explorer/deconPrefix_p__p12_34, explorer/deconPrefix_p__pe_12
--   explorer/deconPrefix_p__ppe1_2, explorer/deconPrefix_p__p12_e, explorer/deconPrefix_p__ppe
--   explorer/deconPrefix_p__pp1, explorer/deconPrefix_p__ppp12, explorer/deconPrefix_p__le
--   explorer/deconPrefix_p__l7, explorer/deconPrefix_p__l12, explorer/deconPrefix_p__l12_3
--   explorer/deconPrefix_p__lle, explorer/deconPrefix_p__l_e, explorer/deconPrefix_p__l_p12
--   explorer/deconPrefix_p__p_l12, explorer/deconPrefix_p__pl1
def p13_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "p", "z"] } :: prelude
def p13_1 : List OwnerLevel := { parameters := [], properties := [] } :: p13_0
def p13_2 : List OwnerLevel := { parameters := ["p", "z"], properties := [] } :: p13_1
def p13_3 : List OwnerLevel := { parameters := [], properties := [] } :: p13_0
def p13_4 : List OwnerLevel := { parameters := ["p", "z"], properties := [] } :: p13_3
#guard selectOwnedDeclaration p13_2 "p" == .parameter 0
#guard elaboratesToParameter p13_2 "p" == true
#guard selectOwnedDeclaration p13_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p13_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p13_4 "z" == .parameter 0
#guard elaboratesToParameter p13_4 "z" == true
#guard selectOwnedDeclaration p13_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p13_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p13_0 "p" == .property 0
#guard elaboratesToParameter p13_0 "p" == false

-- explorer/deconPrefix_z__e: *p, z = () \n z
-- the same levels and decisions, 33 more:
--   explorer/deconPrefix_z__n0, explorer/deconPrefix_z__n1, explorer/deconPrefix_z__bt, explorer/deconPrefix_z__bf
--   explorer/deconPrefix_z__pbt, explorer/deconPrefix_z__pbt_e, explorer/deconPrefix_z__pbt_1
--   explorer/deconPrefix_z__lbt, explorer/deconPrefix_z__lbt_bf, explorer/deconPrefix_z__lpbt_1
--   explorer/deconPrefix_z__p1, explorer/deconPrefix_z__p12, explorer/deconPrefix_z__p123
--   explorer/deconPrefix_z__pee, explorer/deconPrefix_z__pe1, explorer/deconPrefix_z__p1e
--   explorer/deconPrefix_z__p12_3, explorer/deconPrefix_z__p12_34, explorer/deconPrefix_z__pe_12
--   explorer/deconPrefix_z__ppe1_2, explorer/deconPrefix_z__p12_e, explorer/deconPrefix_z__ppe
--   explorer/deconPrefix_z__pp1, explorer/deconPrefix_z__ppp12, explorer/deconPrefix_z__le
--   explorer/deconPrefix_z__l7, explorer/deconPrefix_z__l12, explorer/deconPrefix_z__l12_3
--   explorer/deconPrefix_z__lle, explorer/deconPrefix_z__l_e, explorer/deconPrefix_z__l_p12
--   explorer/deconPrefix_z__p_l12, explorer/deconPrefix_z__pl1
def p14_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "p", "z"] } :: prelude
def p14_1 : List OwnerLevel := { parameters := [], properties := [] } :: p14_0
def p14_2 : List OwnerLevel := { parameters := ["p", "z"], properties := [] } :: p14_1
def p14_3 : List OwnerLevel := { parameters := [], properties := [] } :: p14_0
def p14_4 : List OwnerLevel := { parameters := ["p", "z"], properties := [] } :: p14_3
#guard selectOwnedDeclaration p14_2 "p" == .parameter 0
#guard elaboratesToParameter p14_2 "p" == true
#guard selectOwnedDeclaration p14_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p14_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p14_4 "z" == .parameter 0
#guard elaboratesToParameter p14_4 "z" == true
#guard selectOwnedDeclaration p14_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p14_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p14_0 "z" == .property 0
#guard elaboratesToParameter p14_0 "z" == false

-- explorer/count__e: count(())
-- the same levels and decisions, 108 more:
--   explorer/count__n0, explorer/count__n1, explorer/count__bt, explorer/count__bf, explorer/count__pbt
--   explorer/count__pbt_e, explorer/count__pbt_1, explorer/count__lbt, explorer/count__lbt_bf
--   explorer/count__lpbt_1, explorer/count__p1, explorer/count__p12, explorer/count__p123, explorer/count__pee
--   explorer/count__pe1, explorer/count__p1e, explorer/count__p12_3, explorer/count__p12_34, explorer/count__pe_12
--   explorer/count__ppe1_2, explorer/count__p12_e, explorer/count__ppe, explorer/count__pp1, explorer/count__ppp12
--   explorer/count__le, explorer/count__l7, explorer/count__l12, explorer/count__l12_3, explorer/count__lle
--   explorer/count__l_e, explorer/count__l_p12, explorer/count__p_l12, explorer/count__pl1
--   explorer/countSpread__e, explorer/countSpread__n0, explorer/countSpread__n1, explorer/countSpread__bt
--   explorer/countSpread__bf, explorer/countSpread__pbt, explorer/countSpread__pbt_e, explorer/countSpread__pbt_1
--   explorer/countSpread__lbt, explorer/countSpread__lbt_bf, explorer/countSpread__lpbt_1
--   explorer/countSpread__p1, explorer/countSpread__p12, explorer/countSpread__p123, explorer/countSpread__pee
--   explorer/countSpread__pe1, explorer/countSpread__p1e, explorer/countSpread__p12_3
--   explorer/countSpread__p12_34, explorer/countSpread__pe_12, explorer/countSpread__ppe1_2
--   explorer/countSpread__p12_e, explorer/countSpread__ppe, explorer/countSpread__pp1, explorer/countSpread__ppp12
--   explorer/countSpread__le, explorer/countSpread__l7, explorer/countSpread__l12, explorer/countSpread__l12_3
--   explorer/countSpread__lle, explorer/countSpread__l_e, explorer/countSpread__l_p12, explorer/countSpread__p_l12
--   explorer/countSpread__pl1, explorer/literalDotCount__e, explorer/literalDotCount__n0
--   explorer/literalDotCount__n1, explorer/literalDotCount__bt, explorer/literalDotCount__bf
--   explorer/literalDotCount__pbt, explorer/literalDotCount__pbt_e, explorer/literalDotCount__pbt_1
--   explorer/literalDotCount__lbt, explorer/literalDotCount__lbt_bf, explorer/literalDotCount__lpbt_1
--   explorer/literalDotCount__p1, explorer/literalDotCount__p12, explorer/literalDotCount__p123
--   explorer/literalDotCount__pee, explorer/literalDotCount__pe1, explorer/literalDotCount__p1e
--   explorer/literalDotCount__p12_3, explorer/literalDotCount__p12_34, explorer/literalDotCount__pe_12
--   explorer/literalDotCount__ppe1_2, explorer/literalDotCount__p12_e, explorer/literalDotCount__ppe
--   explorer/literalDotCount__pp1, explorer/literalDotCount__ppp12, explorer/literalDotCount__le
--   explorer/literalDotCount__l7, explorer/literalDotCount__l12, explorer/literalDotCount__l12_3
--   explorer/literalDotCount__lle, explorer/literalDotCount__l_e, explorer/literalDotCount__l_p12
--   explorer/literalDotCount__p_l12, explorer/literalDotCount__pl1, explorer/special__strCount
--   spec/empty-count-one-arg, spec/empty-count-two-args, spec/count-scalar-and-string
--   spec/builtin-fixed-collection-arity, spec/variadic-selection-shares-the-positional-view
--   spec/list-builtin-collection
def p15_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p15_0 "count" == .property 1
#guard elaboratesToParameter p15_0 "count" == false

-- explorer/dotCount__e: x = () \n x.count
-- the same levels and decisions, 33 more:
--   explorer/dotCount__n0, explorer/dotCount__n1, explorer/dotCount__bt, explorer/dotCount__bf
--   explorer/dotCount__pbt, explorer/dotCount__pbt_e, explorer/dotCount__pbt_1, explorer/dotCount__lbt
--   explorer/dotCount__lbt_bf, explorer/dotCount__lpbt_1, explorer/dotCount__p1, explorer/dotCount__p12
--   explorer/dotCount__p123, explorer/dotCount__pee, explorer/dotCount__pe1, explorer/dotCount__p1e
--   explorer/dotCount__p12_3, explorer/dotCount__p12_34, explorer/dotCount__pe_12, explorer/dotCount__ppe1_2
--   explorer/dotCount__p12_e, explorer/dotCount__ppe, explorer/dotCount__pp1, explorer/dotCount__ppp12
--   explorer/dotCount__le, explorer/dotCount__l7, explorer/dotCount__l12, explorer/dotCount__l12_3
--   explorer/dotCount__lle, explorer/dotCount__l_e, explorer/dotCount__l_p12, explorer/dotCount__p_l12
--   explorer/dotCount__pl1
def p16_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p16_1 : List OwnerLevel := { parameters := [], properties := [] } :: p16_0
#guard selectOwnedDeclaration p16_0 "x" == .property 0
#guard elaboratesToParameter p16_0 "x" == false
#guard selectOwnedDeclaration p16_0 "count" == .property 1
#guard elaboratesToParameter p16_0 "count" == false

-- explorer/eqSelf__e: x = () \n x == x
-- the same levels and decisions, 67 more:
--   explorer/eqSelf__n0, explorer/eqSelf__n1, explorer/eqSelf__bt, explorer/eqSelf__bf, explorer/eqSelf__pbt
--   explorer/eqSelf__pbt_e, explorer/eqSelf__pbt_1, explorer/eqSelf__lbt, explorer/eqSelf__lbt_bf
--   explorer/eqSelf__lpbt_1, explorer/eqSelf__p1, explorer/eqSelf__p12, explorer/eqSelf__p123
--   explorer/eqSelf__pee, explorer/eqSelf__pe1, explorer/eqSelf__p1e, explorer/eqSelf__p12_3
--   explorer/eqSelf__p12_34, explorer/eqSelf__pe_12, explorer/eqSelf__ppe1_2, explorer/eqSelf__p12_e
--   explorer/eqSelf__ppe, explorer/eqSelf__pp1, explorer/eqSelf__ppp12, explorer/eqSelf__le, explorer/eqSelf__l7
--   explorer/eqSelf__l12, explorer/eqSelf__l12_3, explorer/eqSelf__lle, explorer/eqSelf__l_e
--   explorer/eqSelf__l_p12, explorer/eqSelf__p_l12, explorer/eqSelf__pl1, explorer/neqSelf__e
--   explorer/neqSelf__n0, explorer/neqSelf__n1, explorer/neqSelf__bt, explorer/neqSelf__bf, explorer/neqSelf__pbt
--   explorer/neqSelf__pbt_e, explorer/neqSelf__pbt_1, explorer/neqSelf__lbt, explorer/neqSelf__lbt_bf
--   explorer/neqSelf__lpbt_1, explorer/neqSelf__p1, explorer/neqSelf__p12, explorer/neqSelf__p123
--   explorer/neqSelf__pee, explorer/neqSelf__pe1, explorer/neqSelf__p1e, explorer/neqSelf__p12_3
--   explorer/neqSelf__p12_34, explorer/neqSelf__pe_12, explorer/neqSelf__ppe1_2, explorer/neqSelf__p12_e
--   explorer/neqSelf__ppe, explorer/neqSelf__pp1, explorer/neqSelf__ppp12, explorer/neqSelf__le
--   explorer/neqSelf__l7, explorer/neqSelf__l12, explorer/neqSelf__l12_3, explorer/neqSelf__lle
--   explorer/neqSelf__l_e, explorer/neqSelf__l_p12, explorer/neqSelf__p_l12, explorer/neqSelf__pl1
def p17_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p17_1 : List OwnerLevel := { parameters := [], properties := [] } :: p17_0
#guard selectOwnedDeclaration p17_0 "x" == .property 0 -- x2
#guard elaboratesToParameter p17_0 "x" == false -- x2

-- explorer/eqIdentity__e: I(a) = a \n x = () \n x == I(x)
-- the same levels and decisions, 33 more:
--   explorer/eqIdentity__n0, explorer/eqIdentity__n1, explorer/eqIdentity__bt, explorer/eqIdentity__bf
--   explorer/eqIdentity__pbt, explorer/eqIdentity__pbt_e, explorer/eqIdentity__pbt_1, explorer/eqIdentity__lbt
--   explorer/eqIdentity__lbt_bf, explorer/eqIdentity__lpbt_1, explorer/eqIdentity__p1, explorer/eqIdentity__p12
--   explorer/eqIdentity__p123, explorer/eqIdentity__pee, explorer/eqIdentity__pe1, explorer/eqIdentity__p1e
--   explorer/eqIdentity__p12_3, explorer/eqIdentity__p12_34, explorer/eqIdentity__pe_12
--   explorer/eqIdentity__ppe1_2, explorer/eqIdentity__p12_e, explorer/eqIdentity__ppe, explorer/eqIdentity__pp1
--   explorer/eqIdentity__ppp12, explorer/eqIdentity__le, explorer/eqIdentity__l7, explorer/eqIdentity__l12
--   explorer/eqIdentity__l12_3, explorer/eqIdentity__lle, explorer/eqIdentity__l_e, explorer/eqIdentity__l_p12
--   explorer/eqIdentity__p_l12, explorer/eqIdentity__pl1
def p18_0 : List OwnerLevel := { parameters := [], properties := ["x", "I"] } :: prelude
def p18_1 : List OwnerLevel := { parameters := [], properties := [] } :: p18_0
def p18_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p18_0
#guard selectOwnedDeclaration p18_2 "a" == .parameter 0
#guard elaboratesToParameter p18_2 "a" == true
#guard selectOwnedDeclaration p18_0 "x" == .property 0 -- x2
#guard elaboratesToParameter p18_0 "x" == false -- x2
#guard selectOwnedDeclaration p18_0 "I" == .property 0
#guard elaboratesToParameter p18_0 "I" == false

-- explorer/identity__e: I(a) = a \n x = () \n I(x)
-- the same levels and decisions, 33 more:
--   explorer/identity__n0, explorer/identity__n1, explorer/identity__bt, explorer/identity__bf
--   explorer/identity__pbt, explorer/identity__pbt_e, explorer/identity__pbt_1, explorer/identity__lbt
--   explorer/identity__lbt_bf, explorer/identity__lpbt_1, explorer/identity__p1, explorer/identity__p12
--   explorer/identity__p123, explorer/identity__pee, explorer/identity__pe1, explorer/identity__p1e
--   explorer/identity__p12_3, explorer/identity__p12_34, explorer/identity__pe_12, explorer/identity__ppe1_2
--   explorer/identity__p12_e, explorer/identity__ppe, explorer/identity__pp1, explorer/identity__ppp12
--   explorer/identity__le, explorer/identity__l7, explorer/identity__l12, explorer/identity__l12_3
--   explorer/identity__lle, explorer/identity__l_e, explorer/identity__l_p12, explorer/identity__p_l12
--   explorer/identity__pl1
def p19_0 : List OwnerLevel := { parameters := [], properties := ["x", "I"] } :: prelude
def p19_1 : List OwnerLevel := { parameters := [], properties := [] } :: p19_0
def p19_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p19_0
#guard selectOwnedDeclaration p19_2 "a" == .parameter 0
#guard elaboratesToParameter p19_2 "a" == true
#guard selectOwnedDeclaration p19_0 "I" == .property 0
#guard elaboratesToParameter p19_0 "I" == false
#guard selectOwnedDeclaration p19_0 "x" == .property 0
#guard elaboratesToParameter p19_0 "x" == false

-- explorer/identityTwice__e: I(a) = a \n x = () \n I(I(x))
-- the same levels and decisions, 33 more:
--   explorer/identityTwice__n0, explorer/identityTwice__n1, explorer/identityTwice__bt, explorer/identityTwice__bf
--   explorer/identityTwice__pbt, explorer/identityTwice__pbt_e, explorer/identityTwice__pbt_1
--   explorer/identityTwice__lbt, explorer/identityTwice__lbt_bf, explorer/identityTwice__lpbt_1
--   explorer/identityTwice__p1, explorer/identityTwice__p12, explorer/identityTwice__p123
--   explorer/identityTwice__pee, explorer/identityTwice__pe1, explorer/identityTwice__p1e
--   explorer/identityTwice__p12_3, explorer/identityTwice__p12_34, explorer/identityTwice__pe_12
--   explorer/identityTwice__ppe1_2, explorer/identityTwice__p12_e, explorer/identityTwice__ppe
--   explorer/identityTwice__pp1, explorer/identityTwice__ppp12, explorer/identityTwice__le
--   explorer/identityTwice__l7, explorer/identityTwice__l12, explorer/identityTwice__l12_3
--   explorer/identityTwice__lle, explorer/identityTwice__l_e, explorer/identityTwice__l_p12
--   explorer/identityTwice__p_l12, explorer/identityTwice__pl1
def p20_0 : List OwnerLevel := { parameters := [], properties := ["x", "I"] } :: prelude
def p20_1 : List OwnerLevel := { parameters := [], properties := [] } :: p20_0
def p20_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p20_0
#guard selectOwnedDeclaration p20_2 "a" == .parameter 0
#guard elaboratesToParameter p20_2 "a" == true
#guard selectOwnedDeclaration p20_0 "I" == .property 0 -- x2
#guard elaboratesToParameter p20_0 "I" == false -- x2
#guard selectOwnedDeclaration p20_0 "x" == .property 0
#guard elaboratesToParameter p20_0 "x" == false

-- explorer/propChain__e: P = () \n Q = P \n Q
-- the same levels and decisions, 33 more:
--   explorer/propChain__n0, explorer/propChain__n1, explorer/propChain__bt, explorer/propChain__bf
--   explorer/propChain__pbt, explorer/propChain__pbt_e, explorer/propChain__pbt_1, explorer/propChain__lbt
--   explorer/propChain__lbt_bf, explorer/propChain__lpbt_1, explorer/propChain__p1, explorer/propChain__p12
--   explorer/propChain__p123, explorer/propChain__pee, explorer/propChain__pe1, explorer/propChain__p1e
--   explorer/propChain__p12_3, explorer/propChain__p12_34, explorer/propChain__pe_12, explorer/propChain__ppe1_2
--   explorer/propChain__p12_e, explorer/propChain__ppe, explorer/propChain__pp1, explorer/propChain__ppp12
--   explorer/propChain__le, explorer/propChain__l7, explorer/propChain__l12, explorer/propChain__l12_3
--   explorer/propChain__lle, explorer/propChain__l_e, explorer/propChain__l_p12, explorer/propChain__p_l12
--   explorer/propChain__pl1
def p21_0 : List OwnerLevel := { parameters := [], properties := ["P", "Q"] } :: prelude
def p21_1 : List OwnerLevel := { parameters := [], properties := [] } :: p21_0
def p21_2 : List OwnerLevel := { parameters := [], properties := [] } :: p21_0
#guard selectOwnedDeclaration p21_2 "P" == .property 1
#guard elaboratesToParameter p21_2 "P" == false
#guard selectOwnedDeclaration p21_0 "Q" == .property 0
#guard elaboratesToParameter p21_0 "Q" == false

-- explorer/take1__e: take((), 1)
-- the same levels and decisions, 74 more:
--   explorer/take1__n0, explorer/take1__n1, explorer/take1__bt, explorer/take1__bf, explorer/take1__pbt
--   explorer/take1__pbt_e, explorer/take1__pbt_1, explorer/take1__lbt, explorer/take1__lbt_bf
--   explorer/take1__lpbt_1, explorer/take1__p1, explorer/take1__p12, explorer/take1__p123, explorer/take1__pee
--   explorer/take1__pe1, explorer/take1__p1e, explorer/take1__p12_3, explorer/take1__p12_34, explorer/take1__pe_12
--   explorer/take1__ppe1_2, explorer/take1__p12_e, explorer/take1__ppe, explorer/take1__pp1, explorer/take1__ppp12
--   explorer/take1__le, explorer/take1__l7, explorer/take1__l12, explorer/take1__l12_3, explorer/take1__lle
--   explorer/take1__l_e, explorer/take1__l_p12, explorer/take1__p_l12, explorer/take1__pl1, explorer/take9__e
--   explorer/take9__n0, explorer/take9__n1, explorer/take9__bt, explorer/take9__bf, explorer/take9__pbt
--   explorer/take9__pbt_e, explorer/take9__pbt_1, explorer/take9__lbt, explorer/take9__lbt_bf
--   explorer/take9__lpbt_1, explorer/take9__p1, explorer/take9__p12, explorer/take9__p123, explorer/take9__pee
--   explorer/take9__pe1, explorer/take9__p1e, explorer/take9__p12_3, explorer/take9__p12_34, explorer/take9__pe_12
--   explorer/take9__ppe1_2, explorer/take9__p12_e, explorer/take9__ppe, explorer/take9__pp1, explorer/take9__ppp12
--   explorer/take9__le, explorer/take9__l7, explorer/take9__l12, explorer/take9__l12_3, explorer/take9__lle
--   explorer/take9__l_e, explorer/take9__l_p12, explorer/take9__p_l12, explorer/take9__pl1
--   explorer/special__takeOneSurvivorPair, explorer/special__takeOneSurvivorPairEq, explorer/special__takeEmpties
--   spec/need-collection-builtin-demands-its-collection-first, spec/take-prefix, spec/take-single-survivor
--   spec/take-zero-empty
def p22_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p22_0 "take" == .property 1
#guard elaboratesToParameter p22_0 "take" == false

-- explorer/skip1__e: skip((), 1)
-- the same levels and decisions, 35 more:
--   explorer/skip1__n0, explorer/skip1__n1, explorer/skip1__bt, explorer/skip1__bf, explorer/skip1__pbt
--   explorer/skip1__pbt_e, explorer/skip1__pbt_1, explorer/skip1__lbt, explorer/skip1__lbt_bf
--   explorer/skip1__lpbt_1, explorer/skip1__p1, explorer/skip1__p12, explorer/skip1__p123, explorer/skip1__pee
--   explorer/skip1__pe1, explorer/skip1__p1e, explorer/skip1__p12_3, explorer/skip1__p12_34, explorer/skip1__pe_12
--   explorer/skip1__ppe1_2, explorer/skip1__p12_e, explorer/skip1__ppe, explorer/skip1__pp1, explorer/skip1__ppp12
--   explorer/skip1__le, explorer/skip1__l7, explorer/skip1__l12, explorer/skip1__l12_3, explorer/skip1__lle
--   explorer/skip1__l_e, explorer/skip1__l_p12, explorer/skip1__p_l12, explorer/skip1__pl1
--   explorer/special__skipToOnePair, spec/skip-prefix
def p23_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p23_0 "skip" == .property 1
#guard elaboratesToParameter p23_0 "skip" == false

-- explorer/distinct__e: distinct(())
-- the same levels and decisions, 39 more:
--   explorer/distinct__n0, explorer/distinct__n1, explorer/distinct__bt, explorer/distinct__bf
--   explorer/distinct__pbt, explorer/distinct__pbt_e, explorer/distinct__pbt_1, explorer/distinct__lbt
--   explorer/distinct__lbt_bf, explorer/distinct__lpbt_1, explorer/distinct__p1, explorer/distinct__p12
--   explorer/distinct__p123, explorer/distinct__pee, explorer/distinct__pe1, explorer/distinct__p1e
--   explorer/distinct__p12_3, explorer/distinct__p12_34, explorer/distinct__pe_12, explorer/distinct__ppe1_2
--   explorer/distinct__p12_e, explorer/distinct__ppe, explorer/distinct__pp1, explorer/distinct__ppp12
--   explorer/distinct__le, explorer/distinct__l7, explorer/distinct__l12, explorer/distinct__l12_3
--   explorer/distinct__lle, explorer/distinct__l_e, explorer/distinct__l_p12, explorer/distinct__p_l12
--   explorer/distinct__pl1, explorer/special__distinctEmpties, explorer/special__distinctPairsToOne
--   spec/boolean-values-and-equality, spec/distinct-preserves-first, spec/distinct-structural-pairs
--   spec/distinct-empties-collapse
def p24_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p24_0 "distinct" == .property 1
#guard elaboratesToParameter p24_0 "distinct" == false

-- explorer/order__e: order(())
-- the same levels and decisions, 39 more:
--   explorer/order__n0, explorer/order__n1, explorer/order__bt, explorer/order__bf, explorer/order__pbt
--   explorer/order__pbt_e, explorer/order__pbt_1, explorer/order__lbt, explorer/order__lbt_bf
--   explorer/order__lpbt_1, explorer/order__p1, explorer/order__p12, explorer/order__p123, explorer/order__pee
--   explorer/order__pe1, explorer/order__p1e, explorer/order__p12_3, explorer/order__p12_34, explorer/order__pe_12
--   explorer/order__ppe1_2, explorer/order__p12_e, explorer/order__ppe, explorer/order__pp1, explorer/order__ppp12
--   explorer/order__le, explorer/order__l7, explorer/order__l12, explorer/order__l12_3, explorer/order__lle
--   explorer/order__l_e, explorer/order__l_p12, explorer/order__p_l12, explorer/order__pl1
--   explorer/special__orderSingle, explorer/special__orderEmpty, explorer/special__orderIndex0
--   spec/order-sorts-atoms, spec/order-rejects-non-numeric, spec/order-is-stable
def p25_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p25_0 "order" == .property 1
#guard elaboratesToParameter p25_0 "order" == false

-- explorer/mapId__e: M(a) = a \n map((), M)
-- the same levels and decisions, 35 more:
--   explorer/mapId__n0, explorer/mapId__n1, explorer/mapId__bt, explorer/mapId__bf, explorer/mapId__pbt
--   explorer/mapId__pbt_e, explorer/mapId__pbt_1, explorer/mapId__lbt, explorer/mapId__lbt_bf
--   explorer/mapId__lpbt_1, explorer/mapId__p1, explorer/mapId__p12, explorer/mapId__p123, explorer/mapId__pee
--   explorer/mapId__pe1, explorer/mapId__p1e, explorer/mapId__p12_3, explorer/mapId__p12_34, explorer/mapId__pe_12
--   explorer/mapId__ppe1_2, explorer/mapId__p12_e, explorer/mapId__ppe, explorer/mapId__pp1, explorer/mapId__ppp12
--   explorer/mapId__le, explorer/mapId__l7, explorer/mapId__l12, explorer/mapId__l12_3, explorer/mapId__lle
--   explorer/mapId__l_e, explorer/mapId__l_p12, explorer/mapId__p_l12, explorer/mapId__pl1
--   explorer/special__mapToOne, spec/map-single-item
def p26_0 : List OwnerLevel := { parameters := [], properties := ["M"] } :: prelude
def p26_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p26_0
#guard selectOwnedDeclaration p26_1 "a" == .parameter 0
#guard elaboratesToParameter p26_1 "a" == true
#guard selectOwnedDeclaration p26_0 "map" == .property 1
#guard elaboratesToParameter p26_0 "map" == false
#guard selectOwnedDeclaration p26_0 "M" == .property 0
#guard elaboratesToParameter p26_0 "M" == false

-- explorer/patternHead__e: P((h, *t)) = [h, t] \n P(())
-- the same levels and decisions, 67 more:
--   explorer/patternHead__n0, explorer/patternHead__n1, explorer/patternHead__bt, explorer/patternHead__bf
--   explorer/patternHead__pbt, explorer/patternHead__pbt_e, explorer/patternHead__pbt_1, explorer/patternHead__lbt
--   explorer/patternHead__lbt_bf, explorer/patternHead__lpbt_1, explorer/patternHead__p1
--   explorer/patternHead__p12, explorer/patternHead__p123, explorer/patternHead__pee, explorer/patternHead__pe1
--   explorer/patternHead__p1e, explorer/patternHead__p12_3, explorer/patternHead__p12_34
--   explorer/patternHead__pe_12, explorer/patternHead__ppe1_2, explorer/patternHead__p12_e
--   explorer/patternHead__ppe, explorer/patternHead__pp1, explorer/patternHead__ppp12, explorer/patternHead__le
--   explorer/patternHead__l7, explorer/patternHead__l12, explorer/patternHead__l12_3, explorer/patternHead__lle
--   explorer/patternHead__l_e, explorer/patternHead__l_p12, explorer/patternHead__p_l12, explorer/patternHead__pl1
--   explorer/listPatternHead__e, explorer/listPatternHead__n0, explorer/listPatternHead__n1
--   explorer/listPatternHead__bt, explorer/listPatternHead__bf, explorer/listPatternHead__pbt
--   explorer/listPatternHead__pbt_e, explorer/listPatternHead__pbt_1, explorer/listPatternHead__lbt
--   explorer/listPatternHead__lbt_bf, explorer/listPatternHead__lpbt_1, explorer/listPatternHead__p1
--   explorer/listPatternHead__p12, explorer/listPatternHead__p123, explorer/listPatternHead__pee
--   explorer/listPatternHead__pe1, explorer/listPatternHead__p1e, explorer/listPatternHead__p12_3
--   explorer/listPatternHead__p12_34, explorer/listPatternHead__pe_12, explorer/listPatternHead__ppe1_2
--   explorer/listPatternHead__p12_e, explorer/listPatternHead__ppe, explorer/listPatternHead__pp1
--   explorer/listPatternHead__ppp12, explorer/listPatternHead__le, explorer/listPatternHead__l7
--   explorer/listPatternHead__l12, explorer/listPatternHead__l12_3, explorer/listPatternHead__lle
--   explorer/listPatternHead__l_e, explorer/listPatternHead__l_p12, explorer/listPatternHead__p_l12
--   explorer/listPatternHead__pl1
def p27_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p27_1 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p27_0
#guard selectOwnedDeclaration p27_1 "h" == .parameter 0
#guard elaboratesToParameter p27_1 "h" == true
#guard selectOwnedDeclaration p27_1 "t" == .parameter 0
#guard elaboratesToParameter p27_1 "t" == true
#guard selectOwnedDeclaration p27_0 "P" == .property 0
#guard elaboratesToParameter p27_0 "P" == false

-- explorer/patternHeadMap__e: P((h, *t)) = [h, t] \n map([()], P)
-- the same levels and decisions, 67 more:
--   explorer/patternHeadMap__n0, explorer/patternHeadMap__n1, explorer/patternHeadMap__bt
--   explorer/patternHeadMap__bf, explorer/patternHeadMap__pbt, explorer/patternHeadMap__pbt_e
--   explorer/patternHeadMap__pbt_1, explorer/patternHeadMap__lbt, explorer/patternHeadMap__lbt_bf
--   explorer/patternHeadMap__lpbt_1, explorer/patternHeadMap__p1, explorer/patternHeadMap__p12
--   explorer/patternHeadMap__p123, explorer/patternHeadMap__pee, explorer/patternHeadMap__pe1
--   explorer/patternHeadMap__p1e, explorer/patternHeadMap__p12_3, explorer/patternHeadMap__p12_34
--   explorer/patternHeadMap__pe_12, explorer/patternHeadMap__ppe1_2, explorer/patternHeadMap__p12_e
--   explorer/patternHeadMap__ppe, explorer/patternHeadMap__pp1, explorer/patternHeadMap__ppp12
--   explorer/patternHeadMap__le, explorer/patternHeadMap__l7, explorer/patternHeadMap__l12
--   explorer/patternHeadMap__l12_3, explorer/patternHeadMap__lle, explorer/patternHeadMap__l_e
--   explorer/patternHeadMap__l_p12, explorer/patternHeadMap__p_l12, explorer/patternHeadMap__pl1
--   explorer/listPatternHeadMap__e, explorer/listPatternHeadMap__n0, explorer/listPatternHeadMap__n1
--   explorer/listPatternHeadMap__bt, explorer/listPatternHeadMap__bf, explorer/listPatternHeadMap__pbt
--   explorer/listPatternHeadMap__pbt_e, explorer/listPatternHeadMap__pbt_1, explorer/listPatternHeadMap__lbt
--   explorer/listPatternHeadMap__lbt_bf, explorer/listPatternHeadMap__lpbt_1, explorer/listPatternHeadMap__p1
--   explorer/listPatternHeadMap__p12, explorer/listPatternHeadMap__p123, explorer/listPatternHeadMap__pee
--   explorer/listPatternHeadMap__pe1, explorer/listPatternHeadMap__p1e, explorer/listPatternHeadMap__p12_3
--   explorer/listPatternHeadMap__p12_34, explorer/listPatternHeadMap__pe_12, explorer/listPatternHeadMap__ppe1_2
--   explorer/listPatternHeadMap__p12_e, explorer/listPatternHeadMap__ppe, explorer/listPatternHeadMap__pp1
--   explorer/listPatternHeadMap__ppp12, explorer/listPatternHeadMap__le, explorer/listPatternHeadMap__l7
--   explorer/listPatternHeadMap__l12, explorer/listPatternHeadMap__l12_3, explorer/listPatternHeadMap__lle
--   explorer/listPatternHeadMap__l_e, explorer/listPatternHeadMap__l_p12, explorer/listPatternHeadMap__p_l12
--   explorer/listPatternHeadMap__pl1
def p28_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p28_1 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p28_0
#guard selectOwnedDeclaration p28_1 "h" == .parameter 0
#guard elaboratesToParameter p28_1 "h" == true
#guard selectOwnedDeclaration p28_1 "t" == .parameter 0
#guard elaboratesToParameter p28_1 "t" == true
#guard selectOwnedDeclaration p28_0 "map" == .property 1
#guard elaboratesToParameter p28_0 "map" == false
#guard selectOwnedDeclaration p28_0 "P" == .property 0
#guard elaboratesToParameter p28_0 "P" == false

-- explorer/patternPair__e: P((x, y)) = [x, y] \n P(())
-- the same levels and decisions, 67 more:
--   explorer/patternPair__n0, explorer/patternPair__n1, explorer/patternPair__bt, explorer/patternPair__bf
--   explorer/patternPair__pbt, explorer/patternPair__pbt_e, explorer/patternPair__pbt_1, explorer/patternPair__lbt
--   explorer/patternPair__lbt_bf, explorer/patternPair__lpbt_1, explorer/patternPair__p1
--   explorer/patternPair__p12, explorer/patternPair__p123, explorer/patternPair__pee, explorer/patternPair__pe1
--   explorer/patternPair__p1e, explorer/patternPair__p12_3, explorer/patternPair__p12_34
--   explorer/patternPair__pe_12, explorer/patternPair__ppe1_2, explorer/patternPair__p12_e
--   explorer/patternPair__ppe, explorer/patternPair__pp1, explorer/patternPair__ppp12, explorer/patternPair__le
--   explorer/patternPair__l7, explorer/patternPair__l12, explorer/patternPair__l12_3, explorer/patternPair__lle
--   explorer/patternPair__l_e, explorer/patternPair__l_p12, explorer/patternPair__p_l12, explorer/patternPair__pl1
--   explorer/listPatternPair__e, explorer/listPatternPair__n0, explorer/listPatternPair__n1
--   explorer/listPatternPair__bt, explorer/listPatternPair__bf, explorer/listPatternPair__pbt
--   explorer/listPatternPair__pbt_e, explorer/listPatternPair__pbt_1, explorer/listPatternPair__lbt
--   explorer/listPatternPair__lbt_bf, explorer/listPatternPair__lpbt_1, explorer/listPatternPair__p1
--   explorer/listPatternPair__p12, explorer/listPatternPair__p123, explorer/listPatternPair__pee
--   explorer/listPatternPair__pe1, explorer/listPatternPair__p1e, explorer/listPatternPair__p12_3
--   explorer/listPatternPair__p12_34, explorer/listPatternPair__pe_12, explorer/listPatternPair__ppe1_2
--   explorer/listPatternPair__p12_e, explorer/listPatternPair__ppe, explorer/listPatternPair__pp1
--   explorer/listPatternPair__ppp12, explorer/listPatternPair__le, explorer/listPatternPair__l7
--   explorer/listPatternPair__l12, explorer/listPatternPair__l12_3, explorer/listPatternPair__lle
--   explorer/listPatternPair__l_e, explorer/listPatternPair__l_p12, explorer/listPatternPair__p_l12
--   explorer/listPatternPair__pl1
def p29_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p29_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p29_0
#guard selectOwnedDeclaration p29_1 "x" == .parameter 0
#guard elaboratesToParameter p29_1 "x" == true
#guard selectOwnedDeclaration p29_1 "y" == .parameter 0
#guard elaboratesToParameter p29_1 "y" == true
#guard selectOwnedDeclaration p29_0 "P" == .property 0
#guard elaboratesToParameter p29_0 "P" == false

-- explorer/patternPairMap__e: P((x, y)) = [x, y] \n map([()], P)
-- the same levels and decisions, 67 more:
--   explorer/patternPairMap__n0, explorer/patternPairMap__n1, explorer/patternPairMap__bt
--   explorer/patternPairMap__bf, explorer/patternPairMap__pbt, explorer/patternPairMap__pbt_e
--   explorer/patternPairMap__pbt_1, explorer/patternPairMap__lbt, explorer/patternPairMap__lbt_bf
--   explorer/patternPairMap__lpbt_1, explorer/patternPairMap__p1, explorer/patternPairMap__p12
--   explorer/patternPairMap__p123, explorer/patternPairMap__pee, explorer/patternPairMap__pe1
--   explorer/patternPairMap__p1e, explorer/patternPairMap__p12_3, explorer/patternPairMap__p12_34
--   explorer/patternPairMap__pe_12, explorer/patternPairMap__ppe1_2, explorer/patternPairMap__p12_e
--   explorer/patternPairMap__ppe, explorer/patternPairMap__pp1, explorer/patternPairMap__ppp12
--   explorer/patternPairMap__le, explorer/patternPairMap__l7, explorer/patternPairMap__l12
--   explorer/patternPairMap__l12_3, explorer/patternPairMap__lle, explorer/patternPairMap__l_e
--   explorer/patternPairMap__l_p12, explorer/patternPairMap__p_l12, explorer/patternPairMap__pl1
--   explorer/listPatternPairMap__e, explorer/listPatternPairMap__n0, explorer/listPatternPairMap__n1
--   explorer/listPatternPairMap__bt, explorer/listPatternPairMap__bf, explorer/listPatternPairMap__pbt
--   explorer/listPatternPairMap__pbt_e, explorer/listPatternPairMap__pbt_1, explorer/listPatternPairMap__lbt
--   explorer/listPatternPairMap__lbt_bf, explorer/listPatternPairMap__lpbt_1, explorer/listPatternPairMap__p1
--   explorer/listPatternPairMap__p12, explorer/listPatternPairMap__p123, explorer/listPatternPairMap__pee
--   explorer/listPatternPairMap__pe1, explorer/listPatternPairMap__p1e, explorer/listPatternPairMap__p12_3
--   explorer/listPatternPairMap__p12_34, explorer/listPatternPairMap__pe_12, explorer/listPatternPairMap__ppe1_2
--   explorer/listPatternPairMap__p12_e, explorer/listPatternPairMap__ppe, explorer/listPatternPairMap__pp1
--   explorer/listPatternPairMap__ppp12, explorer/listPatternPairMap__le, explorer/listPatternPairMap__l7
--   explorer/listPatternPairMap__l12, explorer/listPatternPairMap__l12_3, explorer/listPatternPairMap__lle
--   explorer/listPatternPairMap__l_e, explorer/listPatternPairMap__l_p12, explorer/listPatternPairMap__p_l12
--   explorer/listPatternPairMap__pl1
def p30_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p30_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p30_0
#guard selectOwnedDeclaration p30_1 "x" == .parameter 0
#guard elaboratesToParameter p30_1 "x" == true
#guard selectOwnedDeclaration p30_1 "y" == .parameter 0
#guard elaboratesToParameter p30_1 "y" == true
#guard selectOwnedDeclaration p30_0 "map" == .property 1
#guard elaboratesToParameter p30_0 "map" == false
#guard selectOwnedDeclaration p30_0 "P" == .property 0
#guard elaboratesToParameter p30_0 "P" == false

-- explorer/filterKeep__e: T(a) = true \n filter((), T)
-- the same levels and decisions, 33 more:
--   explorer/filterKeep__n0, explorer/filterKeep__n1, explorer/filterKeep__bt, explorer/filterKeep__bf
--   explorer/filterKeep__pbt, explorer/filterKeep__pbt_e, explorer/filterKeep__pbt_1, explorer/filterKeep__lbt
--   explorer/filterKeep__lbt_bf, explorer/filterKeep__lpbt_1, explorer/filterKeep__p1, explorer/filterKeep__p12
--   explorer/filterKeep__p123, explorer/filterKeep__pee, explorer/filterKeep__pe1, explorer/filterKeep__p1e
--   explorer/filterKeep__p12_3, explorer/filterKeep__p12_34, explorer/filterKeep__pe_12
--   explorer/filterKeep__ppe1_2, explorer/filterKeep__p12_e, explorer/filterKeep__ppe, explorer/filterKeep__pp1
--   explorer/filterKeep__ppp12, explorer/filterKeep__le, explorer/filterKeep__l7, explorer/filterKeep__l12
--   explorer/filterKeep__l12_3, explorer/filterKeep__lle, explorer/filterKeep__l_e, explorer/filterKeep__l_p12
--   explorer/filterKeep__p_l12, explorer/filterKeep__pl1
def p31_0 : List OwnerLevel := { parameters := [], properties := ["T"] } :: prelude
def p31_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p31_0
#guard selectOwnedDeclaration p31_0 "filter" == .property 1
#guard elaboratesToParameter p31_0 "filter" == false
#guard selectOwnedDeclaration p31_0 "T" == .property 0
#guard elaboratesToParameter p31_0 "T" == false

-- explorer/atoms__e: atoms(())
-- the same levels and decisions, 38 more:
--   explorer/atoms__n0, explorer/atoms__n1, explorer/atoms__bt, explorer/atoms__bf, explorer/atoms__pbt
--   explorer/atoms__pbt_e, explorer/atoms__pbt_1, explorer/atoms__lbt, explorer/atoms__lbt_bf
--   explorer/atoms__lpbt_1, explorer/atoms__p1, explorer/atoms__p12, explorer/atoms__p123, explorer/atoms__pee
--   explorer/atoms__pe1, explorer/atoms__p1e, explorer/atoms__p12_3, explorer/atoms__p12_34, explorer/atoms__pe_12
--   explorer/atoms__ppe1_2, explorer/atoms__p12_e, explorer/atoms__ppe, explorer/atoms__pp1, explorer/atoms__ppp12
--   explorer/atoms__le, explorer/atoms__l7, explorer/atoms__l12, explorer/atoms__l12_3, explorer/atoms__lle
--   explorer/atoms__l_e, explorer/atoms__l_p12, explorer/atoms__p_l12, explorer/atoms__pl1
--   explorer/special__atomsNested, spec/atoms-recursive-flatten, spec/atoms-exact-list-result
--   spec/atoms-list-traversal, spec/atoms-mixed-traversal
def p32_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p32_0 "atoms" == .property 1
#guard elaboratesToParameter p32_0 "atoms" == false

-- explorer/takeCapture__e: x = take((), 1) \n x
-- the same levels and decisions, 34 more:
--   explorer/takeCapture__n0, explorer/takeCapture__n1, explorer/takeCapture__bt, explorer/takeCapture__bf
--   explorer/takeCapture__pbt, explorer/takeCapture__pbt_e, explorer/takeCapture__pbt_1, explorer/takeCapture__lbt
--   explorer/takeCapture__lbt_bf, explorer/takeCapture__lpbt_1, explorer/takeCapture__p1
--   explorer/takeCapture__p12, explorer/takeCapture__p123, explorer/takeCapture__pee, explorer/takeCapture__pe1
--   explorer/takeCapture__p1e, explorer/takeCapture__p12_3, explorer/takeCapture__p12_34
--   explorer/takeCapture__pe_12, explorer/takeCapture__ppe1_2, explorer/takeCapture__p12_e
--   explorer/takeCapture__ppe, explorer/takeCapture__pp1, explorer/takeCapture__ppp12, explorer/takeCapture__le
--   explorer/takeCapture__l7, explorer/takeCapture__l12, explorer/takeCapture__l12_3, explorer/takeCapture__lle
--   explorer/takeCapture__l_e, explorer/takeCapture__l_p12, explorer/takeCapture__p_l12, explorer/takeCapture__pl1
--   spec/builtin-result-reentry
def p33_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p33_1 : List OwnerLevel := { parameters := [], properties := [] } :: p33_0
#guard selectOwnedDeclaration p33_1 "take" == .property 2
#guard elaboratesToParameter p33_1 "take" == false
#guard selectOwnedDeclaration p33_0 "x" == .property 0
#guard elaboratesToParameter p33_0 "x" == false

-- explorer/takeIdentity__e: I(a) = a \n I(take((), 1))
-- the same levels and decisions, 33 more:
--   explorer/takeIdentity__n0, explorer/takeIdentity__n1, explorer/takeIdentity__bt, explorer/takeIdentity__bf
--   explorer/takeIdentity__pbt, explorer/takeIdentity__pbt_e, explorer/takeIdentity__pbt_1
--   explorer/takeIdentity__lbt, explorer/takeIdentity__lbt_bf, explorer/takeIdentity__lpbt_1
--   explorer/takeIdentity__p1, explorer/takeIdentity__p12, explorer/takeIdentity__p123, explorer/takeIdentity__pee
--   explorer/takeIdentity__pe1, explorer/takeIdentity__p1e, explorer/takeIdentity__p12_3
--   explorer/takeIdentity__p12_34, explorer/takeIdentity__pe_12, explorer/takeIdentity__ppe1_2
--   explorer/takeIdentity__p12_e, explorer/takeIdentity__ppe, explorer/takeIdentity__pp1
--   explorer/takeIdentity__ppp12, explorer/takeIdentity__le, explorer/takeIdentity__l7, explorer/takeIdentity__l12
--   explorer/takeIdentity__l12_3, explorer/takeIdentity__lle, explorer/takeIdentity__l_e
--   explorer/takeIdentity__l_p12, explorer/takeIdentity__p_l12, explorer/takeIdentity__pl1
def p34_0 : List OwnerLevel := { parameters := [], properties := ["I"] } :: prelude
def p34_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p34_0
#guard selectOwnedDeclaration p34_1 "a" == .parameter 0
#guard elaboratesToParameter p34_1 "a" == true
#guard selectOwnedDeclaration p34_0 "I" == .property 0
#guard elaboratesToParameter p34_0 "I" == false
#guard selectOwnedDeclaration p34_0 "take" == .property 1
#guard elaboratesToParameter p34_0 "take" == false

-- explorer/takeCount__e: count(take((), 1))
-- the same levels and decisions, 34 more:
--   explorer/takeCount__n0, explorer/takeCount__n1, explorer/takeCount__bt, explorer/takeCount__bf
--   explorer/takeCount__pbt, explorer/takeCount__pbt_e, explorer/takeCount__pbt_1, explorer/takeCount__lbt
--   explorer/takeCount__lbt_bf, explorer/takeCount__lpbt_1, explorer/takeCount__p1, explorer/takeCount__p12
--   explorer/takeCount__p123, explorer/takeCount__pee, explorer/takeCount__pe1, explorer/takeCount__p1e
--   explorer/takeCount__p12_3, explorer/takeCount__p12_34, explorer/takeCount__pe_12, explorer/takeCount__ppe1_2
--   explorer/takeCount__p12_e, explorer/takeCount__ppe, explorer/takeCount__pp1, explorer/takeCount__ppp12
--   explorer/takeCount__le, explorer/takeCount__l7, explorer/takeCount__l12, explorer/takeCount__l12_3
--   explorer/takeCount__lle, explorer/takeCount__l_e, explorer/takeCount__l_p12, explorer/takeCount__p_l12
--   explorer/takeCount__pl1, explorer/special__takeOneSurvivorPairCount
def p35_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p35_0 "count" == .property 1
#guard elaboratesToParameter p35_0 "count" == false
#guard selectOwnedDeclaration p35_0 "take" == .property 1
#guard elaboratesToParameter p35_0 "take" == false

-- explorer/takeCollecting__e: G(*a) = a \n G(take((), 1))
-- the same levels and decisions, 33 more:
--   explorer/takeCollecting__n0, explorer/takeCollecting__n1, explorer/takeCollecting__bt
--   explorer/takeCollecting__bf, explorer/takeCollecting__pbt, explorer/takeCollecting__pbt_e
--   explorer/takeCollecting__pbt_1, explorer/takeCollecting__lbt, explorer/takeCollecting__lbt_bf
--   explorer/takeCollecting__lpbt_1, explorer/takeCollecting__p1, explorer/takeCollecting__p12
--   explorer/takeCollecting__p123, explorer/takeCollecting__pee, explorer/takeCollecting__pe1
--   explorer/takeCollecting__p1e, explorer/takeCollecting__p12_3, explorer/takeCollecting__p12_34
--   explorer/takeCollecting__pe_12, explorer/takeCollecting__ppe1_2, explorer/takeCollecting__p12_e
--   explorer/takeCollecting__ppe, explorer/takeCollecting__pp1, explorer/takeCollecting__ppp12
--   explorer/takeCollecting__le, explorer/takeCollecting__l7, explorer/takeCollecting__l12
--   explorer/takeCollecting__l12_3, explorer/takeCollecting__lle, explorer/takeCollecting__l_e
--   explorer/takeCollecting__l_p12, explorer/takeCollecting__p_l12, explorer/takeCollecting__pl1
def p36_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p36_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p36_0
#guard selectOwnedDeclaration p36_1 "a" == .parameter 0
#guard elaboratesToParameter p36_1 "a" == true
#guard selectOwnedDeclaration p36_0 "G" == .property 0
#guard elaboratesToParameter p36_0 "G" == false
#guard selectOwnedDeclaration p36_0 "take" == .property 1
#guard elaboratesToParameter p36_0 "take" == false

-- explorer/special__multiProp: P = 1, 2, 3 \n P
-- the same levels and decisions, 7 more:
--   explorer/special__multiPropCall, explorer/special__multiPropIndex0, explorer/special__multiPropEq
--   explorer/special__propBodyEmptySlot, explorer/special__eqSpreadSeqLiteral, spec/property-call-boundary
--   spec/newline-grammar-priority-continuation
def p37_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p37_1 : List OwnerLevel := { parameters := [], properties := [] } :: p37_0
#guard selectOwnedDeclaration p37_0 "P" == .property 0
#guard elaboratesToParameter p37_0 "P" == false

-- explorer/special__multiPropCount: P = 1, 2, 3 \n count(P)
def p38_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p38_1 : List OwnerLevel := { parameters := [], properties := [] } :: p38_0
#guard selectOwnedDeclaration p38_0 "count" == .property 1
#guard elaboratesToParameter p38_0 "count" == false
#guard selectOwnedDeclaration p38_0 "P" == .property 0
#guard elaboratesToParameter p38_0 "P" == false

-- explorer/special__multiPropDotCount: P = 1, 2, 3 \n P.count
def p39_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p39_1 : List OwnerLevel := { parameters := [], properties := [] } :: p39_0
#guard selectOwnedDeclaration p39_0 "P" == .property 0
#guard elaboratesToParameter p39_0 "P" == false
#guard selectOwnedDeclaration p39_0 "count" == .property 1
#guard elaboratesToParameter p39_0 "count" == false

-- explorer/special__multiCollectingCount: F(*a) = a \n count(F(1, 2, 3))
def p40_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p40_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p40_0
#guard selectOwnedDeclaration p40_1 "a" == .parameter 0
#guard elaboratesToParameter p40_1 "a" == true
#guard selectOwnedDeclaration p40_0 "count" == .property 1
#guard elaboratesToParameter p40_0 "count" == false
#guard selectOwnedDeclaration p40_0 "F" == .property 0
#guard elaboratesToParameter p40_0 "F" == false

-- explorer/special__collectingFwdSum: F(*a) = sum(a) \n F(1, 2, 3)
def p41_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p41_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p41_0
#guard selectOwnedDeclaration p41_1 "sum" == .property 2
#guard elaboratesToParameter p41_1 "sum" == false
#guard selectOwnedDeclaration p41_1 "a" == .parameter 0
#guard elaboratesToParameter p41_1 "a" == true
#guard selectOwnedDeclaration p41_0 "F" == .property 0
#guard elaboratesToParameter p41_0 "F" == false

-- explorer/special__collectingFwdSpread: F(*a) = G(a*) \n G(*b) = b \n F(1, 2, 3)
def p42_0 : List OwnerLevel := { parameters := [], properties := ["F", "G"] } :: prelude
def p42_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p42_0
def p42_2 : List OwnerLevel := { parameters := ["b"], properties := [] } :: p42_0
#guard selectOwnedDeclaration p42_1 "G" == .property 1
#guard elaboratesToParameter p42_1 "G" == false
#guard selectOwnedDeclaration p42_1 "a" == .parameter 0
#guard elaboratesToParameter p42_1 "a" == true
#guard selectOwnedDeclaration p42_2 "b" == .parameter 0
#guard elaboratesToParameter p42_2 "b" == true
#guard selectOwnedDeclaration p42_0 "F" == .property 0
#guard elaboratesToParameter p42_0 "F" == false

-- explorer/special__range13: range(1, 3)
-- the same levels and decisions, 5 more:
--   explorer/special__rangeIndex0, spec/range-inclusive, spec/range-single-value
--   spec/range-integral-bound-quantum, spec/list-index-builtin-results
def p43_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p43_0 "range" == .property 1
#guard elaboratesToParameter p43_0 "range" == false

-- explorer/special__rangeCapture: x = range(1, 3) \n x
def p44_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p44_1 : List OwnerLevel := { parameters := [], properties := [] } :: p44_0
#guard selectOwnedDeclaration p44_1 "range" == .property 2
#guard elaboratesToParameter p44_1 "range" == false
#guard selectOwnedDeclaration p44_0 "x" == .property 0
#guard elaboratesToParameter p44_0 "x" == false

-- explorer/special__rangeCount: count(range(1, 3))
def p45_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p45_0 "count" == .property 1
#guard elaboratesToParameter p45_0 "count" == false
#guard selectOwnedDeclaration p45_0 "range" == .property 1
#guard elaboratesToParameter p45_0 "range" == false

-- explorer/special__filterOneSurvivor: Big(a) = a > 2 \n filter((1, 2, 3), Big)
-- the same levels and decisions, 1 more:
--   spec/filter-single-survivor
def p46_0 : List OwnerLevel := { parameters := [], properties := ["Big"] } :: prelude
def p46_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p46_0
#guard selectOwnedDeclaration p46_1 "a" == .parameter 0
#guard elaboratesToParameter p46_1 "a" == true
#guard selectOwnedDeclaration p46_0 "filter" == .property 1
#guard elaboratesToParameter p46_0 "filter" == false
#guard selectOwnedDeclaration p46_0 "Big" == .property 0
#guard elaboratesToParameter p46_0 "Big" == false

-- explorer/special__filterOneSurvivorCount: Big(a) = a > 2 \n count(filter((1, 2, 3), Big))
def p47_0 : List OwnerLevel := { parameters := [], properties := ["Big"] } :: prelude
def p47_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p47_0
#guard selectOwnedDeclaration p47_1 "a" == .parameter 0
#guard elaboratesToParameter p47_1 "a" == true
#guard selectOwnedDeclaration p47_0 "count" == .property 1
#guard elaboratesToParameter p47_0 "count" == false
#guard selectOwnedDeclaration p47_0 "filter" == .property 1
#guard elaboratesToParameter p47_0 "filter" == false
#guard selectOwnedDeclaration p47_0 "Big" == .property 0
#guard elaboratesToParameter p47_0 "Big" == false

-- explorer/special__filterZeroSurvivors: No(a) = false \n filter((1, 2, 3), No)
-- the same levels and decisions, 1 more:
--   spec/filter-none-empty
def p48_0 : List OwnerLevel := { parameters := [], properties := ["No"] } :: prelude
def p48_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p48_0
#guard selectOwnedDeclaration p48_0 "filter" == .property 1
#guard elaboratesToParameter p48_0 "filter" == false
#guard selectOwnedDeclaration p48_0 "No" == .property 0
#guard elaboratesToParameter p48_0 "No" == false

-- explorer/special__mapPairSwap: Swap(a, b) = b, a \n map(((1, 2), (3, 4)), Swap)
-- the same levels and decisions, 3 more:
--   explorer/special__mapPairSwapOk, explorer/special__mapPairSwapFlatIsArity, spec/map-pair-callback
def p49_0 : List OwnerLevel := { parameters := [], properties := ["Swap"] } :: prelude
def p49_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p49_0
#guard selectOwnedDeclaration p49_1 "b" == .parameter 0
#guard elaboratesToParameter p49_1 "b" == true
#guard selectOwnedDeclaration p49_1 "a" == .parameter 0
#guard elaboratesToParameter p49_1 "a" == true
#guard selectOwnedDeclaration p49_0 "map" == .property 1
#guard elaboratesToParameter p49_0 "map" == false
#guard selectOwnedDeclaration p49_0 "Swap" == .property 0
#guard elaboratesToParameter p49_0 "Swap" == false

-- explorer/special__indexCapturedEq: x = ((1, 2), (3, 4)) \n y = x[0] \n y == (1, 2)
-- the same levels and decisions, 2 more:
--   explorer/special__listIndexCapturedEq, spec/index-captured-requality
def p50_0 : List OwnerLevel := { parameters := [], properties := ["x", "y"] } :: prelude
def p50_1 : List OwnerLevel := { parameters := [], properties := [] } :: p50_0
def p50_2 : List OwnerLevel := { parameters := [], properties := [] } :: p50_0
#guard selectOwnedDeclaration p50_2 "x" == .property 1
#guard elaboratesToParameter p50_2 "x" == false
#guard selectOwnedDeclaration p50_0 "y" == .property 0
#guard elaboratesToParameter p50_0 "y" == false

-- explorer/special__nestedWrittenArg: F(a, b) = a \n F(((1, 2)), 3)
-- the same levels and decisions, 1 more:
--   explorer/special__listFixedCallBoundary
def p51_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p51_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p51_0
#guard selectOwnedDeclaration p51_1 "a" == .parameter 0
#guard elaboratesToParameter p51_1 "a" == true
#guard selectOwnedDeclaration p51_0 "F" == .property 0
#guard elaboratesToParameter p51_0 "F" == false

-- explorer/special__writtenSlotArity: F(a, b) = a + b \n F(((1, 2)))
def p52_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p52_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p52_0
#guard selectOwnedDeclaration p52_1 "a" == .parameter 0
#guard elaboratesToParameter p52_1 "a" == true
#guard selectOwnedDeclaration p52_1 "b" == .parameter 0
#guard elaboratesToParameter p52_1 "b" == true
#guard selectOwnedDeclaration p52_0 "F" == .property 0
#guard elaboratesToParameter p52_0 "F" == false

-- explorer/special__mixedSingleGrouped: F(x, *y, z) = y \n A = (1, 2, 3, 4) \n F(A)
def p53_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p53_1 : List OwnerLevel := { parameters := [], properties := [] } :: p53_0
def p53_2 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p53_0
#guard selectOwnedDeclaration p53_2 "y" == .parameter 0
#guard elaboratesToParameter p53_2 "y" == true
#guard selectOwnedDeclaration p53_0 "F" == .property 0
#guard elaboratesToParameter p53_0 "F" == false
#guard selectOwnedDeclaration p53_0 "A" == .property 0
#guard elaboratesToParameter p53_0 "A" == false

-- explorer/special__sumEmpty: sum(())
def p54_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p54_0 "sum" == .property 1
#guard elaboratesToParameter p54_0 "sum" == false

-- explorer/special__rootSpreadExtra: A = (1, 2) \n A*, 99
-- the same levels and decisions, 10 more:
--   explorer/special__spreadOfSpreadSeqLiteral, explorer/special__listSpreadOfSeqProp
--   explorer/special__listSpreadBetween, explorer/special__listInSeqSpreadKeepsList, spec/empty-capture
--   spec/capture-supply, spec/capture-supply-spread, spec/root-spread-beside-slot
--   spec/line-final-star-attached-at-eof-is-spread, spec/missing-output-not-a-value
def p55_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p55_1 : List OwnerLevel := { parameters := [], properties := [] } :: p55_0
#guard selectOwnedDeclaration p55_0 "A" == .property 0
#guard elaboratesToParameter p55_0 "A" == false

-- explorer/special__loopSpreadHistoryFlat: Step((*history), previous) = (history*, previous + 1), previous + 1 \n Step((1, 2), 2).repeat(2)[0]
def p56_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p56_1 : List OwnerLevel := { parameters := ["history", "previous"], properties := [] } :: p56_0
#guard selectOwnedDeclaration p56_1 "history" == .parameter 0
#guard elaboratesToParameter p56_1 "history" == true
#guard selectOwnedDeclaration p56_1 "previous" == .parameter 0 -- x2
#guard elaboratesToParameter p56_1 "previous" == true -- x2
#guard selectOwnedDeclaration p56_0 "Step" == .property 0
#guard elaboratesToParameter p56_0 "Step" == false
#guard selectOwnedDeclaration p56_0 "repeat" == .property 1
#guard elaboratesToParameter p56_0 "repeat" == false

-- explorer/special__ifBranchSeq: if(true, (1, 2), 3)
-- the same levels and decisions, 1 more:
--   spec/if-arity-is-uniform-across-spellings
def p57_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p57_0 "if" == .property 1
#guard elaboratesToParameter p57_0 "if" == false

-- explorer/special__chainPropertyOperands: P = 2 \n 1 < P < 3, P == P == 2
def p58_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p58_1 : List OwnerLevel := { parameters := [], properties := [] } :: p58_0
#guard selectOwnedDeclaration p58_0 "P" == .property 0 -- x3
#guard elaboratesToParameter p58_0 "P" == false -- x3

-- explorer/special__chainCallOperands: F(x) = x + 1 \n F(0) < F(1) < F(2)
def p59_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p59_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p59_0
#guard selectOwnedDeclaration p59_1 "x" == .parameter 0
#guard elaboratesToParameter p59_1 "x" == true
#guard selectOwnedDeclaration p59_0 "F" == .property 0 -- x3
#guard elaboratesToParameter p59_0 "F" == false -- x3

-- explorer/special__listOfLists: A = [1, 2] \n B = [3, 4] \n [A, B]
-- the same levels and decisions, 6 more:
--   explorer/special__listSpreadConcat, explorer/special__listMixedSpread, spec/eq-structural-nested
--   spec/output-rows-interleave-definitions, spec/star-before-operand-row-is-multiplication
--   spec/star-before-declaration-or-boundary-is-spread
def p60_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p60_1 : List OwnerLevel := { parameters := [], properties := [] } :: p60_0
def p60_2 : List OwnerLevel := { parameters := [], properties := [] } :: p60_0
#guard selectOwnedDeclaration p60_0 "A" == .property 0
#guard elaboratesToParameter p60_0 "A" == false
#guard selectOwnedDeclaration p60_0 "B" == .property 0
#guard elaboratesToParameter p60_0 "B" == false

-- explorer/special__listSpreadCaptureRoundTrip: A = [1, 2, 3] \n B = { A* } \n B == (1, 2, 3)
def p61_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p61_1 : List OwnerLevel := { parameters := [], properties := [] } :: p61_0
def p61_2 : List OwnerLevel := { parameters := [], properties := [] } :: p61_0
#guard selectOwnedDeclaration p61_2 "A" == .property 1
#guard elaboratesToParameter p61_2 "A" == false
#guard selectOwnedDeclaration p61_0 "B" == .property 0
#guard elaboratesToParameter p61_0 "B" == false

-- explorer/special__listCollectingNotSequenceKind: x, *rest = [1, 2, 3] \n rest == (2, 3)
-- the same levels and decisions, 2 more:
--   explorer/special__listCollectingCollectsExactList, spec/decon-collecting-tail
def p62_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "rest"] } :: prelude
def p62_1 : List OwnerLevel := { parameters := [], properties := [] } :: p62_0
def p62_2 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p62_1
def p62_3 : List OwnerLevel := { parameters := [], properties := [] } :: p62_0
def p62_4 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p62_3
#guard selectOwnedDeclaration p62_2 "x" == .parameter 0
#guard elaboratesToParameter p62_2 "x" == true
#guard selectOwnedDeclaration p62_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p62_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p62_4 "rest" == .parameter 0
#guard elaboratesToParameter p62_4 "rest" == true
#guard selectOwnedDeclaration p62_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p62_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p62_0 "rest" == .property 0
#guard elaboratesToParameter p62_0 "rest" == false

-- explorer/special__implicitForwardOrdinarySource: Target(tag, *items) = items \n Use(tag, items) = Target \n Use(0, [1, 2])
def p63_0 : List OwnerLevel := { parameters := [], properties := ["Target", "Use"] } :: prelude
def p63_1 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p63_0
def p63_2 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p63_0
#guard selectOwnedDeclaration p63_1 "items" == .parameter 0
#guard elaboratesToParameter p63_1 "items" == true
#guard selectOwnedDeclaration p63_2 "Target" == .property 1
#guard elaboratesToParameter p63_2 "Target" == false
#guard selectOwnedDeclaration p63_0 "Use" == .property 0
#guard elaboratesToParameter p63_0 "Use" == false

-- explorer/special__callbackSingleCollectingMap: Collect(*items) = items \n [7].map(Collect)
def p64_0 : List OwnerLevel := { parameters := [], properties := ["Collect"] } :: prelude
def p64_1 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p64_0
#guard selectOwnedDeclaration p64_1 "items" == .parameter 0
#guard elaboratesToParameter p64_1 "items" == true
#guard selectOwnedDeclaration p64_0 "map" == .property 1
#guard elaboratesToParameter p64_0 "map" == false
#guard selectOwnedDeclaration p64_0 "Collect" == .property 0
#guard elaboratesToParameter p64_0 "Collect" == false

-- explorer/special__callbackMixedCollectingRow: F(first, *middle, last) = middle \n [(1, 2, 3, 4)].map(F)
-- the same levels and decisions, 1 more:
--   explorer/special__callbackMixedCollectingRowPattern
def p65_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p65_1 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p65_0
#guard selectOwnedDeclaration p65_1 "middle" == .parameter 0
#guard elaboratesToParameter p65_1 "middle" == true
#guard selectOwnedDeclaration p65_0 "map" == .property 1
#guard elaboratesToParameter p65_0 "map" == false
#guard selectOwnedDeclaration p65_0 "F" == .property 0
#guard elaboratesToParameter p65_0 "F" == false

-- explorer/special__callbackCollectingElementIsOneArgument: Cnt(*xs) = xs.count \n map([(10, 7), [10, 7], 20], Cnt)
def p66_0 : List OwnerLevel := { parameters := [], properties := ["Cnt"] } :: prelude
def p66_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p66_0
#guard selectOwnedDeclaration p66_1 "xs" == .parameter 0
#guard elaboratesToParameter p66_1 "xs" == true
#guard selectOwnedDeclaration p66_1 "count" == .property 2
#guard elaboratesToParameter p66_1 "count" == false
#guard selectOwnedDeclaration p66_0 "map" == .property 1
#guard elaboratesToParameter p66_0 "map" == false
#guard selectOwnedDeclaration p66_0 "Cnt" == .property 0
#guard elaboratesToParameter p66_0 "Cnt" == false

-- explorer/special__collectorZeroArgumentCallableFailureIsItsOwn: Bad(*xs) = 1 / 0 \n Coll(*ys) = ys \n Coll(Bad)
def p67_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "Coll"] } :: prelude
def p67_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p67_0
def p67_2 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p67_0
#guard selectOwnedDeclaration p67_2 "ys" == .parameter 0
#guard elaboratesToParameter p67_2 "ys" == true
#guard selectOwnedDeclaration p67_0 "Coll" == .property 0
#guard elaboratesToParameter p67_0 "Coll" == false
#guard selectOwnedDeclaration p67_0 "Bad" == .property 0
#guard elaboratesToParameter p67_0 "Bad" == false

-- explorer/special__listCollectingSpreadCall: F(*a) = a \n A = [1, 2] \n F(A*, 9)
def p68_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p68_1 : List OwnerLevel := { parameters := [], properties := [] } :: p68_0
def p68_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p68_0
#guard selectOwnedDeclaration p68_2 "a" == .parameter 0
#guard elaboratesToParameter p68_2 "a" == true
#guard selectOwnedDeclaration p68_0 "F" == .property 0
#guard elaboratesToParameter p68_0 "F" == false
#guard selectOwnedDeclaration p68_0 "A" == .property 0
#guard elaboratesToParameter p68_0 "A" == false

-- explorer/special__spreadNoOutputBlockRoot: {A = 1}*, 997
-- the same levels and decisions, 2 more:
--   explorer/special__spreadNoOutputBlockList, explorer/special__spreadInnerOwnKept
def p69_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p69_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p69_0
def p69_2 : List OwnerLevel := { parameters := [], properties := [] } :: p69_1

-- explorer/special__spreadNoOutputBlockCallArg: F(a) = a \n F({A = 1}*)
def p70_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p70_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p70_0
def p70_2 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p70_0
def p70_3 : List OwnerLevel := { parameters := [], properties := [] } :: p70_2
#guard selectOwnedDeclaration p70_1 "a" == .parameter 0
#guard elaboratesToParameter p70_1 "a" == true
#guard selectOwnedDeclaration p70_0 "F" == .property 0
#guard elaboratesToParameter p70_0 "F" == false

-- explorer/special__spreadNoOutputResolved: X = {A = 1} \n X*, 997
def p71_0 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p71_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p71_0
def p71_2 : List OwnerLevel := { parameters := [], properties := [] } :: p71_1
#guard selectOwnedDeclaration p71_0 "X" == .property 0
#guard elaboratesToParameter p71_0 "X" == false

-- explorer/special__spreadNestedDependency: G = {A = 1} \n H = G + 1 \n H*, 997
-- the same levels and decisions, 1 more:
--   explorer/special__spreadNestedDependencyCall
def p72_0 : List OwnerLevel := { parameters := [], properties := ["G", "H"] } :: prelude
def p72_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p72_0
def p72_2 : List OwnerLevel := { parameters := [], properties := [] } :: p72_1
def p72_3 : List OwnerLevel := { parameters := [], properties := [] } :: p72_0
#guard selectOwnedDeclaration p72_3 "G" == .property 1
#guard elaboratesToParameter p72_3 "G" == false
#guard selectOwnedDeclaration p72_0 "H" == .property 0
#guard elaboratesToParameter p72_0 "H" == false

-- explorer/special__spreadOwnInvoked: G = {A = 1} \n G()*, 997
-- the same levels and decisions, 2 more:
--   explorer/special__spreadNestedCapture, explorer/special__spreadNestedList
def p73_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p73_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p73_0
def p73_2 : List OwnerLevel := { parameters := [], properties := [] } :: p73_1
#guard selectOwnedDeclaration p73_0 "G" == .property 0
#guard elaboratesToParameter p73_0 "G" == false

-- explorer/special__spreadNestedArgument: F(x) = x \n F({A = 1})*, 997
def p74_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p74_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p74_0
def p74_2 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p74_0
def p74_3 : List OwnerLevel := { parameters := [], properties := [] } :: p74_2
#guard selectOwnedDeclaration p74_1 "x" == .parameter 0
#guard elaboratesToParameter p74_1 "x" == true
#guard selectOwnedDeclaration p74_0 "F" == .property 0
#guard elaboratesToParameter p74_0 "F" == false

-- explorer/special__spreadNestedRow: G = {A = 1} \n { G }*, 997
def p75_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p75_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p75_0
def p75_2 : List OwnerLevel := { parameters := [], properties := [] } :: p75_1
def p75_3 : List OwnerLevel := { parameters := [], properties := [] } :: p75_0
#guard selectOwnedDeclaration p75_3 "G" == .property 1
#guard elaboratesToParameter p75_3 "G" == false

-- explorer/special__spreadNestedBuiltinArgument: G = {A = 1} \n count(G)*, 997
def p76_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p76_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p76_0
def p76_2 : List OwnerLevel := { parameters := [], properties := [] } :: p76_1
#guard selectOwnedDeclaration p76_0 "count" == .property 1
#guard elaboratesToParameter p76_0 "count" == false
#guard selectOwnedDeclaration p76_0 "G" == .property 0
#guard elaboratesToParameter p76_0 "G" == false

-- explorer/special__spreadNestedFamilyMatch: G = {A = 1} \n K(0) = 1 \n K(n) = 2 \n K(G)*, 997
def p77_0 : List OwnerLevel := { parameters := [], properties := ["G", "K"] } :: prelude
def p77_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p77_0
def p77_2 : List OwnerLevel := { parameters := [], properties := [] } :: p77_1
def p77_3 : List OwnerLevel := { parameters := [], properties := [] } :: p77_0
def p77_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p77_0
#guard selectOwnedDeclaration p77_0 "K" == .property 0
#guard elaboratesToParameter p77_0 "K" == false
#guard selectOwnedDeclaration p77_0 "G" == .property 0
#guard elaboratesToParameter p77_0 "G" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family K

-- explorer/special__spreadNestedPatternBinding: G = {A = 1} \n Q((a, b)) = a \n Q(G)*, 997
def p78_0 : List OwnerLevel := { parameters := [], properties := ["G", "Q"] } :: prelude
def p78_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p78_0
def p78_2 : List OwnerLevel := { parameters := [], properties := [] } :: p78_1
def p78_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p78_0
#guard selectOwnedDeclaration p78_3 "a" == .parameter 0
#guard elaboratesToParameter p78_3 "a" == true
#guard selectOwnedDeclaration p78_0 "Q" == .property 0
#guard elaboratesToParameter p78_0 "Q" == false
#guard selectOwnedDeclaration p78_0 "G" == .property 0
#guard elaboratesToParameter p78_0 "G" == false

-- explorer/special__spreadNestedStringReceiver: G = {A = 1} \n G.string*, 997
def p79_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p79_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p79_0
def p79_2 : List OwnerLevel := { parameters := [], properties := [] } :: p79_1
#guard selectOwnedDeclaration p79_0 "G" == .property 0
#guard elaboratesToParameter p79_0 "G" == false
#guard selectOwnedDeclaration p79_0 "string" == .none
#guard elaboratesToParameter p79_0 "string" == false

-- explorer/special__spreadNestedSupplySlot: G = {A = 1} \n H = G + 1 \n count(1, H*)
def p80_0 : List OwnerLevel := { parameters := [], properties := ["G", "H"] } :: prelude
def p80_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p80_0
def p80_2 : List OwnerLevel := { parameters := [], properties := [] } :: p80_1
def p80_3 : List OwnerLevel := { parameters := [], properties := [] } :: p80_0
#guard selectOwnedDeclaration p80_3 "G" == .property 1
#guard elaboratesToParameter p80_3 "G" == false
#guard selectOwnedDeclaration p80_0 "count" == .property 1
#guard elaboratesToParameter p80_0 "count" == false
#guard selectOwnedDeclaration p80_0 "H" == .property 0
#guard elaboratesToParameter p80_0 "H" == false

-- explorer/special__spreadNestedCallbackSlot: G = {A = 1} \n H = G + 1 \n map([], H*)
def p81_0 : List OwnerLevel := { parameters := [], properties := ["G", "H"] } :: prelude
def p81_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p81_0
def p81_2 : List OwnerLevel := { parameters := [], properties := [] } :: p81_1
def p81_3 : List OwnerLevel := { parameters := [], properties := [] } :: p81_0
#guard selectOwnedDeclaration p81_3 "G" == .property 1
#guard elaboratesToParameter p81_3 "G" == false
#guard selectOwnedDeclaration p81_0 "map" == .property 1
#guard elaboratesToParameter p81_0 "map" == false
#guard selectOwnedDeclaration p81_0 "H" == .property 0
#guard elaboratesToParameter p81_0 "H" == false

-- explorer/special__spreadForwardedOwn: P(x) = x* \n P({A = 1})
def p82_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p82_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p82_0
def p82_2 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p82_0
def p82_3 : List OwnerLevel := { parameters := [], properties := [] } :: p82_2
#guard selectOwnedDeclaration p82_1 "x" == .parameter 0
#guard elaboratesToParameter p82_1 "x" == true
#guard selectOwnedDeclaration p82_0 "P" == .property 0
#guard elaboratesToParameter p82_0 "P" == false

-- explorer/special__spreadForwardedNested: G = {A = 1} \n H = G + 1 \n P(x) = x* \n P(H)
def p83_0 : List OwnerLevel := { parameters := [], properties := ["G", "H", "P"] } :: prelude
def p83_1 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p83_0
def p83_2 : List OwnerLevel := { parameters := [], properties := [] } :: p83_1
def p83_3 : List OwnerLevel := { parameters := [], properties := [] } :: p83_0
def p83_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p83_0
#guard selectOwnedDeclaration p83_3 "G" == .property 1
#guard elaboratesToParameter p83_3 "G" == false
#guard selectOwnedDeclaration p83_4 "x" == .parameter 0
#guard elaboratesToParameter p83_4 "x" == true
#guard selectOwnedDeclaration p83_0 "P" == .property 0
#guard elaboratesToParameter p83_0 "P" == false
#guard selectOwnedDeclaration p83_0 "H" == .property 0
#guard elaboratesToParameter p83_0 "H" == false

-- explorer/special__spreadCollectorElement: G = {} \n C(*xs) = xs* \n C(G)
def p84_0 : List OwnerLevel := { parameters := [], properties := ["G", "C"] } :: prelude
def p84_1 : List OwnerLevel := { parameters := [], properties := [] } :: p84_0
def p84_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p84_0
#guard selectOwnedDeclaration p84_2 "xs" == .parameter 0
#guard elaboratesToParameter p84_2 "xs" == true
#guard selectOwnedDeclaration p84_0 "C" == .property 0
#guard elaboratesToParameter p84_0 "C" == false
#guard selectOwnedDeclaration p84_0 "G" == .property 0
#guard elaboratesToParameter p84_0 "G" == false

-- explorer/special__spreadForwardedCollectorElement: G = {} \n P(x) = x* \n C(*xs) = P(xs) \n C(G)
def p85_0 : List OwnerLevel := { parameters := [], properties := ["G", "P", "C"] } :: prelude
def p85_1 : List OwnerLevel := { parameters := [], properties := [] } :: p85_0
def p85_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p85_0
def p85_3 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p85_0
#guard selectOwnedDeclaration p85_2 "x" == .parameter 0
#guard elaboratesToParameter p85_2 "x" == true
#guard selectOwnedDeclaration p85_3 "P" == .property 1
#guard elaboratesToParameter p85_3 "P" == false
#guard selectOwnedDeclaration p85_3 "xs" == .parameter 0
#guard elaboratesToParameter p85_3 "xs" == true
#guard selectOwnedDeclaration p85_0 "C" == .property 0
#guard elaboratesToParameter p85_0 "C" == false
#guard selectOwnedDeclaration p85_0 "G" == .property 0
#guard elaboratesToParameter p85_0 "G" == false

-- explorer/special__listLoneCollectingAssignment: *items = [1, 2, 3]
def p86_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "items"] } :: prelude
def p86_1 : List OwnerLevel := { parameters := [], properties := [] } :: p86_0
def p86_2 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p86_1
#guard selectOwnedDeclaration p86_2 "items" == .parameter 0
#guard elaboratesToParameter p86_2 "items" == true
#guard selectOwnedDeclaration p86_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p86_1 "$deconstruct$0" == false

-- explorer/special__minSeq: min((3, 1, 2))
-- the same levels and decisions, 5 more:
--   explorer/special__minList, explorer/special__minScalar, explorer/special__minEmpty
--   explorer/special__minNestedItem, spec/aggregate-empty-is-domain-error
def p87_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p87_0 "min" == .property 1
#guard elaboratesToParameter p87_0 "min" == false

-- explorer/special__minDot: x = 3, 1, 2 \n x.min
def p88_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p88_1 : List OwnerLevel := { parameters := [], properties := [] } :: p88_0
#guard selectOwnedDeclaration p88_0 "x" == .property 0
#guard elaboratesToParameter p88_0 "x" == false
#guard selectOwnedDeclaration p88_0 "min" == .property 1
#guard elaboratesToParameter p88_0 "min" == false

-- explorer/special__maxSeq: max((3, 1, 2))
-- the same levels and decisions, 2 more:
--   explorer/special__maxList, explorer/special__maxEmpty
def p89_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p89_0 "max" == .property 1
#guard elaboratesToParameter p89_0 "max" == false

-- explorer/special__maxDot: x = 3, 1, 2 \n x.max
def p90_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p90_1 : List OwnerLevel := { parameters := [], properties := [] } :: p90_0
#guard selectOwnedDeclaration p90_0 "x" == .property 0
#guard elaboratesToParameter p90_0 "x" == false
#guard selectOwnedDeclaration p90_0 "max" == .property 1
#guard elaboratesToParameter p90_0 "max" == false

-- explorer/special__firstSeq: first((1, 2, 3))
-- the same levels and decisions, 5 more:
--   explorer/special__firstScalar, explorer/special__firstListElementStaysExact, explorer/special__firstEmptyItem
--   explorer/special__firstEmpty, spec/first-last-empty-is-bad-index
def p91_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p91_0 "first" == .property 1
#guard elaboratesToParameter p91_0 "first" == false

-- explorer/special__firstDot: x = 1, 2, 3 \n x.first
def p92_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p92_1 : List OwnerLevel := { parameters := [], properties := [] } :: p92_0
#guard selectOwnedDeclaration p92_0 "x" == .property 0
#guard elaboratesToParameter p92_0 "x" == false
#guard selectOwnedDeclaration p92_0 "first" == .property 1
#guard elaboratesToParameter p92_0 "first" == false

-- explorer/special__lastSeq: last((1, 2, 3))
-- the same levels and decisions, 2 more:
--   explorer/special__lastListElementStaysExact, explorer/special__lastEmpty
def p93_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p93_0 "last" == .property 1
#guard elaboratesToParameter p93_0 "last" == false

-- explorer/special__orderDescSeq: orderDesc((1, 3, 2))
-- the same levels and decisions, 5 more:
--   explorer/special__orderDescList, explorer/special__orderDescDuplicates, explorer/special__orderDescScalar
--   explorer/special__orderDescEmpty, explorer/special__orderDescString
def p94_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p94_0 "orderDesc" == .property 1
#guard elaboratesToParameter p94_0 "orderDesc" == false

-- explorer/special__orderDescDot: x = 1, 3, 2 \n x.orderDesc
def p95_0 : List OwnerLevel := { parameters := [], properties := ["x"] } :: prelude
def p95_1 : List OwnerLevel := { parameters := [], properties := [] } :: p95_0
#guard selectOwnedDeclaration p95_0 "x" == .property 0
#guard elaboratesToParameter p95_0 "x" == false
#guard selectOwnedDeclaration p95_0 "orderDesc" == .property 1
#guard elaboratesToParameter p95_0 "orderDesc" == false

-- explorer/special__whileCountdown: S(a) = a - 1, a > 1 \n while(S(3))
def p96_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p96_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p96_0
#guard selectOwnedDeclaration p96_1 "a" == .parameter 0 -- x2
#guard elaboratesToParameter p96_1 "a" == true -- x2
#guard selectOwnedDeclaration p96_0 "while" == .property 1
#guard elaboratesToParameter p96_0 "while" == false
#guard selectOwnedDeclaration p96_0 "S" == .property 0
#guard elaboratesToParameter p96_0 "S" == false

-- explorer/special__whileZeroIterations: S(a) = a, 0 \n while(S(5))
-- the same levels and decisions, 2 more:
--   explorer/special__whileEmptyInitialState, explorer/special__whileNonNumericContinuation
def p97_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p97_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p97_0
#guard selectOwnedDeclaration p97_1 "a" == .parameter 0
#guard elaboratesToParameter p97_1 "a" == true
#guard selectOwnedDeclaration p97_0 "while" == .property 1
#guard elaboratesToParameter p97_0 "while" == false
#guard selectOwnedDeclaration p97_0 "S" == .property 0
#guard elaboratesToParameter p97_0 "S" == false

-- explorer/special__whileTwoSlotState: S(a, b) = a + 1, b * 2, a < 3 \n while(S(1, 1))
def p98_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p98_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p98_0
#guard selectOwnedDeclaration p98_1 "a" == .parameter 0 -- x2
#guard elaboratesToParameter p98_1 "a" == true -- x2
#guard selectOwnedDeclaration p98_1 "b" == .parameter 0
#guard elaboratesToParameter p98_1 "b" == true
#guard selectOwnedDeclaration p98_0 "while" == .property 1
#guard elaboratesToParameter p98_0 "while" == false
#guard selectOwnedDeclaration p98_0 "S" == .property 0
#guard elaboratesToParameter p98_0 "S" == false

-- explorer/special__whileDot: S(a) = a - 1, a > 1 \n S(3).while
def p99_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p99_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p99_0
#guard selectOwnedDeclaration p99_1 "a" == .parameter 0 -- x2
#guard elaboratesToParameter p99_1 "a" == true -- x2
#guard selectOwnedDeclaration p99_0 "S" == .property 0
#guard elaboratesToParameter p99_0 "S" == false
#guard selectOwnedDeclaration p99_0 "while" == .property 1
#guard elaboratesToParameter p99_0 "while" == false

-- explorer/special__loopResultIsOneRow: Fibonacci(a, b) = b, a + b \n Fibonacci(0, 1).repeat(10)
-- the same levels and decisions, 2 more:
--   explorer/special__loopResultBesideAnotherRow, explorer/special__loopResultSpreadOpensIt
def p100_0 : List OwnerLevel := { parameters := [], properties := ["Fibonacci"] } :: prelude
def p100_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p100_0
#guard selectOwnedDeclaration p100_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p100_1 "b" == true -- x2
#guard selectOwnedDeclaration p100_1 "a" == .parameter 0
#guard elaboratesToParameter p100_1 "a" == true
#guard selectOwnedDeclaration p100_0 "Fibonacci" == .property 0
#guard elaboratesToParameter p100_0 "Fibonacci" == false
#guard selectOwnedDeclaration p100_0 "repeat" == .property 1
#guard elaboratesToParameter p100_0 "repeat" == false

-- explorer/special__loopZeroSlotResult: Drop(*xs) = { ()* } \n repeat(Drop(5), 1), repeat(Drop(5), 1)*, 9
def p101_0 : List OwnerLevel := { parameters := [], properties := ["Drop"] } :: prelude
def p101_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p101_0
#guard selectOwnedDeclaration p101_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p101_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p101_0 "Drop" == .property 0 -- x2
#guard elaboratesToParameter p101_0 "Drop" == false -- x2

-- explorer/special__repeatedNameStepSpreadRowIsTwoSlots: Dup(x, x) = { (x + 1, x + 1)* } \n Dup(1, 1).repeat(2)
-- the same levels and decisions, 1 more:
--   explorer/special__repeatedNameStepDivergingRowsRebindFails
def p102_0 : List OwnerLevel := { parameters := [], properties := ["Dup"] } :: prelude
def p102_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p102_0
#guard selectOwnedDeclaration p102_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p102_1 "x" == true -- x2
#guard selectOwnedDeclaration p102_0 "Dup" == .property 0
#guard elaboratesToParameter p102_0 "Dup" == false
#guard selectOwnedDeclaration p102_0 "repeat" == .property 1
#guard elaboratesToParameter p102_0 "repeat" == false

-- explorer/special__structuralStepSpreadRowSuppliesItems: Step2((a, b)) = { (b, a + b)* } \n repeat(Step2((0, 1)), 1), Step2((0, 1))
def p103_0 : List OwnerLevel := { parameters := [], properties := ["Step2"] } :: prelude
def p103_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p103_0
#guard selectOwnedDeclaration p103_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p103_1 "b" == true -- x2
#guard selectOwnedDeclaration p103_1 "a" == .parameter 0
#guard elaboratesToParameter p103_1 "a" == true
#guard selectOwnedDeclaration p103_0 "repeat" == .property 1
#guard elaboratesToParameter p103_0 "repeat" == false
#guard selectOwnedDeclaration p103_0 "Step2" == .property 0 -- x2
#guard elaboratesToParameter p103_0 "Step2" == false -- x2

-- explorer/special__structuralStepSpreadRowCannotRebind: Step2((a, b)) = { (b, a + b)* } \n Step2((0, 1)).repeat(2)
def p104_0 : List OwnerLevel := { parameters := [], properties := ["Step2"] } :: prelude
def p104_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p104_0
#guard selectOwnedDeclaration p104_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p104_1 "b" == true -- x2
#guard selectOwnedDeclaration p104_1 "a" == .parameter 0
#guard elaboratesToParameter p104_1 "a" == true
#guard selectOwnedDeclaration p104_0 "Step2" == .property 0
#guard elaboratesToParameter p104_0 "Step2" == false
#guard selectOwnedDeclaration p104_0 "repeat" == .property 1
#guard elaboratesToParameter p104_0 "repeat" == false

-- explorer/special__historyStepSpreadRowEqualsDirectCall: P((*h), n) = { h*, n + 1 } \n repeat(P((1, 2), 0), 1) == P((1, 2), 0)
def p105_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p105_1 : List OwnerLevel := { parameters := ["h", "n"], properties := [] } :: p105_0
#guard selectOwnedDeclaration p105_1 "h" == .parameter 0
#guard elaboratesToParameter p105_1 "h" == true
#guard selectOwnedDeclaration p105_1 "n" == .parameter 0
#guard elaboratesToParameter p105_1 "n" == true
#guard selectOwnedDeclaration p105_0 "repeat" == .property 1
#guard elaboratesToParameter p105_0 "repeat" == false
#guard selectOwnedDeclaration p105_0 "P" == .property 0 -- x2
#guard elaboratesToParameter p105_0 "P" == false -- x2

-- explorer/special__nestedLoopStepRowIsOneSlot: Fibonacci(a, b) = b, a + b \n Two(a, b) = repeat(Fibonacci(a, b), 2) \n Two(0, 1).repeat(3)
-- the same levels and decisions, 2 more:
--   explorer/special__nestedLoopStepRowSpread, spec/loop-nested-step-row-is-one-slot
def p106_0 : List OwnerLevel := { parameters := [], properties := ["Fibonacci", "Two"] } :: prelude
def p106_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p106_0
def p106_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p106_0
#guard selectOwnedDeclaration p106_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p106_1 "b" == true -- x2
#guard selectOwnedDeclaration p106_1 "a" == .parameter 0
#guard elaboratesToParameter p106_1 "a" == true
#guard selectOwnedDeclaration p106_2 "repeat" == .property 2
#guard elaboratesToParameter p106_2 "repeat" == false
#guard selectOwnedDeclaration p106_2 "Fibonacci" == .property 1
#guard elaboratesToParameter p106_2 "Fibonacci" == false
#guard selectOwnedDeclaration p106_2 "a" == .parameter 0
#guard elaboratesToParameter p106_2 "a" == true
#guard selectOwnedDeclaration p106_2 "b" == .parameter 0
#guard elaboratesToParameter p106_2 "b" == true
#guard selectOwnedDeclaration p106_0 "Two" == .property 0
#guard elaboratesToParameter p106_0 "Two" == false
#guard selectOwnedDeclaration p106_0 "repeat" == .property 1
#guard elaboratesToParameter p106_0 "repeat" == false

-- explorer/special__callbackBodyLoopIsOneValue: Fib(x, y) = y, x + y \n [0, 1].map({ repeat(Fib(x, 1), 2) })
def p107_0 : List OwnerLevel := { parameters := [], properties := ["Fib"] } :: prelude
def p107_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p107_0
def p107_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p107_0
#guard selectOwnedDeclaration p107_1 "y" == .parameter 0 -- x2
#guard elaboratesToParameter p107_1 "y" == true -- x2
#guard selectOwnedDeclaration p107_1 "x" == .parameter 0
#guard elaboratesToParameter p107_1 "x" == true
#guard selectOwnedDeclaration p107_0 "map" == .property 1
#guard elaboratesToParameter p107_0 "map" == false
#guard selectOwnedDeclaration p107_2 "repeat" == .property 2
#guard elaboratesToParameter p107_2 "repeat" == false
#guard selectOwnedDeclaration p107_2 "Fib" == .property 1
#guard elaboratesToParameter p107_2 "Fib" == false
#guard selectOwnedDeclaration p107_2 "x" == .parameter 0
#guard elaboratesToParameter p107_2 "x" == true

-- explorer/special__loopStepClauseFamily: Step(0) = 0 \n Step(n) = n - 1 \n repeat(Step(3), 2), Step(3).repeat(5), Step(Step(3))
-- the same levels and decisions, 1 more:
--   spec/loop-step-clause-family
def p108_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p108_1 : List OwnerLevel := { parameters := [], properties := [] } :: p108_0
def p108_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p108_0
#guard selectOwnedDeclaration p108_2 "n" == .parameter 0
#guard elaboratesToParameter p108_2 "n" == true
#guard selectOwnedDeclaration p108_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p108_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p108_0 "Step" == .property 0 -- x4
#guard elaboratesToParameter p108_0 "Step" == false -- x4
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Step

-- explorer/special__loopStepFamilyWhile: Countdown(0) = 0, false \n Countdown(n) = n - 1, true \n while(Countdown(3))
def p109_0 : List OwnerLevel := { parameters := [], properties := ["Countdown"] } :: prelude
def p109_1 : List OwnerLevel := { parameters := [], properties := [] } :: p109_0
def p109_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p109_0
#guard selectOwnedDeclaration p109_2 "n" == .parameter 0
#guard elaboratesToParameter p109_2 "n" == true
#guard selectOwnedDeclaration p109_0 "while" == .property 1
#guard elaboratesToParameter p109_0 "while" == false
#guard selectOwnedDeclaration p109_0 "Countdown" == .property 0
#guard elaboratesToParameter p109_0 "Countdown" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Countdown

-- explorer/special__loopStepFamilyMultiSlot: Gcd(a, 0) = a, 0, false \n Gcd(a, b) = b, a mod b, true \n while(Gcd(48, 18))
def p110_0 : List OwnerLevel := { parameters := [], properties := ["Gcd"] } :: prelude
def p110_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p110_0
def p110_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p110_0
#guard selectOwnedDeclaration p110_1 "a" == .parameter 0
#guard elaboratesToParameter p110_1 "a" == true
#guard selectOwnedDeclaration p110_2 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p110_2 "b" == true -- x2
#guard selectOwnedDeclaration p110_2 "a" == .parameter 0
#guard elaboratesToParameter p110_2 "a" == true
#guard selectOwnedDeclaration p110_0 "while" == .property 1
#guard elaboratesToParameter p110_0 "while" == false
#guard selectOwnedDeclaration p110_0 "Gcd" == .property 0
#guard elaboratesToParameter p110_0 "Gcd" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "a", .litInt 0]), clause (.sequenceValue [.bind "a", .bind "b"])] == some [.capture { name := "a" }, .capture { name := "b" }] -- family Gcd

-- explorer/special__loopStepFamilyRowsAreTheNextState: Two(0) = 9, 9 \n Two(n) = n, n \n repeat(Two(1), 2)
def p111_0 : List OwnerLevel := { parameters := [], properties := ["Two"] } :: prelude
def p111_1 : List OwnerLevel := { parameters := [], properties := [] } :: p111_0
def p111_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p111_0
#guard selectOwnedDeclaration p111_2 "n" == .parameter 0 -- x2
#guard elaboratesToParameter p111_2 "n" == true -- x2
#guard selectOwnedDeclaration p111_0 "repeat" == .property 1
#guard elaboratesToParameter p111_0 "repeat" == false
#guard selectOwnedDeclaration p111_0 "Two" == .property 0
#guard elaboratesToParameter p111_0 "Two" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Two

-- explorer/special__loopStepFamilyNoMatch: F(0) = 1 \n F(1) = 2 \n repeat(F(5), 1)
-- the same levels and decisions, 1 more:
--   spec/loop-step-family-no-match-is-ordinary
def p112_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p112_1 : List OwnerLevel := { parameters := [], properties := [] } :: p112_0
def p112_2 : List OwnerLevel := { parameters := [], properties := [] } :: p112_0
#guard selectOwnedDeclaration p112_0 "repeat" == .property 1
#guard elaboratesToParameter p112_0 "repeat" == false
#guard selectOwnedDeclaration p112_0 "F" == .property 0
#guard elaboratesToParameter p112_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.litInt 1)] == none -- family F

-- explorer/special__loopStepFamilyClauseOrder: F(x) = 1 \n F(0) = 2 \n repeat(F(0), 1), F(0)
def p113_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p113_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p113_0
def p113_2 : List OwnerLevel := { parameters := [], properties := [] } :: p113_0
#guard selectOwnedDeclaration p113_0 "repeat" == .property 1
#guard elaboratesToParameter p113_0 "repeat" == false
#guard selectOwnedDeclaration p113_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p113_0 "F" == false -- x2
#guard familyLiftingSignature? [clause (.bind "x"), clause (.litInt 0)] == some [.capture { name := "x" }] -- family F

-- explorer/special__loopStepFamilyStructural: Sw((a, b)) = (b, a) \n Sw([a, b]) = [b, a] \n repeat(Sw((1, 2)), 1), repeat(Sw([1, 2]), 1)
def p114_0 : List OwnerLevel := { parameters := [], properties := ["Sw"] } :: prelude
def p114_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p114_0
def p114_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p114_0
#guard selectOwnedDeclaration p114_1 "b" == .parameter 0
#guard elaboratesToParameter p114_1 "b" == true
#guard selectOwnedDeclaration p114_1 "a" == .parameter 0
#guard elaboratesToParameter p114_1 "a" == true
#guard selectOwnedDeclaration p114_2 "b" == .parameter 0
#guard elaboratesToParameter p114_2 "b" == true
#guard selectOwnedDeclaration p114_2 "a" == .parameter 0
#guard elaboratesToParameter p114_2 "a" == true
#guard selectOwnedDeclaration p114_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p114_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p114_0 "Sw" == .property 0 -- x2
#guard elaboratesToParameter p114_0 "Sw" == false -- x2
#guard familyLiftingSignature? [clause (.sequenceValue [.sequenceValue [.bind "a", .bind "b"]]), clause (.sequenceValue [.listValue [.bind "a", .bind "b"]])] == none -- family Sw

-- explorer/special__loopStepFamilyRepeatedName: E(x, x) = 0, 0 \n E(a, b) = a + 1, b \n repeat(E(0, 2), 3)
def p115_0 : List OwnerLevel := { parameters := [], properties := ["E"] } :: prelude
def p115_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p115_0
def p115_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p115_0
#guard selectOwnedDeclaration p115_2 "a" == .parameter 0
#guard elaboratesToParameter p115_2 "a" == true
#guard selectOwnedDeclaration p115_2 "b" == .parameter 0
#guard elaboratesToParameter p115_2 "b" == true
#guard selectOwnedDeclaration p115_0 "repeat" == .property 1
#guard elaboratesToParameter p115_0 "repeat" == false
#guard selectOwnedDeclaration p115_0 "E" == .property 0
#guard elaboratesToParameter p115_0 "E" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "x", .bind "x"]), clause (.sequenceValue [.bind "a", .bind "b"])] == none -- family E

-- explorer/special__loopStepBuiltinOneRow: C(c) = count(c) \n repeat(count([1, 2]), 1), repeat(C([1, 2]), 1), repeat(take([1, 2, 3], 2), 1)
def p116_0 : List OwnerLevel := { parameters := [], properties := ["C"] } :: prelude
def p116_1 : List OwnerLevel := { parameters := ["c"], properties := [] } :: p116_0
#guard selectOwnedDeclaration p116_1 "count" == .property 2
#guard elaboratesToParameter p116_1 "count" == false
#guard selectOwnedDeclaration p116_1 "c" == .parameter 0
#guard elaboratesToParameter p116_1 "c" == true
#guard selectOwnedDeclaration p116_0 "repeat" == .property 1 -- x3
#guard elaboratesToParameter p116_0 "repeat" == false -- x3
#guard selectOwnedDeclaration p116_0 "count" == .property 1
#guard elaboratesToParameter p116_0 "count" == false
#guard selectOwnedDeclaration p116_0 "C" == .property 0
#guard elaboratesToParameter p116_0 "C" == false
#guard selectOwnedDeclaration p116_0 "take" == .property 1
#guard elaboratesToParameter p116_0 "take" == false

-- explorer/special__loopStepBuiltinCollectionNextArity: repeat(take([1, 2, 3], 2), 2)
def p117_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p117_0 "repeat" == .property 1
#guard elaboratesToParameter p117_0 "repeat" == false
#guard selectOwnedDeclaration p117_0 "take" == .property 1
#guard elaboratesToParameter p117_0 "take" == false

-- explorer/special__loopStepBuiltinEmptyResultIsTheFlag: while(first([()]))
-- the same levels and decisions, 1 more:
--   spec/loop-step-builtin-empty-result-is-one-slot
def p118_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p118_0 "while" == .property 1
#guard elaboratesToParameter p118_0 "while" == false
#guard selectOwnedDeclaration p118_0 "first" == .property 1
#guard elaboratesToParameter p118_0 "first" == false

-- explorer/special__loopStepBuiltinLazyIf: repeat(if(false, 1 / 0, 2), 1)
-- the same levels and decisions, 1 more:
--   spec/loop-step-lazy-builtin-roles
def p119_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p119_0 "repeat" == .property 1
#guard elaboratesToParameter p119_0 "repeat" == false
#guard selectOwnedDeclaration p119_0 "if" == .property 1
#guard elaboratesToParameter p119_0 "if" == false

-- explorer/special__loopStepAliasOfFamilyAndBuiltin: Step(0) = 0 \n Step(n) = n - 1 \n A = Step \n C = count \n repeat(A(3), 2), repeat(C([1, 2]), 1)
-- the same levels and decisions, 1 more:
--   spec/loop-step-alias-follows-target
def p120_0 : List OwnerLevel := { parameters := [], properties := ["A", "C", "Step"] } :: prelude
def p120_1 : List OwnerLevel := { parameters := [], properties := [] } :: p120_0
def p120_2 : List OwnerLevel := { parameters := [], properties := [] } :: p120_0
def p120_3 : List OwnerLevel := { parameters := [], properties := [] } :: p120_0
def p120_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p120_0
#guard selectOwnedDeclaration p120_1 "Step" == .property 1
#guard elaboratesToParameter p120_1 "Step" == false
#guard selectOwnedDeclaration p120_2 "count" == .property 2
#guard elaboratesToParameter p120_2 "count" == false
#guard selectOwnedDeclaration p120_4 "n" == .parameter 0
#guard elaboratesToParameter p120_4 "n" == true
#guard selectOwnedDeclaration p120_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p120_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p120_0 "A" == .property 0
#guard elaboratesToParameter p120_0 "A" == false
#guard selectOwnedDeclaration p120_0 "C" == .property 0
#guard elaboratesToParameter p120_0 "C" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Step

-- explorer/special__loopStepForwardedFamily: Step(0) = 0 \n Step(n) = n - 1 \n Run(f, *s) = repeat(f(s*), 2) \n Run(Step, 3)
def p121_0 : List OwnerLevel := { parameters := [], properties := ["Step", "Run"] } :: prelude
def p121_1 : List OwnerLevel := { parameters := [], properties := [] } :: p121_0
def p121_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p121_0
def p121_3 : List OwnerLevel := { parameters := ["f", "s"], properties := [] } :: p121_0
#guard selectOwnedDeclaration p121_2 "n" == .parameter 0
#guard elaboratesToParameter p121_2 "n" == true
#guard selectOwnedDeclaration p121_3 "repeat" == .property 2
#guard elaboratesToParameter p121_3 "repeat" == false
#guard selectOwnedDeclaration p121_3 "f" == .parameter 0
#guard elaboratesToParameter p121_3 "f" == true
#guard selectOwnedDeclaration p121_3 "s" == .parameter 0
#guard elaboratesToParameter p121_3 "s" == true
#guard selectOwnedDeclaration p121_0 "Run" == .property 0
#guard elaboratesToParameter p121_0 "Run" == false
#guard selectOwnedDeclaration p121_0 "Step" == .property 0
#guard elaboratesToParameter p121_0 "Step" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Step

-- explorer/special__loopStepValueRejected: Run(f) = repeat(f(0), 1) \n Run(5)
-- the same levels and decisions, 1 more:
--   spec/loop-step-value-is-rejected
def p122_0 : List OwnerLevel := { parameters := [], properties := ["Run"] } :: prelude
def p122_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p122_0
#guard selectOwnedDeclaration p122_1 "repeat" == .property 2
#guard elaboratesToParameter p122_1 "repeat" == false
#guard selectOwnedDeclaration p122_1 "f" == .parameter 0
#guard elaboratesToParameter p122_1 "f" == true
#guard selectOwnedDeclaration p122_0 "Run" == .property 0
#guard elaboratesToParameter p122_0 "Run" == false

-- explorer/special__loopStepZeroIterationsNeverProject: Run(f, s) = repeat(f(s), 0) \n Run(5, 1), Run(1 / 0, 5)
-- the same levels and decisions, 1 more:
--   spec/loop-step-zero-iterations-never-projects
def p123_0 : List OwnerLevel := { parameters := [], properties := ["Run"] } :: prelude
def p123_1 : List OwnerLevel := { parameters := ["f", "s"], properties := [] } :: p123_0
#guard selectOwnedDeclaration p123_1 "repeat" == .property 2
#guard elaboratesToParameter p123_1 "repeat" == false
#guard selectOwnedDeclaration p123_1 "f" == .parameter 0
#guard elaboratesToParameter p123_1 "f" == true
#guard selectOwnedDeclaration p123_1 "s" == .parameter 0
#guard elaboratesToParameter p123_1 "s" == true
#guard selectOwnedDeclaration p123_0 "Run" == .property 0 -- x2
#guard elaboratesToParameter p123_0 "Run" == false -- x2

-- explorer/special__loopMetaValueRefused: repeat(5, 1)
def p124_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p124_0 "repeat" == .property 1
#guard elaboratesToParameter p124_0 "repeat" == false

-- explorer/special__loopMetaPropertyReadRefused: Step(x) = x + 1, x < 3 \n Start = Step(0) \n Start.while
-- the same levels and decisions, 1 more:
--   spec/loop-meta-no-implicit-provenance
def p125_0 : List OwnerLevel := { parameters := [], properties := ["Start", "Step"] } :: prelude
def p125_1 : List OwnerLevel := { parameters := [], properties := [] } :: p125_0
def p125_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p125_0
#guard selectOwnedDeclaration p125_1 "Step" == .property 1
#guard elaboratesToParameter p125_1 "Step" == false
#guard selectOwnedDeclaration p125_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p125_2 "x" == true -- x2
#guard selectOwnedDeclaration p125_0 "Start" == .property 0
#guard elaboratesToParameter p125_0 "Start" == false
#guard selectOwnedDeclaration p125_0 "while" == .property 1
#guard elaboratesToParameter p125_0 "while" == false

-- explorer/special__loopMetaPlainAndDot: Step(x) = x + 1, x < 3 \n Inc(x) = x + 1 \n while(Step(0)), Step(0).while, Step(0).while(), repeat(Inc(0), 5), Inc(0).repeat(5)
-- the same levels and decisions, 1 more:
--   spec/loop-meta-plain-and-dot
def p126_0 : List OwnerLevel := { parameters := [], properties := ["Step", "Inc"] } :: prelude
def p126_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p126_0
def p126_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p126_0
#guard selectOwnedDeclaration p126_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p126_1 "x" == true -- x2
#guard selectOwnedDeclaration p126_2 "x" == .parameter 0
#guard elaboratesToParameter p126_2 "x" == true
#guard selectOwnedDeclaration p126_0 "while" == .property 1 -- x3
#guard elaboratesToParameter p126_0 "while" == false -- x3
#guard selectOwnedDeclaration p126_0 "Step" == .property 0 -- x3
#guard elaboratesToParameter p126_0 "Step" == false -- x3
#guard selectOwnedDeclaration p126_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p126_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p126_0 "Inc" == .property 0 -- x2
#guard elaboratesToParameter p126_0 "Inc" == false -- x2

-- explorer/special__loopMetaZeroState: Z = false \n Z().while, Z().repeat(0)
-- the same levels and decisions, 1 more:
--   spec/loop-meta-zero-state
def p127_0 : List OwnerLevel := { parameters := [], properties := ["Z"] } :: prelude
def p127_1 : List OwnerLevel := { parameters := [], properties := [] } :: p127_0
#guard selectOwnedDeclaration p127_0 "Z" == .property 0 -- x2
#guard elaboratesToParameter p127_0 "Z" == false -- x2
#guard selectOwnedDeclaration p127_0 "while" == .property 1
#guard elaboratesToParameter p127_0 "while" == false
#guard selectOwnedDeclaration p127_0 "repeat" == .property 1
#guard elaboratesToParameter p127_0 "repeat" == false

-- explorer/special__loopMetaSpreadBeforeCount: Inc(x) = x + 1 \n Inc([1][5]*).repeat(1 / 0)
-- the same levels and decisions, 1 more:
--   spec/loop-meta-spread-before-count
def p128_0 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: prelude
def p128_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p128_0
#guard selectOwnedDeclaration p128_1 "x" == .parameter 0
#guard elaboratesToParameter p128_1 "x" == true
#guard selectOwnedDeclaration p128_0 "Inc" == .property 0
#guard elaboratesToParameter p128_0 "Inc" == false
#guard selectOwnedDeclaration p128_0 "repeat" == .property 1
#guard elaboratesToParameter p128_0 "repeat" == false

-- explorer/special__loopMetaExactArity: Step(x) = x + 1, x < 3 \n while(Step, 0)
-- the same levels and decisions, 1 more:
--   spec/loop-meta-exact-arity
def p129_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p129_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p129_0
#guard selectOwnedDeclaration p129_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p129_1 "x" == true -- x2
#guard selectOwnedDeclaration p129_0 "while" == .property 1
#guard elaboratesToParameter p129_0 "while" == false
#guard selectOwnedDeclaration p129_0 "Step" == .property 0
#guard elaboratesToParameter p129_0 "Step" == false

-- explorer/special__loopMetaQualifiedCalleeCaptured: Box = { S(x) = x + 1, x < 3 } \n Box.S(0).while
-- the same levels and decisions, 2 more:
--   explorer/special__loopMetaBareMemberPathRefused, spec/loop-meta-qualified-step
def p130_0 : List OwnerLevel := { parameters := [], properties := ["Box"] } :: prelude
def p130_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p130_0
def p130_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p130_1
#guard selectOwnedDeclaration p130_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p130_2 "x" == true -- x2
#guard selectOwnedDeclaration p130_0 "Box" == .property 0
#guard elaboratesToParameter p130_0 "Box" == false
#guard selectOwnedDeclaration p130_0 "S" == .none
#guard elaboratesToParameter p130_0 "S" == false
#guard selectOwnedDeclaration p130_0 "while" == .property 1
#guard elaboratesToParameter p130_0 "while" == false

-- explorer/special__loopMetaRebuiltProjectedStep: Step(x) = x + 1, x < 3 \n Loop(meta op) = op.Algorithm(op.Arguments*).while \n Step(0).Loop
def p131_0 : List OwnerLevel := { parameters := [], properties := ["Step", "Loop"] } :: prelude
def p131_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p131_0
def p131_2 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p131_0
#guard selectOwnedDeclaration p131_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p131_1 "x" == true -- x2
#guard selectOwnedDeclaration p131_2 "op" == .parameter 0 -- x2
#guard elaboratesToParameter p131_2 "op" == true -- x2
#guard selectOwnedDeclaration p131_2 "Algorithm" == .none
#guard elaboratesToParameter p131_2 "Algorithm" == false
#guard selectOwnedDeclaration p131_2 "Arguments" == .none
#guard elaboratesToParameter p131_2 "Arguments" == false
#guard selectOwnedDeclaration p131_2 "while" == .property 2
#guard elaboratesToParameter p131_2 "while" == false
#guard selectOwnedDeclaration p131_0 "Step" == .property 0
#guard elaboratesToParameter p131_0 "Step" == false
#guard selectOwnedDeclaration p131_0 "Loop" == .property 0
#guard elaboratesToParameter p131_0 "Loop" == false

-- explorer/special__metaExtensionReceiverIsSupplied: Add(a, b) = a + b \n Capture(meta op) = op \n R = Capture(5.Add(1)) \n R.Arguments.count, R.Invoke()
def p132_0 : List OwnerLevel := { parameters := [], properties := ["R", "Add", "Capture"] } :: prelude
def p132_1 : List OwnerLevel := { parameters := [], properties := [] } :: p132_0
def p132_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p132_0
def p132_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p132_0
#guard selectOwnedDeclaration p132_1 "Capture" == .property 1
#guard elaboratesToParameter p132_1 "Capture" == false
#guard selectOwnedDeclaration p132_1 "Add" == .property 1
#guard elaboratesToParameter p132_1 "Add" == false
#guard selectOwnedDeclaration p132_2 "a" == .parameter 0
#guard elaboratesToParameter p132_2 "a" == true
#guard selectOwnedDeclaration p132_2 "b" == .parameter 0
#guard elaboratesToParameter p132_2 "b" == true
#guard selectOwnedDeclaration p132_3 "op" == .parameter 0
#guard elaboratesToParameter p132_3 "op" == true
#guard selectOwnedDeclaration p132_0 "R" == .property 0 -- x2
#guard elaboratesToParameter p132_0 "R" == false -- x2
#guard selectOwnedDeclaration p132_0 "Arguments" == .none
#guard elaboratesToParameter p132_0 "Arguments" == false
#guard selectOwnedDeclaration p132_0 "count" == .property 1
#guard elaboratesToParameter p132_0 "count" == false
#guard selectOwnedDeclaration p132_0 "Invoke" == .none
#guard elaboratesToParameter p132_0 "Invoke" == false

-- explorer/special__loopMetaNamedAlias: Box = { S(x) = x + 1, x < 3 } \n S = Box.S \n S(0).while
def p133_0 : List OwnerLevel := { parameters := [], properties := ["Box", "S"] } :: prelude
def p133_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p133_0
def p133_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p133_1
def p133_3 : List OwnerLevel := { parameters := [], properties := [] } :: p133_0
#guard selectOwnedDeclaration p133_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p133_2 "x" == true -- x2
#guard selectOwnedDeclaration p133_3 "Box" == .property 1
#guard elaboratesToParameter p133_3 "Box" == false
#guard selectOwnedDeclaration p133_3 "S" == .property 1
#guard elaboratesToParameter p133_3 "S" == false
#guard selectOwnedDeclaration p133_0 "S" == .property 0
#guard elaboratesToParameter p133_0 "S" == false
#guard selectOwnedDeclaration p133_0 "while" == .property 1
#guard elaboratesToParameter p133_0 "while" == false

-- explorer/special__loopStepLoopBuiltinAsStep: Step = { x + 1 } \n repeat(repeat(Step(0), 2), 1)
def p134_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p134_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p134_0
#guard selectOwnedDeclaration p134_1 "x" == .parameter 0
#guard elaboratesToParameter p134_1 "x" == true
#guard selectOwnedDeclaration p134_0 "repeat" == .property 1 -- x2
#guard elaboratesToParameter p134_0 "repeat" == false -- x2
#guard selectOwnedDeclaration p134_0 "Step" == .property 0
#guard elaboratesToParameter p134_0 "Step" == false

-- explorer/special__containsSequenceItem: contains(((1, 2), 3), (1, 2))
-- the same levels and decisions, 4 more:
--   explorer/special__containsListItem, explorer/special__containsEmptyItem
--   explorer/special__containsScalarCollection, explorer/special__containsAcrossKinds
def p135_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p135_0 "contains" == .property 1
#guard elaboratesToParameter p135_0 "contains" == false

-- explorer/special__openPublicMember: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     X \n } \n A
def p136_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p136_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p136_0
def p136_2 : List OwnerLevel := { parameters := [], properties := [] } :: p136_1
def p136_3 : List OwnerLevel := { parameters := [], properties := [] } :: p136_0
#guard selectOwnedDeclaration p136_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p136_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p136_3 "X" == .none
#guard elaboratesToParameter p136_3 "X" == false
#guard selectOwnedDeclaration p136_0 "A" == .property 0
#guard elaboratesToParameter p136_0 "A" == false

-- explorer/special__openPrivateMemberHidden: Lib = { \n     X = 101 \n } \n A = { \n     open Lib \n     X \n } \n A(707)
def p137_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p137_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p137_0
def p137_2 : List OwnerLevel := { parameters := [], properties := [] } :: p137_1
def p137_3 : List OwnerLevel := { parameters := ["X"], properties := [] } :: p137_0
#guard selectOwnedDeclaration p137_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p137_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p137_3 "X" == .parameter 0
#guard elaboratesToParameter p137_3 "X" == true
#guard selectOwnedDeclaration p137_0 "A" == .property 0
#guard elaboratesToParameter p137_0 "A" == false

-- explorer/special__openLocalOnlyCapturedParamsInsideOwner: Outer(p) = { \n     open Lib \n     Lib = { \n         public X = p + 101 \n     } \n     X \n } \n Outer(1)
def p138_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p138_1 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p138_0
def p138_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p138_1
def p138_3 : List OwnerLevel := { parameters := [], properties := [] } :: p138_2
#guard selectOwnedDeclaration p138_1 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p138_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p138_3 "p" == .parameter 2
#guard elaboratesToParameter p138_3 "p" == true
#guard selectOwnedDeclaration p138_1 "X" == .none
#guard elaboratesToParameter p138_1 "X" == false
#guard selectOwnedDeclaration p138_0 "Outer" == .property 0
#guard elaboratesToParameter p138_0 "Outer" == false

-- explorer/special__openLocalOnlyCapturedParamsOutsideOwner: Outer(p) = { \n     public Lib = { \n         public X = p + 101 \n     } \n     0 \n } \n A = { \n     open Outer.Lib \n     X \n } \n A
def p139_0 : List OwnerLevel := { parameters := [], properties := ["A", "Outer"] } :: prelude
def p139_1 : List OwnerLevel := { parameters := [], properties := [] } :: p139_0
def p139_2 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p139_0
def p139_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p139_2
def p139_4 : List OwnerLevel := { parameters := [], properties := [] } :: p139_3
#guard selectOwnedDeclaration p139_1 "Outer" == .property 1
#guard openHead? (elaborateOpenHead p139_1 "Outer") == some (false, "Outer")
#guard selectOwnedDeclaration p139_1 "X" == .none
#guard elaboratesToParameter p139_1 "X" == false
#guard selectOwnedDeclaration p139_4 "p" == .parameter 2
#guard elaboratesToParameter p139_4 "p" == true
#guard selectOwnedDeclaration p139_0 "A" == .property 0
#guard elaboratesToParameter p139_0 "A" == false

-- explorer/special__providerRequiringArgumentsCannotBeOpened: Lib(p) = { \n     public X = p + 101 \n     X \n } \n A = { \n     open Lib \n     X \n } \n A
-- the same levels and decisions, 1 more:
--   spec/open-parameterized-provider-rejected
def p140_0 : List OwnerLevel := { parameters := [], properties := ["A", "Lib"] } :: prelude
def p140_1 : List OwnerLevel := { parameters := [], properties := [] } :: p140_0
def p140_2 : List OwnerLevel := { parameters := ["p"], properties := ["X"] } :: p140_0
def p140_3 : List OwnerLevel := { parameters := [], properties := [] } :: p140_2
#guard selectOwnedDeclaration p140_1 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p140_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p140_1 "X" == .none
#guard elaboratesToParameter p140_1 "X" == false
#guard selectOwnedDeclaration p140_3 "p" == .parameter 1
#guard elaboratesToParameter p140_3 "p" == true
#guard selectOwnedDeclaration p140_2 "X" == .property 0
#guard elaboratesToParameter p140_2 "X" == false
#guard selectOwnedDeclaration p140_0 "A" == .property 0
#guard elaboratesToParameter p140_0 "A" == false

-- explorer/special__openTwoProvidersAmbiguous: L1 = { \n     public X = 101 \n } \n L2 = { \n     public X = 202 \n } \n A = { \n     open L1, L2 \n     X \n } \n A
def p141_0 : List OwnerLevel := { parameters := [], properties := ["L1", "L2", "A"] } :: prelude
def p141_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p141_0
def p141_2 : List OwnerLevel := { parameters := [], properties := [] } :: p141_1
def p141_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p141_0
def p141_4 : List OwnerLevel := { parameters := [], properties := [] } :: p141_3
def p141_5 : List OwnerLevel := { parameters := [], properties := [] } :: p141_0
#guard selectOwnedDeclaration p141_5 "L1" == .property 1
#guard openHead? (elaborateOpenHead p141_5 "L1") == some (false, "L1")
#guard selectOwnedDeclaration p141_5 "L2" == .property 1
#guard openHead? (elaborateOpenHead p141_5 "L2") == some (false, "L2")
#guard selectOwnedDeclaration p141_5 "X" == .none
#guard elaboratesToParameter p141_5 "X" == false
#guard selectOwnedDeclaration p141_0 "A" == .property 0
#guard elaboratesToParameter p141_0 "A" == false

-- explorer/special__openTwoProvidersAmbiguousAtRuntime: L1 = { \n     public X(v) = v + 101 \n } \n L2 = { \n     public X(v) = v + 202 \n } \n K(p) = { \n     open L1, L2 \n     p.X \n } \n K(10)
def p142_0 : List OwnerLevel := { parameters := [], properties := ["L1", "L2", "K"] } :: prelude
def p142_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p142_0
def p142_2 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p142_1
def p142_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p142_0
def p142_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p142_3
def p142_5 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p142_0
#guard selectOwnedDeclaration p142_2 "v" == .parameter 0
#guard elaboratesToParameter p142_2 "v" == true
#guard selectOwnedDeclaration p142_4 "v" == .parameter 0
#guard elaboratesToParameter p142_4 "v" == true
#guard selectOwnedDeclaration p142_5 "L1" == .property 1
#guard openHead? (elaborateOpenHead p142_5 "L1") == some (false, "L1")
#guard selectOwnedDeclaration p142_5 "L2" == .property 1
#guard openHead? (elaborateOpenHead p142_5 "L2") == some (false, "L2")
#guard selectOwnedDeclaration p142_5 "p" == .parameter 0
#guard elaboratesToParameter p142_5 "p" == true
#guard selectOwnedDeclaration p142_5 "X" == .none
#guard elaboratesToParameter p142_5 "X" == false
#guard selectOwnedDeclaration p142_0 "K" == .property 0
#guard elaboratesToParameter p142_0 "K" == false

-- explorer/special__openDuplicateTargetDedup: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib, Lib \n     X \n } \n A
def p143_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p143_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p143_0
def p143_2 : List OwnerLevel := { parameters := [], properties := [] } :: p143_1
def p143_3 : List OwnerLevel := { parameters := [], properties := [] } :: p143_0
#guard selectOwnedDeclaration p143_3 "Lib" == .property 1 -- x2
#guard openHead? (elaborateOpenHead p143_3 "Lib") == some (false, "Lib") -- x2
#guard selectOwnedDeclaration p143_3 "X" == .none
#guard elaboratesToParameter p143_3 "X" == false
#guard selectOwnedDeclaration p143_0 "A" == .property 0
#guard elaboratesToParameter p143_0 "A" == false

-- explorer/special__openDuplicateDottedTargetDedup: Lib = { \n     public S = { \n         public X = 101 \n     } \n } \n A = { \n     open Lib.S, Lib.S \n     X \n } \n A
def p144_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p144_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p144_0
def p144_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p144_1
def p144_3 : List OwnerLevel := { parameters := [], properties := [] } :: p144_2
def p144_4 : List OwnerLevel := { parameters := [], properties := [] } :: p144_0
#guard selectOwnedDeclaration p144_4 "Lib" == .property 1 -- x2
#guard openHead? (elaborateOpenHead p144_4 "Lib") == some (false, "Lib") -- x2
#guard selectOwnedDeclaration p144_4 "X" == .none
#guard elaboratesToParameter p144_4 "X" == false
#guard selectOwnedDeclaration p144_0 "A" == .property 0
#guard elaboratesToParameter p144_0 "A" == false

-- explorer/special__openTwoSpellingsOneProvider: Lib = { \n     public Sub = { \n         public X = 101 \n     } \n     public R = { \n         open Sub, Lib.Sub \n         X \n     } \n } \n Lib.R
-- the same levels and decisions, 1 more:
--   spec/open-two-spellings-one-provider
def p145_0 : List OwnerLevel := { parameters := [], properties := ["Lib"] } :: prelude
def p145_1 : List OwnerLevel := { parameters := [], properties := ["Sub", "R"] } :: p145_0
def p145_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p145_1
def p145_3 : List OwnerLevel := { parameters := [], properties := [] } :: p145_2
def p145_4 : List OwnerLevel := { parameters := [], properties := [] } :: p145_1
#guard selectOwnedDeclaration p145_4 "Sub" == .property 1
#guard openHead? (elaborateOpenHead p145_4 "Sub") == some (false, "Sub")
#guard selectOwnedDeclaration p145_4 "Lib" == .property 2
#guard openHead? (elaborateOpenHead p145_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p145_4 "X" == .none
#guard elaboratesToParameter p145_4 "X" == false
#guard selectOwnedDeclaration p145_0 "Lib" == .property 0
#guard elaboratesToParameter p145_0 "Lib" == false
#guard selectOwnedDeclaration p145_0 "R" == .none
#guard elaboratesToParameter p145_0 "R" == false

-- explorer/special__openDuplicateInlineBlocksAmbiguous: A = { \n     open { public X = 101 }, { public X = 202 } \n     X \n } \n A
def p146_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p146_1 : List OwnerLevel := { parameters := [], properties := [] } :: p146_0
def p146_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p146_3 : List OwnerLevel := { parameters := [], properties := [] } :: p146_2
def p146_4 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p146_5 : List OwnerLevel := { parameters := [], properties := [] } :: p146_4
#guard selectOwnedDeclaration p146_1 "X" == .none
#guard elaboratesToParameter p146_1 "X" == false
#guard selectOwnedDeclaration p146_0 "A" == .property 0
#guard elaboratesToParameter p146_0 "A" == false

-- explorer/special__openDuplicateInlineBlocksAmbiguousAtRuntime: K(p) = { \n     open { public X(v) = v + 101 }, { public X(v) = v + 101 } \n     p.X \n } \n K(10)
def p147_0 : List OwnerLevel := { parameters := [], properties := ["K"] } :: prelude
def p147_1 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p147_0
def p147_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p147_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p147_2
def p147_4 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p147_5 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p147_4
#guard selectOwnedDeclaration p147_3 "v" == .parameter 0
#guard elaboratesToParameter p147_3 "v" == true
#guard selectOwnedDeclaration p147_5 "v" == .parameter 0
#guard elaboratesToParameter p147_5 "v" == true
#guard selectOwnedDeclaration p147_1 "p" == .parameter 0
#guard elaboratesToParameter p147_1 "p" == true
#guard selectOwnedDeclaration p147_1 "X" == .none
#guard elaboratesToParameter p147_1 "X" == false
#guard selectOwnedDeclaration p147_0 "K" == .property 0
#guard elaboratesToParameter p147_0 "K" == false

-- explorer/special__openInlineBlock: A = { \n     open { public X = 101 } \n     X \n } \n A
def p148_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p148_1 : List OwnerLevel := { parameters := [], properties := [] } :: p148_0
def p148_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p148_3 : List OwnerLevel := { parameters := [], properties := [] } :: p148_2
#guard selectOwnedDeclaration p148_1 "X" == .none
#guard elaboratesToParameter p148_1 "X" == false
#guard selectOwnedDeclaration p148_0 "A" == .property 0
#guard elaboratesToParameter p148_0 "A" == false

-- explorer/special__openInlineBlockPrivateHidden: A = { \n     open { X = 101 } \n     X \n } \n A(707)
-- the same levels and decisions, 1 more:
--   spec/open-inline-headed-path-must-resolve
def p149_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p149_1 : List OwnerLevel := { parameters := ["X"], properties := [] } :: p149_0
def p149_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p149_3 : List OwnerLevel := { parameters := [], properties := [] } :: p149_2
#guard selectOwnedDeclaration p149_1 "X" == .parameter 0
#guard elaboratesToParameter p149_1 "X" == true
#guard selectOwnedDeclaration p149_0 "A" == .property 0
#guard elaboratesToParameter p149_0 "A" == false

-- explorer/special__openDottedPath: Lib = { \n     public S = { \n         public X = 101 \n     } \n } \n A = { \n     open Lib.S \n     X \n } \n A
def p150_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p150_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p150_0
def p150_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p150_1
def p150_3 : List OwnerLevel := { parameters := [], properties := [] } :: p150_2
def p150_4 : List OwnerLevel := { parameters := [], properties := [] } :: p150_0
#guard selectOwnedDeclaration p150_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p150_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p150_4 "X" == .none
#guard elaboratesToParameter p150_4 "X" == false
#guard selectOwnedDeclaration p150_0 "A" == .property 0
#guard elaboratesToParameter p150_0 "A" == false

-- explorer/special__openDottedPathPrivateIntermediate: Lib = { \n     S = { \n         public X = 101 \n     } \n } \n A = { \n     open Lib.S \n     X \n } \n A(707)
def p151_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p151_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p151_0
def p151_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p151_1
def p151_3 : List OwnerLevel := { parameters := [], properties := [] } :: p151_2
def p151_4 : List OwnerLevel := { parameters := ["X"], properties := [] } :: p151_0
#guard selectOwnedDeclaration p151_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p151_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p151_4 "X" == .parameter 0
#guard elaboratesToParameter p151_4 "X" == true
#guard selectOwnedDeclaration p151_0 "A" == .property 0
#guard elaboratesToParameter p151_0 "A" == false

-- explorer/special__openLocalShadowsOpenedName: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     X = 202 \n     X \n } \n A
def p152_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p152_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p152_0
def p152_2 : List OwnerLevel := { parameters := [], properties := [] } :: p152_1
def p152_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p152_0
def p152_4 : List OwnerLevel := { parameters := [], properties := [] } :: p152_3
#guard selectOwnedDeclaration p152_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p152_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p152_3 "X" == .property 0
#guard elaboratesToParameter p152_3 "X" == false
#guard selectOwnedDeclaration p152_0 "A" == .property 0
#guard elaboratesToParameter p152_0 "A" == false

-- explorer/special__openAncestorPropertyWins: Lib = { \n     public X = 101 \n } \n A = { \n     X = 202 \n     Inner = { \n         open Lib \n         X \n     } \n     Inner \n } \n A
def p153_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p153_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p153_0
def p153_2 : List OwnerLevel := { parameters := [], properties := [] } :: p153_1
def p153_3 : List OwnerLevel := { parameters := [], properties := ["X", "Inner"] } :: p153_0
def p153_4 : List OwnerLevel := { parameters := [], properties := [] } :: p153_3
def p153_5 : List OwnerLevel := { parameters := [], properties := [] } :: p153_3
#guard selectOwnedDeclaration p153_5 "Lib" == .property 2
#guard openHead? (elaborateOpenHead p153_5 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p153_5 "X" == .property 1
#guard elaboratesToParameter p153_5 "X" == false
#guard selectOwnedDeclaration p153_3 "Inner" == .property 0
#guard elaboratesToParameter p153_3 "Inner" == false
#guard selectOwnedDeclaration p153_0 "A" == .property 0
#guard elaboratesToParameter p153_0 "A" == false

-- explorer/special__openParentScopeReachesChild: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     Inner = { \n         X \n     } \n     Inner \n } \n A
def p154_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p154_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p154_0
def p154_2 : List OwnerLevel := { parameters := [], properties := [] } :: p154_1
def p154_3 : List OwnerLevel := { parameters := [], properties := ["Inner"] } :: p154_0
def p154_4 : List OwnerLevel := { parameters := [], properties := [] } :: p154_3
#guard selectOwnedDeclaration p154_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p154_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p154_4 "X" == .none
#guard elaboratesToParameter p154_4 "X" == false
#guard selectOwnedDeclaration p154_3 "Inner" == .property 0
#guard elaboratesToParameter p154_3 "Inner" == false
#guard selectOwnedDeclaration p154_0 "A" == .property 0
#guard elaboratesToParameter p154_0 "A" == false

-- explorer/special__openNestedDoesNotLeakOutward: Lib = { \n     public X = 101 \n } \n A = { \n     Inner = { \n         open Lib \n         X \n     } \n     X \n } \n A(707)
def p155_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p155_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p155_0
def p155_2 : List OwnerLevel := { parameters := [], properties := [] } :: p155_1
def p155_3 : List OwnerLevel := { parameters := ["X"], properties := ["Inner"] } :: p155_0
def p155_4 : List OwnerLevel := { parameters := [], properties := [] } :: p155_3
#guard selectOwnedDeclaration p155_4 "Lib" == .property 2
#guard openHead? (elaborateOpenHead p155_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p155_4 "X" == .parameter 1
#guard elaboratesToParameter p155_4 "X" == true
#guard selectOwnedDeclaration p155_3 "X" == .parameter 0
#guard elaboratesToParameter p155_3 "X" == true
#guard selectOwnedDeclaration p155_0 "A" == .property 0
#guard elaboratesToParameter p155_0 "A" == false

-- explorer/special__openHeadDefinedLater: A = { \n     open Lib \n     X \n } \n Lib = { \n     public X = 101 \n } \n A
def p156_0 : List OwnerLevel := { parameters := [], properties := ["A", "Lib"] } :: prelude
def p156_1 : List OwnerLevel := { parameters := [], properties := [] } :: p156_0
def p156_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p156_0
def p156_3 : List OwnerLevel := { parameters := [], properties := [] } :: p156_2
#guard selectOwnedDeclaration p156_1 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p156_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p156_1 "X" == .none
#guard elaboratesToParameter p156_1 "X" == false
#guard selectOwnedDeclaration p156_0 "A" == .property 0
#guard elaboratesToParameter p156_0 "A" == false

-- explorer/special__openBuiltinNameCollision: Lib = { \n     public count = 101 \n } \n A = { \n     open Lib \n     count([1, 2, 3]) \n } \n A
def p157_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p157_1 : List OwnerLevel := { parameters := [], properties := ["count"] } :: p157_0
def p157_2 : List OwnerLevel := { parameters := [], properties := [] } :: p157_1
def p157_3 : List OwnerLevel := { parameters := [], properties := [] } :: p157_0
#guard selectOwnedDeclaration p157_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p157_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p157_3 "count" == .property 2
#guard elaboratesToParameter p157_3 "count" == false
#guard selectOwnedDeclaration p157_0 "A" == .property 0
#guard elaboratesToParameter p157_0 "A" == false

-- explorer/special__openBuiltinTargetIsIllegal: Lib = { \n     public X = 101 \n } \n A = { \n     open count, Lib \n     X \n } \n A
def p158_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p158_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p158_0
def p158_2 : List OwnerLevel := { parameters := [], properties := [] } :: p158_1
def p158_3 : List OwnerLevel := { parameters := [], properties := [] } :: p158_0
#guard selectOwnedDeclaration p158_3 "count" == .property 2
#guard openHead? (elaborateOpenHead p158_3 "count") == some (false, "count")
#guard selectOwnedDeclaration p158_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p158_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p158_3 "X" == .none
#guard elaboratesToParameter p158_3 "X" == false
#guard selectOwnedDeclaration p158_0 "A" == .property 0
#guard elaboratesToParameter p158_0 "A" == false

-- explorer/special__structuralDotSeesPrivateMember: Lib = { \n     X = 101 \n } \n Lib.X
def p159_0 : List OwnerLevel := { parameters := [], properties := ["Lib"] } :: prelude
def p159_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p159_0
def p159_2 : List OwnerLevel := { parameters := [], properties := [] } :: p159_1
#guard selectOwnedDeclaration p159_0 "Lib" == .property 0
#guard elaboratesToParameter p159_0 "Lib" == false
#guard selectOwnedDeclaration p159_0 "X" == .none
#guard elaboratesToParameter p159_0 "X" == false

-- explorer/special__openPrivateMemberIsNotASecondProvider: Pub = { \n     public X = 101 \n } \n Lib = { \n     X = 202 \n } \n A = { \n     open Pub, Lib \n     X \n } \n A
def p160_0 : List OwnerLevel := { parameters := [], properties := ["Pub", "Lib", "A"] } :: prelude
def p160_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p160_0
def p160_2 : List OwnerLevel := { parameters := [], properties := [] } :: p160_1
def p160_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p160_0
def p160_4 : List OwnerLevel := { parameters := [], properties := [] } :: p160_3
def p160_5 : List OwnerLevel := { parameters := [], properties := [] } :: p160_0
#guard selectOwnedDeclaration p160_5 "Pub" == .property 1
#guard openHead? (elaborateOpenHead p160_5 "Pub") == some (false, "Pub")
#guard selectOwnedDeclaration p160_5 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p160_5 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p160_5 "X" == .none
#guard elaboratesToParameter p160_5 "X" == false
#guard selectOwnedDeclaration p160_0 "A" == .property 0
#guard elaboratesToParameter p160_0 "A" == false

-- explorer/special__openLocalOnlyMemberIsASecondProvider: Pub = { \n     public X = 101 \n } \n Outer(p) = { \n     public Lib = { \n         public X = p + 202 \n     } \n     0 \n } \n A = { \n     open Pub, Outer.Lib \n     X \n } \n A
-- the same levels and decisions, 1 more:
--   spec/open-local-only-member-is-a-second-provider
def p161_0 : List OwnerLevel := { parameters := [], properties := ["Pub", "A", "Outer"] } :: prelude
def p161_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p161_0
def p161_2 : List OwnerLevel := { parameters := [], properties := [] } :: p161_1
def p161_3 : List OwnerLevel := { parameters := [], properties := [] } :: p161_0
def p161_4 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p161_0
def p161_5 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p161_4
def p161_6 : List OwnerLevel := { parameters := [], properties := [] } :: p161_5
#guard selectOwnedDeclaration p161_3 "Pub" == .property 1
#guard openHead? (elaborateOpenHead p161_3 "Pub") == some (false, "Pub")
#guard selectOwnedDeclaration p161_3 "Outer" == .property 1
#guard openHead? (elaborateOpenHead p161_3 "Outer") == some (false, "Outer")
#guard selectOwnedDeclaration p161_3 "X" == .none
#guard elaboratesToParameter p161_3 "X" == false
#guard selectOwnedDeclaration p161_6 "p" == .parameter 2
#guard elaboratesToParameter p161_6 "p" == true
#guard selectOwnedDeclaration p161_0 "A" == .property 0
#guard elaboratesToParameter p161_0 "A" == false

-- explorer/special__openLocalOnlyMemberIsASecondProviderAtRuntime: Pub = { \n     public X(v) = v + 101 \n } \n Outer(p) = { \n     public Lib = { \n         public X(v) = v + p \n     } \n     0 \n } \n A(q) = { \n     open Pub, Outer.Lib \n     q.X \n } \n A(5)
def p162_0 : List OwnerLevel := { parameters := [], properties := ["Pub", "Outer", "A"] } :: prelude
def p162_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p162_0
def p162_2 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p162_1
def p162_3 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p162_0
def p162_4 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p162_3
def p162_5 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p162_4
def p162_6 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p162_0
#guard selectOwnedDeclaration p162_2 "v" == .parameter 0
#guard elaboratesToParameter p162_2 "v" == true
#guard selectOwnedDeclaration p162_5 "v" == .parameter 0
#guard elaboratesToParameter p162_5 "v" == true
#guard selectOwnedDeclaration p162_5 "p" == .parameter 2
#guard elaboratesToParameter p162_5 "p" == true
#guard selectOwnedDeclaration p162_6 "Pub" == .property 1
#guard openHead? (elaborateOpenHead p162_6 "Pub") == some (false, "Pub")
#guard selectOwnedDeclaration p162_6 "Outer" == .property 1
#guard openHead? (elaborateOpenHead p162_6 "Outer") == some (false, "Outer")
#guard selectOwnedDeclaration p162_6 "q" == .parameter 0
#guard elaboratesToParameter p162_6 "q" == true
#guard selectOwnedDeclaration p162_6 "X" == .none
#guard elaboratesToParameter p162_6 "X" == false
#guard selectOwnedDeclaration p162_0 "A" == .property 0
#guard elaboratesToParameter p162_0 "A" == false

-- explorer/special__ifSelectedParameterizedBranchIsArity: Inc(x) = x + 1 \n Probe(u) = if(true, Inc, 0) \n Probe(0)
-- the same levels and decisions, 4 more:
--   explorer/special__ifSelectedParameterizedFalseBranchIsArity, explorer/special__ifParameterizedConditionIsArity
--   explorer/special__ifUnselectedParameterizedBranchStaysLazy
--   spec/lazy-slot-demand-is-the-ordinary-zero-argument-demand
def p163_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Probe"] } :: prelude
def p163_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p163_0
def p163_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p163_0
#guard selectOwnedDeclaration p163_1 "x" == .parameter 0
#guard elaboratesToParameter p163_1 "x" == true
#guard selectOwnedDeclaration p163_2 "if" == .property 2
#guard elaboratesToParameter p163_2 "if" == false
#guard selectOwnedDeclaration p163_2 "Inc" == .property 1
#guard elaboratesToParameter p163_2 "Inc" == false
#guard selectOwnedDeclaration p163_0 "Probe" == .property 0
#guard elaboratesToParameter p163_0 "Probe" == false

-- explorer/special__ifZeroParameterBranchIsValue: A = 7 \n if(true, A, 0)
def p164_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p164_1 : List OwnerLevel := { parameters := [], properties := [] } :: p164_0
#guard selectOwnedDeclaration p164_0 "if" == .property 1
#guard elaboratesToParameter p164_0 "if" == false
#guard selectOwnedDeclaration p164_0 "A" == .property 0
#guard elaboratesToParameter p164_0 "A" == false

-- explorer/special__ifParameterIgnoringBodyStillArity: K(x) = 5 \n Probe(u) = if(true, K, 0) \n Probe(0)
def p165_0 : List OwnerLevel := { parameters := [], properties := ["K", "Probe"] } :: prelude
def p165_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p165_0
def p165_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p165_0
#guard selectOwnedDeclaration p165_2 "if" == .property 2
#guard elaboratesToParameter p165_2 "if" == false
#guard selectOwnedDeclaration p165_2 "K" == .property 1
#guard elaboratesToParameter p165_2 "K" == false
#guard selectOwnedDeclaration p165_0 "Probe" == .property 0
#guard elaboratesToParameter p165_0 "Probe" == false

-- explorer/special__ifCollectingCallableSlotIsCollectedValue: Collect(*xs) = xs \n if(true, Collect, 0)
-- the same levels and decisions, 1 more:
--   explorer/special__ifCollectingCallableExplicitCallIsSameValue
def p166_0 : List OwnerLevel := { parameters := [], properties := ["Collect"] } :: prelude
def p166_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p166_0
#guard selectOwnedDeclaration p166_1 "xs" == .parameter 0
#guard elaboratesToParameter p166_1 "xs" == true
#guard selectOwnedDeclaration p166_0 "if" == .property 1
#guard elaboratesToParameter p166_0 "if" == false
#guard selectOwnedDeclaration p166_0 "Collect" == .property 0
#guard elaboratesToParameter p166_0 "Collect" == false

-- explorer/special__bareCollectingCallableIsAValue: Only(*xs) = xs \n Only
-- the same levels and decisions, 1 more:
--   spec/zero-argument-demand-follows-actual-call-arity
def p167_0 : List OwnerLevel := { parameters := [], properties := ["Only"] } :: prelude
def p167_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p167_0
#guard selectOwnedDeclaration p167_1 "xs" == .parameter 0
#guard elaboratesToParameter p167_1 "xs" == true
#guard selectOwnedDeclaration p167_0 "Only" == .property 0
#guard elaboratesToParameter p167_0 "Only" == false

-- explorer/special__bareCollectingCallableCountAgreesWithDottedForm: Only(*xs) = xs \n count(Only), Only.count
def p168_0 : List OwnerLevel := { parameters := [], properties := ["Only"] } :: prelude
def p168_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p168_0
#guard selectOwnedDeclaration p168_1 "xs" == .parameter 0
#guard elaboratesToParameter p168_1 "xs" == true
#guard selectOwnedDeclaration p168_0 "count" == .property 1 -- x2
#guard elaboratesToParameter p168_0 "count" == false -- x2
#guard selectOwnedDeclaration p168_0 "Only" == .property 0 -- x2
#guard elaboratesToParameter p168_0 "Only" == false -- x2

-- explorer/special__ifRequiredPrefixBesideCollectorIsArity: Head(x, *rest) = x \n Probe(u) = if(true, Head, 0) \n Probe(0)
def p169_0 : List OwnerLevel := { parameters := [], properties := ["Head", "Probe"] } :: prelude
def p169_1 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p169_0
def p169_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p169_0
#guard selectOwnedDeclaration p169_1 "x" == .parameter 0
#guard elaboratesToParameter p169_1 "x" == true
#guard selectOwnedDeclaration p169_2 "if" == .property 2
#guard elaboratesToParameter p169_2 "if" == false
#guard selectOwnedDeclaration p169_2 "Head" == .property 1
#guard elaboratesToParameter p169_2 "Head" == false
#guard selectOwnedDeclaration p169_0 "Probe" == .property 0
#guard elaboratesToParameter p169_0 "Probe" == false

-- explorer/special__ifRequiredSuffixBesideCollectorIsArity: Tail(*rest, z) = z \n Probe(u) = if(true, Tail, 0) \n Probe(0)
def p170_0 : List OwnerLevel := { parameters := [], properties := ["Tail", "Probe"] } :: prelude
def p170_1 : List OwnerLevel := { parameters := ["rest", "z"], properties := [] } :: p170_0
def p170_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p170_0
#guard selectOwnedDeclaration p170_1 "z" == .parameter 0
#guard elaboratesToParameter p170_1 "z" == true
#guard selectOwnedDeclaration p170_2 "if" == .property 2
#guard elaboratesToParameter p170_2 "if" == false
#guard selectOwnedDeclaration p170_2 "Tail" == .property 1
#guard elaboratesToParameter p170_2 "Tail" == false
#guard selectOwnedDeclaration p170_0 "Probe" == .property 0
#guard elaboratesToParameter p170_0 "Probe" == false

-- explorer/special__ifNestedCollectingPatternIsArity: P((x, *rest)) = x \n Probe(u) = if(true, P, 0) \n Probe(0)
def p171_0 : List OwnerLevel := { parameters := [], properties := ["P", "Probe"] } :: prelude
def p171_1 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p171_0
def p171_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p171_0
#guard selectOwnedDeclaration p171_1 "x" == .parameter 0
#guard elaboratesToParameter p171_1 "x" == true
#guard selectOwnedDeclaration p171_2 "if" == .property 2
#guard elaboratesToParameter p171_2 "if" == false
#guard selectOwnedDeclaration p171_2 "P" == .property 1
#guard elaboratesToParameter p171_2 "P" == false
#guard selectOwnedDeclaration p171_0 "Probe" == .property 0
#guard elaboratesToParameter p171_0 "Probe" == false

-- explorer/special__collectingCallableStaysACallbackAlgorithm: Only(*xs) = xs \n map((1, 2), Only)
def p172_0 : List OwnerLevel := { parameters := [], properties := ["Only"] } :: prelude
def p172_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p172_0
#guard selectOwnedDeclaration p172_1 "xs" == .parameter 0
#guard elaboratesToParameter p172_1 "xs" == true
#guard selectOwnedDeclaration p172_0 "map" == .property 1
#guard elaboratesToParameter p172_0 "map" == false
#guard selectOwnedDeclaration p172_0 "Only" == .property 0
#guard elaboratesToParameter p172_0 "Only" == false

-- explorer/special__ifAlgorithmChannelParameterSlotIsArity: Inc(x) = x + 1 \n Apply(g) = if(true, g, 0) \n Apply(Inc)
def p173_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p173_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p173_0
def p173_2 : List OwnerLevel := { parameters := ["g"], properties := [] } :: p173_0
#guard selectOwnedDeclaration p173_1 "x" == .parameter 0
#guard elaboratesToParameter p173_1 "x" == true
#guard selectOwnedDeclaration p173_2 "if" == .property 2
#guard elaboratesToParameter p173_2 "if" == false
#guard selectOwnedDeclaration p173_2 "g" == .parameter 0
#guard elaboratesToParameter p173_2 "g" == true
#guard selectOwnedDeclaration p173_0 "Apply" == .property 0
#guard elaboratesToParameter p173_0 "Apply" == false
#guard selectOwnedDeclaration p173_0 "Inc" == .property 0
#guard elaboratesToParameter p173_0 "Inc" == false

-- explorer/special__repeatInitialParameterizedSlotIsArity: Inc(x) = x + 1 \n Step(s) = s + 1 \n Probe(u) = repeat(Step(Inc), 1) \n Probe(0)
-- the same levels and decisions, 2 more:
--   explorer/special__repeatCountParameterizedSlotIsArity, spec/lazy-slot-demand-covers-every-builtin-value-slot
def p174_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Step", "Probe"] } :: prelude
def p174_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p174_0
def p174_2 : List OwnerLevel := { parameters := ["s"], properties := [] } :: p174_0
def p174_3 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p174_0
#guard selectOwnedDeclaration p174_1 "x" == .parameter 0
#guard elaboratesToParameter p174_1 "x" == true
#guard selectOwnedDeclaration p174_2 "s" == .parameter 0
#guard elaboratesToParameter p174_2 "s" == true
#guard selectOwnedDeclaration p174_3 "repeat" == .property 2
#guard elaboratesToParameter p174_3 "repeat" == false
#guard selectOwnedDeclaration p174_3 "Step" == .property 1
#guard elaboratesToParameter p174_3 "Step" == false
#guard selectOwnedDeclaration p174_3 "Inc" == .property 1
#guard elaboratesToParameter p174_3 "Inc" == false
#guard selectOwnedDeclaration p174_0 "Probe" == .property 0
#guard elaboratesToParameter p174_0 "Probe" == false

-- explorer/special__whileInitialParameterizedSlotIsArity: Inc(x) = x + 1 \n Down(s) = s - 1, s \n Probe(u) = while(Down(Inc)) \n Probe(0)
def p175_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Down", "Probe"] } :: prelude
def p175_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p175_0
def p175_2 : List OwnerLevel := { parameters := ["s"], properties := [] } :: p175_0
def p175_3 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p175_0
#guard selectOwnedDeclaration p175_1 "x" == .parameter 0
#guard elaboratesToParameter p175_1 "x" == true
#guard selectOwnedDeclaration p175_2 "s" == .parameter 0 -- x2
#guard elaboratesToParameter p175_2 "s" == true -- x2
#guard selectOwnedDeclaration p175_3 "while" == .property 2
#guard elaboratesToParameter p175_3 "while" == false
#guard selectOwnedDeclaration p175_3 "Down" == .property 1
#guard elaboratesToParameter p175_3 "Down" == false
#guard selectOwnedDeclaration p175_3 "Inc" == .property 1
#guard elaboratesToParameter p175_3 "Inc" == false
#guard selectOwnedDeclaration p175_0 "Probe" == .property 0
#guard elaboratesToParameter p175_0 "Probe" == false

-- explorer/special__atomsParameterizedSlotIsArity: Inc(x) = x + 1 \n Probe(u) = atoms(Inc) \n Probe(0)
def p176_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Probe"] } :: prelude
def p176_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p176_0
def p176_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p176_0
#guard selectOwnedDeclaration p176_1 "x" == .parameter 0
#guard elaboratesToParameter p176_1 "x" == true
#guard selectOwnedDeclaration p176_2 "atoms" == .property 2
#guard elaboratesToParameter p176_2 "atoms" == false
#guard selectOwnedDeclaration p176_2 "Inc" == .property 1
#guard elaboratesToParameter p176_2 "Inc" == false
#guard selectOwnedDeclaration p176_0 "Probe" == .property 0
#guard elaboratesToParameter p176_0 "Probe" == false

-- explorer/special__rangeParameterizedSlotIsArity: Inc(x) = x + 1 \n Probe(u) = range(1, Inc) \n Probe(0)
def p177_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Probe"] } :: prelude
def p177_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p177_0
def p177_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p177_0
#guard selectOwnedDeclaration p177_1 "x" == .parameter 0
#guard elaboratesToParameter p177_1 "x" == true
#guard selectOwnedDeclaration p177_2 "range" == .property 2
#guard elaboratesToParameter p177_2 "range" == false
#guard selectOwnedDeclaration p177_2 "Inc" == .property 1
#guard elaboratesToParameter p177_2 "Inc" == false
#guard selectOwnedDeclaration p177_0 "Probe" == .property 0
#guard elaboratesToParameter p177_0 "Probe" == false

-- explorer/special__dotStringParameterizedReceiverIsArity: Inc(x) = x + 1 \n Probe(u) = Inc.string \n Probe(0)
-- the same levels and decisions, 1 more:
--   spec/dot-string-receiver-is-a-zero-argument-value-demand
def p178_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Probe"] } :: prelude
def p178_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p178_0
def p178_2 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p178_0
#guard selectOwnedDeclaration p178_1 "x" == .parameter 0
#guard elaboratesToParameter p178_1 "x" == true
#guard selectOwnedDeclaration p178_2 "Inc" == .property 1
#guard elaboratesToParameter p178_2 "Inc" == false
#guard selectOwnedDeclaration p178_2 "string" == .none
#guard elaboratesToParameter p178_2 "string" == false
#guard selectOwnedDeclaration p178_0 "Probe" == .property 0
#guard elaboratesToParameter p178_0 "Probe" == false

-- explorer/special__dotStringNavigatedParameterizedMemberIsArity: Lib = { Sub(x) = x } \n Probe(u) = Lib.Sub.string \n Probe(0)
def p179_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Probe"] } :: prelude
def p179_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p179_0
def p179_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p179_1
def p179_3 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p179_0
#guard selectOwnedDeclaration p179_2 "x" == .parameter 0
#guard elaboratesToParameter p179_2 "x" == true
#guard selectOwnedDeclaration p179_3 "Lib" == .property 1
#guard elaboratesToParameter p179_3 "Lib" == false
#guard selectOwnedDeclaration p179_3 "Sub" == .none
#guard elaboratesToParameter p179_3 "Sub" == false
#guard selectOwnedDeclaration p179_3 "string" == .none
#guard elaboratesToParameter p179_3 "string" == false
#guard selectOwnedDeclaration p179_0 "Probe" == .property 0
#guard elaboratesToParameter p179_0 "Probe" == false

-- explorer/special__reduceParameterIgnoringInitialStillRejected: K(x) = 5 \n Add(e, a) = e + a \n Probe(u) = reduce([1, 2], Add, K) \n Probe(0)
def p180_0 : List OwnerLevel := { parameters := [], properties := ["K", "Add", "Probe"] } :: prelude
def p180_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p180_0
def p180_2 : List OwnerLevel := { parameters := ["e", "a"], properties := [] } :: p180_0
def p180_3 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p180_0
#guard selectOwnedDeclaration p180_2 "e" == .parameter 0
#guard elaboratesToParameter p180_2 "e" == true
#guard selectOwnedDeclaration p180_2 "a" == .parameter 0
#guard elaboratesToParameter p180_2 "a" == true
#guard selectOwnedDeclaration p180_3 "reduce" == .property 2
#guard elaboratesToParameter p180_3 "reduce" == false
#guard selectOwnedDeclaration p180_3 "Add" == .property 1
#guard elaboratesToParameter p180_3 "Add" == false
#guard selectOwnedDeclaration p180_3 "K" == .property 1
#guard elaboratesToParameter p180_3 "K" == false
#guard selectOwnedDeclaration p180_0 "Probe" == .property 0
#guard elaboratesToParameter p180_0 "Probe" == false

-- explorer/special__repeatParameterizedStepIsCallback: Inc(x) = x + 1 \n repeat(Inc(0), 2)
def p181_0 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: prelude
def p181_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p181_0
#guard selectOwnedDeclaration p181_1 "x" == .parameter 0
#guard elaboratesToParameter p181_1 "x" == true
#guard selectOwnedDeclaration p181_0 "repeat" == .property 1
#guard elaboratesToParameter p181_0 "repeat" == false
#guard selectOwnedDeclaration p181_0 "Inc" == .property 0
#guard elaboratesToParameter p181_0 "Inc" == false

-- explorer/special__formulaLiftingIfBranchLiftsWhileStayingLazy: Inc(x) = x + 1 \n G = if(false, Inc, 7) \n G(4)
def p182_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc"] } :: prelude
def p182_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p182_0
def p182_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p182_0
#guard selectOwnedDeclaration p182_1 "if" == .property 2
#guard elaboratesToParameter p182_1 "if" == false
#guard selectOwnedDeclaration p182_1 "Inc" == .property 1
#guard elaboratesToParameter p182_1 "Inc" == false
#guard selectOwnedDeclaration p182_2 "x" == .parameter 0
#guard elaboratesToParameter p182_2 "x" == true
#guard selectOwnedDeclaration p182_0 "G" == .property 0
#guard elaboratesToParameter p182_0 "G" == false

-- explorer/special__formulaLiftingRootValuePositionNeedsTheParameter: Inc(x) = x + 1 \n if(true, Inc, 0)
def p183_0 : List OwnerLevel := { parameters := [], properties := ["Inc"], forwarded := ["x"] } :: prelude
def p183_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p183_0
#guard selectOwnedDeclaration p183_1 "x" == .parameter 0
#guard elaboratesToParameter p183_1 "x" == true
#guard selectOwnedDeclaration p183_0 "if" == .property 1
#guard elaboratesToParameter p183_0 "if" == false
#guard selectOwnedDeclaration p183_0 "Inc" == .property 0
#guard elaboratesToParameter p183_0 "Inc" == false

-- explorer/special__formulaLiftingBuiltinValueSlot: Inc(x) = x + 1 \n G = count(Inc) \n G(4)
def p184_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc"] } :: prelude
def p184_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p184_0
def p184_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p184_0
#guard selectOwnedDeclaration p184_1 "count" == .property 2
#guard elaboratesToParameter p184_1 "count" == false
#guard selectOwnedDeclaration p184_1 "Inc" == .property 1
#guard elaboratesToParameter p184_1 "Inc" == false
#guard selectOwnedDeclaration p184_2 "x" == .parameter 0
#guard elaboratesToParameter p184_2 "x" == true
#guard selectOwnedDeclaration p184_0 "G" == .property 0
#guard elaboratesToParameter p184_0 "G" == false

-- explorer/special__formulaLiftingBuiltinSignature: G = count + 0 \n G((1, 2, 3))
def p185_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p185_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["collection"] } :: p185_0
#guard selectOwnedDeclaration p185_1 "count" == .property 2
#guard elaboratesToParameter p185_1 "count" == false
#guard selectOwnedDeclaration p185_0 "G" == .property 0
#guard elaboratesToParameter p185_0 "G" == false

-- explorer/special__formulaLiftingLoopSignature: Step(s) = s + 1 \n G = repeat + 0 \n G(Step, 2, 0)
def p186_0 : List OwnerLevel := { parameters := [], properties := ["G", "Step"] } :: prelude
def p186_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["step", "count"] } :: p186_0
def p186_2 : List OwnerLevel := { parameters := ["s"], properties := [] } :: p186_0
#guard selectOwnedDeclaration p186_1 "repeat" == .property 2
#guard elaboratesToParameter p186_1 "repeat" == false
#guard selectOwnedDeclaration p186_2 "s" == .parameter 0
#guard elaboratesToParameter p186_2 "s" == true
#guard selectOwnedDeclaration p186_0 "G" == .property 0
#guard elaboratesToParameter p186_0 "G" == false
#guard selectOwnedDeclaration p186_0 "Step" == .property 0
#guard elaboratesToParameter p186_0 "Step" == false

-- explorer/special__formulaLiftingDottedMember: Lib = { \n     public Inc(x) = x + 1 \n } \n G = Lib.Inc + 0 \n G(4)
def p187_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "G"] } :: prelude
def p187_1 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: p187_0
def p187_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p187_1
def p187_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p187_0
#guard selectOwnedDeclaration p187_2 "x" == .parameter 0
#guard elaboratesToParameter p187_2 "x" == true
#guard selectOwnedDeclaration p187_3 "Lib" == .property 1
#guard elaboratesToParameter p187_3 "Lib" == false
#guard selectOwnedDeclaration p187_3 "Inc" == .none
#guard elaboratesToParameter p187_3 "Inc" == false
#guard selectOwnedDeclaration p187_0 "G" == .property 0
#guard elaboratesToParameter p187_0 "G" == false

-- explorer/special__formulaLiftingOpenedMember: Lib = { \n     public Inc(x) = x + 1 \n } \n G = { \n     open Lib \n     Inc + 0 \n } \n G(4)
def p188_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "G"] } :: prelude
def p188_1 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: p188_0
def p188_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p188_1
def p188_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p188_0
#guard selectOwnedDeclaration p188_2 "x" == .parameter 0
#guard elaboratesToParameter p188_2 "x" == true
#guard selectOwnedDeclaration p188_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p188_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p188_3 "Inc" == .none
#guard elaboratesToParameter p188_3 "Inc" == false
#guard selectOwnedDeclaration p188_0 "G" == .property 0
#guard elaboratesToParameter p188_0 "G" == false

-- explorer/special__formulaLiftingClauseFamily: E(0) = 100 \n E(n) = n \n G = E + 1 \n G(0), G(5)
def p189_0 : List OwnerLevel := { parameters := [], properties := ["G", "E"] } :: prelude
def p189_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["n"] } :: p189_0
def p189_2 : List OwnerLevel := { parameters := [], properties := [] } :: p189_0
def p189_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p189_0
#guard selectOwnedDeclaration p189_1 "E" == .property 1
#guard elaboratesToParameter p189_1 "E" == false
#guard selectOwnedDeclaration p189_3 "n" == .parameter 0
#guard elaboratesToParameter p189_3 "n" == true
#guard selectOwnedDeclaration p189_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p189_0 "G" == false -- x2
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family E

-- explorer/special__formulaLiftingCaptureElement: Inc(x) = x + 1 \n G = (Inc, 0) \n G(4)
def p190_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc"] } :: prelude
def p190_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p190_0
def p190_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p190_0
#guard selectOwnedDeclaration p190_1 "Inc" == .property 1
#guard elaboratesToParameter p190_1 "Inc" == false
#guard selectOwnedDeclaration p190_2 "x" == .parameter 0
#guard elaboratesToParameter p190_2 "x" == true
#guard selectOwnedDeclaration p190_0 "G" == .property 0
#guard elaboratesToParameter p190_0 "G" == false

-- explorer/special__formulaLiftingStringReceiver: Inc(x) = x + 1 \n G = Inc.string \n G(3000)
def p191_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc"] } :: prelude
def p191_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p191_0
def p191_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p191_0
#guard selectOwnedDeclaration p191_1 "Inc" == .property 1
#guard elaboratesToParameter p191_1 "Inc" == false
#guard selectOwnedDeclaration p191_1 "string" == .none
#guard elaboratesToParameter p191_1 "string" == false
#guard selectOwnedDeclaration p191_2 "x" == .parameter 0
#guard elaboratesToParameter p191_2 "x" == true
#guard selectOwnedDeclaration p191_0 "G" == .property 0
#guard elaboratesToParameter p191_0 "G" == false

-- explorer/special__formulaLiftingNestedInUserArgument: Inc(x) = x + 1 \n Id(v) = v \n G = Id(Inc + 0) \n G(4)
def p192_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc", "Id"] } :: prelude
def p192_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p192_0
def p192_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p192_0
def p192_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p192_0
#guard selectOwnedDeclaration p192_1 "Id" == .property 1
#guard elaboratesToParameter p192_1 "Id" == false
#guard selectOwnedDeclaration p192_1 "Inc" == .property 1
#guard elaboratesToParameter p192_1 "Inc" == false
#guard selectOwnedDeclaration p192_2 "x" == .parameter 0
#guard elaboratesToParameter p192_2 "x" == true
#guard selectOwnedDeclaration p192_3 "v" == .parameter 0
#guard elaboratesToParameter p192_3 "v" == true
#guard selectOwnedDeclaration p192_0 "G" == .property 0
#guard elaboratesToParameter p192_0 "G" == false

-- explorer/special__formulaLiftingKeepsCallbacks: Inc(x) = x + 1 \n G = map([1, 2], Inc) \n G
def p193_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc"] } :: prelude
def p193_1 : List OwnerLevel := { parameters := [], properties := [] } :: p193_0
def p193_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p193_0
#guard selectOwnedDeclaration p193_1 "map" == .property 2
#guard elaboratesToParameter p193_1 "map" == false
#guard selectOwnedDeclaration p193_1 "Inc" == .property 1
#guard elaboratesToParameter p193_1 "Inc" == false
#guard selectOwnedDeclaration p193_2 "x" == .parameter 0
#guard elaboratesToParameter p193_2 "x" == true
#guard selectOwnedDeclaration p193_0 "G" == .property 0
#guard elaboratesToParameter p193_0 "G" == false

-- explorer/special__formulaLiftingKeepsUserArguments: Inc(x) = x + 1 \n Apply(f) = f(10) \n G = Apply(Inc) \n G
def p194_0 : List OwnerLevel := { parameters := [], properties := ["G", "Inc", "Apply"] } :: prelude
def p194_1 : List OwnerLevel := { parameters := [], properties := [] } :: p194_0
def p194_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p194_0
def p194_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p194_0
#guard selectOwnedDeclaration p194_1 "Apply" == .property 1
#guard elaboratesToParameter p194_1 "Apply" == false
#guard selectOwnedDeclaration p194_1 "Inc" == .property 1
#guard elaboratesToParameter p194_1 "Inc" == false
#guard selectOwnedDeclaration p194_2 "x" == .parameter 0
#guard elaboratesToParameter p194_2 "x" == true
#guard selectOwnedDeclaration p194_3 "f" == .parameter 0
#guard elaboratesToParameter p194_3 "f" == true
#guard selectOwnedDeclaration p194_0 "G" == .property 0
#guard elaboratesToParameter p194_0 "G" == false

-- explorer/special__repeatedNameCallableThenValue: Inc(y) = y + 1 \n P(x, x) = x, x(5) \n P(Inc, 1)
-- the same levels and decisions, 2 more:
--   explorer/special__repeatedNameValueThenCallable, spec/repeated-name-is-a-constraint-not-a-merge
def p195_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "P"] } :: prelude
def p195_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p195_0
def p195_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p195_0
#guard selectOwnedDeclaration p195_1 "y" == .parameter 0
#guard elaboratesToParameter p195_1 "y" == true
#guard selectOwnedDeclaration p195_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p195_2 "x" == true -- x2
#guard selectOwnedDeclaration p195_0 "P" == .property 0
#guard elaboratesToParameter p195_0 "P" == false
#guard selectOwnedDeclaration p195_0 "Inc" == .property 0
#guard elaboratesToParameter p195_0 "Inc" == false

-- explorer/special__repeatedNameFailedThenValue: Bad = 1 / 0 \n Q(x, x) = x \n Q(Bad, 7)
-- the same levels and decisions, 1 more:
--   explorer/special__repeatedNameValueThenFailed
def p196_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "Q"] } :: prelude
def p196_1 : List OwnerLevel := { parameters := [], properties := [] } :: p196_0
def p196_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p196_0
#guard selectOwnedDeclaration p196_2 "x" == .parameter 0
#guard elaboratesToParameter p196_2 "x" == true
#guard selectOwnedDeclaration p196_0 "Q" == .property 0
#guard elaboratesToParameter p196_0 "Q" == false
#guard selectOwnedDeclaration p196_0 "Bad" == .property 0
#guard elaboratesToParameter p196_0 "Bad" == false

-- explorer/special__repeatedNameAcrossCollectorCallable: Inc(y) = y + 1 \n C(x, *r, x) = x \n C(Inc, 9, 1)
def p197_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "C"] } :: prelude
def p197_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p197_0
def p197_2 : List OwnerLevel := { parameters := ["x", "r"], properties := [] } :: p197_0
#guard selectOwnedDeclaration p197_1 "y" == .parameter 0
#guard elaboratesToParameter p197_1 "y" == true
#guard selectOwnedDeclaration p197_2 "x" == .parameter 0
#guard elaboratesToParameter p197_2 "x" == true
#guard selectOwnedDeclaration p197_0 "C" == .property 0
#guard elaboratesToParameter p197_0 "C" == false
#guard selectOwnedDeclaration p197_0 "Inc" == .property 0
#guard elaboratesToParameter p197_0 "Inc" == false

-- explorer/special__repeatedNameAcrossNestedGroupFailed: Bad = 1 / 0 \n N(x, (x, y)) = y \n N(Bad, (7, 8))
def p198_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "N"] } :: prelude
def p198_1 : List OwnerLevel := { parameters := [], properties := [] } :: p198_0
def p198_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p198_0
#guard selectOwnedDeclaration p198_2 "y" == .parameter 0
#guard elaboratesToParameter p198_2 "y" == true
#guard selectOwnedDeclaration p198_0 "N" == .property 0
#guard elaboratesToParameter p198_0 "N" == false
#guard selectOwnedDeclaration p198_0 "Bad" == .property 0
#guard elaboratesToParameter p198_0 "Bad" == false

-- explorer/special__repeatedNameForwardedCallable: Inc(y) = y + 1 \n P(x, x) = x, x(5) \n Fwd(a, b) = P(a, b) \n Fwd(1, Inc)
def p199_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "P", "Fwd"] } :: prelude
def p199_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p199_0
def p199_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p199_0
def p199_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p199_0
#guard selectOwnedDeclaration p199_1 "y" == .parameter 0
#guard elaboratesToParameter p199_1 "y" == true
#guard selectOwnedDeclaration p199_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p199_2 "x" == true -- x2
#guard selectOwnedDeclaration p199_3 "P" == .property 1
#guard elaboratesToParameter p199_3 "P" == false
#guard selectOwnedDeclaration p199_3 "a" == .parameter 0
#guard elaboratesToParameter p199_3 "a" == true
#guard selectOwnedDeclaration p199_3 "b" == .parameter 0
#guard elaboratesToParameter p199_3 "b" == true
#guard selectOwnedDeclaration p199_0 "Fwd" == .property 0
#guard elaboratesToParameter p199_0 "Fwd" == false
#guard selectOwnedDeclaration p199_0 "Inc" == .property 0
#guard elaboratesToParameter p199_0 "Inc" == false

-- explorer/special__repeatedNameDotReceiverFailed: Bad = 1 / 0 \n Q(x, x) = x \n Bad.Q(7)
def p200_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "Q"] } :: prelude
def p200_1 : List OwnerLevel := { parameters := [], properties := [] } :: p200_0
def p200_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p200_0
#guard selectOwnedDeclaration p200_2 "x" == .parameter 0
#guard elaboratesToParameter p200_2 "x" == true
#guard selectOwnedDeclaration p200_0 "Bad" == .property 0
#guard elaboratesToParameter p200_0 "Bad" == false
#guard selectOwnedDeclaration p200_0 "Q" == .property 0
#guard elaboratesToParameter p200_0 "Q" == false

-- explorer/special__repeatedNameValuelessBeforeVerdict: Bad = 1 / 0 \n Q2(x, x, y, y) = 0 \n Q2(Bad, 7, 1, 2)
def p201_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "Q2"] } :: prelude
def p201_1 : List OwnerLevel := { parameters := [], properties := [] } :: p201_0
def p201_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p201_0
#guard selectOwnedDeclaration p201_0 "Q2" == .property 0
#guard elaboratesToParameter p201_0 "Q2" == false
#guard selectOwnedDeclaration p201_0 "Bad" == .property 0
#guard elaboratesToParameter p201_0 "Bad" == false

-- explorer/special__repeatedNameAccompanyingChannel: A = 5 \n P(f, f) = f, f() \n P(5, A)
def p202_0 : List OwnerLevel := { parameters := [], properties := ["A", "P"] } :: prelude
def p202_1 : List OwnerLevel := { parameters := [], properties := [] } :: p202_0
def p202_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p202_0
#guard selectOwnedDeclaration p202_2 "f" == .parameter 0 -- x2
#guard elaboratesToParameter p202_2 "f" == true -- x2
#guard selectOwnedDeclaration p202_0 "P" == .property 0
#guard elaboratesToParameter p202_0 "P" == false
#guard selectOwnedDeclaration p202_0 "A" == .property 0
#guard elaboratesToParameter p202_0 "A" == false

-- explorer/special__forwardByNameAlias: P(x, x) = x \n Some = [P][0] \n Some(7)
-- the same levels and decisions, 2 more:
--   explorer/special__forwardByNameThreeOccurrences, explorer/special__forwardByNameInsideOneGroup
def p203_0 : List OwnerLevel := { parameters := [], properties := ["Some", "P"] } :: prelude
def p203_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p203_0
def p203_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p203_0
#guard selectOwnedDeclaration p203_1 "P" == .property 1
#guard elaboratesToParameter p203_1 "P" == false
#guard selectOwnedDeclaration p203_2 "x" == .parameter 0
#guard elaboratesToParameter p203_2 "x" == true
#guard selectOwnedDeclaration p203_0 "Some" == .property 0
#guard elaboratesToParameter p203_0 "Some" == false

-- explorer/special__forwardByNameNestedGroup: P((x, a), x) = a \n Some = [P][0] \n Some((7, 8))
-- the same levels and decisions, 1 more:
--   explorer/special__forwardByNameAcrossGroup
def p204_0 : List OwnerLevel := { parameters := [], properties := ["Some", "P"] } :: prelude
def p204_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x", "a"] } :: p204_0
def p204_2 : List OwnerLevel := { parameters := ["x", "a"], properties := [] } :: p204_0
#guard selectOwnedDeclaration p204_1 "P" == .property 1
#guard elaboratesToParameter p204_1 "P" == false
#guard selectOwnedDeclaration p204_2 "a" == .parameter 0
#guard elaboratesToParameter p204_2 "a" == true
#guard selectOwnedDeclaration p204_0 "Some" == .property 0
#guard elaboratesToParameter p204_0 "Some" == false

-- explorer/special__forwardByNameBesideCollector: P(x, *rest, x) = rest \n Some = [P][0] \n Some(7, 1, 2)
def p205_0 : List OwnerLevel := { parameters := [], properties := ["Some", "P"] } :: prelude
def p205_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x", "rest"] } :: p205_0
def p205_2 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p205_0
#guard selectOwnedDeclaration p205_1 "P" == .property 1
#guard elaboratesToParameter p205_1 "P" == false
#guard selectOwnedDeclaration p205_2 "rest" == .parameter 0
#guard elaboratesToParameter p205_2 "rest" == true
#guard selectOwnedDeclaration p205_0 "Some" == .property 0
#guard elaboratesToParameter p205_0 "Some" == false

-- explorer/special__forwardByNameClosedList: P(x, x) = x \n Q(x) = [P][0] \n Q(7)
-- the same levels and decisions, 1 more:
--   explorer/special__bareForwardingRepeatedName
def p206_0 : List OwnerLevel := { parameters := [], properties := ["P", "Q"] } :: prelude
def p206_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p206_0
def p206_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p206_0
#guard selectOwnedDeclaration p206_1 "x" == .parameter 0
#guard elaboratesToParameter p206_1 "x" == true
#guard selectOwnedDeclaration p206_2 "P" == .property 1
#guard elaboratesToParameter p206_2 "P" == false
#guard selectOwnedDeclaration p206_0 "Q" == .property 0
#guard elaboratesToParameter p206_0 "Q" == false

-- explorer/special__forwardByNameAcrossCallees: P(x, x) = x \n F(x) = x + 1 \n H = P + F \n H(3)
def p207_0 : List OwnerLevel := { parameters := [], properties := ["H", "P", "F"] } :: prelude
def p207_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p207_0
def p207_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p207_0
def p207_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p207_0
#guard selectOwnedDeclaration p207_1 "P" == .property 1
#guard elaboratesToParameter p207_1 "P" == false
#guard selectOwnedDeclaration p207_1 "F" == .property 1
#guard elaboratesToParameter p207_1 "F" == false
#guard selectOwnedDeclaration p207_2 "x" == .parameter 0
#guard elaboratesToParameter p207_2 "x" == true
#guard selectOwnedDeclaration p207_3 "x" == .parameter 0
#guard elaboratesToParameter p207_3 "x" == true
#guard selectOwnedDeclaration p207_0 "H" == .property 0
#guard elaboratesToParameter p207_0 "H" == false

-- explorer/special__forwardByNameFailedArgument: Bad = 1 / 0 \n P(x, x) = x \n Some = [P][0] \n Some(Bad)
def p208_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "Some", "P"] } :: prelude
def p208_1 : List OwnerLevel := { parameters := [], properties := [] } :: p208_0
def p208_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p208_0
def p208_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p208_0
#guard selectOwnedDeclaration p208_2 "P" == .property 1
#guard elaboratesToParameter p208_2 "P" == false
#guard selectOwnedDeclaration p208_3 "x" == .parameter 0
#guard elaboratesToParameter p208_3 "x" == true
#guard selectOwnedDeclaration p208_0 "Some" == .property 0
#guard elaboratesToParameter p208_0 "Some" == false
#guard selectOwnedDeclaration p208_0 "Bad" == .property 0
#guard elaboratesToParameter p208_0 "Bad" == false

-- explorer/special__forwardByNameCallableArgument: Inc(y) = y + 1 \n P(x, x) = x, x(5) \n Some = [P][0] \n Some(Inc)
def p209_0 : List OwnerLevel := { parameters := [], properties := ["Some", "Inc", "P"] } :: prelude
def p209_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p209_0
def p209_2 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p209_0
def p209_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p209_0
#guard selectOwnedDeclaration p209_1 "P" == .property 1
#guard elaboratesToParameter p209_1 "P" == false
#guard selectOwnedDeclaration p209_2 "y" == .parameter 0
#guard elaboratesToParameter p209_2 "y" == true
#guard selectOwnedDeclaration p209_3 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p209_3 "x" == true -- x2
#guard selectOwnedDeclaration p209_0 "Some" == .property 0
#guard elaboratesToParameter p209_0 "Some" == false
#guard selectOwnedDeclaration p209_0 "Inc" == .property 0
#guard elaboratesToParameter p209_0 "Inc" == false

-- explorer/special__aliasKeepsRepeatedSignature: P(x, x) = x \n A = P \n A(7, 7)
-- the same levels and decisions, 1 more:
--   explorer/special__aliasKeepsRepeatedConstraint
def p210_0 : List OwnerLevel := { parameters := [], properties := ["A", "P"] } :: prelude
def p210_1 : List OwnerLevel := { parameters := [], properties := [] } :: p210_0
def p210_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p210_0
#guard selectOwnedDeclaration p210_1 "P" == .property 1
#guard elaboratesToParameter p210_1 "P" == false
#guard selectOwnedDeclaration p210_2 "x" == .parameter 0
#guard elaboratesToParameter p210_2 "x" == true
#guard selectOwnedDeclaration p210_0 "A" == .property 0
#guard elaboratesToParameter p210_0 "A" == false

-- explorer/special__aliasKeepsListPattern: Single([x]) = x \n A = Single \n A([7]), A([[7]])
def p211_0 : List OwnerLevel := { parameters := [], properties := ["A", "Single"] } :: prelude
def p211_1 : List OwnerLevel := { parameters := [], properties := [] } :: p211_0
def p211_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p211_0
#guard selectOwnedDeclaration p211_1 "Single" == .property 1
#guard elaboratesToParameter p211_1 "Single" == false
#guard selectOwnedDeclaration p211_2 "x" == .parameter 0
#guard elaboratesToParameter p211_2 "x" == true
#guard selectOwnedDeclaration p211_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p211_0 "A" == false -- x2

-- explorer/special__aliasKeepsListPatternRejection: Single([x]) = x \n A = Single \n A(7)
def p212_0 : List OwnerLevel := { parameters := [], properties := ["A", "Single"] } :: prelude
def p212_1 : List OwnerLevel := { parameters := [], properties := [] } :: p212_0
def p212_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p212_0
#guard selectOwnedDeclaration p212_1 "Single" == .property 1
#guard elaboratesToParameter p212_1 "Single" == false
#guard selectOwnedDeclaration p212_2 "x" == .parameter 0
#guard elaboratesToParameter p212_2 "x" == true
#guard selectOwnedDeclaration p212_0 "A" == .property 0
#guard elaboratesToParameter p212_0 "A" == false

-- explorer/special__aliasKeepsBinderlessSignature: E((), []) = 1 \n A = E \n A((), [])
def p213_0 : List OwnerLevel := { parameters := [], properties := ["A", "E"] } :: prelude
def p213_1 : List OwnerLevel := { parameters := [], properties := [] } :: p213_0
def p213_2 : List OwnerLevel := { parameters := [], properties := [] } :: p213_0
#guard selectOwnedDeclaration p213_1 "E" == .property 1
#guard elaboratesToParameter p213_1 "E" == false
#guard selectOwnedDeclaration p213_0 "A" == .property 0
#guard elaboratesToParameter p213_0 "A" == false

-- explorer/special__aliasOfCollectorKeepsSignature: C(*xs) = xs \n A = C \n A(1, 2)
def p214_0 : List OwnerLevel := { parameters := [], properties := ["A", "C"] } :: prelude
def p214_1 : List OwnerLevel := { parameters := [], properties := [] } :: p214_0
def p214_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p214_0
#guard selectOwnedDeclaration p214_1 "C" == .property 1
#guard elaboratesToParameter p214_1 "C" == false
#guard selectOwnedDeclaration p214_2 "xs" == .parameter 0
#guard elaboratesToParameter p214_2 "xs" == true
#guard selectOwnedDeclaration p214_0 "A" == .property 0
#guard elaboratesToParameter p214_0 "A" == false

-- explorer/special__aliasChainKeepsSignature: Single([x]) = x \n A = Single \n B = A \n C = B \n C([[7]])
def p215_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C", "Single"] } :: prelude
def p215_1 : List OwnerLevel := { parameters := [], properties := [] } :: p215_0
def p215_2 : List OwnerLevel := { parameters := [], properties := [] } :: p215_0
def p215_3 : List OwnerLevel := { parameters := [], properties := [] } :: p215_0
def p215_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p215_0
#guard selectOwnedDeclaration p215_1 "Single" == .property 1
#guard elaboratesToParameter p215_1 "Single" == false
#guard selectOwnedDeclaration p215_2 "A" == .property 1
#guard elaboratesToParameter p215_2 "A" == false
#guard selectOwnedDeclaration p215_3 "B" == .property 1
#guard elaboratesToParameter p215_3 "B" == false
#guard selectOwnedDeclaration p215_4 "x" == .parameter 0
#guard elaboratesToParameter p215_4 "x" == true
#guard selectOwnedDeclaration p215_0 "C" == .property 0
#guard elaboratesToParameter p215_0 "C" == false

-- explorer/special__aliasOfBuiltinCount: C = count \n C([1, 2, 3])
def p216_0 : List OwnerLevel := { parameters := [], properties := ["C"] } :: prelude
def p216_1 : List OwnerLevel := { parameters := [], properties := [] } :: p216_0
#guard selectOwnedDeclaration p216_1 "count" == .property 2
#guard elaboratesToParameter p216_1 "count" == false
#guard selectOwnedDeclaration p216_0 "C" == .property 0
#guard elaboratesToParameter p216_0 "C" == false

-- explorer/special__aliasOfIfIsLazy: I = if \n I(true, 1, 1 / 0)
def p217_0 : List OwnerLevel := { parameters := [], properties := ["I"] } :: prelude
def p217_1 : List OwnerLevel := { parameters := [], properties := [] } :: p217_0
#guard selectOwnedDeclaration p217_1 "if" == .property 2
#guard elaboratesToParameter p217_1 "if" == false
#guard selectOwnedDeclaration p217_0 "I" == .property 0
#guard elaboratesToParameter p217_0 "I" == false

-- explorer/special__aliasOfMapDemandsNoCallback: Bad(x) = x / 0 \n M = map \n M([], Bad)
def p218_0 : List OwnerLevel := { parameters := [], properties := ["M", "Bad"] } :: prelude
def p218_1 : List OwnerLevel := { parameters := [], properties := [] } :: p218_0
def p218_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p218_0
#guard selectOwnedDeclaration p218_1 "map" == .property 2
#guard elaboratesToParameter p218_1 "map" == false
#guard selectOwnedDeclaration p218_2 "x" == .parameter 0
#guard elaboratesToParameter p218_2 "x" == true
#guard selectOwnedDeclaration p218_0 "M" == .property 0
#guard elaboratesToParameter p218_0 "M" == false
#guard selectOwnedDeclaration p218_0 "Bad" == .property 0
#guard elaboratesToParameter p218_0 "Bad" == false

-- explorer/special__aliasOfRepeatKeepsMinimumArity: Inc(x) = x + 1 \n R = repeat \n R(Inc)
def p219_0 : List OwnerLevel := { parameters := [], properties := ["R", "Inc"] } :: prelude
def p219_1 : List OwnerLevel := { parameters := [], properties := [] } :: p219_0
def p219_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p219_0
#guard selectOwnedDeclaration p219_1 "repeat" == .property 2
#guard elaboratesToParameter p219_1 "repeat" == false
#guard selectOwnedDeclaration p219_2 "x" == .parameter 0
#guard elaboratesToParameter p219_2 "x" == true
#guard selectOwnedDeclaration p219_0 "R" == .property 0
#guard elaboratesToParameter p219_0 "R" == false
#guard selectOwnedDeclaration p219_0 "Inc" == .property 0
#guard elaboratesToParameter p219_0 "Inc" == false

-- explorer/special__aliasChainOfBuiltin: A = count \n B = A \n C = B \n C([1, 2])
def p220_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C"] } :: prelude
def p220_1 : List OwnerLevel := { parameters := [], properties := [] } :: p220_0
def p220_2 : List OwnerLevel := { parameters := [], properties := [] } :: p220_0
def p220_3 : List OwnerLevel := { parameters := [], properties := [] } :: p220_0
#guard selectOwnedDeclaration p220_1 "count" == .property 2
#guard elaboratesToParameter p220_1 "count" == false
#guard selectOwnedDeclaration p220_2 "A" == .property 1
#guard elaboratesToParameter p220_2 "A" == false
#guard selectOwnedDeclaration p220_3 "B" == .property 1
#guard elaboratesToParameter p220_3 "B" == false
#guard selectOwnedDeclaration p220_0 "C" == .property 0
#guard elaboratesToParameter p220_0 "C" == false

-- explorer/special__aliasOfFamilyDispatches: Fact(0) = 1 \n Fact(n) = n * Fact(n - 1) \n F = Fact \n F(4)
-- the same levels and decisions, 2 more:
--   explorer/special__aliasOfFamilyNoMatchingBranch, spec/alias-of-a-clause-family-dispatches-as-the-family
def p221_0 : List OwnerLevel := { parameters := [], properties := ["F", "Fact"] } :: prelude
def p221_1 : List OwnerLevel := { parameters := [], properties := [] } :: p221_0
def p221_2 : List OwnerLevel := { parameters := [], properties := [] } :: p221_0
def p221_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p221_0
#guard selectOwnedDeclaration p221_1 "Fact" == .property 1
#guard elaboratesToParameter p221_1 "Fact" == false
#guard selectOwnedDeclaration p221_3 "n" == .parameter 0 -- x2
#guard elaboratesToParameter p221_3 "n" == true -- x2
#guard selectOwnedDeclaration p221_3 "Fact" == .property 1
#guard elaboratesToParameter p221_3 "Fact" == false
#guard selectOwnedDeclaration p221_0 "F" == .property 0
#guard elaboratesToParameter p221_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Fact

-- explorer/special__aliasOfUnnameableFamily: S(1) = 1 \n S(-1) = -1 \n SA = S \n SA(-1)
def p222_0 : List OwnerLevel := { parameters := [], properties := ["SA", "S"] } :: prelude
def p222_1 : List OwnerLevel := { parameters := [], properties := [] } :: p222_0
def p222_2 : List OwnerLevel := { parameters := [], properties := [] } :: p222_0
def p222_3 : List OwnerLevel := { parameters := [], properties := [] } :: p222_0
#guard selectOwnedDeclaration p222_1 "S" == .property 1
#guard elaboratesToParameter p222_1 "S" == false
#guard selectOwnedDeclaration p222_0 "SA" == .property 0
#guard elaboratesToParameter p222_0 "SA" == false
#guard familyLiftingSignature? [clause (.litInt 1), clause (.litInt (-1))] == none -- family S

-- explorer/special__aliasRolesAreTargetRoles: Inc(x) = x + 1 \n I = if \n K = I(c, Inc, 0) \n K(true, 4)
-- the same levels and decisions, 1 more:
--   spec/alias-arguments-take-the-targets-roles
def p223_0 : List OwnerLevel := { parameters := [], properties := ["I", "K", "Inc"] } :: prelude
def p223_1 : List OwnerLevel := { parameters := [], properties := [] } :: p223_0
def p223_2 : List OwnerLevel := { parameters := ["c"], properties := [], forwarded := ["x"] } :: p223_0
def p223_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p223_0
#guard selectOwnedDeclaration p223_1 "if" == .property 2
#guard elaboratesToParameter p223_1 "if" == false
#guard selectOwnedDeclaration p223_2 "I" == .property 1
#guard elaboratesToParameter p223_2 "I" == false
#guard selectOwnedDeclaration p223_2 "c" == .parameter 0
#guard elaboratesToParameter p223_2 "c" == true
#guard selectOwnedDeclaration p223_2 "Inc" == .property 1
#guard elaboratesToParameter p223_2 "Inc" == false
#guard selectOwnedDeclaration p223_3 "x" == .parameter 0
#guard elaboratesToParameter p223_3 "x" == true
#guard selectOwnedDeclaration p223_0 "K" == .property 0
#guard elaboratesToParameter p223_0 "K" == false

-- explorer/special__aliasCallableIdentityIsTarget: P(f, f) = f(7) \n Only(*xs) = 0 \n A = Only \n P(A, Only)
-- the same levels and decisions, 1 more:
--   spec/alias-is-the-targets-callable
def p224_0 : List OwnerLevel := { parameters := [], properties := ["A", "P", "Only"] } :: prelude
def p224_1 : List OwnerLevel := { parameters := [], properties := [] } :: p224_0
def p224_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p224_0
def p224_3 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p224_0
#guard selectOwnedDeclaration p224_1 "Only" == .property 1
#guard elaboratesToParameter p224_1 "Only" == false
#guard selectOwnedDeclaration p224_2 "f" == .parameter 0
#guard elaboratesToParameter p224_2 "f" == true
#guard selectOwnedDeclaration p224_0 "P" == .property 0
#guard elaboratesToParameter p224_0 "P" == false
#guard selectOwnedDeclaration p224_0 "A" == .property 0
#guard elaboratesToParameter p224_0 "A" == false
#guard selectOwnedDeclaration p224_0 "Only" == .property 0
#guard elaboratesToParameter p224_0 "Only" == false

-- explorer/special__aliasPassedAsCallableNavigatesTarget: Lib(x) = { \n   K = 5 \n   x \n } \n A = Lib \n Navigate(f) = f.K \n Navigate(A)
def p225_0 : List OwnerLevel := { parameters := [], properties := ["A", "Lib", "Navigate"] } :: prelude
def p225_1 : List OwnerLevel := { parameters := [], properties := [] } :: p225_0
def p225_2 : List OwnerLevel := { parameters := ["x"], properties := ["K"] } :: p225_0
def p225_3 : List OwnerLevel := { parameters := [], properties := [] } :: p225_2
def p225_4 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p225_0
#guard selectOwnedDeclaration p225_1 "Lib" == .property 1
#guard elaboratesToParameter p225_1 "Lib" == false
#guard selectOwnedDeclaration p225_2 "x" == .parameter 0
#guard elaboratesToParameter p225_2 "x" == true
#guard selectOwnedDeclaration p225_4 "f" == .parameter 0
#guard elaboratesToParameter p225_4 "f" == true
#guard selectOwnedDeclaration p225_4 "K" == .none
#guard elaboratesToParameter p225_4 "K" == false
#guard selectOwnedDeclaration p225_0 "Navigate" == .property 0
#guard elaboratesToParameter p225_0 "Navigate" == false
#guard selectOwnedDeclaration p225_0 "A" == .property 0
#guard elaboratesToParameter p225_0 "A" == false

-- explorer/special__bareForwardingThroughAlias: C = count \n W(collection) = C \n W([1, 2])
def p226_0 : List OwnerLevel := { parameters := [], properties := ["C", "W"] } :: prelude
def p226_1 : List OwnerLevel := { parameters := [], properties := [] } :: p226_0
def p226_2 : List OwnerLevel := { parameters := ["collection"], properties := [] } :: p226_0
#guard selectOwnedDeclaration p226_1 "count" == .property 2
#guard elaboratesToParameter p226_1 "count" == false
#guard selectOwnedDeclaration p226_2 "C" == .property 1
#guard elaboratesToParameter p226_2 "C" == false
#guard selectOwnedDeclaration p226_0 "W" == .property 0
#guard elaboratesToParameter p226_0 "W" == false

-- explorer/special__formulaLiftingThroughAlias: C = count \n K = C + 1 \n K([1, 2])
def p227_0 : List OwnerLevel := { parameters := [], properties := ["C", "K"] } :: prelude
def p227_1 : List OwnerLevel := { parameters := [], properties := [] } :: p227_0
def p227_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["collection"] } :: p227_0
#guard selectOwnedDeclaration p227_1 "count" == .property 2
#guard elaboratesToParameter p227_1 "count" == false
#guard selectOwnedDeclaration p227_2 "C" == .property 1
#guard elaboratesToParameter p227_2 "C" == false
#guard selectOwnedDeclaration p227_0 "K" == .property 0
#guard elaboratesToParameter p227_0 "K" == false

-- explorer/special__bareForwardingSameName: Double(x) = x * 2 \n Forward(x) = Double \n Forward(5)
def p228_0 : List OwnerLevel := { parameters := [], properties := ["Double", "Forward"] } :: prelude
def p228_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p228_0
def p228_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p228_0
#guard selectOwnedDeclaration p228_1 "x" == .parameter 0
#guard elaboratesToParameter p228_1 "x" == true
#guard selectOwnedDeclaration p228_2 "Double" == .property 1
#guard elaboratesToParameter p228_2 "Double" == false
#guard selectOwnedDeclaration p228_0 "Forward" == .property 0
#guard elaboratesToParameter p228_0 "Forward" == false

-- explorer/special__bareForwardingIsNotPositional: Sub(y, x) = y - x \n G(x, y) = Sub \n G(10, 3)
def p229_0 : List OwnerLevel := { parameters := [], properties := ["Sub", "G"] } :: prelude
def p229_1 : List OwnerLevel := { parameters := ["y", "x"], properties := [] } :: p229_0
def p229_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p229_0
#guard selectOwnedDeclaration p229_1 "y" == .parameter 0
#guard elaboratesToParameter p229_1 "y" == true
#guard selectOwnedDeclaration p229_1 "x" == .parameter 0
#guard elaboratesToParameter p229_1 "x" == true
#guard selectOwnedDeclaration p229_2 "Sub" == .property 1
#guard elaboratesToParameter p229_2 "Sub" == false
#guard selectOwnedDeclaration p229_0 "G" == .property 0
#guard elaboratesToParameter p229_0 "G" == false

-- explorer/special__bareForwardingIgnoresUnusedParameter: Double(x) = x * 2 \n Forward(x, unused) = Double \n Forward(5, 999)
def p230_0 : List OwnerLevel := { parameters := [], properties := ["Double", "Forward"] } :: prelude
def p230_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p230_0
def p230_2 : List OwnerLevel := { parameters := ["x", "unused"], properties := [] } :: p230_0
#guard selectOwnedDeclaration p230_1 "x" == .parameter 0
#guard elaboratesToParameter p230_1 "x" == true
#guard selectOwnedDeclaration p230_2 "Double" == .property 1
#guard elaboratesToParameter p230_2 "Double" == false
#guard selectOwnedDeclaration p230_0 "Forward" == .property 0
#guard elaboratesToParameter p230_0 "Forward" == false

-- explorer/special__bareForwardingOfAZeroParameterTarget: Ten = 10 \n Always(p) = Ten \n Always(999)
def p231_0 : List OwnerLevel := { parameters := [], properties := ["Ten", "Always"] } :: prelude
def p231_1 : List OwnerLevel := { parameters := [], properties := [] } :: p231_0
def p231_2 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p231_0
#guard selectOwnedDeclaration p231_2 "Ten" == .property 1
#guard elaboratesToParameter p231_2 "Ten" == false
#guard selectOwnedDeclaration p231_0 "Always" == .property 0
#guard elaboratesToParameter p231_0 "Always" == false

-- explorer/special__bareForwardingSamePattern: Single([x]) = x \n G([x]) = Single \n G([7]), G([[7]])
def p232_0 : List OwnerLevel := { parameters := [], properties := ["Single", "G"] } :: prelude
def p232_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p232_0
def p232_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p232_0
#guard selectOwnedDeclaration p232_1 "x" == .parameter 0
#guard elaboratesToParameter p232_1 "x" == true
#guard selectOwnedDeclaration p232_2 "Single" == .property 1
#guard elaboratesToParameter p232_2 "Single" == false
#guard selectOwnedDeclaration p232_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p232_0 "G" == false -- x2

-- explorer/special__bareForwardingRespreadsItsCollector: Coll(*vs) = vs \n G(*vs) = Coll \n G(1, 2)
def p233_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "G"] } :: prelude
def p233_1 : List OwnerLevel := { parameters := ["vs"], properties := [] } :: p233_0
def p233_2 : List OwnerLevel := { parameters := ["vs"], properties := [] } :: p233_0
#guard selectOwnedDeclaration p233_1 "vs" == .parameter 0
#guard elaboratesToParameter p233_1 "vs" == true
#guard selectOwnedDeclaration p233_2 "Coll" == .property 1
#guard elaboratesToParameter p233_2 "Coll" == false
#guard selectOwnedDeclaration p233_0 "G" == .property 0
#guard elaboratesToParameter p233_0 "G" == false

-- explorer/special__bareForwardingBranchForwardsItsBinder: F(n) = n * 10 \n G(0) = 0 \n G(n) = F \n G(0), G(3)
def p234_0 : List OwnerLevel := { parameters := [], properties := ["F", "G"] } :: prelude
def p234_1 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p234_0
def p234_2 : List OwnerLevel := { parameters := [], properties := [] } :: p234_0
def p234_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p234_0
#guard selectOwnedDeclaration p234_1 "n" == .parameter 0
#guard elaboratesToParameter p234_1 "n" == true
#guard selectOwnedDeclaration p234_3 "F" == .property 1
#guard elaboratesToParameter p234_3 "F" == false
#guard selectOwnedDeclaration p234_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p234_0 "G" == false -- x2
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family G

-- explorer/special__bareForwardingReusesEnclosingBinding: A = y + 1 \n G = { \n   F(x) = A \n   F(1) + y \n } \n G(10)
def p235_0 : List OwnerLevel := { parameters := [], properties := ["A", "G"] } :: prelude
def p235_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p235_0
def p235_2 : List OwnerLevel := { parameters := ["y"], properties := ["F"] } :: p235_0
def p235_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p235_2
#guard selectOwnedDeclaration p235_1 "y" == .parameter 0
#guard elaboratesToParameter p235_1 "y" == true
#guard selectOwnedDeclaration p235_3 "A" == .property 2
#guard elaboratesToParameter p235_3 "A" == false
#guard selectOwnedDeclaration p235_2 "F" == .property 0
#guard elaboratesToParameter p235_2 "F" == false
#guard selectOwnedDeclaration p235_2 "y" == .parameter 0
#guard elaboratesToParameter p235_2 "y" == true
#guard selectOwnedDeclaration p235_0 "G" == .property 0
#guard elaboratesToParameter p235_0 "G" == false

-- explorer/special__writtenCallInfersWrittenNames: Add((a, b)) = a + b \n G = Add((x, y)) \n G(2, 3)
def p236_0 : List OwnerLevel := { parameters := [], properties := ["G", "Add"] } :: prelude
def p236_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p236_0
def p236_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p236_0
#guard selectOwnedDeclaration p236_1 "Add" == .property 1
#guard elaboratesToParameter p236_1 "Add" == false
#guard selectOwnedDeclaration p236_1 "x" == .parameter 0
#guard elaboratesToParameter p236_1 "x" == true
#guard selectOwnedDeclaration p236_1 "y" == .parameter 0
#guard elaboratesToParameter p236_1 "y" == true
#guard selectOwnedDeclaration p236_2 "a" == .parameter 0
#guard elaboratesToParameter p236_2 "a" == true
#guard selectOwnedDeclaration p236_2 "b" == .parameter 0
#guard elaboratesToParameter p236_2 "b" == true
#guard selectOwnedDeclaration p236_0 "G" == .property 0
#guard elaboratesToParameter p236_0 "G" == false

-- explorer/special__writtenCallIgnoresCalleeBinderNames: Add((left, right)) = left + right \n G = Add((x, y)) \n G(2, 3)
def p237_0 : List OwnerLevel := { parameters := [], properties := ["G", "Add"] } :: prelude
def p237_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p237_0
def p237_2 : List OwnerLevel := { parameters := ["left", "right"], properties := [] } :: p237_0
#guard selectOwnedDeclaration p237_1 "Add" == .property 1
#guard elaboratesToParameter p237_1 "Add" == false
#guard selectOwnedDeclaration p237_1 "x" == .parameter 0
#guard elaboratesToParameter p237_1 "x" == true
#guard selectOwnedDeclaration p237_1 "y" == .parameter 0
#guard elaboratesToParameter p237_1 "y" == true
#guard selectOwnedDeclaration p237_2 "left" == .parameter 0
#guard elaboratesToParameter p237_2 "left" == true
#guard selectOwnedDeclaration p237_2 "right" == .parameter 0
#guard elaboratesToParameter p237_2 "right" == true
#guard selectOwnedDeclaration p237_0 "G" == .property 0
#guard elaboratesToParameter p237_0 "G" == false

-- spec/need-selected-signature-payload: Inc(x) = x + 1 \n F(x, y) = x(y) \n F(Inc)
def p238_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "F"] } :: prelude
def p238_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p238_0
def p238_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p238_0
#guard selectOwnedDeclaration p238_1 "x" == .parameter 0
#guard elaboratesToParameter p238_1 "x" == true
#guard selectOwnedDeclaration p238_2 "x" == .parameter 0
#guard elaboratesToParameter p238_2 "x" == true
#guard selectOwnedDeclaration p238_2 "y" == .parameter 0
#guard elaboratesToParameter p238_2 "y" == true
#guard selectOwnedDeclaration p238_0 "F" == .property 0
#guard elaboratesToParameter p238_0 "F" == false
#guard selectOwnedDeclaration p238_0 "Inc" == .property 0
#guard elaboratesToParameter p238_0 "Inc" == false

-- spec/need-variadic-minimum-payload: F(x, *middle, z) = x + z \n F(1)
def p239_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p239_1 : List OwnerLevel := { parameters := ["x", "middle", "z"], properties := [] } :: p239_0
#guard selectOwnedDeclaration p239_1 "x" == .parameter 0
#guard elaboratesToParameter p239_1 "x" == true
#guard selectOwnedDeclaration p239_1 "z" == .parameter 0
#guard elaboratesToParameter p239_1 "z" == true
#guard selectOwnedDeclaration p239_0 "F" == .property 0
#guard elaboratesToParameter p239_0 "F" == false

-- spec/need-closed-core-demand-is-runtime: A(q) = q + 1 \n F(x) = A + 0 \n F(7)
def p240_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p240_1 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p240_0
def p240_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p240_0
#guard selectOwnedDeclaration p240_1 "q" == .parameter 0
#guard elaboratesToParameter p240_1 "q" == true
#guard selectOwnedDeclaration p240_2 "A" == .property 1
#guard elaboratesToParameter p240_2 "A" == false
#guard selectOwnedDeclaration p240_0 "F" == .property 0
#guard elaboratesToParameter p240_0 "F" == false

-- spec/need-unused-ordinary-argument: F(x) = 10 \n F(1 / 0)
-- the same levels and decisions, 2 more:
--   spec/need-explicit-spread-precedes-arity, spec/patterned-user-call-is-one-value-boundary
def p241_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p241_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p241_0
#guard selectOwnedDeclaration p241_0 "F" == .property 0
#guard elaboratesToParameter p241_0 "F" == false

-- spec/need-unused-collector-slice: F(*xs) = 10 \n F(1, 1 / 0)
def p242_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p242_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p242_0
#guard selectOwnedDeclaration p242_0 "F" == .property 0
#guard elaboratesToParameter p242_0 "F" == false

-- spec/need-forwarding-preserves-unused-cell: G(x) = 10 \n F(x) = G \n F(1 / 0)
def p243_0 : List OwnerLevel := { parameters := [], properties := ["G", "F"] } :: prelude
def p243_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p243_0
def p243_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p243_0
#guard selectOwnedDeclaration p243_2 "G" == .property 1
#guard elaboratesToParameter p243_2 "G" == false
#guard selectOwnedDeclaration p243_0 "F" == .property 0
#guard elaboratesToParameter p243_0 "F" == false

-- spec/need-collector-forwarding-preserves-unused-slice: G(*xs) = 10 \n F(*xs) = G \n F(1, 1 / 0)
def p244_0 : List OwnerLevel := { parameters := [], properties := ["G", "F"] } :: prelude
def p244_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p244_0
def p244_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p244_0
#guard selectOwnedDeclaration p244_2 "G" == .property 1
#guard elaboratesToParameter p244_2 "G" == false
#guard selectOwnedDeclaration p244_0 "F" == .property 0
#guard elaboratesToParameter p244_0 "F" == false

-- spec/need-ordinary-conditional-selects-one-cell: Choose(true, yes, no) = yes \n Choose(false, yes, no) = no \n Choose(true, 7, 1 / 0)
def p245_0 : List OwnerLevel := { parameters := [], properties := ["Choose"] } :: prelude
def p245_1 : List OwnerLevel := { parameters := ["yes", "no"], properties := [] } :: p245_0
def p245_2 : List OwnerLevel := { parameters := ["yes", "no"], properties := [] } :: p245_0
#guard selectOwnedDeclaration p245_1 "yes" == .parameter 0
#guard elaboratesToParameter p245_1 "yes" == true
#guard selectOwnedDeclaration p245_2 "no" == .parameter 0
#guard elaboratesToParameter p245_2 "no" == true
#guard selectOwnedDeclaration p245_0 "Choose" == .property 0
#guard elaboratesToParameter p245_0 "Choose" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.litBool true, .bind "yes", .bind "no"]), clause (.sequenceValue [.litBool false, .bind "yes", .bind "no"])] == none -- family Choose

-- spec/need-family-shares-failed-attempt-value: F(0, x) = 7 \n F(n, 0) = n \n F(3, 0)
def p246_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p246_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p246_0
def p246_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p246_0
#guard selectOwnedDeclaration p246_2 "n" == .parameter 0
#guard elaboratesToParameter p246_2 "n" == true
#guard selectOwnedDeclaration p246_0 "F" == .property 0
#guard elaboratesToParameter p246_0 "F" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.litInt 0, .bind "x"]), clause (.sequenceValue [.bind "n", .litInt 0])] == some [.capture { name := "n" }, .capture { name := "x" }] -- family F

-- spec/need-first-loop-step-can-ignore-initial: Step(x) = 7 \n repeat(Step(1 / 0), 1)
def p247_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p247_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p247_0
#guard selectOwnedDeclaration p247_0 "repeat" == .property 1
#guard elaboratesToParameter p247_0 "repeat" == false
#guard selectOwnedDeclaration p247_0 "Step" == .property 0
#guard elaboratesToParameter p247_0 "Step" == false

-- spec/need-closed-demand-can-remain-unused: A(q) = q + 1 \n Keep(x) = 7 \n F(x) = Keep(count(A)) \n F(0)
def p248_0 : List OwnerLevel := { parameters := [], properties := ["A", "Keep", "F"] } :: prelude
def p248_1 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p248_0
def p248_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p248_0
def p248_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p248_0
#guard selectOwnedDeclaration p248_1 "q" == .parameter 0
#guard elaboratesToParameter p248_1 "q" == true
#guard selectOwnedDeclaration p248_3 "Keep" == .property 1
#guard elaboratesToParameter p248_3 "Keep" == false
#guard selectOwnedDeclaration p248_3 "count" == .property 2
#guard elaboratesToParameter p248_3 "count" == false
#guard selectOwnedDeclaration p248_3 "A" == .property 1
#guard elaboratesToParameter p248_3 "A" == false
#guard selectOwnedDeclaration p248_0 "F" == .property 0
#guard elaboratesToParameter p248_0 "F" == false

-- spec/need-wrong-arity-precedes-cell-demand: F(x) = x \n F(1 / 0, 2)
-- the same levels and decisions, 1 more:
--   spec/variadic-capture-collects-list
def p249_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p249_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p249_0
#guard selectOwnedDeclaration p249_1 "x" == .parameter 0
#guard elaboratesToParameter p249_1 "x" == true
#guard selectOwnedDeclaration p249_0 "F" == .property 0
#guard elaboratesToParameter p249_0 "F" == false

-- spec/need-collector-demand-materializes-whole-slice: F(*xs) = xs \n F(1, 1 / 0)
-- the same levels and decisions, 3 more:
--   spec/selective-collector-selection-demands-selected-positions
--   spec/selective-collector-whole-value-stays-eager, spec/selective-collector-written-list-stays-eager
def p250_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p250_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p250_0
#guard selectOwnedDeclaration p250_1 "xs" == .parameter 0
#guard elaboratesToParameter p250_1 "xs" == true
#guard selectOwnedDeclaration p250_0 "F" == .property 0
#guard elaboratesToParameter p250_0 "F" == false

-- spec/need-callable-projection-does-not-force-value: Inc(x) = x + 1 \n Apply(f) = f(4) \n Apply(Inc)
def p251_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p251_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p251_0
def p251_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p251_0
#guard selectOwnedDeclaration p251_1 "x" == .parameter 0
#guard elaboratesToParameter p251_1 "x" == true
#guard selectOwnedDeclaration p251_2 "f" == .parameter 0
#guard elaboratesToParameter p251_2 "f" == true
#guard selectOwnedDeclaration p251_0 "Apply" == .property 0
#guard elaboratesToParameter p251_0 "Apply" == false
#guard selectOwnedDeclaration p251_0 "Inc" == .property 0
#guard elaboratesToParameter p251_0 "Inc" == false

-- spec/need-demand-order-decides-the-first-failure: F(x, y) = y + x \n F(1 / 0, 'a' + 1)
def p252_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p252_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p252_0
#guard selectOwnedDeclaration p252_1 "y" == .parameter 0
#guard elaboratesToParameter p252_1 "y" == true
#guard selectOwnedDeclaration p252_1 "x" == .parameter 0
#guard elaboratesToParameter p252_1 "x" == true
#guard selectOwnedDeclaration p252_0 "F" == .property 0
#guard elaboratesToParameter p252_0 "F" == false

-- spec/need-wrapper-keeps-builtin-if-selection: MyIf(c, t, e) = if(c, t, e) \n Apply3(f, a, b, c) = f(a, b, c) \n MyIf(true, 1, 1 / 0) \n Apply3(if, false, 1 / 0, 2)
def p253_0 : List OwnerLevel := { parameters := [], properties := ["MyIf", "Apply3"] } :: prelude
def p253_1 : List OwnerLevel := { parameters := ["c", "t", "e"], properties := [] } :: p253_0
def p253_2 : List OwnerLevel := { parameters := ["f", "a", "b", "c"], properties := [] } :: p253_0
#guard selectOwnedDeclaration p253_1 "if" == .property 2
#guard elaboratesToParameter p253_1 "if" == false
#guard selectOwnedDeclaration p253_1 "c" == .parameter 0
#guard elaboratesToParameter p253_1 "c" == true
#guard selectOwnedDeclaration p253_1 "t" == .parameter 0
#guard elaboratesToParameter p253_1 "t" == true
#guard selectOwnedDeclaration p253_1 "e" == .parameter 0
#guard elaboratesToParameter p253_1 "e" == true
#guard selectOwnedDeclaration p253_2 "f" == .parameter 0
#guard elaboratesToParameter p253_2 "f" == true
#guard selectOwnedDeclaration p253_2 "a" == .parameter 0
#guard elaboratesToParameter p253_2 "a" == true
#guard selectOwnedDeclaration p253_2 "b" == .parameter 0
#guard elaboratesToParameter p253_2 "b" == true
#guard selectOwnedDeclaration p253_2 "c" == .parameter 0
#guard elaboratesToParameter p253_2 "c" == true
#guard selectOwnedDeclaration p253_0 "MyIf" == .property 0
#guard elaboratesToParameter p253_0 "MyIf" == false
#guard selectOwnedDeclaration p253_0 "Apply3" == .property 0
#guard elaboratesToParameter p253_0 "Apply3" == false
#guard selectOwnedDeclaration p253_0 "if" == .property 1
#guard elaboratesToParameter p253_0 "if" == false

-- spec/need-container-call-checks-cardinality-first: A = { \n     public X = 1 \n } \n A(6)
def p254_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p254_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p254_0
def p254_2 : List OwnerLevel := { parameters := [], properties := [] } :: p254_1
#guard selectOwnedDeclaration p254_0 "A" == .property 0
#guard elaboratesToParameter p254_0 "A" == false

-- spec/need-dot-receiver-is-a-supplied-computation: Second(a, b) = b \n (1 / 0).Second(2)
def p255_0 : List OwnerLevel := { parameters := [], properties := ["Second"] } :: prelude
def p255_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p255_0
#guard selectOwnedDeclaration p255_1 "b" == .parameter 0
#guard elaboratesToParameter p255_1 "b" == true
#guard selectOwnedDeclaration p255_0 "Second" == .property 0
#guard elaboratesToParameter p255_0 "Second" == false

-- spec/need-dot-receiver-follows-callee-demand-order: Flip(a, b) = b + a \n (1 / 0).Flip('a' + 1)
def p256_0 : List OwnerLevel := { parameters := [], properties := ["Flip"] } :: prelude
def p256_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p256_0
#guard selectOwnedDeclaration p256_1 "b" == .parameter 0
#guard elaboratesToParameter p256_1 "b" == true
#guard selectOwnedDeclaration p256_1 "a" == .parameter 0
#guard elaboratesToParameter p256_1 "a" == true
#guard selectOwnedDeclaration p256_0 "Flip" == .property 0
#guard elaboratesToParameter p256_0 "Flip" == false

-- spec/need-family-binder-keeps-the-callable: Inc(x) = x + 1 \n App(f, 0) = 0 \n App(f, n) = f(n) \n R(z) = App(Inc, 5) \n R(0)
def p257_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "App", "R"] } :: prelude
def p257_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p257_0
def p257_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p257_0
def p257_3 : List OwnerLevel := { parameters := ["f", "n"], properties := [] } :: p257_0
def p257_4 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p257_0
#guard selectOwnedDeclaration p257_1 "x" == .parameter 0
#guard elaboratesToParameter p257_1 "x" == true
#guard selectOwnedDeclaration p257_3 "f" == .parameter 0
#guard elaboratesToParameter p257_3 "f" == true
#guard selectOwnedDeclaration p257_3 "n" == .parameter 0
#guard elaboratesToParameter p257_3 "n" == true
#guard selectOwnedDeclaration p257_4 "App" == .property 1
#guard elaboratesToParameter p257_4 "App" == false
#guard selectOwnedDeclaration p257_4 "Inc" == .property 1
#guard elaboratesToParameter p257_4 "Inc" == false
#guard selectOwnedDeclaration p257_0 "R" == .property 0
#guard elaboratesToParameter p257_0 "R" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "f", .litInt 0]), clause (.sequenceValue [.bind "f", .bind "n"])] == some [.capture { name := "f" }, .capture { name := "n" }] -- family App

-- spec/need-deconstruction-runs-on-first-target-demand: p, q = 1 / 0, 2 \n I(f) = 0 \n I(p), I(q)
def p258_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "p", "q", "I"] } :: prelude
def p258_1 : List OwnerLevel := { parameters := [], properties := [] } :: p258_0
def p258_2 : List OwnerLevel := { parameters := ["p", "q"], properties := [] } :: p258_1
def p258_3 : List OwnerLevel := { parameters := [], properties := [] } :: p258_0
def p258_4 : List OwnerLevel := { parameters := ["p", "q"], properties := [] } :: p258_3
def p258_5 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p258_0
#guard selectOwnedDeclaration p258_2 "p" == .parameter 0
#guard elaboratesToParameter p258_2 "p" == true
#guard selectOwnedDeclaration p258_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p258_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p258_4 "q" == .parameter 0
#guard elaboratesToParameter p258_4 "q" == true
#guard selectOwnedDeclaration p258_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p258_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p258_0 "I" == .property 0 -- x2
#guard elaboratesToParameter p258_0 "I" == false -- x2
#guard selectOwnedDeclaration p258_0 "p" == .property 0
#guard elaboratesToParameter p258_0 "p" == false
#guard selectOwnedDeclaration p258_0 "q" == .property 0
#guard elaboratesToParameter p258_0 "q" == false

-- spec/collector-alias-keeps-known-slice: Coll(*ys) = 0 \n F(*xs) = { \n     A = xs \n     Coll(A*) \n } \n F(1 / 0)
-- the same levels and decisions, 1 more:
--   spec/collector-carrier-spread-is-arbitrary
def p259_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "F"] } :: prelude
def p259_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p259_0
def p259_2 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p259_0
def p259_3 : List OwnerLevel := { parameters := [], properties := [] } :: p259_2
#guard selectOwnedDeclaration p259_3 "xs" == .parameter 1
#guard elaboratesToParameter p259_3 "xs" == true
#guard selectOwnedDeclaration p259_2 "Coll" == .property 1
#guard elaboratesToParameter p259_2 "Coll" == false
#guard selectOwnedDeclaration p259_2 "A" == .property 0
#guard elaboratesToParameter p259_2 "A" == false
#guard selectOwnedDeclaration p259_0 "F" == .property 0
#guard elaboratesToParameter p259_0 "F" == false

-- spec/collector-alias-keeps-callable-elements: Inc(x) = x + 1 \n Apply(f) = f(9) \n Fwd(*fs) = { \n     A = fs \n     Apply(A*) \n } \n Fwd(Inc)
def p260_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply", "Fwd"] } :: prelude
def p260_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p260_0
def p260_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p260_0
def p260_3 : List OwnerLevel := { parameters := ["fs"], properties := ["A"] } :: p260_0
def p260_4 : List OwnerLevel := { parameters := [], properties := [] } :: p260_3
#guard selectOwnedDeclaration p260_1 "x" == .parameter 0
#guard elaboratesToParameter p260_1 "x" == true
#guard selectOwnedDeclaration p260_2 "f" == .parameter 0
#guard elaboratesToParameter p260_2 "f" == true
#guard selectOwnedDeclaration p260_4 "fs" == .parameter 1
#guard elaboratesToParameter p260_4 "fs" == true
#guard selectOwnedDeclaration p260_3 "Apply" == .property 1
#guard elaboratesToParameter p260_3 "Apply" == false
#guard selectOwnedDeclaration p260_3 "A" == .property 0
#guard elaboratesToParameter p260_3 "A" == false
#guard selectOwnedDeclaration p260_0 "Fwd" == .property 0
#guard elaboratesToParameter p260_0 "Fwd" == false
#guard selectOwnedDeclaration p260_0 "Inc" == .property 0
#guard elaboratesToParameter p260_0 "Inc" == false

-- spec/collector-alias-demand-raises-the-element-failure: Coll(*ys) = ys \n F(*xs) = { \n     A = xs \n     Coll(A*) \n } \n F(1 / 0, 2)
def p261_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "F"] } :: prelude
def p261_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p261_0
def p261_2 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p261_0
def p261_3 : List OwnerLevel := { parameters := [], properties := [] } :: p261_2
#guard selectOwnedDeclaration p261_1 "ys" == .parameter 0
#guard elaboratesToParameter p261_1 "ys" == true
#guard selectOwnedDeclaration p261_3 "xs" == .parameter 1
#guard elaboratesToParameter p261_3 "xs" == true
#guard selectOwnedDeclaration p261_2 "Coll" == .property 1
#guard elaboratesToParameter p261_2 "Coll" == false
#guard selectOwnedDeclaration p261_2 "A" == .property 0
#guard elaboratesToParameter p261_2 "A" == false
#guard selectOwnedDeclaration p261_0 "F" == .property 0
#guard elaboratesToParameter p261_0 "F" == false

-- spec/collector-reference-argument-keeps-known-slice: Coll(*ys) = 0 \n Pass(v) = Coll(v*) \n F(*xs) = { \n     A = xs \n     Pass(A) \n } \n F(1 / 0)
-- the same levels and decisions, 1 more:
--   spec/collector-reference-argument-carrier-stays-arbitrary
def p262_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "Pass", "F"] } :: prelude
def p262_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p262_0
def p262_2 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p262_0
def p262_3 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p262_0
def p262_4 : List OwnerLevel := { parameters := [], properties := [] } :: p262_3
#guard selectOwnedDeclaration p262_2 "Coll" == .property 1
#guard elaboratesToParameter p262_2 "Coll" == false
#guard selectOwnedDeclaration p262_2 "v" == .parameter 0
#guard elaboratesToParameter p262_2 "v" == true
#guard selectOwnedDeclaration p262_4 "xs" == .parameter 1
#guard elaboratesToParameter p262_4 "xs" == true
#guard selectOwnedDeclaration p262_3 "Pass" == .property 1
#guard elaboratesToParameter p262_3 "Pass" == false
#guard selectOwnedDeclaration p262_3 "A" == .property 0
#guard elaboratesToParameter p262_3 "A" == false
#guard selectOwnedDeclaration p262_0 "F" == .property 0
#guard elaboratesToParameter p262_0 "F" == false

-- spec/collector-reference-argument-is-one-argument: Count(*ys) = ys.count \n Pass(v) = Count(v), Count(v*) \n F(*xs) = { \n     A = xs \n     Pass(A) \n } \n F(1 / 0, 2, 3)
def p263_0 : List OwnerLevel := { parameters := [], properties := ["Count", "Pass", "F"] } :: prelude
def p263_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p263_0
def p263_2 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p263_0
def p263_3 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p263_0
def p263_4 : List OwnerLevel := { parameters := [], properties := [] } :: p263_3
#guard selectOwnedDeclaration p263_1 "ys" == .parameter 0
#guard elaboratesToParameter p263_1 "ys" == true
#guard selectOwnedDeclaration p263_1 "count" == .property 2
#guard elaboratesToParameter p263_1 "count" == false
#guard selectOwnedDeclaration p263_2 "Count" == .property 1 -- x2
#guard elaboratesToParameter p263_2 "Count" == false -- x2
#guard selectOwnedDeclaration p263_2 "v" == .parameter 0 -- x2
#guard elaboratesToParameter p263_2 "v" == true -- x2
#guard selectOwnedDeclaration p263_4 "xs" == .parameter 1
#guard elaboratesToParameter p263_4 "xs" == true
#guard selectOwnedDeclaration p263_3 "Pass" == .property 1
#guard elaboratesToParameter p263_3 "Pass" == false
#guard selectOwnedDeclaration p263_3 "A" == .property 0
#guard elaboratesToParameter p263_3 "A" == false
#guard selectOwnedDeclaration p263_0 "F" == .property 0
#guard elaboratesToParameter p263_0 "F" == false

-- spec/collector-reference-argument-keeps-callable-elements: Inc(x) = x + 1 \n Apply(f, *rest) = f(9) \n Pass(v) = Apply(v*) \n F(*xs) = { \n     A = xs \n     Pass(A) \n } \n F(Inc, 1 / 0)
def p264_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply", "Pass", "F"] } :: prelude
def p264_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p264_0
def p264_2 : List OwnerLevel := { parameters := ["f", "rest"], properties := [] } :: p264_0
def p264_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p264_0
def p264_4 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p264_0
def p264_5 : List OwnerLevel := { parameters := [], properties := [] } :: p264_4
#guard selectOwnedDeclaration p264_1 "x" == .parameter 0
#guard elaboratesToParameter p264_1 "x" == true
#guard selectOwnedDeclaration p264_2 "f" == .parameter 0
#guard elaboratesToParameter p264_2 "f" == true
#guard selectOwnedDeclaration p264_3 "Apply" == .property 1
#guard elaboratesToParameter p264_3 "Apply" == false
#guard selectOwnedDeclaration p264_3 "v" == .parameter 0
#guard elaboratesToParameter p264_3 "v" == true
#guard selectOwnedDeclaration p264_5 "xs" == .parameter 1
#guard elaboratesToParameter p264_5 "xs" == true
#guard selectOwnedDeclaration p264_4 "Pass" == .property 1
#guard elaboratesToParameter p264_4 "Pass" == false
#guard selectOwnedDeclaration p264_4 "A" == .property 0
#guard elaboratesToParameter p264_4 "A" == false
#guard selectOwnedDeclaration p264_0 "F" == .property 0
#guard elaboratesToParameter p264_0 "F" == false
#guard selectOwnedDeclaration p264_0 "Inc" == .property 0
#guard elaboratesToParameter p264_0 "Inc" == false

-- spec/collector-reference-argument-arity-precedes-elements: Two(a, b) = a \n Pass(v) = Two(v*) \n F(*xs) = { \n     A = xs \n     Pass(A) \n } \n F(1 / 0)
def p265_0 : List OwnerLevel := { parameters := [], properties := ["Two", "Pass", "F"] } :: prelude
def p265_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p265_0
def p265_2 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p265_0
def p265_3 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p265_0
def p265_4 : List OwnerLevel := { parameters := [], properties := [] } :: p265_3
#guard selectOwnedDeclaration p265_1 "a" == .parameter 0
#guard elaboratesToParameter p265_1 "a" == true
#guard selectOwnedDeclaration p265_2 "Two" == .property 1
#guard elaboratesToParameter p265_2 "Two" == false
#guard selectOwnedDeclaration p265_2 "v" == .parameter 0
#guard elaboratesToParameter p265_2 "v" == true
#guard selectOwnedDeclaration p265_4 "xs" == .parameter 1
#guard elaboratesToParameter p265_4 "xs" == true
#guard selectOwnedDeclaration p265_3 "Pass" == .property 1
#guard elaboratesToParameter p265_3 "Pass" == false
#guard selectOwnedDeclaration p265_3 "A" == .property 0
#guard elaboratesToParameter p265_3 "A" == false
#guard selectOwnedDeclaration p265_0 "F" == .property 0
#guard elaboratesToParameter p265_0 "F" == false

-- spec/selective-collector-count-reads-positions: CountItems(*xs) = xs.count \n CountItems(1 / 0)
def p266_0 : List OwnerLevel := { parameters := [], properties := ["CountItems"] } :: prelude
def p266_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p266_0
#guard selectOwnedDeclaration p266_1 "xs" == .parameter 0
#guard elaboratesToParameter p266_1 "xs" == true
#guard selectOwnedDeclaration p266_1 "count" == .property 2
#guard elaboratesToParameter p266_1 "count" == false
#guard selectOwnedDeclaration p266_0 "CountItems" == .property 0
#guard elaboratesToParameter p266_0 "CountItems" == false

-- spec/selective-collector-first-selects-one-element: FirstItem(*xs) = xs[0] \n FirstItem(10, 1 / 0)
def p267_0 : List OwnerLevel := { parameters := [], properties := ["FirstItem"] } :: prelude
def p267_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p267_0
#guard selectOwnedDeclaration p267_1 "xs" == .parameter 0
#guard elaboratesToParameter p267_1 "xs" == true
#guard selectOwnedDeclaration p267_0 "FirstItem" == .property 0
#guard elaboratesToParameter p267_0 "FirstItem" == false

-- spec/selective-collector-take-demands-its-prefix: Prefix(*xs) = xs.take(1) \n Prefix(10, 1 / 0)
-- the same levels and decisions, 1 more:
--   spec/selective-collector-take-needs-the-prefix-element
def p268_0 : List OwnerLevel := { parameters := [], properties := ["Prefix"] } :: prelude
def p268_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p268_0
#guard selectOwnedDeclaration p268_1 "xs" == .parameter 0
#guard elaboratesToParameter p268_1 "xs" == true
#guard selectOwnedDeclaration p268_1 "take" == .property 2
#guard elaboratesToParameter p268_1 "take" == false
#guard selectOwnedDeclaration p268_0 "Prefix" == .property 0
#guard elaboratesToParameter p268_0 "Prefix" == false

-- spec/selective-collector-effects-follow-first-demand: F(*xs) = xs[1], xs[0], xs[1] \n F(tick(), tick())
def p269_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p269_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p269_0
#guard selectOwnedDeclaration p269_1 "xs" == .parameter 0 -- x3
#guard elaboratesToParameter p269_1 "xs" == true -- x3
#guard selectOwnedDeclaration p269_0 "F" == .property 0
#guard elaboratesToParameter p269_0 "F" == false
#guard selectOwnedDeclaration p269_0 "tick" == .property 1 -- x2
#guard elaboratesToParameter p269_0 "tick" == false -- x2

-- spec/selective-collector-reads-through-a-transparent-reference: F(*xs) = { \n     A = xs \n     Box = { \n         public B = A \n         0 \n     } \n     A.count, Box.B[0] \n } \n F(10, 1 / 0)
def p270_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p270_1 : List OwnerLevel := { parameters := ["xs"], properties := ["A", "Box"] } :: p270_0
def p270_2 : List OwnerLevel := { parameters := [], properties := [] } :: p270_1
def p270_3 : List OwnerLevel := { parameters := [], properties := ["B"] } :: p270_1
def p270_4 : List OwnerLevel := { parameters := [], properties := [] } :: p270_3
#guard selectOwnedDeclaration p270_2 "xs" == .parameter 1
#guard elaboratesToParameter p270_2 "xs" == true
#guard selectOwnedDeclaration p270_4 "A" == .property 2
#guard elaboratesToParameter p270_4 "A" == false
#guard selectOwnedDeclaration p270_1 "A" == .property 0
#guard elaboratesToParameter p270_1 "A" == false
#guard selectOwnedDeclaration p270_1 "count" == .property 2
#guard elaboratesToParameter p270_1 "count" == false
#guard selectOwnedDeclaration p270_1 "Box" == .property 0
#guard elaboratesToParameter p270_1 "Box" == false
#guard selectOwnedDeclaration p270_1 "B" == .none
#guard elaboratesToParameter p270_1 "B" == false
#guard selectOwnedDeclaration p270_0 "F" == .property 0
#guard elaboratesToParameter p270_0 "F" == false

-- spec/selective-collector-carrier-stays-eager: F(*xs) = { \n     A = { xs } \n     A.count \n } \n F(1 / 0)
def p271_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p271_1 : List OwnerLevel := { parameters := ["xs"], properties := ["A"] } :: p271_0
def p271_2 : List OwnerLevel := { parameters := [], properties := [] } :: p271_1
#guard selectOwnedDeclaration p271_2 "xs" == .parameter 1
#guard elaboratesToParameter p271_2 "xs" == true
#guard selectOwnedDeclaration p271_1 "A" == .property 0
#guard elaboratesToParameter p271_1 "A" == false
#guard selectOwnedDeclaration p271_1 "count" == .property 2
#guard elaboratesToParameter p271_1 "count" == false
#guard selectOwnedDeclaration p271_0 "F" == .property 0
#guard elaboratesToParameter p271_0 "F" == false

-- spec/collector-member-path-keeps-known-slice: Coll(*ys) = 0 \n F(*xs) = { \n     Box = { \n         public A = xs \n         0 \n     } \n     Coll(Box.A*) \n } \n F(1 / 0)
-- the same levels and decisions, 1 more:
--   spec/collector-member-nontransparent-spread-is-arbitrary
def p272_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "F"] } :: prelude
def p272_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p272_0
def p272_2 : List OwnerLevel := { parameters := ["xs"], properties := ["Box"] } :: p272_0
def p272_3 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p272_2
def p272_4 : List OwnerLevel := { parameters := [], properties := [] } :: p272_3
#guard selectOwnedDeclaration p272_4 "xs" == .parameter 2
#guard elaboratesToParameter p272_4 "xs" == true
#guard selectOwnedDeclaration p272_2 "Coll" == .property 1
#guard elaboratesToParameter p272_2 "Coll" == false
#guard selectOwnedDeclaration p272_2 "Box" == .property 0
#guard elaboratesToParameter p272_2 "Box" == false
#guard selectOwnedDeclaration p272_2 "A" == .none
#guard elaboratesToParameter p272_2 "A" == false
#guard selectOwnedDeclaration p272_0 "F" == .property 0
#guard elaboratesToParameter p272_0 "F" == false

-- spec/collector-member-path-keeps-callable-elements: Inc(x) = x + 1 \n Apply(f) = f(9) \n Fwd(*fs) = { \n     Box = { \n         public A = fs \n         0 \n     } \n     Apply(Box.A*) \n } \n Fwd(Inc)
def p273_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply", "Fwd"] } :: prelude
def p273_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p273_0
def p273_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p273_0
def p273_3 : List OwnerLevel := { parameters := ["fs"], properties := ["Box"] } :: p273_0
def p273_4 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p273_3
def p273_5 : List OwnerLevel := { parameters := [], properties := [] } :: p273_4
#guard selectOwnedDeclaration p273_1 "x" == .parameter 0
#guard elaboratesToParameter p273_1 "x" == true
#guard selectOwnedDeclaration p273_2 "f" == .parameter 0
#guard elaboratesToParameter p273_2 "f" == true
#guard selectOwnedDeclaration p273_5 "fs" == .parameter 2
#guard elaboratesToParameter p273_5 "fs" == true
#guard selectOwnedDeclaration p273_3 "Apply" == .property 1
#guard elaboratesToParameter p273_3 "Apply" == false
#guard selectOwnedDeclaration p273_3 "Box" == .property 0
#guard elaboratesToParameter p273_3 "Box" == false
#guard selectOwnedDeclaration p273_3 "A" == .none
#guard elaboratesToParameter p273_3 "A" == false
#guard selectOwnedDeclaration p273_0 "Fwd" == .property 0
#guard elaboratesToParameter p273_0 "Fwd" == false
#guard selectOwnedDeclaration p273_0 "Inc" == .property 0
#guard elaboratesToParameter p273_0 "Inc" == false

-- spec/collector-member-path-demand-raises-the-element-failure: Coll(*ys) = ys \n F(*xs) = { \n     Box = { \n         public A = xs \n         0 \n     } \n     Coll(Box.A*) \n } \n F(1 / 0, 2)
def p274_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "F"] } :: prelude
def p274_1 : List OwnerLevel := { parameters := ["ys"], properties := [] } :: p274_0
def p274_2 : List OwnerLevel := { parameters := ["xs"], properties := ["Box"] } :: p274_0
def p274_3 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p274_2
def p274_4 : List OwnerLevel := { parameters := [], properties := [] } :: p274_3
#guard selectOwnedDeclaration p274_1 "ys" == .parameter 0
#guard elaboratesToParameter p274_1 "ys" == true
#guard selectOwnedDeclaration p274_4 "xs" == .parameter 2
#guard elaboratesToParameter p274_4 "xs" == true
#guard selectOwnedDeclaration p274_2 "Coll" == .property 1
#guard elaboratesToParameter p274_2 "Coll" == false
#guard selectOwnedDeclaration p274_2 "Box" == .property 0
#guard elaboratesToParameter p274_2 "Box" == false
#guard selectOwnedDeclaration p274_2 "A" == .none
#guard elaboratesToParameter p274_2 "A" == false
#guard selectOwnedDeclaration p274_0 "F" == .property 0
#guard elaboratesToParameter p274_0 "F" == false

-- spec/collected-callable-survives-explicit-respread: Inc(x) = x + 1 \n Apply(f) = f(9) \n Fwd(*fs) = Apply(fs*) \n Fwd(Inc)
def p275_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply", "Fwd"] } :: prelude
def p275_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p275_0
def p275_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p275_0
def p275_3 : List OwnerLevel := { parameters := ["fs"], properties := [] } :: p275_0
#guard selectOwnedDeclaration p275_1 "x" == .parameter 0
#guard elaboratesToParameter p275_1 "x" == true
#guard selectOwnedDeclaration p275_2 "f" == .parameter 0
#guard elaboratesToParameter p275_2 "f" == true
#guard selectOwnedDeclaration p275_3 "Apply" == .property 1
#guard elaboratesToParameter p275_3 "Apply" == false
#guard selectOwnedDeclaration p275_3 "fs" == .parameter 0
#guard elaboratesToParameter p275_3 "fs" == true
#guard selectOwnedDeclaration p275_0 "Fwd" == .property 0
#guard elaboratesToParameter p275_0 "Fwd" == false
#guard selectOwnedDeclaration p275_0 "Inc" == .property 0
#guard elaboratesToParameter p275_0 "Inc" == false

-- spec/boolean-predicates-and-patterns: F(true) = false \n F(false) = true \n F(true) \n F(false) \n range(-2, 2).filter{x >= 0} \n range(-2, 2).map{x >= 0}.contains(true) \n if(not 1 == 1, 10, 20)
def p276_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p276_1 : List OwnerLevel := { parameters := [], properties := [] } :: p276_0
def p276_2 : List OwnerLevel := { parameters := [], properties := [] } :: p276_0
def p276_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p276_0
def p276_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p276_0
#guard selectOwnedDeclaration p276_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p276_0 "F" == false -- x2
#guard selectOwnedDeclaration p276_0 "range" == .property 1 -- x2
#guard elaboratesToParameter p276_0 "range" == false -- x2
#guard selectOwnedDeclaration p276_0 "filter" == .property 1
#guard elaboratesToParameter p276_0 "filter" == false
#guard selectOwnedDeclaration p276_3 "x" == .parameter 0
#guard elaboratesToParameter p276_3 "x" == true
#guard selectOwnedDeclaration p276_0 "map" == .property 1
#guard elaboratesToParameter p276_0 "map" == false
#guard selectOwnedDeclaration p276_4 "x" == .parameter 0
#guard elaboratesToParameter p276_4 "x" == true
#guard selectOwnedDeclaration p276_0 "contains" == .property 1
#guard elaboratesToParameter p276_0 "contains" == false
#guard selectOwnedDeclaration p276_0 "if" == .property 1
#guard elaboratesToParameter p276_0 "if" == false
#guard familyLiftingSignature? [clause (.litBool true), clause (.litBool false)] == none -- family F

-- spec/boolean-loop-state-transition: S(x) = if(x == true, 0, true), x != 0 \n S(true).while
def p277_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p277_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p277_0
#guard selectOwnedDeclaration p277_1 "if" == .property 2
#guard elaboratesToParameter p277_1 "if" == false
#guard selectOwnedDeclaration p277_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p277_1 "x" == true -- x2
#guard selectOwnedDeclaration p277_0 "S" == .property 0
#guard elaboratesToParameter p277_0 "S" == false
#guard selectOwnedDeclaration p277_0 "while" == .property 1
#guard elaboratesToParameter p277_0 "while" == false

-- spec/boolean-predicate-rejects-visible-empty: F(x) = true, () \n range(0, 2).filter(F).count
def p278_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p278_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p278_0
#guard selectOwnedDeclaration p278_0 "range" == .property 1
#guard elaboratesToParameter p278_0 "range" == false
#guard selectOwnedDeclaration p278_0 "filter" == .property 1
#guard elaboratesToParameter p278_0 "filter" == false
#guard selectOwnedDeclaration p278_0 "F" == .property 0
#guard elaboratesToParameter p278_0 "F" == false
#guard selectOwnedDeclaration p278_0 "count" == .property 1
#guard elaboratesToParameter p278_0 "count" == false

-- spec/integer-division-exact-quotient: X = 8999999999999999999999999999999999 \n X div 3 \n X mod 3 \n X == 3 * (X div 3) + (X mod 3) \n Y = 3e32 \n (13 * Y - 1) div Y \n (12 * Y + 1) div Y \n -X div 3 \n X div -3 \n -X div -3 \n 1e34 div 7 \n 1e34 mod 7 \n 1e40 div 1e5
def p279_0 : List OwnerLevel := { parameters := [], properties := ["X", "Y"] } :: prelude
def p279_1 : List OwnerLevel := { parameters := [], properties := [] } :: p279_0
def p279_2 : List OwnerLevel := { parameters := [], properties := [] } :: p279_0
#guard selectOwnedDeclaration p279_0 "X" == .property 0 -- x8
#guard elaboratesToParameter p279_0 "X" == false -- x8
#guard selectOwnedDeclaration p279_0 "Y" == .property 0 -- x4
#guard elaboratesToParameter p279_0 "Y" == false -- x4

-- spec/property-access-and-call: # Define a property: \n Answer = 42 \n  \n # Property-style access: \n Answer \n  \n # Explicit zero-parameter call: \n Answer()
def p280_0 : List OwnerLevel := { parameters := [], properties := ["Answer"] } :: prelude
def p280_1 : List OwnerLevel := { parameters := [], properties := [] } :: p280_0
#guard selectOwnedDeclaration p280_0 "Answer" == .property 0 -- x2
#guard elaboratesToParameter p280_0 "Answer" == false -- x2

-- spec/output-is-ordinary-property: Output = 5 \n Output
def p281_0 : List OwnerLevel := { parameters := [], properties := ["Output"] } :: prelude
def p281_1 : List OwnerLevel := { parameters := [], properties := [] } :: p281_0
#guard selectOwnedDeclaration p281_0 "Output" == .property 0
#guard elaboratesToParameter p281_0 "Output" == false

-- spec/empty-eq-family: () == ()      # true \n () == (())    # true \n () != (())    # false \n count(())     # 0 \n count((()))   # 0
def p282_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p282_0 "count" == .property 1 -- x2
#guard elaboratesToParameter p282_0 "count" == false -- x2

-- spec/call-reentry-identity: I(a) = a \n A = 1, 2, 3 \n I(I(A))
def p283_0 : List OwnerLevel := { parameters := [], properties := ["A", "I"] } :: prelude
def p283_1 : List OwnerLevel := { parameters := [], properties := [] } :: p283_0
def p283_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p283_0
#guard selectOwnedDeclaration p283_2 "a" == .parameter 0
#guard elaboratesToParameter p283_2 "a" == true
#guard selectOwnedDeclaration p283_0 "I" == .property 0 -- x2
#guard elaboratesToParameter p283_0 "I" == false -- x2
#guard selectOwnedDeclaration p283_0 "A" == .property 0
#guard elaboratesToParameter p283_0 "A" == false

-- spec/call-value-boundary: F(*a) = a \n F(5, 9) \n F(5, 9)*, 997
def p284_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p284_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p284_0
#guard selectOwnedDeclaration p284_1 "a" == .parameter 0
#guard elaboratesToParameter p284_1 "a" == true
#guard selectOwnedDeclaration p284_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p284_0 "F" == false -- x2

-- spec/loop-result-is-one-value: Fibonacci(a, b) = b, a + b \n Fibonacci(0, 1).repeat(10) \n Fibonacci(0, 1).repeat(10)*, \n Fibonacci(0, 1).repeat(10), 7
def p285_0 : List OwnerLevel := { parameters := [], properties := ["Fibonacci"] } :: prelude
def p285_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p285_0
#guard selectOwnedDeclaration p285_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p285_1 "b" == true -- x2
#guard selectOwnedDeclaration p285_1 "a" == .parameter 0
#guard elaboratesToParameter p285_1 "a" == true
#guard selectOwnedDeclaration p285_0 "Fibonacci" == .property 0 -- x3
#guard elaboratesToParameter p285_0 "Fibonacci" == false -- x3
#guard selectOwnedDeclaration p285_0 "repeat" == .property 1 -- x3
#guard elaboratesToParameter p285_0 "repeat" == false -- x3

-- spec/loop-step-patterns-only-bind: Dup(x, x) = { (x + 1, x + 1)* } \n Same(x, x) = { x + 1, x + 1 } \n Step((a, b)) = (b, a + b) \n Dup(1, 1).repeat(2), Same(1, 1).repeat(2), Step((0, 1)).repeat(3)
def p286_0 : List OwnerLevel := { parameters := [], properties := ["Dup", "Same", "Step"] } :: prelude
def p286_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p286_0
def p286_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p286_0
def p286_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p286_0
#guard selectOwnedDeclaration p286_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p286_1 "x" == true -- x2
#guard selectOwnedDeclaration p286_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p286_2 "x" == true -- x2
#guard selectOwnedDeclaration p286_3 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p286_3 "b" == true -- x2
#guard selectOwnedDeclaration p286_3 "a" == .parameter 0
#guard elaboratesToParameter p286_3 "a" == true
#guard selectOwnedDeclaration p286_0 "Dup" == .property 0
#guard elaboratesToParameter p286_0 "Dup" == false
#guard selectOwnedDeclaration p286_0 "repeat" == .property 1 -- x3
#guard elaboratesToParameter p286_0 "repeat" == false -- x3
#guard selectOwnedDeclaration p286_0 "Same" == .property 0
#guard elaboratesToParameter p286_0 "Same" == false
#guard selectOwnedDeclaration p286_0 "Step" == .property 0
#guard elaboratesToParameter p286_0 "Step" == false

-- spec/loop-step-family-while: Countdown(0) = 0, false \n Countdown(n) = n - 1, true \n Countdown(3).while
def p287_0 : List OwnerLevel := { parameters := [], properties := ["Countdown"] } :: prelude
def p287_1 : List OwnerLevel := { parameters := [], properties := [] } :: p287_0
def p287_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p287_0
#guard selectOwnedDeclaration p287_2 "n" == .parameter 0
#guard elaboratesToParameter p287_2 "n" == true
#guard selectOwnedDeclaration p287_0 "Countdown" == .property 0
#guard elaboratesToParameter p287_0 "Countdown" == false
#guard selectOwnedDeclaration p287_0 "while" == .property 1
#guard elaboratesToParameter p287_0 "while" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family Countdown

-- spec/loop-while-condition-first-skips-transition: Step(x) = 10 / (x - 1), x > 1 \n Step(1).while
def p288_0 : List OwnerLevel := { parameters := [], properties := ["Step"] } :: prelude
def p288_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p288_0
#guard selectOwnedDeclaration p288_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p288_1 "x" == true -- x2
#guard selectOwnedDeclaration p288_0 "Step" == .property 0
#guard elaboratesToParameter p288_0 "Step" == false
#guard selectOwnedDeclaration p288_0 "while" == .property 1
#guard elaboratesToParameter p288_0 "while" == false

-- spec/loop-while-condition-first-trailing-empty-spread: Tail(n) = () \n Step(n) = n + 1, n < 2, Tail(n)* \n Step(0).while
def p289_0 : List OwnerLevel := { parameters := [], properties := ["Tail", "Step"] } :: prelude
def p289_1 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p289_0
def p289_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p289_0
#guard selectOwnedDeclaration p289_2 "n" == .parameter 0 -- x3
#guard elaboratesToParameter p289_2 "n" == true -- x3
#guard selectOwnedDeclaration p289_2 "Tail" == .property 1
#guard elaboratesToParameter p289_2 "Tail" == false
#guard selectOwnedDeclaration p289_0 "Step" == .property 0
#guard elaboratesToParameter p289_0 "Step" == false
#guard selectOwnedDeclaration p289_0 "while" == .property 1
#guard elaboratesToParameter p289_0 "while" == false

-- spec/loop-while-condition-first-row-granular: Pack(x) = x - 1, x > 1 \n Step(x) = Pack(x)* \n Step(3).while
def p290_0 : List OwnerLevel := { parameters := [], properties := ["Pack", "Step"] } :: prelude
def p290_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p290_0
def p290_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p290_0
#guard selectOwnedDeclaration p290_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p290_1 "x" == true -- x2
#guard selectOwnedDeclaration p290_2 "Pack" == .property 1
#guard elaboratesToParameter p290_2 "Pack" == false
#guard selectOwnedDeclaration p290_2 "x" == .parameter 0
#guard elaboratesToParameter p290_2 "x" == true
#guard selectOwnedDeclaration p290_0 "Step" == .property 0
#guard elaboratesToParameter p290_0 "Step" == false
#guard selectOwnedDeclaration p290_0 "while" == .property 1
#guard elaboratesToParameter p290_0 "while" == false

-- spec/loop-step-family-multi-slot: Gcd(a, 0) = a, 0, false \n Gcd(a, b) = b, a mod b, true \n Gcd(48, 18).while[0]
def p291_0 : List OwnerLevel := { parameters := [], properties := ["Gcd"] } :: prelude
def p291_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p291_0
def p291_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p291_0
#guard selectOwnedDeclaration p291_1 "a" == .parameter 0
#guard elaboratesToParameter p291_1 "a" == true
#guard selectOwnedDeclaration p291_2 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p291_2 "b" == true -- x2
#guard selectOwnedDeclaration p291_2 "a" == .parameter 0
#guard elaboratesToParameter p291_2 "a" == true
#guard selectOwnedDeclaration p291_0 "Gcd" == .property 0
#guard elaboratesToParameter p291_0 "Gcd" == false
#guard selectOwnedDeclaration p291_0 "while" == .property 1
#guard elaboratesToParameter p291_0 "while" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "a", .litInt 0]), clause (.sequenceValue [.bind "a", .bind "b"])] == some [.capture { name := "a" }, .capture { name := "b" }] -- family Gcd

-- spec/loop-step-builtin-is-one-row-wrapper: C(c) = count(c) \n repeat(count([1, 2]), 1) == repeat(C([1, 2]), 1), count([1, 2]).repeat(1)
def p292_0 : List OwnerLevel := { parameters := [], properties := ["C"] } :: prelude
def p292_1 : List OwnerLevel := { parameters := ["c"], properties := [] } :: p292_0
#guard selectOwnedDeclaration p292_1 "count" == .property 2
#guard elaboratesToParameter p292_1 "count" == false
#guard selectOwnedDeclaration p292_1 "c" == .parameter 0
#guard elaboratesToParameter p292_1 "c" == true
#guard selectOwnedDeclaration p292_0 "repeat" == .property 1 -- x3
#guard elaboratesToParameter p292_0 "repeat" == false -- x3
#guard selectOwnedDeclaration p292_0 "count" == .property 1 -- x2
#guard elaboratesToParameter p292_0 "count" == false -- x2
#guard selectOwnedDeclaration p292_0 "C" == .property 0
#guard elaboratesToParameter p292_0 "C" == false

-- spec/loop-step-builtin-argument-blame: G(z) = repeat(count({ q + 1 }), 1) \n G(0)
def p293_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p293_1 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p293_0
def p293_2 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p293_1
#guard selectOwnedDeclaration p293_1 "repeat" == .property 2
#guard elaboratesToParameter p293_1 "repeat" == false
#guard selectOwnedDeclaration p293_1 "count" == .property 2
#guard elaboratesToParameter p293_1 "count" == false
#guard selectOwnedDeclaration p293_2 "q" == .parameter 0
#guard elaboratesToParameter p293_2 "q" == true
#guard selectOwnedDeclaration p293_0 "G" == .property 0
#guard elaboratesToParameter p293_0 "G" == false

-- spec/loop-meta-forwarding: Step(x) = x + 1, x < 3 \n W(step) = while(step) \n W(Step(0))
def p294_0 : List OwnerLevel := { parameters := [], properties := ["Step", "W"] } :: prelude
def p294_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p294_0
def p294_2 : List OwnerLevel := { parameters := ["step"], properties := [] } :: p294_0
#guard selectOwnedDeclaration p294_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p294_1 "x" == true -- x2
#guard selectOwnedDeclaration p294_2 "while" == .property 2
#guard elaboratesToParameter p294_2 "while" == false
#guard selectOwnedDeclaration p294_2 "step" == .parameter 0
#guard elaboratesToParameter p294_2 "step" == true
#guard selectOwnedDeclaration p294_0 "W" == .property 0
#guard elaboratesToParameter p294_0 "W" == false
#guard selectOwnedDeclaration p294_0 "Step" == .property 0
#guard elaboratesToParameter p294_0 "Step" == false

-- spec/property-value-boundary: Coordinates = 10, 20 \n Coordinates \n Coordinates*, 997
def p295_0 : List OwnerLevel := { parameters := [], properties := ["Coordinates"] } :: prelude
def p295_1 : List OwnerLevel := { parameters := [], properties := [] } :: p295_0
#guard selectOwnedDeclaration p295_0 "Coordinates" == .property 0 -- x2
#guard elaboratesToParameter p295_0 "Coordinates" == false -- x2

-- spec/spread-capture-count: A = [1, 2, 3] \n  \n (A*).count
def p296_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p296_1 : List OwnerLevel := { parameters := [], properties := [] } :: p296_0
#guard selectOwnedDeclaration p296_0 "A" == .property 0
#guard elaboratesToParameter p296_0 "A" == false
#guard selectOwnedDeclaration p296_0 "count" == .property 1
#guard elaboratesToParameter p296_0 "count" == false

-- spec/repeated-spread-fixed-point: Collect(*items) = items \n A = [[1, 2], [3, 4]] \n  \n Collect(A*) \n Collect(A**) \n Collect((A*)*)
def p297_0 : List OwnerLevel := { parameters := [], properties := ["A", "Collect"] } :: prelude
def p297_1 : List OwnerLevel := { parameters := [], properties := [] } :: p297_0
def p297_2 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p297_0
#guard selectOwnedDeclaration p297_2 "items" == .parameter 0
#guard elaboratesToParameter p297_2 "items" == true
#guard selectOwnedDeclaration p297_0 "Collect" == .property 0 -- x3
#guard elaboratesToParameter p297_0 "Collect" == false -- x3
#guard selectOwnedDeclaration p297_0 "A" == .property 0 -- x3
#guard elaboratesToParameter p297_0 "A" == false -- x3

-- spec/repeated-spread-singleton-opens: Collect(*items) = items \n  \n Collect([[7]]*) \n Collect([[7]]**) \n Collect([7]*) \n Collect([7]**)
def p298_0 : List OwnerLevel := { parameters := [], properties := ["Collect"] } :: prelude
def p298_1 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p298_0
#guard selectOwnedDeclaration p298_1 "items" == .parameter 0
#guard elaboratesToParameter p298_1 "items" == true
#guard selectOwnedDeclaration p298_0 "Collect" == .property 0 -- x4
#guard elaboratesToParameter p298_0 "Collect" == false -- x4

-- spec/scalar-spread-neutral: Collect(*items) = items \n  \n Collect(5) \n Collect(5*)
def p299_0 : List OwnerLevel := { parameters := [], properties := ["Collect"] } :: prelude
def p299_1 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p299_0
#guard selectOwnedDeclaration p299_1 "items" == .parameter 0
#guard elaboratesToParameter p299_1 "items" == true
#guard selectOwnedDeclaration p299_0 "Collect" == .property 0 -- x2
#guard elaboratesToParameter p299_0 "Collect" == false -- x2

-- spec/select-spread-vs-capture-select: A = [[1, 2], [3, 4]] \n  \n (A[0])*, \n (A*)[0]
-- the same levels and decisions, 1 more:
--   spec/list-literal-spread-elements
def p300_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p300_1 : List OwnerLevel := { parameters := [], properties := [] } :: p300_0
#guard selectOwnedDeclaration p300_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p300_0 "A" == false -- x2

-- spec/fixed-call-preserves-boundaries: Pair = 10, 20 \n Add(x, y) = x + y \n  \n Add(Pair)
def p301_0 : List OwnerLevel := { parameters := [], properties := ["Pair", "Add"] } :: prelude
def p301_1 : List OwnerLevel := { parameters := [], properties := [] } :: p301_0
def p301_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p301_0
#guard selectOwnedDeclaration p301_2 "x" == .parameter 0
#guard elaboratesToParameter p301_2 "x" == true
#guard selectOwnedDeclaration p301_2 "y" == .parameter 0
#guard elaboratesToParameter p301_2 "y" == true
#guard selectOwnedDeclaration p301_0 "Add" == .property 0
#guard elaboratesToParameter p301_0 "Add" == false
#guard selectOwnedDeclaration p301_0 "Pair" == .property 0
#guard elaboratesToParameter p301_0 "Pair" == false

-- spec/spread-fills-remaining-slots: Tail = 2, 3 \n Use(a, b, c) = a + b + c \n  \n Use(1, Tail*)
def p302_0 : List OwnerLevel := { parameters := [], properties := ["Tail", "Use"] } :: prelude
def p302_1 : List OwnerLevel := { parameters := [], properties := [] } :: p302_0
def p302_2 : List OwnerLevel := { parameters := ["a", "b", "c"], properties := [] } :: p302_0
#guard selectOwnedDeclaration p302_2 "a" == .parameter 0
#guard elaboratesToParameter p302_2 "a" == true
#guard selectOwnedDeclaration p302_2 "b" == .parameter 0
#guard elaboratesToParameter p302_2 "b" == true
#guard selectOwnedDeclaration p302_2 "c" == .parameter 0
#guard elaboratesToParameter p302_2 "c" == true
#guard selectOwnedDeclaration p302_0 "Use" == .property 0
#guard elaboratesToParameter p302_0 "Use" == false
#guard selectOwnedDeclaration p302_0 "Tail" == .property 0
#guard elaboratesToParameter p302_0 "Tail" == false

-- spec/variadic-empty-arg-vs-spread: F(*a) = a.count \n F((), ())
def p303_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p303_1 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p303_0
#guard selectOwnedDeclaration p303_1 "a" == .parameter 0
#guard elaboratesToParameter p303_1 "a" == true
#guard selectOwnedDeclaration p303_1 "count" == .property 2
#guard elaboratesToParameter p303_1 "count" == false
#guard selectOwnedDeclaration p303_0 "F" == .property 0
#guard elaboratesToParameter p303_0 "F" == false

-- spec/decon-pair: x, y = 1, 2 \n x \n y
-- the same levels and decisions, 1 more:
--   spec/list-deconstruction-not-recursive
def p304_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "y"] } :: prelude
def p304_1 : List OwnerLevel := { parameters := [], properties := [] } :: p304_0
def p304_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p304_1
def p304_3 : List OwnerLevel := { parameters := [], properties := [] } :: p304_0
def p304_4 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p304_3
#guard selectOwnedDeclaration p304_2 "x" == .parameter 0
#guard elaboratesToParameter p304_2 "x" == true
#guard selectOwnedDeclaration p304_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p304_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p304_4 "y" == .parameter 0
#guard elaboratesToParameter p304_4 "y" == true
#guard selectOwnedDeclaration p304_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p304_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p304_0 "x" == .property 0
#guard elaboratesToParameter p304_0 "x" == false
#guard selectOwnedDeclaration p304_0 "y" == .property 0
#guard elaboratesToParameter p304_0 "y" == false

-- spec/decon-rhs-implicit-parameter: F = { \n     a, b = x, 10 \n     a + b \n } \n F(1)
def p305_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p305_1 : List OwnerLevel := { parameters := ["x"], properties := ["$deconstruct$0", "a", "b"] } :: p305_0
def p305_2 : List OwnerLevel := { parameters := [], properties := [] } :: p305_1
def p305_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p305_2
def p305_4 : List OwnerLevel := { parameters := [], properties := [] } :: p305_1
def p305_5 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p305_4
#guard selectOwnedDeclaration p305_1 "x" == .parameter 0
#guard elaboratesToParameter p305_1 "x" == true
#guard selectOwnedDeclaration p305_3 "a" == .parameter 0
#guard elaboratesToParameter p305_3 "a" == true
#guard selectOwnedDeclaration p305_2 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p305_2 "$deconstruct$0" == false
#guard selectOwnedDeclaration p305_5 "b" == .parameter 0
#guard elaboratesToParameter p305_5 "b" == true
#guard selectOwnedDeclaration p305_4 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p305_4 "$deconstruct$0" == false
#guard selectOwnedDeclaration p305_1 "a" == .property 0
#guard elaboratesToParameter p305_1 "a" == false
#guard selectOwnedDeclaration p305_1 "b" == .property 0
#guard elaboratesToParameter p305_1 "b" == false
#guard selectOwnedDeclaration p305_0 "F" == .property 0
#guard elaboratesToParameter p305_0 "F" == false

-- spec/decon-rhs-brace-scope: F = { \n     Q = 100 \n     a, b = { Q = 7 \n         Q, 10 } \n     a + b \n } \n F
def p306_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p306_1 : List OwnerLevel := { parameters := [], properties := ["Q", "$deconstruct$0", "a", "b"] } :: p306_0
def p306_2 : List OwnerLevel := { parameters := [], properties := [] } :: p306_1
def p306_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p306_1
def p306_4 : List OwnerLevel := { parameters := [], properties := [] } :: p306_3
def p306_5 : List OwnerLevel := { parameters := [], properties := [] } :: p306_1
def p306_6 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p306_5
def p306_7 : List OwnerLevel := { parameters := [], properties := [] } :: p306_1
def p306_8 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p306_7
#guard selectOwnedDeclaration p306_3 "Q" == .property 0
#guard elaboratesToParameter p306_3 "Q" == false
#guard selectOwnedDeclaration p306_6 "a" == .parameter 0
#guard elaboratesToParameter p306_6 "a" == true
#guard selectOwnedDeclaration p306_5 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p306_5 "$deconstruct$0" == false
#guard selectOwnedDeclaration p306_8 "b" == .parameter 0
#guard elaboratesToParameter p306_8 "b" == true
#guard selectOwnedDeclaration p306_7 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p306_7 "$deconstruct$0" == false
#guard selectOwnedDeclaration p306_1 "a" == .property 0
#guard elaboratesToParameter p306_1 "a" == false
#guard selectOwnedDeclaration p306_1 "b" == .property 0
#guard elaboratesToParameter p306_1 "b" == false
#guard selectOwnedDeclaration p306_0 "F" == .property 0
#guard elaboratesToParameter p306_0 "F" == false

-- spec/decon-rhs-lifted-parameter-order: P = x * 2 \n R = y * 3 \n F = { \n     a, b = P, 10 \n     R + a + b \n } \n F(1, 2)
def p307_0 : List OwnerLevel := { parameters := [], properties := ["P", "R", "F"] } :: prelude
def p307_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p307_0
def p307_2 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p307_0
def p307_3 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "a", "b"], forwarded := ["x", "y"] } :: p307_0
def p307_4 : List OwnerLevel := { parameters := [], properties := [] } :: p307_3
def p307_5 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p307_4
def p307_6 : List OwnerLevel := { parameters := [], properties := [] } :: p307_3
def p307_7 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p307_6
#guard selectOwnedDeclaration p307_1 "x" == .parameter 0
#guard elaboratesToParameter p307_1 "x" == true
#guard selectOwnedDeclaration p307_2 "y" == .parameter 0
#guard elaboratesToParameter p307_2 "y" == true
#guard selectOwnedDeclaration p307_3 "P" == .property 1
#guard elaboratesToParameter p307_3 "P" == false
#guard selectOwnedDeclaration p307_5 "a" == .parameter 0
#guard elaboratesToParameter p307_5 "a" == true
#guard selectOwnedDeclaration p307_4 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p307_4 "$deconstruct$0" == false
#guard selectOwnedDeclaration p307_7 "b" == .parameter 0
#guard elaboratesToParameter p307_7 "b" == true
#guard selectOwnedDeclaration p307_6 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p307_6 "$deconstruct$0" == false
#guard selectOwnedDeclaration p307_3 "R" == .property 1
#guard elaboratesToParameter p307_3 "R" == false
#guard selectOwnedDeclaration p307_3 "a" == .property 0
#guard elaboratesToParameter p307_3 "a" == false
#guard selectOwnedDeclaration p307_3 "b" == .property 0
#guard elaboratesToParameter p307_3 "b" == false
#guard selectOwnedDeclaration p307_0 "F" == .property 0
#guard elaboratesToParameter p307_0 "F" == false

-- spec/decon-collecting-head: *head, last = 1, 2, 3 \n head \n last
def p308_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "head", "last"] } :: prelude
def p308_1 : List OwnerLevel := { parameters := [], properties := [] } :: p308_0
def p308_2 : List OwnerLevel := { parameters := ["head", "last"], properties := [] } :: p308_1
def p308_3 : List OwnerLevel := { parameters := [], properties := [] } :: p308_0
def p308_4 : List OwnerLevel := { parameters := ["head", "last"], properties := [] } :: p308_3
#guard selectOwnedDeclaration p308_2 "head" == .parameter 0
#guard elaboratesToParameter p308_2 "head" == true
#guard selectOwnedDeclaration p308_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p308_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p308_4 "last" == .parameter 0
#guard elaboratesToParameter p308_4 "last" == true
#guard selectOwnedDeclaration p308_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p308_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p308_0 "head" == .property 0
#guard elaboratesToParameter p308_0 "head" == false
#guard selectOwnedDeclaration p308_0 "last" == .property 0
#guard elaboratesToParameter p308_0 "last" == false

-- spec/decon-collecting-middle: x, *middle, z = 1, 2, 3, 4 \n middle
def p309_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "middle", "z"] } :: prelude
def p309_1 : List OwnerLevel := { parameters := [], properties := [] } :: p309_0
def p309_2 : List OwnerLevel := { parameters := ["x", "middle", "z"], properties := [] } :: p309_1
def p309_3 : List OwnerLevel := { parameters := [], properties := [] } :: p309_0
def p309_4 : List OwnerLevel := { parameters := ["x", "middle", "z"], properties := [] } :: p309_3
def p309_5 : List OwnerLevel := { parameters := [], properties := [] } :: p309_0
def p309_6 : List OwnerLevel := { parameters := ["x", "middle", "z"], properties := [] } :: p309_5
#guard selectOwnedDeclaration p309_2 "x" == .parameter 0
#guard elaboratesToParameter p309_2 "x" == true
#guard selectOwnedDeclaration p309_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p309_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p309_4 "middle" == .parameter 0
#guard elaboratesToParameter p309_4 "middle" == true
#guard selectOwnedDeclaration p309_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p309_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p309_6 "z" == .parameter 0
#guard elaboratesToParameter p309_6 "z" == true
#guard selectOwnedDeclaration p309_5 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p309_5 "$deconstruct$0" == false
#guard selectOwnedDeclaration p309_0 "middle" == .property 0
#guard elaboratesToParameter p309_0 "middle" == false

-- spec/decon-empty-collecting: x, *rest = 1 \n rest \n x
def p310_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "rest"] } :: prelude
def p310_1 : List OwnerLevel := { parameters := [], properties := [] } :: p310_0
def p310_2 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p310_1
def p310_3 : List OwnerLevel := { parameters := [], properties := [] } :: p310_0
def p310_4 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p310_3
#guard selectOwnedDeclaration p310_2 "x" == .parameter 0
#guard elaboratesToParameter p310_2 "x" == true
#guard selectOwnedDeclaration p310_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p310_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p310_4 "rest" == .parameter 0
#guard elaboratesToParameter p310_4 "rest" == true
#guard selectOwnedDeclaration p310_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p310_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p310_0 "rest" == .property 0
#guard elaboratesToParameter p310_0 "rest" == false
#guard selectOwnedDeclaration p310_0 "x" == .property 0
#guard elaboratesToParameter p310_0 "x" == false

-- spec/decon-unpacks-stored-value: A = 1, 2, 3 \n x, y, z = A \n y
def p311_0 : List OwnerLevel := { parameters := [], properties := ["A", "$deconstruct$0", "x", "y", "z"] } :: prelude
def p311_1 : List OwnerLevel := { parameters := [], properties := [] } :: p311_0
def p311_2 : List OwnerLevel := { parameters := [], properties := [] } :: p311_0
def p311_3 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p311_2
def p311_4 : List OwnerLevel := { parameters := [], properties := [] } :: p311_0
def p311_5 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p311_4
def p311_6 : List OwnerLevel := { parameters := [], properties := [] } :: p311_0
def p311_7 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p311_6
#guard selectOwnedDeclaration p311_0 "A" == .property 0
#guard elaboratesToParameter p311_0 "A" == false
#guard selectOwnedDeclaration p311_3 "x" == .parameter 0
#guard elaboratesToParameter p311_3 "x" == true
#guard selectOwnedDeclaration p311_2 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p311_2 "$deconstruct$0" == false
#guard selectOwnedDeclaration p311_5 "y" == .parameter 0
#guard elaboratesToParameter p311_5 "y" == true
#guard selectOwnedDeclaration p311_4 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p311_4 "$deconstruct$0" == false
#guard selectOwnedDeclaration p311_7 "z" == .parameter 0
#guard elaboratesToParameter p311_7 "z" == true
#guard selectOwnedDeclaration p311_6 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p311_6 "$deconstruct$0" == false
#guard selectOwnedDeclaration p311_0 "y" == .property 0
#guard elaboratesToParameter p311_0 "y" == false

-- spec/decon-tutorial-full: A = 1, 2, 3, 4, 5 \n  \n x, *y, z = A \n x \n y \n z
def p312_0 : List OwnerLevel := { parameters := [], properties := ["A", "$deconstruct$0", "x", "y", "z"] } :: prelude
def p312_1 : List OwnerLevel := { parameters := [], properties := [] } :: p312_0
def p312_2 : List OwnerLevel := { parameters := [], properties := [] } :: p312_0
def p312_3 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p312_2
def p312_4 : List OwnerLevel := { parameters := [], properties := [] } :: p312_0
def p312_5 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p312_4
def p312_6 : List OwnerLevel := { parameters := [], properties := [] } :: p312_0
def p312_7 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p312_6
#guard selectOwnedDeclaration p312_0 "A" == .property 0
#guard elaboratesToParameter p312_0 "A" == false
#guard selectOwnedDeclaration p312_3 "x" == .parameter 0
#guard elaboratesToParameter p312_3 "x" == true
#guard selectOwnedDeclaration p312_2 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p312_2 "$deconstruct$0" == false
#guard selectOwnedDeclaration p312_5 "y" == .parameter 0
#guard elaboratesToParameter p312_5 "y" == true
#guard selectOwnedDeclaration p312_4 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p312_4 "$deconstruct$0" == false
#guard selectOwnedDeclaration p312_7 "z" == .parameter 0
#guard elaboratesToParameter p312_7 "z" == true
#guard selectOwnedDeclaration p312_6 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p312_6 "$deconstruct$0" == false
#guard selectOwnedDeclaration p312_0 "x" == .property 0
#guard elaboratesToParameter p312_0 "x" == false
#guard selectOwnedDeclaration p312_0 "y" == .property 0
#guard elaboratesToParameter p312_0 "y" == false
#guard selectOwnedDeclaration p312_0 "z" == .property 0
#guard elaboratesToParameter p312_0 "z" == false

-- spec/decon-lone-collecting: *all = 1, 2, 3 \n all
def p313_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "all"] } :: prelude
def p313_1 : List OwnerLevel := { parameters := [], properties := [] } :: p313_0
def p313_2 : List OwnerLevel := { parameters := ["all"], properties := [] } :: p313_1
#guard selectOwnedDeclaration p313_2 "all" == .parameter 0
#guard elaboratesToParameter p313_2 "all" == true
#guard selectOwnedDeclaration p313_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p313_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p313_0 "all" == .property 0
#guard elaboratesToParameter p313_0 "all" == false

-- spec/variadic-grouped-and-spread: A = 1, 2, 3, 4, 5 \n  \n G(*x) = x.sum \n  \n G(A*) \n G(1, 2, 3, 4, 5)
def p314_0 : List OwnerLevel := { parameters := [], properties := ["A", "G"] } :: prelude
def p314_1 : List OwnerLevel := { parameters := [], properties := [] } :: p314_0
def p314_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p314_0
#guard selectOwnedDeclaration p314_2 "x" == .parameter 0
#guard elaboratesToParameter p314_2 "x" == true
#guard selectOwnedDeclaration p314_2 "sum" == .property 2
#guard elaboratesToParameter p314_2 "sum" == false
#guard selectOwnedDeclaration p314_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p314_0 "G" == false -- x2
#guard selectOwnedDeclaration p314_0 "A" == .property 0
#guard elaboratesToParameter p314_0 "A" == false

-- spec/variadic-siblings-preserved: A = 1, 2 \n B = 3, 4 \n  \n G(*x) = x.count \n  \n G(A, B) \n G(A*, B*)
def p315_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "G"] } :: prelude
def p315_1 : List OwnerLevel := { parameters := [], properties := [] } :: p315_0
def p315_2 : List OwnerLevel := { parameters := [], properties := [] } :: p315_0
def p315_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p315_0
#guard selectOwnedDeclaration p315_3 "x" == .parameter 0
#guard elaboratesToParameter p315_3 "x" == true
#guard selectOwnedDeclaration p315_3 "count" == .property 2
#guard elaboratesToParameter p315_3 "count" == false
#guard selectOwnedDeclaration p315_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p315_0 "G" == false -- x2
#guard selectOwnedDeclaration p315_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p315_0 "A" == false -- x2
#guard selectOwnedDeclaration p315_0 "B" == .property 0 -- x2
#guard elaboratesToParameter p315_0 "B" == false -- x2

-- spec/variadic-forwarding-list-spread: Target(*items) = items \n Forward(*items) = Target(items*) \n  \n Forward(1, 2) \n Forward([1, 2])
def p316_0 : List OwnerLevel := { parameters := [], properties := ["Target", "Forward"] } :: prelude
def p316_1 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p316_0
def p316_2 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p316_0
#guard selectOwnedDeclaration p316_1 "items" == .parameter 0
#guard elaboratesToParameter p316_1 "items" == true
#guard selectOwnedDeclaration p316_2 "Target" == .property 1
#guard elaboratesToParameter p316_2 "Target" == false
#guard selectOwnedDeclaration p316_2 "items" == .parameter 0
#guard elaboratesToParameter p316_2 "items" == true
#guard selectOwnedDeclaration p316_0 "Forward" == .property 0 -- x2
#guard elaboratesToParameter p316_0 "Forward" == false -- x2

-- spec/implicit-forwarding-source-kind: Target(tag, *items) = items \n Use(tag, items) = Target \n UseVariadic(tag, *items) = Target \n  \n Use(0, [1, 2]) \n Use(0, (1, 2)) \n UseVariadic(0, 1, 2)
def p317_0 : List OwnerLevel := { parameters := [], properties := ["Target", "Use", "UseVariadic"] } :: prelude
def p317_1 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p317_0
def p317_2 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p317_0
def p317_3 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p317_0
#guard selectOwnedDeclaration p317_1 "items" == .parameter 0
#guard elaboratesToParameter p317_1 "items" == true
#guard selectOwnedDeclaration p317_2 "Target" == .property 1
#guard elaboratesToParameter p317_2 "Target" == false
#guard selectOwnedDeclaration p317_3 "Target" == .property 1
#guard elaboratesToParameter p317_3 "Target" == false
#guard selectOwnedDeclaration p317_0 "Use" == .property 0 -- x2
#guard elaboratesToParameter p317_0 "Use" == false -- x2
#guard selectOwnedDeclaration p317_0 "UseVariadic" == .property 0
#guard elaboratesToParameter p317_0 "UseVariadic" == false

-- spec/variadic-receiver-distinction: Inspect(*items) = items \n A = [1, 2, 3] \n  \n Inspect(A) \n Inspect(A*)
def p318_0 : List OwnerLevel := { parameters := [], properties := ["A", "Inspect"] } :: prelude
def p318_1 : List OwnerLevel := { parameters := [], properties := [] } :: p318_0
def p318_2 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p318_0
#guard selectOwnedDeclaration p318_2 "items" == .parameter 0
#guard elaboratesToParameter p318_2 "items" == true
#guard selectOwnedDeclaration p318_0 "Inspect" == .property 0 -- x2
#guard elaboratesToParameter p318_0 "Inspect" == false -- x2
#guard selectOwnedDeclaration p318_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p318_0 "A" == false -- x2

-- spec/dot-receiver-passes-a-value: Mean(*Vector) = Vector.sum / Vector.count \n  \n Mean(1, 2, 3) \n (1, 2, 3)*.Mean \n [1, 2, 3]*.Mean
def p319_0 : List OwnerLevel := { parameters := [], properties := ["Mean"] } :: prelude
def p319_1 : List OwnerLevel := { parameters := ["Vector"], properties := [] } :: p319_0
#guard selectOwnedDeclaration p319_1 "Vector" == .parameter 0 -- x2
#guard elaboratesToParameter p319_1 "Vector" == true -- x2
#guard selectOwnedDeclaration p319_1 "sum" == .property 2
#guard elaboratesToParameter p319_1 "sum" == false
#guard selectOwnedDeclaration p319_1 "count" == .property 2
#guard elaboratesToParameter p319_1 "count" == false
#guard selectOwnedDeclaration p319_0 "Mean" == .property 0 -- x3
#guard elaboratesToParameter p319_0 "Mean" == false -- x3

-- spec/values-stay-values: Coll(*xs) = xs \n Cnt(*xs) = xs.count \n CntValue(x) = x.count \n  \n Coll((1, 2)) \n Coll([1, 2]) \n Coll((1, 2)*) \n Cnt((10, 7)) \n CntValue((10, 7))
def p320_0 : List OwnerLevel := { parameters := [], properties := ["Coll", "Cnt", "CntValue"] } :: prelude
def p320_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p320_0
def p320_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p320_0
def p320_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p320_0
#guard selectOwnedDeclaration p320_1 "xs" == .parameter 0
#guard elaboratesToParameter p320_1 "xs" == true
#guard selectOwnedDeclaration p320_2 "xs" == .parameter 0
#guard elaboratesToParameter p320_2 "xs" == true
#guard selectOwnedDeclaration p320_2 "count" == .property 2
#guard elaboratesToParameter p320_2 "count" == false
#guard selectOwnedDeclaration p320_3 "x" == .parameter 0
#guard elaboratesToParameter p320_3 "x" == true
#guard selectOwnedDeclaration p320_3 "count" == .property 2
#guard elaboratesToParameter p320_3 "count" == false
#guard selectOwnedDeclaration p320_0 "Coll" == .property 0 -- x3
#guard elaboratesToParameter p320_0 "Coll" == false -- x3
#guard selectOwnedDeclaration p320_0 "Cnt" == .property 0
#guard elaboratesToParameter p320_0 "Cnt" == false
#guard selectOwnedDeclaration p320_0 "CntValue" == .property 0
#guard elaboratesToParameter p320_0 "CntValue" == false

-- spec/callback-element-is-one-argument: AddPair((x, y)) = x + y \n LAddPair([x, y]) = x + y \n  \n map([(1, 2)], AddPair) \n map([[1, 2]], LAddPair)
def p321_0 : List OwnerLevel := { parameters := [], properties := ["AddPair", "LAddPair"] } :: prelude
def p321_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p321_0
def p321_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p321_0
#guard selectOwnedDeclaration p321_1 "x" == .parameter 0
#guard elaboratesToParameter p321_1 "x" == true
#guard selectOwnedDeclaration p321_1 "y" == .parameter 0
#guard elaboratesToParameter p321_1 "y" == true
#guard selectOwnedDeclaration p321_2 "x" == .parameter 0
#guard elaboratesToParameter p321_2 "x" == true
#guard selectOwnedDeclaration p321_2 "y" == .parameter 0
#guard elaboratesToParameter p321_2 "y" == true
#guard selectOwnedDeclaration p321_0 "map" == .property 1 -- x2
#guard elaboratesToParameter p321_0 "map" == false -- x2
#guard selectOwnedDeclaration p321_0 "AddPair" == .property 0
#guard elaboratesToParameter p321_0 "AddPair" == false
#guard selectOwnedDeclaration p321_0 "LAddPair" == .property 0
#guard elaboratesToParameter p321_0 "LAddPair" == false

-- spec/parentheses-group-syntax: Collect(*items) = items \n S = 1, 2 \n L = [1, 2] \n E = () \n  \n Collect(S), Collect((S)), Collect(((S))) \n Collect(L), Collect((L)) \n Collect(E), Collect((E)) \n S.Collect, (S).Collect, ((S)).Collect \n E*.Collect, (E)*.Collect
def p322_0 : List OwnerLevel := { parameters := [], properties := ["S", "L", "E", "Collect"] } :: prelude
def p322_1 : List OwnerLevel := { parameters := [], properties := [] } :: p322_0
def p322_2 : List OwnerLevel := { parameters := [], properties := [] } :: p322_0
def p322_3 : List OwnerLevel := { parameters := [], properties := [] } :: p322_0
def p322_4 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p322_0
#guard selectOwnedDeclaration p322_4 "items" == .parameter 0
#guard elaboratesToParameter p322_4 "items" == true
#guard selectOwnedDeclaration p322_0 "Collect" == .property 0 -- x12
#guard elaboratesToParameter p322_0 "Collect" == false -- x12
#guard selectOwnedDeclaration p322_0 "S" == .property 0 -- x6
#guard elaboratesToParameter p322_0 "S" == false -- x6
#guard selectOwnedDeclaration p322_0 "L" == .property 0 -- x2
#guard elaboratesToParameter p322_0 "L" == false -- x2
#guard selectOwnedDeclaration p322_0 "E" == .property 0 -- x4
#guard elaboratesToParameter p322_0 "E" == false -- x4

-- spec/mixed-collecting-parameter: F(x, *y, z) = x + y.sum + z \n F(1, 2, 3, 4, 5)
def p323_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p323_1 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p323_0
#guard selectOwnedDeclaration p323_1 "x" == .parameter 0
#guard elaboratesToParameter p323_1 "x" == true
#guard selectOwnedDeclaration p323_1 "y" == .parameter 0
#guard elaboratesToParameter p323_1 "y" == true
#guard selectOwnedDeclaration p323_1 "sum" == .property 2
#guard elaboratesToParameter p323_1 "sum" == false
#guard selectOwnedDeclaration p323_1 "z" == .parameter 0
#guard elaboratesToParameter p323_1 "z" == true
#guard selectOwnedDeclaration p323_0 "F" == .property 0
#guard elaboratesToParameter p323_0 "F" == false

-- spec/mixed-front-back-family: Arg = 1, 2, 3 \n  \n Head(first, *rest) = first \n Tail(first, *rest) = rest \n Init(*init, last) = init \n Last(*init, last) = last \n  \n Head(1, (2, 3)) \n Tail(1, (2, 3)) \n Init((1, 2), 3) \n Last(Arg, 3)
def p324_0 : List OwnerLevel := { parameters := [], properties := ["Arg", "Head", "Tail", "Init", "Last"] } :: prelude
def p324_1 : List OwnerLevel := { parameters := [], properties := [] } :: p324_0
def p324_2 : List OwnerLevel := { parameters := ["first", "rest"], properties := [] } :: p324_0
def p324_3 : List OwnerLevel := { parameters := ["first", "rest"], properties := [] } :: p324_0
def p324_4 : List OwnerLevel := { parameters := ["init", "last"], properties := [] } :: p324_0
def p324_5 : List OwnerLevel := { parameters := ["init", "last"], properties := [] } :: p324_0
#guard selectOwnedDeclaration p324_2 "first" == .parameter 0
#guard elaboratesToParameter p324_2 "first" == true
#guard selectOwnedDeclaration p324_3 "rest" == .parameter 0
#guard elaboratesToParameter p324_3 "rest" == true
#guard selectOwnedDeclaration p324_4 "init" == .parameter 0
#guard elaboratesToParameter p324_4 "init" == true
#guard selectOwnedDeclaration p324_5 "last" == .parameter 0
#guard elaboratesToParameter p324_5 "last" == true
#guard selectOwnedDeclaration p324_0 "Head" == .property 0
#guard elaboratesToParameter p324_0 "Head" == false
#guard selectOwnedDeclaration p324_0 "Tail" == .property 0
#guard elaboratesToParameter p324_0 "Tail" == false
#guard selectOwnedDeclaration p324_0 "Init" == .property 0
#guard elaboratesToParameter p324_0 "Init" == false
#guard selectOwnedDeclaration p324_0 "Last" == .property 0
#guard elaboratesToParameter p324_0 "Last" == false
#guard selectOwnedDeclaration p324_0 "Arg" == .property 0
#guard elaboratesToParameter p324_0 "Arg" == false

-- spec/collecting-minimum-arity: F(first, *middle, last) = middle \n  \n F(1, 2) \n F(1, 2, 3)
def p325_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p325_1 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p325_0
#guard selectOwnedDeclaration p325_1 "middle" == .parameter 0
#guard elaboratesToParameter p325_1 "middle" == true
#guard selectOwnedDeclaration p325_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p325_0 "F" == false -- x2

-- spec/variadic-grouped-vs-spread: H(h, *t) = t \n H((1, 2))
def p326_0 : List OwnerLevel := { parameters := [], properties := ["H"] } :: prelude
def p326_1 : List OwnerLevel := { parameters := ["h", "t"], properties := [] } :: p326_0
#guard selectOwnedDeclaration p326_1 "t" == .parameter 0
#guard elaboratesToParameter p326_1 "t" == true
#guard selectOwnedDeclaration p326_0 "H" == .property 0
#guard elaboratesToParameter p326_0 "H" == false

-- spec/variadic-nested-not-flattened: Arg = (1, 2), (3, 4) \n  \n Many(*values) = values.count \n Flattened = atoms(Arg).count \n  \n Many(Arg*) \n Flattened
def p327_0 : List OwnerLevel := { parameters := [], properties := ["Arg", "Flattened", "Many"] } :: prelude
def p327_1 : List OwnerLevel := { parameters := [], properties := [] } :: p327_0
def p327_2 : List OwnerLevel := { parameters := [], properties := [] } :: p327_0
def p327_3 : List OwnerLevel := { parameters := ["values"], properties := [] } :: p327_0
#guard selectOwnedDeclaration p327_2 "atoms" == .property 2
#guard elaboratesToParameter p327_2 "atoms" == false
#guard selectOwnedDeclaration p327_2 "Arg" == .property 1
#guard elaboratesToParameter p327_2 "Arg" == false
#guard selectOwnedDeclaration p327_2 "count" == .property 2
#guard elaboratesToParameter p327_2 "count" == false
#guard selectOwnedDeclaration p327_3 "values" == .parameter 0
#guard elaboratesToParameter p327_3 "values" == true
#guard selectOwnedDeclaration p327_3 "count" == .property 2
#guard elaboratesToParameter p327_3 "count" == false
#guard selectOwnedDeclaration p327_0 "Many" == .property 0
#guard elaboratesToParameter p327_0 "Many" == false
#guard selectOwnedDeclaration p327_0 "Arg" == .property 0
#guard elaboratesToParameter p327_0 "Arg" == false
#guard selectOwnedDeclaration p327_0 "Flattened" == .property 0
#guard elaboratesToParameter p327_0 "Flattened" == false

-- spec/supply-vs-value-patterns: CountValues(*values) = values.count \n CountSequenceValue((*values)) = values.count \n  \n CountValues() \n CountValues(1, 2, 3) \n CountValues((1, 2, 3)) \n CountSequenceValue((1, 2, 3))
def p328_0 : List OwnerLevel := { parameters := [], properties := ["CountValues", "CountSequenceValue"] } :: prelude
def p328_1 : List OwnerLevel := { parameters := ["values"], properties := [] } :: p328_0
def p328_2 : List OwnerLevel := { parameters := ["values"], properties := [] } :: p328_0
#guard selectOwnedDeclaration p328_1 "values" == .parameter 0
#guard elaboratesToParameter p328_1 "values" == true
#guard selectOwnedDeclaration p328_1 "count" == .property 2
#guard elaboratesToParameter p328_1 "count" == false
#guard selectOwnedDeclaration p328_2 "values" == .parameter 0
#guard elaboratesToParameter p328_2 "values" == true
#guard selectOwnedDeclaration p328_2 "count" == .property 2
#guard elaboratesToParameter p328_2 "count" == false
#guard selectOwnedDeclaration p328_0 "CountValues" == .property 0 -- x3
#guard elaboratesToParameter p328_0 "CountValues" == false -- x3
#guard selectOwnedDeclaration p328_0 "CountSequenceValue" == .property 0
#guard elaboratesToParameter p328_0 "CountSequenceValue" == false

-- spec/list-patterns-cover-every-cardinality: L([*xs]) = xs \n Only([x]) = x \n Pair([x, y]) = x + y \n Ends([first, *middle, last]) = first, middle, last \n  \n L([]), L([1]), L([1, 2]) \n Only([10]) \n Pair([10, 20]) \n Ends([1, 2, 3, 4])
def p329_0 : List OwnerLevel := { parameters := [], properties := ["L", "Only", "Pair", "Ends"] } :: prelude
def p329_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p329_0
def p329_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p329_0
def p329_3 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p329_0
def p329_4 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p329_0
#guard selectOwnedDeclaration p329_1 "xs" == .parameter 0
#guard elaboratesToParameter p329_1 "xs" == true
#guard selectOwnedDeclaration p329_2 "x" == .parameter 0
#guard elaboratesToParameter p329_2 "x" == true
#guard selectOwnedDeclaration p329_3 "x" == .parameter 0
#guard elaboratesToParameter p329_3 "x" == true
#guard selectOwnedDeclaration p329_3 "y" == .parameter 0
#guard elaboratesToParameter p329_3 "y" == true
#guard selectOwnedDeclaration p329_4 "first" == .parameter 0
#guard elaboratesToParameter p329_4 "first" == true
#guard selectOwnedDeclaration p329_4 "middle" == .parameter 0
#guard elaboratesToParameter p329_4 "middle" == true
#guard selectOwnedDeclaration p329_4 "last" == .parameter 0
#guard elaboratesToParameter p329_4 "last" == true
#guard selectOwnedDeclaration p329_0 "L" == .property 0 -- x3
#guard elaboratesToParameter p329_0 "L" == false -- x3
#guard selectOwnedDeclaration p329_0 "Only" == .property 0
#guard elaboratesToParameter p329_0 "Only" == false
#guard selectOwnedDeclaration p329_0 "Pair" == .property 0
#guard elaboratesToParameter p329_0 "Pair" == false
#guard selectOwnedDeclaration p329_0 "Ends" == .property 0
#guard elaboratesToParameter p329_0 "Ends" == false

-- spec/nested-structural-patterns-keep-their-kind: F(([x, y], z)) = x + y + z \n G([(x, y), z]) = x + y + z \n  \n F(([10, 20], 30)) \n G([(1, 2), 3])
def p330_0 : List OwnerLevel := { parameters := [], properties := ["F", "G"] } :: prelude
def p330_1 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p330_0
def p330_2 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p330_0
#guard selectOwnedDeclaration p330_1 "x" == .parameter 0
#guard elaboratesToParameter p330_1 "x" == true
#guard selectOwnedDeclaration p330_1 "y" == .parameter 0
#guard elaboratesToParameter p330_1 "y" == true
#guard selectOwnedDeclaration p330_1 "z" == .parameter 0
#guard elaboratesToParameter p330_1 "z" == true
#guard selectOwnedDeclaration p330_2 "x" == .parameter 0
#guard elaboratesToParameter p330_2 "x" == true
#guard selectOwnedDeclaration p330_2 "y" == .parameter 0
#guard elaboratesToParameter p330_2 "y" == true
#guard selectOwnedDeclaration p330_2 "z" == .parameter 0
#guard elaboratesToParameter p330_2 "z" == true
#guard selectOwnedDeclaration p330_0 "F" == .property 0
#guard elaboratesToParameter p330_0 "F" == false
#guard selectOwnedDeclaration p330_0 "G" == .property 0
#guard elaboratesToParameter p330_0 "G" == false

-- spec/structural-patterns-open-only-their-own-kind: PairSum((x, y)) = x + y \n ListSum([x, y]) = x + y \n  \n PairSum((2, 3)) \n ListSum([2, 3])
def p331_0 : List OwnerLevel := { parameters := [], properties := ["PairSum", "ListSum"] } :: prelude
def p331_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p331_0
def p331_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p331_0
#guard selectOwnedDeclaration p331_1 "x" == .parameter 0
#guard elaboratesToParameter p331_1 "x" == true
#guard selectOwnedDeclaration p331_1 "y" == .parameter 0
#guard elaboratesToParameter p331_1 "y" == true
#guard selectOwnedDeclaration p331_2 "x" == .parameter 0
#guard elaboratesToParameter p331_2 "x" == true
#guard selectOwnedDeclaration p331_2 "y" == .parameter 0
#guard elaboratesToParameter p331_2 "y" == true
#guard selectOwnedDeclaration p331_0 "PairSum" == .property 0
#guard elaboratesToParameter p331_0 "PairSum" == false
#guard selectOwnedDeclaration p331_0 "ListSum" == .property 0
#guard elaboratesToParameter p331_0 "ListSum" == false

-- spec/binding-failure-outranks-repeated-name-conflict: Bad = 1 / 0 \n P(x, x, (a, b)) = a \n  \n P(1, 2, Bad)
def p332_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "P"] } :: prelude
def p332_1 : List OwnerLevel := { parameters := [], properties := [] } :: p332_0
def p332_2 : List OwnerLevel := { parameters := ["x", "a", "b"], properties := [] } :: p332_0
#guard selectOwnedDeclaration p332_2 "a" == .parameter 0
#guard elaboratesToParameter p332_2 "a" == true
#guard selectOwnedDeclaration p332_0 "P" == .property 0
#guard elaboratesToParameter p332_0 "P" == false
#guard selectOwnedDeclaration p332_0 "Bad" == .property 0
#guard elaboratesToParameter p332_0 "Bad" == false

-- spec/repeated-name-binding-is-order-independent: A = 5 \n B = 2 + 3 \n P(f, f, f) = f \n  \n P(A, 5, B)
def p333_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "P"] } :: prelude
def p333_1 : List OwnerLevel := { parameters := [], properties := [] } :: p333_0
def p333_2 : List OwnerLevel := { parameters := [], properties := [] } :: p333_0
def p333_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p333_0
#guard selectOwnedDeclaration p333_3 "f" == .parameter 0
#guard elaboratesToParameter p333_3 "f" == true
#guard selectOwnedDeclaration p333_0 "P" == .property 0
#guard elaboratesToParameter p333_0 "P" == false
#guard selectOwnedDeclaration p333_0 "A" == .property 0
#guard elaboratesToParameter p333_0 "A" == false
#guard selectOwnedDeclaration p333_0 "B" == .property 0
#guard elaboratesToParameter p333_0 "B" == false

-- spec/repeated-equal-values-require-one-callable-identity: A(*xs) = 5 \n B(*xs) = 5 + xs.count \n P(f, f) = f(1) \n P(A, B)
def p334_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "P"] } :: prelude
def p334_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p334_0
def p334_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p334_0
def p334_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p334_0
#guard selectOwnedDeclaration p334_2 "xs" == .parameter 0
#guard elaboratesToParameter p334_2 "xs" == true
#guard selectOwnedDeclaration p334_2 "count" == .property 2
#guard elaboratesToParameter p334_2 "count" == false
#guard selectOwnedDeclaration p334_3 "f" == .parameter 0
#guard elaboratesToParameter p334_3 "f" == true
#guard selectOwnedDeclaration p334_0 "P" == .property 0
#guard elaboratesToParameter p334_0 "P" == false
#guard selectOwnedDeclaration p334_0 "A" == .property 0
#guard elaboratesToParameter p334_0 "A" == false
#guard selectOwnedDeclaration p334_0 "B" == .property 0
#guard elaboratesToParameter p334_0 "B" == false

-- spec/implicit-forwarding-is-by-binding-name: F(x) = x + 1 \n G(x) = x * 2 \n H = F + G \n  \n Common(x, x) = x \n Twice = Common * 2 \n  \n H(3) \n Twice(7)
def p335_0 : List OwnerLevel := { parameters := [], properties := ["H", "Twice", "F", "G", "Common"] } :: prelude
def p335_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p335_0
def p335_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p335_0
def p335_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p335_0
def p335_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p335_0
def p335_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p335_0
#guard selectOwnedDeclaration p335_1 "F" == .property 1
#guard elaboratesToParameter p335_1 "F" == false
#guard selectOwnedDeclaration p335_1 "G" == .property 1
#guard elaboratesToParameter p335_1 "G" == false
#guard selectOwnedDeclaration p335_2 "Common" == .property 1
#guard elaboratesToParameter p335_2 "Common" == false
#guard selectOwnedDeclaration p335_3 "x" == .parameter 0
#guard elaboratesToParameter p335_3 "x" == true
#guard selectOwnedDeclaration p335_4 "x" == .parameter 0
#guard elaboratesToParameter p335_4 "x" == true
#guard selectOwnedDeclaration p335_5 "x" == .parameter 0
#guard elaboratesToParameter p335_5 "x" == true
#guard selectOwnedDeclaration p335_0 "H" == .property 0
#guard elaboratesToParameter p335_0 "H" == false
#guard selectOwnedDeclaration p335_0 "Twice" == .property 0
#guard elaboratesToParameter p335_0 "Twice" == false

-- spec/formula-lifting-is-one-law-for-every-callable: Lib = { \n     public Inc(x) = x + 1 \n } \n E(0) = 100 \n E(n) = n \n Total = count + 0 \n Next = Lib.Inc + 0 \n Fam = E + 1 \n  \n Total((1, 2, 3)) \n Next(4) \n Fam(0)
def p336_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Total", "Next", "Fam", "E"] } :: prelude
def p336_1 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: p336_0
def p336_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p336_1
def p336_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["collection"] } :: p336_0
def p336_4 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p336_0
def p336_5 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["n"] } :: p336_0
def p336_6 : List OwnerLevel := { parameters := [], properties := [] } :: p336_0
def p336_7 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p336_0
#guard selectOwnedDeclaration p336_2 "x" == .parameter 0
#guard elaboratesToParameter p336_2 "x" == true
#guard selectOwnedDeclaration p336_3 "count" == .property 2
#guard elaboratesToParameter p336_3 "count" == false
#guard selectOwnedDeclaration p336_4 "Lib" == .property 1
#guard elaboratesToParameter p336_4 "Lib" == false
#guard selectOwnedDeclaration p336_4 "Inc" == .none
#guard elaboratesToParameter p336_4 "Inc" == false
#guard selectOwnedDeclaration p336_5 "E" == .property 1
#guard elaboratesToParameter p336_5 "E" == false
#guard selectOwnedDeclaration p336_7 "n" == .parameter 0
#guard elaboratesToParameter p336_7 "n" == true
#guard selectOwnedDeclaration p336_0 "Total" == .property 0
#guard elaboratesToParameter p336_0 "Total" == false
#guard selectOwnedDeclaration p336_0 "Next" == .property 0
#guard elaboratesToParameter p336_0 "Next" == false
#guard selectOwnedDeclaration p336_0 "Fam" == .property 0
#guard elaboratesToParameter p336_0 "Fam" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family E

-- spec/formula-lifting-follows-the-consumers-role: Inc(x) = x + 1 \n Apply(f) = f(10) \n  \n Values = [Inc, Inc * 2] \n Kept = Apply(Inc) \n Branch = if(true, Inc, 0) \n  \n Values(4) \n Kept \n Branch(4)
def p337_0 : List OwnerLevel := { parameters := [], properties := ["Values", "Kept", "Branch", "Inc", "Apply"] } :: prelude
def p337_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p337_0
def p337_2 : List OwnerLevel := { parameters := [], properties := [] } :: p337_0
def p337_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p337_0
def p337_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p337_0
def p337_5 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p337_0
#guard selectOwnedDeclaration p337_1 "Inc" == .property 1 -- x2
#guard elaboratesToParameter p337_1 "Inc" == false -- x2
#guard selectOwnedDeclaration p337_2 "Apply" == .property 1
#guard elaboratesToParameter p337_2 "Apply" == false
#guard selectOwnedDeclaration p337_2 "Inc" == .property 1
#guard elaboratesToParameter p337_2 "Inc" == false
#guard selectOwnedDeclaration p337_3 "if" == .property 2
#guard elaboratesToParameter p337_3 "if" == false
#guard selectOwnedDeclaration p337_3 "Inc" == .property 1
#guard elaboratesToParameter p337_3 "Inc" == false
#guard selectOwnedDeclaration p337_4 "x" == .parameter 0
#guard elaboratesToParameter p337_4 "x" == true
#guard selectOwnedDeclaration p337_5 "f" == .parameter 0
#guard elaboratesToParameter p337_5 "f" == true
#guard selectOwnedDeclaration p337_0 "Values" == .property 0
#guard elaboratesToParameter p337_0 "Values" == false
#guard selectOwnedDeclaration p337_0 "Kept" == .property 0
#guard elaboratesToParameter p337_0 "Kept" == false
#guard selectOwnedDeclaration p337_0 "Branch" == .property 0
#guard elaboratesToParameter p337_0 "Branch" == false

-- spec/unliftable-clause-family: S(1) = 1 \n S(-1) = -1 \n G = S + 0 \n  \n G(1)
def p338_0 : List OwnerLevel := { parameters := [], properties := ["G", "S"] } :: prelude
def p338_1 : List OwnerLevel := { parameters := [], properties := [] } :: p338_0
def p338_2 : List OwnerLevel := { parameters := [], properties := [] } :: p338_0
def p338_3 : List OwnerLevel := { parameters := [], properties := [] } :: p338_0
#guard selectOwnedDeclaration p338_1 "S" == .property 1
#guard elaboratesToParameter p338_1 "S" == false
#guard selectOwnedDeclaration p338_0 "G" == .property 0
#guard elaboratesToParameter p338_0 "G" == false
#guard familyLiftingSignature? [clause (.litInt 1), clause (.litInt (-1))] == none -- family S

-- spec/root-row-block-head-is-elaborated: Inc(x) = x + 1 \n { \n     public K = if(true, 5, Inc) \n     0 \n }.K
def p339_0 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: prelude
def p339_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p339_0
def p339_2 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p339_0
def p339_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p339_2
#guard selectOwnedDeclaration p339_1 "x" == .parameter 0
#guard elaboratesToParameter p339_1 "x" == true
#guard selectOwnedDeclaration p339_3 "if" == .property 3
#guard elaboratesToParameter p339_3 "if" == false
#guard selectOwnedDeclaration p339_3 "Inc" == .property 2
#guard elaboratesToParameter p339_3 "Inc" == false
#guard selectOwnedDeclaration p339_0 "K" == .none
#guard elaboratesToParameter p339_0 "K" == false

-- spec/root-row-block-head-reports-front-end-errors: C1(a, *p) = a \n C2(b, *q) = b \n { \n     public K = C1 + C2 \n     0 \n }.K
def p340_0 : List OwnerLevel := { parameters := [], properties := ["C1", "C2"] } :: prelude
def p340_1 : List OwnerLevel := { parameters := ["a", "p"], properties := [] } :: p340_0
def p340_2 : List OwnerLevel := { parameters := ["b", "q"], properties := [] } :: p340_0
def p340_3 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p340_0
def p340_4 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["a", "p", "b", "q"] } :: p340_3
#guard selectOwnedDeclaration p340_1 "a" == .parameter 0
#guard elaboratesToParameter p340_1 "a" == true
#guard selectOwnedDeclaration p340_2 "b" == .parameter 0
#guard elaboratesToParameter p340_2 "b" == true
#guard selectOwnedDeclaration p340_4 "C1" == .property 2
#guard elaboratesToParameter p340_4 "C1" == false
#guard selectOwnedDeclaration p340_4 "C2" == .property 2
#guard elaboratesToParameter p340_4 "C2" == false
#guard selectOwnedDeclaration p340_0 "K" == .none
#guard elaboratesToParameter p340_0 "K" == false

-- spec/repeated-name-wrapper-keeps-independent-arguments: Common(x, x) = x \n Both(a, b) = Common(a, b) \n Twice(v) = Common(v, v) \n Some = Common \n  \n Both(7, 7) \n Twice(8) \n Some(9, 9)
def p341_0 : List OwnerLevel := { parameters := [], properties := ["Some", "Common", "Both", "Twice"] } :: prelude
def p341_1 : List OwnerLevel := { parameters := [], properties := [] } :: p341_0
def p341_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p341_0
def p341_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p341_0
def p341_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p341_0
#guard selectOwnedDeclaration p341_1 "Common" == .property 1
#guard elaboratesToParameter p341_1 "Common" == false
#guard selectOwnedDeclaration p341_2 "x" == .parameter 0
#guard elaboratesToParameter p341_2 "x" == true
#guard selectOwnedDeclaration p341_3 "Common" == .property 1
#guard elaboratesToParameter p341_3 "Common" == false
#guard selectOwnedDeclaration p341_3 "a" == .parameter 0
#guard elaboratesToParameter p341_3 "a" == true
#guard selectOwnedDeclaration p341_3 "b" == .parameter 0
#guard elaboratesToParameter p341_3 "b" == true
#guard selectOwnedDeclaration p341_4 "Common" == .property 1
#guard elaboratesToParameter p341_4 "Common" == false
#guard selectOwnedDeclaration p341_4 "v" == .parameter 0 -- x2
#guard elaboratesToParameter p341_4 "v" == true -- x2
#guard selectOwnedDeclaration p341_0 "Both" == .property 0
#guard elaboratesToParameter p341_0 "Both" == false
#guard selectOwnedDeclaration p341_0 "Twice" == .property 0
#guard elaboratesToParameter p341_0 "Twice" == false
#guard selectOwnedDeclaration p341_0 "Some" == .property 0
#guard elaboratesToParameter p341_0 "Some" == false

-- spec/implicit-forwarding-preserves-structural-kind: Single([x]) = x \n A = Single \n Add((x, y)) = x + y \n B = Add \n C((*xs)) = xs.count \n Count = C \n G([x]) = Single \n  \n A([7]) \n A([[7]]) \n B((10, 20)) \n Count((1, 2, 3)) \n G([7])
def p342_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "Count", "Single", "Add", "C", "G"] } :: prelude
def p342_1 : List OwnerLevel := { parameters := [], properties := [] } :: p342_0
def p342_2 : List OwnerLevel := { parameters := [], properties := [] } :: p342_0
def p342_3 : List OwnerLevel := { parameters := [], properties := [] } :: p342_0
def p342_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p342_0
def p342_5 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p342_0
def p342_6 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p342_0
def p342_7 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p342_0
#guard selectOwnedDeclaration p342_1 "Single" == .property 1
#guard elaboratesToParameter p342_1 "Single" == false
#guard selectOwnedDeclaration p342_2 "Add" == .property 1
#guard elaboratesToParameter p342_2 "Add" == false
#guard selectOwnedDeclaration p342_3 "C" == .property 1
#guard elaboratesToParameter p342_3 "C" == false
#guard selectOwnedDeclaration p342_4 "x" == .parameter 0
#guard elaboratesToParameter p342_4 "x" == true
#guard selectOwnedDeclaration p342_5 "x" == .parameter 0
#guard elaboratesToParameter p342_5 "x" == true
#guard selectOwnedDeclaration p342_5 "y" == .parameter 0
#guard elaboratesToParameter p342_5 "y" == true
#guard selectOwnedDeclaration p342_6 "xs" == .parameter 0
#guard elaboratesToParameter p342_6 "xs" == true
#guard selectOwnedDeclaration p342_6 "count" == .property 2
#guard elaboratesToParameter p342_6 "count" == false
#guard selectOwnedDeclaration p342_7 "Single" == .property 1
#guard elaboratesToParameter p342_7 "Single" == false
#guard selectOwnedDeclaration p342_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p342_0 "A" == false -- x2
#guard selectOwnedDeclaration p342_0 "B" == .property 0
#guard elaboratesToParameter p342_0 "B" == false
#guard selectOwnedDeclaration p342_0 "Count" == .property 0
#guard elaboratesToParameter p342_0 "Count" == false
#guard selectOwnedDeclaration p342_0 "G" == .property 0
#guard elaboratesToParameter p342_0 "G" == false

-- spec/alias-forwarding-and-explicit-call: Double(x) = x * 2 \n Other(y) = y * 2 \n  \n Alias = Double \n Forward(x) = Double \n Explicit(x) = Other(x) \n Formula = Double + 1 \n  \n Alias(5) \n Forward(5) \n Explicit(5) \n Formula(5)
def p343_0 : List OwnerLevel := { parameters := [], properties := ["Alias", "Formula", "Double", "Other", "Forward", "Explicit"] } :: prelude
def p343_1 : List OwnerLevel := { parameters := [], properties := [] } :: p343_0
def p343_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p343_0
def p343_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p343_0
def p343_4 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p343_0
def p343_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p343_0
def p343_6 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p343_0
#guard selectOwnedDeclaration p343_1 "Double" == .property 1
#guard elaboratesToParameter p343_1 "Double" == false
#guard selectOwnedDeclaration p343_2 "Double" == .property 1
#guard elaboratesToParameter p343_2 "Double" == false
#guard selectOwnedDeclaration p343_3 "x" == .parameter 0
#guard elaboratesToParameter p343_3 "x" == true
#guard selectOwnedDeclaration p343_4 "y" == .parameter 0
#guard elaboratesToParameter p343_4 "y" == true
#guard selectOwnedDeclaration p343_5 "Double" == .property 1
#guard elaboratesToParameter p343_5 "Double" == false
#guard selectOwnedDeclaration p343_6 "Other" == .property 1
#guard elaboratesToParameter p343_6 "Other" == false
#guard selectOwnedDeclaration p343_6 "x" == .parameter 0
#guard elaboratesToParameter p343_6 "x" == true
#guard selectOwnedDeclaration p343_0 "Alias" == .property 0
#guard elaboratesToParameter p343_0 "Alias" == false
#guard selectOwnedDeclaration p343_0 "Forward" == .property 0
#guard elaboratesToParameter p343_0 "Forward" == false
#guard selectOwnedDeclaration p343_0 "Explicit" == .property 0
#guard elaboratesToParameter p343_0 "Explicit" == false
#guard selectOwnedDeclaration p343_0 "Formula" == .property 0
#guard elaboratesToParameter p343_0 "Formula" == false

-- spec/bare-forwarding-never-renames-a-parameter: Other(y) = y * 2 \n Bad(x) = Other \n  \n Bad(5)
def p344_0 : List OwnerLevel := { parameters := [], properties := ["Other", "Bad"] } :: prelude
def p344_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p344_0
def p344_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p344_0
#guard selectOwnedDeclaration p344_1 "y" == .parameter 0
#guard elaboratesToParameter p344_1 "y" == true
#guard selectOwnedDeclaration p344_2 "Other" == .property 1
#guard elaboratesToParameter p344_2 "Other" == false
#guard selectOwnedDeclaration p344_0 "Bad" == .property 0
#guard elaboratesToParameter p344_0 "Bad" == false

-- spec/bare-forwarding-never-adds-a-parameter: F(p, q) = p + q \n A(p) = F \n  \n A(1)
def p345_0 : List OwnerLevel := { parameters := [], properties := ["F", "A"] } :: prelude
def p345_1 : List OwnerLevel := { parameters := ["p", "q"], properties := [] } :: p345_0
def p345_2 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p345_0
#guard selectOwnedDeclaration p345_1 "p" == .parameter 0
#guard elaboratesToParameter p345_1 "p" == true
#guard selectOwnedDeclaration p345_1 "q" == .parameter 0
#guard elaboratesToParameter p345_1 "q" == true
#guard selectOwnedDeclaration p345_2 "F" == .property 1
#guard elaboratesToParameter p345_2 "F" == false
#guard selectOwnedDeclaration p345_0 "A" == .property 0
#guard elaboratesToParameter p345_0 "A" == false

-- spec/alias-structural-forwarding-and-written-call: Single([x]) = x \n  \n Alias = Single \n SameShape([x]) = Single \n Explicit(x) = Single(x) \n Construct = Single([x]) \n  \n Alias([7]) \n SameShape([7]) \n Explicit([7]) \n Construct(7)
def p346_0 : List OwnerLevel := { parameters := [], properties := ["Alias", "Construct", "Single", "SameShape", "Explicit"] } :: prelude
def p346_1 : List OwnerLevel := { parameters := [], properties := [] } :: p346_0
def p346_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p346_0
def p346_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p346_0
def p346_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p346_0
def p346_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p346_0
#guard selectOwnedDeclaration p346_1 "Single" == .property 1
#guard elaboratesToParameter p346_1 "Single" == false
#guard selectOwnedDeclaration p346_2 "Single" == .property 1
#guard elaboratesToParameter p346_2 "Single" == false
#guard selectOwnedDeclaration p346_2 "x" == .parameter 0
#guard elaboratesToParameter p346_2 "x" == true
#guard selectOwnedDeclaration p346_3 "x" == .parameter 0
#guard elaboratesToParameter p346_3 "x" == true
#guard selectOwnedDeclaration p346_4 "Single" == .property 1
#guard elaboratesToParameter p346_4 "Single" == false
#guard selectOwnedDeclaration p346_5 "Single" == .property 1
#guard elaboratesToParameter p346_5 "Single" == false
#guard selectOwnedDeclaration p346_5 "x" == .parameter 0
#guard elaboratesToParameter p346_5 "x" == true
#guard selectOwnedDeclaration p346_0 "Alias" == .property 0
#guard elaboratesToParameter p346_0 "Alias" == false
#guard selectOwnedDeclaration p346_0 "SameShape" == .property 0
#guard elaboratesToParameter p346_0 "SameShape" == false
#guard selectOwnedDeclaration p346_0 "Explicit" == .property 0
#guard elaboratesToParameter p346_0 "Explicit" == false
#guard selectOwnedDeclaration p346_0 "Construct" == .property 0
#guard elaboratesToParameter p346_0 "Construct" == false

-- spec/bare-forwarding-never-reshapes-a-structural-parameter: Single([x]) = x \n Bad(x) = Single \n  \n Bad([7])
def p347_0 : List OwnerLevel := { parameters := [], properties := ["Single", "Bad"] } :: prelude
def p347_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p347_0
def p347_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p347_0
#guard selectOwnedDeclaration p347_1 "x" == .parameter 0
#guard elaboratesToParameter p347_1 "x" == true
#guard selectOwnedDeclaration p347_2 "Single" == .property 1
#guard elaboratesToParameter p347_2 "Single" == false
#guard selectOwnedDeclaration p347_0 "Bad" == .property 0
#guard elaboratesToParameter p347_0 "Bad" == false

-- spec/bare-forwarding-never-manufactures-a-sequence: Add((x, y)) = x + y \n G(x, y) = Add \n  \n G(2, 3)
def p348_0 : List OwnerLevel := { parameters := [], properties := ["Add", "G"] } :: prelude
def p348_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p348_0
def p348_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p348_0
#guard selectOwnedDeclaration p348_1 "x" == .parameter 0
#guard elaboratesToParameter p348_1 "x" == true
#guard selectOwnedDeclaration p348_1 "y" == .parameter 0
#guard elaboratesToParameter p348_1 "y" == true
#guard selectOwnedDeclaration p348_2 "Add" == .property 1
#guard elaboratesToParameter p348_2 "Add" == false
#guard selectOwnedDeclaration p348_0 "G" == .property 0
#guard elaboratesToParameter p348_0 "G" == false

-- spec/alias-preserves-the-callee-signature: Single([x]) = x \n P(x, x) = x \n E((), []) = 1 \n A = Single \n B = A \n C = B \n AP = P \n AE = E \n  \n C([7]) \n C([[7]]) \n AP(5, 5) \n AE((), [])
def p349_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C", "AP", "AE", "Single", "P", "E"] } :: prelude
def p349_1 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
def p349_2 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
def p349_3 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
def p349_4 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
def p349_5 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
def p349_6 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p349_0
def p349_7 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p349_0
def p349_8 : List OwnerLevel := { parameters := [], properties := [] } :: p349_0
#guard selectOwnedDeclaration p349_1 "Single" == .property 1
#guard elaboratesToParameter p349_1 "Single" == false
#guard selectOwnedDeclaration p349_2 "A" == .property 1
#guard elaboratesToParameter p349_2 "A" == false
#guard selectOwnedDeclaration p349_3 "B" == .property 1
#guard elaboratesToParameter p349_3 "B" == false
#guard selectOwnedDeclaration p349_4 "P" == .property 1
#guard elaboratesToParameter p349_4 "P" == false
#guard selectOwnedDeclaration p349_5 "E" == .property 1
#guard elaboratesToParameter p349_5 "E" == false
#guard selectOwnedDeclaration p349_6 "x" == .parameter 0
#guard elaboratesToParameter p349_6 "x" == true
#guard selectOwnedDeclaration p349_7 "x" == .parameter 0
#guard elaboratesToParameter p349_7 "x" == true
#guard selectOwnedDeclaration p349_0 "C" == .property 0 -- x2
#guard elaboratesToParameter p349_0 "C" == false -- x2
#guard selectOwnedDeclaration p349_0 "AP" == .property 0
#guard elaboratesToParameter p349_0 "AP" == false
#guard selectOwnedDeclaration p349_0 "AE" == .property 0
#guard elaboratesToParameter p349_0 "AE" == false

-- spec/inline-alias-value-demand-is-the-target-contract: Inc(x) = x + 1 \n K(z) = count({ Inc }) \n K(1)
def p350_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "K"] } :: prelude
def p350_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p350_0
def p350_2 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p350_0
def p350_3 : List OwnerLevel := { parameters := [], properties := [] } :: p350_2
#guard selectOwnedDeclaration p350_1 "x" == .parameter 0
#guard elaboratesToParameter p350_1 "x" == true
#guard selectOwnedDeclaration p350_2 "count" == .property 2
#guard elaboratesToParameter p350_2 "count" == false
#guard selectOwnedDeclaration p350_3 "Inc" == .property 2
#guard elaboratesToParameter p350_3 "Inc" == false
#guard selectOwnedDeclaration p350_0 "K" == .property 0
#guard elaboratesToParameter p350_0 "K" == false

-- spec/inline-formula-block-keeps-unresolved-implicit-params: Inc(x) = x + 1 \n K(z) = count({ Inc + 0 }) \n K(1)
def p351_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "K"] } :: prelude
def p351_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p351_0
def p351_2 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p351_0
def p351_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p351_2
#guard selectOwnedDeclaration p351_1 "x" == .parameter 0
#guard elaboratesToParameter p351_1 "x" == true
#guard selectOwnedDeclaration p351_2 "count" == .property 2
#guard elaboratesToParameter p351_2 "count" == false
#guard selectOwnedDeclaration p351_3 "Inc" == .property 2
#guard elaboratesToParameter p351_3 "Inc" == false
#guard selectOwnedDeclaration p351_0 "K" == .property 0
#guard elaboratesToParameter p351_0 "K" == false

-- spec/alias-of-a-builtin-is-the-builtin: C = count \n I = if \n M = map \n Bad(x) = x / 0 \n  \n C([1, 2, 3]) \n I(true, 1, 1 / 0) \n M([], Bad)
def p352_0 : List OwnerLevel := { parameters := [], properties := ["C", "I", "M", "Bad"] } :: prelude
def p352_1 : List OwnerLevel := { parameters := [], properties := [] } :: p352_0
def p352_2 : List OwnerLevel := { parameters := [], properties := [] } :: p352_0
def p352_3 : List OwnerLevel := { parameters := [], properties := [] } :: p352_0
def p352_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p352_0
#guard selectOwnedDeclaration p352_1 "count" == .property 2
#guard elaboratesToParameter p352_1 "count" == false
#guard selectOwnedDeclaration p352_2 "if" == .property 2
#guard elaboratesToParameter p352_2 "if" == false
#guard selectOwnedDeclaration p352_3 "map" == .property 2
#guard elaboratesToParameter p352_3 "map" == false
#guard selectOwnedDeclaration p352_4 "x" == .parameter 0
#guard elaboratesToParameter p352_4 "x" == true
#guard selectOwnedDeclaration p352_0 "C" == .property 0
#guard elaboratesToParameter p352_0 "C" == false
#guard selectOwnedDeclaration p352_0 "I" == .property 0
#guard elaboratesToParameter p352_0 "I" == false
#guard selectOwnedDeclaration p352_0 "M" == .property 0
#guard elaboratesToParameter p352_0 "M" == false
#guard selectOwnedDeclaration p352_0 "Bad" == .property 0
#guard elaboratesToParameter p352_0 "Bad" == false

-- spec/bare-forwarding-needs-parameter-names: S(1) = 1 \n S(-1) = -1 \n SA = S \n W(x) = SA \n  \n W(1)
def p353_0 : List OwnerLevel := { parameters := [], properties := ["SA", "S", "W"] } :: prelude
def p353_1 : List OwnerLevel := { parameters := [], properties := [] } :: p353_0
def p353_2 : List OwnerLevel := { parameters := [], properties := [] } :: p353_0
def p353_3 : List OwnerLevel := { parameters := [], properties := [] } :: p353_0
def p353_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p353_0
#guard selectOwnedDeclaration p353_1 "S" == .property 1
#guard elaboratesToParameter p353_1 "S" == false
#guard selectOwnedDeclaration p353_4 "SA" == .property 1
#guard elaboratesToParameter p353_4 "SA" == false
#guard selectOwnedDeclaration p353_0 "W" == .property 0
#guard elaboratesToParameter p353_0 "W" == false
#guard familyLiftingSignature? [clause (.litInt 1), clause (.litInt (-1))] == none -- family S

-- spec/reference-members-are-the-targets-carrier-members-its-own: Lib(x) = { \n   K = 5 \n   x \n } \n A = Lib \n Navigate(f) = f.K \n  \n Lib.K \n A.K \n Navigate(A)
def p354_0 : List OwnerLevel := { parameters := [], properties := ["A", "Lib", "Navigate"] } :: prelude
def p354_1 : List OwnerLevel := { parameters := [], properties := [] } :: p354_0
def p354_2 : List OwnerLevel := { parameters := ["x"], properties := ["K"] } :: p354_0
def p354_3 : List OwnerLevel := { parameters := [], properties := [] } :: p354_2
def p354_4 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p354_0
#guard selectOwnedDeclaration p354_1 "Lib" == .property 1
#guard elaboratesToParameter p354_1 "Lib" == false
#guard selectOwnedDeclaration p354_2 "x" == .parameter 0
#guard elaboratesToParameter p354_2 "x" == true
#guard selectOwnedDeclaration p354_4 "f" == .parameter 0
#guard elaboratesToParameter p354_4 "f" == true
#guard selectOwnedDeclaration p354_4 "K" == .none
#guard elaboratesToParameter p354_4 "K" == false
#guard selectOwnedDeclaration p354_0 "Lib" == .property 0
#guard elaboratesToParameter p354_0 "Lib" == false
#guard selectOwnedDeclaration p354_0 "K" == .none -- x2
#guard elaboratesToParameter p354_0 "K" == false -- x2
#guard selectOwnedDeclaration p354_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p354_0 "A" == false -- x2
#guard selectOwnedDeclaration p354_0 "Navigate" == .property 0
#guard elaboratesToParameter p354_0 "Navigate" == false

-- spec/open-of-a-callable-alias-is-refused: Lib(x) = x \n A = Lib \n B = { \n   open A \n   1 \n } \n  \n B
def p355_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "Lib"] } :: prelude
def p355_1 : List OwnerLevel := { parameters := [], properties := [] } :: p355_0
def p355_2 : List OwnerLevel := { parameters := [], properties := [] } :: p355_0
def p355_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p355_0
#guard selectOwnedDeclaration p355_1 "Lib" == .property 1
#guard elaboratesToParameter p355_1 "Lib" == false
#guard selectOwnedDeclaration p355_2 "A" == .property 1
#guard openHead? (elaborateOpenHead p355_2 "A") == some (false, "A")
#guard selectOwnedDeclaration p355_3 "x" == .parameter 0
#guard elaboratesToParameter p355_3 "x" == true
#guard selectOwnedDeclaration p355_0 "B" == .property 0
#guard elaboratesToParameter p355_0 "B" == false

-- spec/reference-and-carrier-transport-the-whole-definition: Box = { \n     public Q = 99 \n     F(x) = x * x \n     F \n } \n A = Box \n B = { Box } \n GetQ(f) = f.Q \n  \n A.Q \n GetQ(A) \n A(3) \n B(3)
def p356_0 : List OwnerLevel := { parameters := [], properties := ["Box", "A", "B", "GetQ"] } :: prelude
def p356_1 : List OwnerLevel := { parameters := [], properties := ["Q", "F"] } :: p356_0
def p356_2 : List OwnerLevel := { parameters := [], properties := [] } :: p356_1
def p356_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p356_1
def p356_4 : List OwnerLevel := { parameters := [], properties := [] } :: p356_0
def p356_5 : List OwnerLevel := { parameters := [], properties := [] } :: p356_0
def p356_6 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p356_0
#guard selectOwnedDeclaration p356_3 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p356_3 "x" == true -- x2
#guard selectOwnedDeclaration p356_1 "F" == .property 0
#guard elaboratesToParameter p356_1 "F" == false
#guard selectOwnedDeclaration p356_4 "Box" == .property 1
#guard elaboratesToParameter p356_4 "Box" == false
#guard selectOwnedDeclaration p356_5 "Box" == .property 1
#guard elaboratesToParameter p356_5 "Box" == false
#guard selectOwnedDeclaration p356_6 "f" == .parameter 0
#guard elaboratesToParameter p356_6 "f" == true
#guard selectOwnedDeclaration p356_6 "Q" == .none
#guard elaboratesToParameter p356_6 "Q" == false
#guard selectOwnedDeclaration p356_0 "A" == .property 0 -- x3
#guard elaboratesToParameter p356_0 "A" == false -- x3
#guard selectOwnedDeclaration p356_0 "Q" == .none
#guard elaboratesToParameter p356_0 "Q" == false
#guard selectOwnedDeclaration p356_0 "GetQ" == .property 0
#guard elaboratesToParameter p356_0 "GetQ" == false
#guard selectOwnedDeclaration p356_0 "B" == .property 0
#guard elaboratesToParameter p356_0 "B" == false

-- spec/repeated-name-matches-definitions-by-identity: A = 7 \n D = 7 \n Same(x, x) = true \n Same(x, y) = false \n  \n Same(A, A) \n Same(A, D) \n Same(A, 7)
def p357_0 : List OwnerLevel := { parameters := [], properties := ["A", "D", "Same"] } :: prelude
def p357_1 : List OwnerLevel := { parameters := [], properties := [] } :: p357_0
def p357_2 : List OwnerLevel := { parameters := [], properties := [] } :: p357_0
def p357_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p357_0
def p357_4 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p357_0
#guard selectOwnedDeclaration p357_0 "Same" == .property 0 -- x3
#guard elaboratesToParameter p357_0 "Same" == false -- x3
#guard selectOwnedDeclaration p357_0 "A" == .property 0 -- x4
#guard elaboratesToParameter p357_0 "A" == false -- x4
#guard selectOwnedDeclaration p357_0 "D" == .property 0
#guard elaboratesToParameter p357_0 "D" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "x", .bind "x"]), clause (.sequenceValue [.bind "x", .bind "y"])] == none -- family Same

-- spec/open-through-a-reference-opens-the-target: Lib = { \n     public K = 7 \n     0 \n } \n Alias = Lib \n P = { \n     open Alias, Lib \n     K \n } \n  \n P
def p358_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Alias", "P"] } :: prelude
def p358_1 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p358_0
def p358_2 : List OwnerLevel := { parameters := [], properties := [] } :: p358_1
def p358_3 : List OwnerLevel := { parameters := [], properties := [] } :: p358_0
def p358_4 : List OwnerLevel := { parameters := [], properties := [] } :: p358_0
#guard selectOwnedDeclaration p358_3 "Lib" == .property 1
#guard elaboratesToParameter p358_3 "Lib" == false
#guard selectOwnedDeclaration p358_4 "Alias" == .property 1
#guard openHead? (elaborateOpenHead p358_4 "Alias") == some (false, "Alias")
#guard selectOwnedDeclaration p358_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p358_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p358_4 "K" == .none
#guard elaboratesToParameter p358_4 "K" == false
#guard selectOwnedDeclaration p358_0 "P" == .property 0
#guard elaboratesToParameter p358_0 "P" == false

-- spec/member-path-alias-is-a-member-reference: Box = { G(x) = x * 10 } \n Use(b) = { \n     A = b.G \n     A(3), 3.A \n } \n  \n Use(Box)
def p359_0 : List OwnerLevel := { parameters := [], properties := ["Box", "Use"] } :: prelude
def p359_1 : List OwnerLevel := { parameters := [], properties := ["G"] } :: p359_0
def p359_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p359_1
def p359_3 : List OwnerLevel := { parameters := ["b"], properties := ["A"] } :: p359_0
def p359_4 : List OwnerLevel := { parameters := [], properties := [] } :: p359_3
#guard selectOwnedDeclaration p359_2 "x" == .parameter 0
#guard elaboratesToParameter p359_2 "x" == true
#guard selectOwnedDeclaration p359_4 "b" == .parameter 1
#guard elaboratesToParameter p359_4 "b" == true
#guard selectOwnedDeclaration p359_4 "G" == .none
#guard elaboratesToParameter p359_4 "G" == false
#guard selectOwnedDeclaration p359_3 "A" == .property 0 -- x2
#guard elaboratesToParameter p359_3 "A" == false -- x2
#guard selectOwnedDeclaration p359_0 "Use" == .property 0
#guard elaboratesToParameter p359_0 "Use" == false
#guard selectOwnedDeclaration p359_0 "Box" == .property 0
#guard elaboratesToParameter p359_0 "Box" == false

-- spec/bare-forwarding-keeps-each-parameter-kind: Add((a, b)) = a + b \n Coll(*vs) = vs \n Mid([first, *middle, last]) = [first, middle, last] \n Pair((a, b)) = Add \n Many(*vs) = Coll \n Same([first, *middle, last]) = Mid \n  \n Pair((2, 3)) \n Many(1, 2) \n Same([1, 2, 3, 4])
def p360_0 : List OwnerLevel := { parameters := [], properties := ["Add", "Coll", "Mid", "Pair", "Many", "Same"] } :: prelude
def p360_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p360_0
def p360_2 : List OwnerLevel := { parameters := ["vs"], properties := [] } :: p360_0
def p360_3 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p360_0
def p360_4 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p360_0
def p360_5 : List OwnerLevel := { parameters := ["vs"], properties := [] } :: p360_0
def p360_6 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p360_0
#guard selectOwnedDeclaration p360_1 "a" == .parameter 0
#guard elaboratesToParameter p360_1 "a" == true
#guard selectOwnedDeclaration p360_1 "b" == .parameter 0
#guard elaboratesToParameter p360_1 "b" == true
#guard selectOwnedDeclaration p360_2 "vs" == .parameter 0
#guard elaboratesToParameter p360_2 "vs" == true
#guard selectOwnedDeclaration p360_3 "first" == .parameter 0
#guard elaboratesToParameter p360_3 "first" == true
#guard selectOwnedDeclaration p360_3 "middle" == .parameter 0
#guard elaboratesToParameter p360_3 "middle" == true
#guard selectOwnedDeclaration p360_3 "last" == .parameter 0
#guard elaboratesToParameter p360_3 "last" == true
#guard selectOwnedDeclaration p360_4 "Add" == .property 1
#guard elaboratesToParameter p360_4 "Add" == false
#guard selectOwnedDeclaration p360_5 "Coll" == .property 1
#guard elaboratesToParameter p360_5 "Coll" == false
#guard selectOwnedDeclaration p360_6 "Mid" == .property 1
#guard elaboratesToParameter p360_6 "Mid" == false
#guard selectOwnedDeclaration p360_0 "Pair" == .property 0
#guard elaboratesToParameter p360_0 "Pair" == false
#guard selectOwnedDeclaration p360_0 "Many" == .property 0
#guard elaboratesToParameter p360_0 "Many" == false
#guard selectOwnedDeclaration p360_0 "Same" == .property 0
#guard elaboratesToParameter p360_0 "Same" == false

-- spec/written-call-infers-its-written-names: Add((a, b)) = a + b \n Single([a]) = a \n G = Add((x, y)) \n Construct = Single([x]) \n  \n G(2, 3) \n Construct(7)
def p361_0 : List OwnerLevel := { parameters := [], properties := ["G", "Construct", "Add", "Single"] } :: prelude
def p361_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p361_0
def p361_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p361_0
def p361_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p361_0
def p361_4 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p361_0
#guard selectOwnedDeclaration p361_1 "Add" == .property 1
#guard elaboratesToParameter p361_1 "Add" == false
#guard selectOwnedDeclaration p361_1 "x" == .parameter 0
#guard elaboratesToParameter p361_1 "x" == true
#guard selectOwnedDeclaration p361_1 "y" == .parameter 0
#guard elaboratesToParameter p361_1 "y" == true
#guard selectOwnedDeclaration p361_2 "Single" == .property 1
#guard elaboratesToParameter p361_2 "Single" == false
#guard selectOwnedDeclaration p361_2 "x" == .parameter 0
#guard elaboratesToParameter p361_2 "x" == true
#guard selectOwnedDeclaration p361_3 "a" == .parameter 0
#guard elaboratesToParameter p361_3 "a" == true
#guard selectOwnedDeclaration p361_3 "b" == .parameter 0
#guard elaboratesToParameter p361_3 "b" == true
#guard selectOwnedDeclaration p361_4 "a" == .parameter 0
#guard elaboratesToParameter p361_4 "a" == true
#guard selectOwnedDeclaration p361_0 "G" == .property 0
#guard elaboratesToParameter p361_0 "G" == false
#guard selectOwnedDeclaration p361_0 "Construct" == .property 0
#guard elaboratesToParameter p361_0 "Construct" == false

-- spec/repeated-callable-success-preserves-both-channels: B(*xs) = 5 + xs.count \n P(f, f, f, f, f) = [f, f(1), map([7], f)] \n P(B, 5, B, 5, 5) \n P(5, B, 5, 5, B)
def p362_0 : List OwnerLevel := { parameters := [], properties := ["B", "P"] } :: prelude
def p362_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p362_0
def p362_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p362_0
#guard selectOwnedDeclaration p362_1 "xs" == .parameter 0
#guard elaboratesToParameter p362_1 "xs" == true
#guard selectOwnedDeclaration p362_1 "count" == .property 2
#guard elaboratesToParameter p362_1 "count" == false
#guard selectOwnedDeclaration p362_2 "f" == .parameter 0 -- x3
#guard elaboratesToParameter p362_2 "f" == true -- x3
#guard selectOwnedDeclaration p362_2 "map" == .property 2
#guard elaboratesToParameter p362_2 "map" == false
#guard selectOwnedDeclaration p362_0 "P" == .property 0 -- x2
#guard elaboratesToParameter p362_0 "P" == false -- x2
#guard selectOwnedDeclaration p362_0 "B" == .property 0 -- x4
#guard elaboratesToParameter p362_0 "B" == false -- x4

-- spec/repeated-genuine-aliases-preserve-complete-binding: A(*xs) = 5 + xs.count \n P(f, f) = [f, f.count, f(1), map([7], f)] \n Both(left, right) = [P(left, right), P(right, left)] \n Share(original) = Both(original, original) \n Share(A)
def p363_0 : List OwnerLevel := { parameters := [], properties := ["A", "P", "Both", "Share"] } :: prelude
def p363_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p363_0
def p363_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p363_0
def p363_3 : List OwnerLevel := { parameters := ["left", "right"], properties := [] } :: p363_0
def p363_4 : List OwnerLevel := { parameters := ["original"], properties := [] } :: p363_0
#guard selectOwnedDeclaration p363_1 "xs" == .parameter 0
#guard elaboratesToParameter p363_1 "xs" == true
#guard selectOwnedDeclaration p363_1 "count" == .property 2
#guard elaboratesToParameter p363_1 "count" == false
#guard selectOwnedDeclaration p363_2 "f" == .parameter 0 -- x4
#guard elaboratesToParameter p363_2 "f" == true -- x4
#guard selectOwnedDeclaration p363_2 "count" == .property 2
#guard elaboratesToParameter p363_2 "count" == false
#guard selectOwnedDeclaration p363_2 "map" == .property 2
#guard elaboratesToParameter p363_2 "map" == false
#guard selectOwnedDeclaration p363_3 "P" == .property 1 -- x2
#guard elaboratesToParameter p363_3 "P" == false -- x2
#guard selectOwnedDeclaration p363_3 "left" == .parameter 0 -- x2
#guard elaboratesToParameter p363_3 "left" == true -- x2
#guard selectOwnedDeclaration p363_3 "right" == .parameter 0 -- x2
#guard elaboratesToParameter p363_3 "right" == true -- x2
#guard selectOwnedDeclaration p363_4 "Both" == .property 1
#guard elaboratesToParameter p363_4 "Both" == false
#guard selectOwnedDeclaration p363_4 "original" == .parameter 0 -- x2
#guard elaboratesToParameter p363_4 "original" == true -- x2
#guard selectOwnedDeclaration p363_0 "Share" == .property 0
#guard elaboratesToParameter p363_0 "Share" == false
#guard selectOwnedDeclaration p363_0 "A" == .property 0
#guard elaboratesToParameter p363_0 "A" == false

-- spec/repeated-callable-identity-includes-captured-activation: P(f, f) = f(1) \n Outer(n, previous) = { \n   Inner(*xs) = 5 + n * xs.count \n   if(n == 1, Outer(2, Inner), P(previous, Inner)) \n } \n Outer(1, 0)
def p364_0 : List OwnerLevel := { parameters := [], properties := ["P", "Outer"] } :: prelude
def p364_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p364_0
def p364_2 : List OwnerLevel := { parameters := ["n", "previous"], properties := ["Inner"] } :: p364_0
def p364_3 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p364_2
#guard selectOwnedDeclaration p364_1 "f" == .parameter 0
#guard elaboratesToParameter p364_1 "f" == true
#guard selectOwnedDeclaration p364_3 "n" == .parameter 1
#guard elaboratesToParameter p364_3 "n" == true
#guard selectOwnedDeclaration p364_3 "xs" == .parameter 0
#guard elaboratesToParameter p364_3 "xs" == true
#guard selectOwnedDeclaration p364_3 "count" == .property 3
#guard elaboratesToParameter p364_3 "count" == false
#guard selectOwnedDeclaration p364_2 "if" == .property 2
#guard elaboratesToParameter p364_2 "if" == false
#guard selectOwnedDeclaration p364_2 "n" == .parameter 0
#guard elaboratesToParameter p364_2 "n" == true
#guard selectOwnedDeclaration p364_2 "Outer" == .property 1
#guard elaboratesToParameter p364_2 "Outer" == false
#guard selectOwnedDeclaration p364_2 "Inner" == .property 0 -- x2
#guard elaboratesToParameter p364_2 "Inner" == false -- x2
#guard selectOwnedDeclaration p364_2 "P" == .property 1
#guard elaboratesToParameter p364_2 "P" == false
#guard selectOwnedDeclaration p364_2 "previous" == .parameter 0
#guard elaboratesToParameter p364_2 "previous" == true
#guard selectOwnedDeclaration p364_0 "Outer" == .property 0
#guard elaboratesToParameter p364_0 "Outer" == false

-- spec/repeated-dot-results-have-distinct-wrapper-identities: Obj = { public V = 5 } \n P(f, f) = f \n P(Obj.V, Obj.V)
def p365_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "P"] } :: prelude
def p365_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p365_0
def p365_2 : List OwnerLevel := { parameters := [], properties := [] } :: p365_1
def p365_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p365_0
#guard selectOwnedDeclaration p365_3 "f" == .parameter 0
#guard elaboratesToParameter p365_3 "f" == true
#guard selectOwnedDeclaration p365_0 "P" == .property 0
#guard elaboratesToParameter p365_0 "P" == false
#guard selectOwnedDeclaration p365_0 "Obj" == .property 0 -- x2
#guard elaboratesToParameter p365_0 "Obj" == false -- x2
#guard selectOwnedDeclaration p365_0 "V" == .none -- x2
#guard elaboratesToParameter p365_0 "V" == false -- x2

-- spec/repeated-forwarded-dot-wrapper-keeps-identity: Obj = { public V = 5 } \n P(f, f) = f() \n Pass(g) = P(g, g) \n Pass(Obj.V)
def p366_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "P", "Pass"] } :: prelude
def p366_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p366_0
def p366_2 : List OwnerLevel := { parameters := [], properties := [] } :: p366_1
def p366_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p366_0
def p366_4 : List OwnerLevel := { parameters := ["g"], properties := [] } :: p366_0
#guard selectOwnedDeclaration p366_3 "f" == .parameter 0
#guard elaboratesToParameter p366_3 "f" == true
#guard selectOwnedDeclaration p366_4 "P" == .property 1
#guard elaboratesToParameter p366_4 "P" == false
#guard selectOwnedDeclaration p366_4 "g" == .parameter 0 -- x2
#guard elaboratesToParameter p366_4 "g" == true -- x2
#guard selectOwnedDeclaration p366_0 "Pass" == .property 0
#guard elaboratesToParameter p366_0 "Pass" == false
#guard selectOwnedDeclaration p366_0 "Obj" == .property 0
#guard elaboratesToParameter p366_0 "Obj" == false
#guard selectOwnedDeclaration p366_0 "V" == .none
#guard elaboratesToParameter p366_0 "V" == false

-- spec/collecting-pattern-list-merges-after-the-collector: Bad = 1 / 0 \n P(x, *rest, x) = x \n  \n P(1, Bad, 2)
def p367_0 : List OwnerLevel := { parameters := [], properties := ["Bad", "P"] } :: prelude
def p367_1 : List OwnerLevel := { parameters := [], properties := [] } :: p367_0
def p367_2 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p367_0
#guard selectOwnedDeclaration p367_2 "x" == .parameter 0
#guard elaboratesToParameter p367_2 "x" == true
#guard selectOwnedDeclaration p367_0 "P" == .property 0
#guard elaboratesToParameter p367_0 "P" == false
#guard selectOwnedDeclaration p367_0 "Bad" == .property 0
#guard elaboratesToParameter p367_0 "Bad" == false

-- spec/redundant-call-parens-canonical: Inner = (1, 2, 3) \n CountSequenceValue((*values)) = values.count \n NestedCount([(*values)]) = values.count \n  \n CountSequenceValue(Inner) \n CountSequenceValue((Inner)) \n CountSequenceValue(((1, 2, 3))) \n NestedCount([(1, 2, 3)]) \n NestedCount(([(1, 2, 3)]))
def p368_0 : List OwnerLevel := { parameters := [], properties := ["Inner", "CountSequenceValue", "NestedCount"] } :: prelude
def p368_1 : List OwnerLevel := { parameters := [], properties := [] } :: p368_0
def p368_2 : List OwnerLevel := { parameters := ["values"], properties := [] } :: p368_0
def p368_3 : List OwnerLevel := { parameters := ["values"], properties := [] } :: p368_0
#guard selectOwnedDeclaration p368_2 "values" == .parameter 0
#guard elaboratesToParameter p368_2 "values" == true
#guard selectOwnedDeclaration p368_2 "count" == .property 2
#guard elaboratesToParameter p368_2 "count" == false
#guard selectOwnedDeclaration p368_3 "values" == .parameter 0
#guard elaboratesToParameter p368_3 "values" == true
#guard selectOwnedDeclaration p368_3 "count" == .property 2
#guard elaboratesToParameter p368_3 "count" == false
#guard selectOwnedDeclaration p368_0 "CountSequenceValue" == .property 0 -- x3
#guard elaboratesToParameter p368_0 "CountSequenceValue" == false -- x3
#guard selectOwnedDeclaration p368_0 "Inner" == .property 0 -- x2
#guard elaboratesToParameter p368_0 "Inner" == false -- x2
#guard selectOwnedDeclaration p368_0 "NestedCount" == .property 0 -- x2
#guard elaboratesToParameter p368_0 "NestedCount" == false -- x2

-- spec/call-spread-into-conditional-clauses: F(0, 0) = 100 \n F(x, y) = x + y \n A = (1, 2) \n F(A*)
-- the same levels and decisions, 1 more:
--   spec/call-spread-dispatches-before-clause-selection
def p369_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p369_1 : List OwnerLevel := { parameters := [], properties := [] } :: p369_0
def p369_2 : List OwnerLevel := { parameters := [], properties := [] } :: p369_0
def p369_3 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p369_0
#guard selectOwnedDeclaration p369_3 "x" == .parameter 0
#guard elaboratesToParameter p369_3 "x" == true
#guard selectOwnedDeclaration p369_3 "y" == .parameter 0
#guard elaboratesToParameter p369_3 "y" == true
#guard selectOwnedDeclaration p369_0 "F" == .property 0
#guard elaboratesToParameter p369_0 "F" == false
#guard selectOwnedDeclaration p369_0 "A" == .property 0
#guard elaboratesToParameter p369_0 "A" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.litInt 0, .litInt 0]), clause (.sequenceValue [.bind "x", .bind "y"])] == some [.capture { name := "x" }, .capture { name := "y" }] -- family F

-- spec/conditional-one-element-list-pattern: F([x]) = x \n F(n) = 0 \n  \n F([7]) \n F([1, 2])
def p370_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p370_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p370_0
def p370_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p370_0
#guard selectOwnedDeclaration p370_1 "x" == .parameter 0
#guard elaboratesToParameter p370_1 "x" == true
#guard selectOwnedDeclaration p370_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p370_0 "F" == false -- x2
#guard familyLiftingSignature? [clause (.sequenceValue [.listValue [.bind "x"]]), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/conditional-sequence-pattern-matches-sequence-values-only: F((x, y)) = x + y \n F(z) = 0 \n  \n F((2, 3)) \n F([2, 3])
def p371_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p371_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p371_0
def p371_2 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p371_0
#guard selectOwnedDeclaration p371_1 "x" == .parameter 0
#guard elaboratesToParameter p371_1 "x" == true
#guard selectOwnedDeclaration p371_1 "y" == .parameter 0
#guard elaboratesToParameter p371_1 "y" == true
#guard selectOwnedDeclaration p371_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p371_0 "F" == false -- x2
#guard familyLiftingSignature? [clause (.sequenceValue [.sequenceValue [.bind "x", .bind "y"]]), clause (.bind "z")] == some [.capture { name := "z" }] -- family F

-- spec/empty-structural-patterns-are-distinct-heads: Kind(()) = 'empty sequence' \n Kind([]) = 'empty list' \n Kind(x) = 'other' \n  \n Kind(()) \n Kind([]) \n Kind(0)
def p372_0 : List OwnerLevel := { parameters := [], properties := ["Kind"] } :: prelude
def p372_1 : List OwnerLevel := { parameters := [], properties := [] } :: p372_0
def p372_2 : List OwnerLevel := { parameters := [], properties := [] } :: p372_0
def p372_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p372_0
#guard selectOwnedDeclaration p372_0 "Kind" == .property 0 -- x3
#guard elaboratesToParameter p372_0 "Kind" == false -- x3
#guard familyLiftingSignature? [clause (.sequenceValue [.sequenceValue []]), clause (.sequenceValue [.listValue []]), clause (.bind "x")] == some [.capture { name := "x" }] -- family Kind

-- spec/conditional-clause-head-rejects-extra-arguments: F(0) = 1 \n F(n) = 2 \n F(1, 2)
def p373_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p373_1 : List OwnerLevel := { parameters := [], properties := [] } :: p373_0
def p373_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p373_0
#guard selectOwnedDeclaration p373_0 "F" == .property 0
#guard elaboratesToParameter p373_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/call-spread-into-patterned-callee: F(x, x) = x + 1 \n A = (7, 7) \n F(A*)
def p374_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p374_1 : List OwnerLevel := { parameters := [], properties := [] } :: p374_0
def p374_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p374_0
#guard selectOwnedDeclaration p374_2 "x" == .parameter 0
#guard elaboratesToParameter p374_2 "x" == true
#guard selectOwnedDeclaration p374_0 "F" == .property 0
#guard elaboratesToParameter p374_0 "F" == false
#guard selectOwnedDeclaration p374_0 "A" == .property 0
#guard elaboratesToParameter p374_0 "A" == false

-- spec/root-spread-then-value-slot: First = 1, 2 \n Second = 3, 4 \n  \n First*, Second
def p375_0 : List OwnerLevel := { parameters := [], properties := ["First", "Second"] } :: prelude
def p375_1 : List OwnerLevel := { parameters := [], properties := [] } :: p375_0
def p375_2 : List OwnerLevel := { parameters := [], properties := [] } :: p375_0
#guard selectOwnedDeclaration p375_0 "First" == .property 0
#guard elaboratesToParameter p375_0 "First" == false
#guard selectOwnedDeclaration p375_0 "Second" == .property 0
#guard elaboratesToParameter p375_0 "Second" == false

-- spec/spread-slots-capture: A = 1, 2 \n B = 1*, 2 \n  \n A.count \n B.count
def p376_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p376_1 : List OwnerLevel := { parameters := [], properties := [] } :: p376_0
def p376_2 : List OwnerLevel := { parameters := [], properties := [] } :: p376_0
#guard selectOwnedDeclaration p376_0 "A" == .property 0
#guard elaboratesToParameter p376_0 "A" == false
#guard selectOwnedDeclaration p376_0 "count" == .property 1 -- x2
#guard elaboratesToParameter p376_0 "count" == false -- x2
#guard selectOwnedDeclaration p376_0 "B" == .property 0
#guard elaboratesToParameter p376_0 "B" == false

-- spec/open-local-only-through-capture-row: Outer(p) = { \n     open Lib \n     Lib = { public G = { Q = p + 1 \n     (Q) } } \n     G \n } \n Outer(1)
def p377_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p377_1 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p377_0
def p377_2 : List OwnerLevel := { parameters := [], properties := ["G"] } :: p377_1
def p377_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p377_2
def p377_4 : List OwnerLevel := { parameters := [], properties := [] } :: p377_3
#guard selectOwnedDeclaration p377_1 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p377_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p377_4 "p" == .parameter 3
#guard elaboratesToParameter p377_4 "p" == true
#guard selectOwnedDeclaration p377_3 "Q" == .property 0
#guard elaboratesToParameter p377_3 "Q" == false
#guard selectOwnedDeclaration p377_1 "G" == .none
#guard elaboratesToParameter p377_1 "G" == false
#guard selectOwnedDeclaration p377_0 "Outer" == .property 0
#guard elaboratesToParameter p377_0 "Outer" == false

-- spec/open-self-contained-beside-same-named-sibling: Outer(p) = { \n     open Lib \n     Lib = { \n         public G = { Q = 7 \n         (Q) } \n         Q = p + 1 \n     } \n     G \n } \n Outer(1)
def p378_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p378_1 : List OwnerLevel := { parameters := ["p"], properties := ["Lib"] } :: p378_0
def p378_2 : List OwnerLevel := { parameters := [], properties := ["G", "Q"] } :: p378_1
def p378_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p378_2
def p378_4 : List OwnerLevel := { parameters := [], properties := [] } :: p378_3
def p378_5 : List OwnerLevel := { parameters := [], properties := [] } :: p378_2
#guard selectOwnedDeclaration p378_1 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p378_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p378_3 "Q" == .property 0
#guard elaboratesToParameter p378_3 "Q" == false
#guard selectOwnedDeclaration p378_5 "p" == .parameter 2
#guard elaboratesToParameter p378_5 "p" == true
#guard selectOwnedDeclaration p378_1 "G" == .none
#guard elaboratesToParameter p378_1 "G" == false
#guard selectOwnedDeclaration p378_0 "Outer" == .property 0
#guard elaboratesToParameter p378_0 "Outer" == false

-- spec/zero-param-block-higher-order: Call0 = f() \n Call0({42})
def p379_0 : List OwnerLevel := { parameters := [], properties := ["Call0"] } :: prelude
def p379_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p379_0
def p379_2 : List OwnerLevel := { parameters := [], properties := [] } :: p379_0
#guard selectOwnedDeclaration p379_1 "f" == .parameter 0
#guard elaboratesToParameter p379_1 "f" == true
#guard selectOwnedDeclaration p379_0 "Call0" == .property 0
#guard elaboratesToParameter p379_0 "Call0" == false

-- spec/dot-member-higher-order-parameter: K(a, t) = t(a) \n D(a, t) = a.t \n  \n K(7, {a+1}) \n D(7, {a+1})
def p380_0 : List OwnerLevel := { parameters := [], properties := ["K", "D"] } :: prelude
def p380_1 : List OwnerLevel := { parameters := ["a", "t"], properties := [] } :: p380_0
def p380_2 : List OwnerLevel := { parameters := ["a", "t"], properties := [] } :: p380_0
def p380_3 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p380_0
def p380_4 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p380_0
#guard selectOwnedDeclaration p380_1 "t" == .parameter 0
#guard elaboratesToParameter p380_1 "t" == true
#guard selectOwnedDeclaration p380_1 "a" == .parameter 0
#guard elaboratesToParameter p380_1 "a" == true
#guard selectOwnedDeclaration p380_2 "a" == .parameter 0
#guard elaboratesToParameter p380_2 "a" == true
#guard selectOwnedDeclaration p380_2 "t" == .parameter 0
#guard elaboratesToParameter p380_2 "t" == true
#guard selectOwnedDeclaration p380_0 "K" == .property 0
#guard elaboratesToParameter p380_0 "K" == false
#guard selectOwnedDeclaration p380_3 "a" == .parameter 0
#guard elaboratesToParameter p380_3 "a" == true
#guard selectOwnedDeclaration p380_0 "D" == .property 0
#guard elaboratesToParameter p380_0 "D" == false
#guard selectOwnedDeclaration p380_4 "a" == .parameter 0
#guard elaboratesToParameter p380_4 "a" == true

-- spec/dot-member-fallback-implicit-signature: K = a.t \n K(7, {a+1})
def p381_0 : List OwnerLevel := { parameters := [], properties := ["K"] } :: prelude
def p381_1 : List OwnerLevel := { parameters := ["a", "t"], properties := [] } :: p381_0
def p381_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p381_0
#guard selectOwnedDeclaration p381_1 "a" == .parameter 0
#guard elaboratesToParameter p381_1 "a" == true
#guard selectOwnedDeclaration p381_1 "t" == .parameter 0
#guard elaboratesToParameter p381_1 "t" == true
#guard selectOwnedDeclaration p381_0 "K" == .property 0
#guard elaboratesToParameter p381_0 "K" == false
#guard selectOwnedDeclaration p381_2 "a" == .parameter 0
#guard elaboratesToParameter p381_2 "a" == true

-- spec/grace-dot-higher-order-implicit: K = a~.t \n K({a+1}, 7)
def p382_0 : List OwnerLevel := { parameters := [], properties := ["K"] } :: prelude
def p382_1 : List OwnerLevel := { parameters := ["t", "a"], properties := [] } :: p382_0
def p382_2 : List OwnerLevel := { parameters := ["a"], properties := [] } :: p382_0
#guard selectOwnedDeclaration p382_1 "a" == .parameter 0
#guard elaboratesToParameter p382_1 "a" == true
#guard selectOwnedDeclaration p382_1 "t" == .parameter 0
#guard elaboratesToParameter p382_1 "t" == true
#guard selectOwnedDeclaration p382_0 "K" == .property 0
#guard elaboratesToParameter p382_0 "K" == false
#guard selectOwnedDeclaration p382_2 "a" == .parameter 0
#guard elaboratesToParameter p382_2 "a" == true

-- spec/grace-dot-keeps-structural-precedence: V(x) = 99 \n Obj = { \n     public V = 42 \n     0 \n } \n Read = o~.V \n  \n Obj.V \n Read(Obj)
def p383_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "Read", "V"] } :: prelude
def p383_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p383_0
def p383_2 : List OwnerLevel := { parameters := [], properties := [] } :: p383_1
def p383_3 : List OwnerLevel := { parameters := ["o"], properties := [] } :: p383_0
def p383_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p383_0
#guard selectOwnedDeclaration p383_3 "o" == .parameter 0
#guard elaboratesToParameter p383_3 "o" == true
#guard selectOwnedDeclaration p383_3 "V" == .property 1
#guard elaboratesToParameter p383_3 "V" == false
#guard selectOwnedDeclaration p383_0 "Obj" == .property 0 -- x2
#guard elaboratesToParameter p383_0 "Obj" == false -- x2
#guard selectOwnedDeclaration p383_0 "V" == .property 0
#guard elaboratesToParameter p383_0 "V" == false
#guard selectOwnedDeclaration p383_0 "Read" == .property 0
#guard elaboratesToParameter p383_0 "Read" == false

-- spec/dot-member-fallback-in-closed-parameter-list: K(x) = x.V \n Obj = {public V = 42} \n  \n K(Obj)
def p384_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "K"] } :: prelude
def p384_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p384_0
def p384_2 : List OwnerLevel := { parameters := [], properties := [] } :: p384_1
def p384_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p384_0
#guard selectOwnedDeclaration p384_3 "x" == .parameter 0
#guard elaboratesToParameter p384_3 "x" == true
#guard selectOwnedDeclaration p384_3 "V" == .none
#guard elaboratesToParameter p384_3 "V" == false
#guard selectOwnedDeclaration p384_0 "K" == .property 0
#guard elaboratesToParameter p384_0 "K" == false
#guard selectOwnedDeclaration p384_0 "Obj" == .property 0
#guard elaboratesToParameter p384_0 "Obj" == false

-- spec/dot-fallback-on-known-receiver-stays-valid: Lib = { \n     public Double(x) = 2 * x \n } \n Dubel(a, b) = b * 3 \n  \n Lib.Dubel(4)
def p385_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Dubel"] } :: prelude
def p385_1 : List OwnerLevel := { parameters := [], properties := ["Double"] } :: p385_0
def p385_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p385_1
def p385_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p385_0
#guard selectOwnedDeclaration p385_2 "x" == .parameter 0
#guard elaboratesToParameter p385_2 "x" == true
#guard selectOwnedDeclaration p385_3 "b" == .parameter 0
#guard elaboratesToParameter p385_3 "b" == true
#guard selectOwnedDeclaration p385_0 "Lib" == .property 0
#guard elaboratesToParameter p385_0 "Lib" == false
#guard selectOwnedDeclaration p385_0 "Dubel" == .property 0
#guard elaboratesToParameter p385_0 "Dubel" == false

-- spec/dot-string-declared-member-wins: Obj = { \n     public string = 5 \n     7 \n } \n  \n Obj.string
def p386_0 : List OwnerLevel := { parameters := [], properties := ["Obj"] } :: prelude
def p386_1 : List OwnerLevel := { parameters := [], properties := ["string"] } :: p386_0
def p386_2 : List OwnerLevel := { parameters := [], properties := [] } :: p386_1
#guard selectOwnedDeclaration p386_0 "Obj" == .property 0
#guard elaboratesToParameter p386_0 "Obj" == false
#guard selectOwnedDeclaration p386_0 "string" == .none
#guard elaboratesToParameter p386_0 "string" == false

-- spec/dot-string-intrinsic-on-structural-miss: string(x) = 99 \n Obj = { \n     public V = 1 \n     7 \n } \n  \n 3.string \n Obj.string \n string(3)
def p387_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "string"] } :: prelude
def p387_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p387_0
def p387_2 : List OwnerLevel := { parameters := [], properties := [] } :: p387_1
def p387_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p387_0
#guard selectOwnedDeclaration p387_0 "string" == .property 0 -- x3
#guard elaboratesToParameter p387_0 "string" == false -- x3
#guard selectOwnedDeclaration p387_0 "Obj" == .property 0
#guard elaboratesToParameter p387_0 "Obj" == false

-- spec/grouped-structural-callee-is-the-member: Box = { \n     public G(x) = x * 10 \n } \n Apply(f, v) = f(v) \n  \n Box.G(2) \n (Box.G)(2) \n Apply(Box.G, 2)
def p388_0 : List OwnerLevel := { parameters := [], properties := ["Box", "Apply"] } :: prelude
def p388_1 : List OwnerLevel := { parameters := [], properties := ["G"] } :: p388_0
def p388_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p388_1
def p388_3 : List OwnerLevel := { parameters := ["f", "v"], properties := [] } :: p388_0
#guard selectOwnedDeclaration p388_2 "x" == .parameter 0
#guard elaboratesToParameter p388_2 "x" == true
#guard selectOwnedDeclaration p388_3 "f" == .parameter 0
#guard elaboratesToParameter p388_3 "f" == true
#guard selectOwnedDeclaration p388_3 "v" == .parameter 0
#guard elaboratesToParameter p388_3 "v" == true
#guard selectOwnedDeclaration p388_0 "Box" == .property 0 -- x3
#guard elaboratesToParameter p388_0 "Box" == false -- x3
#guard selectOwnedDeclaration p388_0 "G" == .none -- x3
#guard elaboratesToParameter p388_0 "G" == false -- x3
#guard selectOwnedDeclaration p388_0 "Apply" == .property 0
#guard elaboratesToParameter p388_0 "Apply" == false

-- spec/grouped-zero-arg-member-call-is-fresh: Box = { \n     public V = 7 \n } \n  \n Box.V \n Box.V() \n (Box.V)()
def p389_0 : List OwnerLevel := { parameters := [], properties := ["Box"] } :: prelude
def p389_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p389_0
def p389_2 : List OwnerLevel := { parameters := [], properties := [] } :: p389_1
#guard selectOwnedDeclaration p389_0 "Box" == .property 0 -- x3
#guard elaboratesToParameter p389_0 "Box" == false -- x3
#guard selectOwnedDeclaration p389_0 "V" == .none -- x3
#guard elaboratesToParameter p389_0 "V" == false -- x3

-- spec/computed-dot-callee-is-not-callable: Inc(x) = x + 1 \n (5.Inc)()
def p390_0 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: prelude
def p390_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p390_0
#guard selectOwnedDeclaration p390_1 "x" == .parameter 0
#guard elaboratesToParameter p390_1 "x" == true
#guard selectOwnedDeclaration p390_0 "Inc" == .property 0
#guard elaboratesToParameter p390_0 "Inc" == false

-- spec/closed-list-must-fallback-name-is-checked: Get(obj) = 5.size \n  \n Get(1)
def p391_0 : List OwnerLevel := { parameters := [], properties := ["Get"] } :: prelude
def p391_1 : List OwnerLevel := { parameters := ["obj"], properties := [] } :: p391_0
#guard selectOwnedDeclaration p391_1 "size" == .none
#guard elaboratesToParameter p391_1 "size" == false
#guard selectOwnedDeclaration p391_0 "Get" == .property 0
#guard elaboratesToParameter p391_0 "Get" == false

-- spec/closed-list-may-fallback-name-is-runtime: Get(obj) = obj.size \n Obj = { \n     public size = 11 \n } \n size(v) = 77 \n  \n Get(Obj) \n Get(3)
def p392_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "Get", "size"] } :: prelude
def p392_1 : List OwnerLevel := { parameters := [], properties := ["size"] } :: p392_0
def p392_2 : List OwnerLevel := { parameters := [], properties := [] } :: p392_1
def p392_3 : List OwnerLevel := { parameters := ["obj"], properties := [] } :: p392_0
def p392_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p392_0
#guard selectOwnedDeclaration p392_3 "obj" == .parameter 0
#guard elaboratesToParameter p392_3 "obj" == true
#guard selectOwnedDeclaration p392_3 "size" == .property 1
#guard elaboratesToParameter p392_3 "size" == false
#guard selectOwnedDeclaration p392_0 "Get" == .property 0 -- x2
#guard elaboratesToParameter p392_0 "Get" == false -- x2
#guard selectOwnedDeclaration p392_0 "Obj" == .property 0
#guard elaboratesToParameter p392_0 "Obj" == false

-- spec/branch-must-fallback-name-is-checked: F(0) = 0 \n F(n) = (n + 1).G \n  \n F(0)
def p393_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p393_1 : List OwnerLevel := { parameters := [], properties := [] } :: p393_0
def p393_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p393_0
#guard selectOwnedDeclaration p393_2 "n" == .parameter 0
#guard elaboratesToParameter p393_2 "n" == true
#guard selectOwnedDeclaration p393_2 "G" == .none
#guard elaboratesToParameter p393_2 "G" == false
#guard selectOwnedDeclaration p393_0 "F" == .property 0
#guard elaboratesToParameter p393_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/open-local-only-member-inside-owner: Outer(n) = { \n     open Inner \n     Inner = { \n         public X = n \n     } \n     X + 0 \n } \n Outer(5)
def p394_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p394_1 : List OwnerLevel := { parameters := ["n"], properties := ["Inner"] } :: p394_0
def p394_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p394_1
def p394_3 : List OwnerLevel := { parameters := [], properties := [] } :: p394_2
#guard selectOwnedDeclaration p394_1 "Inner" == .property 0
#guard openHead? (elaborateOpenHead p394_1 "Inner") == some (false, "Inner")
#guard selectOwnedDeclaration p394_3 "n" == .parameter 2
#guard elaboratesToParameter p394_3 "n" == true
#guard selectOwnedDeclaration p394_1 "X" == .none
#guard elaboratesToParameter p394_1 "X" == false
#guard selectOwnedDeclaration p394_0 "Outer" == .property 0
#guard elaboratesToParameter p394_0 "Outer" == false

-- spec/dot-local-only-member-outside-owner: Outer(n) = { \n     Inner = { \n         public X = n \n     } \n     Inner.X \n } \n Outer.Inner.X
def p395_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p395_1 : List OwnerLevel := { parameters := ["n"], properties := ["Inner"] } :: p395_0
def p395_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p395_1
def p395_3 : List OwnerLevel := { parameters := [], properties := [] } :: p395_2
#guard selectOwnedDeclaration p395_3 "n" == .parameter 2
#guard elaboratesToParameter p395_3 "n" == true
#guard selectOwnedDeclaration p395_1 "Inner" == .property 0
#guard elaboratesToParameter p395_1 "Inner" == false
#guard selectOwnedDeclaration p395_1 "X" == .none
#guard elaboratesToParameter p395_1 "X" == false
#guard selectOwnedDeclaration p395_0 "Outer" == .property 0
#guard elaboratesToParameter p395_0 "Outer" == false
#guard selectOwnedDeclaration p395_0 "Inner" == .none
#guard elaboratesToParameter p395_0 "Inner" == false
#guard selectOwnedDeclaration p395_0 "X" == .none
#guard elaboratesToParameter p395_0 "X" == false

-- spec/dot-local-only-reference-target-walk: F(y) = { \n   Lib = { \n     public Sub = { \n       public Q = 1 \n       y \n     } \n     0 \n   } \n   L = Lib.Sub \n   A = L.Q + 0 \n   A \n } \n F(5), F.A
def p396_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p396_1 : List OwnerLevel := { parameters := ["y"], properties := ["Lib", "L", "A"] } :: p396_0
def p396_2 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p396_1
def p396_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p396_2
def p396_4 : List OwnerLevel := { parameters := [], properties := [] } :: p396_3
def p396_5 : List OwnerLevel := { parameters := [], properties := [] } :: p396_1
def p396_6 : List OwnerLevel := { parameters := [], properties := [] } :: p396_1
#guard selectOwnedDeclaration p396_3 "y" == .parameter 2
#guard elaboratesToParameter p396_3 "y" == true
#guard selectOwnedDeclaration p396_5 "Lib" == .property 1
#guard elaboratesToParameter p396_5 "Lib" == false
#guard selectOwnedDeclaration p396_5 "Sub" == .none
#guard elaboratesToParameter p396_5 "Sub" == false
#guard selectOwnedDeclaration p396_6 "L" == .property 1
#guard elaboratesToParameter p396_6 "L" == false
#guard selectOwnedDeclaration p396_6 "Q" == .none
#guard elaboratesToParameter p396_6 "Q" == false
#guard selectOwnedDeclaration p396_1 "A" == .property 0
#guard elaboratesToParameter p396_1 "A" == false
#guard selectOwnedDeclaration p396_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p396_0 "F" == false -- x2
#guard selectOwnedDeclaration p396_0 "A" == .none
#guard elaboratesToParameter p396_0 "A" == false

-- spec/dot-local-only-inline-block-head: F(y) = { \n   A = { \n     public Sub = { \n       public Q = 1 \n       y \n     } \n   }.Sub.Q + 0 \n   A \n } \n F(5), F.A
def p397_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p397_1 : List OwnerLevel := { parameters := ["y"], properties := ["A"] } :: p397_0
def p397_2 : List OwnerLevel := { parameters := [], properties := [] } :: p397_1
def p397_3 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p397_2
def p397_4 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p397_3
def p397_5 : List OwnerLevel := { parameters := [], properties := [] } :: p397_4
#guard selectOwnedDeclaration p397_4 "y" == .parameter 3
#guard elaboratesToParameter p397_4 "y" == true
#guard selectOwnedDeclaration p397_2 "Sub" == .none
#guard elaboratesToParameter p397_2 "Sub" == false
#guard selectOwnedDeclaration p397_2 "Q" == .none
#guard elaboratesToParameter p397_2 "Q" == false
#guard selectOwnedDeclaration p397_1 "A" == .property 0
#guard elaboratesToParameter p397_1 "A" == false
#guard selectOwnedDeclaration p397_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p397_0 "F" == false -- x2
#guard selectOwnedDeclaration p397_0 "A" == .none
#guard elaboratesToParameter p397_0 "A" == false

-- spec/open-local-only-through-reference: F(y) = { \n   Lib = { \n     public Sub = { \n       public Q = 1 \n       y \n     } \n     0 \n   } \n   L = Lib.Sub \n   A = { \n     open L \n     Q + 0 \n   } \n   A \n } \n F(5), F.A
def p398_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p398_1 : List OwnerLevel := { parameters := ["y"], properties := ["Lib", "L", "A"] } :: p398_0
def p398_2 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p398_1
def p398_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p398_2
def p398_4 : List OwnerLevel := { parameters := [], properties := [] } :: p398_3
def p398_5 : List OwnerLevel := { parameters := [], properties := [] } :: p398_1
def p398_6 : List OwnerLevel := { parameters := [], properties := [] } :: p398_1
#guard selectOwnedDeclaration p398_3 "y" == .parameter 2
#guard elaboratesToParameter p398_3 "y" == true
#guard selectOwnedDeclaration p398_5 "Lib" == .property 1
#guard elaboratesToParameter p398_5 "Lib" == false
#guard selectOwnedDeclaration p398_5 "Sub" == .none
#guard elaboratesToParameter p398_5 "Sub" == false
#guard selectOwnedDeclaration p398_6 "L" == .property 1
#guard openHead? (elaborateOpenHead p398_6 "L") == some (false, "L")
#guard selectOwnedDeclaration p398_6 "Q" == .none
#guard elaboratesToParameter p398_6 "Q" == false
#guard selectOwnedDeclaration p398_1 "A" == .property 0
#guard elaboratesToParameter p398_1 "A" == false
#guard selectOwnedDeclaration p398_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p398_0 "F" == false -- x2
#guard selectOwnedDeclaration p398_0 "A" == .none
#guard elaboratesToParameter p398_0 "A" == false

-- spec/open-local-only-enclosing-level: F(y) = { \n   open Lib.Sub \n   Lib = { \n     public Sub = { \n       public Q = 1 \n       y \n     } \n     0 \n   } \n   A = Q + 0 \n   A \n } \n F(5), F.A
def p399_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p399_1 : List OwnerLevel := { parameters := ["y"], properties := ["Lib", "A"] } :: p399_0
def p399_2 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p399_1
def p399_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p399_2
def p399_4 : List OwnerLevel := { parameters := [], properties := [] } :: p399_3
def p399_5 : List OwnerLevel := { parameters := [], properties := [] } :: p399_1
#guard selectOwnedDeclaration p399_1 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p399_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p399_3 "y" == .parameter 2
#guard elaboratesToParameter p399_3 "y" == true
#guard selectOwnedDeclaration p399_5 "Q" == .none
#guard elaboratesToParameter p399_5 "Q" == false
#guard selectOwnedDeclaration p399_1 "A" == .property 0
#guard elaboratesToParameter p399_1 "A" == false
#guard selectOwnedDeclaration p399_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p399_0 "F" == false -- x2
#guard selectOwnedDeclaration p399_0 "A" == .none
#guard elaboratesToParameter p399_0 "A" == false

-- spec/open-block-headed-reference-keeps-requirement: F(y) = { \n   open L \n   L = { \n     public Sub = { \n       public Q = y \n       0 \n     } \n   }.Sub \n   A = Q + 0 \n   A \n } \n F(5), F(7)
def p400_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p400_1 : List OwnerLevel := { parameters := ["y"], properties := ["L", "A"] } :: p400_0
def p400_2 : List OwnerLevel := { parameters := [], properties := [] } :: p400_1
def p400_3 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p400_2
def p400_4 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p400_3
def p400_5 : List OwnerLevel := { parameters := [], properties := [] } :: p400_4
def p400_6 : List OwnerLevel := { parameters := [], properties := [] } :: p400_1
#guard selectOwnedDeclaration p400_1 "L" == .property 0
#guard openHead? (elaborateOpenHead p400_1 "L") == some (false, "L")
#guard selectOwnedDeclaration p400_5 "y" == .parameter 4
#guard elaboratesToParameter p400_5 "y" == true
#guard selectOwnedDeclaration p400_2 "Sub" == .none
#guard elaboratesToParameter p400_2 "Sub" == false
#guard selectOwnedDeclaration p400_6 "Q" == .none
#guard elaboratesToParameter p400_6 "Q" == false
#guard selectOwnedDeclaration p400_1 "A" == .property 0
#guard elaboratesToParameter p400_1 "A" == false
#guard selectOwnedDeclaration p400_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p400_0 "F" == false -- x2

-- spec/impossible-read-in-untaken-branch-charges-nothing: F(y) = { \n   A = y + 1 \n   A \n } \n Box = { \n   public R = if(false, F.A, 0) \n } \n Box.R
def p401_0 : List OwnerLevel := { parameters := [], properties := ["Box", "F"] } :: prelude
def p401_1 : List OwnerLevel := { parameters := [], properties := ["R"] } :: p401_0
def p401_2 : List OwnerLevel := { parameters := [], properties := [] } :: p401_1
def p401_3 : List OwnerLevel := { parameters := ["y"], properties := ["A"] } :: p401_0
def p401_4 : List OwnerLevel := { parameters := [], properties := [] } :: p401_3
#guard selectOwnedDeclaration p401_2 "if" == .property 3
#guard elaboratesToParameter p401_2 "if" == false
#guard selectOwnedDeclaration p401_2 "F" == .property 2
#guard elaboratesToParameter p401_2 "F" == false
#guard selectOwnedDeclaration p401_2 "A" == .none
#guard elaboratesToParameter p401_2 "A" == false
#guard selectOwnedDeclaration p401_4 "y" == .parameter 1
#guard elaboratesToParameter p401_4 "y" == true
#guard selectOwnedDeclaration p401_3 "A" == .property 0
#guard elaboratesToParameter p401_3 "A" == false
#guard selectOwnedDeclaration p401_0 "Box" == .property 0
#guard elaboratesToParameter p401_0 "Box" == false
#guard selectOwnedDeclaration p401_0 "R" == .none
#guard elaboratesToParameter p401_0 "R" == false

-- spec/open-reference-checked-where-it-is-opened: F(y) = { \n   L = Lib.Mid.Sub \n   Lib = { \n     public Mid(p) = { \n       public Sub = { \n         public Q = 1 \n         p \n       } \n       B(z) = { \n         open L \n         Q + 0 \n       } \n       B(0) \n     } \n     0 \n   } \n   Lib.Mid(y) \n } \n F(5)
def p402_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p402_1 : List OwnerLevel := { parameters := ["y"], properties := ["L", "Lib"] } :: p402_0
def p402_2 : List OwnerLevel := { parameters := [], properties := [] } :: p402_1
def p402_3 : List OwnerLevel := { parameters := [], properties := ["Mid"] } :: p402_1
def p402_4 : List OwnerLevel := { parameters := ["p"], properties := ["Sub", "B"] } :: p402_3
def p402_5 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p402_4
def p402_6 : List OwnerLevel := { parameters := [], properties := [] } :: p402_5
def p402_7 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p402_4
#guard selectOwnedDeclaration p402_2 "Lib" == .property 1
#guard elaboratesToParameter p402_2 "Lib" == false
#guard selectOwnedDeclaration p402_2 "Mid" == .none
#guard elaboratesToParameter p402_2 "Mid" == false
#guard selectOwnedDeclaration p402_2 "Sub" == .none
#guard elaboratesToParameter p402_2 "Sub" == false
#guard selectOwnedDeclaration p402_5 "p" == .parameter 1
#guard elaboratesToParameter p402_5 "p" == true
#guard selectOwnedDeclaration p402_7 "L" == .property 3
#guard openHead? (elaborateOpenHead p402_7 "L") == some (false, "L")
#guard selectOwnedDeclaration p402_7 "Q" == .none
#guard elaboratesToParameter p402_7 "Q" == false
#guard selectOwnedDeclaration p402_4 "B" == .property 0
#guard elaboratesToParameter p402_4 "B" == false
#guard selectOwnedDeclaration p402_1 "Lib" == .property 0
#guard elaboratesToParameter p402_1 "Lib" == false
#guard selectOwnedDeclaration p402_1 "Mid" == .none
#guard elaboratesToParameter p402_1 "Mid" == false
#guard selectOwnedDeclaration p402_1 "y" == .parameter 0
#guard elaboratesToParameter p402_1 "y" == true
#guard selectOwnedDeclaration p402_0 "F" == .property 0
#guard elaboratesToParameter p402_0 "F" == false

-- spec/open-block-headed-reference-target-must-resolve: F(y) = { \n   open L.Missing \n   L = { \n     public Sub = { \n       public Q = y \n       0 \n     } \n   }.Sub \n   1 \n } \n F(5)
def p403_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p403_1 : List OwnerLevel := { parameters := ["y"], properties := ["L"] } :: p403_0
def p403_2 : List OwnerLevel := { parameters := [], properties := [] } :: p403_1
def p403_3 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p403_2
def p403_4 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p403_3
def p403_5 : List OwnerLevel := { parameters := [], properties := [] } :: p403_4
#guard selectOwnedDeclaration p403_1 "L" == .property 0
#guard openHead? (elaborateOpenHead p403_1 "L") == some (false, "L")
#guard selectOwnedDeclaration p403_5 "y" == .parameter 4
#guard elaboratesToParameter p403_5 "y" == true
#guard selectOwnedDeclaration p403_2 "Sub" == .none
#guard elaboratesToParameter p403_2 "Sub" == false
#guard selectOwnedDeclaration p403_0 "F" == .property 0
#guard elaboratesToParameter p403_0 "F" == false

-- spec/dot-exported-inline-block-head-member: F(y) = { \n   A = { \n     public Q = 1 \n     y + 0 \n   }.Q + 0 \n   A \n } \n F(5), F.A
def p404_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p404_1 : List OwnerLevel := { parameters := ["y"], properties := ["A"] } :: p404_0
def p404_2 : List OwnerLevel := { parameters := [], properties := [] } :: p404_1
def p404_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p404_2
def p404_4 : List OwnerLevel := { parameters := [], properties := [] } :: p404_3
#guard selectOwnedDeclaration p404_3 "y" == .parameter 2
#guard elaboratesToParameter p404_3 "y" == true
#guard selectOwnedDeclaration p404_2 "Q" == .none
#guard elaboratesToParameter p404_2 "Q" == false
#guard selectOwnedDeclaration p404_1 "A" == .property 0
#guard elaboratesToParameter p404_1 "A" == false
#guard selectOwnedDeclaration p404_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p404_0 "F" == false -- x2
#guard selectOwnedDeclaration p404_0 "A" == .none
#guard elaboratesToParameter p404_0 "A" == false

-- spec/dot-exported-value-only-reference: F(y) = { \n   Lib = { \n     public Q = 1 \n     y \n   } \n   L = Lib \n   A = L.Q + 0 \n   A \n } \n F(5), F.A
def p405_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p405_1 : List OwnerLevel := { parameters := ["y"], properties := ["Lib", "L", "A"] } :: p405_0
def p405_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p405_1
def p405_3 : List OwnerLevel := { parameters := [], properties := [] } :: p405_2
def p405_4 : List OwnerLevel := { parameters := [], properties := [] } :: p405_1
def p405_5 : List OwnerLevel := { parameters := [], properties := [] } :: p405_1
#guard selectOwnedDeclaration p405_2 "y" == .parameter 1
#guard elaboratesToParameter p405_2 "y" == true
#guard selectOwnedDeclaration p405_4 "Lib" == .property 1
#guard elaboratesToParameter p405_4 "Lib" == false
#guard selectOwnedDeclaration p405_5 "L" == .property 1
#guard elaboratesToParameter p405_5 "L" == false
#guard selectOwnedDeclaration p405_5 "Q" == .none
#guard elaboratesToParameter p405_5 "Q" == false
#guard selectOwnedDeclaration p405_1 "A" == .property 0
#guard elaboratesToParameter p405_1 "A" == false
#guard selectOwnedDeclaration p405_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p405_0 "F" == false -- x2
#guard selectOwnedDeclaration p405_0 "A" == .none
#guard elaboratesToParameter p405_0 "A" == false

-- spec/open-exported-runtime-reference: F(y) = { \n   open L, Other \n   L = y \n   Other = { public Q = 1 } \n   A = Q + 0 \n   A \n } \n F(5), F.A
def p406_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p406_1 : List OwnerLevel := { parameters := ["y"], properties := ["L", "Other", "A"] } :: p406_0
def p406_2 : List OwnerLevel := { parameters := [], properties := [] } :: p406_1
def p406_3 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p406_1
def p406_4 : List OwnerLevel := { parameters := [], properties := [] } :: p406_3
def p406_5 : List OwnerLevel := { parameters := [], properties := [] } :: p406_1
#guard selectOwnedDeclaration p406_1 "L" == .property 0
#guard openHead? (elaborateOpenHead p406_1 "L") == some (false, "L")
#guard selectOwnedDeclaration p406_1 "Other" == .property 0
#guard openHead? (elaborateOpenHead p406_1 "Other") == some (false, "Other")
#guard selectOwnedDeclaration p406_2 "y" == .parameter 1
#guard elaboratesToParameter p406_2 "y" == true
#guard selectOwnedDeclaration p406_5 "Q" == .none
#guard elaboratesToParameter p406_5 "Q" == false
#guard selectOwnedDeclaration p406_1 "A" == .property 0
#guard elaboratesToParameter p406_1 "A" == false
#guard selectOwnedDeclaration p406_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p406_0 "F" == false -- x2
#guard selectOwnedDeclaration p406_0 "A" == .none
#guard elaboratesToParameter p406_0 "A" == false

-- spec/dot-path-fallback-edges-charge-their-callee: F(y) = { \n   T(v) = v + y \n   U(v) = v \n   Box = { public S = 5 } \n   A = Box.S.T.U + 0 \n   A \n } \n F(1), F(2)
def p407_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p407_1 : List OwnerLevel := { parameters := ["y"], properties := ["Box", "A", "T", "U"] } :: p407_0
def p407_2 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p407_1
def p407_3 : List OwnerLevel := { parameters := [], properties := [] } :: p407_2
def p407_4 : List OwnerLevel := { parameters := [], properties := [] } :: p407_1
def p407_5 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p407_1
def p407_6 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p407_1
#guard selectOwnedDeclaration p407_4 "Box" == .property 1
#guard elaboratesToParameter p407_4 "Box" == false
#guard selectOwnedDeclaration p407_4 "S" == .none
#guard elaboratesToParameter p407_4 "S" == false
#guard selectOwnedDeclaration p407_4 "T" == .property 1
#guard elaboratesToParameter p407_4 "T" == false
#guard selectOwnedDeclaration p407_4 "U" == .property 1
#guard elaboratesToParameter p407_4 "U" == false
#guard selectOwnedDeclaration p407_5 "v" == .parameter 0
#guard elaboratesToParameter p407_5 "v" == true
#guard selectOwnedDeclaration p407_5 "y" == .parameter 1
#guard elaboratesToParameter p407_5 "y" == true
#guard selectOwnedDeclaration p407_6 "v" == .parameter 0
#guard elaboratesToParameter p407_6 "v" == true
#guard selectOwnedDeclaration p407_1 "A" == .property 0
#guard elaboratesToParameter p407_1 "A" == false
#guard selectOwnedDeclaration p407_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p407_0 "F" == false -- x2

-- spec/dot-path-fallback-edges-inline-block-head: F(y) = { \n   T(v) = v + y \n   U(v) = v \n   A = { public S = 5 }.S.T.U + 0 \n   A \n } \n F(1), F(2)
def p408_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p408_1 : List OwnerLevel := { parameters := ["y"], properties := ["A", "T", "U"] } :: p408_0
def p408_2 : List OwnerLevel := { parameters := [], properties := [] } :: p408_1
def p408_3 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p408_2
def p408_4 : List OwnerLevel := { parameters := [], properties := [] } :: p408_3
def p408_5 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p408_1
def p408_6 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p408_1
#guard selectOwnedDeclaration p408_2 "S" == .none
#guard elaboratesToParameter p408_2 "S" == false
#guard selectOwnedDeclaration p408_2 "T" == .property 1
#guard elaboratesToParameter p408_2 "T" == false
#guard selectOwnedDeclaration p408_2 "U" == .property 1
#guard elaboratesToParameter p408_2 "U" == false
#guard selectOwnedDeclaration p408_5 "v" == .parameter 0
#guard elaboratesToParameter p408_5 "v" == true
#guard selectOwnedDeclaration p408_5 "y" == .parameter 1
#guard elaboratesToParameter p408_5 "y" == true
#guard selectOwnedDeclaration p408_6 "v" == .parameter 0
#guard elaboratesToParameter p408_6 "v" == true
#guard selectOwnedDeclaration p408_1 "A" == .property 0
#guard elaboratesToParameter p408_1 "A" == false
#guard selectOwnedDeclaration p408_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p408_0 "F" == false -- x2

-- spec/deconstruction-source-inline-block-member: F(y) = { \n   a, b = { public Q = (y, y + 1) }.Q \n   a, b \n } \n F(1), F(2)
def p409_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p409_1 : List OwnerLevel := { parameters := ["y"], properties := ["$deconstruct$0", "a", "b"] } :: p409_0
def p409_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p409_1
def p409_3 : List OwnerLevel := { parameters := [], properties := [] } :: p409_2
def p409_4 : List OwnerLevel := { parameters := [], properties := [] } :: p409_1
def p409_5 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p409_4
def p409_6 : List OwnerLevel := { parameters := [], properties := [] } :: p409_1
def p409_7 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p409_6
#guard selectOwnedDeclaration p409_3 "y" == .parameter 2 -- x2
#guard elaboratesToParameter p409_3 "y" == true -- x2
#guard selectOwnedDeclaration p409_1 "Q" == .none
#guard elaboratesToParameter p409_1 "Q" == false
#guard selectOwnedDeclaration p409_5 "a" == .parameter 0
#guard elaboratesToParameter p409_5 "a" == true
#guard selectOwnedDeclaration p409_4 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p409_4 "$deconstruct$0" == false
#guard selectOwnedDeclaration p409_7 "b" == .parameter 0
#guard elaboratesToParameter p409_7 "b" == true
#guard selectOwnedDeclaration p409_6 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p409_6 "$deconstruct$0" == false
#guard selectOwnedDeclaration p409_1 "a" == .property 0
#guard elaboratesToParameter p409_1 "a" == false
#guard selectOwnedDeclaration p409_1 "b" == .property 0
#guard elaboratesToParameter p409_1 "b" == false
#guard selectOwnedDeclaration p409_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p409_0 "F" == false -- x2

-- spec/open-distinct-declarations-stay-distinct-providers: open NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA, NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB \n NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA = { public X = 1 } \n NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB = { public X = 1 } \n X
def p410_0 : List OwnerLevel := { parameters := [], properties := ["NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA", "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB"] } :: prelude
def p410_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p410_0
def p410_2 : List OwnerLevel := { parameters := [], properties := [] } :: p410_1
def p410_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p410_0
def p410_4 : List OwnerLevel := { parameters := [], properties := [] } :: p410_3
#guard selectOwnedDeclaration p410_0 "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA" == .property 0
#guard openHead? (elaborateOpenHead p410_0 "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA") == some (false, "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNA")
#guard selectOwnedDeclaration p410_0 "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB" == .property 0
#guard openHead? (elaborateOpenHead p410_0 "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB") == some (false, "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNB")
#guard selectOwnedDeclaration p410_0 "X" == .none
#guard elaboratesToParameter p410_0 "X" == false

-- spec/open-identical-inline-blocks-two-providers: open { public X = 1 }, { public X = 1 } \n X
def p411_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p411_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p411_2 : List OwnerLevel := { parameters := [], properties := [] } :: p411_1
def p411_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p411_4 : List OwnerLevel := { parameters := [], properties := [] } :: p411_3
#guard selectOwnedDeclaration p411_0 "X" == .none
#guard elaboratesToParameter p411_0 "X" == false

-- spec/ambiguous-open-written-use-is-static: open A, B \n A = { \n     public X = 1 \n } \n B = { \n     public X = 2 \n } \n Y = X \n 5
def p412_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "Y"] } :: prelude
def p412_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p412_0
def p412_2 : List OwnerLevel := { parameters := [], properties := [] } :: p412_1
def p412_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p412_0
def p412_4 : List OwnerLevel := { parameters := [], properties := [] } :: p412_3
def p412_5 : List OwnerLevel := { parameters := [], properties := [] } :: p412_0
#guard selectOwnedDeclaration p412_0 "A" == .property 0
#guard openHead? (elaborateOpenHead p412_0 "A") == some (false, "A")
#guard selectOwnedDeclaration p412_0 "B" == .property 0
#guard openHead? (elaborateOpenHead p412_0 "B") == some (false, "B")
#guard selectOwnedDeclaration p412_5 "X" == .none
#guard elaboratesToParameter p412_5 "X" == false

-- spec/ambiguous-open-unused-overlap-is-valid: open A, B \n A = { \n     public X = 1 \n     public P = 10 \n } \n B = { \n     public X = 2 \n     public Q = 20 \n } \n P + Q
def p413_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p413_1 : List OwnerLevel := { parameters := [], properties := ["X", "P"] } :: p413_0
def p413_2 : List OwnerLevel := { parameters := [], properties := [] } :: p413_1
def p413_3 : List OwnerLevel := { parameters := [], properties := [] } :: p413_1
def p413_4 : List OwnerLevel := { parameters := [], properties := ["X", "Q"] } :: p413_0
def p413_5 : List OwnerLevel := { parameters := [], properties := [] } :: p413_4
def p413_6 : List OwnerLevel := { parameters := [], properties := [] } :: p413_4
#guard selectOwnedDeclaration p413_0 "A" == .property 0
#guard openHead? (elaborateOpenHead p413_0 "A") == some (false, "A")
#guard selectOwnedDeclaration p413_0 "B" == .property 0
#guard openHead? (elaborateOpenHead p413_0 "B") == some (false, "B")
#guard selectOwnedDeclaration p413_0 "P" == .none
#guard elaboratesToParameter p413_0 "P" == false
#guard selectOwnedDeclaration p413_0 "Q" == .none
#guard elaboratesToParameter p413_0 "Q" == false

-- spec/dot-chain-structural-member-beats-extension: Lib = { \n     public Sub = { \n         public Q = 1 \n     } \n } \n  \n Q(x) = 99 \n  \n Lib.Sub.Q
def p414_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Q"] } :: prelude
def p414_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p414_0
def p414_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p414_1
def p414_3 : List OwnerLevel := { parameters := [], properties := [] } :: p414_2
def p414_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p414_0
#guard selectOwnedDeclaration p414_0 "Lib" == .property 0
#guard elaboratesToParameter p414_0 "Lib" == false
#guard selectOwnedDeclaration p414_0 "Sub" == .none
#guard elaboratesToParameter p414_0 "Sub" == false
#guard selectOwnedDeclaration p414_0 "Q" == .property 0
#guard elaboratesToParameter p414_0 "Q" == false

-- spec/dot-chain-extension-fallback-composes: A = x + 7 \n B = x * 5 \n  \n 3.A.B \n B(A(3)) \n B(3.A)
def p415_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p415_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p415_0
def p415_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p415_0
#guard selectOwnedDeclaration p415_1 "x" == .parameter 0
#guard elaboratesToParameter p415_1 "x" == true
#guard selectOwnedDeclaration p415_2 "x" == .parameter 0
#guard elaboratesToParameter p415_2 "x" == true
#guard selectOwnedDeclaration p415_0 "A" == .property 0 -- x3
#guard elaboratesToParameter p415_0 "A" == false -- x3
#guard selectOwnedDeclaration p415_0 "B" == .property 0 -- x3
#guard elaboratesToParameter p415_0 "B" == false -- x3

-- spec/dot-chain-nested-structural-members: A = { \n     public B = { \n         public C = { \n             public D = 7 \n         } \n     } \n } \n D(x) = 93 \n  \n A.B.C.D
def p416_0 : List OwnerLevel := { parameters := [], properties := ["A", "D"] } :: prelude
def p416_1 : List OwnerLevel := { parameters := [], properties := ["B"] } :: p416_0
def p416_2 : List OwnerLevel := { parameters := [], properties := ["C"] } :: p416_1
def p416_3 : List OwnerLevel := { parameters := [], properties := ["D"] } :: p416_2
def p416_4 : List OwnerLevel := { parameters := [], properties := [] } :: p416_3
def p416_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p416_0
#guard selectOwnedDeclaration p416_0 "A" == .property 0
#guard elaboratesToParameter p416_0 "A" == false
#guard selectOwnedDeclaration p416_0 "B" == .none
#guard elaboratesToParameter p416_0 "B" == false
#guard selectOwnedDeclaration p416_0 "C" == .none
#guard elaboratesToParameter p416_0 "C" == false
#guard selectOwnedDeclaration p416_0 "D" == .property 0
#guard elaboratesToParameter p416_0 "D" == false

-- spec/dot-chain-local-only-member-is-not-a-fallback: G(x) = { \n     public Sub = { \n         public Q = 1 \n         x \n     } \n     0 \n } \n Q(v) = 99 \n  \n G.Sub.Q
def p417_0 : List OwnerLevel := { parameters := [], properties := ["G", "Q"] } :: prelude
def p417_1 : List OwnerLevel := { parameters := ["x"], properties := ["Sub"] } :: p417_0
def p417_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p417_1
def p417_3 : List OwnerLevel := { parameters := [], properties := [] } :: p417_2
def p417_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p417_0
#guard selectOwnedDeclaration p417_2 "x" == .parameter 1
#guard elaboratesToParameter p417_2 "x" == true
#guard selectOwnedDeclaration p417_0 "G" == .property 0
#guard elaboratesToParameter p417_0 "G" == false
#guard selectOwnedDeclaration p417_0 "Sub" == .none
#guard elaboratesToParameter p417_0 "Sub" == false
#guard selectOwnedDeclaration p417_0 "Q" == .property 0
#guard elaboratesToParameter p417_0 "Q" == false

-- spec/inline-headed-open-paths-keep-distinct-providers: open { public S = { public X = 5 } }.S, { public S = { public X = 7 } }.S \n X
def p418_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p418_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p418_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p418_1
def p418_3 : List OwnerLevel := { parameters := [], properties := [] } :: p418_2
def p418_4 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p418_5 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p418_4
def p418_6 : List OwnerLevel := { parameters := [], properties := [] } :: p418_5
#guard selectOwnedDeclaration p418_0 "X" == .none
#guard elaboratesToParameter p418_0 "X" == false

-- spec/capture-suppresses-higher-order-identity: Apply = f(9) \n Increment(x) = x + 1 \n Probe(u) = Apply((Increment, Increment)) \n Probe(0)
def p419_0 : List OwnerLevel := { parameters := [], properties := ["Apply", "Increment", "Probe"] } :: prelude
def p419_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p419_0
def p419_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p419_0
def p419_3 : List OwnerLevel := { parameters := ["u"], properties := [] } :: p419_0
#guard selectOwnedDeclaration p419_1 "f" == .parameter 0
#guard elaboratesToParameter p419_1 "f" == true
#guard selectOwnedDeclaration p419_2 "x" == .parameter 0
#guard elaboratesToParameter p419_2 "x" == true
#guard selectOwnedDeclaration p419_3 "Apply" == .property 1
#guard elaboratesToParameter p419_3 "Apply" == false
#guard selectOwnedDeclaration p419_3 "Increment" == .property 1 -- x2
#guard elaboratesToParameter p419_3 "Increment" == false -- x2
#guard selectOwnedDeclaration p419_0 "Probe" == .property 0
#guard elaboratesToParameter p419_0 "Probe" == false

-- spec/capture-suppresses-structural-members: V(x) = 99 \n Obj = { \n     public V = 7 \n     0 \n } \n  \n Obj.V \n (Obj).V \n (Obj*).V
def p420_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "V"] } :: prelude
def p420_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p420_0
def p420_2 : List OwnerLevel := { parameters := [], properties := [] } :: p420_1
def p420_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p420_0
#guard selectOwnedDeclaration p420_0 "Obj" == .property 0 -- x3
#guard elaboratesToParameter p420_0 "Obj" == false -- x3
#guard selectOwnedDeclaration p420_0 "V" == .property 0 -- x3
#guard elaboratesToParameter p420_0 "V" == false -- x3

-- spec/output-dotted-access-ordinary: A = { \n     Output = 9 \n } \n  \n A.Output
def p421_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p421_1 : List OwnerLevel := { parameters := [], properties := ["Output"] } :: p421_0
def p421_2 : List OwnerLevel := { parameters := [], properties := [] } :: p421_1
#guard selectOwnedDeclaration p421_0 "A" == .property 0
#guard elaboratesToParameter p421_0 "A" == false
#guard selectOwnedDeclaration p421_0 "Output" == .none
#guard elaboratesToParameter p421_0 "Output" == false

-- spec/dot-call-structural-member-is-not-a-lexical-rewrite: B(a, c) = a * 100 + c \n Obj = { \n     public B(c) = c + 1 \n } \n  \n Obj.B(5) \n 3.B(5)
def p422_0 : List OwnerLevel := { parameters := [], properties := ["Obj", "B"] } :: prelude
def p422_1 : List OwnerLevel := { parameters := [], properties := ["B"] } :: p422_0
def p422_2 : List OwnerLevel := { parameters := ["c"], properties := [] } :: p422_1
def p422_3 : List OwnerLevel := { parameters := ["a", "c"], properties := [] } :: p422_0
#guard selectOwnedDeclaration p422_2 "c" == .parameter 0
#guard elaboratesToParameter p422_2 "c" == true
#guard selectOwnedDeclaration p422_3 "a" == .parameter 0
#guard elaboratesToParameter p422_3 "a" == true
#guard selectOwnedDeclaration p422_3 "c" == .parameter 0
#guard elaboratesToParameter p422_3 "c" == true
#guard selectOwnedDeclaration p422_0 "Obj" == .property 0
#guard elaboratesToParameter p422_0 "Obj" == false
#guard selectOwnedDeclaration p422_0 "B" == .property 0 -- x2
#guard elaboratesToParameter p422_0 "B" == false -- x2

-- spec/visibility-private-member-is-structural-not-exported: Lib = { \n     public Area = 4 \n     Helper = Area / 2 \n } \n  \n Lib.Area \n Lib.Helper
def p423_0 : List OwnerLevel := { parameters := [], properties := ["Lib"] } :: prelude
def p423_1 : List OwnerLevel := { parameters := [], properties := ["Area", "Helper"] } :: p423_0
def p423_2 : List OwnerLevel := { parameters := [], properties := [] } :: p423_1
def p423_3 : List OwnerLevel := { parameters := [], properties := [] } :: p423_1
#guard selectOwnedDeclaration p423_3 "Area" == .property 1
#guard elaboratesToParameter p423_3 "Area" == false
#guard selectOwnedDeclaration p423_0 "Lib" == .property 0 -- x2
#guard elaboratesToParameter p423_0 "Lib" == false -- x2
#guard selectOwnedDeclaration p423_0 "Area" == .none
#guard elaboratesToParameter p423_0 "Area" == false
#guard selectOwnedDeclaration p423_0 "Helper" == .none
#guard elaboratesToParameter p423_0 "Helper" == false

-- spec/zero-arg-access-of-parametrized: Add(a, b) = a + b \n  \n Add \n (1, 2)
-- the same levels and decisions, 1 more:
--   spec/multiline-call-open-delimiter
def p424_0 : List OwnerLevel := { parameters := [], properties := ["Add"] } :: prelude
def p424_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p424_0
#guard selectOwnedDeclaration p424_1 "a" == .parameter 0
#guard elaboratesToParameter p424_1 "a" == true
#guard selectOwnedDeclaration p424_1 "b" == .parameter 0
#guard elaboratesToParameter p424_1 "b" == true
#guard selectOwnedDeclaration p424_0 "Add" == .property 0
#guard elaboratesToParameter p424_0 "Add" == false

-- spec/filter-keeps-matching: IsEven = x mod 2 == 0 \n filter((1, 2, 3, 4, 5, 6), IsEven)
def p425_0 : List OwnerLevel := { parameters := [], properties := ["IsEven"] } :: prelude
def p425_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p425_0
#guard selectOwnedDeclaration p425_1 "x" == .parameter 0
#guard elaboratesToParameter p425_1 "x" == true
#guard selectOwnedDeclaration p425_0 "filter" == .property 1
#guard elaboratesToParameter p425_0 "filter" == false
#guard selectOwnedDeclaration p425_0 "IsEven" == .property 0
#guard elaboratesToParameter p425_0 "IsEven" == false

-- spec/map-transforms-items: Double = x * 2 \n map((1, 2, 3), Double)
def p426_0 : List OwnerLevel := { parameters := [], properties := ["Double"] } :: prelude
def p426_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p426_0
#guard selectOwnedDeclaration p426_1 "x" == .parameter 0
#guard elaboratesToParameter p426_1 "x" == true
#guard selectOwnedDeclaration p426_0 "map" == .property 1
#guard elaboratesToParameter p426_0 "map" == false
#guard selectOwnedDeclaration p426_0 "Double" == .property 0
#guard elaboratesToParameter p426_0 "Double" == false

-- spec/clause-family-multirow-callback-is-one-value: F(0) = 1, 2 \n F(n) = n, n \n map([0, 3], F)
def p427_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p427_1 : List OwnerLevel := { parameters := [], properties := [] } :: p427_0
def p427_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p427_0
#guard selectOwnedDeclaration p427_2 "n" == .parameter 0 -- x2
#guard elaboratesToParameter p427_2 "n" == true -- x2
#guard selectOwnedDeclaration p427_0 "map" == .property 1
#guard elaboratesToParameter p427_0 "map" == false
#guard selectOwnedDeclaration p427_0 "F" == .property 0
#guard elaboratesToParameter p427_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/clause-family-multirow-reduce-step-is-one-value: R(e, 0) = e, 0 \n R(e, acc) = e, acc \n reduce([1], R, 0)
def p428_0 : List OwnerLevel := { parameters := [], properties := ["R"] } :: prelude
def p428_1 : List OwnerLevel := { parameters := ["e"], properties := [] } :: p428_0
def p428_2 : List OwnerLevel := { parameters := ["e", "acc"], properties := [] } :: p428_0
#guard selectOwnedDeclaration p428_1 "e" == .parameter 0
#guard elaboratesToParameter p428_1 "e" == true
#guard selectOwnedDeclaration p428_2 "e" == .parameter 0
#guard elaboratesToParameter p428_2 "e" == true
#guard selectOwnedDeclaration p428_2 "acc" == .parameter 0
#guard elaboratesToParameter p428_2 "acc" == true
#guard selectOwnedDeclaration p428_0 "reduce" == .property 1
#guard elaboratesToParameter p428_0 "reduce" == false
#guard selectOwnedDeclaration p428_0 "R" == .property 0
#guard elaboratesToParameter p428_0 "R" == false
#guard familyLiftingSignature? [clause (.sequenceValue [.bind "e", .litInt 0]), clause (.sequenceValue [.bind "e", .bind "acc"])] == some [.capture { name := "e" }, .capture { name := "acc" }] -- family R

-- spec/clause-family-callback-single-value-accepted: F(0) = 1, 2 \n P(0) = (1, 2) \n P(n) = (n, n) \n L(0) = [] \n L(n) = [n] \n map([0, 3], P), map([0, 3], L), F(0) == P(0)
def p429_0 : List OwnerLevel := { parameters := [], properties := ["F", "P", "L"] } :: prelude
def p429_1 : List OwnerLevel := { parameters := [], properties := [] } :: p429_0
def p429_2 : List OwnerLevel := { parameters := [], properties := [] } :: p429_0
def p429_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p429_0
def p429_4 : List OwnerLevel := { parameters := [], properties := [] } :: p429_0
def p429_5 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p429_0
#guard selectOwnedDeclaration p429_3 "n" == .parameter 0 -- x2
#guard elaboratesToParameter p429_3 "n" == true -- x2
#guard selectOwnedDeclaration p429_5 "n" == .parameter 0
#guard elaboratesToParameter p429_5 "n" == true
#guard selectOwnedDeclaration p429_0 "map" == .property 1 -- x2
#guard elaboratesToParameter p429_0 "map" == false -- x2
#guard selectOwnedDeclaration p429_0 "P" == .property 0 -- x2
#guard elaboratesToParameter p429_0 "P" == false -- x2
#guard selectOwnedDeclaration p429_0 "L" == .property 0
#guard elaboratesToParameter p429_0 "L" == false
#guard selectOwnedDeclaration p429_0 "F" == .property 0
#guard elaboratesToParameter p429_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0)] == none -- family F
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family P
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family L

-- spec/callback-result-is-the-ordinary-call-result: D(x) = x, x \n G(x) = D(x) \n H(x) = (x, x) \n map([1], D), map([1], G), map([1], H), map([1, 2], D) == [D(1), D(2)]
def p430_0 : List OwnerLevel := { parameters := [], properties := ["D", "G", "H"] } :: prelude
def p430_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p430_0
def p430_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p430_0
def p430_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p430_0
#guard selectOwnedDeclaration p430_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p430_1 "x" == true -- x2
#guard selectOwnedDeclaration p430_2 "D" == .property 1
#guard elaboratesToParameter p430_2 "D" == false
#guard selectOwnedDeclaration p430_2 "x" == .parameter 0
#guard elaboratesToParameter p430_2 "x" == true
#guard selectOwnedDeclaration p430_3 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p430_3 "x" == true -- x2
#guard selectOwnedDeclaration p430_0 "map" == .property 1 -- x4
#guard elaboratesToParameter p430_0 "map" == false -- x4
#guard selectOwnedDeclaration p430_0 "D" == .property 0 -- x4
#guard elaboratesToParameter p430_0 "D" == false -- x4
#guard selectOwnedDeclaration p430_0 "G" == .property 0
#guard elaboratesToParameter p430_0 "G" == false
#guard selectOwnedDeclaration p430_0 "H" == .property 0
#guard elaboratesToParameter p430_0 "H" == false

-- spec/reduce-demands-initial-before-iteration: R(x, acc) = x \n reduce([1, 2], R, 1 / 0)
def p431_0 : List OwnerLevel := { parameters := [], properties := ["R"] } :: prelude
def p431_1 : List OwnerLevel := { parameters := ["x", "acc"], properties := [] } :: p431_0
#guard selectOwnedDeclaration p431_1 "x" == .parameter 0
#guard elaboratesToParameter p431_1 "x" == true
#guard selectOwnedDeclaration p431_0 "reduce" == .property 1
#guard elaboratesToParameter p431_0 "reduce" == false
#guard selectOwnedDeclaration p431_0 "R" == .property 0
#guard elaboratesToParameter p431_0 "R" == false

-- spec/nested-reducer-calls-may-skip-unused-initial: R(x, acc) = x \n R(2, R(1, 1 / 0))
def p432_0 : List OwnerLevel := { parameters := [], properties := ["R"] } :: prelude
def p432_1 : List OwnerLevel := { parameters := ["x", "acc"], properties := [] } :: p432_0
#guard selectOwnedDeclaration p432_1 "x" == .parameter 0
#guard elaboratesToParameter p432_1 "x" == true
#guard selectOwnedDeclaration p432_0 "R" == .property 0 -- x2
#guard elaboratesToParameter p432_0 "R" == false -- x2

-- spec/map-demands-collection-before-transforms: L = [1 / 0, 2] \n F(x) = 0 \n map(L, F)
def p433_0 : List OwnerLevel := { parameters := [], properties := ["L", "F"] } :: prelude
def p433_1 : List OwnerLevel := { parameters := [], properties := [] } :: p433_0
def p433_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p433_0
#guard selectOwnedDeclaration p433_0 "map" == .property 1
#guard elaboratesToParameter p433_0 "map" == false
#guard selectOwnedDeclaration p433_0 "L" == .property 0
#guard elaboratesToParameter p433_0 "L" == false
#guard selectOwnedDeclaration p433_0 "F" == .property 0
#guard elaboratesToParameter p433_0 "F" == false

-- spec/expanded-map-calls-may-skip-indexed-arguments: L = [1 / 0, 2] \n F(x) = 0 \n [F(L[0]), F(L[1])]
def p434_0 : List OwnerLevel := { parameters := [], properties := ["L", "F"] } :: prelude
def p434_1 : List OwnerLevel := { parameters := [], properties := [] } :: p434_0
def p434_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p434_0
#guard selectOwnedDeclaration p434_0 "F" == .property 0 -- x2
#guard elaboratesToParameter p434_0 "F" == false -- x2
#guard selectOwnedDeclaration p434_0 "L" == .property 0 -- x2
#guard elaboratesToParameter p434_0 "L" == false -- x2

-- spec/map-identity-preserves-empty-elements: Id(x) = x \n map([(), 1, [], 2], Id)
def p435_0 : List OwnerLevel := { parameters := [], properties := ["Id"] } :: prelude
def p435_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p435_0
#guard selectOwnedDeclaration p435_1 "x" == .parameter 0
#guard elaboratesToParameter p435_1 "x" == true
#guard selectOwnedDeclaration p435_0 "map" == .property 1
#guard elaboratesToParameter p435_0 "map" == false
#guard selectOwnedDeclaration p435_0 "Id" == .property 0
#guard elaboratesToParameter p435_0 "Id" == false

-- spec/reduce-accumulator-may-be-empty: R(x, acc) = acc \n reduce([1], R, ())
def p436_0 : List OwnerLevel := { parameters := [], properties := ["R"] } :: prelude
def p436_1 : List OwnerLevel := { parameters := ["x", "acc"], properties := [] } :: p436_0
#guard selectOwnedDeclaration p436_1 "acc" == .parameter 0
#guard elaboratesToParameter p436_1 "acc" == true
#guard selectOwnedDeclaration p436_0 "reduce" == .property 1
#guard elaboratesToParameter p436_0 "reduce" == false
#guard selectOwnedDeclaration p436_0 "R" == .property 0
#guard elaboratesToParameter p436_0 "R" == false

-- spec/callback-variadic-collects: Collect(*items) = items \n  \n [7].map(Collect) \n [(1, 2)].map(Collect) \n [[1, 2]].map(Collect)
def p437_0 : List OwnerLevel := { parameters := [], properties := ["Collect"] } :: prelude
def p437_1 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p437_0
#guard selectOwnedDeclaration p437_1 "items" == .parameter 0
#guard elaboratesToParameter p437_1 "items" == true
#guard selectOwnedDeclaration p437_0 "map" == .property 1 -- x3
#guard elaboratesToParameter p437_0 "map" == false -- x3
#guard selectOwnedDeclaration p437_0 "Collect" == .property 0 -- x3
#guard elaboratesToParameter p437_0 "Collect" == false -- x3

-- spec/callback-mixed-variadic-rows: F((first, *middle, last)) = middle \n Rows = [(1, 2, 3, 4)] \n  \n Rows.map(F)
def p438_0 : List OwnerLevel := { parameters := [], properties := ["Rows", "F"] } :: prelude
def p438_1 : List OwnerLevel := { parameters := [], properties := [] } :: p438_0
def p438_2 : List OwnerLevel := { parameters := ["first", "middle", "last"], properties := [] } :: p438_0
#guard selectOwnedDeclaration p438_2 "middle" == .parameter 0
#guard elaboratesToParameter p438_2 "middle" == true
#guard selectOwnedDeclaration p438_0 "Rows" == .property 0
#guard elaboratesToParameter p438_0 "Rows" == false
#guard selectOwnedDeclaration p438_0 "map" == .property 1
#guard elaboratesToParameter p438_0 "map" == false
#guard selectOwnedDeclaration p438_0 "F" == .property 0
#guard elaboratesToParameter p438_0 "F" == false

-- spec/callback-nested-pattern-binds-like-call: Head((x, *rest)) = [x, rest] \n  \n Head((7, 8)) \n [(7, 8)].map(Head) \n map([(7, 8), (9, 10, 11)], Head)
def p439_0 : List OwnerLevel := { parameters := [], properties := ["Head"] } :: prelude
def p439_1 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p439_0
#guard selectOwnedDeclaration p439_1 "x" == .parameter 0
#guard elaboratesToParameter p439_1 "x" == true
#guard selectOwnedDeclaration p439_1 "rest" == .parameter 0
#guard elaboratesToParameter p439_1 "rest" == true
#guard selectOwnedDeclaration p439_0 "Head" == .property 0 -- x3
#guard elaboratesToParameter p439_0 "Head" == false -- x3
#guard selectOwnedDeclaration p439_0 "map" == .property 1 -- x2
#guard elaboratesToParameter p439_0 "map" == false -- x2

-- spec/forwarded-callable-keeps-its-algorithm-channel: Cnt(*xs) = xs.count \n SumWhile(*s) = s.sum + 1, s.sum + 1 < 3 \n Apply(f, xs) = xs.map(f) \n Loop(g) = while(g(0)) \n Outer(xs) = { \n   Inner(g) = xs.map(g) \n   Inner(Cnt) \n } \n  \n Apply(Cnt, [1, 2]) \n Loop(SumWhile) \n Outer([1, 2])
def p440_0 : List OwnerLevel := { parameters := [], properties := ["Cnt", "SumWhile", "Apply", "Loop", "Outer"] } :: prelude
def p440_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p440_0
def p440_2 : List OwnerLevel := { parameters := ["s"], properties := [] } :: p440_0
def p440_3 : List OwnerLevel := { parameters := ["f", "xs"], properties := [] } :: p440_0
def p440_4 : List OwnerLevel := { parameters := ["g"], properties := [] } :: p440_0
def p440_5 : List OwnerLevel := { parameters := ["xs"], properties := ["Inner"] } :: p440_0
def p440_6 : List OwnerLevel := { parameters := ["g"], properties := [] } :: p440_5
#guard selectOwnedDeclaration p440_1 "xs" == .parameter 0
#guard elaboratesToParameter p440_1 "xs" == true
#guard selectOwnedDeclaration p440_1 "count" == .property 2
#guard elaboratesToParameter p440_1 "count" == false
#guard selectOwnedDeclaration p440_2 "s" == .parameter 0 -- x2
#guard elaboratesToParameter p440_2 "s" == true -- x2
#guard selectOwnedDeclaration p440_2 "sum" == .property 2 -- x2
#guard elaboratesToParameter p440_2 "sum" == false -- x2
#guard selectOwnedDeclaration p440_3 "xs" == .parameter 0
#guard elaboratesToParameter p440_3 "xs" == true
#guard selectOwnedDeclaration p440_3 "map" == .property 2
#guard elaboratesToParameter p440_3 "map" == false
#guard selectOwnedDeclaration p440_3 "f" == .parameter 0
#guard elaboratesToParameter p440_3 "f" == true
#guard selectOwnedDeclaration p440_4 "while" == .property 2
#guard elaboratesToParameter p440_4 "while" == false
#guard selectOwnedDeclaration p440_4 "g" == .parameter 0
#guard elaboratesToParameter p440_4 "g" == true
#guard selectOwnedDeclaration p440_6 "xs" == .parameter 1
#guard elaboratesToParameter p440_6 "xs" == true
#guard selectOwnedDeclaration p440_6 "map" == .property 3
#guard elaboratesToParameter p440_6 "map" == false
#guard selectOwnedDeclaration p440_6 "g" == .parameter 0
#guard elaboratesToParameter p440_6 "g" == true
#guard selectOwnedDeclaration p440_5 "Inner" == .property 0
#guard elaboratesToParameter p440_5 "Inner" == false
#guard selectOwnedDeclaration p440_5 "Cnt" == .property 1
#guard elaboratesToParameter p440_5 "Cnt" == false
#guard selectOwnedDeclaration p440_0 "Apply" == .property 0
#guard elaboratesToParameter p440_0 "Apply" == false
#guard selectOwnedDeclaration p440_0 "Cnt" == .property 0
#guard elaboratesToParameter p440_0 "Cnt" == false
#guard selectOwnedDeclaration p440_0 "Loop" == .property 0
#guard elaboratesToParameter p440_0 "Loop" == false
#guard selectOwnedDeclaration p440_0 "SumWhile" == .property 0
#guard elaboratesToParameter p440_0 "SumWhile" == false
#guard selectOwnedDeclaration p440_0 "Outer" == .property 0
#guard elaboratesToParameter p440_0 "Outer" == false

-- spec/builtin-call-assembly-respects-argument-roles: L = L + 1 \n Add(a, b) = a + b \n  \n map([], L) \n filter([], L) \n reduce([], L, 7) \n reduce([1, 2], Add, 10)
def p441_0 : List OwnerLevel := { parameters := [], properties := ["L", "Add"] } :: prelude
def p441_1 : List OwnerLevel := { parameters := [], properties := [] } :: p441_0
def p441_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p441_0
#guard selectOwnedDeclaration p441_1 "L" == .property 1
#guard elaboratesToParameter p441_1 "L" == false
#guard selectOwnedDeclaration p441_2 "a" == .parameter 0
#guard elaboratesToParameter p441_2 "a" == true
#guard selectOwnedDeclaration p441_2 "b" == .parameter 0
#guard elaboratesToParameter p441_2 "b" == true
#guard selectOwnedDeclaration p441_0 "map" == .property 1
#guard elaboratesToParameter p441_0 "map" == false
#guard selectOwnedDeclaration p441_0 "L" == .property 0 -- x3
#guard elaboratesToParameter p441_0 "L" == false -- x3
#guard selectOwnedDeclaration p441_0 "filter" == .property 1
#guard elaboratesToParameter p441_0 "filter" == false
#guard selectOwnedDeclaration p441_0 "reduce" == .property 1 -- x2
#guard elaboratesToParameter p441_0 "reduce" == false -- x2
#guard selectOwnedDeclaration p441_0 "Add" == .property 0
#guard elaboratesToParameter p441_0 "Add" == false

-- spec/take-family-tutorial: take((1, 2, 3, 4, 5), 3) \n  \n take(((1, 2), (3, 4)), 1) \n  \n range(1, 5).take(2)
def p442_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p442_0 "take" == .property 1 -- x3
#guard elaboratesToParameter p442_0 "take" == false -- x3
#guard selectOwnedDeclaration p442_0 "range" == .property 1
#guard elaboratesToParameter p442_0 "range" == false

-- spec/distinct-family-tutorial: distinct((3, 1, 3, 2, 1, 2)) \n  \n distinct(((1, 2), (1, 2), (3, 4))) \n  \n Values = 3, 1, 3, 2, 1, 2 \n Values.distinct
def p443_0 : List OwnerLevel := { parameters := [], properties := ["Values"] } :: prelude
def p443_1 : List OwnerLevel := { parameters := [], properties := [] } :: p443_0
#guard selectOwnedDeclaration p443_0 "distinct" == .property 1 -- x3
#guard elaboratesToParameter p443_0 "distinct" == false -- x3
#guard selectOwnedDeclaration p443_0 "Values" == .property 0
#guard elaboratesToParameter p443_0 "Values" == false

-- spec/spread-arguments-keep-written-order: Lo = 2 \n Hi = 4 \n range(Lo*, Hi*)
def p444_0 : List OwnerLevel := { parameters := [], properties := ["Lo", "Hi"] } :: prelude
def p444_1 : List OwnerLevel := { parameters := [], properties := [] } :: p444_0
def p444_2 : List OwnerLevel := { parameters := [], properties := [] } :: p444_0
#guard selectOwnedDeclaration p444_0 "range" == .property 1
#guard elaboratesToParameter p444_0 "range" == false
#guard selectOwnedDeclaration p444_0 "Lo" == .property 0
#guard elaboratesToParameter p444_0 "Lo" == false
#guard selectOwnedDeclaration p444_0 "Hi" == .property 0
#guard elaboratesToParameter p444_0 "Hi" == false

-- spec/atoms-list-composition: [1, 2, 3].skip(1).atoms
def p445_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p445_0 "skip" == .property 1
#guard elaboratesToParameter p445_0 "skip" == false
#guard selectOwnedDeclaration p445_0 "atoms" == .property 1
#guard elaboratesToParameter p445_0 "atoms" == false

-- spec/atoms-no-truthiness: if(atoms((1, [2])), 10, 20)
def p446_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p446_0 "if" == .property 1
#guard elaboratesToParameter p446_0 "if" == false
#guard selectOwnedDeclaration p446_0 "atoms" == .property 1
#guard elaboratesToParameter p446_0 "atoms" == false

-- spec/sum-of-range-collection: sum(range(1, 3))
def p447_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p447_0 "sum" == .property 1
#guard elaboratesToParameter p447_0 "sum" == false
#guard selectOwnedDeclaration p447_0 "range" == .property 1
#guard elaboratesToParameter p447_0 "range" == false

-- spec/count-family: count(()) \n count((())) \n  \n count(range(1, 5)) \n  \n count((10, 20, 30)) \n  \n count((3, 4, range(1, 5)*, 7)) \n  \n count((range(1, 5)*, 7)) \n  \n count(((1, 2), (3, 4))) \n  \n Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5) \n (Data[0]).count
def p448_0 : List OwnerLevel := { parameters := [], properties := ["Data"] } :: prelude
def p448_1 : List OwnerLevel := { parameters := [], properties := [] } :: p448_0
#guard selectOwnedDeclaration p448_0 "count" == .property 1 -- x8
#guard elaboratesToParameter p448_0 "count" == false -- x8
#guard selectOwnedDeclaration p448_0 "range" == .property 1 -- x3
#guard elaboratesToParameter p448_0 "range" == false -- x3
#guard selectOwnedDeclaration p448_0 "Data" == .property 0
#guard elaboratesToParameter p448_0 "Data" == false

-- spec/count-dotcount-agree: T = (1, 2, 3) \n T.count \n  \n A = 1, 2, 3 \n A.count \n  \n count(A)
def p449_0 : List OwnerLevel := { parameters := [], properties := ["T", "A"] } :: prelude
def p449_1 : List OwnerLevel := { parameters := [], properties := [] } :: p449_0
def p449_2 : List OwnerLevel := { parameters := [], properties := [] } :: p449_0
#guard selectOwnedDeclaration p449_0 "T" == .property 0
#guard elaboratesToParameter p449_0 "T" == false
#guard selectOwnedDeclaration p449_0 "count" == .property 1 -- x3
#guard elaboratesToParameter p449_0 "count" == false -- x3
#guard selectOwnedDeclaration p449_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p449_0 "A" == false -- x2

-- spec/if-value-boundary: X = 1, 2, 3 \n if(true, X, X)
def p450_0 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p450_1 : List OwnerLevel := { parameters := [], properties := [] } :: p450_0
#guard selectOwnedDeclaration p450_0 "if" == .property 1
#guard elaboratesToParameter p450_0 "if" == false
#guard selectOwnedDeclaration p450_0 "X" == .property 0 -- x2
#guard elaboratesToParameter p450_0 "X" == false -- x2

-- spec/reduce-accumulates-value: Append(item, (*history)) = (history*, item) \n reduce((2, 3, 4), Append, (0, 1))
def p451_0 : List OwnerLevel := { parameters := [], properties := ["Append"] } :: prelude
def p451_1 : List OwnerLevel := { parameters := ["item", "history"], properties := [] } :: p451_0
#guard selectOwnedDeclaration p451_1 "history" == .parameter 0
#guard elaboratesToParameter p451_1 "history" == true
#guard selectOwnedDeclaration p451_1 "item" == .parameter 0
#guard elaboratesToParameter p451_1 "item" == true
#guard selectOwnedDeclaration p451_0 "reduce" == .property 1
#guard elaboratesToParameter p451_0 "reduce" == false
#guard selectOwnedDeclaration p451_0 "Append" == .property 0
#guard elaboratesToParameter p451_0 "Append" == false

-- spec/reduce-empty-initial-is-one-value: R(x, acc) = acc + x \n Init = 1, 2 \n reduce((), R, Init)
def p452_0 : List OwnerLevel := { parameters := [], properties := ["Init", "R"] } :: prelude
def p452_1 : List OwnerLevel := { parameters := [], properties := [] } :: p452_0
def p452_2 : List OwnerLevel := { parameters := ["x", "acc"], properties := [] } :: p452_0
#guard selectOwnedDeclaration p452_2 "acc" == .parameter 0
#guard elaboratesToParameter p452_2 "acc" == true
#guard selectOwnedDeclaration p452_2 "x" == .parameter 0
#guard elaboratesToParameter p452_2 "x" == true
#guard selectOwnedDeclaration p452_0 "reduce" == .property 1
#guard elaboratesToParameter p452_0 "reduce" == false
#guard selectOwnedDeclaration p452_0 "R" == .property 0
#guard elaboratesToParameter p452_0 "R" == false
#guard selectOwnedDeclaration p452_0 "Init" == .property 0
#guard elaboratesToParameter p452_0 "Init" == false

-- spec/index-selects-atom: Nums = 10, 20, 30, 40, 50 \n  \n # Select the third value (index 2): \n Nums[2]
def p453_0 : List OwnerLevel := { parameters := [], properties := ["Nums"] } :: prelude
def p453_1 : List OwnerLevel := { parameters := [], properties := [] } :: p453_0
#guard selectOwnedDeclaration p453_0 "Nums" == .property 0
#guard elaboratesToParameter p453_0 "Nums" == false

-- spec/index-selects-one-value: Pairs = (1, 2), (3, 4) \n Pairs[0]
def p454_0 : List OwnerLevel := { parameters := [], properties := ["Pairs"] } :: prelude
def p454_1 : List OwnerLevel := { parameters := [], properties := [] } :: p454_0
#guard selectOwnedDeclaration p454_0 "Pairs" == .property 0
#guard elaboratesToParameter p454_0 "Pairs" == false

-- spec/selection-forms-agree: Coll(*xs) = xs \n Pairs = (1, 2), (3, 4) \n first(Pairs).Coll \n Pairs[0].Coll \n (Pairs[0])*.Coll \n Pairs[0].Coll(3)
def p455_0 : List OwnerLevel := { parameters := [], properties := ["Pairs", "Coll"] } :: prelude
def p455_1 : List OwnerLevel := { parameters := [], properties := [] } :: p455_0
def p455_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p455_0
#guard selectOwnedDeclaration p455_2 "xs" == .parameter 0
#guard elaboratesToParameter p455_2 "xs" == true
#guard selectOwnedDeclaration p455_0 "first" == .property 1
#guard elaboratesToParameter p455_0 "first" == false
#guard selectOwnedDeclaration p455_0 "Pairs" == .property 0 -- x4
#guard elaboratesToParameter p455_0 "Pairs" == false -- x4
#guard selectOwnedDeclaration p455_0 "Coll" == .property 0 -- x4
#guard elaboratesToParameter p455_0 "Coll" == false -- x4

-- spec/index-nested-stays-intact: Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8)) \n Bags[0] \n Bags[0][1]
def p456_0 : List OwnerLevel := { parameters := [], properties := ["Bags"] } :: prelude
def p456_1 : List OwnerLevel := { parameters := [], properties := [] } :: p456_0
#guard selectOwnedDeclaration p456_0 "Bags" == .property 0 -- x2
#guard elaboratesToParameter p456_0 "Bags" == false -- x2

-- spec/variadic-selection-several-values: Data = 10, 20, 30 \n Data[2, 0, 2]
-- the same levels and decisions, 1 more:
--   spec/variadic-selection-bracket-on-a-later-line-is-a-list
def p457_0 : List OwnerLevel := { parameters := [], properties := ["Data"] } :: prelude
def p457_1 : List OwnerLevel := { parameters := [], properties := [] } :: p457_0
#guard selectOwnedDeclaration p457_0 "Data" == .property 0
#guard elaboratesToParameter p457_0 "Data" == false

-- spec/variadic-selection-keeps-empty-values: X = ((), [], 1) \n X[0, 1]
def p458_0 : List OwnerLevel := { parameters := [], properties := ["X"] } :: prelude
def p458_1 : List OwnerLevel := { parameters := [], properties := [] } :: p458_0
#guard selectOwnedDeclaration p458_0 "X" == .property 0
#guard elaboratesToParameter p458_0 "X" == false

-- spec/variadic-selection-has-no-callable-identity: K = 5 \n Apply(f) = f() \n Apply([K][0])
def p459_0 : List OwnerLevel := { parameters := [], properties := ["K", "Apply"] } :: prelude
def p459_1 : List OwnerLevel := { parameters := [], properties := [] } :: p459_0
def p459_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p459_0
#guard selectOwnedDeclaration p459_2 "f" == .parameter 0
#guard elaboratesToParameter p459_2 "f" == true
#guard selectOwnedDeclaration p459_0 "Apply" == .property 0
#guard elaboratesToParameter p459_0 "Apply" == false
#guard selectOwnedDeclaration p459_0 "K" == .property 0
#guard elaboratesToParameter p459_0 "K" == false

-- spec/line-final-star-in-definition-continues: A = 2 \n X = A * \n 3 \n X
def p460_0 : List OwnerLevel := { parameters := [], properties := ["A", "X"] } :: prelude
def p460_1 : List OwnerLevel := { parameters := [], properties := [] } :: p460_0
def p460_2 : List OwnerLevel := { parameters := [], properties := [] } :: p460_0
#guard selectOwnedDeclaration p460_2 "A" == .property 1
#guard elaboratesToParameter p460_2 "A" == false
#guard selectOwnedDeclaration p460_0 "X" == .property 0
#guard elaboratesToParameter p460_0 "X" == false

-- spec/grace-on-bound-name-rejected: X = 1 \n K = ~X + 2 \n K
def p461_0 : List OwnerLevel := { parameters := [], properties := ["X", "K"] } :: prelude
def p461_1 : List OwnerLevel := { parameters := [], properties := [] } :: p461_0
def p461_2 : List OwnerLevel := { parameters := [], properties := [] } :: p461_0
#guard selectOwnedDeclaration p461_2 "X" == .property 1
#guard elaboratesToParameter p461_2 "X" == false
#guard selectOwnedDeclaration p461_0 "K" == .property 0
#guard elaboratesToParameter p461_0 "K" == false

-- spec/grace-under-explicit-list-rejected: K(b, a) = b, ~a \n K(1, 2)
def p462_0 : List OwnerLevel := { parameters := [], properties := ["K"] } :: prelude
def p462_1 : List OwnerLevel := { parameters := ["b", "a"], properties := [] } :: p462_0
#guard selectOwnedDeclaration p462_1 "b" == .parameter 0
#guard elaboratesToParameter p462_1 "b" == true
#guard selectOwnedDeclaration p462_1 "a" == .parameter 0
#guard elaboratesToParameter p462_1 "a" == true
#guard selectOwnedDeclaration p462_0 "K" == .property 0
#guard elaboratesToParameter p462_0 "K" == false

-- spec/grace-in-branch-deconstruction-rejected: F(0) = 0 \n F(n) = { \n     a, b = (~n, 1) \n     a + b \n } \n F(5)
def p463_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p463_1 : List OwnerLevel := { parameters := [], properties := [] } :: p463_0
def p463_2 : List OwnerLevel := { parameters := ["n"], properties := ["$deconstruct$0", "a", "b"] } :: p463_0
def p463_3 : List OwnerLevel := { parameters := [], properties := [] } :: p463_2
def p463_4 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p463_3
def p463_5 : List OwnerLevel := { parameters := [], properties := [] } :: p463_2
def p463_6 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p463_5
#guard selectOwnedDeclaration p463_2 "n" == .parameter 0
#guard elaboratesToParameter p463_2 "n" == true
#guard selectOwnedDeclaration p463_4 "a" == .parameter 0
#guard elaboratesToParameter p463_4 "a" == true
#guard selectOwnedDeclaration p463_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p463_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p463_6 "b" == .parameter 0
#guard elaboratesToParameter p463_6 "b" == true
#guard selectOwnedDeclaration p463_5 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p463_5 "$deconstruct$0" == false
#guard selectOwnedDeclaration p463_2 "a" == .property 0
#guard elaboratesToParameter p463_2 "a" == false
#guard selectOwnedDeclaration p463_2 "b" == .property 0
#guard elaboratesToParameter p463_2 "b" == false
#guard selectOwnedDeclaration p463_0 "F" == .property 0
#guard elaboratesToParameter p463_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/grace-in-branch-nested-block-belongs-to-the-block: Apply(f) = f(1, 10) \n F(0) = Apply({ y - ~x }) \n F(0)
def p464_0 : List OwnerLevel := { parameters := [], properties := ["Apply", "F"] } :: prelude
def p464_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p464_0
def p464_2 : List OwnerLevel := { parameters := [], properties := [] } :: p464_0
def p464_3 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p464_2
#guard selectOwnedDeclaration p464_1 "f" == .parameter 0
#guard elaboratesToParameter p464_1 "f" == true
#guard selectOwnedDeclaration p464_2 "Apply" == .property 1
#guard elaboratesToParameter p464_2 "Apply" == false
#guard selectOwnedDeclaration p464_3 "y" == .parameter 0
#guard elaboratesToParameter p464_3 "y" == true
#guard selectOwnedDeclaration p464_3 "x" == .parameter 0
#guard elaboratesToParameter p464_3 "x" == true
#guard selectOwnedDeclaration p464_0 "F" == .property 0
#guard elaboratesToParameter p464_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0)] == none -- family F

-- spec/grace-saturation-is-valid: F = ~x + 1 \n A = p - q \n G = A - z~ \n H = ~a + b * 10 \n F(3), G(1, 2, 3), H(1, 2)
def p465_0 : List OwnerLevel := { parameters := [], properties := ["F", "A", "G", "H"] } :: prelude
def p465_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p465_0
def p465_2 : List OwnerLevel := { parameters := ["p", "q"], properties := [] } :: p465_0
def p465_3 : List OwnerLevel := { parameters := ["z"], properties := [], forwarded := ["p", "q"] } :: p465_0
def p465_4 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p465_0
#guard selectOwnedDeclaration p465_1 "x" == .parameter 0
#guard elaboratesToParameter p465_1 "x" == true
#guard selectOwnedDeclaration p465_2 "p" == .parameter 0
#guard elaboratesToParameter p465_2 "p" == true
#guard selectOwnedDeclaration p465_2 "q" == .parameter 0
#guard elaboratesToParameter p465_2 "q" == true
#guard selectOwnedDeclaration p465_3 "A" == .property 1
#guard elaboratesToParameter p465_3 "A" == false
#guard selectOwnedDeclaration p465_3 "z" == .parameter 0
#guard elaboratesToParameter p465_3 "z" == true
#guard selectOwnedDeclaration p465_4 "a" == .parameter 0
#guard elaboratesToParameter p465_4 "a" == true
#guard selectOwnedDeclaration p465_4 "b" == .parameter 0
#guard elaboratesToParameter p465_4 "b" == true
#guard selectOwnedDeclaration p465_0 "F" == .property 0
#guard elaboratesToParameter p465_0 "F" == false
#guard selectOwnedDeclaration p465_0 "G" == .property 0
#guard elaboratesToParameter p465_0 "G" == false
#guard selectOwnedDeclaration p465_0 "H" == .property 0
#guard elaboratesToParameter p465_0 "H" == false

-- spec/grace-on-branch-binder-in-nested-block-rejected: Apply(f) = f(1) \n F(0) = 0 \n F(n) = Apply({ x - ~n }) \n F(1)
def p466_0 : List OwnerLevel := { parameters := [], properties := ["Apply", "F"] } :: prelude
def p466_1 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p466_0
def p466_2 : List OwnerLevel := { parameters := [], properties := [] } :: p466_0
def p466_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p466_0
def p466_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p466_3
#guard selectOwnedDeclaration p466_1 "f" == .parameter 0
#guard elaboratesToParameter p466_1 "f" == true
#guard selectOwnedDeclaration p466_3 "Apply" == .property 1
#guard elaboratesToParameter p466_3 "Apply" == false
#guard selectOwnedDeclaration p466_4 "x" == .parameter 0
#guard elaboratesToParameter p466_4 "x" == true
#guard selectOwnedDeclaration p466_4 "n" == .parameter 1
#guard elaboratesToParameter p466_4 "n" == true
#guard selectOwnedDeclaration p466_0 "F" == .property 0
#guard elaboratesToParameter p466_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/grace-weights-accumulate: Weighted = a + 10 * b + 100 * ~~c \n  \n Weighted(1, 2, 3)
def p467_0 : List OwnerLevel := { parameters := [], properties := ["Weighted"] } :: prelude
def p467_1 : List OwnerLevel := { parameters := ["c", "a", "b"], properties := [] } :: p467_0
#guard selectOwnedDeclaration p467_1 "a" == .parameter 0
#guard elaboratesToParameter p467_1 "a" == true
#guard selectOwnedDeclaration p467_1 "b" == .parameter 0
#guard elaboratesToParameter p467_1 "b" == true
#guard selectOwnedDeclaration p467_1 "c" == .parameter 0
#guard elaboratesToParameter p467_1 "c" == true
#guard selectOwnedDeclaration p467_0 "Weighted" == .property 0
#guard elaboratesToParameter p467_0 "Weighted" == false

-- spec/grace-front-first-movement: A = s * 100 + ~x * 10 + ~y \n B = s~ * 100 + x~ * 10 + y \n C = a * 100 + b~ * 10 + ~~c \n D = a~ * 100 + b * 10 + ~c \n E = ~a * 100 + b * 10 + ~~c \n A(1, 2, 3), B(1, 2, 3), C(1, 2, 3), D(1, 2, 3), E(1, 2, 3)
def p468_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C", "D", "E"] } :: prelude
def p468_1 : List OwnerLevel := { parameters := ["x", "y", "s"], properties := [] } :: p468_0
def p468_2 : List OwnerLevel := { parameters := ["y", "s", "x"], properties := [] } :: p468_0
def p468_3 : List OwnerLevel := { parameters := ["c", "a", "b"], properties := [] } :: p468_0
def p468_4 : List OwnerLevel := { parameters := ["b", "c", "a"], properties := [] } :: p468_0
def p468_5 : List OwnerLevel := { parameters := ["a", "c", "b"], properties := [] } :: p468_0
#guard selectOwnedDeclaration p468_1 "s" == .parameter 0
#guard elaboratesToParameter p468_1 "s" == true
#guard selectOwnedDeclaration p468_1 "x" == .parameter 0
#guard elaboratesToParameter p468_1 "x" == true
#guard selectOwnedDeclaration p468_1 "y" == .parameter 0
#guard elaboratesToParameter p468_1 "y" == true
#guard selectOwnedDeclaration p468_2 "s" == .parameter 0
#guard elaboratesToParameter p468_2 "s" == true
#guard selectOwnedDeclaration p468_2 "x" == .parameter 0
#guard elaboratesToParameter p468_2 "x" == true
#guard selectOwnedDeclaration p468_2 "y" == .parameter 0
#guard elaboratesToParameter p468_2 "y" == true
#guard selectOwnedDeclaration p468_3 "a" == .parameter 0
#guard elaboratesToParameter p468_3 "a" == true
#guard selectOwnedDeclaration p468_3 "b" == .parameter 0
#guard elaboratesToParameter p468_3 "b" == true
#guard selectOwnedDeclaration p468_3 "c" == .parameter 0
#guard elaboratesToParameter p468_3 "c" == true
#guard selectOwnedDeclaration p468_4 "a" == .parameter 0
#guard elaboratesToParameter p468_4 "a" == true
#guard selectOwnedDeclaration p468_4 "b" == .parameter 0
#guard elaboratesToParameter p468_4 "b" == true
#guard selectOwnedDeclaration p468_4 "c" == .parameter 0
#guard elaboratesToParameter p468_4 "c" == true
#guard selectOwnedDeclaration p468_5 "a" == .parameter 0
#guard elaboratesToParameter p468_5 "a" == true
#guard selectOwnedDeclaration p468_5 "b" == .parameter 0
#guard elaboratesToParameter p468_5 "b" == true
#guard selectOwnedDeclaration p468_5 "c" == .parameter 0
#guard elaboratesToParameter p468_5 "c" == true
#guard selectOwnedDeclaration p468_0 "A" == .property 0
#guard elaboratesToParameter p468_0 "A" == false
#guard selectOwnedDeclaration p468_0 "B" == .property 0
#guard elaboratesToParameter p468_0 "B" == false
#guard selectOwnedDeclaration p468_0 "C" == .property 0
#guard elaboratesToParameter p468_0 "C" == false
#guard selectOwnedDeclaration p468_0 "D" == .property 0
#guard elaboratesToParameter p468_0 "D" == false
#guard selectOwnedDeclaration p468_0 "E" == .property 0
#guard elaboratesToParameter p468_0 "E" == false

-- spec/grace-prefix-marker-led-row: K = { \n   a \n   ~b \n } \n K(10, 20)
def p469_0 : List OwnerLevel := { parameters := [], properties := ["K"] } :: prelude
def p469_1 : List OwnerLevel := { parameters := ["b", "a"], properties := [] } :: p469_0
#guard selectOwnedDeclaration p469_1 "a" == .parameter 0
#guard elaboratesToParameter p469_1 "a" == true
#guard selectOwnedDeclaration p469_1 "b" == .parameter 0
#guard elaboratesToParameter p469_1 "b" == true
#guard selectOwnedDeclaration p469_0 "K" == .property 0
#guard elaboratesToParameter p469_0 "K" == false

-- spec/adjacency-call-across-space: Add(a, b) = a + b \n  \n Add(1, 2)    # 3 \n Add (1, 2)   # the same call, 3
def p470_0 : List OwnerLevel := { parameters := [], properties := ["Add"] } :: prelude
def p470_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p470_0
#guard selectOwnedDeclaration p470_1 "a" == .parameter 0
#guard elaboratesToParameter p470_1 "a" == true
#guard selectOwnedDeclaration p470_1 "b" == .parameter 0
#guard elaboratesToParameter p470_1 "b" == true
#guard selectOwnedDeclaration p470_0 "Add" == .property 0 -- x2
#guard elaboratesToParameter p470_0 "Add" == false -- x2

-- spec/newline-ends-property-body: P = 1 \n 2
def p471_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p471_1 : List OwnerLevel := { parameters := [], properties := [] } :: p471_0

-- spec/spread-binds-before-list: X(*vals) = vals.count \n b = (1, 2) \n X(7, b*)
def p472_0 : List OwnerLevel := { parameters := [], properties := ["b", "X"] } :: prelude
def p472_1 : List OwnerLevel := { parameters := [], properties := [] } :: p472_0
def p472_2 : List OwnerLevel := { parameters := ["vals"], properties := [] } :: p472_0
#guard selectOwnedDeclaration p472_2 "vals" == .parameter 0
#guard elaboratesToParameter p472_2 "vals" == true
#guard selectOwnedDeclaration p472_2 "count" == .property 2
#guard elaboratesToParameter p472_2 "count" == false
#guard selectOwnedDeclaration p472_0 "X" == .property 0
#guard elaboratesToParameter p472_0 "X" == false
#guard selectOwnedDeclaration p472_0 "b" == .property 0
#guard elaboratesToParameter p472_0 "b" == false

-- spec/dot-chain-continuation: (1, 2, 3) \n .map { n * 2 } \n .sum
def p473_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p473_1 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p473_0
#guard selectOwnedDeclaration p473_0 "map" == .property 1
#guard elaboratesToParameter p473_0 "map" == false
#guard selectOwnedDeclaration p473_1 "n" == .parameter 0
#guard elaboratesToParameter p473_1 "n" == true
#guard selectOwnedDeclaration p473_0 "sum" == .property 1
#guard elaboratesToParameter p473_0 "sum" == false

-- spec/arity-too-many-arguments: KeepFirst(a, b) = a \n KeepFirst(42, 999, 1)
def p474_0 : List OwnerLevel := { parameters := [], properties := ["KeepFirst"] } :: prelude
def p474_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p474_0
#guard selectOwnedDeclaration p474_1 "a" == .parameter 0
#guard elaboratesToParameter p474_1 "a" == true
#guard selectOwnedDeclaration p474_0 "KeepFirst" == .property 0
#guard elaboratesToParameter p474_0 "KeepFirst" == false

-- spec/spread-preserves-nested-missing-output: G = { \n     public X = 1 \n } \n H = G + 1 \n H*
def p475_0 : List OwnerLevel := { parameters := [], properties := ["G", "H"] } :: prelude
def p475_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p475_0
def p475_2 : List OwnerLevel := { parameters := [], properties := [] } :: p475_1
def p475_3 : List OwnerLevel := { parameters := [], properties := [] } :: p475_0
#guard selectOwnedDeclaration p475_3 "G" == .property 1
#guard elaboratesToParameter p475_3 "G" == false
#guard selectOwnedDeclaration p475_0 "H" == .property 0
#guard elaboratesToParameter p475_0 "H" == false

-- spec/missing-output-as-builtin-arg: count({})
def p476_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p476_1 : List OwnerLevel := { parameters := [], properties := [] } :: p476_0
#guard selectOwnedDeclaration p476_0 "count" == .property 1
#guard elaboratesToParameter p476_0 "count" == false

-- spec/output-less-argument-is-not-an-omitted-argument: Coll(*xs) = xs \n Coll({})
def p477_0 : List OwnerLevel := { parameters := [], properties := ["Coll"] } :: prelude
def p477_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p477_0
def p477_2 : List OwnerLevel := { parameters := [], properties := [] } :: p477_0
#guard selectOwnedDeclaration p477_1 "xs" == .parameter 0
#guard elaboratesToParameter p477_1 "xs" == true
#guard selectOwnedDeclaration p477_0 "Coll" == .property 0
#guard elaboratesToParameter p477_0 "Coll" == false

-- spec/argument-value-outcome-is-final: Plus(f, x) = f + x \n Plus({x + 1}, 5)
def p478_0 : List OwnerLevel := { parameters := [], properties := ["Plus"] } :: prelude
def p478_1 : List OwnerLevel := { parameters := ["f", "x"], properties := [] } :: p478_0
def p478_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p478_0
#guard selectOwnedDeclaration p478_1 "f" == .parameter 0
#guard elaboratesToParameter p478_1 "f" == true
#guard selectOwnedDeclaration p478_1 "x" == .parameter 0
#guard elaboratesToParameter p478_1 "x" == true
#guard selectOwnedDeclaration p478_0 "Plus" == .property 0
#guard elaboratesToParameter p478_0 "Plus" == false
#guard selectOwnedDeclaration p478_2 "x" == .parameter 0
#guard elaboratesToParameter p478_2 "x" == true

-- spec/invoking-slot-without-callable-is-not-an-algorithm: map([1, 2], 5)
def p479_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p479_0 "map" == .property 1
#guard elaboratesToParameter p479_0 "map" == false

-- spec/zero-parameter-callable-in-invoking-slot-is-arity: A = 7 \n map([1, 2], A)
def p480_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p480_1 : List OwnerLevel := { parameters := [], properties := [] } :: p480_0
#guard selectOwnedDeclaration p480_0 "map" == .property 1
#guard elaboratesToParameter p480_0 "map" == false
#guard selectOwnedDeclaration p480_0 "A" == .property 0
#guard elaboratesToParameter p480_0 "A" == false

-- spec/spread-arguments-fail-left-to-right: P = 1 / 0 \n Q = 'x' + 1 \n range(P*, Q*)
def p481_0 : List OwnerLevel := { parameters := [], properties := ["P", "Q"] } :: prelude
def p481_1 : List OwnerLevel := { parameters := [], properties := [] } :: p481_0
def p481_2 : List OwnerLevel := { parameters := [], properties := [] } :: p481_0
#guard selectOwnedDeclaration p481_0 "range" == .property 1
#guard elaboratesToParameter p481_0 "range" == false
#guard selectOwnedDeclaration p481_0 "P" == .property 0
#guard elaboratesToParameter p481_0 "P" == false
#guard selectOwnedDeclaration p481_0 "Q" == .property 0
#guard elaboratesToParameter p481_0 "Q" == false

-- spec/unresolved-implicit-parameter: Nope
def p482_0 : List OwnerLevel := { parameters := ["Nope"], properties := [] } :: prelude
#guard selectOwnedDeclaration p482_0 "Nope" == .parameter 0
#guard elaboratesToParameter p482_0 "Nope" == true

-- spec/list-index-nested-element-stays-exact: Rows = [[1, 2], [3, 4]] \n Rows[0] \n Rows[0][1]
def p483_0 : List OwnerLevel := { parameters := [], properties := ["Rows"] } :: prelude
def p483_1 : List OwnerLevel := { parameters := [], properties := [] } :: p483_0
#guard selectOwnedDeclaration p483_0 "Rows" == .property 0 -- x2
#guard elaboratesToParameter p483_0 "Rows" == false -- x2

-- spec/list-spread-capture: A = [1, 2, 3] \n  \n x = A \n y = (A*) \n  \n x \n y
def p484_0 : List OwnerLevel := { parameters := [], properties := ["A", "x", "y"] } :: prelude
def p484_1 : List OwnerLevel := { parameters := [], properties := [] } :: p484_0
def p484_2 : List OwnerLevel := { parameters := [], properties := [] } :: p484_0
def p484_3 : List OwnerLevel := { parameters := [], properties := [] } :: p484_0
#guard selectOwnedDeclaration p484_2 "A" == .property 1
#guard elaboratesToParameter p484_2 "A" == false
#guard selectOwnedDeclaration p484_3 "A" == .property 1
#guard elaboratesToParameter p484_3 "A" == false
#guard selectOwnedDeclaration p484_0 "x" == .property 0
#guard elaboratesToParameter p484_0 "x" == false
#guard selectOwnedDeclaration p484_0 "y" == .property 0
#guard elaboratesToParameter p484_0 "y" == false

-- spec/list-spread-edges: A = [] \n B = [7] \n C = [[7]] \n  \n A*, \n B*, \n C*, 997
def p485_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C"] } :: prelude
def p485_1 : List OwnerLevel := { parameters := [], properties := [] } :: p485_0
def p485_2 : List OwnerLevel := { parameters := [], properties := [] } :: p485_0
def p485_3 : List OwnerLevel := { parameters := [], properties := [] } :: p485_0
#guard selectOwnedDeclaration p485_0 "A" == .property 0
#guard elaboratesToParameter p485_0 "A" == false
#guard selectOwnedDeclaration p485_0 "B" == .property 0
#guard elaboratesToParameter p485_0 "B" == false
#guard selectOwnedDeclaration p485_0 "C" == .property 0
#guard elaboratesToParameter p485_0 "C" == false

-- spec/list-elements-preserve-boundaries: A = [1, 2] \n B = [3, 4] \n  \n [A, B] \n [A*, B*] \n [A, B*]
def p486_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p486_1 : List OwnerLevel := { parameters := [], properties := [] } :: p486_0
def p486_2 : List OwnerLevel := { parameters := [], properties := [] } :: p486_0
#guard selectOwnedDeclaration p486_0 "A" == .property 0 -- x3
#guard elaboratesToParameter p486_0 "A" == false -- x3
#guard selectOwnedDeclaration p486_0 "B" == .property 0 -- x3
#guard elaboratesToParameter p486_0 "B" == false -- x3

-- spec/list-written-slot-reifies-selection: S = ((1, 2), (3, 4)) \n  \n [S[0], 5] \n [S[0]*, 5]
def p487_0 : List OwnerLevel := { parameters := [], properties := ["S"] } :: prelude
def p487_1 : List OwnerLevel := { parameters := [], properties := [] } :: p487_0
#guard selectOwnedDeclaration p487_0 "S" == .property 0 -- x2
#guard elaboratesToParameter p487_0 "S" == false -- x2

-- spec/list-call-boundary: F(a, b, c) = a + b + c \n One(x) = 7 \n  \n A = [1, 2, 3] \n  \n One(A) \n F(A*)
def p488_0 : List OwnerLevel := { parameters := [], properties := ["A", "F", "One"] } :: prelude
def p488_1 : List OwnerLevel := { parameters := [], properties := [] } :: p488_0
def p488_2 : List OwnerLevel := { parameters := ["a", "b", "c"], properties := [] } :: p488_0
def p488_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p488_0
#guard selectOwnedDeclaration p488_2 "a" == .parameter 0
#guard elaboratesToParameter p488_2 "a" == true
#guard selectOwnedDeclaration p488_2 "b" == .parameter 0
#guard elaboratesToParameter p488_2 "b" == true
#guard selectOwnedDeclaration p488_2 "c" == .parameter 0
#guard elaboratesToParameter p488_2 "c" == true
#guard selectOwnedDeclaration p488_0 "One" == .property 0
#guard elaboratesToParameter p488_0 "One" == false
#guard selectOwnedDeclaration p488_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p488_0 "A" == false -- x2
#guard selectOwnedDeclaration p488_0 "F" == .property 0
#guard elaboratesToParameter p488_0 "F" == false

-- spec/list-lone-deconstruction: x, y, z = [1, 2, 3] \n  \n x \n y \n z
def p489_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "y", "z"] } :: prelude
def p489_1 : List OwnerLevel := { parameters := [], properties := [] } :: p489_0
def p489_2 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p489_1
def p489_3 : List OwnerLevel := { parameters := [], properties := [] } :: p489_0
def p489_4 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p489_3
def p489_5 : List OwnerLevel := { parameters := [], properties := [] } :: p489_0
def p489_6 : List OwnerLevel := { parameters := ["x", "y", "z"], properties := [] } :: p489_5
#guard selectOwnedDeclaration p489_2 "x" == .parameter 0
#guard elaboratesToParameter p489_2 "x" == true
#guard selectOwnedDeclaration p489_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p489_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p489_4 "y" == .parameter 0
#guard elaboratesToParameter p489_4 "y" == true
#guard selectOwnedDeclaration p489_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p489_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p489_6 "z" == .parameter 0
#guard elaboratesToParameter p489_6 "z" == true
#guard selectOwnedDeclaration p489_5 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p489_5 "$deconstruct$0" == false
#guard selectOwnedDeclaration p489_0 "x" == .property 0
#guard elaboratesToParameter p489_0 "x" == false
#guard selectOwnedDeclaration p489_0 "y" == .property 0
#guard elaboratesToParameter p489_0 "y" == false
#guard selectOwnedDeclaration p489_0 "z" == .property 0
#guard elaboratesToParameter p489_0 "z" == false

-- spec/collecting-binding-exact-list: x, *rest = [1, 2, 3] \n  \n x \n rest
def p490_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "x", "rest"] } :: prelude
def p490_1 : List OwnerLevel := { parameters := [], properties := [] } :: p490_0
def p490_2 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p490_1
def p490_3 : List OwnerLevel := { parameters := [], properties := [] } :: p490_0
def p490_4 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p490_3
#guard selectOwnedDeclaration p490_2 "x" == .parameter 0
#guard elaboratesToParameter p490_2 "x" == true
#guard selectOwnedDeclaration p490_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p490_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p490_4 "rest" == .parameter 0
#guard elaboratesToParameter p490_4 "rest" == true
#guard selectOwnedDeclaration p490_3 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p490_3 "$deconstruct$0" == false
#guard selectOwnedDeclaration p490_0 "x" == .property 0
#guard elaboratesToParameter p490_0 "x" == false
#guard selectOwnedDeclaration p490_0 "rest" == .property 0
#guard elaboratesToParameter p490_0 "rest" == false

-- spec/list-lone-collecting-assignment: *items = [1, 2, 3] \n items
def p491_0 : List OwnerLevel := { parameters := [], properties := ["$deconstruct$0", "items"] } :: prelude
def p491_1 : List OwnerLevel := { parameters := [], properties := [] } :: p491_0
def p491_2 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p491_1
#guard selectOwnedDeclaration p491_2 "items" == .parameter 0
#guard elaboratesToParameter p491_2 "items" == true
#guard selectOwnedDeclaration p491_1 "$deconstruct$0" == .property 1
#guard elaboratesToParameter p491_1 "$deconstruct$0" == false
#guard selectOwnedDeclaration p491_0 "items" == .property 0
#guard elaboratesToParameter p491_0 "items" == false

-- spec/avg-decimal-mean: avg((1, 2))
-- the same levels and decisions, 1 more:
--   spec/avg-is-the-correctly-rounded-exact-mean
def p492_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p492_0 "avg" == .property 1
#guard elaboratesToParameter p492_0 "avg" == false

-- spec/nan-equality-vs-ordering: N = (-2) ^ 0.5 \n N == (-3) ^ 0.5 \n N < 1 \n N <= 1 \n N > 1 \n N >= 1
def p493_0 : List OwnerLevel := { parameters := [], properties := ["N"] } :: prelude
def p493_1 : List OwnerLevel := { parameters := [], properties := [] } :: p493_0
#guard selectOwnedDeclaration p493_0 "N" == .property 0 -- x5
#guard elaboratesToParameter p493_0 "N" == false -- x5

-- spec/native-flat-callback-binding: F(x) = [1, -2].map(abs) \n F(5)
def p494_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p494_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p494_0
#guard selectOwnedDeclaration p494_1 "map" == .property 2
#guard elaboratesToParameter p494_1 "map" == false
#guard selectOwnedDeclaration p494_1 "abs" == .property 2
#guard elaboratesToParameter p494_1 "abs" == false
#guard selectOwnedDeclaration p494_0 "F" == .property 0
#guard elaboratesToParameter p494_0 "F" == false

-- spec/callable-argument-parameter-shadowing: A = q + 1 \n Add1(x) = x + 1 \n F(x) = Add1(A) \n  \n F(7)
def p495_0 : List OwnerLevel := { parameters := [], properties := ["A", "Add1", "F"] } :: prelude
def p495_1 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p495_0
def p495_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p495_0
def p495_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p495_0
#guard selectOwnedDeclaration p495_1 "q" == .parameter 0
#guard elaboratesToParameter p495_1 "q" == true
#guard selectOwnedDeclaration p495_2 "x" == .parameter 0
#guard elaboratesToParameter p495_2 "x" == true
#guard selectOwnedDeclaration p495_3 "Add1" == .property 1
#guard elaboratesToParameter p495_3 "Add1" == false
#guard selectOwnedDeclaration p495_3 "A" == .property 1
#guard elaboratesToParameter p495_3 "A" == false
#guard selectOwnedDeclaration p495_0 "F" == .property 0
#guard elaboratesToParameter p495_0 "F" == false

-- spec/value-argument-parameter-shadowing: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(f) = f(2) \n     Inner(5) \n } \n  \n Apply(Inc)
def p496_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p496_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p496_0
def p496_2 : List OwnerLevel := { parameters := ["f"], properties := ["Inner"] } :: p496_0
def p496_3 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p496_2
#guard selectOwnedDeclaration p496_1 "x" == .parameter 0
#guard elaboratesToParameter p496_1 "x" == true
#guard selectOwnedDeclaration p496_3 "f" == .parameter 0
#guard elaboratesToParameter p496_3 "f" == true
#guard selectOwnedDeclaration p496_2 "Inner" == .property 0
#guard elaboratesToParameter p496_2 "Inner" == false
#guard selectOwnedDeclaration p496_0 "Apply" == .property 0
#guard elaboratesToParameter p496_0 "Apply" == false
#guard selectOwnedDeclaration p496_0 "Inc" == .property 0
#guard elaboratesToParameter p496_0 "Inc" == false

-- spec/value-parameter-shadowing-through-nested-scope: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(f) = { \n         Local(y) = f(y) \n         Local(2) \n     } \n     Inner(5) \n } \n  \n Apply(Inc)
def p497_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p497_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p497_0
def p497_2 : List OwnerLevel := { parameters := ["f"], properties := ["Inner"] } :: p497_0
def p497_3 : List OwnerLevel := { parameters := ["f"], properties := ["Local"] } :: p497_2
def p497_4 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p497_3
#guard selectOwnedDeclaration p497_1 "x" == .parameter 0
#guard elaboratesToParameter p497_1 "x" == true
#guard selectOwnedDeclaration p497_4 "f" == .parameter 1
#guard elaboratesToParameter p497_4 "f" == true
#guard selectOwnedDeclaration p497_4 "y" == .parameter 0
#guard elaboratesToParameter p497_4 "y" == true
#guard selectOwnedDeclaration p497_3 "Local" == .property 0
#guard elaboratesToParameter p497_3 "Local" == false
#guard selectOwnedDeclaration p497_2 "Inner" == .property 0
#guard elaboratesToParameter p497_2 "Inner" == false
#guard selectOwnedDeclaration p497_0 "Apply" == .property 0
#guard elaboratesToParameter p497_0 "Apply" == false
#guard selectOwnedDeclaration p497_0 "Inc" == .property 0
#guard elaboratesToParameter p497_0 "Inc" == false

-- spec/value-binder-parameter-shadowing: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(0) = 0 \n     Inner(f) = f(2) \n     Inner(5) \n } \n  \n Apply(Inc)
def p498_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p498_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p498_0
def p498_2 : List OwnerLevel := { parameters := ["f"], properties := ["Inner"] } :: p498_0
def p498_3 : List OwnerLevel := { parameters := [], properties := [] } :: p498_2
def p498_4 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p498_2
#guard selectOwnedDeclaration p498_1 "x" == .parameter 0
#guard elaboratesToParameter p498_1 "x" == true
#guard selectOwnedDeclaration p498_4 "f" == .parameter 0
#guard elaboratesToParameter p498_4 "f" == true
#guard selectOwnedDeclaration p498_2 "Inner" == .property 0
#guard elaboratesToParameter p498_2 "Inner" == false
#guard selectOwnedDeclaration p498_0 "Apply" == .property 0
#guard elaboratesToParameter p498_0 "Apply" == false
#guard selectOwnedDeclaration p498_0 "Inc" == .property 0
#guard elaboratesToParameter p498_0 "Inc" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "f")] == some [.capture { name := "f" }] -- family Inner

-- spec/ancestor-callable-visible-without-same-named-parameter: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(x) = f(x) \n     Inner(5) \n } \n  \n Apply(Inc)
def p499_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "Apply"] } :: prelude
def p499_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p499_0
def p499_2 : List OwnerLevel := { parameters := ["f"], properties := ["Inner"] } :: p499_0
def p499_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p499_2
#guard selectOwnedDeclaration p499_1 "x" == .parameter 0
#guard elaboratesToParameter p499_1 "x" == true
#guard selectOwnedDeclaration p499_3 "f" == .parameter 1
#guard elaboratesToParameter p499_3 "f" == true
#guard selectOwnedDeclaration p499_3 "x" == .parameter 0
#guard elaboratesToParameter p499_3 "x" == true
#guard selectOwnedDeclaration p499_2 "Inner" == .property 0
#guard elaboratesToParameter p499_2 "Inner" == false
#guard selectOwnedDeclaration p499_0 "Apply" == .property 0
#guard elaboratesToParameter p499_0 "Apply" == false
#guard selectOwnedDeclaration p499_0 "Inc" == .property 0
#guard elaboratesToParameter p499_0 "Inc" == false

-- spec/ownership-same-owner-nested-reference-rejected: Outer(v) = { \n     v = 5 \n     Inner = v + 1 \n     Inner \n } \n Outer(7)
def p500_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p500_1 : List OwnerLevel := { parameters := ["v"], properties := ["v", "Inner"] } :: p500_0
def p500_2 : List OwnerLevel := { parameters := [], properties := [] } :: p500_1
def p500_3 : List OwnerLevel := { parameters := [], properties := [] } :: p500_1
#guard selectOwnedDeclaration p500_3 "v" == .parameter 1
#guard elaboratesToParameter p500_3 "v" == true
#guard selectOwnedDeclaration p500_1 "Inner" == .property 0
#guard elaboratesToParameter p500_1 "Inner" == false
#guard selectOwnedDeclaration p500_0 "Outer" == .property 0
#guard elaboratesToParameter p500_0 "Outer" == false

-- spec/ownership-same-owner-later-property-rejected: Outer(v) = { \n     Inner = v + 1 \n     v = 5 \n     Inner \n } \n Outer(7)
def p501_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p501_1 : List OwnerLevel := { parameters := ["v"], properties := ["Inner", "v"] } :: p501_0
def p501_2 : List OwnerLevel := { parameters := [], properties := [] } :: p501_1
def p501_3 : List OwnerLevel := { parameters := [], properties := [] } :: p501_1
#guard selectOwnedDeclaration p501_2 "v" == .parameter 1
#guard elaboratesToParameter p501_2 "v" == true
#guard selectOwnedDeclaration p501_1 "Inner" == .property 0
#guard elaboratesToParameter p501_1 "Inner" == false
#guard selectOwnedDeclaration p501_0 "Outer" == .property 0
#guard elaboratesToParameter p501_0 "Outer" == false

-- spec/ownership-branch-binder-property-collision: F(0) = 0 \n F(v) = { \n     v = 5 \n     Inner = v + 1 \n     Inner \n } \n F(7)
def p502_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p502_1 : List OwnerLevel := { parameters := [], properties := [] } :: p502_0
def p502_2 : List OwnerLevel := { parameters := ["v"], properties := ["v", "Inner"] } :: p502_0
def p502_3 : List OwnerLevel := { parameters := [], properties := [] } :: p502_2
def p502_4 : List OwnerLevel := { parameters := [], properties := [] } :: p502_2
#guard selectOwnedDeclaration p502_4 "v" == .parameter 1
#guard elaboratesToParameter p502_4 "v" == true
#guard selectOwnedDeclaration p502_2 "Inner" == .property 0
#guard elaboratesToParameter p502_2 "Inner" == false
#guard selectOwnedDeclaration p502_0 "F" == .property 0
#guard elaboratesToParameter p502_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "v")] == some [.capture { name := "v" }] -- family F

-- spec/ownership-lifted-parameter-property-collision: Need(v) = v \n Outer = { v = 5 \n Inner = v \n Need + Inner } \n Outer(7)
def p503_0 : List OwnerLevel := { parameters := [], properties := ["Outer", "Need"] } :: prelude
def p503_1 : List OwnerLevel := { parameters := [], properties := ["v", "Inner"], forwarded := ["v"] } :: p503_0
def p503_2 : List OwnerLevel := { parameters := [], properties := [] } :: p503_1
def p503_3 : List OwnerLevel := { parameters := [], properties := [] } :: p503_1
def p503_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p503_0
#guard selectOwnedDeclaration p503_3 "v" == .property 1
#guard elaboratesToParameter p503_3 "v" == false
#guard selectOwnedDeclaration p503_1 "Need" == .property 1
#guard elaboratesToParameter p503_1 "Need" == false
#guard selectOwnedDeclaration p503_1 "Inner" == .property 0
#guard elaboratesToParameter p503_1 "Inner" == false
#guard selectOwnedDeclaration p503_4 "v" == .parameter 0
#guard elaboratesToParameter p503_4 "v" == true
#guard selectOwnedDeclaration p503_0 "Outer" == .property 0
#guard elaboratesToParameter p503_0 "Outer" == false

-- spec/forwarded-parameter-leaves-an-opened-reference: Lib = { public v = 99 } \n Outer = { \n     Inner = { open Lib \n         v \n     } \n     Need = v \n     Inner + Need \n } \n Outer(7)
def p504_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Outer"] } :: prelude
def p504_1 : List OwnerLevel := { parameters := [], properties := ["v"] } :: p504_0
def p504_2 : List OwnerLevel := { parameters := [], properties := [] } :: p504_1
def p504_3 : List OwnerLevel := { parameters := [], properties := ["Inner", "Need"], forwarded := ["v"] } :: p504_0
def p504_4 : List OwnerLevel := { parameters := [], properties := [] } :: p504_3
def p504_5 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p504_3
#guard selectOwnedDeclaration p504_4 "Lib" == .property 2
#guard openHead? (elaborateOpenHead p504_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p504_4 "v" == .none
#guard elaboratesToParameter p504_4 "v" == false
#guard selectOwnedDeclaration p504_5 "v" == .parameter 0
#guard elaboratesToParameter p504_5 "v" == true
#guard selectOwnedDeclaration p504_3 "Inner" == .property 0
#guard elaboratesToParameter p504_3 "Inner" == false
#guard selectOwnedDeclaration p504_3 "Need" == .property 0
#guard elaboratesToParameter p504_3 "Need" == false
#guard selectOwnedDeclaration p504_0 "Outer" == .property 0
#guard elaboratesToParameter p504_0 "Outer" == false

-- spec/forwarded-parameter-names-nothing-in-a-closed-body: Need(v) = v \n Outer = { F(0) = 0 \n F(n) = v \n F(1) + Need } \n Outer(7)
def p505_0 : List OwnerLevel := { parameters := [], properties := ["Outer", "Need"] } :: prelude
def p505_1 : List OwnerLevel := { parameters := [], properties := ["F"], forwarded := ["v"] } :: p505_0
def p505_2 : List OwnerLevel := { parameters := [], properties := [] } :: p505_1
def p505_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p505_1
def p505_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p505_0
#guard selectOwnedDeclaration p505_3 "v" == .none
#guard elaboratesToParameter p505_3 "v" == false
#guard selectOwnedDeclaration p505_1 "F" == .property 0
#guard elaboratesToParameter p505_1 "F" == false
#guard selectOwnedDeclaration p505_1 "Need" == .property 1
#guard elaboratesToParameter p505_1 "Need" == false
#guard selectOwnedDeclaration p505_4 "v" == .parameter 0
#guard elaboratesToParameter p505_4 "v" == true
#guard selectOwnedDeclaration p505_0 "Outer" == .property 0
#guard elaboratesToParameter p505_0 "Outer" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/forwarding-reuses-a-captured-ancestor-parameter: A = y + 1 \n F(y) = { \n     G = y * 1000 + A \n     H(y) = G \n     H(100) \n } \n F(3)
def p506_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p506_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p506_0
def p506_2 : List OwnerLevel := { parameters := ["y"], properties := ["G", "H"] } :: p506_0
def p506_3 : List OwnerLevel := { parameters := [], properties := [] } :: p506_2
def p506_4 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p506_2
#guard selectOwnedDeclaration p506_1 "y" == .parameter 0
#guard elaboratesToParameter p506_1 "y" == true
#guard selectOwnedDeclaration p506_3 "y" == .parameter 1
#guard elaboratesToParameter p506_3 "y" == true
#guard selectOwnedDeclaration p506_3 "A" == .property 2
#guard elaboratesToParameter p506_3 "A" == false
#guard selectOwnedDeclaration p506_4 "G" == .property 1
#guard elaboratesToParameter p506_4 "G" == false
#guard selectOwnedDeclaration p506_2 "H" == .property 0
#guard elaboratesToParameter p506_2 "H" == false
#guard selectOwnedDeclaration p506_0 "F" == .property 0
#guard elaboratesToParameter p506_0 "F" == false

-- spec/forwarding-never-supplies-a-property-an-open-or-a-builtin: v = 99 \n Need(v) = v \n Outer = Need + 1 \n Outer(7)
def p507_0 : List OwnerLevel := { parameters := [], properties := ["v", "Outer", "Need"] } :: prelude
def p507_1 : List OwnerLevel := { parameters := [], properties := [] } :: p507_0
def p507_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["v"] } :: p507_0
def p507_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p507_0
#guard selectOwnedDeclaration p507_2 "Need" == .property 1
#guard elaboratesToParameter p507_2 "Need" == false
#guard selectOwnedDeclaration p507_3 "v" == .parameter 0
#guard elaboratesToParameter p507_3 "v" == true
#guard selectOwnedDeclaration p507_0 "Outer" == .property 0
#guard elaboratesToParameter p507_0 "Outer" == false

-- spec/forwarding-reused-binding-kind-preserves-values: Target(tag, *items) = items \n Collected(tag, *items) = { \n     G(q) = [Target][0] \n     G(99) \n } \n Fixed(tag, items) = { \n     G(q) = [Target][0] \n     G(99) \n } \n Head(x, *rest) = x + rest.count \n Partial(x) = { \n     H = [Head][0] \n     [H, H(10, 20)] \n } \n [Collected(0, (1, 2), [3], ()), Fixed(0, [(1, 2), [3], ()]), Partial(4)]
def p508_0 : List OwnerLevel := { parameters := [], properties := ["Target", "Collected", "Fixed", "Head", "Partial"] } :: prelude
def p508_1 : List OwnerLevel := { parameters := ["tag", "items"], properties := [] } :: p508_0
def p508_2 : List OwnerLevel := { parameters := ["tag", "items"], properties := ["G"] } :: p508_0
def p508_3 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p508_2
def p508_4 : List OwnerLevel := { parameters := ["tag", "items"], properties := ["G"] } :: p508_0
def p508_5 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p508_4
def p508_6 : List OwnerLevel := { parameters := ["x", "rest"], properties := [] } :: p508_0
def p508_7 : List OwnerLevel := { parameters := ["x"], properties := ["H"] } :: p508_0
def p508_8 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["rest"] } :: p508_7
#guard selectOwnedDeclaration p508_1 "items" == .parameter 0
#guard elaboratesToParameter p508_1 "items" == true
#guard selectOwnedDeclaration p508_3 "Target" == .property 2
#guard elaboratesToParameter p508_3 "Target" == false
#guard selectOwnedDeclaration p508_2 "G" == .property 0
#guard elaboratesToParameter p508_2 "G" == false
#guard selectOwnedDeclaration p508_5 "Target" == .property 2
#guard elaboratesToParameter p508_5 "Target" == false
#guard selectOwnedDeclaration p508_4 "G" == .property 0
#guard elaboratesToParameter p508_4 "G" == false
#guard selectOwnedDeclaration p508_6 "x" == .parameter 0
#guard elaboratesToParameter p508_6 "x" == true
#guard selectOwnedDeclaration p508_6 "rest" == .parameter 0
#guard elaboratesToParameter p508_6 "rest" == true
#guard selectOwnedDeclaration p508_6 "count" == .property 2
#guard elaboratesToParameter p508_6 "count" == false
#guard selectOwnedDeclaration p508_8 "Head" == .property 2
#guard elaboratesToParameter p508_8 "Head" == false
#guard selectOwnedDeclaration p508_7 "H" == .property 0 -- x2
#guard elaboratesToParameter p508_7 "H" == false -- x2
#guard selectOwnedDeclaration p508_0 "Collected" == .property 0
#guard elaboratesToParameter p508_0 "Collected" == false
#guard selectOwnedDeclaration p508_0 "Fixed" == .property 0
#guard elaboratesToParameter p508_0 "Fixed" == false
#guard selectOwnedDeclaration p508_0 "Partial" == .property 0
#guard elaboratesToParameter p508_0 "Partial" == false

-- spec/ownership-captured-parameter-beats-outer-property: v = 99 \n Outer(v) = { \n     Inner = v + 1 \n     Inner \n } \n Outer(7)
def p509_0 : List OwnerLevel := { parameters := [], properties := ["v", "Outer"] } :: prelude
def p509_1 : List OwnerLevel := { parameters := [], properties := [] } :: p509_0
def p509_2 : List OwnerLevel := { parameters := ["v"], properties := ["Inner"] } :: p509_0
def p509_3 : List OwnerLevel := { parameters := [], properties := [] } :: p509_2
#guard selectOwnedDeclaration p509_3 "v" == .parameter 1
#guard elaboratesToParameter p509_3 "v" == true
#guard selectOwnedDeclaration p509_2 "Inner" == .property 0
#guard elaboratesToParameter p509_2 "Inner" == false
#guard selectOwnedDeclaration p509_0 "Outer" == .property 0
#guard elaboratesToParameter p509_0 "Outer" == false

-- spec/ownership-same-owner-parameter-beats-property: Outer(v) = { \n     v = 5 \n     Inner = v + 1 \n     Inner + v \n } \n Outer(7)
def p510_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p510_1 : List OwnerLevel := { parameters := ["v"], properties := ["v", "Inner"] } :: p510_0
def p510_2 : List OwnerLevel := { parameters := [], properties := [] } :: p510_1
def p510_3 : List OwnerLevel := { parameters := [], properties := [] } :: p510_1
#guard selectOwnedDeclaration p510_3 "v" == .parameter 1
#guard elaboratesToParameter p510_3 "v" == true
#guard selectOwnedDeclaration p510_1 "Inner" == .property 0
#guard elaboratesToParameter p510_1 "Inner" == false
#guard selectOwnedDeclaration p510_1 "v" == .parameter 0
#guard elaboratesToParameter p510_1 "v" == true
#guard selectOwnedDeclaration p510_0 "Outer" == .property 0
#guard elaboratesToParameter p510_0 "Outer" == false

-- spec/ownership-nearer-property-beats-outer-parameter: v = 99 \n Outer(v) = { \n     Mid = { \n         v = 5 \n         Inner = v + 1 \n         Inner \n     } \n     Mid \n } \n Outer(7)
def p511_0 : List OwnerLevel := { parameters := [], properties := ["v", "Outer"] } :: prelude
def p511_1 : List OwnerLevel := { parameters := [], properties := [] } :: p511_0
def p511_2 : List OwnerLevel := { parameters := ["v"], properties := ["Mid"] } :: p511_0
def p511_3 : List OwnerLevel := { parameters := [], properties := ["v", "Inner"] } :: p511_2
def p511_4 : List OwnerLevel := { parameters := [], properties := [] } :: p511_3
def p511_5 : List OwnerLevel := { parameters := [], properties := [] } :: p511_3
#guard selectOwnedDeclaration p511_5 "v" == .property 1
#guard elaboratesToParameter p511_5 "v" == false
#guard selectOwnedDeclaration p511_3 "Inner" == .property 0
#guard elaboratesToParameter p511_3 "Inner" == false
#guard selectOwnedDeclaration p511_2 "Mid" == .property 0
#guard elaboratesToParameter p511_2 "Mid" == false
#guard selectOwnedDeclaration p511_0 "Outer" == .property 0
#guard elaboratesToParameter p511_0 "Outer" == false

-- spec/ownership-nearest-enclosing-parameter-wins: v = 99 \n Outer(v) = { \n     Mid(v) = { \n         Inner = v + 1 \n         Inner \n     } \n     Mid(7) \n } \n Outer(20)
def p512_0 : List OwnerLevel := { parameters := [], properties := ["v", "Outer"] } :: prelude
def p512_1 : List OwnerLevel := { parameters := [], properties := [] } :: p512_0
def p512_2 : List OwnerLevel := { parameters := ["v"], properties := ["Mid"] } :: p512_0
def p512_3 : List OwnerLevel := { parameters := ["v"], properties := ["Inner"] } :: p512_2
def p512_4 : List OwnerLevel := { parameters := [], properties := [] } :: p512_3
#guard selectOwnedDeclaration p512_4 "v" == .parameter 1
#guard elaboratesToParameter p512_4 "v" == true
#guard selectOwnedDeclaration p512_3 "Inner" == .property 0
#guard elaboratesToParameter p512_3 "Inner" == false
#guard selectOwnedDeclaration p512_2 "Mid" == .property 0
#guard elaboratesToParameter p512_2 "Mid" == false
#guard selectOwnedDeclaration p512_0 "Outer" == .property 0
#guard elaboratesToParameter p512_0 "Outer" == false

-- spec/ownership-parameter-beats-prelude-alias: Outer(pi) = { \n     Inner = pi + 1 \n     Inner \n } \n Outer(7)
def p513_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p513_1 : List OwnerLevel := { parameters := ["pi"], properties := ["Inner"] } :: p513_0
def p513_2 : List OwnerLevel := { parameters := [], properties := [] } :: p513_1
#guard selectOwnedDeclaration p513_2 "pi" == .parameter 1
#guard elaboratesToParameter p513_2 "pi" == true
#guard selectOwnedDeclaration p513_1 "Inner" == .property 0
#guard elaboratesToParameter p513_1 "Inner" == false
#guard selectOwnedDeclaration p513_0 "Outer" == .property 0
#guard elaboratesToParameter p513_0 "Outer" == false

-- spec/ownership-parameter-beats-opened-name: Lib = { \n     public v = 99 \n } \n Outer(v) = { \n     open Lib \n     Inner = v + 1 \n     Inner \n } \n Outer(7)
def p514_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Outer"] } :: prelude
def p514_1 : List OwnerLevel := { parameters := [], properties := ["v"] } :: p514_0
def p514_2 : List OwnerLevel := { parameters := [], properties := [] } :: p514_1
def p514_3 : List OwnerLevel := { parameters := ["v"], properties := ["Inner"] } :: p514_0
def p514_4 : List OwnerLevel := { parameters := [], properties := [] } :: p514_3
#guard selectOwnedDeclaration p514_3 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p514_3 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p514_4 "v" == .parameter 1
#guard elaboratesToParameter p514_4 "v" == true
#guard selectOwnedDeclaration p514_3 "Inner" == .property 0
#guard elaboratesToParameter p514_3 "Inner" == false
#guard selectOwnedDeclaration p514_0 "Outer" == .property 0
#guard elaboratesToParameter p514_0 "Outer" == false

-- spec/ownership-open-target-parameter-rejected: Lib = { \n     public X = 7 \n } \n Other = { \n     public X = 8 \n } \n F(Lib) = { \n     open Lib \n     X, Lib.X \n } \n F(Other)
def p515_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Other", "F"] } :: prelude
def p515_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p515_0
def p515_2 : List OwnerLevel := { parameters := [], properties := [] } :: p515_1
def p515_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p515_0
def p515_4 : List OwnerLevel := { parameters := [], properties := [] } :: p515_3
def p515_5 : List OwnerLevel := { parameters := ["Lib"], properties := [] } :: p515_0
#guard selectOwnedDeclaration p515_5 "Lib" == .parameter 0 -- x2
#guard openHead? (elaborateOpenHead p515_5 "Lib") == some (true, "Lib")
#guard selectOwnedDeclaration p515_5 "X" == .none -- x2
#guard elaboratesToParameter p515_5 "X" == false -- x2
#guard elaboratesToParameter p515_5 "Lib" == true
#guard selectOwnedDeclaration p515_0 "F" == .property 0
#guard elaboratesToParameter p515_0 "F" == false
#guard selectOwnedDeclaration p515_0 "Other" == .property 0
#guard elaboratesToParameter p515_0 "Other" == false

-- spec/ownership-open-target-parameter-without-farther-declaration: Other = { \n     public X = 8 \n } \n F(Lib) = { \n     open Lib \n     X \n } \n F(Other)
def p516_0 : List OwnerLevel := { parameters := [], properties := ["Other", "F"] } :: prelude
def p516_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p516_0
def p516_2 : List OwnerLevel := { parameters := [], properties := [] } :: p516_1
def p516_3 : List OwnerLevel := { parameters := ["Lib"], properties := [] } :: p516_0
#guard selectOwnedDeclaration p516_3 "Lib" == .parameter 0
#guard openHead? (elaborateOpenHead p516_3 "Lib") == some (true, "Lib")
#guard selectOwnedDeclaration p516_3 "X" == .none
#guard elaboratesToParameter p516_3 "X" == false
#guard selectOwnedDeclaration p516_0 "F" == .property 0
#guard elaboratesToParameter p516_0 "F" == false
#guard selectOwnedDeclaration p516_0 "Other" == .property 0
#guard elaboratesToParameter p516_0 "Other" == false

-- spec/ownership-open-qualified-target-parameter-rejected: Root = { \n     public Sub = { \n         public X = 7 \n     } \n } \n F(Root) = { \n     open Root.Sub \n     X \n } \n F(Root)
def p517_0 : List OwnerLevel := { parameters := [], properties := ["Root", "F"] } :: prelude
def p517_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p517_0
def p517_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p517_1
def p517_3 : List OwnerLevel := { parameters := [], properties := [] } :: p517_2
def p517_4 : List OwnerLevel := { parameters := ["Root"], properties := [] } :: p517_0
#guard selectOwnedDeclaration p517_4 "Root" == .parameter 0
#guard openHead? (elaborateOpenHead p517_4 "Root") == some (true, "Root")
#guard selectOwnedDeclaration p517_4 "X" == .none
#guard elaboratesToParameter p517_4 "X" == false
#guard selectOwnedDeclaration p517_0 "F" == .property 0
#guard elaboratesToParameter p517_0 "F" == false
#guard selectOwnedDeclaration p517_0 "Root" == .property 0
#guard elaboratesToParameter p517_0 "Root" == false

-- spec/ownership-open-target-enclosing-parameter-rejected: Lib = { \n     public X = 7 \n } \n Outer(Lib) = { \n     Inner = { \n         open Lib \n         X \n     } \n     Inner \n } \n Outer(3)
def p518_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Outer"] } :: prelude
def p518_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p518_0
def p518_2 : List OwnerLevel := { parameters := [], properties := [] } :: p518_1
def p518_3 : List OwnerLevel := { parameters := ["Lib"], properties := ["Inner"] } :: p518_0
def p518_4 : List OwnerLevel := { parameters := ["X"], properties := [] } :: p518_3
#guard selectOwnedDeclaration p518_4 "Lib" == .parameter 1
#guard openHead? (elaborateOpenHead p518_4 "Lib") == some (true, "Lib")
#guard selectOwnedDeclaration p518_4 "X" == .parameter 0
#guard elaboratesToParameter p518_4 "X" == true
#guard selectOwnedDeclaration p518_3 "Inner" == .property 0
#guard elaboratesToParameter p518_3 "Inner" == false
#guard selectOwnedDeclaration p518_0 "Outer" == .property 0
#guard elaboratesToParameter p518_0 "Outer" == false

-- spec/native-argument-value-demand: Z = 1 / 0 \n  \n Math.Abs(Z)
def p519_0 : List OwnerLevel := { parameters := [], properties := ["Z"] } :: prelude
def p519_1 : List OwnerLevel := { parameters := [], properties := [] } :: p519_0
#guard selectOwnedDeclaration p519_0 "Math" == .property 1
#guard elaboratesToParameter p519_0 "Math" == false
#guard selectOwnedDeclaration p519_0 "Abs" == .none
#guard elaboratesToParameter p519_0 "Abs" == false
#guard selectOwnedDeclaration p519_0 "Z" == .property 0
#guard elaboratesToParameter p519_0 "Z" == false

-- spec/closed-list-strict-value-forwarding: A = q + 1 \n F(x) = Math.Abs(A) \n  \n F(7)
def p520_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p520_1 : List OwnerLevel := { parameters := ["q"], properties := [] } :: p520_0
def p520_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p520_0
#guard selectOwnedDeclaration p520_1 "q" == .parameter 0
#guard elaboratesToParameter p520_1 "q" == true
#guard selectOwnedDeclaration p520_2 "Math" == .property 2
#guard elaboratesToParameter p520_2 "Math" == false
#guard selectOwnedDeclaration p520_2 "Abs" == .none
#guard elaboratesToParameter p520_2 "Abs" == false
#guard selectOwnedDeclaration p520_2 "A" == .property 1
#guard elaboratesToParameter p520_2 "A" == false
#guard selectOwnedDeclaration p520_0 "F" == .property 0
#guard elaboratesToParameter p520_0 "F" == false

-- spec/clause-family-nested-in-branch-body-binds-its-own-binders: n = 99 \n F(0) = { \n   G(0) = 'zero' \n   G(n) = n \n   G(5) \n } \n F(k) = k \n  \n F(0)
def p521_0 : List OwnerLevel := { parameters := [], properties := ["n", "F"] } :: prelude
def p521_1 : List OwnerLevel := { parameters := [], properties := [] } :: p521_0
def p521_2 : List OwnerLevel := { parameters := [], properties := ["G"] } :: p521_0
def p521_3 : List OwnerLevel := { parameters := [], properties := [] } :: p521_2
def p521_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p521_2
def p521_5 : List OwnerLevel := { parameters := ["k"], properties := [] } :: p521_0
#guard selectOwnedDeclaration p521_4 "n" == .parameter 0
#guard elaboratesToParameter p521_4 "n" == true
#guard selectOwnedDeclaration p521_2 "G" == .property 0
#guard elaboratesToParameter p521_2 "G" == false
#guard selectOwnedDeclaration p521_5 "k" == .parameter 0
#guard elaboratesToParameter p521_5 "k" == true
#guard selectOwnedDeclaration p521_0 "F" == .property 0
#guard elaboratesToParameter p521_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "k")] == some [.capture { name := "k" }] -- family F
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family G

-- spec/conditional-branch-pattern-is-a-closed-input-specification: A = x + 1 \n F(0) = A + 0 \n F(n) = n \n  \n F(0)
def p522_0 : List OwnerLevel := { parameters := [], properties := ["A", "F"] } :: prelude
def p522_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p522_0
def p522_2 : List OwnerLevel := { parameters := [], properties := [] } :: p522_0
def p522_3 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p522_0
#guard selectOwnedDeclaration p522_1 "x" == .parameter 0
#guard elaboratesToParameter p522_1 "x" == true
#guard selectOwnedDeclaration p522_2 "A" == .property 1
#guard elaboratesToParameter p522_2 "A" == false
#guard selectOwnedDeclaration p522_3 "n" == .parameter 0
#guard elaboratesToParameter p522_3 "n" == true
#guard selectOwnedDeclaration p522_0 "F" == .property 0
#guard elaboratesToParameter p522_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/expression-position-block-closed-list-is-diagnosed: { \n   F(x) = y \n   F(1) \n }
def p523_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p523_1 : List OwnerLevel := { parameters := [], properties := ["F"] } :: p523_0
def p523_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p523_1
#guard selectOwnedDeclaration p523_2 "y" == .none
#guard elaboratesToParameter p523_2 "y" == false
#guard selectOwnedDeclaration p523_1 "F" == .property 0
#guard elaboratesToParameter p523_1 "F" == false

-- spec/conditional-branch-inline-open-exposes-members-to-the-branch: F(0) = { \n   open { \n     public Helper = 5 \n   } \n   Helper \n } \n F(n) = n \n  \n F(0)
def p524_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p524_1 : List OwnerLevel := { parameters := [], properties := [] } :: p524_0
def p524_2 : List OwnerLevel := { parameters := [], properties := ["Helper"] } :: prelude
def p524_3 : List OwnerLevel := { parameters := [], properties := [] } :: p524_2
def p524_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p524_0
#guard selectOwnedDeclaration p524_1 "Helper" == .none
#guard elaboratesToParameter p524_1 "Helper" == false
#guard selectOwnedDeclaration p524_4 "n" == .parameter 0
#guard elaboratesToParameter p524_4 "n" == true
#guard selectOwnedDeclaration p524_0 "F" == .property 0
#guard elaboratesToParameter p524_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/conditional-branch-inline-open-does-not-leak-to-sibling-branches: F(0) = { \n   open { \n     public Helper = 5 \n   } \n   Helper \n } \n F(1) = Helper \n F(n) = n \n  \n F(1)
def p525_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p525_1 : List OwnerLevel := { parameters := [], properties := [] } :: p525_0
def p525_2 : List OwnerLevel := { parameters := [], properties := ["Helper"] } :: prelude
def p525_3 : List OwnerLevel := { parameters := [], properties := [] } :: p525_2
def p525_4 : List OwnerLevel := { parameters := [], properties := [] } :: p525_0
def p525_5 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p525_0
#guard selectOwnedDeclaration p525_1 "Helper" == .none
#guard elaboratesToParameter p525_1 "Helper" == false
#guard selectOwnedDeclaration p525_4 "Helper" == .none
#guard elaboratesToParameter p525_4 "Helper" == false
#guard selectOwnedDeclaration p525_5 "n" == .parameter 0
#guard elaboratesToParameter p525_5 "n" == true
#guard selectOwnedDeclaration p525_0 "F" == .property 0
#guard elaboratesToParameter p525_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.litInt 1), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches: open Lib \n Lib = { \n   public Helper = 7 \n } \n F(0) = { \n   open { \n     public Helper = 5 \n   } \n   Helper \n } \n F(1) = Helper \n F(n) = n \n  \n F(0), F(1), F(2)
def p526_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "F"] } :: prelude
def p526_1 : List OwnerLevel := { parameters := [], properties := ["Helper"] } :: p526_0
def p526_2 : List OwnerLevel := { parameters := [], properties := [] } :: p526_1
def p526_3 : List OwnerLevel := { parameters := [], properties := [] } :: p526_0
def p526_4 : List OwnerLevel := { parameters := [], properties := ["Helper"] } :: prelude
def p526_5 : List OwnerLevel := { parameters := [], properties := [] } :: p526_4
def p526_6 : List OwnerLevel := { parameters := [], properties := [] } :: p526_0
def p526_7 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p526_0
#guard selectOwnedDeclaration p526_0 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p526_0 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p526_3 "Helper" == .none
#guard elaboratesToParameter p526_3 "Helper" == false
#guard selectOwnedDeclaration p526_6 "Helper" == .none
#guard elaboratesToParameter p526_6 "Helper" == false
#guard selectOwnedDeclaration p526_7 "n" == .parameter 0
#guard elaboratesToParameter p526_7 "n" == true
#guard selectOwnedDeclaration p526_0 "F" == .property 0 -- x3
#guard elaboratesToParameter p526_0 "F" == false -- x3
#guard familyLiftingSignature? [clause (.litInt 0), clause (.litInt 1), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/conditional-branch-local-library-is-openable-within-the-branch: F(0) = { \n   Lib = { \n     public X = 1 \n   } \n   G = { \n     open Lib \n     X \n   } \n   G \n } \n F(n) = n \n  \n F(0)
def p527_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p527_1 : List OwnerLevel := { parameters := [], properties := ["Lib", "G"] } :: p527_0
def p527_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p527_1
def p527_3 : List OwnerLevel := { parameters := [], properties := [] } :: p527_2
def p527_4 : List OwnerLevel := { parameters := [], properties := [] } :: p527_1
def p527_5 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p527_0
#guard selectOwnedDeclaration p527_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p527_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p527_4 "X" == .none
#guard elaboratesToParameter p527_4 "X" == false
#guard selectOwnedDeclaration p527_1 "G" == .property 0
#guard elaboratesToParameter p527_1 "G" == false
#guard selectOwnedDeclaration p527_5 "n" == .parameter 0
#guard elaboratesToParameter p527_5 "n" == true
#guard selectOwnedDeclaration p527_0 "F" == .property 0
#guard elaboratesToParameter p527_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/conditional-branch-local-library-does-not-leak-to-sibling-branches: F(0) = { \n   Lib = { \n     public X = 1 \n   } \n   G = { \n     open Lib \n     X \n   } \n   G \n } \n F(1) = X \n F(n) = n \n  \n F(1)
def p528_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p528_1 : List OwnerLevel := { parameters := [], properties := ["Lib", "G"] } :: p528_0
def p528_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p528_1
def p528_3 : List OwnerLevel := { parameters := [], properties := [] } :: p528_2
def p528_4 : List OwnerLevel := { parameters := [], properties := [] } :: p528_1
def p528_5 : List OwnerLevel := { parameters := [], properties := [] } :: p528_0
def p528_6 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p528_0
#guard selectOwnedDeclaration p528_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p528_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p528_4 "X" == .none
#guard elaboratesToParameter p528_4 "X" == false
#guard selectOwnedDeclaration p528_1 "G" == .property 0
#guard elaboratesToParameter p528_1 "G" == false
#guard selectOwnedDeclaration p528_5 "X" == .none
#guard elaboratesToParameter p528_5 "X" == false
#guard selectOwnedDeclaration p528_6 "n" == .parameter 0
#guard elaboratesToParameter p528_6 "n" == true
#guard selectOwnedDeclaration p528_0 "F" == .property 0
#guard elaboratesToParameter p528_0 "F" == false
#guard familyLiftingSignature? [clause (.litInt 0), clause (.litInt 1), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

-- spec/builtin-callable-is-an-ordinary-prelude-binding: if(x) = x + 1 \n  \n if(7) \n 7.if \n if((7)*)
def p529_0 : List OwnerLevel := { parameters := [], properties := ["if"] } :: prelude
def p529_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p529_0
#guard selectOwnedDeclaration p529_1 "x" == .parameter 0
#guard elaboratesToParameter p529_1 "x" == true
#guard selectOwnedDeclaration p529_0 "if" == .property 0 -- x3
#guard elaboratesToParameter p529_0 "if" == false -- x3

-- spec/no-arity-based-callable-selection: if(x) = x + 1 \n  \n if(true, 2, 3)
def p530_0 : List OwnerLevel := { parameters := [], properties := ["if"] } :: prelude
def p530_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p530_0
#guard selectOwnedDeclaration p530_1 "x" == .parameter 0
#guard elaboratesToParameter p530_1 "x" == true
#guard selectOwnedDeclaration p530_0 "if" == .property 0
#guard elaboratesToParameter p530_0 "if" == false

-- spec/if-composition-forms-agree: Cond = true \n Branches = (10, 20) \n Apply3(f, a, b, c) = f(a, b, c) \n  \n if(Cond, 10, 20) \n Cond.if(10, 20) \n if(Cond, Branches*) \n Cond.if(Branches*) \n Apply3(if, Cond, 10, 20)
def p531_0 : List OwnerLevel := { parameters := [], properties := ["Cond", "Branches", "Apply3"] } :: prelude
def p531_1 : List OwnerLevel := { parameters := [], properties := [] } :: p531_0
def p531_2 : List OwnerLevel := { parameters := [], properties := [] } :: p531_0
def p531_3 : List OwnerLevel := { parameters := ["f", "a", "b", "c"], properties := [] } :: p531_0
#guard selectOwnedDeclaration p531_3 "f" == .parameter 0
#guard elaboratesToParameter p531_3 "f" == true
#guard selectOwnedDeclaration p531_3 "a" == .parameter 0
#guard elaboratesToParameter p531_3 "a" == true
#guard selectOwnedDeclaration p531_3 "b" == .parameter 0
#guard elaboratesToParameter p531_3 "b" == true
#guard selectOwnedDeclaration p531_3 "c" == .parameter 0
#guard elaboratesToParameter p531_3 "c" == true
#guard selectOwnedDeclaration p531_0 "if" == .property 1 -- x5
#guard elaboratesToParameter p531_0 "if" == false -- x5
#guard selectOwnedDeclaration p531_0 "Cond" == .property 0 -- x5
#guard elaboratesToParameter p531_0 "Cond" == false -- x5
#guard selectOwnedDeclaration p531_0 "Branches" == .property 0 -- x2
#guard elaboratesToParameter p531_0 "Branches" == false -- x2
#guard selectOwnedDeclaration p531_0 "Apply3" == .property 0
#guard elaboratesToParameter p531_0 "Apply3" == false

-- spec/if-laziness-follows-the-resolved-identity: Boom = 1 / 0 \n  \n if(true, 10, Boom) \n false.if(Boom, 20)
def p532_0 : List OwnerLevel := { parameters := [], properties := ["Boom"] } :: prelude
def p532_1 : List OwnerLevel := { parameters := [], properties := [] } :: p532_0
#guard selectOwnedDeclaration p532_0 "if" == .property 1 -- x2
#guard elaboratesToParameter p532_0 "if" == false -- x2
#guard selectOwnedDeclaration p532_0 "Boom" == .property 0 -- x2
#guard elaboratesToParameter p532_0 "Boom" == false -- x2

-- spec/dot-string-parameter-receiver-reports-the-written-argument: Show(v) = v.string \n Show({ x + 1 })
def p533_0 : List OwnerLevel := { parameters := [], properties := ["Show"] } :: prelude
def p533_1 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p533_0
def p533_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p533_0
#guard selectOwnedDeclaration p533_1 "v" == .parameter 0
#guard elaboratesToParameter p533_1 "v" == true
#guard selectOwnedDeclaration p533_1 "string" == .none
#guard elaboratesToParameter p533_1 "string" == false
#guard selectOwnedDeclaration p533_0 "Show" == .property 0
#guard elaboratesToParameter p533_0 "Show" == false
#guard selectOwnedDeclaration p533_2 "x" == .parameter 0
#guard elaboratesToParameter p533_2 "x" == true

-- spec/zero-argument-callable-name-is-read-not-lifted: Cnt(*xs) = xs.count \n Pair(*xs) = 10, 20 \n Alias = Cnt \n Twice(*items) = Cnt + Cnt \n  \n Cnt + 1, [Cnt], Cnt == Cnt, Pair[1] \n Alias, Alias() \n Twice(1, 2, 3)
def p534_0 : List OwnerLevel := { parameters := [], properties := ["Alias", "Cnt", "Pair", "Twice"] } :: prelude
def p534_1 : List OwnerLevel := { parameters := [], properties := [] } :: p534_0
def p534_2 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p534_0
def p534_3 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p534_0
def p534_4 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p534_0
#guard selectOwnedDeclaration p534_1 "Cnt" == .property 1
#guard elaboratesToParameter p534_1 "Cnt" == false
#guard selectOwnedDeclaration p534_2 "xs" == .parameter 0
#guard elaboratesToParameter p534_2 "xs" == true
#guard selectOwnedDeclaration p534_2 "count" == .property 2
#guard elaboratesToParameter p534_2 "count" == false
#guard selectOwnedDeclaration p534_4 "Cnt" == .property 1 -- x2
#guard elaboratesToParameter p534_4 "Cnt" == false -- x2
#guard selectOwnedDeclaration p534_0 "Cnt" == .property 0 -- x4
#guard elaboratesToParameter p534_0 "Cnt" == false -- x4
#guard selectOwnedDeclaration p534_0 "Pair" == .property 0
#guard elaboratesToParameter p534_0 "Pair" == false
#guard selectOwnedDeclaration p534_0 "Alias" == .property 0 -- x2
#guard elaboratesToParameter p534_0 "Alias" == false -- x2
#guard selectOwnedDeclaration p534_0 "Twice" == .property 0
#guard elaboratesToParameter p534_0 "Twice" == false

-- spec/same-arity-user-if-keeps-user-identity: if(a, b, c) = a + b + c \n if(1, 10, 20) \n 1.if(10, 20)
def p535_0 : List OwnerLevel := { parameters := [], properties := ["if"] } :: prelude
def p535_1 : List OwnerLevel := { parameters := ["a", "b", "c"], properties := [] } :: p535_0
#guard selectOwnedDeclaration p535_1 "a" == .parameter 0
#guard elaboratesToParameter p535_1 "a" == true
#guard selectOwnedDeclaration p535_1 "b" == .parameter 0
#guard elaboratesToParameter p535_1 "b" == true
#guard selectOwnedDeclaration p535_1 "c" == .parameter 0
#guard elaboratesToParameter p535_1 "c" == true
#guard selectOwnedDeclaration p535_0 "if" == .property 0 -- x2
#guard elaboratesToParameter p535_0 "if" == false -- x2

-- spec/parameter-named-if-carries-the-supplied-callable: Apply(if, x) = { Inner = if(x) \n  Inner } \n Inc(x) = x + 1 \n Apply(Inc, 7)
def p536_0 : List OwnerLevel := { parameters := [], properties := ["Apply", "Inc"] } :: prelude
def p536_1 : List OwnerLevel := { parameters := ["if", "x"], properties := ["Inner"] } :: p536_0
def p536_2 : List OwnerLevel := { parameters := [], properties := [] } :: p536_1
def p536_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p536_0
#guard selectOwnedDeclaration p536_2 "if" == .parameter 1
#guard elaboratesToParameter p536_2 "if" == true
#guard selectOwnedDeclaration p536_2 "x" == .parameter 1
#guard elaboratesToParameter p536_2 "x" == true
#guard selectOwnedDeclaration p536_1 "Inner" == .property 0
#guard elaboratesToParameter p536_1 "Inner" == false
#guard selectOwnedDeclaration p536_3 "x" == .parameter 0
#guard elaboratesToParameter p536_3 "x" == true
#guard selectOwnedDeclaration p536_0 "Apply" == .property 0
#guard elaboratesToParameter p536_0 "Apply" == false
#guard selectOwnedDeclaration p536_0 "Inc" == .property 0
#guard elaboratesToParameter p536_0 "Inc" == false

-- spec/if-spread-builds-values-before-branch-selection: Risky = (10, 1 / 0) \n if(true, Risky*)
def p537_0 : List OwnerLevel := { parameters := [], properties := ["Risky"] } :: prelude
def p537_1 : List OwnerLevel := { parameters := [], properties := [] } :: p537_0
#guard selectOwnedDeclaration p537_0 "if" == .property 1
#guard elaboratesToParameter p537_0 "if" == false
#guard selectOwnedDeclaration p537_0 "Risky" == .property 0
#guard elaboratesToParameter p537_0 "Risky" == false

-- spec/dot-string-intrinsic-rejects-arguments: A = 42 \n A.string(1)
def p538_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p538_1 : List OwnerLevel := { parameters := [], properties := [] } :: p538_0
#guard selectOwnedDeclaration p538_0 "A" == .property 0
#guard elaboratesToParameter p538_0 "A" == false
#guard selectOwnedDeclaration p538_0 "string" == .none
#guard elaboratesToParameter p538_0 "string" == false

-- spec/ownership-open-provided-captured-member-read-by-sibling-is-local-only: Outer(p) = { \n     open Lib \n     Lib = { public X = p } \n     public Y = X \n     Y \n } \n Outer.Y
def p539_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p539_1 : List OwnerLevel := { parameters := ["p"], properties := ["Lib", "Y"] } :: p539_0
def p539_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p539_1
def p539_3 : List OwnerLevel := { parameters := [], properties := [] } :: p539_2
def p539_4 : List OwnerLevel := { parameters := [], properties := [] } :: p539_1
#guard selectOwnedDeclaration p539_1 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p539_1 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p539_3 "p" == .parameter 2
#guard elaboratesToParameter p539_3 "p" == true
#guard selectOwnedDeclaration p539_4 "X" == .none
#guard elaboratesToParameter p539_4 "X" == false
#guard selectOwnedDeclaration p539_1 "Y" == .property 0
#guard elaboratesToParameter p539_1 "Y" == false
#guard selectOwnedDeclaration p539_0 "Outer" == .property 0
#guard elaboratesToParameter p539_0 "Outer" == false
#guard selectOwnedDeclaration p539_0 "Y" == .none
#guard elaboratesToParameter p539_0 "Y" == false

-- spec/ownership-open-head-between-opener-and-settling-level-charges-the-capture: Outer(p) = { \n     Mid = { \n         Lib = { public X = p } \n         Inner = { \n             open Lib \n             X \n         } \n         Inner \n     } \n     Mid \n } \n Outer.Mid
def p540_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p540_1 : List OwnerLevel := { parameters := ["p"], properties := ["Mid"] } :: p540_0
def p540_2 : List OwnerLevel := { parameters := [], properties := ["Lib", "Inner"] } :: p540_1
def p540_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p540_2
def p540_4 : List OwnerLevel := { parameters := [], properties := [] } :: p540_3
def p540_5 : List OwnerLevel := { parameters := [], properties := [] } :: p540_2
#guard selectOwnedDeclaration p540_4 "p" == .parameter 3
#guard elaboratesToParameter p540_4 "p" == true
#guard selectOwnedDeclaration p540_5 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p540_5 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p540_5 "X" == .none
#guard elaboratesToParameter p540_5 "X" == false
#guard selectOwnedDeclaration p540_2 "Inner" == .property 0
#guard elaboratesToParameter p540_2 "Inner" == false
#guard selectOwnedDeclaration p540_1 "Mid" == .property 0
#guard elaboratesToParameter p540_1 "Mid" == false
#guard selectOwnedDeclaration p540_0 "Outer" == .property 0
#guard elaboratesToParameter p540_0 "Outer" == false
#guard selectOwnedDeclaration p540_0 "Mid" == .none
#guard elaboratesToParameter p540_0 "Mid" == false

-- spec/grace-in-redundant-group-is-grace-on-the-name: V(x) = x * 2 \n F = b + (~a).V \n F(5, 1)
def p541_0 : List OwnerLevel := { parameters := [], properties := ["F", "V"] } :: prelude
def p541_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p541_0
def p541_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p541_0
#guard selectOwnedDeclaration p541_1 "b" == .parameter 0
#guard elaboratesToParameter p541_1 "b" == true
#guard selectOwnedDeclaration p541_1 "a" == .parameter 0
#guard elaboratesToParameter p541_1 "a" == true
#guard selectOwnedDeclaration p541_1 "V" == .property 1
#guard elaboratesToParameter p541_1 "V" == false
#guard selectOwnedDeclaration p541_2 "x" == .parameter 0
#guard elaboratesToParameter p541_2 "x" == true
#guard selectOwnedDeclaration p541_0 "F" == .property 0
#guard elaboratesToParameter p541_0 "F" == false

-- spec/open-builtin-target-rejected: open count \n Q = 5 \n Q
def p542_0 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: prelude
def p542_1 : List OwnerLevel := { parameters := [], properties := [] } :: p542_0
#guard selectOwnedDeclaration p542_0 "count" == .property 1
#guard openHead? (elaborateOpenHead p542_0 "count") == some (false, "count")
#guard selectOwnedDeclaration p542_0 "Q" == .property 0
#guard elaboratesToParameter p542_0 "Q" == false

-- spec/min-max-signed-zero: min((0, -0)) \n min((-0, 0)) \n max((0, -0)) \n max((-0, 0))
def p543_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p543_0 "min" == .property 1 -- x2
#guard elaboratesToParameter p543_0 "min" == false -- x2
#guard selectOwnedDeclaration p543_0 "max" == .property 1 -- x2
#guard elaboratesToParameter p543_0 "max" == false -- x2

-- spec/repeated-name-keeps-first-equally-rich-representative: P(x, x) = x.string \n  \n P(1.5, 1.50) \n P(1.50, 1.5) \n P(0, -0) \n P(-0, 0)
def p544_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p544_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p544_0
#guard selectOwnedDeclaration p544_1 "x" == .parameter 0
#guard elaboratesToParameter p544_1 "x" == true
#guard selectOwnedDeclaration p544_1 "string" == .none
#guard elaboratesToParameter p544_1 "string" == false
#guard selectOwnedDeclaration p544_0 "P" == .property 0 -- x4
#guard elaboratesToParameter p544_0 "P" == false -- x4

-- spec/decimal-literal-patterns-match-by-value: F(1.5) = 'hit' \n F(x) = 'miss' \n Z(0) = 'zero' \n Z(x) = 'other' \n  \n F(1.50), F(3 / 2), F(1.6) \n Z(-0), Z(0.0)
def p545_0 : List OwnerLevel := { parameters := [], properties := ["F", "Z"] } :: prelude
def p545_1 : List OwnerLevel := { parameters := [], properties := [] } :: p545_0
def p545_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p545_0
def p545_3 : List OwnerLevel := { parameters := [], properties := [] } :: p545_0
def p545_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p545_0
#guard selectOwnedDeclaration p545_0 "F" == .property 0 -- x3
#guard elaboratesToParameter p545_0 "F" == false -- x3
#guard selectOwnedDeclaration p545_0 "Z" == .property 0 -- x2
#guard elaboratesToParameter p545_0 "Z" == false -- x2
-- family F: not guarded (a clause head holds a literal the Lean core cannot spell)
#guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "x")] == some [.capture { name := "x" }] -- family Z

-- spec/max-decimal-places-rounds-ties-away-from-zero: MaxDecimalPlaces = 2 \n 0.125, 0.375, -0.125, 2.5
-- the same levels and decisions, 1 more:
--   spec/decimal-places-show-the-value-not-the-stored-digits
def p546_0 : List OwnerLevel := { parameters := [], properties := ["MaxDecimalPlaces"] } :: prelude
def p546_1 : List OwnerLevel := { parameters := [], properties := [] } :: p546_0

-- spec/min-decimal-places-pads-and-never-rounds: MinDecimalPlaces = 2 \n 10, 2.5, 1.234567, 0
def p547_0 : List OwnerLevel := { parameters := [], properties := ["MinDecimalPlaces"] } :: prelude
def p547_1 : List OwnerLevel := { parameters := [], properties := [] } :: p547_0

-- spec/equal-min-and-max-decimal-places-fix-the-places: MinDecimalPlaces = 2 \n MaxDecimalPlaces = 2 \n 1.234567, 10, 9.9996, -0.004
def p548_0 : List OwnerLevel := { parameters := [], properties := ["MinDecimalPlaces", "MaxDecimalPlaces"] } :: prelude
def p548_1 : List OwnerLevel := { parameters := [], properties := [] } :: p548_0
def p548_2 : List OwnerLevel := { parameters := [], properties := [] } :: p548_0

-- spec/logarithm-near-one-is-accurate: Math.Ln(1 + 1e-20)
def p549_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p549_0 "Math" == .property 1
#guard elaboratesToParameter p549_0 "Math" == false
#guard selectOwnedDeclaration p549_0 "Ln" == .none
#guard elaboratesToParameter p549_0 "Ln" == false

-- spec/negative-near-one-base-power-is-sign-symmetric: B = 0.9999999999999999999999999999999999 \n (-B) ^ 1e34 == B ^ 1e34
def p550_0 : List OwnerLevel := { parameters := [], properties := ["B"] } :: prelude
def p550_1 : List OwnerLevel := { parameters := [], properties := [] } :: p550_0
#guard selectOwnedDeclaration p550_0 "B" == .property 0 -- x2
#guard elaboratesToParameter p550_0 "B" == false -- x2

-- spec/string-literal-pattern-selects-a-clause: Greeting('en') = 'Hello' \n Greeting('lv') = 'Sveiki' \n Greeting(x) = '?' \n  \n Greeting('lv') \n Greeting('de') \n Greeting(5)
def p551_0 : List OwnerLevel := { parameters := [], properties := ["Greeting"] } :: prelude
def p551_1 : List OwnerLevel := { parameters := [], properties := [] } :: p551_0
def p551_2 : List OwnerLevel := { parameters := [], properties := [] } :: p551_0
def p551_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p551_0
#guard selectOwnedDeclaration p551_0 "Greeting" == .property 0 -- x3
#guard elaboratesToParameter p551_0 "Greeting" == false -- x3
#guard familyLiftingSignature? [clause (.litString "en"), clause (.litString "lv"), clause (.bind "x")] == some [.capture { name := "x" }] -- family Greeting

-- spec/string-and-number-stay-separate-items: Total = 3 + 8 \n 'Total', Total \n ['a', 1, 'b']
def p552_0 : List OwnerLevel := { parameters := [], properties := ["Total"] } :: prelude
def p552_1 : List OwnerLevel := { parameters := [], properties := [] } :: p552_0
#guard selectOwnedDeclaration p552_0 "Total" == .property 0
#guard elaboratesToParameter p552_0 "Total" == false

-- spec/meta-capture-invokes-the-original-call: Square(x) = x * x \n Capture(meta operation) = operation \n R = Capture(Square(5)) \n  \n R.Invoke() \n R.Invoke()
def p553_0 : List OwnerLevel := { parameters := [], properties := ["R", "Square", "Capture"] } :: prelude
def p553_1 : List OwnerLevel := { parameters := [], properties := [] } :: p553_0
def p553_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p553_0
def p553_3 : List OwnerLevel := { parameters := ["operation"], properties := [] } :: p553_0
#guard selectOwnedDeclaration p553_1 "Capture" == .property 1
#guard elaboratesToParameter p553_1 "Capture" == false
#guard selectOwnedDeclaration p553_1 "Square" == .property 1
#guard elaboratesToParameter p553_1 "Square" == false
#guard selectOwnedDeclaration p553_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p553_2 "x" == true -- x2
#guard selectOwnedDeclaration p553_3 "operation" == .parameter 0
#guard elaboratesToParameter p553_3 "operation" == true
#guard selectOwnedDeclaration p553_0 "R" == .property 0 -- x2
#guard elaboratesToParameter p553_0 "R" == false -- x2
#guard selectOwnedDeclaration p553_0 "Invoke" == .none -- x2
#guard elaboratesToParameter p553_0 "Invoke" == false -- x2

-- spec/meta-capture-sees-through-forwarding-and-value: Square(x) = x * x \n Capture(meta op) = op \n Fwd(y) = Capture(y) \n Use(v) = v + Fwd(v).Invoke() \n  \n Use(Square(3))
def p554_0 : List OwnerLevel := { parameters := [], properties := ["Square", "Capture", "Fwd", "Use"] } :: prelude
def p554_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p554_0
def p554_2 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p554_0
def p554_3 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p554_0
def p554_4 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p554_0
#guard selectOwnedDeclaration p554_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p554_1 "x" == true -- x2
#guard selectOwnedDeclaration p554_2 "op" == .parameter 0
#guard elaboratesToParameter p554_2 "op" == true
#guard selectOwnedDeclaration p554_3 "Capture" == .property 1
#guard elaboratesToParameter p554_3 "Capture" == false
#guard selectOwnedDeclaration p554_3 "y" == .parameter 0
#guard elaboratesToParameter p554_3 "y" == true
#guard selectOwnedDeclaration p554_4 "v" == .parameter 0 -- x2
#guard elaboratesToParameter p554_4 "v" == true -- x2
#guard selectOwnedDeclaration p554_4 "Fwd" == .property 1
#guard elaboratesToParameter p554_4 "Fwd" == false
#guard selectOwnedDeclaration p554_4 "Invoke" == .none
#guard elaboratesToParameter p554_4 "Invoke" == false
#guard selectOwnedDeclaration p554_0 "Use" == .property 0
#guard elaboratesToParameter p554_0 "Use" == false
#guard selectOwnedDeclaration p554_0 "Square" == .property 0
#guard elaboratesToParameter p554_0 "Square" == false

-- spec/meta-refuses-anything-but-a-written-call: Square(x) = x * x \n Capture(meta op) = op \n Y = Square(5) \n Capture(Y)
def p555_0 : List OwnerLevel := { parameters := [], properties := ["Y", "Square", "Capture"] } :: prelude
def p555_1 : List OwnerLevel := { parameters := [], properties := [] } :: p555_0
def p555_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p555_0
def p555_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p555_0
#guard selectOwnedDeclaration p555_1 "Square" == .property 1
#guard elaboratesToParameter p555_1 "Square" == false
#guard selectOwnedDeclaration p555_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p555_2 "x" == true -- x2
#guard selectOwnedDeclaration p555_3 "op" == .parameter 0
#guard elaboratesToParameter p555_3 "op" == true
#guard selectOwnedDeclaration p555_0 "Capture" == .property 0
#guard elaboratesToParameter p555_0 "Capture" == false
#guard selectOwnedDeclaration p555_0 "Y" == .property 0
#guard elaboratesToParameter p555_0 "Y" == false

-- spec/invoke-needs-its-argument-list: Square(x) = x * x \n Capture(meta op) = op \n R = Capture(Square(5)) \n R.Invoke
def p556_0 : List OwnerLevel := { parameters := [], properties := ["R", "Square", "Capture"] } :: prelude
def p556_1 : List OwnerLevel := { parameters := [], properties := [] } :: p556_0
def p556_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p556_0
def p556_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p556_0
#guard selectOwnedDeclaration p556_1 "Capture" == .property 1
#guard elaboratesToParameter p556_1 "Capture" == false
#guard selectOwnedDeclaration p556_1 "Square" == .property 1
#guard elaboratesToParameter p556_1 "Square" == false
#guard selectOwnedDeclaration p556_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p556_2 "x" == true -- x2
#guard selectOwnedDeclaration p556_3 "op" == .parameter 0
#guard elaboratesToParameter p556_3 "op" == true
#guard selectOwnedDeclaration p556_0 "R" == .property 0
#guard elaboratesToParameter p556_0 "R" == false
#guard selectOwnedDeclaration p556_0 "Invoke" == .none
#guard elaboratesToParameter p556_0 "Invoke" == false

-- spec/invoke-is-not-an-extension-call: Invoke(r) = r + 1 \n Invoke(4)
def p557_0 : List OwnerLevel := { parameters := [], properties := ["Invoke"] } :: prelude
def p557_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p557_0
#guard selectOwnedDeclaration p557_1 "r" == .parameter 0
#guard elaboratesToParameter p557_1 "r" == true
#guard selectOwnedDeclaration p557_0 "Invoke" == .property 0
#guard elaboratesToParameter p557_0 "Invoke" == false

-- spec/call-reference-never-leaves-its-run: Square(x) = x * x \n Capture(meta op) = op \n Capture(Square(5))
def p558_0 : List OwnerLevel := { parameters := [], properties := ["Square", "Capture"] } :: prelude
def p558_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p558_0
def p558_2 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p558_0
#guard selectOwnedDeclaration p558_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p558_1 "x" == true -- x2
#guard selectOwnedDeclaration p558_2 "op" == .parameter 0
#guard elaboratesToParameter p558_2 "op" == true
#guard selectOwnedDeclaration p558_0 "Capture" == .property 0
#guard elaboratesToParameter p558_0 "Capture" == false
#guard selectOwnedDeclaration p558_0 "Square" == .property 0
#guard elaboratesToParameter p558_0 "Square" == false

-- spec/call-reference-arguments-view: Add(x, y) = x + y \n Capture(meta op) = op \n R = Capture(Add(10, 20)) \n  \n R.Arguments.count \n R.Arguments[0] \n R.Arguments[1]
def p559_0 : List OwnerLevel := { parameters := [], properties := ["R", "Add", "Capture"] } :: prelude
def p559_1 : List OwnerLevel := { parameters := [], properties := [] } :: p559_0
def p559_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p559_0
def p559_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p559_0
#guard selectOwnedDeclaration p559_1 "Capture" == .property 1
#guard elaboratesToParameter p559_1 "Capture" == false
#guard selectOwnedDeclaration p559_1 "Add" == .property 1
#guard elaboratesToParameter p559_1 "Add" == false
#guard selectOwnedDeclaration p559_2 "x" == .parameter 0
#guard elaboratesToParameter p559_2 "x" == true
#guard selectOwnedDeclaration p559_2 "y" == .parameter 0
#guard elaboratesToParameter p559_2 "y" == true
#guard selectOwnedDeclaration p559_3 "op" == .parameter 0
#guard elaboratesToParameter p559_3 "op" == true
#guard selectOwnedDeclaration p559_0 "R" == .property 0 -- x3
#guard elaboratesToParameter p559_0 "R" == false -- x3
#guard selectOwnedDeclaration p559_0 "Arguments" == .none -- x3
#guard elaboratesToParameter p559_0 "Arguments" == false -- x3
#guard selectOwnedDeclaration p559_0 "count" == .property 1
#guard elaboratesToParameter p559_0 "count" == false

-- spec/arguments-spread-forwards-the-original-arguments: Add(x, y) = x + y \n First(x, y) = x \n Capture(meta op) = op \n R = Capture(Add(5, 1 / 0)) \n  \n First(R.Arguments*)
def p560_0 : List OwnerLevel := { parameters := [], properties := ["R", "Add", "First", "Capture"] } :: prelude
def p560_1 : List OwnerLevel := { parameters := [], properties := [] } :: p560_0
def p560_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p560_0
def p560_3 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p560_0
def p560_4 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p560_0
#guard selectOwnedDeclaration p560_1 "Capture" == .property 1
#guard elaboratesToParameter p560_1 "Capture" == false
#guard selectOwnedDeclaration p560_1 "Add" == .property 1
#guard elaboratesToParameter p560_1 "Add" == false
#guard selectOwnedDeclaration p560_2 "x" == .parameter 0
#guard elaboratesToParameter p560_2 "x" == true
#guard selectOwnedDeclaration p560_2 "y" == .parameter 0
#guard elaboratesToParameter p560_2 "y" == true
#guard selectOwnedDeclaration p560_3 "x" == .parameter 0
#guard elaboratesToParameter p560_3 "x" == true
#guard selectOwnedDeclaration p560_4 "op" == .parameter 0
#guard elaboratesToParameter p560_4 "op" == true
#guard selectOwnedDeclaration p560_0 "First" == .property 0
#guard elaboratesToParameter p560_0 "First" == false
#guard selectOwnedDeclaration p560_0 "R" == .property 0
#guard elaboratesToParameter p560_0 "R" == false
#guard selectOwnedDeclaration p560_0 "Arguments" == .none
#guard elaboratesToParameter p560_0 "Arguments" == false

-- spec/arguments-view-is-not-a-collection: Add(x, y) = x + y \n Capture(meta op) = op \n R = Capture(Add(10, 20)) \n [R.Arguments*]
def p561_0 : List OwnerLevel := { parameters := [], properties := ["R", "Add", "Capture"] } :: prelude
def p561_1 : List OwnerLevel := { parameters := [], properties := [] } :: p561_0
def p561_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p561_0
def p561_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p561_0
#guard selectOwnedDeclaration p561_1 "Capture" == .property 1
#guard elaboratesToParameter p561_1 "Capture" == false
#guard selectOwnedDeclaration p561_1 "Add" == .property 1
#guard elaboratesToParameter p561_1 "Add" == false
#guard selectOwnedDeclaration p561_2 "x" == .parameter 0
#guard elaboratesToParameter p561_2 "x" == true
#guard selectOwnedDeclaration p561_2 "y" == .parameter 0
#guard elaboratesToParameter p561_2 "y" == true
#guard selectOwnedDeclaration p561_3 "op" == .parameter 0
#guard elaboratesToParameter p561_3 "op" == true
#guard selectOwnedDeclaration p561_0 "R" == .property 0
#guard elaboratesToParameter p561_0 "R" == false
#guard selectOwnedDeclaration p561_0 "Arguments" == .none
#guard elaboratesToParameter p561_0 "Arguments" == false

-- spec/arguments-is-not-an-extension-call: Arguments(r) = r + 1 \n Arguments(4)
def p562_0 : List OwnerLevel := { parameters := [], properties := ["Arguments"] } :: prelude
def p562_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p562_0
#guard selectOwnedDeclaration p562_1 "r" == .parameter 0
#guard elaboratesToParameter p562_1 "r" == true
#guard selectOwnedDeclaration p562_0 "Arguments" == .property 0
#guard elaboratesToParameter p562_0 "Arguments" == false

-- spec/call-reference-algorithm-projection: Square(x) = x * x \n Capture(meta op) = op \n R = Capture(Square(5)) \n  \n R.Algorithm(8) \n (R.Algorithm)(8) \n R.Invoke()
def p563_0 : List OwnerLevel := { parameters := [], properties := ["R", "Square", "Capture"] } :: prelude
def p563_1 : List OwnerLevel := { parameters := [], properties := [] } :: p563_0
def p563_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p563_0
def p563_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p563_0
#guard selectOwnedDeclaration p563_1 "Capture" == .property 1
#guard elaboratesToParameter p563_1 "Capture" == false
#guard selectOwnedDeclaration p563_1 "Square" == .property 1
#guard elaboratesToParameter p563_1 "Square" == false
#guard selectOwnedDeclaration p563_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p563_2 "x" == true -- x2
#guard selectOwnedDeclaration p563_3 "op" == .parameter 0
#guard elaboratesToParameter p563_3 "op" == true
#guard selectOwnedDeclaration p563_0 "R" == .property 0 -- x3
#guard elaboratesToParameter p563_0 "R" == false -- x3
#guard selectOwnedDeclaration p563_0 "Algorithm" == .none -- x2
#guard elaboratesToParameter p563_0 "Algorithm" == false -- x2
#guard selectOwnedDeclaration p563_0 "Invoke" == .none
#guard elaboratesToParameter p563_0 "Invoke" == false

-- spec/call-reference-algorithm-loops: Step(x) = x + 1, x < 3 \n Loop(meta operation) = operation.Algorithm(operation.Arguments*).while \n  \n Step(0).Loop
def p564_0 : List OwnerLevel := { parameters := [], properties := ["Step", "Loop"] } :: prelude
def p564_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p564_0
def p564_2 : List OwnerLevel := { parameters := ["operation"], properties := [] } :: p564_0
#guard selectOwnedDeclaration p564_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p564_1 "x" == true -- x2
#guard selectOwnedDeclaration p564_2 "operation" == .parameter 0 -- x2
#guard elaboratesToParameter p564_2 "operation" == true -- x2
#guard selectOwnedDeclaration p564_2 "Algorithm" == .none
#guard elaboratesToParameter p564_2 "Algorithm" == false
#guard selectOwnedDeclaration p564_2 "Arguments" == .none
#guard elaboratesToParameter p564_2 "Arguments" == false
#guard selectOwnedDeclaration p564_2 "while" == .property 2
#guard elaboratesToParameter p564_2 "while" == false
#guard selectOwnedDeclaration p564_0 "Step" == .property 0
#guard elaboratesToParameter p564_0 "Step" == false
#guard selectOwnedDeclaration p564_0 "Loop" == .property 0
#guard elaboratesToParameter p564_0 "Loop" == false

-- spec/algorithm-is-not-an-extension-call: Algorithm(r) = r + 1 \n Algorithm(4)
def p565_0 : List OwnerLevel := { parameters := [], properties := ["Algorithm"] } :: prelude
def p565_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p565_0
#guard selectOwnedDeclaration p565_1 "r" == .parameter 0
#guard elaboratesToParameter p565_1 "r" == true
#guard selectOwnedDeclaration p565_0 "Algorithm" == .property 0
#guard elaboratesToParameter p565_0 "Algorithm" == false

-- spec/algorithm-projection-cycle: Hold(g) = Capture(g(0)) \n Capture(meta op) = op \n R = Hold(R.Algorithm) \n R.Algorithm(1)
def p566_0 : List OwnerLevel := { parameters := [], properties := ["R", "Hold", "Capture"] } :: prelude
def p566_1 : List OwnerLevel := { parameters := [], properties := [] } :: p566_0
def p566_2 : List OwnerLevel := { parameters := ["g"], properties := [] } :: p566_0
def p566_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p566_0
#guard selectOwnedDeclaration p566_1 "Hold" == .property 1
#guard elaboratesToParameter p566_1 "Hold" == false
#guard selectOwnedDeclaration p566_1 "R" == .property 1
#guard elaboratesToParameter p566_1 "R" == false
#guard selectOwnedDeclaration p566_1 "Algorithm" == .none
#guard elaboratesToParameter p566_1 "Algorithm" == false
#guard selectOwnedDeclaration p566_2 "Capture" == .property 1
#guard elaboratesToParameter p566_2 "Capture" == false
#guard selectOwnedDeclaration p566_2 "g" == .parameter 0
#guard elaboratesToParameter p566_2 "g" == true
#guard selectOwnedDeclaration p566_3 "op" == .parameter 0
#guard elaboratesToParameter p566_3 "op" == true
#guard selectOwnedDeclaration p566_0 "R" == .property 0
#guard elaboratesToParameter p566_0 "R" == false
#guard selectOwnedDeclaration p566_0 "Algorithm" == .none
#guard elaboratesToParameter p566_0 "Algorithm" == false

-- spec/runtime-alias-of-a-parameter: Square(x) = x * x \n Apply(f, x) = f(x) \n Use(f) = { \n     A = f \n     A(9), 2.A, Apply(A, 4) \n } \n  \n Use(Square)
def p567_0 : List OwnerLevel := { parameters := [], properties := ["Square", "Apply", "Use"] } :: prelude
def p567_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p567_0
def p567_2 : List OwnerLevel := { parameters := ["f", "x"], properties := [] } :: p567_0
def p567_3 : List OwnerLevel := { parameters := ["f"], properties := ["A"] } :: p567_0
def p567_4 : List OwnerLevel := { parameters := [], properties := [] } :: p567_3
#guard selectOwnedDeclaration p567_1 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p567_1 "x" == true -- x2
#guard selectOwnedDeclaration p567_2 "f" == .parameter 0
#guard elaboratesToParameter p567_2 "f" == true
#guard selectOwnedDeclaration p567_2 "x" == .parameter 0
#guard elaboratesToParameter p567_2 "x" == true
#guard selectOwnedDeclaration p567_4 "f" == .parameter 1
#guard elaboratesToParameter p567_4 "f" == true
#guard selectOwnedDeclaration p567_3 "A" == .property 0 -- x3
#guard elaboratesToParameter p567_3 "A" == false -- x3
#guard selectOwnedDeclaration p567_3 "Apply" == .property 1
#guard elaboratesToParameter p567_3 "Apply" == false
#guard selectOwnedDeclaration p567_0 "Use" == .property 0
#guard elaboratesToParameter p567_0 "Use" == false
#guard selectOwnedDeclaration p567_0 "Square" == .property 0
#guard elaboratesToParameter p567_0 "Square" == false

-- spec/runtime-alias-of-a-projection: Square(x) = x * x \n Capture(meta op) = op \n R = Capture(Square(5)) \n A = R.Algorithm \n B = A \n  \n A(9) \n B(3) \n [1, 2].map(A)
def p568_0 : List OwnerLevel := { parameters := [], properties := ["R", "A", "B", "Square", "Capture"] } :: prelude
def p568_1 : List OwnerLevel := { parameters := [], properties := [] } :: p568_0
def p568_2 : List OwnerLevel := { parameters := [], properties := [] } :: p568_0
def p568_3 : List OwnerLevel := { parameters := [], properties := [] } :: p568_0
def p568_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p568_0
def p568_5 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p568_0
#guard selectOwnedDeclaration p568_1 "Capture" == .property 1
#guard elaboratesToParameter p568_1 "Capture" == false
#guard selectOwnedDeclaration p568_1 "Square" == .property 1
#guard elaboratesToParameter p568_1 "Square" == false
#guard selectOwnedDeclaration p568_2 "R" == .property 1
#guard elaboratesToParameter p568_2 "R" == false
#guard selectOwnedDeclaration p568_2 "Algorithm" == .none
#guard elaboratesToParameter p568_2 "Algorithm" == false
#guard selectOwnedDeclaration p568_3 "A" == .property 1
#guard elaboratesToParameter p568_3 "A" == false
#guard selectOwnedDeclaration p568_4 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p568_4 "x" == true -- x2
#guard selectOwnedDeclaration p568_5 "op" == .parameter 0
#guard elaboratesToParameter p568_5 "op" == true
#guard selectOwnedDeclaration p568_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p568_0 "A" == false -- x2
#guard selectOwnedDeclaration p568_0 "B" == .property 0
#guard elaboratesToParameter p568_0 "B" == false
#guard selectOwnedDeclaration p568_0 "map" == .property 1
#guard elaboratesToParameter p568_0 "map" == false

-- spec/runtime-alias-of-a-parameter-member: G(o) = o + 100 \n Box = { G(x) = x * 10 } \n Use(b) = { \n     A = b.G \n     A(3) \n } \n  \n Use(Box)
def p569_0 : List OwnerLevel := { parameters := [], properties := ["Box", "G", "Use"] } :: prelude
def p569_1 : List OwnerLevel := { parameters := [], properties := ["G"] } :: p569_0
def p569_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p569_1
def p569_3 : List OwnerLevel := { parameters := ["o"], properties := [] } :: p569_0
def p569_4 : List OwnerLevel := { parameters := ["b"], properties := ["A"] } :: p569_0
def p569_5 : List OwnerLevel := { parameters := [], properties := [] } :: p569_4
#guard selectOwnedDeclaration p569_2 "x" == .parameter 0
#guard elaboratesToParameter p569_2 "x" == true
#guard selectOwnedDeclaration p569_3 "o" == .parameter 0
#guard elaboratesToParameter p569_3 "o" == true
#guard selectOwnedDeclaration p569_5 "b" == .parameter 1
#guard elaboratesToParameter p569_5 "b" == true
#guard selectOwnedDeclaration p569_5 "G" == .property 2
#guard elaboratesToParameter p569_5 "G" == false
#guard selectOwnedDeclaration p569_4 "A" == .property 0
#guard elaboratesToParameter p569_4 "A" == false
#guard selectOwnedDeclaration p569_0 "Use" == .property 0
#guard elaboratesToParameter p569_0 "Use" == false
#guard selectOwnedDeclaration p569_0 "Box" == .property 0
#guard elaboratesToParameter p569_0 "Box" == false

-- spec/runtime-alias-transport-reads-the-target-members: Lib(*xs) = { \n     public K = 99 \n     0 \n } \n K(v) = 7 \n Navigate(f) = f.K \n Use(f) = { \n     A = f \n     Navigate(A), A.K \n } \n  \n Use(Lib)
def p570_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "K", "Navigate", "Use"] } :: prelude
def p570_1 : List OwnerLevel := { parameters := ["xs"], properties := ["K"] } :: p570_0
def p570_2 : List OwnerLevel := { parameters := [], properties := [] } :: p570_1
def p570_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p570_0
def p570_4 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p570_0
def p570_5 : List OwnerLevel := { parameters := ["f"], properties := ["A"] } :: p570_0
def p570_6 : List OwnerLevel := { parameters := [], properties := [] } :: p570_5
#guard selectOwnedDeclaration p570_4 "f" == .parameter 0
#guard elaboratesToParameter p570_4 "f" == true
#guard selectOwnedDeclaration p570_4 "K" == .property 1
#guard elaboratesToParameter p570_4 "K" == false
#guard selectOwnedDeclaration p570_6 "f" == .parameter 1
#guard elaboratesToParameter p570_6 "f" == true
#guard selectOwnedDeclaration p570_5 "Navigate" == .property 1
#guard elaboratesToParameter p570_5 "Navigate" == false
#guard selectOwnedDeclaration p570_5 "A" == .property 0 -- x2
#guard elaboratesToParameter p570_5 "A" == false -- x2
#guard selectOwnedDeclaration p570_5 "K" == .property 1
#guard elaboratesToParameter p570_5 "K" == false
#guard selectOwnedDeclaration p570_0 "Use" == .property 0
#guard elaboratesToParameter p570_0 "Use" == false
#guard selectOwnedDeclaration p570_0 "Lib" == .property 0
#guard elaboratesToParameter p570_0 "Lib" == false

-- spec/runtime-alias-namespace-of-its-own-declarations: Outer(n) = { \n     Lib = { public X = 10 \n     n } \n     P = { open Lib \n     X } \n     P + Lib \n } \n  \n Outer(1)
def p571_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
def p571_1 : List OwnerLevel := { parameters := ["n"], properties := ["Lib", "P"] } :: p571_0
def p571_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p571_1
def p571_3 : List OwnerLevel := { parameters := [], properties := [] } :: p571_2
def p571_4 : List OwnerLevel := { parameters := [], properties := [] } :: p571_1
#guard selectOwnedDeclaration p571_2 "n" == .parameter 1
#guard elaboratesToParameter p571_2 "n" == true
#guard selectOwnedDeclaration p571_4 "Lib" == .property 1
#guard openHead? (elaborateOpenHead p571_4 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p571_4 "X" == .none
#guard elaboratesToParameter p571_4 "X" == false
#guard selectOwnedDeclaration p571_1 "P" == .property 0
#guard elaboratesToParameter p571_1 "P" == false
#guard selectOwnedDeclaration p571_1 "Lib" == .property 0
#guard elaboratesToParameter p571_1 "Lib" == false
#guard selectOwnedDeclaration p571_0 "Outer" == .property 0
#guard elaboratesToParameter p571_0 "Outer" == false

-- spec/runtime-alias-failure-is-not-absence: R = 5 \n A = R.Algorithm \n  \n A(9)
def p572_0 : List OwnerLevel := { parameters := [], properties := ["R", "A"] } :: prelude
def p572_1 : List OwnerLevel := { parameters := [], properties := [] } :: p572_0
def p572_2 : List OwnerLevel := { parameters := [], properties := [] } :: p572_0
#guard selectOwnedDeclaration p572_2 "R" == .property 1
#guard elaboratesToParameter p572_2 "R" == false
#guard selectOwnedDeclaration p572_2 "Algorithm" == .none
#guard elaboratesToParameter p572_2 "Algorithm" == false
#guard selectOwnedDeclaration p572_0 "A" == .property 0
#guard elaboratesToParameter p572_0 "A" == false

-- spec/runtime-alias-cycle: Capture(meta op) = op \n A = R.Algorithm \n R = Capture(A(1)) \n  \n A(2)
def p573_0 : List OwnerLevel := { parameters := [], properties := ["A", "R", "Capture"] } :: prelude
def p573_1 : List OwnerLevel := { parameters := [], properties := [] } :: p573_0
def p573_2 : List OwnerLevel := { parameters := [], properties := [] } :: p573_0
def p573_3 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p573_0
#guard selectOwnedDeclaration p573_1 "R" == .property 1
#guard elaboratesToParameter p573_1 "R" == false
#guard selectOwnedDeclaration p573_1 "Algorithm" == .none
#guard elaboratesToParameter p573_1 "Algorithm" == false
#guard selectOwnedDeclaration p573_2 "Capture" == .property 1
#guard elaboratesToParameter p573_2 "Capture" == false
#guard selectOwnedDeclaration p573_2 "A" == .property 1
#guard elaboratesToParameter p573_2 "A" == false
#guard selectOwnedDeclaration p573_3 "op" == .parameter 0
#guard elaboratesToParameter p573_3 "op" == true
#guard selectOwnedDeclaration p573_0 "A" == .property 0
#guard elaboratesToParameter p573_0 "A" == false

-- spec/runtime-alias-cell-read-and-path-share-one-call: G(x) = tick() + x * 0 \n F(b) = { \n     B = { \n         public A = b.G \n         A + 0 \n     } \n     B.A, B \n } \n  \n F(5)
def p574_0 : List OwnerLevel := { parameters := [], properties := ["G", "F"] } :: prelude
def p574_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p574_0
def p574_2 : List OwnerLevel := { parameters := ["b"], properties := ["B"] } :: p574_0
def p574_3 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p574_2
def p574_4 : List OwnerLevel := { parameters := [], properties := [] } :: p574_3
#guard selectOwnedDeclaration p574_1 "tick" == .property 2
#guard elaboratesToParameter p574_1 "tick" == false
#guard selectOwnedDeclaration p574_1 "x" == .parameter 0
#guard elaboratesToParameter p574_1 "x" == true
#guard selectOwnedDeclaration p574_4 "b" == .parameter 2
#guard elaboratesToParameter p574_4 "b" == true
#guard selectOwnedDeclaration p574_4 "G" == .property 3
#guard elaboratesToParameter p574_4 "G" == false
#guard selectOwnedDeclaration p574_3 "A" == .property 0
#guard elaboratesToParameter p574_3 "A" == false
#guard selectOwnedDeclaration p574_2 "B" == .property 0 -- x2
#guard elaboratesToParameter p574_2 "B" == false -- x2
#guard selectOwnedDeclaration p574_2 "A" == .none
#guard elaboratesToParameter p574_2 "A" == false
#guard selectOwnedDeclaration p574_0 "F" == .property 0
#guard elaboratesToParameter p574_0 "F" == false

-- spec/runtime-alias-cell-explicit-call-is-fresh: G(x) = tick() + x * 0 \n F(b) = { \n     B = { \n         public A = b.G \n         A + 0 \n     } \n     B, B, B.A, B.A, B(), B.A \n } \n  \n F(5)
def p575_0 : List OwnerLevel := { parameters := [], properties := ["G", "F"] } :: prelude
def p575_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p575_0
def p575_2 : List OwnerLevel := { parameters := ["b"], properties := ["B"] } :: p575_0
def p575_3 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p575_2
def p575_4 : List OwnerLevel := { parameters := [], properties := [] } :: p575_3
#guard selectOwnedDeclaration p575_1 "tick" == .property 2
#guard elaboratesToParameter p575_1 "tick" == false
#guard selectOwnedDeclaration p575_1 "x" == .parameter 0
#guard elaboratesToParameter p575_1 "x" == true
#guard selectOwnedDeclaration p575_4 "b" == .parameter 2
#guard elaboratesToParameter p575_4 "b" == true
#guard selectOwnedDeclaration p575_4 "G" == .property 3
#guard elaboratesToParameter p575_4 "G" == false
#guard selectOwnedDeclaration p575_3 "A" == .property 0
#guard elaboratesToParameter p575_3 "A" == false
#guard selectOwnedDeclaration p575_2 "B" == .property 0 -- x6
#guard elaboratesToParameter p575_2 "B" == false -- x6
#guard selectOwnedDeclaration p575_2 "A" == .none -- x3
#guard elaboratesToParameter p575_2 "A" == false -- x3
#guard selectOwnedDeclaration p575_0 "F" == .property 0
#guard elaboratesToParameter p575_0 "F" == false

-- spec/runtime-alias-cell-one-per-run-across-calls: Cap(meta r) = r \n Ten(x) = x * 10 \n Hun(x) = x * 100 \n Pick(n) = if(n == 1, Cap(Ten(0)), Cap(Hun(0))) \n Outer(k) = { \n     A = Pick(tick()).Algorithm \n     A(1) \n } \n  \n Outer(0) \n Outer(0)
def p576_0 : List OwnerLevel := { parameters := [], properties := ["Cap", "Ten", "Hun", "Pick", "Outer"] } :: prelude
def p576_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p576_0
def p576_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p576_0
def p576_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p576_0
def p576_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p576_0
def p576_5 : List OwnerLevel := { parameters := ["k"], properties := ["A"] } :: p576_0
def p576_6 : List OwnerLevel := { parameters := [], properties := [] } :: p576_5
#guard selectOwnedDeclaration p576_1 "r" == .parameter 0
#guard elaboratesToParameter p576_1 "r" == true
#guard selectOwnedDeclaration p576_2 "x" == .parameter 0
#guard elaboratesToParameter p576_2 "x" == true
#guard selectOwnedDeclaration p576_3 "x" == .parameter 0
#guard elaboratesToParameter p576_3 "x" == true
#guard selectOwnedDeclaration p576_4 "if" == .property 2
#guard elaboratesToParameter p576_4 "if" == false
#guard selectOwnedDeclaration p576_4 "n" == .parameter 0
#guard elaboratesToParameter p576_4 "n" == true
#guard selectOwnedDeclaration p576_4 "Cap" == .property 1 -- x2
#guard elaboratesToParameter p576_4 "Cap" == false -- x2
#guard selectOwnedDeclaration p576_4 "Ten" == .property 1
#guard elaboratesToParameter p576_4 "Ten" == false
#guard selectOwnedDeclaration p576_4 "Hun" == .property 1
#guard elaboratesToParameter p576_4 "Hun" == false
#guard selectOwnedDeclaration p576_6 "Pick" == .property 2
#guard elaboratesToParameter p576_6 "Pick" == false
#guard selectOwnedDeclaration p576_6 "tick" == .property 3
#guard elaboratesToParameter p576_6 "tick" == false
#guard selectOwnedDeclaration p576_6 "Algorithm" == .none
#guard elaboratesToParameter p576_6 "Algorithm" == false
#guard selectOwnedDeclaration p576_5 "A" == .property 0
#guard elaboratesToParameter p576_5 "A" == false
#guard selectOwnedDeclaration p576_0 "Outer" == .property 0 -- x2
#guard elaboratesToParameter p576_0 "Outer" == false -- x2

-- spec/runtime-alias-cell-unused-sibling-changes-nothing: Cap(meta r) = r \n Ten(x) = x * 10 \n Hun(x) = x * 100 \n Pick(n) = if(n == 1, Cap(Ten(0)), Cap(Hun(0))) \n F(k) = { \n     Outer = { \n         U = k + 0 \n         A = Pick(tick()).Algorithm \n         A(1) \n     } \n     Outer(), Outer() \n } \n  \n F(0)
def p577_0 : List OwnerLevel := { parameters := [], properties := ["Cap", "Ten", "Hun", "Pick", "F"] } :: prelude
def p577_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p577_0
def p577_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p577_0
def p577_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p577_0
def p577_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p577_0
def p577_5 : List OwnerLevel := { parameters := ["k"], properties := ["Outer"] } :: p577_0
def p577_6 : List OwnerLevel := { parameters := [], properties := ["U", "A"] } :: p577_5
def p577_7 : List OwnerLevel := { parameters := [], properties := [] } :: p577_6
def p577_8 : List OwnerLevel := { parameters := [], properties := [] } :: p577_6
#guard selectOwnedDeclaration p577_1 "r" == .parameter 0
#guard elaboratesToParameter p577_1 "r" == true
#guard selectOwnedDeclaration p577_2 "x" == .parameter 0
#guard elaboratesToParameter p577_2 "x" == true
#guard selectOwnedDeclaration p577_3 "x" == .parameter 0
#guard elaboratesToParameter p577_3 "x" == true
#guard selectOwnedDeclaration p577_4 "if" == .property 2
#guard elaboratesToParameter p577_4 "if" == false
#guard selectOwnedDeclaration p577_4 "n" == .parameter 0
#guard elaboratesToParameter p577_4 "n" == true
#guard selectOwnedDeclaration p577_4 "Cap" == .property 1 -- x2
#guard elaboratesToParameter p577_4 "Cap" == false -- x2
#guard selectOwnedDeclaration p577_4 "Ten" == .property 1
#guard elaboratesToParameter p577_4 "Ten" == false
#guard selectOwnedDeclaration p577_4 "Hun" == .property 1
#guard elaboratesToParameter p577_4 "Hun" == false
#guard selectOwnedDeclaration p577_7 "k" == .parameter 2
#guard elaboratesToParameter p577_7 "k" == true
#guard selectOwnedDeclaration p577_8 "Pick" == .property 3
#guard elaboratesToParameter p577_8 "Pick" == false
#guard selectOwnedDeclaration p577_8 "tick" == .property 4
#guard elaboratesToParameter p577_8 "tick" == false
#guard selectOwnedDeclaration p577_8 "Algorithm" == .none
#guard elaboratesToParameter p577_8 "Algorithm" == false
#guard selectOwnedDeclaration p577_6 "A" == .property 0
#guard elaboratesToParameter p577_6 "A" == false
#guard selectOwnedDeclaration p577_5 "Outer" == .property 0 -- x2
#guard elaboratesToParameter p577_5 "Outer" == false -- x2
#guard selectOwnedDeclaration p577_0 "F" == .property 0
#guard elaboratesToParameter p577_0 "F" == false

-- spec/runtime-alias-cell-read-from-outside-after-a-call: Cap(meta r) = r \n Ten(x) = x * 10 \n Hun(x) = x * 100 \n Pick(n) = if(n == 1, Cap(Ten(0)), Cap(Hun(0))) \n Outer(k) = { \n     public A = Pick(tick()).Algorithm \n     A(1) \n } \n  \n Outer(0) \n Outer.A(1)
def p578_0 : List OwnerLevel := { parameters := [], properties := ["Cap", "Ten", "Hun", "Pick", "Outer"] } :: prelude
def p578_1 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p578_0
def p578_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p578_0
def p578_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p578_0
def p578_4 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p578_0
def p578_5 : List OwnerLevel := { parameters := ["k"], properties := ["A"] } :: p578_0
def p578_6 : List OwnerLevel := { parameters := [], properties := [] } :: p578_5
#guard selectOwnedDeclaration p578_1 "r" == .parameter 0
#guard elaboratesToParameter p578_1 "r" == true
#guard selectOwnedDeclaration p578_2 "x" == .parameter 0
#guard elaboratesToParameter p578_2 "x" == true
#guard selectOwnedDeclaration p578_3 "x" == .parameter 0
#guard elaboratesToParameter p578_3 "x" == true
#guard selectOwnedDeclaration p578_4 "if" == .property 2
#guard elaboratesToParameter p578_4 "if" == false
#guard selectOwnedDeclaration p578_4 "n" == .parameter 0
#guard elaboratesToParameter p578_4 "n" == true
#guard selectOwnedDeclaration p578_4 "Cap" == .property 1 -- x2
#guard elaboratesToParameter p578_4 "Cap" == false -- x2
#guard selectOwnedDeclaration p578_4 "Ten" == .property 1
#guard elaboratesToParameter p578_4 "Ten" == false
#guard selectOwnedDeclaration p578_4 "Hun" == .property 1
#guard elaboratesToParameter p578_4 "Hun" == false
#guard selectOwnedDeclaration p578_6 "Pick" == .property 2
#guard elaboratesToParameter p578_6 "Pick" == false
#guard selectOwnedDeclaration p578_6 "tick" == .property 3
#guard elaboratesToParameter p578_6 "tick" == false
#guard selectOwnedDeclaration p578_6 "Algorithm" == .none
#guard elaboratesToParameter p578_6 "Algorithm" == false
#guard selectOwnedDeclaration p578_5 "A" == .property 0
#guard elaboratesToParameter p578_5 "A" == false
#guard selectOwnedDeclaration p578_0 "Outer" == .property 0 -- x2
#guard elaboratesToParameter p578_0 "Outer" == false -- x2
#guard selectOwnedDeclaration p578_0 "A" == .none
#guard elaboratesToParameter p578_0 "A" == false

-- spec/runtime-alias-self-link-is-a-demand-cycle: A = A.Algorithm \n  \n A
def p579_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p579_1 : List OwnerLevel := { parameters := [], properties := [] } :: p579_0
#guard selectOwnedDeclaration p579_1 "A" == .property 1
#guard elaboratesToParameter p579_1 "A" == false
#guard selectOwnedDeclaration p579_1 "Algorithm" == .none
#guard elaboratesToParameter p579_1 "Algorithm" == false
#guard selectOwnedDeclaration p579_0 "A" == .property 0
#guard elaboratesToParameter p579_0 "A" == false

-- spec/reference-head-resolves-in-its-own-scope: Lib = { public Inc(x) = x + 1 } \n A = Lib \n F = { \n     open A \n     Lib = { public Dec(x) = x - 1 } \n     G = Inc \n     G(5) \n } \n  \n F
def p580_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A", "F"] } :: prelude
def p580_1 : List OwnerLevel := { parameters := [], properties := ["Inc"] } :: p580_0
def p580_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p580_1
def p580_3 : List OwnerLevel := { parameters := [], properties := [] } :: p580_0
def p580_4 : List OwnerLevel := { parameters := [], properties := ["Lib", "G"] } :: p580_0
def p580_5 : List OwnerLevel := { parameters := [], properties := ["Dec"] } :: p580_4
def p580_6 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p580_5
def p580_7 : List OwnerLevel := { parameters := [], properties := [] } :: p580_4
#guard selectOwnedDeclaration p580_2 "x" == .parameter 0
#guard elaboratesToParameter p580_2 "x" == true
#guard selectOwnedDeclaration p580_3 "Lib" == .property 1
#guard elaboratesToParameter p580_3 "Lib" == false
#guard selectOwnedDeclaration p580_4 "A" == .property 1
#guard openHead? (elaborateOpenHead p580_4 "A") == some (false, "A")
#guard selectOwnedDeclaration p580_6 "x" == .parameter 0
#guard elaboratesToParameter p580_6 "x" == true
#guard selectOwnedDeclaration p580_7 "Inc" == .none
#guard elaboratesToParameter p580_7 "Inc" == false
#guard selectOwnedDeclaration p580_4 "G" == .property 0
#guard elaboratesToParameter p580_4 "G" == false
#guard selectOwnedDeclaration p580_0 "F" == .property 0
#guard elaboratesToParameter p580_0 "F" == false

-- spec/reference-receiver-is-its-target-structure: Lib = { \n     Defaults = { public Rate = 2 } \n     public Cfg = Defaults \n } \n Tax = Lib.Cfg.Rate * 100 \n  \n Tax
def p581_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Tax"] } :: prelude
def p581_1 : List OwnerLevel := { parameters := [], properties := ["Defaults", "Cfg"] } :: p581_0
def p581_2 : List OwnerLevel := { parameters := [], properties := ["Rate"] } :: p581_1
def p581_3 : List OwnerLevel := { parameters := [], properties := [] } :: p581_2
def p581_4 : List OwnerLevel := { parameters := [], properties := [] } :: p581_1
def p581_5 : List OwnerLevel := { parameters := [], properties := [] } :: p581_0
#guard selectOwnedDeclaration p581_4 "Defaults" == .property 1
#guard elaboratesToParameter p581_4 "Defaults" == false
#guard selectOwnedDeclaration p581_5 "Lib" == .property 1
#guard elaboratesToParameter p581_5 "Lib" == false
#guard selectOwnedDeclaration p581_5 "Cfg" == .none
#guard elaboratesToParameter p581_5 "Cfg" == false
#guard selectOwnedDeclaration p581_5 "Rate" == .none
#guard elaboratesToParameter p581_5 "Rate" == false
#guard selectOwnedDeclaration p581_0 "Tax" == .property 0
#guard elaboratesToParameter p581_0 "Tax" == false

-- spec/block-headed-reference-navigates-its-block: A = { \n     V = { public W = 7 } \n     K = V \n }.K \n  \n A.W
def p582_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p582_1 : List OwnerLevel := { parameters := [], properties := [] } :: p582_0
def p582_2 : List OwnerLevel := { parameters := [], properties := ["V", "K"] } :: p582_1
def p582_3 : List OwnerLevel := { parameters := [], properties := ["W"] } :: p582_2
def p582_4 : List OwnerLevel := { parameters := [], properties := [] } :: p582_3
def p582_5 : List OwnerLevel := { parameters := [], properties := [] } :: p582_2
#guard selectOwnedDeclaration p582_5 "V" == .property 1
#guard elaboratesToParameter p582_5 "V" == false
#guard selectOwnedDeclaration p582_1 "K" == .none
#guard elaboratesToParameter p582_1 "K" == false
#guard selectOwnedDeclaration p582_0 "A" == .property 0
#guard elaboratesToParameter p582_0 "A" == false
#guard selectOwnedDeclaration p582_0 "W" == .none
#guard elaboratesToParameter p582_0 "W" == false

-- spec/reference-behind-a-carrier-that-reads-it-back: A = B \n B = { \n     public F(x) = x * x \n     A.F \n } \n  \n A(3)
def p583_0 : List OwnerLevel := { parameters := [], properties := ["A", "B"] } :: prelude
def p583_1 : List OwnerLevel := { parameters := [], properties := [] } :: p583_0
def p583_2 : List OwnerLevel := { parameters := [], properties := ["F"] } :: p583_0
def p583_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p583_2
#guard selectOwnedDeclaration p583_1 "B" == .property 1
#guard elaboratesToParameter p583_1 "B" == false
#guard selectOwnedDeclaration p583_3 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p583_3 "x" == true -- x2
#guard selectOwnedDeclaration p583_2 "A" == .property 1
#guard elaboratesToParameter p583_2 "A" == false
#guard selectOwnedDeclaration p583_2 "F" == .property 0
#guard elaboratesToParameter p583_2 "F" == false
#guard selectOwnedDeclaration p583_0 "A" == .property 0
#guard elaboratesToParameter p583_0 "A" == false

-- spec/reference-through-a-carrier-reads-the-carriers-member: Settings = Config \n Config = { \n     public Rate = 2 \n     Default \n } \n Default = Settings.Rate \n  \n Settings
def p584_0 : List OwnerLevel := { parameters := [], properties := ["Settings", "Config", "Default"] } :: prelude
def p584_1 : List OwnerLevel := { parameters := [], properties := [] } :: p584_0
def p584_2 : List OwnerLevel := { parameters := [], properties := ["Rate"] } :: p584_0
def p584_3 : List OwnerLevel := { parameters := [], properties := [] } :: p584_2
def p584_4 : List OwnerLevel := { parameters := [], properties := [] } :: p584_0
#guard selectOwnedDeclaration p584_1 "Config" == .property 1
#guard elaboratesToParameter p584_1 "Config" == false
#guard selectOwnedDeclaration p584_2 "Default" == .property 1
#guard elaboratesToParameter p584_2 "Default" == false
#guard selectOwnedDeclaration p584_4 "Settings" == .property 1
#guard elaboratesToParameter p584_4 "Settings" == false
#guard selectOwnedDeclaration p584_4 "Rate" == .none
#guard elaboratesToParameter p584_4 "Rate" == false
#guard selectOwnedDeclaration p584_0 "Settings" == .property 0
#guard elaboratesToParameter p584_0 "Settings" == false

-- spec/same-shape-references-are-distinct-bindings: Primary = Config \n Backup = Config \n Config = { \n     public Rate = 2 \n     Backup.Rate \n } \n  \n Primary
def p585_0 : List OwnerLevel := { parameters := [], properties := ["Primary", "Backup", "Config"] } :: prelude
def p585_1 : List OwnerLevel := { parameters := [], properties := [] } :: p585_0
def p585_2 : List OwnerLevel := { parameters := [], properties := [] } :: p585_0
def p585_3 : List OwnerLevel := { parameters := [], properties := ["Rate"] } :: p585_0
def p585_4 : List OwnerLevel := { parameters := [], properties := [] } :: p585_3
#guard selectOwnedDeclaration p585_1 "Config" == .property 1
#guard elaboratesToParameter p585_1 "Config" == false
#guard selectOwnedDeclaration p585_2 "Config" == .property 1
#guard elaboratesToParameter p585_2 "Config" == false
#guard selectOwnedDeclaration p585_3 "Backup" == .property 1
#guard elaboratesToParameter p585_3 "Backup" == false
#guard selectOwnedDeclaration p585_3 "Rate" == .property 0
#guard elaboratesToParameter p585_3 "Rate" == false
#guard selectOwnedDeclaration p585_0 "Primary" == .property 0
#guard elaboratesToParameter p585_0 "Primary" == false

-- spec/algorithm-member-of-a-reference-behind-a-carrier: P = C \n C = { \n     public Algorithm = 5 \n     A \n } \n A = P.Algorithm \n  \n P
def p586_0 : List OwnerLevel := { parameters := [], properties := ["P", "C", "A"] } :: prelude
def p586_1 : List OwnerLevel := { parameters := [], properties := [] } :: p586_0
def p586_2 : List OwnerLevel := { parameters := [], properties := ["Algorithm"] } :: p586_0
def p586_3 : List OwnerLevel := { parameters := [], properties := [] } :: p586_2
def p586_4 : List OwnerLevel := { parameters := [], properties := [] } :: p586_0
#guard selectOwnedDeclaration p586_1 "C" == .property 1
#guard elaboratesToParameter p586_1 "C" == false
#guard selectOwnedDeclaration p586_2 "A" == .property 1
#guard elaboratesToParameter p586_2 "A" == false
#guard selectOwnedDeclaration p586_4 "P" == .property 1
#guard elaboratesToParameter p586_4 "P" == false
#guard selectOwnedDeclaration p586_4 "Algorithm" == .none
#guard elaboratesToParameter p586_4 "Algorithm" == false
#guard selectOwnedDeclaration p586_0 "P" == .property 0
#guard elaboratesToParameter p586_0 "P" == false

-- spec/carrier-of-a-parameter-in-every-activation: Inc(x) = x + 1 \n F(f, n) = { \n     A = { f } \n     if(n == 0, A(5), F(A, n - 1)) \n } \n  \n F(Inc, 1)
def p587_0 : List OwnerLevel := { parameters := [], properties := ["Inc", "F"] } :: prelude
def p587_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p587_0
def p587_2 : List OwnerLevel := { parameters := ["f", "n"], properties := ["A"] } :: p587_0
def p587_3 : List OwnerLevel := { parameters := [], properties := [] } :: p587_2
#guard selectOwnedDeclaration p587_1 "x" == .parameter 0
#guard elaboratesToParameter p587_1 "x" == true
#guard selectOwnedDeclaration p587_3 "f" == .parameter 1
#guard elaboratesToParameter p587_3 "f" == true
#guard selectOwnedDeclaration p587_2 "if" == .property 2
#guard elaboratesToParameter p587_2 "if" == false
#guard selectOwnedDeclaration p587_2 "n" == .parameter 0 -- x2
#guard elaboratesToParameter p587_2 "n" == true -- x2
#guard selectOwnedDeclaration p587_2 "A" == .property 0 -- x2
#guard elaboratesToParameter p587_2 "A" == false -- x2
#guard selectOwnedDeclaration p587_2 "F" == .property 1
#guard elaboratesToParameter p587_2 "F" == false
#guard selectOwnedDeclaration p587_0 "F" == .property 0
#guard elaboratesToParameter p587_0 "F" == false
#guard selectOwnedDeclaration p587_0 "Inc" == .property 0
#guard elaboratesToParameter p587_0 "Inc" == false

-- spec/reference-cycle-through-an-open-is-no-alias: open Lib \n Lib = { public B = A } \n A = B \n Same(x, x) = 0 \n  \n Same(A, A)
def p588_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A", "Same"] } :: prelude
def p588_1 : List OwnerLevel := { parameters := [], properties := ["B"] } :: p588_0
def p588_2 : List OwnerLevel := { parameters := [], properties := [] } :: p588_1
def p588_3 : List OwnerLevel := { parameters := [], properties := [] } :: p588_0
def p588_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p588_0
#guard selectOwnedDeclaration p588_0 "Lib" == .property 0
#guard openHead? (elaborateOpenHead p588_0 "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p588_2 "A" == .property 2
#guard elaboratesToParameter p588_2 "A" == false
#guard selectOwnedDeclaration p588_3 "B" == .none
#guard elaboratesToParameter p588_3 "B" == false
#guard selectOwnedDeclaration p588_0 "Same" == .property 0
#guard elaboratesToParameter p588_0 "Same" == false
#guard selectOwnedDeclaration p588_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p588_0 "A" == false -- x2

-- spec/reference-to-a-carrier-that-leads-back-is-no-alias: A = B \n B = { \n     public X = 1 \n     A \n } \n G(p) = A.X \n  \n G(1)
def p589_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "G"] } :: prelude
def p589_1 : List OwnerLevel := { parameters := [], properties := [] } :: p589_0
def p589_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p589_0
def p589_3 : List OwnerLevel := { parameters := [], properties := [] } :: p589_2
def p589_4 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p589_0
#guard selectOwnedDeclaration p589_1 "B" == .property 1
#guard elaboratesToParameter p589_1 "B" == false
#guard selectOwnedDeclaration p589_2 "A" == .property 1
#guard elaboratesToParameter p589_2 "A" == false
#guard selectOwnedDeclaration p589_4 "A" == .property 1
#guard elaboratesToParameter p589_4 "A" == false
#guard selectOwnedDeclaration p589_4 "X" == .none
#guard elaboratesToParameter p589_4 "X" == false
#guard selectOwnedDeclaration p589_0 "G" == .property 0
#guard elaboratesToParameter p589_0 "G" == false

-- spec/sibling-cycle-member-path-is-read-statically: A = B.C \n B = Lib \n Lib = { \n     public C = { public X = 1 } \n     public D = A \n } \n  \n A.X
def p590_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "Lib"] } :: prelude
def p590_1 : List OwnerLevel := { parameters := [], properties := [] } :: p590_0
def p590_2 : List OwnerLevel := { parameters := [], properties := [] } :: p590_0
def p590_3 : List OwnerLevel := { parameters := [], properties := ["C", "D"] } :: p590_0
def p590_4 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p590_3
def p590_5 : List OwnerLevel := { parameters := [], properties := [] } :: p590_4
def p590_6 : List OwnerLevel := { parameters := [], properties := [] } :: p590_3
#guard selectOwnedDeclaration p590_1 "B" == .property 1
#guard elaboratesToParameter p590_1 "B" == false
#guard selectOwnedDeclaration p590_1 "C" == .none
#guard elaboratesToParameter p590_1 "C" == false
#guard selectOwnedDeclaration p590_2 "Lib" == .property 1
#guard elaboratesToParameter p590_2 "Lib" == false
#guard selectOwnedDeclaration p590_6 "A" == .property 2
#guard elaboratesToParameter p590_6 "A" == false
#guard selectOwnedDeclaration p590_0 "A" == .property 0
#guard elaboratesToParameter p590_0 "A" == false
#guard selectOwnedDeclaration p590_0 "X" == .none
#guard elaboratesToParameter p590_0 "X" == false

-- spec/open-block-member-reference-opens-its-target: open { \n     public Lib = { public K = 7 } \n     public A = Lib \n }.A \n  \n K
def p591_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
def p591_1 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p591_2 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p591_1
def p591_3 : List OwnerLevel := { parameters := [], properties := [] } :: p591_2
def p591_4 : List OwnerLevel := { parameters := [], properties := [] } :: p591_1
#guard selectOwnedDeclaration p591_4 "Lib" == .property 1
#guard elaboratesToParameter p591_4 "Lib" == false
#guard selectOwnedDeclaration p591_0 "K" == .none
#guard elaboratesToParameter p591_0 "K" == false

-- spec/block-receiver-reference-member: V = { public W = 7 } \n Y = { K = V }.K.W + 0 \n  \n Y
def p592_0 : List OwnerLevel := { parameters := [], properties := ["V", "Y"] } :: prelude
def p592_1 : List OwnerLevel := { parameters := [], properties := ["W"] } :: p592_0
def p592_2 : List OwnerLevel := { parameters := [], properties := [] } :: p592_1
def p592_3 : List OwnerLevel := { parameters := [], properties := [] } :: p592_0
def p592_4 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p592_3
def p592_5 : List OwnerLevel := { parameters := [], properties := [] } :: p592_4
#guard selectOwnedDeclaration p592_5 "V" == .property 3
#guard elaboratesToParameter p592_5 "V" == false
#guard selectOwnedDeclaration p592_3 "K" == .none
#guard elaboratesToParameter p592_3 "K" == false
#guard selectOwnedDeclaration p592_3 "W" == .none
#guard elaboratesToParameter p592_3 "W" == false
#guard selectOwnedDeclaration p592_0 "Y" == .property 0
#guard elaboratesToParameter p592_0 "Y" == false

-- spec/member-miss-makes-the-body-its-own-structure: B = { Q = 1 } \n A = B.foo \n G(p) = A.bar \n  \n G(1)
def p593_0 : List OwnerLevel := { parameters := [], properties := ["B", "A", "G"] } :: prelude
def p593_1 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p593_0
def p593_2 : List OwnerLevel := { parameters := [], properties := [] } :: p593_1
def p593_3 : List OwnerLevel := { parameters := ["foo"], properties := [] } :: p593_0
def p593_4 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p593_0
#guard selectOwnedDeclaration p593_3 "B" == .property 1
#guard elaboratesToParameter p593_3 "B" == false
#guard selectOwnedDeclaration p593_3 "foo" == .parameter 0
#guard elaboratesToParameter p593_3 "foo" == true
#guard selectOwnedDeclaration p593_4 "A" == .property 1
#guard elaboratesToParameter p593_4 "A" == false
#guard selectOwnedDeclaration p593_4 "bar" == .none
#guard elaboratesToParameter p593_4 "bar" == false
#guard selectOwnedDeclaration p593_0 "G" == .property 0
#guard elaboratesToParameter p593_0 "G" == false

-- spec/reference-cycle-only-the-final-providers-close-is-no-alias: open Back \n A = B \n B = { \n     public N = 5 \n     A \n } \n Back = { public N = G.Z } \n G = { \n     open A \n     public Z = N \n     0 \n } \n Same(x, x) = 0 \n  \n Same(G.Z, G.Z)
def p594_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "Back", "G", "Same"] } :: prelude
def p594_1 : List OwnerLevel := { parameters := [], properties := [] } :: p594_0
def p594_2 : List OwnerLevel := { parameters := [], properties := ["N"] } :: p594_0
def p594_3 : List OwnerLevel := { parameters := [], properties := [] } :: p594_2
def p594_4 : List OwnerLevel := { parameters := [], properties := ["N"] } :: p594_0
def p594_5 : List OwnerLevel := { parameters := [], properties := [] } :: p594_4
def p594_6 : List OwnerLevel := { parameters := [], properties := ["Z"] } :: p594_0
def p594_7 : List OwnerLevel := { parameters := [], properties := [] } :: p594_6
def p594_8 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p594_0
#guard selectOwnedDeclaration p594_0 "Back" == .property 0
#guard openHead? (elaborateOpenHead p594_0 "Back") == some (false, "Back")
#guard selectOwnedDeclaration p594_1 "B" == .property 1
#guard elaboratesToParameter p594_1 "B" == false
#guard selectOwnedDeclaration p594_2 "A" == .property 1
#guard elaboratesToParameter p594_2 "A" == false
#guard selectOwnedDeclaration p594_5 "G" == .property 2
#guard elaboratesToParameter p594_5 "G" == false
#guard selectOwnedDeclaration p594_5 "Z" == .none
#guard elaboratesToParameter p594_5 "Z" == false
#guard selectOwnedDeclaration p594_6 "A" == .property 1
#guard openHead? (elaborateOpenHead p594_6 "A") == some (false, "A")
#guard selectOwnedDeclaration p594_7 "N" == .none
#guard elaboratesToParameter p594_7 "N" == false
#guard selectOwnedDeclaration p594_0 "Same" == .property 0
#guard elaboratesToParameter p594_0 "Same" == false
#guard selectOwnedDeclaration p594_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p594_0 "G" == false -- x2
#guard selectOwnedDeclaration p594_0 "Z" == .none -- x2
#guard elaboratesToParameter p594_0 "Z" == false -- x2

-- spec/member-path-through-a-lower-cyclic-receiver-is-no-alias: X(v) = 0 \n A = B \n B = { \n     public X = D \n     A \n } \n D = { \n     public Q = 7 \n     A.X \n } \n E = D \n Same(x, x) = 0 \n  \n Same(E, D)
def p595_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "D", "E", "X", "Same"] } :: prelude
def p595_1 : List OwnerLevel := { parameters := [], properties := [] } :: p595_0
def p595_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p595_0
def p595_3 : List OwnerLevel := { parameters := [], properties := [] } :: p595_2
def p595_4 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p595_0
def p595_5 : List OwnerLevel := { parameters := [], properties := [] } :: p595_4
def p595_6 : List OwnerLevel := { parameters := [], properties := [] } :: p595_0
def p595_7 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p595_0
def p595_8 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p595_0
#guard selectOwnedDeclaration p595_1 "B" == .property 1
#guard elaboratesToParameter p595_1 "B" == false
#guard selectOwnedDeclaration p595_3 "D" == .property 2
#guard elaboratesToParameter p595_3 "D" == false
#guard selectOwnedDeclaration p595_2 "A" == .property 1
#guard elaboratesToParameter p595_2 "A" == false
#guard selectOwnedDeclaration p595_4 "A" == .property 1
#guard elaboratesToParameter p595_4 "A" == false
#guard selectOwnedDeclaration p595_4 "X" == .property 1
#guard elaboratesToParameter p595_4 "X" == false
#guard selectOwnedDeclaration p595_6 "D" == .property 1
#guard elaboratesToParameter p595_6 "D" == false
#guard selectOwnedDeclaration p595_0 "Same" == .property 0
#guard elaboratesToParameter p595_0 "Same" == false
#guard selectOwnedDeclaration p595_0 "E" == .property 0
#guard elaboratesToParameter p595_0 "E" == false
#guard selectOwnedDeclaration p595_0 "D" == .property 0
#guard elaboratesToParameter p595_0 "D" == false

-- spec/reference-head-is-the-parameter-its-own-scope-binds: F(x) = { \n     A = x \n     G(x) = A.W + 0 \n     G(5) \n } \n  \n F({ public W = 9 })
def p596_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
def p596_1 : List OwnerLevel := { parameters := ["x"], properties := ["A", "G"] } :: p596_0
def p596_2 : List OwnerLevel := { parameters := [], properties := [] } :: p596_1
def p596_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p596_1
def p596_4 : List OwnerLevel := { parameters := [], properties := ["W"] } :: p596_0
def p596_5 : List OwnerLevel := { parameters := [], properties := [] } :: p596_4
#guard selectOwnedDeclaration p596_2 "x" == .parameter 1
#guard elaboratesToParameter p596_2 "x" == true
#guard selectOwnedDeclaration p596_3 "A" == .property 1
#guard elaboratesToParameter p596_3 "A" == false
#guard selectOwnedDeclaration p596_3 "W" == .none
#guard elaboratesToParameter p596_3 "W" == false
#guard selectOwnedDeclaration p596_1 "G" == .property 0
#guard elaboratesToParameter p596_1 "G" == false
#guard selectOwnedDeclaration p596_0 "F" == .property 0
#guard elaboratesToParameter p596_0 "F" == false

-- spec/open-path-into-a-parameterized-body-is-its-own-namespace: p = { public K = 1 } \n Q(p) = { \n     public M = p \n     0 \n } \n F(z) = { \n     open Q.M \n     K \n } \n  \n F(1)
def p597_0 : List OwnerLevel := { parameters := [], properties := ["p", "Q", "F"] } :: prelude
def p597_1 : List OwnerLevel := { parameters := [], properties := ["K"] } :: p597_0
def p597_2 : List OwnerLevel := { parameters := [], properties := [] } :: p597_1
def p597_3 : List OwnerLevel := { parameters := ["p"], properties := ["M"] } :: p597_0
def p597_4 : List OwnerLevel := { parameters := [], properties := [] } :: p597_3
def p597_5 : List OwnerLevel := { parameters := ["z"], properties := [] } :: p597_0
#guard selectOwnedDeclaration p597_4 "p" == .parameter 1
#guard elaboratesToParameter p597_4 "p" == true
#guard selectOwnedDeclaration p597_5 "Q" == .property 1
#guard openHead? (elaborateOpenHead p597_5 "Q") == some (false, "Q")
#guard selectOwnedDeclaration p597_5 "K" == .none
#guard elaboratesToParameter p597_5 "K" == false
#guard selectOwnedDeclaration p597_0 "F" == .property 0
#guard elaboratesToParameter p597_0 "F" == false

-- spec/tick-counts-executions-in-the-run: tick(), tick(), tick()
def p598_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p598_0 "tick" == .property 1 -- x3
#guard elaboratesToParameter p598_0 "tick" == false -- x3

-- spec/tick-property-is-cached-call-is-fresh: A = tick() \n A(), A, A(), A
def p599_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p599_1 : List OwnerLevel := { parameters := [], properties := [] } :: p599_0
#guard selectOwnedDeclaration p599_1 "tick" == .property 2
#guard elaboratesToParameter p599_1 "tick" == false
#guard selectOwnedDeclaration p599_0 "A" == .property 0 -- x4
#guard elaboratesToParameter p599_0 "A" == false -- x4

-- spec/tick-argument-is-one-lazy-computation: Ignore(x) = 7 \n Twice(x) = x + x \n Ignore(tick()), Twice(tick()), tick()
def p600_0 : List OwnerLevel := { parameters := [], properties := ["Ignore", "Twice"] } :: prelude
def p600_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p600_0
def p600_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p600_0
#guard selectOwnedDeclaration p600_2 "x" == .parameter 0 -- x2
#guard elaboratesToParameter p600_2 "x" == true -- x2
#guard selectOwnedDeclaration p600_0 "Ignore" == .property 0
#guard elaboratesToParameter p600_0 "Ignore" == false
#guard selectOwnedDeclaration p600_0 "tick" == .property 1 -- x3
#guard elaboratesToParameter p600_0 "tick" == false -- x3
#guard selectOwnedDeclaration p600_0 "Twice" == .property 0
#guard elaboratesToParameter p600_0 "Twice" == false

-- spec/tick-callable-reference-is-not-an-execution: T = tick \n Apply(f) = f() \n T(), Apply(tick), tick()
def p601_0 : List OwnerLevel := { parameters := [], properties := ["T", "Apply"] } :: prelude
def p601_1 : List OwnerLevel := { parameters := [], properties := [] } :: p601_0
def p601_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p601_0
#guard selectOwnedDeclaration p601_1 "tick" == .property 2
#guard elaboratesToParameter p601_1 "tick" == false
#guard selectOwnedDeclaration p601_2 "f" == .parameter 0
#guard elaboratesToParameter p601_2 "f" == true
#guard selectOwnedDeclaration p601_0 "T" == .property 0
#guard elaboratesToParameter p601_0 "T" == false
#guard selectOwnedDeclaration p601_0 "Apply" == .property 0
#guard elaboratesToParameter p601_0 "Apply" == false
#guard selectOwnedDeclaration p601_0 "tick" == .property 1 -- x2
#guard elaboratesToParameter p601_0 "tick" == false -- x2

-- spec/tick-meta-replay-is-fresh: Replay(meta op) = op.Invoke() + op.Invoke() \n Replay(tick()), tick()
def p602_0 : List OwnerLevel := { parameters := [], properties := ["Replay"] } :: prelude
def p602_1 : List OwnerLevel := { parameters := ["op"], properties := [] } :: p602_0
#guard selectOwnedDeclaration p602_1 "op" == .parameter 0 -- x2
#guard elaboratesToParameter p602_1 "op" == true -- x2
#guard selectOwnedDeclaration p602_1 "Invoke" == .none -- x2
#guard elaboratesToParameter p602_1 "Invoke" == false -- x2
#guard selectOwnedDeclaration p602_0 "Replay" == .property 0
#guard elaboratesToParameter p602_0 "Replay" == false
#guard selectOwnedDeclaration p602_0 "tick" == .property 1 -- x2
#guard elaboratesToParameter p602_0 "tick" == false -- x2

-- spec/tick-bare-value-requires-invocation: tick + 1
-- the same levels and decisions, 1 more:
--   spec/tick-argument-is-an-arity-error
def p603_0 : List OwnerLevel := { parameters := [], properties := [] } :: prelude
#guard selectOwnedDeclaration p603_0 "tick" == .property 1
#guard elaboratesToParameter p603_0 "tick" == false

-- spec/tick-is-an-ordinary-shadowable-binding: tick(x) = x + 100 \n tick(1)
def p604_0 : List OwnerLevel := { parameters := [], properties := ["tick"] } :: prelude
def p604_1 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p604_0
#guard selectOwnedDeclaration p604_1 "x" == .parameter 0
#guard elaboratesToParameter p604_1 "x" == true
#guard selectOwnedDeclaration p604_0 "tick" == .property 0
#guard elaboratesToParameter p604_0 "tick" == false

-- spec/grouped-runtime-member-value-call: Use(v) = { \n     Box = { \n         public A = v \n         0 \n     } \n     (Box.A)() \n } \n Use(5)
-- the same levels and decisions, 1 more:
--   spec/grouped-runtime-member-value-arity
def p605_0 : List OwnerLevel := { parameters := [], properties := ["Use"] } :: prelude
def p605_1 : List OwnerLevel := { parameters := ["v"], properties := ["Box"] } :: p605_0
def p605_2 : List OwnerLevel := { parameters := [], properties := ["A"] } :: p605_1
def p605_3 : List OwnerLevel := { parameters := [], properties := [] } :: p605_2
#guard selectOwnedDeclaration p605_3 "v" == .parameter 2
#guard elaboratesToParameter p605_3 "v" == true
#guard selectOwnedDeclaration p605_1 "Box" == .property 0
#guard elaboratesToParameter p605_1 "Box" == false
#guard selectOwnedDeclaration p605_1 "A" == .none
#guard elaboratesToParameter p605_1 "A" == false
#guard selectOwnedDeclaration p605_0 "Use" == .property 0
#guard elaboratesToParameter p605_0 "Use" == false

-- spec/open-reference-private-member-provides-public-names: open A \n Lib = { \n     Sub = { \n         public Q(x) = x + 1 \n     } \n } \n A = Lib.Sub \n Q(5)
def p606_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "A"] } :: prelude
def p606_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p606_0
def p606_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p606_1
def p606_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p606_2
def p606_4 : List OwnerLevel := { parameters := [], properties := [] } :: p606_0
#guard selectOwnedDeclaration p606_0 "A" == .property 0
#guard openHead? (elaborateOpenHead p606_0 "A") == some (false, "A")
#guard selectOwnedDeclaration p606_3 "x" == .parameter 0
#guard elaboratesToParameter p606_3 "x" == true
#guard selectOwnedDeclaration p606_4 "Lib" == .property 1
#guard elaboratesToParameter p606_4 "Lib" == false
#guard selectOwnedDeclaration p606_4 "Sub" == .none
#guard elaboratesToParameter p606_4 "Sub" == false
#guard selectOwnedDeclaration p606_0 "Q" == .none
#guard elaboratesToParameter p606_0 "Q" == false

-- spec/open-reference-private-member-keeps-private-names: open Lib.Sub \n Lib = { \n     Sub = { \n         public Q(x) = x + 1 \n     } \n } \n Q(5)
def p607_0 : List OwnerLevel := { parameters := ["Q"], properties := ["Lib"] } :: prelude
def p607_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p607_0
def p607_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p607_1
def p607_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p607_2
def p607_0c : List OwnerLevel := { parameters := [], properties := ["Lib"] } :: prelude
#guard selectOwnedDeclaration p607_0c "Lib" == .property 0
#guard openHead? (elaborateOpenHead p607_0c "Lib") == some (false, "Lib")
#guard selectOwnedDeclaration p607_3 "x" == .parameter 0
#guard elaboratesToParameter p607_3 "x" == true
#guard selectOwnedDeclaration p607_0 "Q" == .parameter 0
#guard elaboratesToParameter p607_0 "Q" == true

-- spec/open-runtime-link-provides-its-own-namespace: Cap(meta r) = r \n Inc(x) = x + 1 \n L = Cap(Inc(1)).Algorithm \n K = { \n     open L \n     5 \n } \n K
def p608_0 : List OwnerLevel := { parameters := [], properties := ["L", "K", "Cap", "Inc"] } :: prelude
def p608_1 : List OwnerLevel := { parameters := [], properties := [] } :: p608_0
def p608_2 : List OwnerLevel := { parameters := [], properties := [] } :: p608_0
def p608_3 : List OwnerLevel := { parameters := ["r"], properties := [] } :: p608_0
def p608_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p608_0
#guard selectOwnedDeclaration p608_1 "Cap" == .property 1
#guard elaboratesToParameter p608_1 "Cap" == false
#guard selectOwnedDeclaration p608_1 "Inc" == .property 1
#guard elaboratesToParameter p608_1 "Inc" == false
#guard selectOwnedDeclaration p608_1 "Algorithm" == .none
#guard elaboratesToParameter p608_1 "Algorithm" == false
#guard selectOwnedDeclaration p608_2 "L" == .property 1
#guard openHead? (elaborateOpenHead p608_2 "L") == some (false, "L")
#guard selectOwnedDeclaration p608_3 "r" == .parameter 0
#guard elaboratesToParameter p608_3 "r" == true
#guard selectOwnedDeclaration p608_4 "x" == .parameter 0
#guard elaboratesToParameter p608_4 "x" == true
#guard selectOwnedDeclaration p608_0 "K" == .property 0
#guard elaboratesToParameter p608_0 "K" == false

-- spec/open-calculation-link-is-refused: Mk(t) = t + 1 \n L = Mk.Algorithm \n K = { \n     open L \n     5 \n } \n K
def p609_0 : List OwnerLevel := { parameters := [], properties := ["L", "K", "Mk"] } :: prelude
def p609_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["t"] } :: p609_0
def p609_2 : List OwnerLevel := { parameters := [], properties := [] } :: p609_0
def p609_3 : List OwnerLevel := { parameters := ["t"], properties := [] } :: p609_0
#guard selectOwnedDeclaration p609_1 "Mk" == .property 1
#guard elaboratesToParameter p609_1 "Mk" == false
#guard selectOwnedDeclaration p609_1 "Algorithm" == .none
#guard elaboratesToParameter p609_1 "Algorithm" == false
#guard selectOwnedDeclaration p609_2 "L" == .property 1
#guard openHead? (elaborateOpenHead p609_2 "L") == some (false, "L")
#guard selectOwnedDeclaration p609_3 "t" == .parameter 0
#guard elaboratesToParameter p609_3 "t" == true
#guard selectOwnedDeclaration p609_0 "K" == .property 0
#guard elaboratesToParameter p609_0 "K" == false

-- spec/open-reference-to-a-calculation-link-reports-the-target-refusal: Mk(t) = t + 1 \n L = Mk.Algorithm \n A = L \n K = { \n     open A \n     5 \n } \n K
def p610_0 : List OwnerLevel := { parameters := [], properties := ["L", "A", "K", "Mk"] } :: prelude
def p610_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["t"] } :: p610_0
def p610_2 : List OwnerLevel := { parameters := [], properties := [] } :: p610_0
def p610_3 : List OwnerLevel := { parameters := [], properties := [] } :: p610_0
def p610_4 : List OwnerLevel := { parameters := ["t"], properties := [] } :: p610_0
#guard selectOwnedDeclaration p610_1 "Mk" == .property 1
#guard elaboratesToParameter p610_1 "Mk" == false
#guard selectOwnedDeclaration p610_1 "Algorithm" == .none
#guard elaboratesToParameter p610_1 "Algorithm" == false
#guard selectOwnedDeclaration p610_2 "L" == .property 1
#guard elaboratesToParameter p610_2 "L" == false
#guard selectOwnedDeclaration p610_3 "A" == .property 1
#guard openHead? (elaborateOpenHead p610_3 "A") == some (false, "A")
#guard selectOwnedDeclaration p610_4 "t" == .parameter 0
#guard elaboratesToParameter p610_4 "t" == true
#guard selectOwnedDeclaration p610_0 "K" == .property 0
#guard elaboratesToParameter p610_0 "K" == false

-- spec/open-parameterized-fallback-row-is-refused: Add(x, y) = x + y \n L = Add.abs \n K = { \n     open L \n     5 \n } \n K
def p611_0 : List OwnerLevel := { parameters := [], properties := ["L", "K", "Add"] } :: prelude
def p611_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x", "y"] } :: p611_0
def p611_2 : List OwnerLevel := { parameters := [], properties := [] } :: p611_0
def p611_3 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p611_0
#guard selectOwnedDeclaration p611_1 "Add" == .property 1
#guard elaboratesToParameter p611_1 "Add" == false
#guard selectOwnedDeclaration p611_1 "abs" == .property 2
#guard elaboratesToParameter p611_1 "abs" == false
#guard selectOwnedDeclaration p611_2 "L" == .property 1
#guard openHead? (elaborateOpenHead p611_2 "L") == some (false, "L")
#guard selectOwnedDeclaration p611_3 "x" == .parameter 0
#guard elaboratesToParameter p611_3 "x" == true
#guard selectOwnedDeclaration p611_3 "y" == .parameter 0
#guard elaboratesToParameter p611_3 "y" == true
#guard selectOwnedDeclaration p611_0 "K" == .property 0
#guard elaboratesToParameter p611_0 "K" == false

-- spec/open-link-over-a-head-only-an-open-provides-is-unresolved: Q = { \n     public S = { \n         public X = 1 \n     } \n } \n K = { \n     open Q \n     L = S.Algorithm \n     M = { \n         open L \n         5 \n     } \n     M \n } \n K
def p612_0 : List OwnerLevel := { parameters := [], properties := ["Q", "K"] } :: prelude
def p612_1 : List OwnerLevel := { parameters := [], properties := ["S"] } :: p612_0
def p612_2 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p612_1
def p612_3 : List OwnerLevel := { parameters := [], properties := [] } :: p612_2
def p612_4 : List OwnerLevel := { parameters := [], properties := ["L", "M"] } :: p612_0
def p612_5 : List OwnerLevel := { parameters := [], properties := [] } :: p612_4
def p612_6 : List OwnerLevel := { parameters := [], properties := [] } :: p612_4
#guard selectOwnedDeclaration p612_4 "Q" == .property 1
#guard openHead? (elaborateOpenHead p612_4 "Q") == some (false, "Q")
#guard selectOwnedDeclaration p612_5 "S" == .none
#guard elaboratesToParameter p612_5 "S" == false
#guard selectOwnedDeclaration p612_5 "Algorithm" == .none
#guard elaboratesToParameter p612_5 "Algorithm" == false
#guard selectOwnedDeclaration p612_6 "L" == .property 1
#guard openHead? (elaborateOpenHead p612_6 "L") == some (false, "L")
#guard selectOwnedDeclaration p612_4 "M" == .property 0
#guard elaboratesToParameter p612_4 "M" == false
#guard selectOwnedDeclaration p612_0 "K" == .property 0
#guard elaboratesToParameter p612_0 "K" == false

-- spec/open-of-a-link-over-a-cyclic-head-compiles-in-every-order: P5 = { \n     open P3 \n     Z \n } \n P6 = P6 \n P3 = P6.Algorithm \n P5(1)
def p613_0 : List OwnerLevel := { parameters := [], properties := ["P5", "P6", "P3"] } :: prelude
def p613_1 : List OwnerLevel := { parameters := ["Z"], properties := [] } :: p613_0
def p613_2 : List OwnerLevel := { parameters := [], properties := [] } :: p613_0
def p613_3 : List OwnerLevel := { parameters := [], properties := [] } :: p613_0
#guard selectOwnedDeclaration p613_1 "P3" == .property 1
#guard openHead? (elaborateOpenHead p613_1 "P3") == some (false, "P3")
#guard selectOwnedDeclaration p613_1 "Z" == .parameter 0
#guard elaboratesToParameter p613_1 "Z" == true
#guard selectOwnedDeclaration p613_2 "P6" == .property 1
#guard elaboratesToParameter p613_2 "P6" == false
#guard selectOwnedDeclaration p613_3 "P6" == .property 1
#guard elaboratesToParameter p613_3 "P6" == false
#guard selectOwnedDeclaration p613_3 "Algorithm" == .none
#guard elaboratesToParameter p613_3 "Algorithm" == false
#guard selectOwnedDeclaration p613_0 "P5" == .property 0
#guard elaboratesToParameter p613_0 "P5" == false

-- spec/receiver-expansion-return-through-a-reference: A = B \n B = { \n     public M = C \n     0 \n } \n C = A.M.abs \n 7
def p614_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C"] } :: prelude
def p614_1 : List OwnerLevel := { parameters := [], properties := [] } :: p614_0
def p614_2 : List OwnerLevel := { parameters := [], properties := ["M"] } :: p614_0
def p614_3 : List OwnerLevel := { parameters := [], properties := [] } :: p614_2
def p614_4 : List OwnerLevel := { parameters := [], properties := [] } :: p614_0
#guard selectOwnedDeclaration p614_1 "B" == .property 1
#guard elaboratesToParameter p614_1 "B" == false
#guard selectOwnedDeclaration p614_3 "C" == .property 2
#guard elaboratesToParameter p614_3 "C" == false
#guard selectOwnedDeclaration p614_4 "A" == .property 1
#guard elaboratesToParameter p614_4 "A" == false
#guard selectOwnedDeclaration p614_4 "M" == .none
#guard elaboratesToParameter p614_4 "M" == false
#guard selectOwnedDeclaration p614_4 "abs" == .property 2
#guard elaboratesToParameter p614_4 "abs" == false

-- spec/receiver-expansion-return-through-a-reference-link: A = B \n B = { \n     public M = C \n     0 \n } \n C = A.M.Algorithm \n 7
def p615_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C"] } :: prelude
def p615_1 : List OwnerLevel := { parameters := [], properties := [] } :: p615_0
def p615_2 : List OwnerLevel := { parameters := [], properties := ["M"] } :: p615_0
def p615_3 : List OwnerLevel := { parameters := [], properties := [] } :: p615_2
def p615_4 : List OwnerLevel := { parameters := [], properties := [] } :: p615_0
#guard selectOwnedDeclaration p615_1 "B" == .property 1
#guard elaboratesToParameter p615_1 "B" == false
#guard selectOwnedDeclaration p615_3 "C" == .property 2
#guard elaboratesToParameter p615_3 "C" == false
#guard selectOwnedDeclaration p615_4 "A" == .property 1
#guard elaboratesToParameter p615_4 "A" == false
#guard selectOwnedDeclaration p615_4 "M" == .none
#guard elaboratesToParameter p615_4 "M" == false
#guard selectOwnedDeclaration p615_4 "Algorithm" == .none
#guard elaboratesToParameter p615_4 "Algorithm" == false

-- spec/receiver-expansion-return-through-a-self-member: B = { \n     public M = B \n     public N = C \n     0 \n } \n C = B.M.N.abs \n 7
def p616_0 : List OwnerLevel := { parameters := [], properties := ["B", "C"] } :: prelude
def p616_1 : List OwnerLevel := { parameters := [], properties := ["M", "N"] } :: p616_0
def p616_2 : List OwnerLevel := { parameters := [], properties := [] } :: p616_1
def p616_3 : List OwnerLevel := { parameters := [], properties := [] } :: p616_1
def p616_4 : List OwnerLevel := { parameters := [], properties := [] } :: p616_0
#guard selectOwnedDeclaration p616_2 "B" == .property 2
#guard elaboratesToParameter p616_2 "B" == false
#guard selectOwnedDeclaration p616_3 "C" == .property 2
#guard elaboratesToParameter p616_3 "C" == false
#guard selectOwnedDeclaration p616_4 "B" == .property 1
#guard elaboratesToParameter p616_4 "B" == false
#guard selectOwnedDeclaration p616_4 "M" == .none
#guard elaboratesToParameter p616_4 "M" == false
#guard selectOwnedDeclaration p616_4 "N" == .none
#guard elaboratesToParameter p616_4 "N" == false
#guard selectOwnedDeclaration p616_4 "abs" == .property 2
#guard elaboratesToParameter p616_4 "abs" == false

-- spec/receiver-expansion-consumed-members-are-no-return: Q = { \n     public V = 5 \n } \n B = { \n     public M = B \n     public N = Q \n     0 \n } \n C = B.M.M.N \n C.V
def p617_0 : List OwnerLevel := { parameters := [], properties := ["Q", "B", "C"] } :: prelude
def p617_1 : List OwnerLevel := { parameters := [], properties := ["V"] } :: p617_0
def p617_2 : List OwnerLevel := { parameters := [], properties := [] } :: p617_1
def p617_3 : List OwnerLevel := { parameters := [], properties := ["M", "N"] } :: p617_0
def p617_4 : List OwnerLevel := { parameters := [], properties := [] } :: p617_3
def p617_5 : List OwnerLevel := { parameters := [], properties := [] } :: p617_3
def p617_6 : List OwnerLevel := { parameters := [], properties := [] } :: p617_0
#guard selectOwnedDeclaration p617_4 "B" == .property 2
#guard elaboratesToParameter p617_4 "B" == false
#guard selectOwnedDeclaration p617_5 "Q" == .property 2
#guard elaboratesToParameter p617_5 "Q" == false
#guard selectOwnedDeclaration p617_6 "B" == .property 1
#guard elaboratesToParameter p617_6 "B" == false
#guard selectOwnedDeclaration p617_6 "M" == .none -- x2
#guard elaboratesToParameter p617_6 "M" == false -- x2
#guard selectOwnedDeclaration p617_6 "N" == .none
#guard elaboratesToParameter p617_6 "N" == false
#guard selectOwnedDeclaration p617_0 "C" == .property 0
#guard elaboratesToParameter p617_0 "C" == false
#guard selectOwnedDeclaration p617_0 "V" == .none
#guard elaboratesToParameter p617_0 "V" == false

-- spec/output-spread-marked-call-spreads-its-rows: A(x, y)* = x, y \n A(1, 2) \n A(3, 4)
def p618_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p618_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p618_0
#guard selectOwnedDeclaration p618_1 "x" == .parameter 0
#guard elaboratesToParameter p618_1 "x" == true
#guard selectOwnedDeclaration p618_1 "y" == .parameter 0
#guard elaboratesToParameter p618_1 "y" == true
#guard selectOwnedDeclaration p618_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p618_0 "A" == false -- x2

-- spec/output-spread-argument-and-element-slots: A(x, y)* = x, y \n Add(x, y) = x + y \n Add(A(1, 2)), [A(1, 2), A(3, 4)]
def p619_0 : List OwnerLevel := { parameters := [], properties := ["A", "Add"] } :: prelude
def p619_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p619_0
def p619_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p619_0
#guard selectOwnedDeclaration p619_1 "x" == .parameter 0
#guard elaboratesToParameter p619_1 "x" == true
#guard selectOwnedDeclaration p619_1 "y" == .parameter 0
#guard elaboratesToParameter p619_1 "y" == true
#guard selectOwnedDeclaration p619_2 "x" == .parameter 0
#guard elaboratesToParameter p619_2 "x" == true
#guard selectOwnedDeclaration p619_2 "y" == .parameter 0
#guard elaboratesToParameter p619_2 "y" == true
#guard selectOwnedDeclaration p619_0 "Add" == .property 0
#guard elaboratesToParameter p619_0 "Add" == false
#guard selectOwnedDeclaration p619_0 "A" == .property 0 -- x3
#guard elaboratesToParameter p619_0 "A" == false -- x3

-- spec/output-spread-alias-inherits-the-marker: A(x, y)* = x, y \n B = A \n [B(3, 4)]
-- the same levels and decisions, 1 more:
--   spec/output-spread-marker-on-an-alias-is-an-error
def p620_0 : List OwnerLevel := { parameters := [], properties := ["B", "A"] } :: prelude
def p620_1 : List OwnerLevel := { parameters := [], properties := [] } :: p620_0
def p620_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p620_0
#guard selectOwnedDeclaration p620_1 "A" == .property 1
#guard elaboratesToParameter p620_1 "A" == false
#guard selectOwnedDeclaration p620_2 "x" == .parameter 0
#guard elaboratesToParameter p620_2 "x" == true
#guard selectOwnedDeclaration p620_2 "y" == .parameter 0
#guard elaboratesToParameter p620_2 "y" == true
#guard selectOwnedDeclaration p620_0 "B" == .property 0
#guard elaboratesToParameter p620_0 "B" == false

-- spec/output-spread-value-positions-keep-one-value: A(x, y)* = x, y \n A(1, 2)[0], count({ A(1, 2) }), count([A(1, 2)])
def p621_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p621_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p621_0
def p621_2 : List OwnerLevel := { parameters := [], properties := [] } :: p621_0
#guard selectOwnedDeclaration p621_1 "x" == .parameter 0
#guard elaboratesToParameter p621_1 "x" == true
#guard selectOwnedDeclaration p621_1 "y" == .parameter 0
#guard elaboratesToParameter p621_1 "y" == true
#guard selectOwnedDeclaration p621_0 "A" == .property 0 -- x2
#guard elaboratesToParameter p621_0 "A" == false -- x2
#guard selectOwnedDeclaration p621_0 "count" == .property 1 -- x2
#guard elaboratesToParameter p621_0 "count" == false -- x2
#guard selectOwnedDeclaration p621_2 "A" == .property 1
#guard elaboratesToParameter p621_2 "A" == false

-- spec/output-spread-builtin-argument-is-spread-too: A(x, y)* = x, y \n count(A(1, 2))
def p622_0 : List OwnerLevel := { parameters := [], properties := ["A"] } :: prelude
def p622_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p622_0
#guard selectOwnedDeclaration p622_1 "x" == .parameter 0
#guard elaboratesToParameter p622_1 "x" == true
#guard selectOwnedDeclaration p622_1 "y" == .parameter 0
#guard elaboratesToParameter p622_1 "y" == true
#guard selectOwnedDeclaration p622_0 "count" == .property 1
#guard elaboratesToParameter p622_0 "count" == false
#guard selectOwnedDeclaration p622_0 "A" == .property 0
#guard elaboratesToParameter p622_0 "A" == false

-- spec/output-spread-not-through-a-parameter: A(x, y)* = x, y \n Apply(f) = count(f(1, 2)) \n Apply(A)
def p623_0 : List OwnerLevel := { parameters := [], properties := ["A", "Apply"] } :: prelude
def p623_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p623_0
def p623_2 : List OwnerLevel := { parameters := ["f"], properties := [] } :: p623_0
#guard selectOwnedDeclaration p623_1 "x" == .parameter 0
#guard elaboratesToParameter p623_1 "x" == true
#guard selectOwnedDeclaration p623_1 "y" == .parameter 0
#guard elaboratesToParameter p623_1 "y" == true
#guard selectOwnedDeclaration p623_2 "count" == .property 2
#guard elaboratesToParameter p623_2 "count" == false
#guard selectOwnedDeclaration p623_2 "f" == .parameter 0
#guard elaboratesToParameter p623_2 "f" == true
#guard selectOwnedDeclaration p623_0 "Apply" == .property 0
#guard elaboratesToParameter p623_0 "Apply" == false
#guard selectOwnedDeclaration p623_0 "A" == .property 0
#guard elaboratesToParameter p623_0 "A" == false

-- spec/output-spread-lifted-call-spreads: A(x, y)* = x, y \n S = [A] \n S(1, 2)
def p624_0 : List OwnerLevel := { parameters := [], properties := ["S", "A"] } :: prelude
def p624_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x", "y"] } :: p624_0
def p624_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p624_0
#guard selectOwnedDeclaration p624_1 "A" == .property 1
#guard elaboratesToParameter p624_1 "A" == false
#guard selectOwnedDeclaration p624_2 "x" == .parameter 0
#guard elaboratesToParameter p624_2 "x" == true
#guard selectOwnedDeclaration p624_2 "y" == .parameter 0
#guard elaboratesToParameter p624_2 "y" == true
#guard selectOwnedDeclaration p624_0 "S" == .property 0
#guard elaboratesToParameter p624_0 "S" == false

-- spec/output-spread-loop-step-through-a-wrapper: Fib(a, b)* = b, a + b \n Step(a, b) = Fib(a, b) \n Step(0, 1).repeat(10)
def p625_0 : List OwnerLevel := { parameters := [], properties := ["Fib", "Step"] } :: prelude
def p625_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p625_0
def p625_2 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p625_0
#guard selectOwnedDeclaration p625_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p625_1 "b" == true -- x2
#guard selectOwnedDeclaration p625_1 "a" == .parameter 0
#guard elaboratesToParameter p625_1 "a" == true
#guard selectOwnedDeclaration p625_2 "Fib" == .property 1
#guard elaboratesToParameter p625_2 "Fib" == false
#guard selectOwnedDeclaration p625_2 "a" == .parameter 0
#guard elaboratesToParameter p625_2 "a" == true
#guard selectOwnedDeclaration p625_2 "b" == .parameter 0
#guard elaboratesToParameter p625_2 "b" == true
#guard selectOwnedDeclaration p625_0 "Step" == .property 0
#guard elaboratesToParameter p625_0 "Step" == false
#guard selectOwnedDeclaration p625_0 "repeat" == .property 1
#guard elaboratesToParameter p625_0 "repeat" == false

-- spec/output-spread-marked-call-as-loop-receiver: Fib(a, b)* = b, a + b \n Fib(0, 1).repeat(10)
def p626_0 : List OwnerLevel := { parameters := [], properties := ["Fib"] } :: prelude
def p626_1 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p626_0
#guard selectOwnedDeclaration p626_1 "b" == .parameter 0 -- x2
#guard elaboratesToParameter p626_1 "b" == true -- x2
#guard selectOwnedDeclaration p626_1 "a" == .parameter 0
#guard elaboratesToParameter p626_1 "a" == true
#guard selectOwnedDeclaration p626_0 "repeat" == .property 1
#guard elaboratesToParameter p626_0 "repeat" == false
#guard selectOwnedDeclaration p626_0 "Fib" == .property 0
#guard elaboratesToParameter p626_0 "Fib" == false

-- spec/output-spread-zero-parameter-only-explicit-calls: P* = 1, 2 \n count(P), [P()]
def p627_0 : List OwnerLevel := { parameters := [], properties := ["P"] } :: prelude
def p627_1 : List OwnerLevel := { parameters := [], properties := [] } :: p627_0
#guard selectOwnedDeclaration p627_0 "count" == .property 1
#guard elaboratesToParameter p627_0 "count" == false
#guard selectOwnedDeclaration p627_0 "P" == .property 0 -- x2
#guard elaboratesToParameter p627_0 "P" == false -- x2

-- spec/output-spread-argument-runs-at-formation: D(x, y)* = x / y, y \n FirstOf(a, *rest) = a \n FirstOf(5, D(1, 0))
def p628_0 : List OwnerLevel := { parameters := [], properties := ["D", "FirstOf"] } :: prelude
def p628_1 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p628_0
def p628_2 : List OwnerLevel := { parameters := ["a", "rest"], properties := [] } :: p628_0
#guard selectOwnedDeclaration p628_1 "x" == .parameter 0
#guard elaboratesToParameter p628_1 "x" == true
#guard selectOwnedDeclaration p628_1 "y" == .parameter 0 -- x2
#guard elaboratesToParameter p628_1 "y" == true -- x2
#guard selectOwnedDeclaration p628_2 "a" == .parameter 0
#guard elaboratesToParameter p628_2 "a" == true
#guard selectOwnedDeclaration p628_0 "FirstOf" == .property 0
#guard elaboratesToParameter p628_0 "FirstOf" == false
#guard selectOwnedDeclaration p628_0 "D" == .property 0
#guard elaboratesToParameter p628_0 "D" == false

-- spec/output-spread-opens-one-level: G* = [[1, 2], [3]] \n [G()], (G(), 9)
def p629_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
def p629_1 : List OwnerLevel := { parameters := [], properties := [] } :: p629_0
#guard selectOwnedDeclaration p629_0 "G" == .property 0 -- x2
#guard elaboratesToParameter p629_0 "G" == false -- x2

-- spec/output-spread-receiver-edge-is-the-lowered-call: A(x, y)* = x, y \n Add3(a, b, c) = a + b + c \n H = A(x, y).F(3) \n H(Add3, 1, 2)
def p630_0 : List OwnerLevel := { parameters := [], properties := ["H", "A", "Add3"] } :: prelude
def p630_1 : List OwnerLevel := { parameters := ["F", "x", "y"], properties := [] } :: p630_0
def p630_2 : List OwnerLevel := { parameters := ["x", "y"], properties := [] } :: p630_0
def p630_3 : List OwnerLevel := { parameters := ["a", "b", "c"], properties := [] } :: p630_0
#guard selectOwnedDeclaration p630_1 "F" == .parameter 0
#guard elaboratesToParameter p630_1 "F" == true
#guard selectOwnedDeclaration p630_1 "A" == .property 1
#guard elaboratesToParameter p630_1 "A" == false
#guard selectOwnedDeclaration p630_1 "x" == .parameter 0
#guard elaboratesToParameter p630_1 "x" == true
#guard selectOwnedDeclaration p630_1 "y" == .parameter 0
#guard elaboratesToParameter p630_1 "y" == true
#guard selectOwnedDeclaration p630_2 "x" == .parameter 0
#guard elaboratesToParameter p630_2 "x" == true
#guard selectOwnedDeclaration p630_2 "y" == .parameter 0
#guard elaboratesToParameter p630_2 "y" == true
#guard selectOwnedDeclaration p630_3 "a" == .parameter 0
#guard elaboratesToParameter p630_3 "a" == true
#guard selectOwnedDeclaration p630_3 "b" == .parameter 0
#guard elaboratesToParameter p630_3 "b" == true
#guard selectOwnedDeclaration p630_3 "c" == .parameter 0
#guard elaboratesToParameter p630_3 "c" == true
#guard selectOwnedDeclaration p630_0 "H" == .property 0
#guard elaboratesToParameter p630_0 "H" == false
#guard selectOwnedDeclaration p630_0 "Add3" == .property 0
#guard elaboratesToParameter p630_0 "Add3" == false

-- spec/output-spread-lifted-call-ends-known-positions: P(x)* = [x] \n Add(a, b) = a + b \n Inc(x) = x + 1 \n H = reduce(P, Add, Inc) \n H(1)
def p631_0 : List OwnerLevel := { parameters := [], properties := ["H", "P", "Add", "Inc"] } :: prelude
def p631_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p631_0
def p631_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p631_0
def p631_3 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p631_0
def p631_4 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p631_0
#guard selectOwnedDeclaration p631_1 "reduce" == .property 2
#guard elaboratesToParameter p631_1 "reduce" == false
#guard selectOwnedDeclaration p631_1 "P" == .property 1
#guard elaboratesToParameter p631_1 "P" == false
#guard selectOwnedDeclaration p631_1 "Add" == .property 1
#guard elaboratesToParameter p631_1 "Add" == false
#guard selectOwnedDeclaration p631_1 "Inc" == .property 1
#guard elaboratesToParameter p631_1 "Inc" == false
#guard selectOwnedDeclaration p631_2 "x" == .parameter 0
#guard elaboratesToParameter p631_2 "x" == true
#guard selectOwnedDeclaration p631_3 "a" == .parameter 0
#guard elaboratesToParameter p631_3 "a" == true
#guard selectOwnedDeclaration p631_3 "b" == .parameter 0
#guard elaboratesToParameter p631_3 "b" == true
#guard selectOwnedDeclaration p631_4 "x" == .parameter 0
#guard elaboratesToParameter p631_4 "x" == true
#guard selectOwnedDeclaration p631_0 "H" == .property 0
#guard elaboratesToParameter p631_0 "H" == false

-- spec/output-spread-reference-needs-call: Q(x) = [[x]] \n P* = Q[0] \n Add(a, b) = a + b \n Inc(x) = x + 1 \n H = reduce(P, Add, Inc) \n H(1)
def p632_0 : List OwnerLevel := { parameters := [], properties := ["P", "H", "Q", "Add", "Inc"] } :: prelude
def p632_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p632_0
def p632_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p632_0
def p632_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p632_0
def p632_4 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p632_0
def p632_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p632_0
#guard selectOwnedDeclaration p632_1 "Q" == .property 1
#guard elaboratesToParameter p632_1 "Q" == false
#guard selectOwnedDeclaration p632_2 "reduce" == .property 2
#guard elaboratesToParameter p632_2 "reduce" == false
#guard selectOwnedDeclaration p632_2 "P" == .property 1
#guard elaboratesToParameter p632_2 "P" == false
#guard selectOwnedDeclaration p632_2 "Add" == .property 1
#guard elaboratesToParameter p632_2 "Add" == false
#guard selectOwnedDeclaration p632_2 "Inc" == .property 1
#guard elaboratesToParameter p632_2 "Inc" == false
#guard selectOwnedDeclaration p632_3 "x" == .parameter 0
#guard elaboratesToParameter p632_3 "x" == true
#guard selectOwnedDeclaration p632_4 "a" == .parameter 0
#guard elaboratesToParameter p632_4 "a" == true
#guard selectOwnedDeclaration p632_4 "b" == .parameter 0
#guard elaboratesToParameter p632_4 "b" == true
#guard selectOwnedDeclaration p632_5 "x" == .parameter 0
#guard elaboratesToParameter p632_5 "x" == true
#guard selectOwnedDeclaration p632_0 "H" == .property 0
#guard elaboratesToParameter p632_0 "H" == false

-- spec/output-spread-reference-certainly-read: Q = [[1, 2], 3] \n P* = Q[0] \n Add(a, b) = a + b \n Inc(x) = x + 1 \n H = reduce(P, Add, Inc) \n H(-3)
def p633_0 : List OwnerLevel := { parameters := [], properties := ["Q", "P", "H", "Add", "Inc"] } :: prelude
def p633_1 : List OwnerLevel := { parameters := [], properties := [] } :: p633_0
def p633_2 : List OwnerLevel := { parameters := [], properties := [] } :: p633_0
def p633_3 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p633_0
def p633_4 : List OwnerLevel := { parameters := ["a", "b"], properties := [] } :: p633_0
def p633_5 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p633_0
#guard selectOwnedDeclaration p633_2 "Q" == .property 1
#guard elaboratesToParameter p633_2 "Q" == false
#guard selectOwnedDeclaration p633_3 "reduce" == .property 2
#guard elaboratesToParameter p633_3 "reduce" == false
#guard selectOwnedDeclaration p633_3 "P" == .property 1
#guard elaboratesToParameter p633_3 "P" == false
#guard selectOwnedDeclaration p633_3 "Add" == .property 1
#guard elaboratesToParameter p633_3 "Add" == false
#guard selectOwnedDeclaration p633_3 "Inc" == .property 1
#guard elaboratesToParameter p633_3 "Inc" == false
#guard selectOwnedDeclaration p633_4 "a" == .parameter 0
#guard elaboratesToParameter p633_4 "a" == true
#guard selectOwnedDeclaration p633_4 "b" == .parameter 0
#guard elaboratesToParameter p633_4 "b" == true
#guard selectOwnedDeclaration p633_5 "x" == .parameter 0
#guard elaboratesToParameter p633_5 "x" == true
#guard selectOwnedDeclaration p633_0 "H" == .property 0
#guard elaboratesToParameter p633_0 "H" == false

/--
Machine-checked partition count: the id list is built by the loop that emits the guards above,
while the expected total is computed from the corpus partition, so a generation bug fails `lake build`.
-/
def guardedProgramIds : List String := [
  "explorer/root__e",
  "explorer/root__n0",
  "explorer/root__n1",
  "explorer/root__bt",
  "explorer/root__bf",
  "explorer/root__pbt",
  "explorer/root__pbt_e",
  "explorer/root__pbt_1",
  "explorer/root__lbt",
  "explorer/root__lbt_bf",
  "explorer/root__lpbt_1",
  "explorer/root__p1",
  "explorer/root__p12",
  "explorer/root__p123",
  "explorer/root__pee",
  "explorer/root__pe1",
  "explorer/root__p1e",
  "explorer/root__p12_3",
  "explorer/root__p12_34",
  "explorer/root__pe_12",
  "explorer/root__ppe1_2",
  "explorer/root__p12_e",
  "explorer/root__ppe",
  "explorer/root__pp1",
  "explorer/root__ppp12",
  "explorer/root__le",
  "explorer/root__l7",
  "explorer/root__l12",
  "explorer/root__l12_3",
  "explorer/root__lle",
  "explorer/root__l_e",
  "explorer/root__l_p12",
  "explorer/root__p_l12",
  "explorer/root__pl1",
  "explorer/seqWrapPair__e",
  "explorer/seqWrapPair__n0",
  "explorer/seqWrapPair__n1",
  "explorer/seqWrapPair__bt",
  "explorer/seqWrapPair__bf",
  "explorer/seqWrapPair__pbt",
  "explorer/seqWrapPair__pbt_e",
  "explorer/seqWrapPair__pbt_1",
  "explorer/seqWrapPair__lbt",
  "explorer/seqWrapPair__lbt_bf",
  "explorer/seqWrapPair__lpbt_1",
  "explorer/seqWrapPair__p1",
  "explorer/seqWrapPair__p12",
  "explorer/seqWrapPair__p123",
  "explorer/seqWrapPair__pee",
  "explorer/seqWrapPair__pe1",
  "explorer/seqWrapPair__p1e",
  "explorer/seqWrapPair__p12_3",
  "explorer/seqWrapPair__p12_34",
  "explorer/seqWrapPair__pe_12",
  "explorer/seqWrapPair__ppe1_2",
  "explorer/seqWrapPair__p12_e",
  "explorer/seqWrapPair__ppe",
  "explorer/seqWrapPair__pp1",
  "explorer/seqWrapPair__ppp12",
  "explorer/seqWrapPair__le",
  "explorer/seqWrapPair__l7",
  "explorer/seqWrapPair__l12",
  "explorer/seqWrapPair__l12_3",
  "explorer/seqWrapPair__lle",
  "explorer/seqWrapPair__l_e",
  "explorer/seqWrapPair__l_p12",
  "explorer/seqWrapPair__p_l12",
  "explorer/seqWrapPair__pl1",
  "explorer/seqWrapSolo__e",
  "explorer/seqWrapSolo__n0",
  "explorer/seqWrapSolo__n1",
  "explorer/seqWrapSolo__bt",
  "explorer/seqWrapSolo__bf",
  "explorer/seqWrapSolo__pbt",
  "explorer/seqWrapSolo__pbt_e",
  "explorer/seqWrapSolo__pbt_1",
  "explorer/seqWrapSolo__lbt",
  "explorer/seqWrapSolo__lbt_bf",
  "explorer/seqWrapSolo__lpbt_1",
  "explorer/seqWrapSolo__p1",
  "explorer/seqWrapSolo__p12",
  "explorer/seqWrapSolo__p123",
  "explorer/seqWrapSolo__pee",
  "explorer/seqWrapSolo__pe1",
  "explorer/seqWrapSolo__p1e",
  "explorer/seqWrapSolo__p12_3",
  "explorer/seqWrapSolo__p12_34",
  "explorer/seqWrapSolo__pe_12",
  "explorer/seqWrapSolo__ppe1_2",
  "explorer/seqWrapSolo__p12_e",
  "explorer/seqWrapSolo__ppe",
  "explorer/seqWrapSolo__pp1",
  "explorer/seqWrapSolo__ppp12",
  "explorer/seqWrapSolo__le",
  "explorer/seqWrapSolo__l7",
  "explorer/seqWrapSolo__l12",
  "explorer/seqWrapSolo__l12_3",
  "explorer/seqWrapSolo__lle",
  "explorer/seqWrapSolo__l_e",
  "explorer/seqWrapSolo__l_p12",
  "explorer/seqWrapSolo__p_l12",
  "explorer/seqWrapSolo__pl1",
  "explorer/spreadRoot__e",
  "explorer/spreadRoot__n0",
  "explorer/spreadRoot__n1",
  "explorer/spreadRoot__bt",
  "explorer/spreadRoot__bf",
  "explorer/spreadRoot__pbt",
  "explorer/spreadRoot__pbt_e",
  "explorer/spreadRoot__pbt_1",
  "explorer/spreadRoot__lbt",
  "explorer/spreadRoot__lbt_bf",
  "explorer/spreadRoot__lpbt_1",
  "explorer/spreadRoot__p1",
  "explorer/spreadRoot__p12",
  "explorer/spreadRoot__p123",
  "explorer/spreadRoot__pee",
  "explorer/spreadRoot__pe1",
  "explorer/spreadRoot__p1e",
  "explorer/spreadRoot__p12_3",
  "explorer/spreadRoot__p12_34",
  "explorer/spreadRoot__pe_12",
  "explorer/spreadRoot__ppe1_2",
  "explorer/spreadRoot__p12_e",
  "explorer/spreadRoot__ppe",
  "explorer/spreadRoot__pp1",
  "explorer/spreadRoot__ppp12",
  "explorer/spreadRoot__le",
  "explorer/spreadRoot__l7",
  "explorer/spreadRoot__l12",
  "explorer/spreadRoot__l12_3",
  "explorer/spreadRoot__lle",
  "explorer/spreadRoot__l_e",
  "explorer/spreadRoot__l_p12",
  "explorer/spreadRoot__p_l12",
  "explorer/spreadRoot__pl1",
  "explorer/spreadInSeq__e",
  "explorer/spreadInSeq__n0",
  "explorer/spreadInSeq__n1",
  "explorer/spreadInSeq__bt",
  "explorer/spreadInSeq__bf",
  "explorer/spreadInSeq__pbt",
  "explorer/spreadInSeq__pbt_e",
  "explorer/spreadInSeq__pbt_1",
  "explorer/spreadInSeq__lbt",
  "explorer/spreadInSeq__lbt_bf",
  "explorer/spreadInSeq__lpbt_1",
  "explorer/spreadInSeq__p1",
  "explorer/spreadInSeq__p12",
  "explorer/spreadInSeq__p123",
  "explorer/spreadInSeq__pee",
  "explorer/spreadInSeq__pe1",
  "explorer/spreadInSeq__p1e",
  "explorer/spreadInSeq__p12_3",
  "explorer/spreadInSeq__p12_34",
  "explorer/spreadInSeq__pe_12",
  "explorer/spreadInSeq__ppe1_2",
  "explorer/spreadInSeq__p12_e",
  "explorer/spreadInSeq__ppe",
  "explorer/spreadInSeq__pp1",
  "explorer/spreadInSeq__ppp12",
  "explorer/spreadInSeq__le",
  "explorer/spreadInSeq__l7",
  "explorer/spreadInSeq__l12",
  "explorer/spreadInSeq__l12_3",
  "explorer/spreadInSeq__lle",
  "explorer/spreadInSeq__l_e",
  "explorer/spreadInSeq__l_p12",
  "explorer/spreadInSeq__p_l12",
  "explorer/spreadInSeq__pl1",
  "explorer/spreadRootStacked__e",
  "explorer/spreadRootStacked__n0",
  "explorer/spreadRootStacked__n1",
  "explorer/spreadRootStacked__bt",
  "explorer/spreadRootStacked__bf",
  "explorer/spreadRootStacked__pbt",
  "explorer/spreadRootStacked__pbt_e",
  "explorer/spreadRootStacked__pbt_1",
  "explorer/spreadRootStacked__lbt",
  "explorer/spreadRootStacked__lbt_bf",
  "explorer/spreadRootStacked__lpbt_1",
  "explorer/spreadRootStacked__p1",
  "explorer/spreadRootStacked__p12",
  "explorer/spreadRootStacked__p123",
  "explorer/spreadRootStacked__pee",
  "explorer/spreadRootStacked__pe1",
  "explorer/spreadRootStacked__p1e",
  "explorer/spreadRootStacked__p12_3",
  "explorer/spreadRootStacked__p12_34",
  "explorer/spreadRootStacked__pe_12",
  "explorer/spreadRootStacked__ppe1_2",
  "explorer/spreadRootStacked__p12_e",
  "explorer/spreadRootStacked__ppe",
  "explorer/spreadRootStacked__pp1",
  "explorer/spreadRootStacked__ppp12",
  "explorer/spreadRootStacked__le",
  "explorer/spreadRootStacked__l7",
  "explorer/spreadRootStacked__l12",
  "explorer/spreadRootStacked__l12_3",
  "explorer/spreadRootStacked__lle",
  "explorer/spreadRootStacked__l_e",
  "explorer/spreadRootStacked__l_p12",
  "explorer/spreadRootStacked__p_l12",
  "explorer/spreadRootStacked__pl1",
  "explorer/special__emptyOpGreater",
  "explorer/special__emptyOpPlus",
  "explorer/special__emptyOpPlusRight",
  "explorer/special__emptyOpDivRight",
  "explorer/special__emptyOpAnd",
  "explorer/special__emptyOpString",
  "explorer/special__emptyOpBoth",
  "explorer/special__emptyUnaryMinus",
  "explorer/special__emptyUnaryNot",
  "explorer/special__emptyEqEmpty",
  "explorer/special__emptyEqNestedEmpty",
  "explorer/special__emptyNeNestedEmpty",
  "explorer/special__rootEmptySlots",
  "explorer/special__seqOfSpreadEmpty",
  "explorer/special__listIndexSelectedKindEqFalse",
  "explorer/special__spreadEmptyBetween",
  "explorer/special__divZero",
  "explorer/special__negativeResult",
  "explorer/special__strEq",
  "explorer/special__chainAllTrue",
  "explorer/special__chainMixed",
  "explorer/special__chainFalseMiddle",
  "explorer/special__chainFalseLast",
  "explorer/special__chainEqOnly",
  "explorer/special__chainNeAdjacent",
  "explorer/special__chainNeAdjacentFalse",
  "explorer/special__chainEqThenLt",
  "explorer/special__chainBoolEqMixed",
  "explorer/special__chainSeqEq",
  "explorer/special__chainStrEq",
  "explorer/special__chainParenFirst",
  "explorer/special__chainParenRight",
  "explorer/special__chainParenBoth",
  "explorer/special__chainUnderNot",
  "explorer/special__chainUnderAnd",
  "explorer/special__chainArithmeticOperands",
  "explorer/special__chainInvalidLater",
  "explorer/special__chainErrorFirstOperand",
  "explorer/special__chainErrorAfterFalse",
  "explorer/special__chainLtThenEq",
  "explorer/special__chainLtThenGt",
  "explorer/special__chainNeThenLt",
  "explorer/special__chainFalseFirstThenEqFalse",
  "explorer/special__chainGroupedNotOperand",
  "explorer/special__chainParenLeftUnderOrdering",
  "explorer/special__chainNegatedBasePower",
  "explorer/special__chainNegatedPowerOperand",
  "explorer/special__chainGroupedNegatedBasePowerOperand",
  "explorer/special__chainArithmeticTiers",
  "explorer/special__chainMiddleOperandError",
  "explorer/special__chainGroupedSelectionReceiver",
  "explorer/special__listEmptyListSpreadBetween",
  "explorer/special__listEmptySeqSpreadBetween",
  "explorer/special__listNeSeq",
  "explorer/special__listEmptyNeEmptySeq",
  "explorer/special__listSingletonNeItem",
  "explorer/special__listWrapCanonicalizes",
  "explorer/special__spreadOrdinaryFailureKept",
  "spec/first-program",
  "spec/power-unary-precedence",
  "spec/not-binds-below-comparisons",
  "spec/comparison-chains-compare-adjacent-pairs",
  "spec/comparison-chain-boolean-and-arithmetic-operands",
  "spec/comparison-chain-is-eager-after-false",
  "spec/integer-division-truncates",
  "spec/integer-division-beyond-consecutive-integers",
  "spec/empty-literal",
  "spec/empty-wrapped",
  "spec/empty-wrapped-twice",
  "spec/singleton-paren",
  "spec/singleton-paren-deep",
  "spec/supply-three-rows",
  "spec/value-three-items",
  "spec/spread-empty-in-sequence",
  "spec/empty-visible-in-sequence",
  "spec/empty-visible-at-root",
  "spec/wrapped-pair-collapses",
  "spec/pair-of-pairs-preserved",
  "spec/pair-then-empty-preserved",
  "spec/spread-empty-between-siblings",
  "spec/spread-one-level-only",
  "spec/spread-one-level-family",
  "spec/variadic-selection-spread-forms-before-selection",
  "spec/trailing-comma-continues-line",
  "spec/comment-does-not-change-parse",
  "spec/scalar-op-rejects-sequence",
  "spec/empty-sequence-is-not-an-operator-identity",
  "spec/division-by-zero",
  "spec/kind-errors-are-type-mismatch",
  "spec/string-equality-exact",
  "spec/list-literal",
  "spec/list-exactness",
  "spec/list-vs-sequence-kind",
  "spec/list-index-selects-element",
  "spec/list-index-out-of-range",
  "spec/list-redundant-parens-canonicalize",
  "spec/list-empty-spread-neutral",
  "spec/decimal-fraction-arithmetic",
  "spec/division-decimal-quotient",
  "spec/overflow-produces-infinity",
  "spec/negative-zero-display",
  "spec/pow-integer-exponent-inexact-accuracy",
  "spec/pow-zero-base-negative-exponent",
  "spec/string-single-quoted-text-is-raw",
  "explorer/capture__e",
  "explorer/capture__n0",
  "explorer/capture__n1",
  "explorer/capture__bt",
  "explorer/capture__bf",
  "explorer/capture__pbt",
  "explorer/capture__pbt_e",
  "explorer/capture__pbt_1",
  "explorer/capture__lbt",
  "explorer/capture__lbt_bf",
  "explorer/capture__lpbt_1",
  "explorer/capture__p1",
  "explorer/capture__p12",
  "explorer/capture__p123",
  "explorer/capture__pee",
  "explorer/capture__pe1",
  "explorer/capture__p1e",
  "explorer/capture__p12_3",
  "explorer/capture__p12_34",
  "explorer/capture__pe_12",
  "explorer/capture__ppe1_2",
  "explorer/capture__p12_e",
  "explorer/capture__ppe",
  "explorer/capture__pp1",
  "explorer/capture__ppp12",
  "explorer/capture__le",
  "explorer/capture__l7",
  "explorer/capture__l12",
  "explorer/capture__l12_3",
  "explorer/capture__lle",
  "explorer/capture__l_e",
  "explorer/capture__l_p12",
  "explorer/capture__p_l12",
  "explorer/capture__pl1",
  "explorer/captureCall__e",
  "explorer/captureCall__n0",
  "explorer/captureCall__n1",
  "explorer/captureCall__bt",
  "explorer/captureCall__bf",
  "explorer/captureCall__pbt",
  "explorer/captureCall__pbt_e",
  "explorer/captureCall__pbt_1",
  "explorer/captureCall__lbt",
  "explorer/captureCall__lbt_bf",
  "explorer/captureCall__lpbt_1",
  "explorer/captureCall__p1",
  "explorer/captureCall__p12",
  "explorer/captureCall__p123",
  "explorer/captureCall__pee",
  "explorer/captureCall__pe1",
  "explorer/captureCall__p1e",
  "explorer/captureCall__p12_3",
  "explorer/captureCall__p12_34",
  "explorer/captureCall__pe_12",
  "explorer/captureCall__ppe1_2",
  "explorer/captureCall__p12_e",
  "explorer/captureCall__ppe",
  "explorer/captureCall__pp1",
  "explorer/captureCall__ppp12",
  "explorer/captureCall__le",
  "explorer/captureCall__l7",
  "explorer/captureCall__l12",
  "explorer/captureCall__l12_3",
  "explorer/captureCall__lle",
  "explorer/captureCall__l_e",
  "explorer/captureCall__l_p12",
  "explorer/captureCall__p_l12",
  "explorer/captureCall__pl1",
  "explorer/index0__e",
  "explorer/index0__n0",
  "explorer/index0__n1",
  "explorer/index0__bt",
  "explorer/index0__bf",
  "explorer/index0__pbt",
  "explorer/index0__pbt_e",
  "explorer/index0__pbt_1",
  "explorer/index0__lbt",
  "explorer/index0__lbt_bf",
  "explorer/index0__lpbt_1",
  "explorer/index0__p1",
  "explorer/index0__p12",
  "explorer/index0__p123",
  "explorer/index0__pee",
  "explorer/index0__pe1",
  "explorer/index0__p1e",
  "explorer/index0__p12_3",
  "explorer/index0__p12_34",
  "explorer/index0__pe_12",
  "explorer/index0__ppe1_2",
  "explorer/index0__p12_e",
  "explorer/index0__ppe",
  "explorer/index0__pp1",
  "explorer/index0__ppp12",
  "explorer/index0__le",
  "explorer/index0__l7",
  "explorer/index0__l12",
  "explorer/index0__l12_3",
  "explorer/index0__lle",
  "explorer/index0__l_e",
  "explorer/index0__l_p12",
  "explorer/index0__p_l12",
  "explorer/index0__pl1",
  "explorer/index1__e",
  "explorer/index1__n0",
  "explorer/index1__n1",
  "explorer/index1__bt",
  "explorer/index1__bf",
  "explorer/index1__pbt",
  "explorer/index1__pbt_e",
  "explorer/index1__pbt_1",
  "explorer/index1__lbt",
  "explorer/index1__lbt_bf",
  "explorer/index1__lpbt_1",
  "explorer/index1__p1",
  "explorer/index1__p12",
  "explorer/index1__p123",
  "explorer/index1__pee",
  "explorer/index1__pe1",
  "explorer/index1__p1e",
  "explorer/index1__p12_3",
  "explorer/index1__p12_34",
  "explorer/index1__pe_12",
  "explorer/index1__ppe1_2",
  "explorer/index1__p12_e",
  "explorer/index1__ppe",
  "explorer/index1__pp1",
  "explorer/index1__ppp12",
  "explorer/index1__le",
  "explorer/index1__l7",
  "explorer/index1__l12",
  "explorer/index1__l12_3",
  "explorer/index1__lle",
  "explorer/index1__l_e",
  "explorer/index1__l_p12",
  "explorer/index1__p_l12",
  "explorer/index1__pl1",
  "explorer/indexBig__e",
  "explorer/indexBig__n0",
  "explorer/indexBig__n1",
  "explorer/indexBig__bt",
  "explorer/indexBig__bf",
  "explorer/indexBig__pbt",
  "explorer/indexBig__pbt_e",
  "explorer/indexBig__pbt_1",
  "explorer/indexBig__lbt",
  "explorer/indexBig__lbt_bf",
  "explorer/indexBig__lpbt_1",
  "explorer/indexBig__p1",
  "explorer/indexBig__p12",
  "explorer/indexBig__p123",
  "explorer/indexBig__pee",
  "explorer/indexBig__pe1",
  "explorer/indexBig__p1e",
  "explorer/indexBig__p12_3",
  "explorer/indexBig__p12_34",
  "explorer/indexBig__pe_12",
  "explorer/indexBig__ppe1_2",
  "explorer/indexBig__p12_e",
  "explorer/indexBig__ppe",
  "explorer/indexBig__pp1",
  "explorer/indexBig__ppp12",
  "explorer/indexBig__le",
  "explorer/indexBig__l7",
  "explorer/indexBig__l12",
  "explorer/indexBig__l12_3",
  "explorer/indexBig__lle",
  "explorer/indexBig__l_e",
  "explorer/indexBig__l_p12",
  "explorer/indexBig__p_l12",
  "explorer/indexBig__pl1",
  "explorer/indexNeg__e",
  "explorer/indexNeg__n0",
  "explorer/indexNeg__n1",
  "explorer/indexNeg__bt",
  "explorer/indexNeg__bf",
  "explorer/indexNeg__pbt",
  "explorer/indexNeg__pbt_e",
  "explorer/indexNeg__pbt_1",
  "explorer/indexNeg__lbt",
  "explorer/indexNeg__lbt_bf",
  "explorer/indexNeg__lpbt_1",
  "explorer/indexNeg__p1",
  "explorer/indexNeg__p12",
  "explorer/indexNeg__p123",
  "explorer/indexNeg__pee",
  "explorer/indexNeg__pe1",
  "explorer/indexNeg__p1e",
  "explorer/indexNeg__p12_3",
  "explorer/indexNeg__p12_34",
  "explorer/indexNeg__pe_12",
  "explorer/indexNeg__ppe1_2",
  "explorer/indexNeg__p12_e",
  "explorer/indexNeg__ppe",
  "explorer/indexNeg__pp1",
  "explorer/indexNeg__ppp12",
  "explorer/indexNeg__le",
  "explorer/indexNeg__l7",
  "explorer/indexNeg__l12",
  "explorer/indexNeg__l12_3",
  "explorer/indexNeg__lle",
  "explorer/indexNeg__l_e",
  "explorer/indexNeg__l_p12",
  "explorer/indexNeg__p_l12",
  "explorer/indexNeg__pl1",
  "explorer/captureStacked__e",
  "explorer/captureStacked__n0",
  "explorer/captureStacked__n1",
  "explorer/captureStacked__bt",
  "explorer/captureStacked__bf",
  "explorer/captureStacked__pbt",
  "explorer/captureStacked__pbt_e",
  "explorer/captureStacked__pbt_1",
  "explorer/captureStacked__lbt",
  "explorer/captureStacked__lbt_bf",
  "explorer/captureStacked__lpbt_1",
  "explorer/captureStacked__p1",
  "explorer/captureStacked__p12",
  "explorer/captureStacked__p123",
  "explorer/captureStacked__pee",
  "explorer/captureStacked__pe1",
  "explorer/captureStacked__p1e",
  "explorer/captureStacked__p12_3",
  "explorer/captureStacked__p12_34",
  "explorer/captureStacked__pe_12",
  "explorer/captureStacked__ppe1_2",
  "explorer/captureStacked__p12_e",
  "explorer/captureStacked__ppe",
  "explorer/captureStacked__pp1",
  "explorer/captureStacked__ppp12",
  "explorer/captureStacked__le",
  "explorer/captureStacked__l7",
  "explorer/captureStacked__l12",
  "explorer/captureStacked__l12_3",
  "explorer/captureStacked__lle",
  "explorer/captureStacked__l_e",
  "explorer/captureStacked__l_p12",
  "explorer/captureStacked__p_l12",
  "explorer/captureStacked__pl1",
  "explorer/special__indexPairInSeq",
  "explorer/special__indexEmptyItemRoot",
  "explorer/special__chainedListIndex",
  "explorer/special__spreadWithSiblingSeqLiteral",
  "explorer/special__strCapture",
  "spec/spread-splices-into-sequence",
  "spec/index-empty-item-visible",
  "spec/index-out-of-range",
  "spec/negative-index-selects-no-position",
  "spec/string-displays-unquoted",
  "explorer/dotAccess__e",
  "explorer/dotAccess__n0",
  "explorer/dotAccess__n1",
  "explorer/dotAccess__bt",
  "explorer/dotAccess__bf",
  "explorer/dotAccess__pbt",
  "explorer/dotAccess__pbt_e",
  "explorer/dotAccess__pbt_1",
  "explorer/dotAccess__lbt",
  "explorer/dotAccess__lbt_bf",
  "explorer/dotAccess__lpbt_1",
  "explorer/dotAccess__p1",
  "explorer/dotAccess__p12",
  "explorer/dotAccess__p123",
  "explorer/dotAccess__pee",
  "explorer/dotAccess__pe1",
  "explorer/dotAccess__p1e",
  "explorer/dotAccess__p12_3",
  "explorer/dotAccess__p12_34",
  "explorer/dotAccess__pe_12",
  "explorer/dotAccess__ppe1_2",
  "explorer/dotAccess__p12_e",
  "explorer/dotAccess__ppe",
  "explorer/dotAccess__pp1",
  "explorer/dotAccess__ppp12",
  "explorer/dotAccess__le",
  "explorer/dotAccess__l7",
  "explorer/dotAccess__l12",
  "explorer/dotAccess__l12_3",
  "explorer/dotAccess__lle",
  "explorer/dotAccess__l_e",
  "explorer/dotAccess__l_p12",
  "explorer/dotAccess__p_l12",
  "explorer/dotAccess__pl1",
  "explorer/dotAccessCall__e",
  "explorer/dotAccessCall__n0",
  "explorer/dotAccessCall__n1",
  "explorer/dotAccessCall__bt",
  "explorer/dotAccessCall__bf",
  "explorer/dotAccessCall__pbt",
  "explorer/dotAccessCall__pbt_e",
  "explorer/dotAccessCall__pbt_1",
  "explorer/dotAccessCall__lbt",
  "explorer/dotAccessCall__lbt_bf",
  "explorer/dotAccessCall__lpbt_1",
  "explorer/dotAccessCall__p1",
  "explorer/dotAccessCall__p12",
  "explorer/dotAccessCall__p123",
  "explorer/dotAccessCall__pee",
  "explorer/dotAccessCall__pe1",
  "explorer/dotAccessCall__p1e",
  "explorer/dotAccessCall__p12_3",
  "explorer/dotAccessCall__p12_34",
  "explorer/dotAccessCall__pe_12",
  "explorer/dotAccessCall__ppe1_2",
  "explorer/dotAccessCall__p12_e",
  "explorer/dotAccessCall__ppe",
  "explorer/dotAccessCall__pp1",
  "explorer/dotAccessCall__ppp12",
  "explorer/dotAccessCall__le",
  "explorer/dotAccessCall__l7",
  "explorer/dotAccessCall__l12",
  "explorer/dotAccessCall__l12_3",
  "explorer/dotAccessCall__lle",
  "explorer/dotAccessCall__l_e",
  "explorer/dotAccessCall__l_p12",
  "explorer/dotAccessCall__p_l12",
  "explorer/dotAccessCall__pl1",
  "explorer/special__multiPropDot",
  "explorer/special__dotAccessPublicMember",
  "explorer/special__dotAccessCallPublicMember",
  "spec/dot-access-value-boundary",
  "explorer/fixed__e",
  "explorer/fixed__n0",
  "explorer/fixed__n1",
  "explorer/fixed__bt",
  "explorer/fixed__bf",
  "explorer/fixed__pbt",
  "explorer/fixed__pbt_e",
  "explorer/fixed__pbt_1",
  "explorer/fixed__lbt",
  "explorer/fixed__lbt_bf",
  "explorer/fixed__lpbt_1",
  "explorer/fixed__p1",
  "explorer/fixed__p12",
  "explorer/fixed__p123",
  "explorer/fixed__pee",
  "explorer/fixed__pe1",
  "explorer/fixed__p1e",
  "explorer/fixed__p12_3",
  "explorer/fixed__p12_34",
  "explorer/fixed__pe_12",
  "explorer/fixed__ppe1_2",
  "explorer/fixed__p12_e",
  "explorer/fixed__ppe",
  "explorer/fixed__pp1",
  "explorer/fixed__ppp12",
  "explorer/fixed__le",
  "explorer/fixed__l7",
  "explorer/fixed__l12",
  "explorer/fixed__l12_3",
  "explorer/fixed__lle",
  "explorer/fixed__l_e",
  "explorer/fixed__l_p12",
  "explorer/fixed__p_l12",
  "explorer/fixed__pl1",
  "explorer/fixedSpread__e",
  "explorer/fixedSpread__n0",
  "explorer/fixedSpread__n1",
  "explorer/fixedSpread__bt",
  "explorer/fixedSpread__bf",
  "explorer/fixedSpread__pbt",
  "explorer/fixedSpread__pbt_e",
  "explorer/fixedSpread__pbt_1",
  "explorer/fixedSpread__lbt",
  "explorer/fixedSpread__lbt_bf",
  "explorer/fixedSpread__lpbt_1",
  "explorer/fixedSpread__p1",
  "explorer/fixedSpread__p12",
  "explorer/fixedSpread__p123",
  "explorer/fixedSpread__pee",
  "explorer/fixedSpread__pe1",
  "explorer/fixedSpread__p1e",
  "explorer/fixedSpread__p12_3",
  "explorer/fixedSpread__p12_34",
  "explorer/fixedSpread__pe_12",
  "explorer/fixedSpread__ppe1_2",
  "explorer/fixedSpread__p12_e",
  "explorer/fixedSpread__ppe",
  "explorer/fixedSpread__pp1",
  "explorer/fixedSpread__ppp12",
  "explorer/fixedSpread__le",
  "explorer/fixedSpread__l7",
  "explorer/fixedSpread__l12",
  "explorer/fixedSpread__l12_3",
  "explorer/fixedSpread__lle",
  "explorer/fixedSpread__l_e",
  "explorer/fixedSpread__l_p12",
  "explorer/fixedSpread__p_l12",
  "explorer/fixedSpread__pl1",
  "explorer/collecting__e",
  "explorer/collecting__n0",
  "explorer/collecting__n1",
  "explorer/collecting__bt",
  "explorer/collecting__bf",
  "explorer/collecting__pbt",
  "explorer/collecting__pbt_e",
  "explorer/collecting__pbt_1",
  "explorer/collecting__lbt",
  "explorer/collecting__lbt_bf",
  "explorer/collecting__lpbt_1",
  "explorer/collecting__p1",
  "explorer/collecting__p12",
  "explorer/collecting__p123",
  "explorer/collecting__pee",
  "explorer/collecting__pe1",
  "explorer/collecting__p1e",
  "explorer/collecting__p12_3",
  "explorer/collecting__p12_34",
  "explorer/collecting__pe_12",
  "explorer/collecting__ppe1_2",
  "explorer/collecting__p12_e",
  "explorer/collecting__ppe",
  "explorer/collecting__pp1",
  "explorer/collecting__ppp12",
  "explorer/collecting__le",
  "explorer/collecting__l7",
  "explorer/collecting__l12",
  "explorer/collecting__l12_3",
  "explorer/collecting__lle",
  "explorer/collecting__l_e",
  "explorer/collecting__l_p12",
  "explorer/collecting__p_l12",
  "explorer/collecting__pl1",
  "explorer/collectingSpread__e",
  "explorer/collectingSpread__n0",
  "explorer/collectingSpread__n1",
  "explorer/collectingSpread__bt",
  "explorer/collectingSpread__bf",
  "explorer/collectingSpread__pbt",
  "explorer/collectingSpread__pbt_e",
  "explorer/collectingSpread__pbt_1",
  "explorer/collectingSpread__lbt",
  "explorer/collectingSpread__lbt_bf",
  "explorer/collectingSpread__lpbt_1",
  "explorer/collectingSpread__p1",
  "explorer/collectingSpread__p12",
  "explorer/collectingSpread__p123",
  "explorer/collectingSpread__pee",
  "explorer/collectingSpread__pe1",
  "explorer/collectingSpread__p1e",
  "explorer/collectingSpread__p12_3",
  "explorer/collectingSpread__p12_34",
  "explorer/collectingSpread__pe_12",
  "explorer/collectingSpread__ppe1_2",
  "explorer/collectingSpread__p12_e",
  "explorer/collectingSpread__ppe",
  "explorer/collectingSpread__pp1",
  "explorer/collectingSpread__ppp12",
  "explorer/collectingSpread__le",
  "explorer/collectingSpread__l7",
  "explorer/collectingSpread__l12",
  "explorer/collectingSpread__l12_3",
  "explorer/collectingSpread__lle",
  "explorer/collectingSpread__l_e",
  "explorer/collectingSpread__l_p12",
  "explorer/collectingSpread__p_l12",
  "explorer/collectingSpread__pl1",
  "explorer/literalDotCollecting__e",
  "explorer/literalDotCollecting__n0",
  "explorer/literalDotCollecting__n1",
  "explorer/literalDotCollecting__bt",
  "explorer/literalDotCollecting__bf",
  "explorer/literalDotCollecting__pbt",
  "explorer/literalDotCollecting__pbt_e",
  "explorer/literalDotCollecting__pbt_1",
  "explorer/literalDotCollecting__lbt",
  "explorer/literalDotCollecting__lbt_bf",
  "explorer/literalDotCollecting__lpbt_1",
  "explorer/literalDotCollecting__p1",
  "explorer/literalDotCollecting__p12",
  "explorer/literalDotCollecting__p123",
  "explorer/literalDotCollecting__pee",
  "explorer/literalDotCollecting__pe1",
  "explorer/literalDotCollecting__p1e",
  "explorer/literalDotCollecting__p12_3",
  "explorer/literalDotCollecting__p12_34",
  "explorer/literalDotCollecting__pe_12",
  "explorer/literalDotCollecting__ppe1_2",
  "explorer/literalDotCollecting__p12_e",
  "explorer/literalDotCollecting__ppe",
  "explorer/literalDotCollecting__pp1",
  "explorer/literalDotCollecting__ppp12",
  "explorer/literalDotCollecting__le",
  "explorer/literalDotCollecting__l7",
  "explorer/literalDotCollecting__l12",
  "explorer/literalDotCollecting__l12_3",
  "explorer/literalDotCollecting__lle",
  "explorer/literalDotCollecting__l_e",
  "explorer/literalDotCollecting__l_p12",
  "explorer/literalDotCollecting__p_l12",
  "explorer/literalDotCollecting__pl1",
  "explorer/collectingStacked__e",
  "explorer/collectingStacked__n0",
  "explorer/collectingStacked__n1",
  "explorer/collectingStacked__bt",
  "explorer/collectingStacked__bf",
  "explorer/collectingStacked__pbt",
  "explorer/collectingStacked__pbt_e",
  "explorer/collectingStacked__pbt_1",
  "explorer/collectingStacked__lbt",
  "explorer/collectingStacked__lbt_bf",
  "explorer/collectingStacked__lpbt_1",
  "explorer/collectingStacked__p1",
  "explorer/collectingStacked__p12",
  "explorer/collectingStacked__p123",
  "explorer/collectingStacked__pee",
  "explorer/collectingStacked__pe1",
  "explorer/collectingStacked__p1e",
  "explorer/collectingStacked__p12_3",
  "explorer/collectingStacked__p12_34",
  "explorer/collectingStacked__pe_12",
  "explorer/collectingStacked__ppe1_2",
  "explorer/collectingStacked__p12_e",
  "explorer/collectingStacked__ppe",
  "explorer/collectingStacked__pp1",
  "explorer/collectingStacked__ppp12",
  "explorer/collectingStacked__le",
  "explorer/collectingStacked__l7",
  "explorer/collectingStacked__l12",
  "explorer/collectingStacked__l12_3",
  "explorer/collectingStacked__lle",
  "explorer/collectingStacked__l_e",
  "explorer/collectingStacked__l_p12",
  "explorer/collectingStacked__p_l12",
  "explorer/collectingStacked__pl1",
  "explorer/special__multiCollecting",
  "explorer/special__collectingEmptyCall",
  "explorer/special__collectingJoin",
  "spec/fixed-empty-arg-visible",
  "spec/fixed-empty-spread-zero-items",
  "explorer/collectingViaProp__e",
  "explorer/collectingViaProp__n0",
  "explorer/collectingViaProp__n1",
  "explorer/collectingViaProp__bt",
  "explorer/collectingViaProp__bf",
  "explorer/collectingViaProp__pbt",
  "explorer/collectingViaProp__pbt_e",
  "explorer/collectingViaProp__pbt_1",
  "explorer/collectingViaProp__lbt",
  "explorer/collectingViaProp__lbt_bf",
  "explorer/collectingViaProp__lpbt_1",
  "explorer/collectingViaProp__p1",
  "explorer/collectingViaProp__p12",
  "explorer/collectingViaProp__p123",
  "explorer/collectingViaProp__pee",
  "explorer/collectingViaProp__pe1",
  "explorer/collectingViaProp__p1e",
  "explorer/collectingViaProp__p12_3",
  "explorer/collectingViaProp__p12_34",
  "explorer/collectingViaProp__pe_12",
  "explorer/collectingViaProp__ppe1_2",
  "explorer/collectingViaProp__p12_e",
  "explorer/collectingViaProp__ppe",
  "explorer/collectingViaProp__pp1",
  "explorer/collectingViaProp__ppp12",
  "explorer/collectingViaProp__le",
  "explorer/collectingViaProp__l7",
  "explorer/collectingViaProp__l12",
  "explorer/collectingViaProp__l12_3",
  "explorer/collectingViaProp__lle",
  "explorer/collectingViaProp__l_e",
  "explorer/collectingViaProp__l_p12",
  "explorer/collectingViaProp__p_l12",
  "explorer/collectingViaProp__pl1",
  "explorer/fluentSpreadCollecting__e",
  "explorer/fluentSpreadCollecting__n0",
  "explorer/fluentSpreadCollecting__n1",
  "explorer/fluentSpreadCollecting__bt",
  "explorer/fluentSpreadCollecting__bf",
  "explorer/fluentSpreadCollecting__pbt",
  "explorer/fluentSpreadCollecting__pbt_e",
  "explorer/fluentSpreadCollecting__pbt_1",
  "explorer/fluentSpreadCollecting__lbt",
  "explorer/fluentSpreadCollecting__lbt_bf",
  "explorer/fluentSpreadCollecting__lpbt_1",
  "explorer/fluentSpreadCollecting__p1",
  "explorer/fluentSpreadCollecting__p12",
  "explorer/fluentSpreadCollecting__p123",
  "explorer/fluentSpreadCollecting__pee",
  "explorer/fluentSpreadCollecting__pe1",
  "explorer/fluentSpreadCollecting__p1e",
  "explorer/fluentSpreadCollecting__p12_3",
  "explorer/fluentSpreadCollecting__p12_34",
  "explorer/fluentSpreadCollecting__pe_12",
  "explorer/fluentSpreadCollecting__ppe1_2",
  "explorer/fluentSpreadCollecting__p12_e",
  "explorer/fluentSpreadCollecting__ppe",
  "explorer/fluentSpreadCollecting__pp1",
  "explorer/fluentSpreadCollecting__ppp12",
  "explorer/fluentSpreadCollecting__le",
  "explorer/fluentSpreadCollecting__l7",
  "explorer/fluentSpreadCollecting__l12",
  "explorer/fluentSpreadCollecting__l12_3",
  "explorer/fluentSpreadCollecting__lle",
  "explorer/fluentSpreadCollecting__l_e",
  "explorer/fluentSpreadCollecting__l_p12",
  "explorer/fluentSpreadCollecting__p_l12",
  "explorer/fluentSpreadCollecting__pl1",
  "explorer/dotCollectingViaProp__e",
  "explorer/dotCollectingViaProp__n0",
  "explorer/dotCollectingViaProp__n1",
  "explorer/dotCollectingViaProp__bt",
  "explorer/dotCollectingViaProp__bf",
  "explorer/dotCollectingViaProp__pbt",
  "explorer/dotCollectingViaProp__pbt_e",
  "explorer/dotCollectingViaProp__pbt_1",
  "explorer/dotCollectingViaProp__lbt",
  "explorer/dotCollectingViaProp__lbt_bf",
  "explorer/dotCollectingViaProp__lpbt_1",
  "explorer/dotCollectingViaProp__p1",
  "explorer/dotCollectingViaProp__p12",
  "explorer/dotCollectingViaProp__p123",
  "explorer/dotCollectingViaProp__pee",
  "explorer/dotCollectingViaProp__pe1",
  "explorer/dotCollectingViaProp__p1e",
  "explorer/dotCollectingViaProp__p12_3",
  "explorer/dotCollectingViaProp__p12_34",
  "explorer/dotCollectingViaProp__pe_12",
  "explorer/dotCollectingViaProp__ppe1_2",
  "explorer/dotCollectingViaProp__p12_e",
  "explorer/dotCollectingViaProp__ppe",
  "explorer/dotCollectingViaProp__pp1",
  "explorer/dotCollectingViaProp__ppp12",
  "explorer/dotCollectingViaProp__le",
  "explorer/dotCollectingViaProp__l7",
  "explorer/dotCollectingViaProp__l12",
  "explorer/dotCollectingViaProp__l12_3",
  "explorer/dotCollectingViaProp__lle",
  "explorer/dotCollectingViaProp__l_e",
  "explorer/dotCollectingViaProp__l_p12",
  "explorer/dotCollectingViaProp__p_l12",
  "explorer/dotCollectingViaProp__pl1",
  "explorer/mixed_h__e",
  "explorer/mixed_h__n0",
  "explorer/mixed_h__n1",
  "explorer/mixed_h__bt",
  "explorer/mixed_h__bf",
  "explorer/mixed_h__pbt",
  "explorer/mixed_h__pbt_e",
  "explorer/mixed_h__pbt_1",
  "explorer/mixed_h__lbt",
  "explorer/mixed_h__lbt_bf",
  "explorer/mixed_h__lpbt_1",
  "explorer/mixed_h__p1",
  "explorer/mixed_h__p12",
  "explorer/mixed_h__p123",
  "explorer/mixed_h__pee",
  "explorer/mixed_h__pe1",
  "explorer/mixed_h__p1e",
  "explorer/mixed_h__p12_3",
  "explorer/mixed_h__p12_34",
  "explorer/mixed_h__pe_12",
  "explorer/mixed_h__ppe1_2",
  "explorer/mixed_h__p12_e",
  "explorer/mixed_h__ppe",
  "explorer/mixed_h__pp1",
  "explorer/mixed_h__ppp12",
  "explorer/mixed_h__le",
  "explorer/mixed_h__l7",
  "explorer/mixed_h__l12",
  "explorer/mixed_h__l12_3",
  "explorer/mixed_h__lle",
  "explorer/mixed_h__l_e",
  "explorer/mixed_h__l_p12",
  "explorer/mixed_h__p_l12",
  "explorer/mixed_h__pl1",
  "explorer/mixed_t__e",
  "explorer/mixed_t__n0",
  "explorer/mixed_t__n1",
  "explorer/mixed_t__bt",
  "explorer/mixed_t__bf",
  "explorer/mixed_t__pbt",
  "explorer/mixed_t__pbt_e",
  "explorer/mixed_t__pbt_1",
  "explorer/mixed_t__lbt",
  "explorer/mixed_t__lbt_bf",
  "explorer/mixed_t__lpbt_1",
  "explorer/mixed_t__p1",
  "explorer/mixed_t__p12",
  "explorer/mixed_t__p123",
  "explorer/mixed_t__pee",
  "explorer/mixed_t__pe1",
  "explorer/mixed_t__p1e",
  "explorer/mixed_t__p12_3",
  "explorer/mixed_t__p12_34",
  "explorer/mixed_t__pe_12",
  "explorer/mixed_t__ppe1_2",
  "explorer/mixed_t__p12_e",
  "explorer/mixed_t__ppe",
  "explorer/mixed_t__pp1",
  "explorer/mixed_t__ppp12",
  "explorer/mixed_t__le",
  "explorer/mixed_t__l7",
  "explorer/mixed_t__l12",
  "explorer/mixed_t__l12_3",
  "explorer/mixed_t__lle",
  "explorer/mixed_t__l_e",
  "explorer/mixed_t__l_p12",
  "explorer/mixed_t__p_l12",
  "explorer/mixed_t__pl1",
  "explorer/mixedBack_t__e",
  "explorer/mixedBack_t__n0",
  "explorer/mixedBack_t__n1",
  "explorer/mixedBack_t__bt",
  "explorer/mixedBack_t__bf",
  "explorer/mixedBack_t__pbt",
  "explorer/mixedBack_t__pbt_e",
  "explorer/mixedBack_t__pbt_1",
  "explorer/mixedBack_t__lbt",
  "explorer/mixedBack_t__lbt_bf",
  "explorer/mixedBack_t__lpbt_1",
  "explorer/mixedBack_t__p1",
  "explorer/mixedBack_t__p12",
  "explorer/mixedBack_t__p123",
  "explorer/mixedBack_t__pee",
  "explorer/mixedBack_t__pe1",
  "explorer/mixedBack_t__p1e",
  "explorer/mixedBack_t__p12_3",
  "explorer/mixedBack_t__p12_34",
  "explorer/mixedBack_t__pe_12",
  "explorer/mixedBack_t__ppe1_2",
  "explorer/mixedBack_t__p12_e",
  "explorer/mixedBack_t__ppe",
  "explorer/mixedBack_t__pp1",
  "explorer/mixedBack_t__ppp12",
  "explorer/mixedBack_t__le",
  "explorer/mixedBack_t__l7",
  "explorer/mixedBack_t__l12",
  "explorer/mixedBack_t__l12_3",
  "explorer/mixedBack_t__lle",
  "explorer/mixedBack_t__l_e",
  "explorer/mixedBack_t__l_p12",
  "explorer/mixedBack_t__p_l12",
  "explorer/mixedBack_t__pl1",
  "explorer/mixedBack_z__e",
  "explorer/mixedBack_z__n0",
  "explorer/mixedBack_z__n1",
  "explorer/mixedBack_z__bt",
  "explorer/mixedBack_z__bf",
  "explorer/mixedBack_z__pbt",
  "explorer/mixedBack_z__pbt_e",
  "explorer/mixedBack_z__pbt_1",
  "explorer/mixedBack_z__lbt",
  "explorer/mixedBack_z__lbt_bf",
  "explorer/mixedBack_z__lpbt_1",
  "explorer/mixedBack_z__p1",
  "explorer/mixedBack_z__p12",
  "explorer/mixedBack_z__p123",
  "explorer/mixedBack_z__pee",
  "explorer/mixedBack_z__pe1",
  "explorer/mixedBack_z__p1e",
  "explorer/mixedBack_z__p12_3",
  "explorer/mixedBack_z__p12_34",
  "explorer/mixedBack_z__pe_12",
  "explorer/mixedBack_z__ppe1_2",
  "explorer/mixedBack_z__p12_e",
  "explorer/mixedBack_z__ppe",
  "explorer/mixedBack_z__pp1",
  "explorer/mixedBack_z__ppp12",
  "explorer/mixedBack_z__le",
  "explorer/mixedBack_z__l7",
  "explorer/mixedBack_z__l12",
  "explorer/mixedBack_z__l12_3",
  "explorer/mixedBack_z__lle",
  "explorer/mixedBack_z__l_e",
  "explorer/mixedBack_z__l_p12",
  "explorer/mixedBack_z__p_l12",
  "explorer/mixedBack_z__pl1",
  "explorer/deconPair_x__e",
  "explorer/deconPair_x__n0",
  "explorer/deconPair_x__n1",
  "explorer/deconPair_x__bt",
  "explorer/deconPair_x__bf",
  "explorer/deconPair_x__pbt",
  "explorer/deconPair_x__pbt_e",
  "explorer/deconPair_x__pbt_1",
  "explorer/deconPair_x__lbt",
  "explorer/deconPair_x__lbt_bf",
  "explorer/deconPair_x__lpbt_1",
  "explorer/deconPair_x__p1",
  "explorer/deconPair_x__p12",
  "explorer/deconPair_x__p123",
  "explorer/deconPair_x__pee",
  "explorer/deconPair_x__pe1",
  "explorer/deconPair_x__p1e",
  "explorer/deconPair_x__p12_3",
  "explorer/deconPair_x__p12_34",
  "explorer/deconPair_x__pe_12",
  "explorer/deconPair_x__ppe1_2",
  "explorer/deconPair_x__p12_e",
  "explorer/deconPair_x__ppe",
  "explorer/deconPair_x__pp1",
  "explorer/deconPair_x__ppp12",
  "explorer/deconPair_x__le",
  "explorer/deconPair_x__l7",
  "explorer/deconPair_x__l12",
  "explorer/deconPair_x__l12_3",
  "explorer/deconPair_x__lle",
  "explorer/deconPair_x__l_e",
  "explorer/deconPair_x__l_p12",
  "explorer/deconPair_x__p_l12",
  "explorer/deconPair_x__pl1",
  "explorer/deconPairSpread_x__e",
  "explorer/deconPairSpread_x__n0",
  "explorer/deconPairSpread_x__n1",
  "explorer/deconPairSpread_x__bt",
  "explorer/deconPairSpread_x__bf",
  "explorer/deconPairSpread_x__pbt",
  "explorer/deconPairSpread_x__pbt_e",
  "explorer/deconPairSpread_x__pbt_1",
  "explorer/deconPairSpread_x__lbt",
  "explorer/deconPairSpread_x__lbt_bf",
  "explorer/deconPairSpread_x__lpbt_1",
  "explorer/deconPairSpread_x__p1",
  "explorer/deconPairSpread_x__p12",
  "explorer/deconPairSpread_x__p123",
  "explorer/deconPairSpread_x__pee",
  "explorer/deconPairSpread_x__pe1",
  "explorer/deconPairSpread_x__p1e",
  "explorer/deconPairSpread_x__p12_3",
  "explorer/deconPairSpread_x__p12_34",
  "explorer/deconPairSpread_x__pe_12",
  "explorer/deconPairSpread_x__ppe1_2",
  "explorer/deconPairSpread_x__p12_e",
  "explorer/deconPairSpread_x__ppe",
  "explorer/deconPairSpread_x__pp1",
  "explorer/deconPairSpread_x__ppp12",
  "explorer/deconPairSpread_x__le",
  "explorer/deconPairSpread_x__l7",
  "explorer/deconPairSpread_x__l12",
  "explorer/deconPairSpread_x__l12_3",
  "explorer/deconPairSpread_x__lle",
  "explorer/deconPairSpread_x__l_e",
  "explorer/deconPairSpread_x__l_p12",
  "explorer/deconPairSpread_x__p_l12",
  "explorer/deconPairSpread_x__pl1",
  "spec/decon-arity-under",
  "spec/decon-arity-over",
  "explorer/deconPair_y__e",
  "explorer/deconPair_y__n0",
  "explorer/deconPair_y__n1",
  "explorer/deconPair_y__bt",
  "explorer/deconPair_y__bf",
  "explorer/deconPair_y__pbt",
  "explorer/deconPair_y__pbt_e",
  "explorer/deconPair_y__pbt_1",
  "explorer/deconPair_y__lbt",
  "explorer/deconPair_y__lbt_bf",
  "explorer/deconPair_y__lpbt_1",
  "explorer/deconPair_y__p1",
  "explorer/deconPair_y__p12",
  "explorer/deconPair_y__p123",
  "explorer/deconPair_y__pee",
  "explorer/deconPair_y__pe1",
  "explorer/deconPair_y__p1e",
  "explorer/deconPair_y__p12_3",
  "explorer/deconPair_y__p12_34",
  "explorer/deconPair_y__pe_12",
  "explorer/deconPair_y__ppe1_2",
  "explorer/deconPair_y__p12_e",
  "explorer/deconPair_y__ppe",
  "explorer/deconPair_y__pp1",
  "explorer/deconPair_y__ppp12",
  "explorer/deconPair_y__le",
  "explorer/deconPair_y__l7",
  "explorer/deconPair_y__l12",
  "explorer/deconPair_y__l12_3",
  "explorer/deconPair_y__lle",
  "explorer/deconPair_y__l_e",
  "explorer/deconPair_y__l_p12",
  "explorer/deconPair_y__p_l12",
  "explorer/deconPair_y__pl1",
  "explorer/deconCollect_t__e",
  "explorer/deconCollect_t__n0",
  "explorer/deconCollect_t__n1",
  "explorer/deconCollect_t__bt",
  "explorer/deconCollect_t__bf",
  "explorer/deconCollect_t__pbt",
  "explorer/deconCollect_t__pbt_e",
  "explorer/deconCollect_t__pbt_1",
  "explorer/deconCollect_t__lbt",
  "explorer/deconCollect_t__lbt_bf",
  "explorer/deconCollect_t__lpbt_1",
  "explorer/deconCollect_t__p1",
  "explorer/deconCollect_t__p12",
  "explorer/deconCollect_t__p123",
  "explorer/deconCollect_t__pee",
  "explorer/deconCollect_t__pe1",
  "explorer/deconCollect_t__p1e",
  "explorer/deconCollect_t__p12_3",
  "explorer/deconCollect_t__p12_34",
  "explorer/deconCollect_t__pe_12",
  "explorer/deconCollect_t__ppe1_2",
  "explorer/deconCollect_t__p12_e",
  "explorer/deconCollect_t__ppe",
  "explorer/deconCollect_t__pp1",
  "explorer/deconCollect_t__ppp12",
  "explorer/deconCollect_t__le",
  "explorer/deconCollect_t__l7",
  "explorer/deconCollect_t__l12",
  "explorer/deconCollect_t__l12_3",
  "explorer/deconCollect_t__lle",
  "explorer/deconCollect_t__l_e",
  "explorer/deconCollect_t__l_p12",
  "explorer/deconCollect_t__p_l12",
  "explorer/deconCollect_t__pl1",
  "explorer/deconCollectSpread_t__e",
  "explorer/deconCollectSpread_t__n0",
  "explorer/deconCollectSpread_t__n1",
  "explorer/deconCollectSpread_t__bt",
  "explorer/deconCollectSpread_t__bf",
  "explorer/deconCollectSpread_t__pbt",
  "explorer/deconCollectSpread_t__pbt_e",
  "explorer/deconCollectSpread_t__pbt_1",
  "explorer/deconCollectSpread_t__lbt",
  "explorer/deconCollectSpread_t__lbt_bf",
  "explorer/deconCollectSpread_t__lpbt_1",
  "explorer/deconCollectSpread_t__p1",
  "explorer/deconCollectSpread_t__p12",
  "explorer/deconCollectSpread_t__p123",
  "explorer/deconCollectSpread_t__pee",
  "explorer/deconCollectSpread_t__pe1",
  "explorer/deconCollectSpread_t__p1e",
  "explorer/deconCollectSpread_t__p12_3",
  "explorer/deconCollectSpread_t__p12_34",
  "explorer/deconCollectSpread_t__pe_12",
  "explorer/deconCollectSpread_t__ppe1_2",
  "explorer/deconCollectSpread_t__p12_e",
  "explorer/deconCollectSpread_t__ppe",
  "explorer/deconCollectSpread_t__pp1",
  "explorer/deconCollectSpread_t__ppp12",
  "explorer/deconCollectSpread_t__le",
  "explorer/deconCollectSpread_t__l7",
  "explorer/deconCollectSpread_t__l12",
  "explorer/deconCollectSpread_t__l12_3",
  "explorer/deconCollectSpread_t__lle",
  "explorer/deconCollectSpread_t__l_e",
  "explorer/deconCollectSpread_t__l_p12",
  "explorer/deconCollectSpread_t__p_l12",
  "explorer/deconCollectSpread_t__pl1",
  "explorer/deconPrefix_p__e",
  "explorer/deconPrefix_p__n0",
  "explorer/deconPrefix_p__n1",
  "explorer/deconPrefix_p__bt",
  "explorer/deconPrefix_p__bf",
  "explorer/deconPrefix_p__pbt",
  "explorer/deconPrefix_p__pbt_e",
  "explorer/deconPrefix_p__pbt_1",
  "explorer/deconPrefix_p__lbt",
  "explorer/deconPrefix_p__lbt_bf",
  "explorer/deconPrefix_p__lpbt_1",
  "explorer/deconPrefix_p__p1",
  "explorer/deconPrefix_p__p12",
  "explorer/deconPrefix_p__p123",
  "explorer/deconPrefix_p__pee",
  "explorer/deconPrefix_p__pe1",
  "explorer/deconPrefix_p__p1e",
  "explorer/deconPrefix_p__p12_3",
  "explorer/deconPrefix_p__p12_34",
  "explorer/deconPrefix_p__pe_12",
  "explorer/deconPrefix_p__ppe1_2",
  "explorer/deconPrefix_p__p12_e",
  "explorer/deconPrefix_p__ppe",
  "explorer/deconPrefix_p__pp1",
  "explorer/deconPrefix_p__ppp12",
  "explorer/deconPrefix_p__le",
  "explorer/deconPrefix_p__l7",
  "explorer/deconPrefix_p__l12",
  "explorer/deconPrefix_p__l12_3",
  "explorer/deconPrefix_p__lle",
  "explorer/deconPrefix_p__l_e",
  "explorer/deconPrefix_p__l_p12",
  "explorer/deconPrefix_p__p_l12",
  "explorer/deconPrefix_p__pl1",
  "explorer/deconPrefix_z__e",
  "explorer/deconPrefix_z__n0",
  "explorer/deconPrefix_z__n1",
  "explorer/deconPrefix_z__bt",
  "explorer/deconPrefix_z__bf",
  "explorer/deconPrefix_z__pbt",
  "explorer/deconPrefix_z__pbt_e",
  "explorer/deconPrefix_z__pbt_1",
  "explorer/deconPrefix_z__lbt",
  "explorer/deconPrefix_z__lbt_bf",
  "explorer/deconPrefix_z__lpbt_1",
  "explorer/deconPrefix_z__p1",
  "explorer/deconPrefix_z__p12",
  "explorer/deconPrefix_z__p123",
  "explorer/deconPrefix_z__pee",
  "explorer/deconPrefix_z__pe1",
  "explorer/deconPrefix_z__p1e",
  "explorer/deconPrefix_z__p12_3",
  "explorer/deconPrefix_z__p12_34",
  "explorer/deconPrefix_z__pe_12",
  "explorer/deconPrefix_z__ppe1_2",
  "explorer/deconPrefix_z__p12_e",
  "explorer/deconPrefix_z__ppe",
  "explorer/deconPrefix_z__pp1",
  "explorer/deconPrefix_z__ppp12",
  "explorer/deconPrefix_z__le",
  "explorer/deconPrefix_z__l7",
  "explorer/deconPrefix_z__l12",
  "explorer/deconPrefix_z__l12_3",
  "explorer/deconPrefix_z__lle",
  "explorer/deconPrefix_z__l_e",
  "explorer/deconPrefix_z__l_p12",
  "explorer/deconPrefix_z__p_l12",
  "explorer/deconPrefix_z__pl1",
  "explorer/count__e",
  "explorer/count__n0",
  "explorer/count__n1",
  "explorer/count__bt",
  "explorer/count__bf",
  "explorer/count__pbt",
  "explorer/count__pbt_e",
  "explorer/count__pbt_1",
  "explorer/count__lbt",
  "explorer/count__lbt_bf",
  "explorer/count__lpbt_1",
  "explorer/count__p1",
  "explorer/count__p12",
  "explorer/count__p123",
  "explorer/count__pee",
  "explorer/count__pe1",
  "explorer/count__p1e",
  "explorer/count__p12_3",
  "explorer/count__p12_34",
  "explorer/count__pe_12",
  "explorer/count__ppe1_2",
  "explorer/count__p12_e",
  "explorer/count__ppe",
  "explorer/count__pp1",
  "explorer/count__ppp12",
  "explorer/count__le",
  "explorer/count__l7",
  "explorer/count__l12",
  "explorer/count__l12_3",
  "explorer/count__lle",
  "explorer/count__l_e",
  "explorer/count__l_p12",
  "explorer/count__p_l12",
  "explorer/count__pl1",
  "explorer/countSpread__e",
  "explorer/countSpread__n0",
  "explorer/countSpread__n1",
  "explorer/countSpread__bt",
  "explorer/countSpread__bf",
  "explorer/countSpread__pbt",
  "explorer/countSpread__pbt_e",
  "explorer/countSpread__pbt_1",
  "explorer/countSpread__lbt",
  "explorer/countSpread__lbt_bf",
  "explorer/countSpread__lpbt_1",
  "explorer/countSpread__p1",
  "explorer/countSpread__p12",
  "explorer/countSpread__p123",
  "explorer/countSpread__pee",
  "explorer/countSpread__pe1",
  "explorer/countSpread__p1e",
  "explorer/countSpread__p12_3",
  "explorer/countSpread__p12_34",
  "explorer/countSpread__pe_12",
  "explorer/countSpread__ppe1_2",
  "explorer/countSpread__p12_e",
  "explorer/countSpread__ppe",
  "explorer/countSpread__pp1",
  "explorer/countSpread__ppp12",
  "explorer/countSpread__le",
  "explorer/countSpread__l7",
  "explorer/countSpread__l12",
  "explorer/countSpread__l12_3",
  "explorer/countSpread__lle",
  "explorer/countSpread__l_e",
  "explorer/countSpread__l_p12",
  "explorer/countSpread__p_l12",
  "explorer/countSpread__pl1",
  "explorer/literalDotCount__e",
  "explorer/literalDotCount__n0",
  "explorer/literalDotCount__n1",
  "explorer/literalDotCount__bt",
  "explorer/literalDotCount__bf",
  "explorer/literalDotCount__pbt",
  "explorer/literalDotCount__pbt_e",
  "explorer/literalDotCount__pbt_1",
  "explorer/literalDotCount__lbt",
  "explorer/literalDotCount__lbt_bf",
  "explorer/literalDotCount__lpbt_1",
  "explorer/literalDotCount__p1",
  "explorer/literalDotCount__p12",
  "explorer/literalDotCount__p123",
  "explorer/literalDotCount__pee",
  "explorer/literalDotCount__pe1",
  "explorer/literalDotCount__p1e",
  "explorer/literalDotCount__p12_3",
  "explorer/literalDotCount__p12_34",
  "explorer/literalDotCount__pe_12",
  "explorer/literalDotCount__ppe1_2",
  "explorer/literalDotCount__p12_e",
  "explorer/literalDotCount__ppe",
  "explorer/literalDotCount__pp1",
  "explorer/literalDotCount__ppp12",
  "explorer/literalDotCount__le",
  "explorer/literalDotCount__l7",
  "explorer/literalDotCount__l12",
  "explorer/literalDotCount__l12_3",
  "explorer/literalDotCount__lle",
  "explorer/literalDotCount__l_e",
  "explorer/literalDotCount__l_p12",
  "explorer/literalDotCount__p_l12",
  "explorer/literalDotCount__pl1",
  "explorer/special__strCount",
  "spec/empty-count-one-arg",
  "spec/empty-count-two-args",
  "spec/count-scalar-and-string",
  "spec/builtin-fixed-collection-arity",
  "spec/variadic-selection-shares-the-positional-view",
  "spec/list-builtin-collection",
  "explorer/dotCount__e",
  "explorer/dotCount__n0",
  "explorer/dotCount__n1",
  "explorer/dotCount__bt",
  "explorer/dotCount__bf",
  "explorer/dotCount__pbt",
  "explorer/dotCount__pbt_e",
  "explorer/dotCount__pbt_1",
  "explorer/dotCount__lbt",
  "explorer/dotCount__lbt_bf",
  "explorer/dotCount__lpbt_1",
  "explorer/dotCount__p1",
  "explorer/dotCount__p12",
  "explorer/dotCount__p123",
  "explorer/dotCount__pee",
  "explorer/dotCount__pe1",
  "explorer/dotCount__p1e",
  "explorer/dotCount__p12_3",
  "explorer/dotCount__p12_34",
  "explorer/dotCount__pe_12",
  "explorer/dotCount__ppe1_2",
  "explorer/dotCount__p12_e",
  "explorer/dotCount__ppe",
  "explorer/dotCount__pp1",
  "explorer/dotCount__ppp12",
  "explorer/dotCount__le",
  "explorer/dotCount__l7",
  "explorer/dotCount__l12",
  "explorer/dotCount__l12_3",
  "explorer/dotCount__lle",
  "explorer/dotCount__l_e",
  "explorer/dotCount__l_p12",
  "explorer/dotCount__p_l12",
  "explorer/dotCount__pl1",
  "explorer/eqSelf__e",
  "explorer/eqSelf__n0",
  "explorer/eqSelf__n1",
  "explorer/eqSelf__bt",
  "explorer/eqSelf__bf",
  "explorer/eqSelf__pbt",
  "explorer/eqSelf__pbt_e",
  "explorer/eqSelf__pbt_1",
  "explorer/eqSelf__lbt",
  "explorer/eqSelf__lbt_bf",
  "explorer/eqSelf__lpbt_1",
  "explorer/eqSelf__p1",
  "explorer/eqSelf__p12",
  "explorer/eqSelf__p123",
  "explorer/eqSelf__pee",
  "explorer/eqSelf__pe1",
  "explorer/eqSelf__p1e",
  "explorer/eqSelf__p12_3",
  "explorer/eqSelf__p12_34",
  "explorer/eqSelf__pe_12",
  "explorer/eqSelf__ppe1_2",
  "explorer/eqSelf__p12_e",
  "explorer/eqSelf__ppe",
  "explorer/eqSelf__pp1",
  "explorer/eqSelf__ppp12",
  "explorer/eqSelf__le",
  "explorer/eqSelf__l7",
  "explorer/eqSelf__l12",
  "explorer/eqSelf__l12_3",
  "explorer/eqSelf__lle",
  "explorer/eqSelf__l_e",
  "explorer/eqSelf__l_p12",
  "explorer/eqSelf__p_l12",
  "explorer/eqSelf__pl1",
  "explorer/neqSelf__e",
  "explorer/neqSelf__n0",
  "explorer/neqSelf__n1",
  "explorer/neqSelf__bt",
  "explorer/neqSelf__bf",
  "explorer/neqSelf__pbt",
  "explorer/neqSelf__pbt_e",
  "explorer/neqSelf__pbt_1",
  "explorer/neqSelf__lbt",
  "explorer/neqSelf__lbt_bf",
  "explorer/neqSelf__lpbt_1",
  "explorer/neqSelf__p1",
  "explorer/neqSelf__p12",
  "explorer/neqSelf__p123",
  "explorer/neqSelf__pee",
  "explorer/neqSelf__pe1",
  "explorer/neqSelf__p1e",
  "explorer/neqSelf__p12_3",
  "explorer/neqSelf__p12_34",
  "explorer/neqSelf__pe_12",
  "explorer/neqSelf__ppe1_2",
  "explorer/neqSelf__p12_e",
  "explorer/neqSelf__ppe",
  "explorer/neqSelf__pp1",
  "explorer/neqSelf__ppp12",
  "explorer/neqSelf__le",
  "explorer/neqSelf__l7",
  "explorer/neqSelf__l12",
  "explorer/neqSelf__l12_3",
  "explorer/neqSelf__lle",
  "explorer/neqSelf__l_e",
  "explorer/neqSelf__l_p12",
  "explorer/neqSelf__p_l12",
  "explorer/neqSelf__pl1",
  "explorer/eqIdentity__e",
  "explorer/eqIdentity__n0",
  "explorer/eqIdentity__n1",
  "explorer/eqIdentity__bt",
  "explorer/eqIdentity__bf",
  "explorer/eqIdentity__pbt",
  "explorer/eqIdentity__pbt_e",
  "explorer/eqIdentity__pbt_1",
  "explorer/eqIdentity__lbt",
  "explorer/eqIdentity__lbt_bf",
  "explorer/eqIdentity__lpbt_1",
  "explorer/eqIdentity__p1",
  "explorer/eqIdentity__p12",
  "explorer/eqIdentity__p123",
  "explorer/eqIdentity__pee",
  "explorer/eqIdentity__pe1",
  "explorer/eqIdentity__p1e",
  "explorer/eqIdentity__p12_3",
  "explorer/eqIdentity__p12_34",
  "explorer/eqIdentity__pe_12",
  "explorer/eqIdentity__ppe1_2",
  "explorer/eqIdentity__p12_e",
  "explorer/eqIdentity__ppe",
  "explorer/eqIdentity__pp1",
  "explorer/eqIdentity__ppp12",
  "explorer/eqIdentity__le",
  "explorer/eqIdentity__l7",
  "explorer/eqIdentity__l12",
  "explorer/eqIdentity__l12_3",
  "explorer/eqIdentity__lle",
  "explorer/eqIdentity__l_e",
  "explorer/eqIdentity__l_p12",
  "explorer/eqIdentity__p_l12",
  "explorer/eqIdentity__pl1",
  "explorer/identity__e",
  "explorer/identity__n0",
  "explorer/identity__n1",
  "explorer/identity__bt",
  "explorer/identity__bf",
  "explorer/identity__pbt",
  "explorer/identity__pbt_e",
  "explorer/identity__pbt_1",
  "explorer/identity__lbt",
  "explorer/identity__lbt_bf",
  "explorer/identity__lpbt_1",
  "explorer/identity__p1",
  "explorer/identity__p12",
  "explorer/identity__p123",
  "explorer/identity__pee",
  "explorer/identity__pe1",
  "explorer/identity__p1e",
  "explorer/identity__p12_3",
  "explorer/identity__p12_34",
  "explorer/identity__pe_12",
  "explorer/identity__ppe1_2",
  "explorer/identity__p12_e",
  "explorer/identity__ppe",
  "explorer/identity__pp1",
  "explorer/identity__ppp12",
  "explorer/identity__le",
  "explorer/identity__l7",
  "explorer/identity__l12",
  "explorer/identity__l12_3",
  "explorer/identity__lle",
  "explorer/identity__l_e",
  "explorer/identity__l_p12",
  "explorer/identity__p_l12",
  "explorer/identity__pl1",
  "explorer/identityTwice__e",
  "explorer/identityTwice__n0",
  "explorer/identityTwice__n1",
  "explorer/identityTwice__bt",
  "explorer/identityTwice__bf",
  "explorer/identityTwice__pbt",
  "explorer/identityTwice__pbt_e",
  "explorer/identityTwice__pbt_1",
  "explorer/identityTwice__lbt",
  "explorer/identityTwice__lbt_bf",
  "explorer/identityTwice__lpbt_1",
  "explorer/identityTwice__p1",
  "explorer/identityTwice__p12",
  "explorer/identityTwice__p123",
  "explorer/identityTwice__pee",
  "explorer/identityTwice__pe1",
  "explorer/identityTwice__p1e",
  "explorer/identityTwice__p12_3",
  "explorer/identityTwice__p12_34",
  "explorer/identityTwice__pe_12",
  "explorer/identityTwice__ppe1_2",
  "explorer/identityTwice__p12_e",
  "explorer/identityTwice__ppe",
  "explorer/identityTwice__pp1",
  "explorer/identityTwice__ppp12",
  "explorer/identityTwice__le",
  "explorer/identityTwice__l7",
  "explorer/identityTwice__l12",
  "explorer/identityTwice__l12_3",
  "explorer/identityTwice__lle",
  "explorer/identityTwice__l_e",
  "explorer/identityTwice__l_p12",
  "explorer/identityTwice__p_l12",
  "explorer/identityTwice__pl1",
  "explorer/propChain__e",
  "explorer/propChain__n0",
  "explorer/propChain__n1",
  "explorer/propChain__bt",
  "explorer/propChain__bf",
  "explorer/propChain__pbt",
  "explorer/propChain__pbt_e",
  "explorer/propChain__pbt_1",
  "explorer/propChain__lbt",
  "explorer/propChain__lbt_bf",
  "explorer/propChain__lpbt_1",
  "explorer/propChain__p1",
  "explorer/propChain__p12",
  "explorer/propChain__p123",
  "explorer/propChain__pee",
  "explorer/propChain__pe1",
  "explorer/propChain__p1e",
  "explorer/propChain__p12_3",
  "explorer/propChain__p12_34",
  "explorer/propChain__pe_12",
  "explorer/propChain__ppe1_2",
  "explorer/propChain__p12_e",
  "explorer/propChain__ppe",
  "explorer/propChain__pp1",
  "explorer/propChain__ppp12",
  "explorer/propChain__le",
  "explorer/propChain__l7",
  "explorer/propChain__l12",
  "explorer/propChain__l12_3",
  "explorer/propChain__lle",
  "explorer/propChain__l_e",
  "explorer/propChain__l_p12",
  "explorer/propChain__p_l12",
  "explorer/propChain__pl1",
  "explorer/take1__e",
  "explorer/take1__n0",
  "explorer/take1__n1",
  "explorer/take1__bt",
  "explorer/take1__bf",
  "explorer/take1__pbt",
  "explorer/take1__pbt_e",
  "explorer/take1__pbt_1",
  "explorer/take1__lbt",
  "explorer/take1__lbt_bf",
  "explorer/take1__lpbt_1",
  "explorer/take1__p1",
  "explorer/take1__p12",
  "explorer/take1__p123",
  "explorer/take1__pee",
  "explorer/take1__pe1",
  "explorer/take1__p1e",
  "explorer/take1__p12_3",
  "explorer/take1__p12_34",
  "explorer/take1__pe_12",
  "explorer/take1__ppe1_2",
  "explorer/take1__p12_e",
  "explorer/take1__ppe",
  "explorer/take1__pp1",
  "explorer/take1__ppp12",
  "explorer/take1__le",
  "explorer/take1__l7",
  "explorer/take1__l12",
  "explorer/take1__l12_3",
  "explorer/take1__lle",
  "explorer/take1__l_e",
  "explorer/take1__l_p12",
  "explorer/take1__p_l12",
  "explorer/take1__pl1",
  "explorer/take9__e",
  "explorer/take9__n0",
  "explorer/take9__n1",
  "explorer/take9__bt",
  "explorer/take9__bf",
  "explorer/take9__pbt",
  "explorer/take9__pbt_e",
  "explorer/take9__pbt_1",
  "explorer/take9__lbt",
  "explorer/take9__lbt_bf",
  "explorer/take9__lpbt_1",
  "explorer/take9__p1",
  "explorer/take9__p12",
  "explorer/take9__p123",
  "explorer/take9__pee",
  "explorer/take9__pe1",
  "explorer/take9__p1e",
  "explorer/take9__p12_3",
  "explorer/take9__p12_34",
  "explorer/take9__pe_12",
  "explorer/take9__ppe1_2",
  "explorer/take9__p12_e",
  "explorer/take9__ppe",
  "explorer/take9__pp1",
  "explorer/take9__ppp12",
  "explorer/take9__le",
  "explorer/take9__l7",
  "explorer/take9__l12",
  "explorer/take9__l12_3",
  "explorer/take9__lle",
  "explorer/take9__l_e",
  "explorer/take9__l_p12",
  "explorer/take9__p_l12",
  "explorer/take9__pl1",
  "explorer/special__takeOneSurvivorPair",
  "explorer/special__takeOneSurvivorPairEq",
  "explorer/special__takeEmpties",
  "spec/need-collection-builtin-demands-its-collection-first",
  "spec/take-prefix",
  "spec/take-single-survivor",
  "spec/take-zero-empty",
  "explorer/skip1__e",
  "explorer/skip1__n0",
  "explorer/skip1__n1",
  "explorer/skip1__bt",
  "explorer/skip1__bf",
  "explorer/skip1__pbt",
  "explorer/skip1__pbt_e",
  "explorer/skip1__pbt_1",
  "explorer/skip1__lbt",
  "explorer/skip1__lbt_bf",
  "explorer/skip1__lpbt_1",
  "explorer/skip1__p1",
  "explorer/skip1__p12",
  "explorer/skip1__p123",
  "explorer/skip1__pee",
  "explorer/skip1__pe1",
  "explorer/skip1__p1e",
  "explorer/skip1__p12_3",
  "explorer/skip1__p12_34",
  "explorer/skip1__pe_12",
  "explorer/skip1__ppe1_2",
  "explorer/skip1__p12_e",
  "explorer/skip1__ppe",
  "explorer/skip1__pp1",
  "explorer/skip1__ppp12",
  "explorer/skip1__le",
  "explorer/skip1__l7",
  "explorer/skip1__l12",
  "explorer/skip1__l12_3",
  "explorer/skip1__lle",
  "explorer/skip1__l_e",
  "explorer/skip1__l_p12",
  "explorer/skip1__p_l12",
  "explorer/skip1__pl1",
  "explorer/special__skipToOnePair",
  "spec/skip-prefix",
  "explorer/distinct__e",
  "explorer/distinct__n0",
  "explorer/distinct__n1",
  "explorer/distinct__bt",
  "explorer/distinct__bf",
  "explorer/distinct__pbt",
  "explorer/distinct__pbt_e",
  "explorer/distinct__pbt_1",
  "explorer/distinct__lbt",
  "explorer/distinct__lbt_bf",
  "explorer/distinct__lpbt_1",
  "explorer/distinct__p1",
  "explorer/distinct__p12",
  "explorer/distinct__p123",
  "explorer/distinct__pee",
  "explorer/distinct__pe1",
  "explorer/distinct__p1e",
  "explorer/distinct__p12_3",
  "explorer/distinct__p12_34",
  "explorer/distinct__pe_12",
  "explorer/distinct__ppe1_2",
  "explorer/distinct__p12_e",
  "explorer/distinct__ppe",
  "explorer/distinct__pp1",
  "explorer/distinct__ppp12",
  "explorer/distinct__le",
  "explorer/distinct__l7",
  "explorer/distinct__l12",
  "explorer/distinct__l12_3",
  "explorer/distinct__lle",
  "explorer/distinct__l_e",
  "explorer/distinct__l_p12",
  "explorer/distinct__p_l12",
  "explorer/distinct__pl1",
  "explorer/special__distinctEmpties",
  "explorer/special__distinctPairsToOne",
  "spec/boolean-values-and-equality",
  "spec/distinct-preserves-first",
  "spec/distinct-structural-pairs",
  "spec/distinct-empties-collapse",
  "explorer/order__e",
  "explorer/order__n0",
  "explorer/order__n1",
  "explorer/order__bt",
  "explorer/order__bf",
  "explorer/order__pbt",
  "explorer/order__pbt_e",
  "explorer/order__pbt_1",
  "explorer/order__lbt",
  "explorer/order__lbt_bf",
  "explorer/order__lpbt_1",
  "explorer/order__p1",
  "explorer/order__p12",
  "explorer/order__p123",
  "explorer/order__pee",
  "explorer/order__pe1",
  "explorer/order__p1e",
  "explorer/order__p12_3",
  "explorer/order__p12_34",
  "explorer/order__pe_12",
  "explorer/order__ppe1_2",
  "explorer/order__p12_e",
  "explorer/order__ppe",
  "explorer/order__pp1",
  "explorer/order__ppp12",
  "explorer/order__le",
  "explorer/order__l7",
  "explorer/order__l12",
  "explorer/order__l12_3",
  "explorer/order__lle",
  "explorer/order__l_e",
  "explorer/order__l_p12",
  "explorer/order__p_l12",
  "explorer/order__pl1",
  "explorer/special__orderSingle",
  "explorer/special__orderEmpty",
  "explorer/special__orderIndex0",
  "spec/order-sorts-atoms",
  "spec/order-rejects-non-numeric",
  "spec/order-is-stable",
  "explorer/mapId__e",
  "explorer/mapId__n0",
  "explorer/mapId__n1",
  "explorer/mapId__bt",
  "explorer/mapId__bf",
  "explorer/mapId__pbt",
  "explorer/mapId__pbt_e",
  "explorer/mapId__pbt_1",
  "explorer/mapId__lbt",
  "explorer/mapId__lbt_bf",
  "explorer/mapId__lpbt_1",
  "explorer/mapId__p1",
  "explorer/mapId__p12",
  "explorer/mapId__p123",
  "explorer/mapId__pee",
  "explorer/mapId__pe1",
  "explorer/mapId__p1e",
  "explorer/mapId__p12_3",
  "explorer/mapId__p12_34",
  "explorer/mapId__pe_12",
  "explorer/mapId__ppe1_2",
  "explorer/mapId__p12_e",
  "explorer/mapId__ppe",
  "explorer/mapId__pp1",
  "explorer/mapId__ppp12",
  "explorer/mapId__le",
  "explorer/mapId__l7",
  "explorer/mapId__l12",
  "explorer/mapId__l12_3",
  "explorer/mapId__lle",
  "explorer/mapId__l_e",
  "explorer/mapId__l_p12",
  "explorer/mapId__p_l12",
  "explorer/mapId__pl1",
  "explorer/special__mapToOne",
  "spec/map-single-item",
  "explorer/patternHead__e",
  "explorer/patternHead__n0",
  "explorer/patternHead__n1",
  "explorer/patternHead__bt",
  "explorer/patternHead__bf",
  "explorer/patternHead__pbt",
  "explorer/patternHead__pbt_e",
  "explorer/patternHead__pbt_1",
  "explorer/patternHead__lbt",
  "explorer/patternHead__lbt_bf",
  "explorer/patternHead__lpbt_1",
  "explorer/patternHead__p1",
  "explorer/patternHead__p12",
  "explorer/patternHead__p123",
  "explorer/patternHead__pee",
  "explorer/patternHead__pe1",
  "explorer/patternHead__p1e",
  "explorer/patternHead__p12_3",
  "explorer/patternHead__p12_34",
  "explorer/patternHead__pe_12",
  "explorer/patternHead__ppe1_2",
  "explorer/patternHead__p12_e",
  "explorer/patternHead__ppe",
  "explorer/patternHead__pp1",
  "explorer/patternHead__ppp12",
  "explorer/patternHead__le",
  "explorer/patternHead__l7",
  "explorer/patternHead__l12",
  "explorer/patternHead__l12_3",
  "explorer/patternHead__lle",
  "explorer/patternHead__l_e",
  "explorer/patternHead__l_p12",
  "explorer/patternHead__p_l12",
  "explorer/patternHead__pl1",
  "explorer/listPatternHead__e",
  "explorer/listPatternHead__n0",
  "explorer/listPatternHead__n1",
  "explorer/listPatternHead__bt",
  "explorer/listPatternHead__bf",
  "explorer/listPatternHead__pbt",
  "explorer/listPatternHead__pbt_e",
  "explorer/listPatternHead__pbt_1",
  "explorer/listPatternHead__lbt",
  "explorer/listPatternHead__lbt_bf",
  "explorer/listPatternHead__lpbt_1",
  "explorer/listPatternHead__p1",
  "explorer/listPatternHead__p12",
  "explorer/listPatternHead__p123",
  "explorer/listPatternHead__pee",
  "explorer/listPatternHead__pe1",
  "explorer/listPatternHead__p1e",
  "explorer/listPatternHead__p12_3",
  "explorer/listPatternHead__p12_34",
  "explorer/listPatternHead__pe_12",
  "explorer/listPatternHead__ppe1_2",
  "explorer/listPatternHead__p12_e",
  "explorer/listPatternHead__ppe",
  "explorer/listPatternHead__pp1",
  "explorer/listPatternHead__ppp12",
  "explorer/listPatternHead__le",
  "explorer/listPatternHead__l7",
  "explorer/listPatternHead__l12",
  "explorer/listPatternHead__l12_3",
  "explorer/listPatternHead__lle",
  "explorer/listPatternHead__l_e",
  "explorer/listPatternHead__l_p12",
  "explorer/listPatternHead__p_l12",
  "explorer/listPatternHead__pl1",
  "explorer/patternHeadMap__e",
  "explorer/patternHeadMap__n0",
  "explorer/patternHeadMap__n1",
  "explorer/patternHeadMap__bt",
  "explorer/patternHeadMap__bf",
  "explorer/patternHeadMap__pbt",
  "explorer/patternHeadMap__pbt_e",
  "explorer/patternHeadMap__pbt_1",
  "explorer/patternHeadMap__lbt",
  "explorer/patternHeadMap__lbt_bf",
  "explorer/patternHeadMap__lpbt_1",
  "explorer/patternHeadMap__p1",
  "explorer/patternHeadMap__p12",
  "explorer/patternHeadMap__p123",
  "explorer/patternHeadMap__pee",
  "explorer/patternHeadMap__pe1",
  "explorer/patternHeadMap__p1e",
  "explorer/patternHeadMap__p12_3",
  "explorer/patternHeadMap__p12_34",
  "explorer/patternHeadMap__pe_12",
  "explorer/patternHeadMap__ppe1_2",
  "explorer/patternHeadMap__p12_e",
  "explorer/patternHeadMap__ppe",
  "explorer/patternHeadMap__pp1",
  "explorer/patternHeadMap__ppp12",
  "explorer/patternHeadMap__le",
  "explorer/patternHeadMap__l7",
  "explorer/patternHeadMap__l12",
  "explorer/patternHeadMap__l12_3",
  "explorer/patternHeadMap__lle",
  "explorer/patternHeadMap__l_e",
  "explorer/patternHeadMap__l_p12",
  "explorer/patternHeadMap__p_l12",
  "explorer/patternHeadMap__pl1",
  "explorer/listPatternHeadMap__e",
  "explorer/listPatternHeadMap__n0",
  "explorer/listPatternHeadMap__n1",
  "explorer/listPatternHeadMap__bt",
  "explorer/listPatternHeadMap__bf",
  "explorer/listPatternHeadMap__pbt",
  "explorer/listPatternHeadMap__pbt_e",
  "explorer/listPatternHeadMap__pbt_1",
  "explorer/listPatternHeadMap__lbt",
  "explorer/listPatternHeadMap__lbt_bf",
  "explorer/listPatternHeadMap__lpbt_1",
  "explorer/listPatternHeadMap__p1",
  "explorer/listPatternHeadMap__p12",
  "explorer/listPatternHeadMap__p123",
  "explorer/listPatternHeadMap__pee",
  "explorer/listPatternHeadMap__pe1",
  "explorer/listPatternHeadMap__p1e",
  "explorer/listPatternHeadMap__p12_3",
  "explorer/listPatternHeadMap__p12_34",
  "explorer/listPatternHeadMap__pe_12",
  "explorer/listPatternHeadMap__ppe1_2",
  "explorer/listPatternHeadMap__p12_e",
  "explorer/listPatternHeadMap__ppe",
  "explorer/listPatternHeadMap__pp1",
  "explorer/listPatternHeadMap__ppp12",
  "explorer/listPatternHeadMap__le",
  "explorer/listPatternHeadMap__l7",
  "explorer/listPatternHeadMap__l12",
  "explorer/listPatternHeadMap__l12_3",
  "explorer/listPatternHeadMap__lle",
  "explorer/listPatternHeadMap__l_e",
  "explorer/listPatternHeadMap__l_p12",
  "explorer/listPatternHeadMap__p_l12",
  "explorer/listPatternHeadMap__pl1",
  "explorer/patternPair__e",
  "explorer/patternPair__n0",
  "explorer/patternPair__n1",
  "explorer/patternPair__bt",
  "explorer/patternPair__bf",
  "explorer/patternPair__pbt",
  "explorer/patternPair__pbt_e",
  "explorer/patternPair__pbt_1",
  "explorer/patternPair__lbt",
  "explorer/patternPair__lbt_bf",
  "explorer/patternPair__lpbt_1",
  "explorer/patternPair__p1",
  "explorer/patternPair__p12",
  "explorer/patternPair__p123",
  "explorer/patternPair__pee",
  "explorer/patternPair__pe1",
  "explorer/patternPair__p1e",
  "explorer/patternPair__p12_3",
  "explorer/patternPair__p12_34",
  "explorer/patternPair__pe_12",
  "explorer/patternPair__ppe1_2",
  "explorer/patternPair__p12_e",
  "explorer/patternPair__ppe",
  "explorer/patternPair__pp1",
  "explorer/patternPair__ppp12",
  "explorer/patternPair__le",
  "explorer/patternPair__l7",
  "explorer/patternPair__l12",
  "explorer/patternPair__l12_3",
  "explorer/patternPair__lle",
  "explorer/patternPair__l_e",
  "explorer/patternPair__l_p12",
  "explorer/patternPair__p_l12",
  "explorer/patternPair__pl1",
  "explorer/listPatternPair__e",
  "explorer/listPatternPair__n0",
  "explorer/listPatternPair__n1",
  "explorer/listPatternPair__bt",
  "explorer/listPatternPair__bf",
  "explorer/listPatternPair__pbt",
  "explorer/listPatternPair__pbt_e",
  "explorer/listPatternPair__pbt_1",
  "explorer/listPatternPair__lbt",
  "explorer/listPatternPair__lbt_bf",
  "explorer/listPatternPair__lpbt_1",
  "explorer/listPatternPair__p1",
  "explorer/listPatternPair__p12",
  "explorer/listPatternPair__p123",
  "explorer/listPatternPair__pee",
  "explorer/listPatternPair__pe1",
  "explorer/listPatternPair__p1e",
  "explorer/listPatternPair__p12_3",
  "explorer/listPatternPair__p12_34",
  "explorer/listPatternPair__pe_12",
  "explorer/listPatternPair__ppe1_2",
  "explorer/listPatternPair__p12_e",
  "explorer/listPatternPair__ppe",
  "explorer/listPatternPair__pp1",
  "explorer/listPatternPair__ppp12",
  "explorer/listPatternPair__le",
  "explorer/listPatternPair__l7",
  "explorer/listPatternPair__l12",
  "explorer/listPatternPair__l12_3",
  "explorer/listPatternPair__lle",
  "explorer/listPatternPair__l_e",
  "explorer/listPatternPair__l_p12",
  "explorer/listPatternPair__p_l12",
  "explorer/listPatternPair__pl1",
  "explorer/patternPairMap__e",
  "explorer/patternPairMap__n0",
  "explorer/patternPairMap__n1",
  "explorer/patternPairMap__bt",
  "explorer/patternPairMap__bf",
  "explorer/patternPairMap__pbt",
  "explorer/patternPairMap__pbt_e",
  "explorer/patternPairMap__pbt_1",
  "explorer/patternPairMap__lbt",
  "explorer/patternPairMap__lbt_bf",
  "explorer/patternPairMap__lpbt_1",
  "explorer/patternPairMap__p1",
  "explorer/patternPairMap__p12",
  "explorer/patternPairMap__p123",
  "explorer/patternPairMap__pee",
  "explorer/patternPairMap__pe1",
  "explorer/patternPairMap__p1e",
  "explorer/patternPairMap__p12_3",
  "explorer/patternPairMap__p12_34",
  "explorer/patternPairMap__pe_12",
  "explorer/patternPairMap__ppe1_2",
  "explorer/patternPairMap__p12_e",
  "explorer/patternPairMap__ppe",
  "explorer/patternPairMap__pp1",
  "explorer/patternPairMap__ppp12",
  "explorer/patternPairMap__le",
  "explorer/patternPairMap__l7",
  "explorer/patternPairMap__l12",
  "explorer/patternPairMap__l12_3",
  "explorer/patternPairMap__lle",
  "explorer/patternPairMap__l_e",
  "explorer/patternPairMap__l_p12",
  "explorer/patternPairMap__p_l12",
  "explorer/patternPairMap__pl1",
  "explorer/listPatternPairMap__e",
  "explorer/listPatternPairMap__n0",
  "explorer/listPatternPairMap__n1",
  "explorer/listPatternPairMap__bt",
  "explorer/listPatternPairMap__bf",
  "explorer/listPatternPairMap__pbt",
  "explorer/listPatternPairMap__pbt_e",
  "explorer/listPatternPairMap__pbt_1",
  "explorer/listPatternPairMap__lbt",
  "explorer/listPatternPairMap__lbt_bf",
  "explorer/listPatternPairMap__lpbt_1",
  "explorer/listPatternPairMap__p1",
  "explorer/listPatternPairMap__p12",
  "explorer/listPatternPairMap__p123",
  "explorer/listPatternPairMap__pee",
  "explorer/listPatternPairMap__pe1",
  "explorer/listPatternPairMap__p1e",
  "explorer/listPatternPairMap__p12_3",
  "explorer/listPatternPairMap__p12_34",
  "explorer/listPatternPairMap__pe_12",
  "explorer/listPatternPairMap__ppe1_2",
  "explorer/listPatternPairMap__p12_e",
  "explorer/listPatternPairMap__ppe",
  "explorer/listPatternPairMap__pp1",
  "explorer/listPatternPairMap__ppp12",
  "explorer/listPatternPairMap__le",
  "explorer/listPatternPairMap__l7",
  "explorer/listPatternPairMap__l12",
  "explorer/listPatternPairMap__l12_3",
  "explorer/listPatternPairMap__lle",
  "explorer/listPatternPairMap__l_e",
  "explorer/listPatternPairMap__l_p12",
  "explorer/listPatternPairMap__p_l12",
  "explorer/listPatternPairMap__pl1",
  "explorer/filterKeep__e",
  "explorer/filterKeep__n0",
  "explorer/filterKeep__n1",
  "explorer/filterKeep__bt",
  "explorer/filterKeep__bf",
  "explorer/filterKeep__pbt",
  "explorer/filterKeep__pbt_e",
  "explorer/filterKeep__pbt_1",
  "explorer/filterKeep__lbt",
  "explorer/filterKeep__lbt_bf",
  "explorer/filterKeep__lpbt_1",
  "explorer/filterKeep__p1",
  "explorer/filterKeep__p12",
  "explorer/filterKeep__p123",
  "explorer/filterKeep__pee",
  "explorer/filterKeep__pe1",
  "explorer/filterKeep__p1e",
  "explorer/filterKeep__p12_3",
  "explorer/filterKeep__p12_34",
  "explorer/filterKeep__pe_12",
  "explorer/filterKeep__ppe1_2",
  "explorer/filterKeep__p12_e",
  "explorer/filterKeep__ppe",
  "explorer/filterKeep__pp1",
  "explorer/filterKeep__ppp12",
  "explorer/filterKeep__le",
  "explorer/filterKeep__l7",
  "explorer/filterKeep__l12",
  "explorer/filterKeep__l12_3",
  "explorer/filterKeep__lle",
  "explorer/filterKeep__l_e",
  "explorer/filterKeep__l_p12",
  "explorer/filterKeep__p_l12",
  "explorer/filterKeep__pl1",
  "explorer/atoms__e",
  "explorer/atoms__n0",
  "explorer/atoms__n1",
  "explorer/atoms__bt",
  "explorer/atoms__bf",
  "explorer/atoms__pbt",
  "explorer/atoms__pbt_e",
  "explorer/atoms__pbt_1",
  "explorer/atoms__lbt",
  "explorer/atoms__lbt_bf",
  "explorer/atoms__lpbt_1",
  "explorer/atoms__p1",
  "explorer/atoms__p12",
  "explorer/atoms__p123",
  "explorer/atoms__pee",
  "explorer/atoms__pe1",
  "explorer/atoms__p1e",
  "explorer/atoms__p12_3",
  "explorer/atoms__p12_34",
  "explorer/atoms__pe_12",
  "explorer/atoms__ppe1_2",
  "explorer/atoms__p12_e",
  "explorer/atoms__ppe",
  "explorer/atoms__pp1",
  "explorer/atoms__ppp12",
  "explorer/atoms__le",
  "explorer/atoms__l7",
  "explorer/atoms__l12",
  "explorer/atoms__l12_3",
  "explorer/atoms__lle",
  "explorer/atoms__l_e",
  "explorer/atoms__l_p12",
  "explorer/atoms__p_l12",
  "explorer/atoms__pl1",
  "explorer/special__atomsNested",
  "spec/atoms-recursive-flatten",
  "spec/atoms-exact-list-result",
  "spec/atoms-list-traversal",
  "spec/atoms-mixed-traversal",
  "explorer/takeCapture__e",
  "explorer/takeCapture__n0",
  "explorer/takeCapture__n1",
  "explorer/takeCapture__bt",
  "explorer/takeCapture__bf",
  "explorer/takeCapture__pbt",
  "explorer/takeCapture__pbt_e",
  "explorer/takeCapture__pbt_1",
  "explorer/takeCapture__lbt",
  "explorer/takeCapture__lbt_bf",
  "explorer/takeCapture__lpbt_1",
  "explorer/takeCapture__p1",
  "explorer/takeCapture__p12",
  "explorer/takeCapture__p123",
  "explorer/takeCapture__pee",
  "explorer/takeCapture__pe1",
  "explorer/takeCapture__p1e",
  "explorer/takeCapture__p12_3",
  "explorer/takeCapture__p12_34",
  "explorer/takeCapture__pe_12",
  "explorer/takeCapture__ppe1_2",
  "explorer/takeCapture__p12_e",
  "explorer/takeCapture__ppe",
  "explorer/takeCapture__pp1",
  "explorer/takeCapture__ppp12",
  "explorer/takeCapture__le",
  "explorer/takeCapture__l7",
  "explorer/takeCapture__l12",
  "explorer/takeCapture__l12_3",
  "explorer/takeCapture__lle",
  "explorer/takeCapture__l_e",
  "explorer/takeCapture__l_p12",
  "explorer/takeCapture__p_l12",
  "explorer/takeCapture__pl1",
  "spec/builtin-result-reentry",
  "explorer/takeIdentity__e",
  "explorer/takeIdentity__n0",
  "explorer/takeIdentity__n1",
  "explorer/takeIdentity__bt",
  "explorer/takeIdentity__bf",
  "explorer/takeIdentity__pbt",
  "explorer/takeIdentity__pbt_e",
  "explorer/takeIdentity__pbt_1",
  "explorer/takeIdentity__lbt",
  "explorer/takeIdentity__lbt_bf",
  "explorer/takeIdentity__lpbt_1",
  "explorer/takeIdentity__p1",
  "explorer/takeIdentity__p12",
  "explorer/takeIdentity__p123",
  "explorer/takeIdentity__pee",
  "explorer/takeIdentity__pe1",
  "explorer/takeIdentity__p1e",
  "explorer/takeIdentity__p12_3",
  "explorer/takeIdentity__p12_34",
  "explorer/takeIdentity__pe_12",
  "explorer/takeIdentity__ppe1_2",
  "explorer/takeIdentity__p12_e",
  "explorer/takeIdentity__ppe",
  "explorer/takeIdentity__pp1",
  "explorer/takeIdentity__ppp12",
  "explorer/takeIdentity__le",
  "explorer/takeIdentity__l7",
  "explorer/takeIdentity__l12",
  "explorer/takeIdentity__l12_3",
  "explorer/takeIdentity__lle",
  "explorer/takeIdentity__l_e",
  "explorer/takeIdentity__l_p12",
  "explorer/takeIdentity__p_l12",
  "explorer/takeIdentity__pl1",
  "explorer/takeCount__e",
  "explorer/takeCount__n0",
  "explorer/takeCount__n1",
  "explorer/takeCount__bt",
  "explorer/takeCount__bf",
  "explorer/takeCount__pbt",
  "explorer/takeCount__pbt_e",
  "explorer/takeCount__pbt_1",
  "explorer/takeCount__lbt",
  "explorer/takeCount__lbt_bf",
  "explorer/takeCount__lpbt_1",
  "explorer/takeCount__p1",
  "explorer/takeCount__p12",
  "explorer/takeCount__p123",
  "explorer/takeCount__pee",
  "explorer/takeCount__pe1",
  "explorer/takeCount__p1e",
  "explorer/takeCount__p12_3",
  "explorer/takeCount__p12_34",
  "explorer/takeCount__pe_12",
  "explorer/takeCount__ppe1_2",
  "explorer/takeCount__p12_e",
  "explorer/takeCount__ppe",
  "explorer/takeCount__pp1",
  "explorer/takeCount__ppp12",
  "explorer/takeCount__le",
  "explorer/takeCount__l7",
  "explorer/takeCount__l12",
  "explorer/takeCount__l12_3",
  "explorer/takeCount__lle",
  "explorer/takeCount__l_e",
  "explorer/takeCount__l_p12",
  "explorer/takeCount__p_l12",
  "explorer/takeCount__pl1",
  "explorer/special__takeOneSurvivorPairCount",
  "explorer/takeCollecting__e",
  "explorer/takeCollecting__n0",
  "explorer/takeCollecting__n1",
  "explorer/takeCollecting__bt",
  "explorer/takeCollecting__bf",
  "explorer/takeCollecting__pbt",
  "explorer/takeCollecting__pbt_e",
  "explorer/takeCollecting__pbt_1",
  "explorer/takeCollecting__lbt",
  "explorer/takeCollecting__lbt_bf",
  "explorer/takeCollecting__lpbt_1",
  "explorer/takeCollecting__p1",
  "explorer/takeCollecting__p12",
  "explorer/takeCollecting__p123",
  "explorer/takeCollecting__pee",
  "explorer/takeCollecting__pe1",
  "explorer/takeCollecting__p1e",
  "explorer/takeCollecting__p12_3",
  "explorer/takeCollecting__p12_34",
  "explorer/takeCollecting__pe_12",
  "explorer/takeCollecting__ppe1_2",
  "explorer/takeCollecting__p12_e",
  "explorer/takeCollecting__ppe",
  "explorer/takeCollecting__pp1",
  "explorer/takeCollecting__ppp12",
  "explorer/takeCollecting__le",
  "explorer/takeCollecting__l7",
  "explorer/takeCollecting__l12",
  "explorer/takeCollecting__l12_3",
  "explorer/takeCollecting__lle",
  "explorer/takeCollecting__l_e",
  "explorer/takeCollecting__l_p12",
  "explorer/takeCollecting__p_l12",
  "explorer/takeCollecting__pl1",
  "explorer/special__multiProp",
  "explorer/special__multiPropCall",
  "explorer/special__multiPropIndex0",
  "explorer/special__multiPropEq",
  "explorer/special__propBodyEmptySlot",
  "explorer/special__eqSpreadSeqLiteral",
  "spec/property-call-boundary",
  "spec/newline-grammar-priority-continuation",
  "explorer/special__multiPropCount",
  "explorer/special__multiPropDotCount",
  "explorer/special__multiCollectingCount",
  "explorer/special__collectingFwdSum",
  "explorer/special__collectingFwdSpread",
  "explorer/special__range13",
  "explorer/special__rangeIndex0",
  "spec/range-inclusive",
  "spec/range-single-value",
  "spec/range-integral-bound-quantum",
  "spec/list-index-builtin-results",
  "explorer/special__rangeCapture",
  "explorer/special__rangeCount",
  "explorer/special__filterOneSurvivor",
  "spec/filter-single-survivor",
  "explorer/special__filterOneSurvivorCount",
  "explorer/special__filterZeroSurvivors",
  "spec/filter-none-empty",
  "explorer/special__mapPairSwap",
  "explorer/special__mapPairSwapOk",
  "explorer/special__mapPairSwapFlatIsArity",
  "spec/map-pair-callback",
  "explorer/special__indexCapturedEq",
  "explorer/special__listIndexCapturedEq",
  "spec/index-captured-requality",
  "explorer/special__nestedWrittenArg",
  "explorer/special__listFixedCallBoundary",
  "explorer/special__writtenSlotArity",
  "explorer/special__mixedSingleGrouped",
  "explorer/special__sumEmpty",
  "explorer/special__rootSpreadExtra",
  "explorer/special__spreadOfSpreadSeqLiteral",
  "explorer/special__listSpreadOfSeqProp",
  "explorer/special__listSpreadBetween",
  "explorer/special__listInSeqSpreadKeepsList",
  "spec/empty-capture",
  "spec/capture-supply",
  "spec/capture-supply-spread",
  "spec/root-spread-beside-slot",
  "spec/line-final-star-attached-at-eof-is-spread",
  "spec/missing-output-not-a-value",
  "explorer/special__loopSpreadHistoryFlat",
  "explorer/special__ifBranchSeq",
  "spec/if-arity-is-uniform-across-spellings",
  "explorer/special__chainPropertyOperands",
  "explorer/special__chainCallOperands",
  "explorer/special__listOfLists",
  "explorer/special__listSpreadConcat",
  "explorer/special__listMixedSpread",
  "spec/eq-structural-nested",
  "spec/output-rows-interleave-definitions",
  "spec/star-before-operand-row-is-multiplication",
  "spec/star-before-declaration-or-boundary-is-spread",
  "explorer/special__listSpreadCaptureRoundTrip",
  "explorer/special__listCollectingNotSequenceKind",
  "explorer/special__listCollectingCollectsExactList",
  "spec/decon-collecting-tail",
  "explorer/special__implicitForwardOrdinarySource",
  "explorer/special__callbackSingleCollectingMap",
  "explorer/special__callbackMixedCollectingRow",
  "explorer/special__callbackMixedCollectingRowPattern",
  "explorer/special__callbackCollectingElementIsOneArgument",
  "explorer/special__collectorZeroArgumentCallableFailureIsItsOwn",
  "explorer/special__listCollectingSpreadCall",
  "explorer/special__spreadNoOutputBlockRoot",
  "explorer/special__spreadNoOutputBlockList",
  "explorer/special__spreadInnerOwnKept",
  "explorer/special__spreadNoOutputBlockCallArg",
  "explorer/special__spreadNoOutputResolved",
  "explorer/special__spreadNestedDependency",
  "explorer/special__spreadNestedDependencyCall",
  "explorer/special__spreadOwnInvoked",
  "explorer/special__spreadNestedCapture",
  "explorer/special__spreadNestedList",
  "explorer/special__spreadNestedArgument",
  "explorer/special__spreadNestedRow",
  "explorer/special__spreadNestedBuiltinArgument",
  "explorer/special__spreadNestedFamilyMatch",
  "explorer/special__spreadNestedPatternBinding",
  "explorer/special__spreadNestedStringReceiver",
  "explorer/special__spreadNestedSupplySlot",
  "explorer/special__spreadNestedCallbackSlot",
  "explorer/special__spreadForwardedOwn",
  "explorer/special__spreadForwardedNested",
  "explorer/special__spreadCollectorElement",
  "explorer/special__spreadForwardedCollectorElement",
  "explorer/special__listLoneCollectingAssignment",
  "explorer/special__minSeq",
  "explorer/special__minList",
  "explorer/special__minScalar",
  "explorer/special__minEmpty",
  "explorer/special__minNestedItem",
  "spec/aggregate-empty-is-domain-error",
  "explorer/special__minDot",
  "explorer/special__maxSeq",
  "explorer/special__maxList",
  "explorer/special__maxEmpty",
  "explorer/special__maxDot",
  "explorer/special__firstSeq",
  "explorer/special__firstScalar",
  "explorer/special__firstListElementStaysExact",
  "explorer/special__firstEmptyItem",
  "explorer/special__firstEmpty",
  "spec/first-last-empty-is-bad-index",
  "explorer/special__firstDot",
  "explorer/special__lastSeq",
  "explorer/special__lastListElementStaysExact",
  "explorer/special__lastEmpty",
  "explorer/special__orderDescSeq",
  "explorer/special__orderDescList",
  "explorer/special__orderDescDuplicates",
  "explorer/special__orderDescScalar",
  "explorer/special__orderDescEmpty",
  "explorer/special__orderDescString",
  "explorer/special__orderDescDot",
  "explorer/special__whileCountdown",
  "explorer/special__whileZeroIterations",
  "explorer/special__whileEmptyInitialState",
  "explorer/special__whileNonNumericContinuation",
  "explorer/special__whileTwoSlotState",
  "explorer/special__whileDot",
  "explorer/special__loopResultIsOneRow",
  "explorer/special__loopResultBesideAnotherRow",
  "explorer/special__loopResultSpreadOpensIt",
  "explorer/special__loopZeroSlotResult",
  "explorer/special__repeatedNameStepSpreadRowIsTwoSlots",
  "explorer/special__repeatedNameStepDivergingRowsRebindFails",
  "explorer/special__structuralStepSpreadRowSuppliesItems",
  "explorer/special__structuralStepSpreadRowCannotRebind",
  "explorer/special__historyStepSpreadRowEqualsDirectCall",
  "explorer/special__nestedLoopStepRowIsOneSlot",
  "explorer/special__nestedLoopStepRowSpread",
  "spec/loop-nested-step-row-is-one-slot",
  "explorer/special__callbackBodyLoopIsOneValue",
  "explorer/special__loopStepClauseFamily",
  "spec/loop-step-clause-family",
  "explorer/special__loopStepFamilyWhile",
  "explorer/special__loopStepFamilyMultiSlot",
  "explorer/special__loopStepFamilyRowsAreTheNextState",
  "explorer/special__loopStepFamilyNoMatch",
  "spec/loop-step-family-no-match-is-ordinary",
  "explorer/special__loopStepFamilyClauseOrder",
  "explorer/special__loopStepFamilyStructural",
  "explorer/special__loopStepFamilyRepeatedName",
  "explorer/special__loopStepBuiltinOneRow",
  "explorer/special__loopStepBuiltinCollectionNextArity",
  "explorer/special__loopStepBuiltinEmptyResultIsTheFlag",
  "spec/loop-step-builtin-empty-result-is-one-slot",
  "explorer/special__loopStepBuiltinLazyIf",
  "spec/loop-step-lazy-builtin-roles",
  "explorer/special__loopStepAliasOfFamilyAndBuiltin",
  "spec/loop-step-alias-follows-target",
  "explorer/special__loopStepForwardedFamily",
  "explorer/special__loopStepValueRejected",
  "spec/loop-step-value-is-rejected",
  "explorer/special__loopStepZeroIterationsNeverProject",
  "spec/loop-step-zero-iterations-never-projects",
  "explorer/special__loopMetaValueRefused",
  "explorer/special__loopMetaPropertyReadRefused",
  "spec/loop-meta-no-implicit-provenance",
  "explorer/special__loopMetaPlainAndDot",
  "spec/loop-meta-plain-and-dot",
  "explorer/special__loopMetaZeroState",
  "spec/loop-meta-zero-state",
  "explorer/special__loopMetaSpreadBeforeCount",
  "spec/loop-meta-spread-before-count",
  "explorer/special__loopMetaExactArity",
  "spec/loop-meta-exact-arity",
  "explorer/special__loopMetaQualifiedCalleeCaptured",
  "explorer/special__loopMetaBareMemberPathRefused",
  "spec/loop-meta-qualified-step",
  "explorer/special__loopMetaRebuiltProjectedStep",
  "explorer/special__metaExtensionReceiverIsSupplied",
  "explorer/special__loopMetaNamedAlias",
  "explorer/special__loopStepLoopBuiltinAsStep",
  "explorer/special__containsSequenceItem",
  "explorer/special__containsListItem",
  "explorer/special__containsEmptyItem",
  "explorer/special__containsScalarCollection",
  "explorer/special__containsAcrossKinds",
  "explorer/special__openPublicMember",
  "explorer/special__openPrivateMemberHidden",
  "explorer/special__openLocalOnlyCapturedParamsInsideOwner",
  "explorer/special__openLocalOnlyCapturedParamsOutsideOwner",
  "explorer/special__providerRequiringArgumentsCannotBeOpened",
  "spec/open-parameterized-provider-rejected",
  "explorer/special__openTwoProvidersAmbiguous",
  "explorer/special__openTwoProvidersAmbiguousAtRuntime",
  "explorer/special__openDuplicateTargetDedup",
  "explorer/special__openDuplicateDottedTargetDedup",
  "explorer/special__openTwoSpellingsOneProvider",
  "spec/open-two-spellings-one-provider",
  "explorer/special__openDuplicateInlineBlocksAmbiguous",
  "explorer/special__openDuplicateInlineBlocksAmbiguousAtRuntime",
  "explorer/special__openInlineBlock",
  "explorer/special__openInlineBlockPrivateHidden",
  "spec/open-inline-headed-path-must-resolve",
  "explorer/special__openDottedPath",
  "explorer/special__openDottedPathPrivateIntermediate",
  "explorer/special__openLocalShadowsOpenedName",
  "explorer/special__openAncestorPropertyWins",
  "explorer/special__openParentScopeReachesChild",
  "explorer/special__openNestedDoesNotLeakOutward",
  "explorer/special__openHeadDefinedLater",
  "explorer/special__openBuiltinNameCollision",
  "explorer/special__openBuiltinTargetIsIllegal",
  "explorer/special__structuralDotSeesPrivateMember",
  "explorer/special__openPrivateMemberIsNotASecondProvider",
  "explorer/special__openLocalOnlyMemberIsASecondProvider",
  "spec/open-local-only-member-is-a-second-provider",
  "explorer/special__openLocalOnlyMemberIsASecondProviderAtRuntime",
  "explorer/special__ifSelectedParameterizedBranchIsArity",
  "explorer/special__ifSelectedParameterizedFalseBranchIsArity",
  "explorer/special__ifParameterizedConditionIsArity",
  "explorer/special__ifUnselectedParameterizedBranchStaysLazy",
  "spec/lazy-slot-demand-is-the-ordinary-zero-argument-demand",
  "explorer/special__ifZeroParameterBranchIsValue",
  "explorer/special__ifParameterIgnoringBodyStillArity",
  "explorer/special__ifCollectingCallableSlotIsCollectedValue",
  "explorer/special__ifCollectingCallableExplicitCallIsSameValue",
  "explorer/special__bareCollectingCallableIsAValue",
  "spec/zero-argument-demand-follows-actual-call-arity",
  "explorer/special__bareCollectingCallableCountAgreesWithDottedForm",
  "explorer/special__ifRequiredPrefixBesideCollectorIsArity",
  "explorer/special__ifRequiredSuffixBesideCollectorIsArity",
  "explorer/special__ifNestedCollectingPatternIsArity",
  "explorer/special__collectingCallableStaysACallbackAlgorithm",
  "explorer/special__ifAlgorithmChannelParameterSlotIsArity",
  "explorer/special__repeatInitialParameterizedSlotIsArity",
  "explorer/special__repeatCountParameterizedSlotIsArity",
  "spec/lazy-slot-demand-covers-every-builtin-value-slot",
  "explorer/special__whileInitialParameterizedSlotIsArity",
  "explorer/special__atomsParameterizedSlotIsArity",
  "explorer/special__rangeParameterizedSlotIsArity",
  "explorer/special__dotStringParameterizedReceiverIsArity",
  "spec/dot-string-receiver-is-a-zero-argument-value-demand",
  "explorer/special__dotStringNavigatedParameterizedMemberIsArity",
  "explorer/special__reduceParameterIgnoringInitialStillRejected",
  "explorer/special__repeatParameterizedStepIsCallback",
  "explorer/special__formulaLiftingIfBranchLiftsWhileStayingLazy",
  "explorer/special__formulaLiftingRootValuePositionNeedsTheParameter",
  "explorer/special__formulaLiftingBuiltinValueSlot",
  "explorer/special__formulaLiftingBuiltinSignature",
  "explorer/special__formulaLiftingLoopSignature",
  "explorer/special__formulaLiftingDottedMember",
  "explorer/special__formulaLiftingOpenedMember",
  "explorer/special__formulaLiftingClauseFamily",
  "explorer/special__formulaLiftingCaptureElement",
  "explorer/special__formulaLiftingStringReceiver",
  "explorer/special__formulaLiftingNestedInUserArgument",
  "explorer/special__formulaLiftingKeepsCallbacks",
  "explorer/special__formulaLiftingKeepsUserArguments",
  "explorer/special__repeatedNameCallableThenValue",
  "explorer/special__repeatedNameValueThenCallable",
  "spec/repeated-name-is-a-constraint-not-a-merge",
  "explorer/special__repeatedNameFailedThenValue",
  "explorer/special__repeatedNameValueThenFailed",
  "explorer/special__repeatedNameAcrossCollectorCallable",
  "explorer/special__repeatedNameAcrossNestedGroupFailed",
  "explorer/special__repeatedNameForwardedCallable",
  "explorer/special__repeatedNameDotReceiverFailed",
  "explorer/special__repeatedNameValuelessBeforeVerdict",
  "explorer/special__repeatedNameAccompanyingChannel",
  "explorer/special__forwardByNameAlias",
  "explorer/special__forwardByNameThreeOccurrences",
  "explorer/special__forwardByNameInsideOneGroup",
  "explorer/special__forwardByNameNestedGroup",
  "explorer/special__forwardByNameAcrossGroup",
  "explorer/special__forwardByNameBesideCollector",
  "explorer/special__forwardByNameClosedList",
  "explorer/special__bareForwardingRepeatedName",
  "explorer/special__forwardByNameAcrossCallees",
  "explorer/special__forwardByNameFailedArgument",
  "explorer/special__forwardByNameCallableArgument",
  "explorer/special__aliasKeepsRepeatedSignature",
  "explorer/special__aliasKeepsRepeatedConstraint",
  "explorer/special__aliasKeepsListPattern",
  "explorer/special__aliasKeepsListPatternRejection",
  "explorer/special__aliasKeepsBinderlessSignature",
  "explorer/special__aliasOfCollectorKeepsSignature",
  "explorer/special__aliasChainKeepsSignature",
  "explorer/special__aliasOfBuiltinCount",
  "explorer/special__aliasOfIfIsLazy",
  "explorer/special__aliasOfMapDemandsNoCallback",
  "explorer/special__aliasOfRepeatKeepsMinimumArity",
  "explorer/special__aliasChainOfBuiltin",
  "explorer/special__aliasOfFamilyDispatches",
  "explorer/special__aliasOfFamilyNoMatchingBranch",
  "spec/alias-of-a-clause-family-dispatches-as-the-family",
  "explorer/special__aliasOfUnnameableFamily",
  "explorer/special__aliasRolesAreTargetRoles",
  "spec/alias-arguments-take-the-targets-roles",
  "explorer/special__aliasCallableIdentityIsTarget",
  "spec/alias-is-the-targets-callable",
  "explorer/special__aliasPassedAsCallableNavigatesTarget",
  "explorer/special__bareForwardingThroughAlias",
  "explorer/special__formulaLiftingThroughAlias",
  "explorer/special__bareForwardingSameName",
  "explorer/special__bareForwardingIsNotPositional",
  "explorer/special__bareForwardingIgnoresUnusedParameter",
  "explorer/special__bareForwardingOfAZeroParameterTarget",
  "explorer/special__bareForwardingSamePattern",
  "explorer/special__bareForwardingRespreadsItsCollector",
  "explorer/special__bareForwardingBranchForwardsItsBinder",
  "explorer/special__bareForwardingReusesEnclosingBinding",
  "explorer/special__writtenCallInfersWrittenNames",
  "explorer/special__writtenCallIgnoresCalleeBinderNames",
  "spec/need-selected-signature-payload",
  "spec/need-variadic-minimum-payload",
  "spec/need-closed-core-demand-is-runtime",
  "spec/need-unused-ordinary-argument",
  "spec/need-explicit-spread-precedes-arity",
  "spec/patterned-user-call-is-one-value-boundary",
  "spec/need-unused-collector-slice",
  "spec/need-forwarding-preserves-unused-cell",
  "spec/need-collector-forwarding-preserves-unused-slice",
  "spec/need-ordinary-conditional-selects-one-cell",
  "spec/need-family-shares-failed-attempt-value",
  "spec/need-first-loop-step-can-ignore-initial",
  "spec/need-closed-demand-can-remain-unused",
  "spec/need-wrong-arity-precedes-cell-demand",
  "spec/variadic-capture-collects-list",
  "spec/need-collector-demand-materializes-whole-slice",
  "spec/selective-collector-selection-demands-selected-positions",
  "spec/selective-collector-whole-value-stays-eager",
  "spec/selective-collector-written-list-stays-eager",
  "spec/need-callable-projection-does-not-force-value",
  "spec/need-demand-order-decides-the-first-failure",
  "spec/need-wrapper-keeps-builtin-if-selection",
  "spec/need-container-call-checks-cardinality-first",
  "spec/need-dot-receiver-is-a-supplied-computation",
  "spec/need-dot-receiver-follows-callee-demand-order",
  "spec/need-family-binder-keeps-the-callable",
  "spec/need-deconstruction-runs-on-first-target-demand",
  "spec/collector-alias-keeps-known-slice",
  "spec/collector-carrier-spread-is-arbitrary",
  "spec/collector-alias-keeps-callable-elements",
  "spec/collector-alias-demand-raises-the-element-failure",
  "spec/collector-reference-argument-keeps-known-slice",
  "spec/collector-reference-argument-carrier-stays-arbitrary",
  "spec/collector-reference-argument-is-one-argument",
  "spec/collector-reference-argument-keeps-callable-elements",
  "spec/collector-reference-argument-arity-precedes-elements",
  "spec/selective-collector-count-reads-positions",
  "spec/selective-collector-first-selects-one-element",
  "spec/selective-collector-take-demands-its-prefix",
  "spec/selective-collector-take-needs-the-prefix-element",
  "spec/selective-collector-effects-follow-first-demand",
  "spec/selective-collector-reads-through-a-transparent-reference",
  "spec/selective-collector-carrier-stays-eager",
  "spec/collector-member-path-keeps-known-slice",
  "spec/collector-member-nontransparent-spread-is-arbitrary",
  "spec/collector-member-path-keeps-callable-elements",
  "spec/collector-member-path-demand-raises-the-element-failure",
  "spec/collected-callable-survives-explicit-respread",
  "spec/boolean-predicates-and-patterns",
  "spec/boolean-loop-state-transition",
  "spec/boolean-predicate-rejects-visible-empty",
  "spec/integer-division-exact-quotient",
  "spec/property-access-and-call",
  "spec/output-is-ordinary-property",
  "spec/empty-eq-family",
  "spec/call-reentry-identity",
  "spec/call-value-boundary",
  "spec/loop-result-is-one-value",
  "spec/loop-step-patterns-only-bind",
  "spec/loop-step-family-while",
  "spec/loop-while-condition-first-skips-transition",
  "spec/loop-while-condition-first-trailing-empty-spread",
  "spec/loop-while-condition-first-row-granular",
  "spec/loop-step-family-multi-slot",
  "spec/loop-step-builtin-is-one-row-wrapper",
  "spec/loop-step-builtin-argument-blame",
  "spec/loop-meta-forwarding",
  "spec/property-value-boundary",
  "spec/spread-capture-count",
  "spec/repeated-spread-fixed-point",
  "spec/repeated-spread-singleton-opens",
  "spec/scalar-spread-neutral",
  "spec/select-spread-vs-capture-select",
  "spec/list-literal-spread-elements",
  "spec/fixed-call-preserves-boundaries",
  "spec/spread-fills-remaining-slots",
  "spec/variadic-empty-arg-vs-spread",
  "spec/decon-pair",
  "spec/list-deconstruction-not-recursive",
  "spec/decon-rhs-implicit-parameter",
  "spec/decon-rhs-brace-scope",
  "spec/decon-rhs-lifted-parameter-order",
  "spec/decon-collecting-head",
  "spec/decon-collecting-middle",
  "spec/decon-empty-collecting",
  "spec/decon-unpacks-stored-value",
  "spec/decon-tutorial-full",
  "spec/decon-lone-collecting",
  "spec/variadic-grouped-and-spread",
  "spec/variadic-siblings-preserved",
  "spec/variadic-forwarding-list-spread",
  "spec/implicit-forwarding-source-kind",
  "spec/variadic-receiver-distinction",
  "spec/dot-receiver-passes-a-value",
  "spec/values-stay-values",
  "spec/callback-element-is-one-argument",
  "spec/parentheses-group-syntax",
  "spec/mixed-collecting-parameter",
  "spec/mixed-front-back-family",
  "spec/collecting-minimum-arity",
  "spec/variadic-grouped-vs-spread",
  "spec/variadic-nested-not-flattened",
  "spec/supply-vs-value-patterns",
  "spec/list-patterns-cover-every-cardinality",
  "spec/nested-structural-patterns-keep-their-kind",
  "spec/structural-patterns-open-only-their-own-kind",
  "spec/binding-failure-outranks-repeated-name-conflict",
  "spec/repeated-name-binding-is-order-independent",
  "spec/repeated-equal-values-require-one-callable-identity",
  "spec/implicit-forwarding-is-by-binding-name",
  "spec/formula-lifting-is-one-law-for-every-callable",
  "spec/formula-lifting-follows-the-consumers-role",
  "spec/unliftable-clause-family",
  "spec/root-row-block-head-is-elaborated",
  "spec/root-row-block-head-reports-front-end-errors",
  "spec/repeated-name-wrapper-keeps-independent-arguments",
  "spec/implicit-forwarding-preserves-structural-kind",
  "spec/alias-forwarding-and-explicit-call",
  "spec/bare-forwarding-never-renames-a-parameter",
  "spec/bare-forwarding-never-adds-a-parameter",
  "spec/alias-structural-forwarding-and-written-call",
  "spec/bare-forwarding-never-reshapes-a-structural-parameter",
  "spec/bare-forwarding-never-manufactures-a-sequence",
  "spec/alias-preserves-the-callee-signature",
  "spec/inline-alias-value-demand-is-the-target-contract",
  "spec/inline-formula-block-keeps-unresolved-implicit-params",
  "spec/alias-of-a-builtin-is-the-builtin",
  "spec/bare-forwarding-needs-parameter-names",
  "spec/reference-members-are-the-targets-carrier-members-its-own",
  "spec/open-of-a-callable-alias-is-refused",
  "spec/reference-and-carrier-transport-the-whole-definition",
  "spec/repeated-name-matches-definitions-by-identity",
  "spec/open-through-a-reference-opens-the-target",
  "spec/member-path-alias-is-a-member-reference",
  "spec/bare-forwarding-keeps-each-parameter-kind",
  "spec/written-call-infers-its-written-names",
  "spec/repeated-callable-success-preserves-both-channels",
  "spec/repeated-genuine-aliases-preserve-complete-binding",
  "spec/repeated-callable-identity-includes-captured-activation",
  "spec/repeated-dot-results-have-distinct-wrapper-identities",
  "spec/repeated-forwarded-dot-wrapper-keeps-identity",
  "spec/collecting-pattern-list-merges-after-the-collector",
  "spec/redundant-call-parens-canonical",
  "spec/call-spread-into-conditional-clauses",
  "spec/call-spread-dispatches-before-clause-selection",
  "spec/conditional-one-element-list-pattern",
  "spec/conditional-sequence-pattern-matches-sequence-values-only",
  "spec/empty-structural-patterns-are-distinct-heads",
  "spec/conditional-clause-head-rejects-extra-arguments",
  "spec/call-spread-into-patterned-callee",
  "spec/root-spread-then-value-slot",
  "spec/spread-slots-capture",
  "spec/open-local-only-through-capture-row",
  "spec/open-self-contained-beside-same-named-sibling",
  "spec/zero-param-block-higher-order",
  "spec/dot-member-higher-order-parameter",
  "spec/dot-member-fallback-implicit-signature",
  "spec/grace-dot-higher-order-implicit",
  "spec/grace-dot-keeps-structural-precedence",
  "spec/dot-member-fallback-in-closed-parameter-list",
  "spec/dot-fallback-on-known-receiver-stays-valid",
  "spec/dot-string-declared-member-wins",
  "spec/dot-string-intrinsic-on-structural-miss",
  "spec/grouped-structural-callee-is-the-member",
  "spec/grouped-zero-arg-member-call-is-fresh",
  "spec/computed-dot-callee-is-not-callable",
  "spec/closed-list-must-fallback-name-is-checked",
  "spec/closed-list-may-fallback-name-is-runtime",
  "spec/branch-must-fallback-name-is-checked",
  "spec/open-local-only-member-inside-owner",
  "spec/dot-local-only-member-outside-owner",
  "spec/dot-local-only-reference-target-walk",
  "spec/dot-local-only-inline-block-head",
  "spec/open-local-only-through-reference",
  "spec/open-local-only-enclosing-level",
  "spec/open-block-headed-reference-keeps-requirement",
  "spec/impossible-read-in-untaken-branch-charges-nothing",
  "spec/open-reference-checked-where-it-is-opened",
  "spec/open-block-headed-reference-target-must-resolve",
  "spec/dot-exported-inline-block-head-member",
  "spec/dot-exported-value-only-reference",
  "spec/open-exported-runtime-reference",
  "spec/dot-path-fallback-edges-charge-their-callee",
  "spec/dot-path-fallback-edges-inline-block-head",
  "spec/deconstruction-source-inline-block-member",
  "spec/open-distinct-declarations-stay-distinct-providers",
  "spec/open-identical-inline-blocks-two-providers",
  "spec/ambiguous-open-written-use-is-static",
  "spec/ambiguous-open-unused-overlap-is-valid",
  "spec/dot-chain-structural-member-beats-extension",
  "spec/dot-chain-extension-fallback-composes",
  "spec/dot-chain-nested-structural-members",
  "spec/dot-chain-local-only-member-is-not-a-fallback",
  "spec/inline-headed-open-paths-keep-distinct-providers",
  "spec/capture-suppresses-higher-order-identity",
  "spec/capture-suppresses-structural-members",
  "spec/output-dotted-access-ordinary",
  "spec/dot-call-structural-member-is-not-a-lexical-rewrite",
  "spec/visibility-private-member-is-structural-not-exported",
  "spec/zero-arg-access-of-parametrized",
  "spec/multiline-call-open-delimiter",
  "spec/filter-keeps-matching",
  "spec/map-transforms-items",
  "spec/clause-family-multirow-callback-is-one-value",
  "spec/clause-family-multirow-reduce-step-is-one-value",
  "spec/clause-family-callback-single-value-accepted",
  "spec/callback-result-is-the-ordinary-call-result",
  "spec/reduce-demands-initial-before-iteration",
  "spec/nested-reducer-calls-may-skip-unused-initial",
  "spec/map-demands-collection-before-transforms",
  "spec/expanded-map-calls-may-skip-indexed-arguments",
  "spec/map-identity-preserves-empty-elements",
  "spec/reduce-accumulator-may-be-empty",
  "spec/callback-variadic-collects",
  "spec/callback-mixed-variadic-rows",
  "spec/callback-nested-pattern-binds-like-call",
  "spec/forwarded-callable-keeps-its-algorithm-channel",
  "spec/builtin-call-assembly-respects-argument-roles",
  "spec/take-family-tutorial",
  "spec/distinct-family-tutorial",
  "spec/spread-arguments-keep-written-order",
  "spec/atoms-list-composition",
  "spec/atoms-no-truthiness",
  "spec/sum-of-range-collection",
  "spec/count-family",
  "spec/count-dotcount-agree",
  "spec/if-value-boundary",
  "spec/reduce-accumulates-value",
  "spec/reduce-empty-initial-is-one-value",
  "spec/index-selects-atom",
  "spec/index-selects-one-value",
  "spec/selection-forms-agree",
  "spec/index-nested-stays-intact",
  "spec/variadic-selection-several-values",
  "spec/variadic-selection-bracket-on-a-later-line-is-a-list",
  "spec/variadic-selection-keeps-empty-values",
  "spec/variadic-selection-has-no-callable-identity",
  "spec/line-final-star-in-definition-continues",
  "spec/grace-on-bound-name-rejected",
  "spec/grace-under-explicit-list-rejected",
  "spec/grace-in-branch-deconstruction-rejected",
  "spec/grace-in-branch-nested-block-belongs-to-the-block",
  "spec/grace-saturation-is-valid",
  "spec/grace-on-branch-binder-in-nested-block-rejected",
  "spec/grace-weights-accumulate",
  "spec/grace-front-first-movement",
  "spec/grace-prefix-marker-led-row",
  "spec/adjacency-call-across-space",
  "spec/newline-ends-property-body",
  "spec/spread-binds-before-list",
  "spec/dot-chain-continuation",
  "spec/arity-too-many-arguments",
  "spec/spread-preserves-nested-missing-output",
  "spec/missing-output-as-builtin-arg",
  "spec/output-less-argument-is-not-an-omitted-argument",
  "spec/argument-value-outcome-is-final",
  "spec/invoking-slot-without-callable-is-not-an-algorithm",
  "spec/zero-parameter-callable-in-invoking-slot-is-arity",
  "spec/spread-arguments-fail-left-to-right",
  "spec/unresolved-implicit-parameter",
  "spec/list-index-nested-element-stays-exact",
  "spec/list-spread-capture",
  "spec/list-spread-edges",
  "spec/list-elements-preserve-boundaries",
  "spec/list-written-slot-reifies-selection",
  "spec/list-call-boundary",
  "spec/list-lone-deconstruction",
  "spec/collecting-binding-exact-list",
  "spec/list-lone-collecting-assignment",
  "spec/avg-decimal-mean",
  "spec/avg-is-the-correctly-rounded-exact-mean",
  "spec/nan-equality-vs-ordering",
  "spec/native-flat-callback-binding",
  "spec/callable-argument-parameter-shadowing",
  "spec/value-argument-parameter-shadowing",
  "spec/value-parameter-shadowing-through-nested-scope",
  "spec/value-binder-parameter-shadowing",
  "spec/ancestor-callable-visible-without-same-named-parameter",
  "spec/ownership-same-owner-nested-reference-rejected",
  "spec/ownership-same-owner-later-property-rejected",
  "spec/ownership-branch-binder-property-collision",
  "spec/ownership-lifted-parameter-property-collision",
  "spec/forwarded-parameter-leaves-an-opened-reference",
  "spec/forwarded-parameter-names-nothing-in-a-closed-body",
  "spec/forwarding-reuses-a-captured-ancestor-parameter",
  "spec/forwarding-never-supplies-a-property-an-open-or-a-builtin",
  "spec/forwarding-reused-binding-kind-preserves-values",
  "spec/ownership-captured-parameter-beats-outer-property",
  "spec/ownership-same-owner-parameter-beats-property",
  "spec/ownership-nearer-property-beats-outer-parameter",
  "spec/ownership-nearest-enclosing-parameter-wins",
  "spec/ownership-parameter-beats-prelude-alias",
  "spec/ownership-parameter-beats-opened-name",
  "spec/ownership-open-target-parameter-rejected",
  "spec/ownership-open-target-parameter-without-farther-declaration",
  "spec/ownership-open-qualified-target-parameter-rejected",
  "spec/ownership-open-target-enclosing-parameter-rejected",
  "spec/native-argument-value-demand",
  "spec/closed-list-strict-value-forwarding",
  "spec/clause-family-nested-in-branch-body-binds-its-own-binders",
  "spec/conditional-branch-pattern-is-a-closed-input-specification",
  "spec/expression-position-block-closed-list-is-diagnosed",
  "spec/conditional-branch-inline-open-exposes-members-to-the-branch",
  "spec/conditional-branch-inline-open-does-not-leak-to-sibling-branches",
  "spec/conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches",
  "spec/conditional-branch-local-library-is-openable-within-the-branch",
  "spec/conditional-branch-local-library-does-not-leak-to-sibling-branches",
  "spec/builtin-callable-is-an-ordinary-prelude-binding",
  "spec/no-arity-based-callable-selection",
  "spec/if-composition-forms-agree",
  "spec/if-laziness-follows-the-resolved-identity",
  "spec/dot-string-parameter-receiver-reports-the-written-argument",
  "spec/zero-argument-callable-name-is-read-not-lifted",
  "spec/same-arity-user-if-keeps-user-identity",
  "spec/parameter-named-if-carries-the-supplied-callable",
  "spec/if-spread-builds-values-before-branch-selection",
  "spec/dot-string-intrinsic-rejects-arguments",
  "spec/ownership-open-provided-captured-member-read-by-sibling-is-local-only",
  "spec/ownership-open-head-between-opener-and-settling-level-charges-the-capture",
  "spec/grace-in-redundant-group-is-grace-on-the-name",
  "spec/open-builtin-target-rejected",
  "spec/min-max-signed-zero",
  "spec/repeated-name-keeps-first-equally-rich-representative",
  "spec/decimal-literal-patterns-match-by-value",
  "spec/max-decimal-places-rounds-ties-away-from-zero",
  "spec/decimal-places-show-the-value-not-the-stored-digits",
  "spec/min-decimal-places-pads-and-never-rounds",
  "spec/equal-min-and-max-decimal-places-fix-the-places",
  "spec/logarithm-near-one-is-accurate",
  "spec/negative-near-one-base-power-is-sign-symmetric",
  "spec/string-literal-pattern-selects-a-clause",
  "spec/string-and-number-stay-separate-items",
  "spec/meta-capture-invokes-the-original-call",
  "spec/meta-capture-sees-through-forwarding-and-value",
  "spec/meta-refuses-anything-but-a-written-call",
  "spec/invoke-needs-its-argument-list",
  "spec/invoke-is-not-an-extension-call",
  "spec/call-reference-never-leaves-its-run",
  "spec/call-reference-arguments-view",
  "spec/arguments-spread-forwards-the-original-arguments",
  "spec/arguments-view-is-not-a-collection",
  "spec/arguments-is-not-an-extension-call",
  "spec/call-reference-algorithm-projection",
  "spec/call-reference-algorithm-loops",
  "spec/algorithm-is-not-an-extension-call",
  "spec/algorithm-projection-cycle",
  "spec/runtime-alias-of-a-parameter",
  "spec/runtime-alias-of-a-projection",
  "spec/runtime-alias-of-a-parameter-member",
  "spec/runtime-alias-transport-reads-the-target-members",
  "spec/runtime-alias-namespace-of-its-own-declarations",
  "spec/runtime-alias-failure-is-not-absence",
  "spec/runtime-alias-cycle",
  "spec/runtime-alias-cell-read-and-path-share-one-call",
  "spec/runtime-alias-cell-explicit-call-is-fresh",
  "spec/runtime-alias-cell-one-per-run-across-calls",
  "spec/runtime-alias-cell-unused-sibling-changes-nothing",
  "spec/runtime-alias-cell-read-from-outside-after-a-call",
  "spec/runtime-alias-self-link-is-a-demand-cycle",
  "spec/reference-head-resolves-in-its-own-scope",
  "spec/reference-receiver-is-its-target-structure",
  "spec/block-headed-reference-navigates-its-block",
  "spec/reference-behind-a-carrier-that-reads-it-back",
  "spec/reference-through-a-carrier-reads-the-carriers-member",
  "spec/same-shape-references-are-distinct-bindings",
  "spec/algorithm-member-of-a-reference-behind-a-carrier",
  "spec/carrier-of-a-parameter-in-every-activation",
  "spec/reference-cycle-through-an-open-is-no-alias",
  "spec/reference-to-a-carrier-that-leads-back-is-no-alias",
  "spec/sibling-cycle-member-path-is-read-statically",
  "spec/open-block-member-reference-opens-its-target",
  "spec/block-receiver-reference-member",
  "spec/member-miss-makes-the-body-its-own-structure",
  "spec/reference-cycle-only-the-final-providers-close-is-no-alias",
  "spec/member-path-through-a-lower-cyclic-receiver-is-no-alias",
  "spec/reference-head-is-the-parameter-its-own-scope-binds",
  "spec/open-path-into-a-parameterized-body-is-its-own-namespace",
  "spec/tick-counts-executions-in-the-run",
  "spec/tick-property-is-cached-call-is-fresh",
  "spec/tick-argument-is-one-lazy-computation",
  "spec/tick-callable-reference-is-not-an-execution",
  "spec/tick-meta-replay-is-fresh",
  "spec/tick-bare-value-requires-invocation",
  "spec/tick-argument-is-an-arity-error",
  "spec/tick-is-an-ordinary-shadowable-binding",
  "spec/grouped-runtime-member-value-call",
  "spec/grouped-runtime-member-value-arity",
  "spec/open-reference-private-member-provides-public-names",
  "spec/open-reference-private-member-keeps-private-names",
  "spec/open-runtime-link-provides-its-own-namespace",
  "spec/open-calculation-link-is-refused",
  "spec/open-reference-to-a-calculation-link-reports-the-target-refusal",
  "spec/open-parameterized-fallback-row-is-refused",
  "spec/open-link-over-a-head-only-an-open-provides-is-unresolved",
  "spec/open-of-a-link-over-a-cyclic-head-compiles-in-every-order",
  "spec/receiver-expansion-return-through-a-reference",
  "spec/receiver-expansion-return-through-a-reference-link",
  "spec/receiver-expansion-return-through-a-self-member",
  "spec/receiver-expansion-consumed-members-are-no-return",
  "spec/output-spread-marked-call-spreads-its-rows",
  "spec/output-spread-argument-and-element-slots",
  "spec/output-spread-alias-inherits-the-marker",
  "spec/output-spread-marker-on-an-alias-is-an-error",
  "spec/output-spread-value-positions-keep-one-value",
  "spec/output-spread-builtin-argument-is-spread-too",
  "spec/output-spread-not-through-a-parameter",
  "spec/output-spread-lifted-call-spreads",
  "spec/output-spread-loop-step-through-a-wrapper",
  "spec/output-spread-marked-call-as-loop-receiver",
  "spec/output-spread-zero-parameter-only-explicit-calls",
  "spec/output-spread-argument-runs-at-formation",
  "spec/output-spread-opens-one-level",
  "spec/output-spread-receiver-edge-is-the-lowered-call",
  "spec/output-spread-lifted-call-ends-known-positions",
  "spec/output-spread-reference-needs-call",
  "spec/output-spread-reference-certainly-read"
]
#guard guardedProgramIds.length == 3103

/--
The programs that contribute no guard (the reasons are counted in the partition above).
-/
def skippedProgramIds : List String := [
  "explorer/special__trailingComma",
  "explorer/special__spreadAsBinaryOperand",
  "explorer/special__semicolonSeparator",
  "explorer/special__listUnterminated",
  "explorer/special__listDefinitionInside",
  "explorer/special__doubleQuotedStringRejected",
  "explorer/special__doubleQuotedInterpolationRejected",
  "spec/not-cannot-be-a-tighter-operand",
  "spec/same-line-slots-need-comma",
  "spec/same-line-call-arguments-need-comma",
  "spec/same-line-declaration-begins-a-line",
  "spec/same-line-slot-before-spread-needs-comma",
  "spec/same-line-parameter-patterns-need-comma",
  "spec/decon-two-collecting-rejected",
  "spec/singleton-sequence-pattern-is-invalid",
  "spec/expression-is-not-a-pattern",
  "spec/conditional-clauses-share-top-level-arity",
  "spec/conditional-clauses-share-top-level-output-arity",
  "spec/call-after-argument-bearing-dot-edge-is-a-parse-error",
  "spec/open-capture-target-rejected",
  "spec/open-target-head-must-name-an-algorithm",
  "spec/open-after-clause-definition-rejected",
  "spec/semicolon-not-expression-syntax",
  "spec/trailing-comma-in-parens-rejected",
  "spec/spread-marker-must-be-attached",
  "spec/grace-marker-must-be-attached",
  "spec/declaration-head-never-spans-lines",
  "spec/collect-marker-must-be-attached",
  "spec/spread-not-binary-operand",
  "spec/retired-colon-selection-rejected",
  "spec/grace-line-final-marker-after-call-rejected",
  "spec/unary-minus-must-be-attached",
  "spec/negative-pattern-sign-must-be-attached",
  "spec/line-final-star-at-eof-is-incomplete",
  "spec/owed-closer-recovery-keeps-later-declarations",
  "spec/string-double-quotes-are-not-supported",
  "spec/string-interpolation-is-not-supported",
  "spec/string-double-quote-run-ends-with-its-line",
  "spec/meta-modifies-one-plain-parameter-name",
  "spec/output-spread-marker-must-be-attached",
  "spec/output-spread-marker-on-every-clause-or-none",
  "spec/output-spread-marker-not-on-a-deconstruction-target"
]
#guard skippedProgramIds.length == 42

end FrontEndDecisionCases
