import KatLang
import CoreTests.Common
import CoreTests.DotReceiverSegments

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- builtin arity parity guards
--------------------------------------------------------------------------------
-- `builtinAcceptsArity` is the normative arity spec (mirrored by the C#
-- `BuiltinRegistry.AcceptsArity`), while `applyBuiltinCounted` enforces
-- arities structurally via pattern-match fall-through (`applyBuiltin`
-- inherits them as its Result projection). Nothing in the
-- model itself forces the two encodings to agree, so these guards sweep every
-- builtin across argument counts 0..6 on both dispatch paths:
--   - a rejected count must fail with an arity-mismatch error, and
--   - an accepted count must never fail with one. It may still fail for
--     value/domain reasons; domain rejections (empty-collection policy,
--     numeric item shape) deliberately bottom out in `badArity`, not
--     `arityMismatch`, so the two directions stay distinguishable.

inductive BuiltinApplyOutcome where
  | succeeded
  | arityRejected
  | failedOtherwise
  deriving BEq, Repr

def builtinProbeCtx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }

/-- Apply a builtin through both the plain and the counted dispatch path. -/
def builtinApplyResults (b : KatLang.Builtin) (args : List Algorithm)
    : List (Except Error Unit) :=
  [ (KatLang.runEvalM (KatLang.applyBuiltin b args builtinProbeCtx [])).map (fun _ => ()),
    (KatLang.runEvalM (KatLang.applyBuiltinCounted b args builtinProbeCtx [])).map (fun _ => ()) ]

def classifyBuiltinApply : Except Error Unit -> BuiltinApplyOutcome
  | .ok _ => .succeeded
  | .error err =>
      if innermostIsAnyArityMismatch err then .arityRejected else .failedOtherwise

def applyBuiltinOutcomes (b : KatLang.Builtin) (args : List Algorithm)
    : List BuiltinApplyOutcome :=
  (builtinApplyResults b args).map classifyBuiltinApply

-- Dummy arguments chosen to be valid for each builtin, so accepted counts
-- exercise real success paths instead of failing for unrelated reasons.

/-- Zero-parameter algorithm producing one numeric value. -/
def builtinProbeValueArg (n : Int) : Algorithm := alg [] [] [] [.num n]

/-- `count` distinct single-value arguments `1, 2, ...`. -/
def builtinProbeValueArgs (count : Nat) : List Algorithm :=
  (List.range count).map (fun i => builtinProbeValueArg (Int.ofNat i + 1))

/-- Valid `map` transform: identity. -/
def builtinProbeMapperArg : Algorithm := alg ["x"] [] [] [.param "x"]

/-- Valid `filter` predicate: keep everything. -/
def builtinProbePredicateArg : Algorithm := alg ["x"] [] [] [.num 1]

/-- Valid `reduce` step: numeric addition. -/
def builtinProbeReducerArg : Algorithm :=
  alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]

/-- Loop step whose single output slot is a `0` continuation flag, so accepted
    `while` counts terminate after one step probe and accepted `repeat` counts
    pair it with repeat count `0`. -/
def builtinProbeLoopStepArg (paramCount : Nat) : Algorithm :=
  alg ((List.range paramCount).map (fun i => s!"s{i}")) [] [] [.num 0]

/-- Builtin-shaped dummy argument lists: suffix arguments (callbacks, counts,
    searched values) sit in their declared trailing positions, loop steps lead,
    and every remaining slot is a plain numeric value. Counts below the
    builtin's structural minimum just produce plain value lists, since those
    must be rejected before any argument is interpreted. -/
def builtinProbeArgsFor (b : KatLang.Builtin) (argCount : Nat) : List Algorithm :=
  match b with
  | .mapBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbeMapperArg]
  | .filterBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbePredicateArg]
  | .reduceBuiltin =>
      if argCount < 2 then builtinProbeValueArgs argCount
      else builtinProbeValueArgs (argCount - 2) ++ [builtinProbeReducerArg, builtinProbeValueArg 0]
  | .containsBuiltin | .takeBuiltin | .skipBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbeValueArg 1]
  | .whileBuiltin =>
      if argCount == 0 then []
      else builtinProbeLoopStepArg (argCount - 1) :: builtinProbeValueArgs (argCount - 1)
  | .repeatBuiltin =>
      if argCount == 0 then []
      else if argCount == 1 then [builtinProbeLoopStepArg 0]
      else builtinProbeLoopStepArg (argCount - 2) :: builtinProbeValueArg 0
        :: builtinProbeValueArgs (argCount - 2)
  | _ => builtinProbeValueArgs argCount

/-- Every builtin is swept for spec/dispatch arity parity. -/
def builtinArityParityTargets : List KatLang.Builtin :=
  [ .ifBuiltin, .whileBuiltin, .repeatBuiltin, .atomsBuiltin,
    .rangeBuiltin, .filterBuiltin, .mapBuiltin, .orderBuiltin, .orderDescBuiltin,
    .countBuiltin, .containsBuiltin, .firstBuiltin, .lastBuiltin, .distinctBuiltin,
    .takeBuiltin, .skipBuiltin, .minBuiltin, .maxBuiltin, .sumBuiltin,
    .avgBuiltin, .reduceBuiltin ]

/-- Compile-time exhaustiveness pin: this match is deliberately wildcard-free,
    so adding a `Builtin` constructor stops compiling here until the new
    builtin is routed into `builtinArityParityTargets`. -/
def builtinArityParitySweepCovers (b : KatLang.Builtin) : Bool :=
  match b with
  | .ifBuiltin | .whileBuiltin | .repeatBuiltin | .atomsBuiltin
  | .rangeBuiltin | .filterBuiltin | .mapBuiltin | .orderBuiltin | .orderDescBuiltin
  | .countBuiltin | .containsBuiltin | .firstBuiltin | .lastBuiltin | .distinctBuiltin
  | .takeBuiltin | .skipBuiltin | .minBuiltin | .maxBuiltin | .sumBuiltin
  | .avgBuiltin | .reduceBuiltin => builtinArityParityTargets.contains b

#guard builtinArityParityTargets.all builtinArityParitySweepCovers

/-- Spec/dispatch arity parity for one builtin across counts `0..maxArgCount`:
    `builtinAcceptsArity b n = false` must surface as an arity rejection, and
    `= true` must never. -/
def builtinArityParityHolds (b : KatLang.Builtin) (maxArgCount : Nat := 6) : Bool :=
  (List.range (maxArgCount + 1)).all fun argCount =>
    let expectAccepted := KatLang.builtinAcceptsArity b argCount
    (applyBuiltinOutcomes b (builtinProbeArgsFor b argCount)).all fun outcome =>
      if expectAccepted then outcome != .arityRejected else outcome == .arityRejected

/-- Display names of builtins violating arity parity; `#eval` this on guard
    failure to see which builtin and then probe its counts directly. -/
def builtinsFailingArityParity : List String :=
  (builtinArityParityTargets.filter (fun b => !(builtinArityParityHolds b))).map
    KatLang.builtinDisplayName

#guard builtinsFailingArityParity == []

-- Keep the probe arguments honest: representative accepted counts must
-- actually succeed (not merely avoid arity errors), so a silently broken
-- dummy argument cannot make the accepted direction of the sweep vacuous.
-- Covers each builtin's accepted count (fixed-arity builtins have exactly
-- one) plus one extra-argument count for the variable-arity loop builtins
-- (`while`/`repeat`).
def builtinAcceptedAritySpotCases : List (KatLang.Builtin × Nat) :=
  [ (.ifBuiltin, 3),
    (.whileBuiltin, 2), (.whileBuiltin, 4),
    (.repeatBuiltin, 3), (.repeatBuiltin, 5),
    (.atomsBuiltin, 1), (.rangeBuiltin, 2),
    (.countBuiltin, 1),
    (.sumBuiltin, 1),
    (.avgBuiltin, 1), (.minBuiltin, 1), (.maxBuiltin, 1),
    (.firstBuiltin, 1), (.lastBuiltin, 1),
    (.distinctBuiltin, 1),
    (.orderBuiltin, 1), (.orderDescBuiltin, 1),
    (.mapBuiltin, 2),
    (.filterBuiltin, 2),
    (.containsBuiltin, 2),
    (.takeBuiltin, 2),
    (.skipBuiltin, 2),
    (.reduceBuiltin, 3) ]

def builtinAcceptedAritySpotFailures : List String :=
  (builtinAcceptedAritySpotCases.filter (fun (b, argCount) =>
    (applyBuiltinOutcomes b (builtinProbeArgsFor b argCount)).any (· != .succeeded))).map
    (fun (b, argCount) => s!"{KatLang.builtinDisplayName b}@{argCount}")

#guard builtinAcceptedAritySpotFailures == []

-- Accepted count does not promise success: the empty-collection policy rejects
-- `first(())`-style calls at the accepted count 1 with a non-arity diagnostic.
-- Pin that distinction so the accepted direction of the sweep stays meaningful.
def builtinEmptyPolicyFailuresAreNotArityErrors : Bool :=
  let emptyArg := alg [] [] [] []
  [KatLang.Builtin.firstBuiltin, .lastBuiltin, .minBuiltin, .maxBuiltin, .avgBuiltin].all
    fun b =>
      KatLang.builtinAcceptsArity b 1
      && (applyBuiltinOutcomes b [emptyArg]).all (· == .failedOtherwise)

#guard builtinEmptyPolicyFailuresAreNotArityErrors

--------------------------------------------------------------------------------
-- builtin projection parity guards
--------------------------------------------------------------------------------
-- `applyBuiltin` must behave as the Result projection of `applyBuiltinCounted`:
--   applyBuiltin b args == Prod.fst <$> applyBuiltinCounted b args
-- including identical error diagnostics and identical final evaluator state
-- (per-run zero-arg property cache). These guards pin that equivalence so the
-- non-counted path can delegate to the counted path instead of duplicating
-- builtin semantics.

def builtinProjectionParityAt (b : KatLang.Builtin) (args : List Algorithm) : Bool :=
  let plain := (KatLang.applyBuiltin b args builtinProbeCtx []).run KatLang.EvalState.empty
  let counted := (KatLang.applyBuiltinCounted b args builtinProbeCtx []).run KatLang.EvalState.empty
  match plain, counted with
  | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
      value == countedValue && reprStr plainState == reprStr countedState
  | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
  | _, _ => false

/-- Sweep the same builtin/argument-count matrix as the arity parity guards:
    valid calls, arity-rejected calls, and empty-collection domain failures
    must all project identically. -/
def builtinsFailingProjectionParity : List String :=
  (builtinArityParityTargets.filter (fun b =>
    !((List.range 7).all fun argCount =>
      builtinProjectionParityAt b (builtinProbeArgsFor b argCount)))).map
    KatLang.builtinDisplayName

#guard builtinsFailingProjectionParity == []

-- Probe shapes for cases the uniform matrix does not reach: branch forcing
-- through the counted/non-counted output cores, cache-writing property
-- access, loops that actually iterate, and per-builtin domain failures.

/-- Branch emitting two top-level outputs. -/
def builtinProbeMultiOutputArg : Algorithm := alg [] [] [] [.num 1, .num 2]

/-- Branch emitting one sequence value. -/
def builtinProbeSequenceValueOutputArg : Algorithm :=
  alg [] [] [] [.capture [.num 1, .num 2]]

/-- Branch with no output: forcing it raises `missingOutput`. -/
def builtinProbeEmptyOutputArg : Algorithm := alg [] [] [] []

/-- Branch whose output reads a cacheable zero-arg property twice, so both
    dispatch paths must leave the same per-run cache state behind. -/
def builtinProbeCachedPropArg : Algorithm :=
  algPrivate [] [] [("P", alg [] [] [] [.num 7])] [.resolve "P", .resolve "P"]

/-- `while` step `(x - 1, x - 1)`: iterates until the state reaches zero. -/
def builtinProbeDecrementStepArg : Algorithm :=
  alg ["x"] [] [] [.binary .sub (.param "x") (.num 1), .binary .sub (.param "x") (.num 1)]

/-- `repeat` step `x + 1`. -/
def builtinProbeIncrementStepArg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

/-- (label, builtin, args, expected outcome on both dispatch paths). The
    expected outcome keeps each case honest: a typo cannot silently turn an
    intended success case into two identical failures. -/
def builtinProjectionExplicitCases
    : List (String × KatLang.Builtin × List Algorithm × BuiltinApplyOutcome) :=
  [ ("if/multi-output-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeMultiOutputArg, builtinProbeValueArg 9], .succeeded),
    ("if/sequenceValue-else-branch", .ifBuiltin,
      [builtinProbeValueArg 0, builtinProbeValueArg 9, builtinProbeSequenceValueOutputArg], .succeeded),
    ("if/cached-property-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeCachedPropArg, builtinProbeValueArg 9], .succeeded),
    ("if/missing-output-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeEmptyOutputArg, builtinProbeValueArg 9], .failedOtherwise),
    -- `truthValue?` flattens the condition and reads its first numeric atom,
    -- so a sequence-value condition is truthy; only atom-free conditions are invalid.
    ("if/sequenceValue-condition-truthy", .ifBuiltin,
      [builtinProbeSequenceValueOutputArg, builtinProbeValueArg 1, builtinProbeValueArg 2], .succeeded),
    ("if/atom-free-condition", .ifBuiltin,
      [alg [] [] [] [.emptySequence 0], builtinProbeValueArg 1, builtinProbeValueArg 2],
      .failedOtherwise),
    ("while/iterates", .whileBuiltin,
      [builtinProbeDecrementStepArg, builtinProbeValueArg 2], .succeeded),
    ("repeat/iterates", .repeatBuiltin,
      [builtinProbeIncrementStepArg, builtinProbeValueArg 2, builtinProbeValueArg 5], .succeeded),
    ("repeat/negative-count", .repeatBuiltin,
      [builtinProbeLoopStepArg 1, builtinProbeValueArg (-1), builtinProbeValueArg 5], .failedOtherwise),
    ("order/sequenceValue-item", .orderBuiltin, [builtinProbeSequenceValueOutputArg], .succeeded),
    ("avg/empty-collection", .avgBuiltin, [builtinProbeEmptyOutputArg], .failedOtherwise),
    ("take/non-numeric-count", .takeBuiltin,
      [builtinProbeValueArg 1, builtinProbeSequenceValueOutputArg], .failedOtherwise) ]

def builtinProjectionExplicitCaseFailures : List String :=
  (builtinProjectionExplicitCases.filter (fun (_, b, args, expected) =>
    !(builtinProjectionParityAt b args
      && (applyBuiltinOutcomes b args).all (· == expected)))).map
    (fun (label, _, _, _) => label)

#guard builtinProjectionExplicitCaseFailures == []

--------------------------------------------------------------------------------
-- issue #130: counted `if` collapses a multi-output branch to one value
--------------------------------------------------------------------------------
-- The selected `if` branch is one argument expression, so `if` observes it as a
-- single value boundary -- exactly like value-position property access. A
-- multi-output branch property such as `X = 1, 2, 3` therefore yields the grouped
-- sequence value `(1, 2, 3)` with emitted count 1, not three separate outputs.
-- (Contrast `while`/`repeat`, whose multi-slot loop state is intentional.) These
-- guards pin the emitted count exactly, which the `.succeeded` projection-parity
-- cases above do not constrain.

/-- Branch property emitting three top-level outputs (`X = 1, 2, 3`). -/
def ifBranchThreeOutputs : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

/-- Branch property emitting three other outputs (`Y = 10, 20, 30`). -/
def ifBranchThreeOutputsAlt : Algorithm := alg [] [] [] [.num 10, .num 20, .num 30]

/-- Already-grouped branch property (`X = (1, 2, 3)`). -/
def ifBranchSequenceValue : Algorithm :=
  alg [] [] [] [.capture [.num 1, .num 2, .num 3]]

/-- Run counted `if` with an integer condition and two branch algorithms. -/
def ifCountedResult (cond : Int) (t e : Algorithm) : Except KatLang.Error KatLang.CountedResult :=
  match (KatLang.applyBuiltinCounted .ifBuiltin
      [builtinProbeValueArg cond, t, e] builtinProbeCtx []).run KatLang.EvalState.empty with
  | .ok (counted, _) => .ok counted
  | .error err => .error err

def ifCountedCollapsesMultiOutputTrueBranch : Bool :=
  match ifCountedResult 1 ifBranchThreeOutputs ifBranchThreeOutputs with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedCollapsesMultiOutputTrueBranch

def ifCountedCollapsesMultiOutputFalseBranch : Bool :=
  match ifCountedResult 0 ifBranchThreeOutputs ifBranchThreeOutputs with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedCollapsesMultiOutputFalseBranch

def ifCountedDistinctBranchesTrueSelectsThen : Bool :=
  match ifCountedResult 1 ifBranchThreeOutputs ifBranchThreeOutputsAlt with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedDistinctBranchesTrueSelectsThen

def ifCountedDistinctBranchesFalseSelectsElse : Bool :=
  match ifCountedResult 0 ifBranchThreeOutputs ifBranchThreeOutputsAlt with
  | .ok (Result.sequenceValue [Result.atom 10, Result.atom 20, Result.atom 30], 1) => true
  | _ => false

#guard ifCountedDistinctBranchesFalseSelectsElse

def ifCountedParenthesizedBranchStaysOneValue : Bool :=
  match ifCountedResult 1 ifBranchSequenceValue ifBranchSequenceValue with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedParenthesizedBranchStaysOneValue

--------------------------------------------------------------------------------
-- issue #131: explicit spread opens a value into `if`'s three argument slots
--------------------------------------------------------------------------------
-- An explicit spread argument (`if(X*)`) has a runtime-only count. The C#
-- parser is the only layer that gated `if` arity statically; the shared
-- evaluator already expands spread before applying counted `if`, via
-- `applyBuiltinCountedResolved -> expandSequenceSpreadBuiltinArguments`. So a
-- spread of `1, 2, 3` opens into the three argument slots and selects `whenTrue`
-- (2) as one value, matching the user wrapper `MyIF(a, b, c) = if(a, b, c)`.
-- This guard witnesses that no Lean evaluator change was needed for #131.

/-- One spread argument whose value opens to three top-level items (`X*`). -/
def ifSpreadThreeItemsArg : KatLang.ResolvedArgumentAlgorithm :=
  { algorithm := ifBranchThreeOutputs, spreadsSequence := true }

/-- Run counted `if` through the resolved, spread-aware builtin entry point. -/
def ifCountedResolvedResult (args : List KatLang.ResolvedArgumentAlgorithm)
    : Except KatLang.Error KatLang.CountedResult :=
  match (KatLang.applyBuiltinCountedResolved .ifBuiltin args builtinProbeCtx []).run
      KatLang.EvalState.empty with
  | .ok (counted, _) => .ok counted
  | .error err => .error err

def ifSpreadArgumentOpensIntoThreeArguments : Bool :=
  match ifCountedResolvedResult [ifSpreadThreeItemsArg] with
  | .ok (Result.atom 2, 1) => true
  | _ => false

#guard ifSpreadArgumentOpensIntoThreeArguments

-- The same holds when the spread operand is an already-grouped (count-1) value
-- `(1, 2, 3)*`: the spread supplies its items, so the argument still expands to
-- three slots. This mirrors the C# engine test for `TrueResult = (1, 2, 3)`.
def ifSpreadGroupedOperandArg : KatLang.ResolvedArgumentAlgorithm :=
  { algorithm := alg [] [] [] [.sequenceSpread (.algorithmExpr ifBranchThreeOutputs)],
    spreadsSequence := true }

def ifSpreadGroupedOperandOpensIntoThreeArguments : Bool :=
  match ifCountedResolvedResult [ifSpreadGroupedOperandArg] with
  | .ok (Result.atom 2, 1) => true
  | _ => false

#guard ifSpreadGroupedOperandOpensIntoThreeArguments

--------------------------------------------------------------------------------
-- dot-call projection parity guards
--------------------------------------------------------------------------------
-- `evalDotCallCounted` is the canonical owner of dot-call dispatch — receiver
-- resolution, structural lookup, lexical fallback with receiver injection,
-- zero-arg property access, conditional value-position dispatch, and the
-- receiver-spreading rules — and `evalDotCall` is its Result projection.
-- These guards pin representative projection parity
--   evalDotCall target name args == Prod.fst <$> evalDotCallCounted target name args
-- from identical initial state: equal Result values on success, equal error
-- diagnostics on failure (compared via Repr, so context wording is pinned),
-- and equal final evaluator state (per-run zero-arg property cache). The
-- projection makes parity true by construction; the guards keep it true
-- against any future re-duplication of the plain path.

-- Choose(0, y) = y; Choose(x, y) = x + y
def dotCallParityChooseAlg : Algorithm := .conditional none [] [
  ⟨ .sequenceValue [.litInt 0, .bind "y"], alg [] [] [] [.param "y"] ⟩,
  ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩ ]

-- G((0)) = 100; G((x)) = x
def dotCallParitySingletonSequenceValueAlg : Algorithm := .conditional none [] [
  ⟨ .sequenceValue [.litInt 0], alg [] [] [] [.num 100] ⟩,
  ⟨ .sequenceValue [.bind "x"], alg [] [] [] [.param "x"] ⟩ ]

/-- One shared program providing every receiver, user callee, callback, and
    conditional used by the parity cases below. -/
def dotCallParityProg : Algorithm :=
  algPrivate [] [] [
    ("Double", alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]),
    ("KeepPositive", alg ["x"] [] [] [.binary .gt (.param "x") (.num 0)]),
    ("Add", alg ["item", "acc"] [] [] [.binary .add (.param "item") (.param "acc")]),
    ("NItems", receiverSymmetryNItemsAlg),
    ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg),
    ("FixedPairCount", alg ["values", "t"] [] [] [.dotCall (.param "values") "count" none]),
    ("Pair", alg [] [] [] [.capture [.num 10, .num 20]]),
    ("Values", alg [] [] [] [.num 10, .num 20]),
    ("Value", alg [] [] [] [.num 42]),
    ("Receiver", alg [] [] [] [.num 1]),
    ("Bad", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
    ("Holder", alg [] [] [publicProp "Inner" (alg [] [] [] [.num 42])] [.num 1]),
    ("Choose", dotCallParityChooseAlg),
    ("G", dotCallParitySingletonSequenceValueAlg)
  ] [.num 0]

-- Inline `(…)` receivers expose their top-level output items.
def dotCallParityData123 : KatLang.Expr := .capture [.num 1, .num 2, .num 3]
def dotCallParityData312 : KatLang.Expr := .capture [.num 3, .num 1, .num 2]
def dotCallParityDataMixedSigns : KatLang.Expr :=
  .capture [.num (-1), .num 2, .num (-3)]

def dotCallArgs (items : List KatLang.Expr) : Option (List KatLang.Expr) :=
  some items

structure DotCallParityCase where
  label : String
  target : KatLang.Expr
  name : String
  argsOpt : Option (List KatLang.Expr) := none
  expected : BuiltinApplyOutcome := .succeeded
  expectedAtoms : Option (List Int) := none
  -- Elaborated dot-edge fact; the default mirrors the `Expr.dotCall` sugar
  -- (`.resolve name` fallback).
  fallback? : Option KatLang.Expr := none

/-- Lexical context mirroring `runResultM`: the program algorithm is wired
    onto the prelude and pushed, exactly as when its output expressions are
    evaluated, so dot-call targets resolve the program's properties and the
    builtin prelude. -/
def dotCallParityCtx (prog : Algorithm) : KatLang.EvalCtx :=
  let base : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  KatLang.EvalCtx.push (KatLang.wireToCaller base prog) base

/-- Run both dot-call twins from identical initial state and require:
    projection parity (value / error Repr / final state Repr), the expected
    outcome classification, and the expected atoms for success cases — the
    last two keep each case honest about what it exercises. Atoms are compared
    through the host-boundary view (`Result.hostAtoms`), which opens exact list
    values, so collection-builtin cases still assert their numeric contents. -/
def dotCallParityCaseHolds (c : DotCallParityCase) : Bool :=
  let ctx := dotCallParityCtx dotCallParityProg
  let fallback := c.fallback?.getD (.resolve c.name)
  let plain := (KatLang.evalDotCall c.target c.name fallback c.argsOpt ctx []).run KatLang.EvalState.empty
  let counted := (KatLang.evalDotCallCounted c.target c.name fallback c.argsOpt ctx []).run KatLang.EvalState.empty
  let parity :=
    match plain, counted with
    | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
        value == countedValue && reprStr plainState == reprStr countedState
    | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
    | _, _ => false
  let outcome := classifyBuiltinApply (plain.map (fun _ => ()))
  let atomsMatch :=
    match c.expectedAtoms, plain with
    | some expected, .ok (value, _) => Result.hostAtoms value == expected
    | some _, .error _ => false
    | none, _ => true
  parity && outcome == c.expected && atomsMatch

def dotCallParityCases : List DotCallParityCase :=
  [ -- A: ordinary lexical user-defined dot-call, receiver injected as one
    -- leading argument: 5.Double == Double(5).
    { label := "A/lexical-user-callee", target := .num 5, name := "Double",
      expectedAtoms := some [10] },
    -- B: sequence-valued property receiver is ONE argument slot, never implicitly
    -- spread: Pair.NItems == NItems(Pair) collects `values = [Pair]`, count 1.
    { label := "B/sequenceValue-receiver-one-slot", target := resolve "Pair", name := "NItems",
      expectedAtoms := some [1] },
    -- C: explicit spread of a multi-output property spreads its emitted top-level
    -- values into the single-collecting `NItems(*values)` item supply: (Values*).NItems
    -- binds the two values, count 2.
    { label := "C/spread-multi-output-receiver",
      target := sequenceSpreadReceiver (resolve "Values"), name := "NItems",
      expectedAtoms := some [2] },
    -- D: explicit spread of a sequence-valued property opens it into the item
    -- supply the same way: (Pair*).NItems binds the two elements, count 2.
    { label := "D/spread-sequenceValue-receiver-stays-sequenceValue",
      target := sequenceSpreadReceiver (resolve "Pair"), name := "NItems",
      expectedAtoms := some [2] },
    -- E: leading variadic with suffix: Pair.BeforeLastCount(99) collects the
    -- sequence-value receiver as one collected element, count 1.
    { label := "E/leading-variadic-with-suffix", target := resolve "Pair",
      name := "BeforeLastCount", argsOpt := dotCallArgs [.num 99],
      expectedAtoms := some [1] },
    -- F/G: a receiver is ONE segment for arity checking regardless of its
    -- supply (the segment supply is consumed only by an allocated collector),
    -- so a fixed-arity callee receives the grouped-spread receiver as ONE
    -- slot and under-binds — for the multi-output and the sequence-valued
    -- property alike.
    { label := "F/spread-fixed-arity-multi-output",
      target := sequenceSpreadReceiver (resolve "Values"), name := "FixedPairCount",
      expected := .arityRejected },
    { label := "G/spread-fixed-arity-sequenceValue",
      target := sequenceSpreadReceiver (resolve "Pair"), name := "FixedPairCount",
      expected := .arityRejected },
    -- H: sequence builtin dot-calls.
    { label := "H/builtin-sum", target := dotCallParityData123, name := "sum",
      expectedAtoms := some [6] },
    { label := "H/builtin-count", target := dotCallParityData123, name := "count",
      expectedAtoms := some [3] },
    { label := "H/builtin-order", target := dotCallParityData312, name := "order",
      expectedAtoms := some [1, 2, 3] },
    -- I: sequence builtin dot-calls with suffix arguments.
    { label := "I/builtin-take-suffix", target := dotCallParityData123, name := "take",
      argsOpt := dotCallArgs [.num 2], expectedAtoms := some [1, 2] },
    { label := "I/builtin-skip-suffix", target := dotCallParityData123, name := "skip",
      argsOpt := dotCallArgs [.num 1], expectedAtoms := some [2, 3] },
    { label := "I/builtin-contains-suffix", target := dotCallParityData123, name := "contains",
      argsOpt := dotCallArgs [.num 2], expectedAtoms := some [1] },
    -- J: sequence builtin dot-calls with user callbacks.
    { label := "J/builtin-map-callback", target := dotCallParityData123, name := "map",
      argsOpt := dotCallArgs [resolve "Double"], expectedAtoms := some [2, 4, 6] },
    { label := "J/builtin-filter-callback", target := dotCallParityDataMixedSigns,
      name := "filter", argsOpt := dotCallArgs [resolve "KeepPositive"],
      expectedAtoms := some [2] },
    { label := "J/builtin-reduce-callback", target := dotCallParityData123, name := "reduce",
      argsOpt := dotCallArgs [resolve "Add", .num 0], expectedAtoms := some [6] },
    -- K: `Receiver.Value` falls back lexically and injects the receiver as
    -- one leading argument, so the zero-parameter property under-binds:
    -- arityMismatch 0 1 on both paths.
    { label := "K/lexical-zero-arg-prop-receiver-arity", target := resolve "Receiver",
      name := "Value", expected := .arityRejected },
    -- L: `1.Choose` injects one argument against two-argument clause
    -- patterns: noMatchingBranch "Choose" on both paths.
    { label := "L/conditional-receiver-underbinds", target := .num 1, name := "Choose",
      expected := .failedOtherwise },
    -- M: `1.G` SUCCEEDS: singleton sequence-value clause patterns match a non-sequence-value
    -- argument (`patternSequenceValueMembers?` adaptation), so G((x)) binds x = 1.
    { label := "M/singleton-sequence-value-conditional-matches", target := .num 1, name := "G",
      expectedAtoms := some [1] },
    -- N: unknown member: unknownName "DoesNotExist" on both paths.
    { label := "N/unknown-name", target := .num 1, name := "DoesNotExist",
      expected := .failedOtherwise },
    -- O: receiver evaluation failure (division by zero) propagates with the
    -- same diagnostic on both paths.
    { label := "O/receiver-evaluation-failure", target := resolve "Bad", name := "NItems",
      expected := .failedOtherwise },
    -- P: structural zero-arg property access through dot-call writes the
    -- per-run cache; both paths must leave the same cache state.
    { label := "P/structural-zero-arg-cache", target := resolve "Holder", name := "Inner",
      expectedAtoms := some [42] },
    -- Q: a stored `.param` fallback with NO algEnv binding fails with the
    -- canonical parameter-resolution error on both paths — the stored
    -- identity decides, never the runtime environment.
    { label := "Q/param-fallback-unbound", target := .num 5, name := "Missing",
      fallback? := some (.param "Missing"), expected := .failedOtherwise } ]

def dotCallParityCaseFailures : List String :=
  (dotCallParityCases.filter (fun c => !(dotCallParityCaseHolds c))).map
    (fun c => c.label)

#guard dotCallParityCaseFailures == []

-- The cache-sensitive cases must actually write the cache, so the final-state
-- comparison inside the parity helper is not vacuously `empty == empty`.
def dotCallParityCacheCasesWriteCache : Bool :=
  [ (resolve "Holder", "Inner") ].all
    fun (target, name) =>
      match (KatLang.evalDotCall target name (.resolve name) none
          (dotCallParityCtx dotCallParityProg) []).run
          KatLang.EvalState.empty with
      | .ok (_, state) => !state.zeroArgPropertyCache.isEmpty
      | .error _ => false

#guard dotCallParityCacheCasesWriteCache

--------------------------------------------------------------------------------
-- call-family projection parity guards
--------------------------------------------------------------------------------
-- The counted call family is canonical and the plain family is its value
-- projection: `evalUserCall`, `evalConditionalCall`, `evalResolvedCall`, and
-- `evalCallExpr` each return `Prod.fst <$>` of their counted twins. These
-- guards pin representative parity from identical initial state — equal
-- values, equal error Reprs, equal final evaluator state — so a future
-- re-duplication of any plain call family cannot drift silently. The shared
-- program/context comes from the dot-call parity section above; expected
-- outcomes/atoms keep each case honest about what it exercises.

structure CallProjectionParityCase where
  label : String
  callee : KatLang.Expr
  args : List KatLang.Expr := []
  expected : BuiltinApplyOutcome := .succeeded
  expectedAtoms : Option (List Int) := none

def callProjectionParityCaseHolds (c : CallProjectionParityCase) : Bool :=
  let ctx := dotCallParityCtx dotCallParityProg
  let plain := (KatLang.evalCallExpr c.callee c.args ctx []).run KatLang.EvalState.empty
  let counted := (KatLang.evalCallCountedExpr c.callee c.args ctx []).run KatLang.EvalState.empty
  let parity :=
    match plain, counted with
    | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
        value == countedValue && reprStr plainState == reprStr countedState
    | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
    | _, _ => false
  let outcome := classifyBuiltinApply (plain.map (fun _ => ()))
  let atomsMatch :=
    match c.expectedAtoms, plain with
    | some expected, .ok (value, _) => Result.hostAtoms value == expected
    | some _, .error _ => false
    | none, _ => true
  parity && outcome == c.expected && atomsMatch

def callProjectionParityCases : List CallProjectionParityCase :=
  [ { label := "flat-user-call", callee := resolve "Double", args := [.num 5],
      expectedAtoms := some [10] },
    { label := "collecting-user-call", callee := resolve "NItems",
      args := [.num 1, .num 2, .num 3], expectedAtoms := some [3] },
    { label := "conditional-first-clause", callee := resolve "Choose",
      args := [.num 0, .num 9], expectedAtoms := some [9] },
    { label := "conditional-fallback-clause", callee := resolve "Choose",
      args := [.num 2, .num 3], expectedAtoms := some [5] },
    { label := "conditional-no-branch", callee := resolve "Choose",
      args := [.num 1], expected := .failedOtherwise },
    { label := "builtin-sum-callee", callee := resolve "sum",
      args := [.capture [.num 1, .num 2, .num 3]], expectedAtoms := some [6] },
    { label := "builtin-arity-rejected", callee := resolve "count",
      args := [], expected := .arityRejected },
    { label := "user-call-arity-rejected", callee := resolve "Double",
      args := [.num 1, .num 2], expected := .arityRejected },
    { label := "unknown-callee", callee := resolve "Nope",
      args := [.num 1], expected := .failedOtherwise },
    -- Reading the cacheable `Value` property while evaluating the argument
    -- writes the per-run cache, so the final-state parity comparison is not
    -- vacuous for the call family.
    { label := "cached-property-argument", callee := resolve "Double",
      args := [resolve "Value"], expectedAtoms := some [84] },
    { label := "argument-failure", callee := resolve "Double",
      args := [resolve "Bad"], expected := .failedOtherwise } ]

def callProjectionParityCaseFailures : List String :=
  (callProjectionParityCases.filter (fun c => !(callProjectionParityCaseHolds c))).map
    (fun c => c.label)

#guard callProjectionParityCaseFailures == []

/-- Direct (non-expression-position) parity for `evalUserCall`,
    `evalConditionalCall`, and `evalResolvedCall` against their counted twins,
    including the missing-output error edge that never reaches
    `evalCallExpr` through resolution. -/
def directCallProjectionParityHolds : Bool :=
  let ctx := dotCallParityCtx dotCallParityProg
  let doubleAlg := alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]
  let userParity :=
    let plain := (KatLang.evalUserCall doubleAlg [KatLang.Expr.num 21] ctx []).run KatLang.EvalState.empty
    let counted := (KatLang.evalUserCallCounted doubleAlg [KatLang.Expr.num 21] ctx []).run KatLang.EvalState.empty
    match plain, counted with
    | .ok (value, s1), .ok ((countedValue, _), s2) =>
        value == countedValue && value == Result.atom 42 && reprStr s1 == reprStr s2
    | _, _ => false
  let userMissingOutputParity :=
    let noOutput := alg [] [] [] []
    let plain := (KatLang.evalUserCall noOutput [] ctx []).run KatLang.EvalState.empty
    let counted := (KatLang.evalUserCallCounted noOutput [] ctx []).run KatLang.EvalState.empty
    match plain, counted with
    | .error e1, .error e2 => reprStr e1 == reprStr e2
    | _, _ => false
  let conditionalParity :=
    let plain := (KatLang.evalConditionalCall dotCallParityChooseAlg
      [KatLang.Expr.num 0, KatLang.Expr.num 7] ctx [] "Choose").run KatLang.EvalState.empty
    let counted := (KatLang.evalConditionalCallCounted dotCallParityChooseAlg
      [KatLang.Expr.num 0, KatLang.Expr.num 7] ctx [] "Choose").run KatLang.EvalState.empty
    match plain, counted with
    | .ok (value, s1), .ok ((countedValue, _), s2) =>
        value == countedValue && value == Result.atom 7 && reprStr s1 == reprStr s2
    | _, _ => false
  let resolvedBuiltinParity :=
    let plain := (KatLang.evalResolvedCall (.builtin .sumBuiltin)
      [KatLang.Expr.capture [.num 1, .num 2, .num 3]] ctx []).run KatLang.EvalState.empty
    let counted := (KatLang.evalResolvedCallCounted (.builtin .sumBuiltin)
      [KatLang.Expr.capture [.num 1, .num 2, .num 3]] ctx []).run KatLang.EvalState.empty
    match plain, counted with
    | .ok (value, s1), .ok ((countedValue, _), s2) =>
        value == countedValue && value == Result.atom 6 && reprStr s1 == reprStr s2
    | _, _ => false
  userParity && userMissingOutputParity && conditionalParity && resolvedBuiltinParity

#guard directCallProjectionParityHolds

--------------------------------------------------------------------------------
-- total eval projection parity guards
--------------------------------------------------------------------------------
-- `evalCounted` is the canonical expression dispatch: it matches EVERY `Expr`
-- variant explicitly (leaves included — num, stringLiteral, unary, binary now
-- live in counted arms/`evalUnaryCounted`/`evalBinaryCounted`), and plain
-- `eval` is its TOTAL value projection with no arms of its own. These probes
-- pin `eval e == Prod.fst <$> evalCounted e` — values, error Reprs, and final
-- evaluator state — across one representative expression per variant plus the
-- operator edges whose semantics moved into the counted arms (empty
-- transparency, string rejection, division by zero, negative power). The
-- expected-success flag keeps each probe honest.

def evalProjectionProbes : List (String × KatLang.Expr × Bool) :=
  [ ("num", .num 42, true),
    ("string", .stringLiteral "text", true),
    ("unary-minus", .unary .minus (.num 7), true),
    ("unary-not-zero", .unary .not (.num 0), true),
    ("unary-empty-propagates", .unary .minus (.emptySequence 0), true),
    ("unary-string-rejected", .unary .minus (.stringLiteral "s"), false),
    ("binary-add", .binary .add (.num 2) (.num 3), true),
    ("binary-eq-mixed-kinds", .binary .eq (.num 1) (.stringLiteral "1"), true),
    ("binary-ne-strings", .binary .ne (.stringLiteral "a") (.stringLiteral "b"), true),
    ("binary-empty-left-transparent", .binary .add (.emptySequence 0) (.num 5), true),
    ("binary-both-empty", .binary .add (.emptySequence 0) (.emptySequence 0), true),
    ("binary-string-op-rejected", .binary .add (.stringLiteral "a") (.stringLiteral "b"), false),
    ("binary-mixed-string-rejected", .binary .lt (.num 1) (.stringLiteral "b"), false),
    ("binary-div-by-zero", .binary .div (.num 1) (.num 0), false),
    ("binary-negative-pow-exact", .binary .pow (.num (-1)) (.num (-2)), true),
    -- The Int-valued Lean core rejects fractional reciprocals explicitly
    -- (`negativeIntPow`); parity covers the error Repr on both sides.
    ("binary-negative-pow-fractional", .binary .pow (.num 2) (.num (-2)), false),
    ("index-selects", .index (.capture [.num 1, .num 2, .num 3]) (.num 1), true),
    ("index-out-of-range", .index (.capture [.num 1]) (.num 5), false),
    ("index-negative", .index (.capture [.num 1]) (.unary .minus (.num 1)), false),
    ("param-unknown", .param "nope", false),
    ("resolve-cached-property", resolve "Value", true),
    ("resolve-unknown", resolve "NoSuchName", false),
    ("empty-sequence", .emptySequence 0, true),
    ("capture", .capture [.num 1, .num 2], true),
    ("list-literal", .listLiteral [.num 1, .capture [.num 2, .num 3]], true),
    ("sequence-spread", .sequenceSpread (resolve "Pair"), true),
    ("algorithm-expr", .algorithmExpr (alg [] [] [] [.num 9]), true),
    ("dot-call", KatLang.Expr.dotCall (resolve "Pair") "count" none, true),
    ("call", .call (resolve "Double") [.num 4], true) ]

def evalProjectionParityAt (e : KatLang.Expr) (expectOk : Bool) : Bool :=
  let ctx := dotCallParityCtx dotCallParityProg
  let plain := (KatLang.eval e ctx []).run KatLang.EvalState.empty
  let counted := (KatLang.evalCounted e ctx []).run KatLang.EvalState.empty
  let parity :=
    match plain, counted with
    | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
        value == countedValue && reprStr plainState == reprStr countedState
    | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
    | _, _ => false
  parity && plain.isOk == expectOk

def evalProjectionParityFailures : List String :=
  (evalProjectionProbes.filter (fun (_, e, expectOk) => !evalProjectionParityAt e expectOk)).map
    (fun (label, _, _) => label)

#guard evalProjectionParityFailures == []

--------------------------------------------------------------------------------
-- lookup projection parity guards
--------------------------------------------------------------------------------
-- `lookupLexicalProperty` is the canonical ownership-first lookup chain
-- (local → ancestor-structural → opens with public-only filtering, dedup, and
-- ambiguity); `lookupLexical` is its algorithm projection. These scenarios
-- pin that the projection selects the same declaration and reports the same
-- errors, so the algorithm-position path can never regrow an independent
-- chain.

def lookupProjectionLibs : List (String × Algorithm) :=
  [ ("LibA", alg [] [] [publicProp "Shared" (alg [] [] [] [.num 101]),
                        publicProp "OnlyA" (alg [] [] [] [.num 111]),
                        privateProp "Hidden" (alg [] [] [] [.num 121])] [.num 0]),
    ("LibB", alg [] [] [publicProp "Shared" (alg [] [] [] [.num 202])] [.num 0]),
    ("Own", alg [] [] [] [.num 7]) ]

def lookupProjectionProg : Algorithm :=
  algPrivate [] [] lookupProjectionLibs [.num 0]

/-- Child of the program scope that opens both libraries and shadows one name. -/
def lookupProjectionOpener : Algorithm :=
  alg [] [resolve "LibA", resolve "LibB"]
    [publicProp "Shadowed" (alg [] [] [] [.num 333])] [.num 0]

def lookupProjectionScenarioHolds (name : String) (expectOk : Bool) : Bool :=
  let ctx := dotCallParityCtx lookupProjectionProg
  let opener := KatLang.wireToCaller ctx lookupProjectionOpener
  let algSide := (KatLang.lookupLexical opener name ctx).run KatLang.EvalState.empty
  let propSide := (KatLang.lookupLexicalProperty opener name ctx).run KatLang.EvalState.empty
  match algSide, propSide with
  | .ok (resolvedAlg, s1), .ok (resolvedProp, s2) =>
      expectOk && reprStr resolvedAlg == reprStr resolvedProp.alg && reprStr s1 == reprStr s2
  | .error e1, .error e2 => !expectOk && reprStr e1 == reprStr e2
  | _, _ => false

def lookupProjectionScenarios : List (String × String × Bool) :=
  [ ("local-property", "Shadowed", true),
    ("ancestor-structural", "Own", true),
    ("open-provided", "OnlyA", true),
    ("open-ambiguous", "Shared", false),
    ("private-through-open", "Hidden", false),
    ("unknown-name", "Missing", false) ]

def lookupProjectionScenarioFailures : List String :=
  (lookupProjectionScenarios.filter (fun (_, name, expectOk) =>
    !(lookupProjectionScenarioHolds name expectOk))).map
    (fun (label, _, _) => label)

#guard lookupProjectionScenarioFailures == []

end KatLangTests
