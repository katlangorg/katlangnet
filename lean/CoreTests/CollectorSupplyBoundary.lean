import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- THE COLLECTOR SUPPLY-BOUNDARY LAW (September 2026)
--------------------------------------------------------------------------------
-- A collecting parameter consumes its allocated argument supply. Multiple
-- supplied items are collected exactly. If its entire segment is one lone
-- non-spread sequence value, that sequence may provide the collector's whole
-- supply, opening exactly one level. Lists remain exact. Items already
-- produced by explicit spread are final supplied items.
--
-- The rule reads only SLOT PROVENANCE (`SupplyOrigin`: a written non-spread
-- slot versus an item an explicit spread produced), never result provenance:
-- how a value was computed (a literal, a property, a call, a selection, a
-- conditional, a block) changes nothing. Fixed prefix/suffix positions are
-- allocated BEFORE the law reads the collector's segment. Dot-call is
-- ordinary receiver injection (`R.F(args)` is `F(R, args)`), so the fluent
-- spellings follow from the same law.
--
-- Lean: `collectorSupply` applied by `bindParameterPatternList` /
-- `bindCountedParameterPatternList`, origins recorded by
-- `collectVariadicCallItems`; laws in `KatLangArityLaws.lean` (section
-- "Collector supply-boundary laws"). C#: `CollectorSupply` in the same two
-- binders, fed by `BuildCallArgumentInputs`; `CollectorSupplyBoundaryTests`.

-- Coll(*xs) = xs
def collAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]

-- F(*xs, z) = xs, z
def collSuffixAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }, { name := "z" }] [] []
    [.param "xs", .param "z"]

-- G(x, *rest) = x, rest
def collPrefixAlg : Algorithm :=
  algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }] [] []
    [.param "x", .param "rest"]

-- H(x, *middle, z) = x, middle, z
def collMiddleAlg : Algorithm :=
  algWithParameters
    [{ name := "x" }, { name := "middle", kind := .collecting }, { name := "z" }] [] []
    [.param "x", .param "middle", .param "z"]

-- Id(x) = x ; Add(x, y) = x + y
def collIdAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def collAddAlg : Algorithm := alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def collProps : List (Prod String Algorithm) :=
  [ ("Coll", collAlg), ("F", collSuffixAlg), ("G", collPrefixAlg), ("H", collMiddleAlg),
    ("Id", collIdAlg), ("Add", collAddAlg),
    ("A", alg [] [] [] [.num 1, .num 2]),                       -- A = 1, 2
    ("Make", alg [] [] [] [.capture [.num 1, .num 2]]),         -- Make = (1, 2)
    ("B", alg [] [] [] [.capture [.capture [.num 1, .num 2], .num 3]]),  -- B = ((1, 2), 3)
    ("C", alg [] [] [] [.capture [.num 3, .capture [.num 1, .num 2]]]),  -- C = (3, (1, 2))
    ("E", alg [] [] [] [.emptySequence 0]),                     -- E = ()
    ("L", alg [] [] [] [.listLiteral [.num 1, .num 2]]) ]       -- L = [1, 2]

def runColl (out : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] collProps [out]))

def collIs (expected : Result) (out : KatLang.Expr) : Bool :=
  match runColl out with
  | Except.ok value => value == expected
  | _ => false

def collFails (classify : Error -> Bool) (out : KatLang.Expr) : Bool :=
  match runColl out with
  | Except.error err => classify err
  | _ => false

def pair12 : KatLang.Expr := .capture [.num 1, .num 2]
def seq12 : Result := .sequenceValue [.atom 1, .atom 2]
def list12 : Result := .listValue [.atom 1, .atom 2]

-- The required table, as direct calls `Coll(args)` and as the dotted spelling
-- `receiver.Coll(rest)` (dot-call passes a value: `R.Coll(rest)` IS
-- `Coll(R, rest)`), each row pinned in both spellings.
def requiredTable : List (List KatLang.Expr × Result) :=
  [ ([], .listValue []),
    ([.num 1], .listValue [.atom 1]),
    ([.num 1, .num 2], list12),
    ([.emptySequence 0], .listValue []),
    ([pair12], list12),
    ([.capture [.emptySequence 0, .num 3]], .listValue [.sequenceValue [], .atom 3]),
    ([.capture [pair12, .num 3]], .listValue [seq12, .atom 3]),
    ([.emptySequence 0, .num 3], .listValue [.sequenceValue [], .atom 3]),
    ([pair12, .num 3], .listValue [seq12, .atom 3]),
    ([.listLiteral []], .listValue [.listValue []]),
    ([.listLiteral [.num 1, .num 2]], .listValue [list12]),
    ([sequenceSpread pair12], list12),
    ([sequenceSpread (.listLiteral [pair12])], .listValue [seq12]),
    ([sequenceSpread (.listLiteral [.emptySequence 0])], .listValue [.sequenceValue []]),
    ([sequenceSpread (.listLiteral [])], .listValue []),
    ([sequenceSpread pair12, .num 3], .listValue [.atom 1, .atom 2, .atom 3]) ]

def requiredTableHoldsForDirectCalls : Bool :=
  requiredTable.all fun (args, expected) =>
    collIs expected (.call (resolve "Coll") args)

#guard requiredTableHoldsForDirectCalls

def requiredTableHoldsForDottedCalls : Bool :=
  requiredTable.all fun (args, expected) =>
    match args with
    | [] => true  -- no receiver to write
    | receiver :: rest =>
        collIs expected (.dotCall receiver "Coll" (if rest.isEmpty then none else some rest))

#guard requiredTableHoldsForDottedCalls

-- Origin independence: every expression below evaluates to the sequence value
-- `(1, 2)`; as the lone written slot of a collector each opens one level
-- (`[1, 2]`), and beside another slot each is collected exactly
-- (`[(1, 2), 3]`). Only the value and the slot's provenance count.
def pairOrigins : List KatLang.Expr :=
  [ pair12,
    .capture [pair12],
    resolve "A",
    resolve "Make",
    .call (resolve "if") [.boolLiteral true, pair12, .num 0],
    .index (resolve "B") (.num 0),
    .call (resolve "first") [resolve "B"],
    .call (resolve "last") [resolve "C"],
    .index (.call (resolve "map") [resolve "B", resolve "Id"]) (.num 0),
    .capture [sequenceSpread (resolve "A")],
    .algorithmExpr (alg [] [] [] [.num 1, .num 2]) ]

def loneWrittenSequenceOpensOneLevelWhateverItsOrigin : Bool :=
  pairOrigins.all fun receiver =>
    collIs list12 (.call (resolve "Coll") [receiver]) &&
    collIs list12 (.dotCall receiver "Coll" none) &&
    collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [receiver, .num 3]) &&
    collIs (.listValue [seq12, .atom 3]) (.dotCall receiver "Coll" (some [.num 3]))

#guard loneWrittenSequenceOpensOneLevelWhateverItsOrigin

-- `()` is the same rule, never a special case: a lone written `()` opens to
-- zero collected items, beside another slot it is one visible item, a spread
-- `()` contributes nothing, and a selected `()` behaves like the literal.
def emptySequenceIsTheSameRule : Bool :=
  collIs (.listValue []) (.call (resolve "Coll") [.emptySequence 0]) &&
  collIs (.listValue []) (.call (resolve "Coll") [resolve "E"]) &&
  collIs (.listValue []) (.dotCall (resolve "E") "Coll" none) &&
  collIs (.listValue [.sequenceValue [], .atom 3]) (.call (resolve "Coll") [resolve "E", .num 3]) &&
  collIs (.listValue [.sequenceValue [], .atom 3]) (.dotCall (resolve "E") "Coll" (some [.num 3])) &&
  collIs (.listValue []) (.call (resolve "Coll") [sequenceSpread (resolve "E")]) &&
  collIs (.listValue [.atom 3]) (.call (resolve "Coll") [sequenceSpread (resolve "E"), .num 3]) &&
  collIs (.listValue []) (.call (resolve "Coll") [.index (.capture [.emptySequence 0, .num 1]) (.num 0)])

#guard emptySequenceIsTheSameRule

-- Lists stay exact until explicitly spread, at every position.
def listsStayExactUntilExplicitlySpread : Bool :=
  collIs (.listValue [list12]) (.call (resolve "Coll") [resolve "L"]) &&
  collIs (.listValue [list12]) (.dotCall (resolve "L") "Coll" none) &&
  collIs list12 (.call (resolve "Coll") [sequenceSpread (resolve "L")]) &&
  collIs (.listValue [list12, .atom 3]) (.call (resolve "Coll") [resolve "L", .num 3]) &&
  collIs (.sequenceValue [.listValue [list12], .atom 3]) (.call (resolve "F") [resolve "L", .num 3]) &&
  collIs (.sequenceValue [.atom 1, .listValue [list12]]) (.call (resolve "G") [.num 1, resolve "L"]) &&
  collIs (.listValue [.listValue [list12]]) (.call (resolve "Coll") [.listLiteral [resolve "L"]]) &&
  collIs (.listValue [list12]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [resolve "L"])])

#guard listsStayExactUntilExplicitlySpread

-- Written slot versus explicit-spread item holding the SAME value: the value
-- `(1, 2)` opens when written, and is final (collected exactly) when an
-- explicit spread produced it; a captured spread `([(1, 2)]*)` is a written
-- slot again, so `Coll(([(1, 2)]*))` opens like `Coll((1, 2))`; and a
-- stacked spread `[(1, 2)]**` re-spreads the captured pair into two items.
def writtenSlotAndFinalItemAreDistinguished : Bool :=
  collIs list12 (.call (resolve "Coll") [pair12]) &&
  collIs (.listValue [seq12]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [pair12])]) &&
  collIs (.listValue [.sequenceValue []]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [.emptySequence 0])]) &&
  collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [pair12]), .num 3]) &&
  collIs list12 (.call (resolve "Coll") [.capture [sequenceSpread (.listLiteral [pair12])]]) &&
  collIs list12 (.dotCall (.capture [sequenceSpread (.listLiteral [pair12])]) "Coll" none) &&
  collIs list12 (.call (resolve "Coll") [sequenceSpread (.capture [sequenceSpread (.listLiteral [pair12])])])

#guard writtenSlotAndFinalItemAreDistinguished

-- Redundant grouping creates no distinction (`((1, 2))` normalizes to
-- `(1, 2)`), and opening is ONE level: a nested pair inside the lone
-- sequence stays one collected item, and a spread of the nested value
-- likewise supplies the pair as one final item.
def redundantGroupingCreatesNoDistinctionAndOpeningIsOneLevel : Bool :=
  collIs list12 (.call (resolve "Coll") [.capture [pair12]]) &&
  collIs list12 (.call (resolve "Coll") [.capture [.capture [pair12]]]) &&
  collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [.capture [pair12, .num 3]]) &&
  collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [sequenceSpread (.capture [pair12, .num 3])]) &&
  collIs (.listValue [.atom 1, seq12]) (.call (resolve "Coll") [.capture [.num 1, pair12]]) &&
  collIs (.listValue [.sequenceValue [seq12, .atom 3], .atom 4])
    (.call (resolve "Coll") [.capture [pair12, .num 3], .num 4])

#guard redundantGroupingCreatesNoDistinctionAndOpeningIsOneLevel

-- Fixed parameters bind their values unchanged: the law never reaches a fixed
-- position, so `Id((1, 2))` is the pair, `Add((1, 2))` is the ordinary arity
-- rejection (one item against two fixed parameters; the flat binder reports
-- the remaining `y` unbound, `arityMismatch 1 0`, as in every other fixed
-- under-supply guard), and `Add((1, 2)*)` is 3.
def fixedParametersBindTheirValuesUnchanged : Bool :=
  collIs seq12 (.call (resolve "Id") [pair12]) &&
  collIs seq12 (.dotCall pair12 "Id" none) &&
  collIs (.listValue [.atom 1]) (.call (resolve "Id") [.listLiteral [.num 1]]) &&
  collIs (.sequenceValue []) (.call (resolve "Id") [.emptySequence 0]) &&
  collFails (innermostIsArityMismatch 1 0) (.call (resolve "Add") [pair12]) &&
  collFails (innermostIsArityMismatch 1 0) (.dotCall pair12 "Add" none) &&
  collIs (.atom 3) (.call (resolve "Add") [sequenceSpread pair12]) &&
  collIs (.atom 3) (.dotCall (sequenceSpread pair12) "Add" none)

#guard fixedParametersBindTheirValuesUnchanged

-- Mixed signatures: fixed prefix/suffix allocation happens FIRST, and the law
-- then reads the segment left to the collector.
def mixedSignaturesApplyTheRuleAfterFixedAllocation : Bool :=
  -- F(*xs, z)
  collIs (.sequenceValue [list12, .atom 3]) (.call (resolve "F") [pair12, .num 3]) &&
  collIs (.sequenceValue [.listValue [seq12, .atom 3], .atom 4]) (.call (resolve "F") [pair12, .num 3, .num 4]) &&
  collIs (.sequenceValue [.listValue [seq12], .atom 3])
    (.call (resolve "F") [sequenceSpread (.listLiteral [pair12]), .num 3]) &&
  collIs (.sequenceValue [.listValue [], seq12]) (.call (resolve "F") [pair12]) &&
  collIs (.sequenceValue [.listValue [.atom 1], .atom 2]) (.call (resolve "F") [sequenceSpread pair12]) &&
  collIs (.sequenceValue [.listValue [], .atom 3]) (.call (resolve "F") [.emptySequence 0, .num 3]) &&
  collIs (.sequenceValue [.listValue [list12], .atom 3]) (.call (resolve "F") [.listLiteral [.num 1, .num 2], .num 3]) &&
  -- G(x, *rest)
  collIs (.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3]])
    (.call (resolve "G") [.num 1, .capture [.num 2, .num 3]]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3], .atom 4]])
    (.call (resolve "G") [.num 1, .capture [.num 2, .num 3], .num 4]) &&
  collIs (.sequenceValue [seq12, .listValue []]) (.call (resolve "G") [pair12]) &&
  collIs (.sequenceValue [.atom 1, .listValue []]) (.call (resolve "G") [.num 1, .emptySequence 0]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.listValue [.atom 2, .atom 3]]])
    (.call (resolve "G") [.num 1, .listLiteral [.num 2, .num 3]]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.call (resolve "G") [.num 1, sequenceSpread (.listLiteral [.capture [.num 2, .num 3]])]) &&
  -- H(x, *middle, z)
  collIs (.sequenceValue [.atom 0, list12, .atom 3]) (.call (resolve "H") [.num 0, pair12, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [seq12, .atom 3], .atom 4])
    (.call (resolve "H") [.num 0, pair12, .num 3, .num 4]) &&
  collIs (.sequenceValue [.atom 0, .listValue [], .atom 3]) (.call (resolve "H") [.num 0, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [], .atom 3]) (.call (resolve "H") [.num 0, .emptySequence 0, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [list12], .atom 3])
    (.call (resolve "H") [.num 0, .listLiteral [.num 1, .num 2], .num 3]) &&
  collIs (.sequenceValue [.atom 1, .listValue [], .atom 2]) (.call (resolve "H") [sequenceSpread pair12]) &&
  -- The dotted spellings are the same calls.
  collIs (.sequenceValue [list12, .atom 3]) (.dotCall pair12 "F" (some [.num 3])) &&
  collIs (.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3]])
    (.dotCall (.num 1) "G" (some [.capture [.num 2, .num 3]])) &&
  collIs (.sequenceValue [.atom 0, list12, .atom 3]) (.dotCall (.num 0) "H" (some [pair12, .num 3]))

#guard mixedSignaturesApplyTheRuleAfterFixedAllocation

-- Arity counts supplied items, never a sequence's element count: one written
-- sequence slot is ONE item however many elements it holds.
def arityCountsSuppliedItems : Bool :=
  collFails (innermostIsArityMismatch 1 0) (.call (resolve "F") []) &&
  collFails (innermostIsArityMismatch 1 0) (.call (resolve "G") []) &&
  collFails (innermostIsArityMismatch 2 0) (.call (resolve "H") []) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [pair12]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [.emptySequence 0]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [.listLiteral [.num 1, .num 2, .num 3, .num 4]]) &&
  collFails (innermostIsArityMismatch 2 1) (.dotCall pair12 "H" none)

#guard arityCountsSuppliedItems

-- Nested sequence-value parameter patterns open exactly one written level, and
-- the items a pattern opens are FINAL, so the nested collector never reopens
-- them: Pat((x, *y)) on `(1, (2, 3))` binds `y = [(2, 3)]`.
def nestedPatternsKeepOneLevelOpening : Bool :=
  let patAlg := algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y", kind := .collecting }]
  ] [] [] [.listLiteral [.param "x"], .param "y"]
  let pat2Alg := algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y", kind := .collecting }],
    .capture { name := "z" }
  ] [] [] [.listLiteral [.param "x"], .param "y", .listLiteral [.param "z"]]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("Pat", patAlg), ("Pat2", pat2Alg)] [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  is (.sequenceValue [.listValue [.atom 1], .listValue [.atom 2, .atom 3]])
    (.call (resolve "Pat") [.capture [.num 1, .num 2, .num 3]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.call (resolve "Pat") [.capture [.num 1, .capture [.num 2, .num 3]]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.listValue [.atom 2, .atom 3]]])
    (.call (resolve "Pat") [.capture [.num 1, .listLiteral [.num 2, .num 3]]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]], .listValue [.atom 9]])
    (.call (resolve "Pat2") [.capture [.num 1, .capture [.num 2, .num 3]], .num 9]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]], .listValue [.atom 9]])
    (.dotCall (.capture [.num 1, .capture [.num 2, .num 3]]) "Pat2" (some [.num 9]))

#guard nestedPatternsKeepOneLevelOpening

-- Callbacks use the same law through the ordinary callback binder: a whole
-- callback item is the collector's lone WRITTEN slot (so a sequence item
-- opens one level and a list item stays exact), while the flat-callback row
-- convention, which opens a lone sequence item into row slots for a
-- multi-parameter callee, produces FINAL row slots that are never reopened.
def callbacksUseTheSameLaw : Bool :=
  let restAlg := algWithParameters [{ name := "a" }, { name := "rest", kind := .collecting }] [] []
    [.param "rest"]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("Coll", collAlg), ("Rest", restAlg)] [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  is (.listValue [list12, .listValue [.atom 3, .atom 4]])
    (.call (resolve "map") [.capture [pair12, .capture [.num 3, .num 4]], resolve "Coll"]) &&
  is (.listValue [.listValue [], .listValue [.atom 3, .atom 4]])
    (.call (resolve "map") [.capture [.emptySequence 0, .capture [.num 3, .num 4]], resolve "Coll"]) &&
  is (.listValue [.listValue [list12], .listValue [.listValue [.atom 3]]])
    (.call (resolve "map") [.capture [.listLiteral [.num 1, .num 2], .listLiteral [.num 3]], resolve "Coll"]) &&
  is (.listValue [.listValue [.atom 7], .listValue [.atom 8]])
    (.call (resolve "map") [.capture [.num 7, .num 8], resolve "Coll"]) &&
  is (.listValue [.listValue [seq12, .atom 3]])
    (.call (resolve "map") [.listLiteral [.capture [pair12, .num 3]], resolve "Coll"]) &&
  is (.listValue [.listValue [.sequenceValue [.atom 2, .atom 3]], .listValue [.atom 5]])
    (.call (resolve "map") [.capture [.capture [.num 1, .capture [.num 2, .num 3]], .capture [.num 4, .num 5]], resolve "Rest"]) &&
  is (.listValue [.listValue [.atom 2, .atom 3]])
    (.call (resolve "map") [.listLiteral [.capture [.num 1, .num 2, .num 3]], resolve "Rest"]) &&
  -- The dotted spelling of the higher-order call is the same call.
  is (.listValue [list12, .listValue [.atom 3, .atom 4]])
    (.dotCall (.capture [pair12, .capture [.num 3, .num 4]]) "map" (some [resolve "Coll"]))

#guard callbacksUseTheSameLaw

-- A reducer with a collecting accumulator side binds the accumulator's own
-- one-level slots (`Result.toItems`), which are FINAL: a sequence-valued slot
-- stays one item and a list accumulator stays one opaque slot.
def reducerAccumulatorSlotsAreFinal : Bool :=
  let accAlg := algWithParameters [{ name := "x" }, { name := "acc", kind := .collecting }] [] []
    [.param "acc"]
  let run (initial : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("Acc", accAlg)] [
      .call (resolve "reduce") [.listLiteral [.num 9], resolve "Acc", initial]
    ]))
  (match run (.capture [pair12, .num 3]) with
   | Except.ok value => value == .listValue [seq12, .atom 3]
   | _ => false) &&
  (match run pair12 with
   | Except.ok value => value == list12
   | _ => false) &&
  (match run (.listLiteral [pair12]) with
   | Except.ok value => value == .listValue [.listValue [seq12]]
   | _ => false)

#guard reducerAccumulatorSlotsAreFinal

-- Loop state slots are FINAL items: a loop step is never called with written
-- arguments, so a collecting step collects its state slots exactly — a lone
-- sequence-valued state slot is NOT opened, in `repeat` as in the mixed step
-- shape whose suffix consumes the last slot.
def loopStateSlotsAreFinalItems : Bool :=
  let stepAlg := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.dotCall (.param "xs") "count" none]
  let mixedStepAlg := algWithParameters [{ name := "xs", kind := .collecting }, { name := "last" }] [] []
    [.dotCall (.param "xs") "count" none, .param "last"]
  (match runFlat (.algorithmExpr (algPrivate [] [] [("Step", stepAlg)] [
      .call (resolve "repeat") [resolve "Step", .num 1, pair12],
      .call (resolve "repeat") [resolve "Step", .num 1, .num 1, .num 2],
      .call (resolve "repeat") [resolve "Step", .num 1, .listLiteral [.num 1, .num 2]]
    ])) with
   | Except.ok [1, 2, 1] => true
   | _ => false) &&
  (match runFlat (.algorithmExpr (algPrivate [] [] [("Step", mixedStepAlg)] [
      .call (resolve "repeat") [resolve "Step", .num 1, pair12, .num 3],
      .call (resolve "repeat") [resolve "Step", .num 1, pair12, .num 3, .num 4]
    ])) with
   | Except.ok [1, 3, 2, 4] => true
   | _ => false)

#guard loopStateSlotsAreFinalItems

-- Assignment deconstruction keeps its own one-level opening rule: it opens one
-- lone sequence or list boundary of its shared right-hand side, and its
-- collecting target collects the matched (pattern-opened, hence final) items
-- exactly — a sequence-valued item is never reopened by the collector rule.
def deconstructionKeepsItsOwnRule : Bool :=
  let decon (targets : List KatLang.ParameterPattern) (observed : String) (rhs : List KatLang.Expr)
      : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("sharedRhs", alg [] [] [] rhs)]
      [.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue targets] [] [] [.param observed]))
        [resolve "sharedRhs"]]))
  let fix (name : String) : KatLang.ParameterPattern := .capture { name := name }
  let coll (name : String) : KatLang.ParameterPattern := .capture { name := name, kind := .collecting }
  (match decon [fix "x", coll "y", fix "z"] "y" [.num 1, .num 2, .num 3, .num 4] with
   | Except.ok value => value == .listValue [.atom 2, .atom 3]
   | _ => false) &&
  (match decon [fix "x", coll "y", fix "z"] "y" [.num 1, .capture [.num 2, .num 3], .num 4] with
   | Except.ok value => value == .listValue [.sequenceValue [.atom 2, .atom 3]]
   | _ => false) &&
  (match decon [fix "x", coll "y", fix "z"] "y" [.num 1, .listLiteral [.num 2, .num 3], .num 4] with
   | Except.ok value => value == .listValue [.listValue [.atom 2, .atom 3]]
   | _ => false) &&
  (match decon [fix "first", coll "rest"] "rest" [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok value => value == .listValue [.atom 2, .atom 3]
   | _ => false) &&
  (match decon [fix "first", coll "rest"] "rest" [.num 1] with
   | Except.ok value => value == .listValue []
   | _ => false) &&
  (match decon [coll "all"] "all" [.num 1, .capture [.num 2, .num 3]] with
   | Except.ok value => value == .listValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]
   | _ => false)

#guard deconstructionKeepsItsOwnRule

-- Collection builtins keep their fixed `collection` parameter: an unspread
-- sequence or list is ONE argument read through the post-binding view, and
-- a spread sequence against the fixed signature is the ordinary arity error.
def collectionBuiltinsKeepTheirFixedCollectionParameter : Bool :=
  let props : List (Prod String Algorithm) :=
    [ ("A", alg [] [] [] [.capture [.num 1, .num 2]]),
      ("L", alg [] [] [] [.listLiteral [.num 1, .num 2]]),
      ("N", alg [] [] [] [.capture [.capture [.num 1, .num 2], .num 3]]) ]
  (match runFlat (.algorithmExpr (algPrivate [] [] props [
      .call (resolve "count") [resolve "A"], .dotCall (resolve "A") "count" none,
      .call (resolve "count") [resolve "L"], .dotCall (resolve "L") "count" none,
      .call (resolve "sum") [resolve "A"], .dotCall (resolve "A") "sum" none,
      .call (resolve "count") [resolve "N"], .dotCall (resolve "N") "count" none,
      .call (resolve "count") [.emptySequence 0], .dotCall (.emptySequence 0) "count" none,
      .call (resolve "count") [.listLiteral []]
    ])) with
   | Except.ok [2, 2, 2, 2, 3, 3, 2, 2, 0, 0, 0] => true
   | _ => false) &&
  expectInnermostArityMismatch 1 2 (runFlat (.algorithmExpr (algPrivate [] [] props [
    .call (resolve "count") [sequenceSpread (resolve "A")]
  ])))

#guard collectionBuiltinsKeepTheirFixedCollectionParameter

-- The plain and counted evaluators agree on every row of the required table
-- (the counted binder is the canonical implementation, the plain one its
-- projection): value AND emitted count 1 for the collected list.
def requiredTableAgreesBetweenPlainAndCounted : Bool :=
  requiredTable.all fun (args, expected) =>
    match runCountedProgram (.algorithmExpr (algPrivate [] [] collProps [.call (resolve "Coll") args])) with
    | Except.ok (value, count) => value == expected && count == 1
    | _ => false

#guard requiredTableAgreesBetweenPlainAndCounted

-- A reducer's element-side collector is distinct from accumulator-side state:
-- allocating the fixed accumulator leaves one WRITTEN element slot.
def reducerElementSideCollectorUsesWrittenSlot : Bool :=
  let reducer := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] [] [.param "items"]
  let cases : List (KatLang.Expr × Result) :=
    [(pair12, list12), (.emptySequence 0, .listValue []),
     (.listLiteral [], .listValue [.listValue []]),
     (.listLiteral [.num 1, .num 2], .listValue [list12]),
     (.capture [pair12, .num 3], .listValue [seq12, .atom 3])]
  cases.all fun (item, expected) =>
    match runCountedProgram (.algorithmExpr (algPrivate [] [] [("R", reducer)] [
      .call (resolve "reduce") [.listLiteral [item], resolve "R", .num 99]
    ])) with
    | .ok (actual, count) => actual == expected && count == 1
    | _ => false

#guard reducerElementSideCollectorUsesWrittenSlot

-- Final-item provenance belongs to one call supply. A fixed parameter's
-- returned value and a cached property subsequently enter fresh written slots.
def collectorOriginEndsAtReturnedAndStoredValues : Bool :=
  let cases : List (KatLang.Expr × Result) :=
    [(pair12, list12), (.emptySequence 0, .listValue []),
     (.listLiteral [], .listValue [.listValue []]),
     (.listLiteral [.num 1, .num 2], .listValue [list12]),
     (.capture [pair12, .num 3], .listValue [seq12, .atom 3])]
  cases.all fun (item, expected) =>
    let returned := KatLang.Expr.call (resolve "Id") [sequenceSpread (.listLiteral [item])]
    let stored := alg [] [] [] [returned]
    match runCountedProgram (.algorithmExpr (algPrivate [] []
      (collProps ++ [("Stored", stored)]) [
        .call (resolve "Coll") [returned],
        .call (resolve "Coll") [resolve "Stored"],
        .call (resolve "Coll") [resolve "Stored"]
      ])) with
    | .ok (actual, count) => actual == .sequenceValue [expected, expected, expected] && count == 3
    | _ => false

#guard collectorOriginEndsAtReturnedAndStoredValues

end KatLangTests
