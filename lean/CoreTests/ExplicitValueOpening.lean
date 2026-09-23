import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- VALUES STAY VALUES: EXPLICIT VALUE OPENING (September 2026)
--------------------------------------------------------------------------------
-- A non-spread argument supplies exactly ONE item — its value, whatever that
-- value is (a scalar, a sequence, a list, `()`, `[]`). Only an explicit spread
-- `v*` turns one value into several supplied items (one level, a sequence and
-- a list alike), and only an explicit structural pattern (`F((x, y))`,
-- `x, *r = v`) opens a received value. Fixed parameters bind their allocated
-- item unchanged; a collecting parameter collects exactly its allocated items
-- as one list (THE EXACT COLLECTOR LAW); a callback receives each element as
-- ONE ordinary argument (THE CALLBACK LAW). No collector, callback, reducer,
-- dot-call, selection, alias, or forwarding mechanism opens a value on the
-- programmer's behalf.
--
-- Lean: `collectVariadicCallItems` (one item per non-spread slot),
-- `collectSegment` in `bindParameterPatternList` /
-- `bindCountedParameterPatternList`, `evalUserCallbackCallCounted`; laws in
-- `KatLangArityLaws.lean` ("Exact collector laws"). C#: `BuildCallArgumentInputs`,
-- `CollectSegment`, the ordinary counted callback binder;
-- `ExplicitValueOpeningTests`.

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

-- Id(x) = x ; Add(x, y) = x + y ; AddPair((x, y)) = x + y
def collIdAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def collAddAlg : Algorithm := alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]
def collAddPairAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] []
    [.binary .add (.param "x") (.param "y")]

-- Cnt(*xs) = xs.count ; CntValue(x) = x.count
def collCntAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.dotCall (.param "xs") "count" none]
def collCntValueAlg : Algorithm := alg ["x"] [] [] [.dotCall (.param "x") "count" none]

-- Parts((*xs)) = xs — the explicit structural opener
def collPartsAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] []
    [.param "xs"]

-- Target(*xs) = xs ; Forward(*xs) = Target(xs*)
def collForwardAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.call (resolve "Coll") [sequenceSpread (.param "xs")]]

def collProps : List (Prod String Algorithm) :=
  [ ("Coll", collAlg), ("F", collSuffixAlg), ("G", collPrefixAlg), ("H", collMiddleAlg),
    ("Id", collIdAlg), ("Add", collAddAlg), ("AddPair", collAddPairAlg),
    ("Cnt", collCntAlg), ("CntValue", collCntValueAlg), ("Forward", collForwardAlg),
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
-- `Coll(R, rest)`), each row pinned in both spellings. Every non-spread
-- argument is ONE collected item; only the spread rows open a value.
def requiredTable : List (List KatLang.Expr × Result) :=
  [ ([], .listValue []),
    ([.num 1], .listValue [.atom 1]),
    ([.num 1, .num 2], list12),
    ([.emptySequence 0], .listValue [.sequenceValue []]),
    ([pair12], .listValue [seq12]),
    ([.capture [.emptySequence 0, .num 3]], .listValue [.sequenceValue [.sequenceValue [], .atom 3]]),
    ([.capture [pair12, .num 3]], .listValue [.sequenceValue [seq12, .atom 3]]),
    ([.emptySequence 0, .num 3], .listValue [.sequenceValue [], .atom 3]),
    ([pair12, .num 3], .listValue [seq12, .atom 3]),
    ([.listLiteral []], .listValue [.listValue []]),
    ([.listLiteral [.num 1, .num 2]], .listValue [list12]),
    ([.listLiteral [.listLiteral [.num 1, .num 2], .num 3]], .listValue [.listValue [list12, .atom 3]]),
    ([sequenceSpread pair12], list12),
    ([sequenceSpread (.listLiteral [.num 1, .num 2])], list12),
    ([sequenceSpread (.emptySequence 0)], .listValue []),
    ([sequenceSpread (.listLiteral [])], .listValue []),
    ([sequenceSpread (.listLiteral [pair12])], .listValue [seq12]),
    ([sequenceSpread (.listLiteral [.emptySequence 0])], .listValue [.sequenceValue []]),
    ([sequenceSpread (.listLiteral [.listLiteral [.num 1, .num 2]])], .listValue [list12]),
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
-- `(1, 2)`; as a written argument each is ONE collected item (`[(1, 2)]`),
-- beside another argument each is one item of the two (`[(1, 2), 3]`), and
-- only its explicit spread supplies its items (`[1, 2]`). No expression
-- provenance influences whether a value opens.
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

def everyOriginOfAValueIsOneArgument : Bool :=
  pairOrigins.all fun receiver =>
    collIs (.listValue [seq12]) (.call (resolve "Coll") [receiver]) &&
    collIs (.listValue [seq12]) (.dotCall receiver "Coll" none) &&
    collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [receiver, .num 3]) &&
    collIs (.listValue [seq12, .atom 3]) (.dotCall receiver "Coll" (some [.num 3])) &&
    collIs list12 (.call (resolve "Coll") [sequenceSpread receiver]) &&
    collIs seq12 (.call (resolve "Id") [receiver])

#guard everyOriginOfAValueIsOneArgument

-- An empty value is still a value: a written `()` or `[]` is ONE collected
-- item, never the zero-item supply of `Coll()`; only its explicit spread
-- supplies nothing. A selected `()` behaves like the literal.
def emptyValuesAreOneArgument : Bool :=
  collIs (.listValue []) (.call (resolve "Coll") []) &&
  collIs (.listValue [.sequenceValue []]) (.call (resolve "Coll") [.emptySequence 0]) &&
  collIs (.listValue [.sequenceValue []]) (.call (resolve "Coll") [resolve "E"]) &&
  collIs (.listValue [.sequenceValue []]) (.dotCall (resolve "E") "Coll" none) &&
  collIs (.listValue [.listValue []]) (.call (resolve "Coll") [.listLiteral []]) &&
  collIs (.listValue [.sequenceValue [], .atom 3]) (.call (resolve "Coll") [resolve "E", .num 3]) &&
  collIs (.listValue [.sequenceValue [], .atom 3]) (.dotCall (resolve "E") "Coll" (some [.num 3])) &&
  collIs (.listValue []) (.call (resolve "Coll") [sequenceSpread (resolve "E")]) &&
  collIs (.listValue []) (.call (resolve "Coll") [sequenceSpread (.listLiteral [])]) &&
  collIs (.listValue [.atom 3]) (.call (resolve "Coll") [sequenceSpread (resolve "E"), .num 3]) &&
  collIs (.listValue [.sequenceValue []])
    (.call (resolve "Coll") [.index (.capture [.emptySequence 0, .num 1]) (.num 0)])

#guard emptyValuesAreOneArgument

-- Sequences and lists are treated ALIKE at every call position: each is one
-- argument until explicitly spread.
def sequencesAndListsAreBothOneArgument : Bool :=
  collIs (.listValue [list12]) (.call (resolve "Coll") [resolve "L"]) &&
  collIs (.listValue [seq12]) (.call (resolve "Coll") [resolve "Make"]) &&
  collIs (.listValue [list12]) (.dotCall (resolve "L") "Coll" none) &&
  collIs (.listValue [seq12]) (.dotCall (resolve "Make") "Coll" none) &&
  collIs list12 (.call (resolve "Coll") [sequenceSpread (resolve "L")]) &&
  collIs list12 (.call (resolve "Coll") [sequenceSpread (resolve "Make")]) &&
  collIs (.listValue [list12, .atom 3]) (.call (resolve "Coll") [resolve "L", .num 3]) &&
  collIs (.sequenceValue [.listValue [list12], .atom 3]) (.call (resolve "F") [resolve "L", .num 3]) &&
  collIs (.sequenceValue [.listValue [seq12], .atom 3]) (.call (resolve "F") [resolve "Make", .num 3]) &&
  collIs (.sequenceValue [.atom 1, .listValue [list12]]) (.call (resolve "G") [.num 1, resolve "L"]) &&
  collIs (.sequenceValue [.atom 1, .listValue [seq12]]) (.call (resolve "G") [.num 1, resolve "Make"]) &&
  collIs (.listValue [.listValue [list12]]) (.call (resolve "Coll") [.listLiteral [resolve "L"]]) &&
  collIs (.listValue [list12]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [resolve "L"])])

#guard sequencesAndListsAreBothOneArgument

-- Spread-produced items are established items and are never reopened, and
-- no slot provenance exists: a written `(1, 2)` and a spread-produced `(1, 2)`
-- bind identically. A captured spread `([(1, 2)]*)` is the value `(1, 2)`
-- (one argument); the stacked spread `(([(1, 2)]*))*` opens that value.
def spreadItemsAreNeverReopened : Bool :=
  collIs (.listValue [seq12]) (.call (resolve "Coll") [pair12]) &&
  collIs (.listValue [seq12]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [pair12])]) &&
  collIs (.listValue [.sequenceValue []]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [.emptySequence 0])]) &&
  collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [sequenceSpread (.listLiteral [pair12]), .num 3]) &&
  collIs (.listValue [seq12]) (.call (resolve "Coll") [.capture [sequenceSpread (.listLiteral [pair12])]]) &&
  collIs (.listValue [seq12]) (.dotCall (.capture [sequenceSpread (.listLiteral [pair12])]) "Coll" none) &&
  collIs list12 (.call (resolve "Coll") [sequenceSpread (.capture [sequenceSpread (.listLiteral [pair12])])])

#guard spreadItemsAreNeverReopened

-- Redundant grouping creates no distinction (`((1, 2))` normalizes to
-- `(1, 2)`), and explicit opening is ONE level: spreading `((1, 2), 3)`
-- supplies the pair as one item.
def groupingAndOneLevelOpening : Bool :=
  collIs (.listValue [seq12]) (.call (resolve "Coll") [.capture [pair12]]) &&
  collIs (.listValue [seq12]) (.call (resolve "Coll") [.capture [.capture [pair12]]]) &&
  collIs (.listValue [.sequenceValue [seq12, .atom 3]]) (.call (resolve "Coll") [.capture [pair12, .num 3]]) &&
  collIs (.listValue [seq12, .atom 3]) (.call (resolve "Coll") [sequenceSpread (.capture [pair12, .num 3])]) &&
  collIs (.listValue [.sequenceValue [.atom 1, seq12]]) (.call (resolve "Coll") [.capture [.num 1, pair12]]) &&
  collIs (.listValue [.sequenceValue [seq12, .atom 3], .atom 4])
    (.call (resolve "Coll") [.capture [pair12, .num 3], .num 4]) &&
  collIs (.listValue [list12, .atom 3])
    (.call (resolve "Coll") [sequenceSpread (.listLiteral [.listLiteral [.num 1, .num 2], .num 3])])

#guard groupingAndOneLevelOpening

-- Fixed parameters bind their values unchanged, so `Id((1, 2))` is the pair,
-- `Add((1, 2))` and `Add([1, 2])` are the ordinary arity rejection (one item
-- against two fixed parameters, `arityMismatch 2 1`), and `Add((1, 2)*)` /
-- `Add([1, 2]*)` are 3. The payload agrees with the callback binder and C#.
def fixedParametersBindTheirValuesUnchanged : Bool :=
  collIs seq12 (.call (resolve "Id") [pair12]) &&
  collIs seq12 (.dotCall pair12 "Id" none) &&
  collIs (.listValue [.atom 1]) (.call (resolve "Id") [.listLiteral [.num 1]]) &&
  collIs (.sequenceValue []) (.call (resolve "Id") [.emptySequence 0]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "Add") [pair12]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "Add") [.listLiteral [.num 1, .num 2]]) &&
  collFails (innermostIsArityMismatch 2 1) (.dotCall pair12 "Add" none) &&
  collIs (.atom 3) (.call (resolve "Add") [sequenceSpread pair12]) &&
  collIs (.atom 3) (.call (resolve "Add") [sequenceSpread (.listLiteral [.num 1, .num 2])]) &&
  collIs (.atom 3) (.dotCall (sequenceSpread pair12) "Add" none)

#guard fixedParametersBindTheirValuesUnchanged

-- Mixed signatures: fixed prefix/suffix allocation happens first and the
-- collector then collects its segment EXACTLY — a lone segment item is never
-- opened; explicit spread changes the supply before allocation.
def mixedSignaturesCollectTheirSegmentExactly : Bool :=
  -- F(*xs, z)
  collIs (.sequenceValue [.listValue [seq12], .atom 3]) (.call (resolve "F") [pair12, .num 3]) &&
  collIs (.sequenceValue [.listValue [seq12, .atom 3], .atom 4]) (.call (resolve "F") [pair12, .num 3, .num 4]) &&
  collIs (.sequenceValue [.listValue [seq12], .atom 3])
    (.call (resolve "F") [sequenceSpread (.listLiteral [pair12]), .num 3]) &&
  collIs (.sequenceValue [.listValue [], seq12]) (.call (resolve "F") [pair12]) &&
  collIs (.sequenceValue [.listValue [.atom 1], .atom 2]) (.call (resolve "F") [sequenceSpread pair12]) &&
  collIs (.sequenceValue [.listValue [.sequenceValue []], .atom 3]) (.call (resolve "F") [.emptySequence 0, .num 3]) &&
  collIs (.sequenceValue [.listValue [list12], .atom 3]) (.call (resolve "F") [.listLiteral [.num 1, .num 2], .num 3]) &&
  collIs (.sequenceValue [list12, .atom 3]) (.call (resolve "F") [sequenceSpread pair12, .num 3]) &&
  -- G(x, *rest)
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.call (resolve "G") [.num 1, .capture [.num 2, .num 3]]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3], .atom 4]])
    (.call (resolve "G") [.num 1, .capture [.num 2, .num 3], .num 4]) &&
  collIs (.sequenceValue [seq12, .listValue []]) (.call (resolve "G") [pair12]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue []]]) (.call (resolve "G") [.num 1, .emptySequence 0]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.listValue [.atom 2, .atom 3]]])
    (.call (resolve "G") [.num 1, .listLiteral [.num 2, .num 3]]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.call (resolve "G") [.num 1, sequenceSpread (.listLiteral [.capture [.num 2, .num 3]])]) &&
  collIs (.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3]])
    (.call (resolve "G") [.num 1, sequenceSpread (.capture [.num 2, .num 3])]) &&
  -- H(x, *middle, z)
  collIs (.sequenceValue [.atom 0, .listValue [seq12], .atom 3]) (.call (resolve "H") [.num 0, pair12, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [seq12, .atom 3], .atom 4])
    (.call (resolve "H") [.num 0, pair12, .num 3, .num 4]) &&
  collIs (.sequenceValue [.atom 0, .listValue [], .atom 3]) (.call (resolve "H") [.num 0, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [.sequenceValue []], .atom 3])
    (.call (resolve "H") [.num 0, .emptySequence 0, .num 3]) &&
  collIs (.sequenceValue [.atom 0, .listValue [list12], .atom 3])
    (.call (resolve "H") [.num 0, .listLiteral [.num 1, .num 2], .num 3]) &&
  collIs (.sequenceValue [.atom 0, list12, .atom 3])
    (.call (resolve "H") [.num 0, sequenceSpread (.listLiteral [.num 1, .num 2]), .num 3]) &&
  collIs (.sequenceValue [.atom 1, .listValue [], .atom 2]) (.call (resolve "H") [sequenceSpread pair12]) &&
  -- The dotted spellings are the same calls.
  collIs (.sequenceValue [.listValue [seq12], .atom 3]) (.dotCall pair12 "F" (some [.num 3])) &&
  collIs (.sequenceValue [.atom 1, .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.dotCall (.num 1) "G" (some [.capture [.num 2, .num 3]])) &&
  collIs (.sequenceValue [.atom 0, .listValue [seq12], .atom 3]) (.dotCall (.num 0) "H" (some [pair12, .num 3])) &&
  collIs (.sequenceValue [list12, .atom 3]) (.dotCall (sequenceSpread pair12) "F" (some [.num 3]))

#guard mixedSignaturesCollectTheirSegmentExactly

-- Arity counts supplied items, never a value's element count: one written
-- sequence or list argument is ONE item however many elements it holds.
def arityCountsSuppliedItems : Bool :=
  collFails (innermostIsArityMismatch 1 0) (.call (resolve "F") []) &&
  collFails (innermostIsArityMismatch 1 0) (.call (resolve "G") []) &&
  collFails (innermostIsArityMismatch 2 0) (.call (resolve "H") []) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [pair12]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [.emptySequence 0]) &&
  collFails (innermostIsArityMismatch 2 1) (.call (resolve "H") [.listLiteral [.num 1, .num 2, .num 3, .num 4]]) &&
  collFails (innermostIsArityMismatch 2 1) (.dotCall pair12 "H" none)

#guard arityCountsSuppliedItems

-- Collecting parameters count ARGUMENTS; a fixed parameter reads a collection
-- value's contents through the builtin: `Cnt((10, 7))` and `Cnt([10, 7])` are
-- 1, `Cnt((10, 7)*)` and `Cnt([10, 7]*)` are 2, and `CntValue((10, 7))` /
-- `CntValue([10, 7])` are 2.
def collectorsCountArgumentsAndFixedParametersReadContents : Bool :=
  let pair107 : KatLang.Expr := .capture [.num 10, .num 7]
  let list107 : KatLang.Expr := .listLiteral [.num 10, .num 7]
  collIs (.atom 0) (.call (resolve "Cnt") []) &&
  collIs (.atom 1) (.call (resolve "Cnt") [.num 7]) &&
  collIs (.atom 1) (.call (resolve "Cnt") [pair107]) &&
  collIs (.atom 1) (.call (resolve "Cnt") [list107]) &&
  collIs (.atom 2) (.call (resolve "Cnt") [sequenceSpread pair107]) &&
  collIs (.atom 2) (.call (resolve "Cnt") [sequenceSpread list107]) &&
  collIs (.atom 2) (.call (resolve "CntValue") [pair107]) &&
  collIs (.atom 2) (.call (resolve "CntValue") [list107]) &&
  collIs (.atom 2) (.dotCall pair107 "count" none) &&
  collIs (.atom 2) (.dotCall list107 "count" none)

#guard collectorsCountArgumentsAndFixedParametersReadContents

-- Nested sequence-value parameter patterns are the explicit structural
-- openers: they open exactly one level of a sequence or a list, and a nested
-- collector collects the opened items exactly: Pat((x, *y)) on `(1, (2, 3))`
-- binds `y = [(2, 3)]`.
def nestedPatternsOpenExplicitly : Bool :=
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
  is (.sequenceValue [.listValue [.atom 1], .listValue [.atom 2, .atom 3]])
    (.call (resolve "Pat") [.listLiteral [.num 1, .num 2, .num 3]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]]])
    (.call (resolve "Pat") [.capture [.num 1, .capture [.num 2, .num 3]]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.listValue [.atom 2, .atom 3]]])
    (.call (resolve "Pat") [.capture [.num 1, .listLiteral [.num 2, .num 3]]]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]], .listValue [.atom 9]])
    (.call (resolve "Pat2") [.capture [.num 1, .capture [.num 2, .num 3]], .num 9]) &&
  is (.sequenceValue [.listValue [.atom 1], .listValue [.sequenceValue [.atom 2, .atom 3]], .listValue [.atom 9]])
    (.dotCall (.capture [.num 1, .capture [.num 2, .num 3]]) "Pat2" (some [.num 9]))

#guard nestedPatternsOpenExplicitly

-- THE CALLBACK LAW: a callback element is ONE ordinary argument, bound exactly
-- as the direct call with that element: a single collector collects it as one
-- item, a two-parameter flat callee rejects it with the ordinary arity error,
-- and only an explicit pattern opens it — a sequence and a list alike.
def callbacksPassEachElementAsOneArgument : Bool :=
  let restAlg := algWithParameters [{ name := "a" }, { name := "rest", kind := .collecting }] [] []
    [.param "rest"]
  let props := collProps ++ [("Rest", restAlg)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  let fails (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.error err => innermostIsArityMismatch 2 1 err
    | _ => false
  is (.listValue [.listValue [seq12], .listValue [.sequenceValue [.atom 3, .atom 4]]])
    (.call (resolve "map") [.capture [pair12, .capture [.num 3, .num 4]], resolve "Coll"]) &&
  is (.listValue [.listValue [.sequenceValue []], .listValue [.sequenceValue [.atom 3, .atom 4]]])
    (.call (resolve "map") [.capture [.emptySequence 0, .capture [.num 3, .num 4]], resolve "Coll"]) &&
  is (.listValue [.listValue [list12], .listValue [.listValue [.atom 3]]])
    (.call (resolve "map") [.capture [.listLiteral [.num 1, .num 2], .listLiteral [.num 3]], resolve "Coll"]) &&
  is (.listValue [.listValue [.atom 7], .listValue [.atom 8]])
    (.call (resolve "map") [.capture [.num 7, .num 8], resolve "Coll"]) &&
  is (.listValue [.listValue [.sequenceValue [seq12, .atom 3]]])
    (.call (resolve "map") [.listLiteral [.capture [pair12, .num 3]], resolve "Coll"]) &&
  is (.listValue [.listValue [], .listValue []])
    (.call (resolve "map") [.capture [.capture [.num 1, .capture [.num 2, .num 3]], .capture [.num 4, .num 5]], resolve "Rest"]) &&
  is (.listValue [.atom 1, .atom 1])
    (.call (resolve "map") [.listLiteral [.capture [.num 10, .num 7], .listLiteral [.num 10, .num 7]], resolve "Cnt"]) &&
  fails (.call (resolve "map") [.listLiteral [pair12], resolve "Add"]) &&
  fails (.call (resolve "map") [.listLiteral [.listLiteral [.num 1, .num 2]], resolve "Add"]) &&
  is (.listValue [.atom 3]) (.call (resolve "map") [.listLiteral [pair12], resolve "AddPair"]) &&
  is (.listValue [.atom 3]) (.call (resolve "map") [.listLiteral [.listLiteral [.num 1, .num 2]], resolve "AddPair"]) &&
  -- The dotted spelling of the higher-order call is the same call.
  is (.listValue [.listValue [seq12], .listValue [.sequenceValue [.atom 3, .atom 4]]])
    (.dotCall (.capture [pair12, .capture [.num 3, .num 4]]) "map" (some [resolve "Coll"]))

#guard callbacksPassEachElementAsOneArgument

-- Callback binding IS the ordinary call: for each element `E`, `map([E], F)`
-- is `[F(E)]` for every callee shape (collecting, prefix + collector, fixed,
-- explicit pattern) and every element kind, and the two fail together. The one
-- independent difference is map's own single-value RESULT contract: a
-- transform returning `()` (here `Id(())`) is no single element, so the map
-- fails where the direct call returns `()`.
def callbackBindingMatchesTheDirectCall : Bool :=
  let rec rootError : Error → Error
    | .withContext _ inner => rootError inner
    | error => error
  let restAlg := algWithParameters [{ name := "a" }, { name := "rest", kind := .collecting }] [] []
    [.param "rest"]
  let props := collProps ++ [("Rest", restAlg), ("Parts", collPartsAlg)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let elements : List KatLang.Expr :=
    [ .num 1, .emptySequence 0, .listLiteral [], pair12, .listLiteral [.num 1, .num 2],
      .capture [pair12, .num 3], .listLiteral [.listLiteral [.num 1, .num 2], .num 3] ]
  let callees := ["Coll", "Rest", "Id", "Add", "AddPair", "Parts", "Cnt", "CntValue"]
  elements.all fun element => callees.all fun callee =>
    match run (.call (resolve "map") [.listLiteral [element], resolve callee]),
          run (.call (resolve callee) [element]) with
    | Except.ok (.listValue [mapped]), Except.ok direct => mapped == direct
    | Except.error error, Except.ok (.sequenceValue []) => innermostIsBadArity error
    | Except.error mapped, Except.error direct => reprStr (rootError mapped) == reprStr (rootError direct)
    | _, _ => false

#guard callbackBindingMatchesTheDirectCall

-- Filter predicates follow the same callback law: `IsPair(*xs) = xs.count == 2`
-- receives one argument per element and keeps nothing, while the fixed
-- `IsPairValue(x) = x.count == 2` reads each element's contents.
def filterPredicatesReceiveOneArgument : Bool :=
  let isPairAlg := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.compare .eq (.dotCall (.param "xs") "count" none) (.num 2)]
  let isPairValueAlg := alg ["x"] [] [] [.compare .eq (.dotCall (.param "x") "count" none) (.num 2)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("IsPair", isPairAlg), ("IsPairValue", isPairValueAlg)] [out]))
  (match run (.call (resolve "filter") [.listLiteral [pair12, .listLiteral [.num 1, .num 2], .num 5], resolve "IsPair"]) with
   | Except.ok value => value == .listValue []
   | _ => false) &&
  (match run (.call (resolve "filter") [.listLiteral [pair12, .listLiteral [.num 1, .num 2], .num 5], resolve "IsPairValue"]) with
   | Except.ok value => value == .listValue [seq12, list12]
   | _ => false)

#guard filterPredicatesReceiveOneArgument

-- A reducer is an ordinary two-argument callback: the accumulator is ONE value,
-- so an accumulator-side collector collects exactly that one value — a
-- sequence and a list alike — and only an explicit pattern opens it.
def reducerAccumulatorIsOneArgument : Bool :=
  let accAlg := algWithParameters [{ name := "x" }, { name := "acc", kind := .collecting }] [] []
    [.param "acc"]
  let pairAccAlg := algWithParameterPatterns
    [.capture { name := "x" }, .sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] []
    [.capture [.param "b", .binary .add (.param "a") (.param "x")]]
  let run (reducer : String) (collection initial : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("Acc", accAlg), ("PairAcc", pairAccAlg)] [
      .call (resolve "reduce") [collection, resolve reducer, initial]
    ]))
  (match run "Acc" (.listLiteral [.num 9]) (.capture [pair12, .num 3]) with
   | Except.ok value => value == .listValue [.sequenceValue [seq12, .atom 3]]
   | _ => false) &&
  (match run "Acc" (.listLiteral [.num 9]) pair12 with
   | Except.ok value => value == .listValue [seq12]
   | _ => false) &&
  (match run "Acc" (.listLiteral [.num 9]) (.listLiteral [pair12]) with
   | Except.ok value => value == .listValue [.listValue [seq12]]
   | _ => false) &&
  (match run "Acc" (.listLiteral [.num 9]) (.emptySequence 0) with
   | Except.ok value => value == .listValue [.sequenceValue []]
   | _ => false) &&
  (match run "Acc" (.listLiteral [.num 9]) (.listLiteral []) with
   | Except.ok value => value == .listValue [.listValue []]
   | _ => false) &&
  (match run "PairAcc" (.listLiteral [.num 10, .num 20]) (.capture [.num 1, .num 2]) with
   | Except.ok value => value == .sequenceValue [.atom 11, .atom 22]
   | _ => false) &&
  (match run "PairAcc" (.listLiteral [.num 10]) (.listLiteral [.num 1, .num 2]) with
   | Except.ok value => value == .sequenceValue [.atom 2, .atom 11]
   | _ => false)

#guard reducerAccumulatorIsOneArgument

-- Loop state slots are the loop's established supply: each state slot is one
-- item, so a collecting step collects its state slots exactly — a lone
-- sequence-valued state slot is one item, in `repeat` as in the mixed step
-- shape whose suffix consumes the last slot.
def loopStateSlotsAreEstablishedItems : Bool :=
  let stepAlg := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.dotCall (.param "xs") "count" none]
  let mixedStepAlg := algWithParameters [{ name := "xs", kind := .collecting }, { name := "last" }] [] []
    [.dotCall (.param "xs") "count" none, .param "last"]
  (match runFlat (.algorithmExpr (algPrivate [] [] [("Step", stepAlg)] [
      .call (resolve "repeat") [resolve "Step", .num 1, pair12],
      .call (resolve "repeat") [resolve "Step", .num 1, .num 1, .num 2],
      .call (resolve "repeat") [resolve "Step", .num 1, .listLiteral [.num 1, .num 2]],
      .call (resolve "repeat") [resolve "Step", .num 1, sequenceSpread pair12]
    ])) with
   | Except.ok [1, 2, 1, 2] => true
   | _ => false) &&
  (match runFlat (.algorithmExpr (algPrivate [] [] [("Step", mixedStepAlg)] [
      .call (resolve "repeat") [resolve "Step", .num 1, pair12, .num 3],
      .call (resolve "repeat") [resolve "Step", .num 1, pair12, .num 3, .num 4]
    ])) with
   | Except.ok [1, 3, 2, 4] => true
   | _ => false)

#guard loopStateSlotsAreEstablishedItems

-- Assignment deconstruction is explicit structural syntax: it opens one lone
-- sequence or list boundary of its shared right-hand side, and its collecting
-- target collects the matched (pattern-opened) items exactly.
def deconstructionOpensExplicitly : Bool :=
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

#guard deconstructionOpensExplicitly

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

-- A reducer's element-side collector receives the element as ONE argument:
-- `R(*items, acc)` collects `[E]` for every element `E`.
def reducerElementSideCollectorReceivesOneArgument : Bool :=
  let reducer := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] [] [.param "items"]
  let cases : List (KatLang.Expr × Result) :=
    [(pair12, .listValue [seq12]), (.emptySequence 0, .listValue [.sequenceValue []]),
     (.listLiteral [], .listValue [.listValue []]),
     (.listLiteral [.num 1, .num 2], .listValue [list12]),
     (.capture [pair12, .num 3], .listValue [.sequenceValue [seq12, .atom 3]])]
  cases.all fun (item, expected) =>
    match runCountedProgram (.algorithmExpr (algPrivate [] [] [("R", reducer)] [
      .call (resolve "reduce") [.listLiteral [item], resolve "R", .num 99]
    ])) with
    | .ok (actual, count) => actual == expected && count == 1
    | _ => false

#guard reducerElementSideCollectorReceivesOneArgument

-- A value that crossed a spread, a fixed parameter's return, or a stored
-- property enters the next call as ONE argument like any other value.
def valuesStayValuesThroughReturnsAndStorage : Bool :=
  let cases : List (KatLang.Expr × Result) :=
    [(pair12, seq12), (.emptySequence 0, .sequenceValue []),
     (.listLiteral [], .listValue []),
     (.listLiteral [.num 1, .num 2], list12),
     (.capture [pair12, .num 3], .sequenceValue [seq12, .atom 3])]
  cases.all fun (item, value) =>
    let returned := KatLang.Expr.call (resolve "Id") [sequenceSpread (.listLiteral [item])]
    let stored := alg [] [] [] [returned]
    match runCountedProgram (.algorithmExpr (algPrivate [] []
      (collProps ++ [("Stored", stored)]) [
        .call (resolve "Coll") [returned],
        .call (resolve "Coll") [resolve "Stored"],
        .call (resolve "Coll") [resolve "Stored"]
      ])) with
    | .ok (actual, count) =>
        let expected := Result.listValue [value]
        actual == .sequenceValue [expected, expected, expected] && count == 3
    | _ => false

#guard valuesStayValuesThroughReturnsAndStorage

-- FORWARDING LAW: `Forward(*xs) = Coll(xs*)` re-supplies exactly the collected
-- items — spread(collect(S)) = S — for every supply shape.
def forwardingReconstructsTheCollectedSupply : Bool :=
  let supplies : List (List KatLang.Expr) :=
    [ [], [.num 1], [.emptySequence 0], [.listLiteral []], [pair12],
      [.listLiteral [.num 1, .num 2]], [sequenceSpread (.listLiteral [pair12])],
      [sequenceSpread (.listLiteral [.emptySequence 0])],
      [.listLiteral [.listLiteral [.num 1, .num 2]], .capture [pair12, .num 3]],
      [.num 1, pair12, .listLiteral [], .emptySequence 0] ]
  supplies.all fun args =>
    match runColl (.call (resolve "Forward") args), runColl (.call (resolve "Coll") args) with
    | Except.ok forwarded, Except.ok direct => forwarded == direct
    | _, _ => false

#guard forwardingReconstructsTheCollectedSupply

/-- The innermost error beneath `withContext` frames (local copy; the shared
    `innermostError` lives in `SequenceCallbackBuiltins`). -/
def evoInnermostError : Error -> Error
  | .withContext _ inner => evoInnermostError inner
  | other => other

/-- Two outcomes agree: equal results, or the same innermost error. -/
def evoSameOutcome (expected actual : Except Error Result) : Bool :=
  match expected, actual with
  | .ok e, .ok a => e == a
  | .error e, .error a => reprStr (evoInnermostError e) == reprStr (evoInnermostError a)
  | _, _ => false

-- Explicit structural parameter patterns remain the openers, for a sequence
-- and a list alike: `Pair((x, y)) = [x, y]`, `Parts((*xs)) = xs`,
-- `HeadTail((x, *xs)) = [x, xs]`. A non-structured argument is the ordinary
-- one-item fallback of a nested pattern, and `()` / `[]` open to zero items.
-- The callback spelling `map([V], P)` binds exactly as the direct call `P(V)`.
def structuralPatternsOpenSequencesAndListsAlike : Bool :=
  let pairAlg := algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] []
    [.listLiteral [.param "x", .param "y"]]
  let headTailAlg := algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "xs", kind := .collecting }]] [] []
    [.listLiteral [.param "x", .param "xs"]]
  let props := [("Pair", pairAlg), ("Parts", collPartsAlg), ("HeadTail", headTailAlg)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  let fails (expected actual : Nat) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.error err => innermostIsArityMismatch expected actual err
    | _ => false
  let nestedSeq : KatLang.Expr := .capture [pair12, .num 3]
  let nestedList : KatLang.Expr := .listLiteral [.listLiteral [.num 1, .num 2], .num 3]
  let list12Expr : KatLang.Expr := .listLiteral [.num 1, .num 2]
  is (.listValue [.atom 1, .atom 2]) (.call (resolve "Pair") [pair12]) &&
  is (.listValue [.atom 1, .atom 2]) (.call (resolve "Pair") [list12Expr]) &&
  is (.listValue [seq12, .atom 3]) (.call (resolve "Pair") [nestedSeq]) &&
  is (.listValue [list12, .atom 3]) (.call (resolve "Pair") [nestedList]) &&
  fails 2 0 (.call (resolve "Pair") [.emptySequence 0]) &&
  fails 2 0 (.call (resolve "Pair") [.listLiteral []]) &&
  fails 2 1 (.call (resolve "Pair") [.num 7]) &&
  is list12 (.call (resolve "Parts") [pair12]) &&
  is list12 (.call (resolve "Parts") [list12Expr]) &&
  is (.listValue []) (.call (resolve "Parts") [.emptySequence 0]) &&
  is (.listValue []) (.call (resolve "Parts") [.listLiteral []]) &&
  is (.listValue [seq12, .atom 3]) (.call (resolve "Parts") [nestedSeq]) &&
  is (.listValue [list12, .atom 3]) (.call (resolve "Parts") [nestedList]) &&
  is (.listValue [.atom 7]) (.call (resolve "Parts") [.num 7]) &&
  is (.listValue [.atom 1, .listValue [.atom 2]]) (.call (resolve "HeadTail") [pair12]) &&
  is (.listValue [.atom 1, .listValue [.atom 2]]) (.call (resolve "HeadTail") [list12Expr]) &&
  is (.listValue [seq12, .listValue [.atom 3]]) (.call (resolve "HeadTail") [nestedSeq]) &&
  is (.listValue [.atom 7, .listValue []]) (.call (resolve "HeadTail") [.num 7]) &&
  fails 1 0 (.call (resolve "HeadTail") [.emptySequence 0]) &&
  -- The callback spelling binds exactly like the direct call.
  ([pair12, list12Expr, .emptySequence 0, .listLiteral [], nestedSeq, nestedList, .num 7]).all fun value =>
    ["Pair", "Parts", "HeadTail"].all fun callee =>
      match run (.call (resolve callee) [value]),
            run (.call (resolve "map") [.listLiteral [value], resolve callee]) with
      | Except.ok direct, Except.ok (.listValue [mapped]) => direct == mapped
      | Except.error direct, Except.error mapped =>
          reprStr (evoInnermostError direct) == reprStr (evoInnermostError mapped)
      | _, _ => false

#guard structuralPatternsOpenSequencesAndListsAlike

-- ALIASES AND FORWARDING change neither the callable nor the supply: with
-- `Cnt(*xs) = xs.count`, `Alias = Cnt`, `Apply(f, xs) = map(xs, f)`,
-- `Forward(g, xs) = Apply(g, xs)`, `Forward2(h, xs) = Forward(h, xs)` and a
-- nested-capture spelling `ApplyBlock(f, xs) = { map(xs, f) }`, every path
-- passes each element as ONE argument — a sequence element and a list element
-- alike — so every row is `[1, 1]`; the direct calls agree (`Cnt((10, 7))`
-- and `Cnt([10, 7])` are 1) and only the explicit spread supplies the
-- element's items (`Cnt((10, 7)*)`, `Cnt([10, 7]*)` are 2).
def aliasesAndForwardingKeepTheCallbackLaw : Bool :=
  -- `Alias = Cnt` elaborates to the implicit forwarding `Alias(*xs) = Cnt(xs*)`
  -- (the front end forwards a collecting capture into a collecting callee
  -- through the explicit spread), so the forwarding law is part of the path.
  let aliasAlg : Algorithm := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.call (resolve "Cnt") [sequenceSpread (.param "xs")]]
  let applyAlg : Algorithm := alg ["f", "xs"] [] [] [.call (resolve "map") [.param "xs", .param "f"]]
  let forwardAlg : Algorithm := alg ["g", "xs"] [] [] [.call (resolve "Apply") [.param "g", .param "xs"]]
  let forward2Alg : Algorithm := alg ["h", "xs"] [] [] [.call (resolve "Forward") [.param "h", .param "xs"]]
  let applyBlockAlg : Algorithm := alg ["f", "xs"] [] []
    [.algorithmExpr (alg [] [] [] [.call (resolve "map") [.param "xs", .param "f"]])]
  let props : List (Prod String Algorithm) :=
    [("Cnt", collCntAlg), ("Alias", aliasAlg), ("Apply", applyAlg), ("Forward", forwardAlg),
     ("Forward2", forward2Alg), ("ApplyBlock", applyBlockAlg)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  let seqInput : KatLang.Expr := .listLiteral [.capture [.num 10, .num 7], .num 20]
  let listInput : KatLang.Expr := .listLiteral [.listLiteral [.num 10, .num 7], .num 20]
  let ones : Result := .listValue [.atom 1, .atom 1]
  ([seqInput, listInput]).all (fun input =>
    is ones (.call (resolve "map") [input, resolve "Cnt"]) &&
    is ones (.call (resolve "map") [input, resolve "Alias"]) &&
    is ones (.call (resolve "Apply") [resolve "Cnt", input]) &&
    is ones (.call (resolve "Apply") [resolve "Alias", input]) &&
    is ones (.call (resolve "Forward") [resolve "Alias", input]) &&
    is ones (.call (resolve "Forward2") [resolve "Alias", input]) &&
    is ones (.call (resolve "Forward2") [resolve "Cnt", input]) &&
    is ones (.call (resolve "ApplyBlock") [resolve "Alias", input]) &&
    is ones (.dotCall input "map" (some [resolve "Alias"]))) &&
  is (.atom 1) (.call (resolve "Cnt") [.capture [.num 10, .num 7]]) &&
  is (.atom 1) (.call (resolve "Cnt") [.listLiteral [.num 10, .num 7]]) &&
  is (.atom 1) (.call (resolve "Alias") [.listLiteral [.num 10, .num 7]]) &&
  is (.atom 2) (.call (resolve "Cnt") [sequenceSpread (.capture [.num 10, .num 7])]) &&
  is (.atom 2) (.call (resolve "Cnt") [sequenceSpread (.listLiteral [.num 10, .num 7])]) &&
  is (.atom 2) (.call (resolve "Alias") [sequenceSpread (.listLiteral [.num 10, .num 7])])

#guard aliasesAndForwardingKeepTheCallbackLaw

-- THE REDUCE STEP IS THE ORDINARY TWO-ARGUMENT CALL: for every item `I`,
-- accumulator `A`, and reducer shape `R`, `reduce([I], R, A)` agrees with
-- `R(I, A)` — equal results, or the same innermost error. The accumulator is
-- ONE argument like the item: an accumulator-side collector collects it as one
-- item, a fixed parameter binds it unchanged, and only an explicit pattern
-- opens it — a sequence accumulator and a list accumulator alike.
def reduceStepIsTheOrdinaryTwoArgumentCall : Bool :=
  let fix (name : String) : KatLang.ParameterPattern := .capture { name := name }
  let coll (name : String) : KatLang.ParameterPattern := .capture { name := name, kind := .collecting }
  let reducers : List (Prod String Algorithm) :=
    [ ("Fixed", algWithParameterPatterns [fix "x", fix "acc"] [] []
        [.listLiteral [.param "x", .param "acc"]]),
      ("AccColl", algWithParameterPatterns [fix "x", coll "acc"] [] []
        [.listLiteral [.param "x", .param "acc"]]),
      ("Both", algWithParameterPatterns [coll "xs"] [] [] [.param "xs"]),
      ("ItemColl", algWithParameterPatterns [coll "items", fix "acc"] [] []
        [.listLiteral [.param "items", .param "acc"]]),
      ("AccPat", algWithParameterPatterns [fix "x", .sequenceValue [fix "a", coll "rest"]] [] []
        [.listLiteral [.param "x", .param "a", .param "rest"]]),
      ("ItemPat", algWithParameterPatterns [.sequenceValue [fix "p", coll "q"], fix "acc"] [] []
        [.listLiteral [.param "p", .param "q", .param "acc"]]) ]
  let items : List KatLang.Expr :=
    [ .num 7, pair12, .listLiteral [.num 1, .num 2], .emptySequence 0, .listLiteral [],
      .capture [pair12, .num 3], .listLiteral [.listLiteral [.num 1, .num 2], .num 3] ]
  let accumulators : List KatLang.Expr :=
    [ .num 0, pair12, .listLiteral [.num 1, .num 2], .emptySequence 0, .listLiteral [] ]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] reducers [out]))
  reducers.all fun (name, _) => items.all fun item => accumulators.all fun acc =>
    evoSameOutcome
      (run (.call (resolve name) [item, acc]))
      (run (.call (resolve "reduce") [.listLiteral [item], resolve name, acc]))

#guard reduceStepIsTheOrdinaryTwoArgumentCall

-- Loop state slots are the loop's ESTABLISHED supply and are never reopened or
-- collapsed: one scalar, sequence, or list state is one slot for a fixed step
-- (`repeat(Id, 1, S)` returns `S` unchanged); an explicit structural step
-- pattern opens a sequence and a list state alike (`Swap((a, b)) = (b, a)`);
-- several written state arguments are several slots; and a collecting `while`
-- step collects its state slots exactly — `W(n, *xs) = n + 1, xs.count, n < 1`
-- started from `0, (1, 2)` sees `xs = [(1, 2)]` (count 1), so it stops at the
-- state `(1, 1)`.
def loopStateMatrix : Bool :=
  let swapAlg := algWithParameterPatterns
    [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] []
    [.capture [.param "b", .param "a"]]
  let whileCollAlg := algWithParameters [{ name := "n" }, { name := "xs", kind := .collecting }] [] []
    [.binary .add (.param "n") (.num 1), .dotCall (.param "xs") "count" none,
     .compare .lt (.param "n") (.num 1)]
  let props := collProps ++ [("Swap", swapAlg), ("W", whileCollAlg)]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  is (.atom 7) (.call (resolve "repeat") [resolve "Id", .num 1, .num 7]) &&
  is seq12 (.call (resolve "repeat") [resolve "Id", .num 1, pair12]) &&
  is list12 (.call (resolve "repeat") [resolve "Id", .num 1, .listLiteral [.num 1, .num 2]]) &&
  is (.sequenceValue []) (.call (resolve "repeat") [resolve "Id", .num 1, .emptySequence 0]) &&
  is (.sequenceValue [.atom 2, .atom 1]) (.call (resolve "repeat") [resolve "Swap", .num 1, pair12]) &&
  is (.sequenceValue [.atom 2, .atom 1])
    (.call (resolve "repeat") [resolve "Swap", .num 1, .listLiteral [.num 1, .num 2]]) &&
  is seq12 (.call (resolve "repeat") [resolve "Swap", .num 2, pair12]) &&
  is (.atom 1) (.call (resolve "repeat") [resolve "Cnt", .num 1, pair12]) &&
  is (.atom 1) (.call (resolve "repeat") [resolve "Cnt", .num 1, .listLiteral [.num 1, .num 2]]) &&
  is (.atom 2) (.call (resolve "repeat") [resolve "Cnt", .num 1, .num 1, .num 2]) &&
  is (.atom 2) (.call (resolve "repeat") [resolve "Cnt", .num 1, sequenceSpread pair12]) &&
  is (.sequenceValue [.atom 1, .atom 1]) (.call (resolve "while") [resolve "W", .num 0, pair12]) &&
  is (.sequenceValue [.atom 1, .atom 1])
    (.call (resolve "while") [resolve "W", .num 0, .listLiteral [.num 1, .num 2]]) &&
  is (.sequenceValue [.atom 1, .atom 2])
    (.call (resolve "while") [resolve "W", .num 0, .num 1, .num 2])

#guard loopStateMatrix

-- Selection feeds every later consumer as ONE value: with `B = ((1, 2), 3)`
-- and `LL = [[1, 2], 3]`, `B:0`, `first(B)`, `LL:0`, and `first(LL)` bind a fixed
-- parameter unchanged, are rejected by a two-parameter callee (one argument),
-- are opened by an explicit structural pattern (`AddPair`) and by the
-- explicit spread (`Add(sel*)`), and are ONE collected item.
def selectionFeedsEveryConsumerAsOneValue : Bool :=
  let props := collProps ++ [("LL", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
  let run (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let is (expected : Result) (out : KatLang.Expr) : Bool :=
    match run out with
    | Except.ok value => value == expected
    | _ => false
  let selections : List (KatLang.Expr × Result) :=
    [ (.index (resolve "B") (.num 0), seq12),
      (.call (resolve "first") [resolve "B"], seq12),
      (.index (resolve "LL") (.num 0), list12),
      (.call (resolve "first") [resolve "LL"], list12) ]
  selections.all fun (selection, value) =>
    is value (.call (resolve "Id") [selection]) &&
    (match run (.call (resolve "Add") [selection]) with
     | Except.error err => innermostIsArityMismatch 2 1 err
     | _ => false) &&
    is (.atom 3) (.call (resolve "AddPair") [selection]) &&
    is (.atom 3) (.call (resolve "Add") [sequenceSpread selection]) &&
    is (.listValue [value]) (.call (resolve "Coll") [selection]) &&
    is (.listValue [value]) (.dotCall selection "Coll" none) &&
    is list12 (.call (resolve "Coll") [sequenceSpread selection]) &&
    is list12 (.dotCall (sequenceSpread selection) "Coll" none) &&
    is (.listValue [.atom 3]) (.call (resolve "map") [.listLiteral [selection], resolve "AddPair"])

#guard selectionFeedsEveryConsumerAsOneValue

-- Independent C-full review: the real flat binder must report the original
-- argument supply, just as the counted callback binder and the C# binder do.
#guard match KatLang.runEvalM (KatLang.bindParams ["x", "y"] [seq12]) with
  | .error (.arityMismatch 2 1) => true
  | _ => false

-- The algebra aliases callback binding to ordinary binding. This executable
-- guard checks the TWO real evaluator binders instead, including exact error
-- payloads, empty/structured values, mixed collectors, and repeated names.
-- Count provenance is deliberately varied before the callback value boundary.
def realCallbackBinderMatchesOrdinaryValueSupply : Bool := Id.run do
  let x : KatLang.ParameterPattern := .capture { name := "x" }
  let y : KatLang.ParameterPattern := .capture { name := "y" }
  let rest : KatLang.ParameterPattern := .capture { name := "rest", kind := .collecting }
  let pair : KatLang.ParameterPattern := .sequenceValue [x, y]
  let patterns := [[], [x], [x, y], [rest], [x, rest], [rest, y], [x, rest, y],
    [pair], [pair, y], [x, pair], [.sequenceValue [rest]],
    [.sequenceValue [x, rest]], [.sequenceValue [x, x]], [x, rest, x]]
  let values : List Result := [.atom 1, .sequenceValue [], .listValue [], seq12, list12,
    .sequenceValue [seq12, .atom 3], .listValue [list12, .atom 3],
    .listValue [seq12], .listValue [.sequenceValue []]]
  let supplies := [[]] ++ values.map (fun v => [v]) ++
    values.flatMap (fun v => values.map (fun w => [v, w]))
  return patterns.all fun ps => supplies.all fun supply => [0, 1, 4].all fun history =>
    let ordinary := KatLang.runEvalM (KatLang.bindParameterPatternList ps
      (supply.map fun v => { value? := some v }) false)
    let callback := KatLang.runEvalM (KatLang.bindCountedParameterPatternList ps
      (supply.map fun v => KatLang.countedSequenceCallbackItem (v, history)))
    match ordinary, callback with
    | .ok a, .ok b => a.argEnv == b.countedParamEnv.map (fun (name, value) => (name, value.fst))
    | .error a, .error b => reprStr a == reprStr b
    | _, _ => false

#guard realCallbackBinderMatchesOrdinaryValueSupply

end KatLangTests
