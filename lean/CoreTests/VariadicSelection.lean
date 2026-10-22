import KatLang
import CoreTests.Common

/-!
# Variadic postfix selection (October 2026)

`receiver[s1, …, sn]` replaces the retired colon form. PARENTHESES INVOKE A
COMPUTATION; POSTFIX BRACKETS SELECT FROM A VALUE; selection never changes how its
receiver obtains that value. These guards pin the `.index` arm of `evalCounted`
executably — the production instantiation of the total core whose laws live in
`KatLangArityLaws.lean` § Variadic postfix selection:

1. the receiver is demanded ONCE through its ordinary value path, even for an empty
   selection;
2. the selector supply is formed like a call's (`formNeedSupply`): explicit spreads
   run during formation, ordinary selectors stay suspended;
3. the supplied selectors are demanded, validated and selected LEFT TO RIGHT, and the
   first failure ends the selection;
4. the selected values are captured by ordinary normalization of the result grouping.

Evidence without host operations (the convention of `ArgumentValueOutcome`): every
user call opens ONE binding context (`EvalState.nextBindingContext`, allocated by
`EvalCtx.bindParameters`), kept for a failed run too, so the contexts a run opens
count how often each written computation ran. Distinct error kinds tell which failure
won. C# twin: `VariadicSelectionSemanticsTests` / `VariadicSelectionDemandTests`.
-/

namespace KatLangTests.VariadicSelection
open KatLang

/-- `Id(y) = y`: one binding context per call. -/
def idAlg : Algorithm := alg ["y"] [] [] [param "y"]

def list (items : List Int) : Expr := .listLiteral (items.map Expr.num)

/-- `Data = Id([10, 20, 30])`: its body opens exactly one context. -/
def dataAlg : Algorithm := alg [] [] [] [.call (resolve "Id") [list [10, 20, 30]]]

/-- `Bad = Id(1) / 0`: its body opens one context, then fails with `divByZero`. -/
def badAlg : Algorithm := alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)]

/-- `Kind = Id(true) + 1`: its body opens one context, then fails with `typeMismatch`. -/
def kindAlg : Algorithm := alg [] [] [] [.binary .add (.call (resolve "Id") [.boolLiteral true]) (num 1)]

/-- `Nested = [(10, 20), [30, 40], (), []]`. -/
def nestedAlg : Algorithm :=
  alg [] [] [] [.listLiteral [.capture [num 10, num 20], list [30, 40], .emptySequence 0, .listLiteral []]]

/-- `Pairs = [(10, 20), 30]`. -/
def pairsAlg : Algorithm := alg [] [] [] [.listLiteral [.capture [num 10, num 20], num 30]]

/-- `Grid = [[10, 20], [30, 40]]`. -/
def gridAlg : Algorithm := alg [] [] [] [.listLiteral [list [10, 20], list [30, 40]]]

/-- `Add(a, b) = a + b`. -/
def addAlg : Algorithm := alg ["a", "b"] [] [] [param "a" + param "b"]

/-- `Pick(*is) = Data[is*]`: the selectors are a collector slice, transported unforced. -/
def pickAlg : Algorithm :=
  algWithParameters [{ name := "is", kind := .collecting }] [] []
    [.index (resolve "Data") [.sequenceSpread (param "is")]]

/-- `K(x) = 7`: never demands its argument. -/
def kAlg : Algorithm := alg ["x"] [] [] [num 7]

def root (out : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", idAlg), ("Data", dataAlg), ("Bad", badAlg), ("Kind", kindAlg), ("Nested", nestedAlg)
    , ("Pairs", pairsAlg), ("Grid", gridAlg), ("Add", addAlg), ("Pick", pickAlg), ("K", kAlg) ]
    out)

/-- The outcome of a run AND the binding contexts it opened (kept for a failed run). -/
def runWithContexts (out : List Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM (root out)).runState EvalState.empty
  (result, state.nextBindingContext - 1)

def value (out : List Expr) : Option Result := (runResult (root out)).toOption
def contexts (out : List Expr) : Nat := (runWithContexts out).snd
def fails (check : Error -> Bool) (out : List Expr) : Bool :=
  match (runWithContexts out).fst with
  | .error err => check err
  | .ok _ => false

def sel (receiver : Expr) (selectors : List Expr) : Expr := .index receiver selectors
def data : Expr := resolve "Data"
def dataFresh : Expr := .call (resolve "Data") []
def seqv (items : List Result) : Result := .sequenceValue items
def atoms (items : List Int) : List Result := items.map Result.atom
def listv (items : List Int) : Result := .listValue (atoms items)

/-! ## 4. Normalization of the result grouping (the issue's table) -/

#guard value [sel data []] == some (seqv [])
#guard value [sel data [num 0]] == some (.atom 10)
#guard value [sel data [num 0, num 1]] == some (seqv (atoms [10, 20]))
#guard value [sel data [num 2, num 0]] == some (seqv (atoms [30, 10]))
#guard value [sel data [num 2, num 0, num 2]] == some (seqv (atoms [30, 10, 30]))

-- Nested and empty values are kept whole; selected `()` and `[]` stay elements.
#guard value [sel (resolve "Nested") [num 0]] == some (seqv (atoms [10, 20]))
#guard value [sel (resolve "Nested") [num 1]] == some (listv [30, 40])
#guard value [sel (resolve "Nested") [num 2]] == some (seqv [])
#guard value [sel (resolve "Nested") [num 3]] == some (.listValue [])
#guard value [sel (resolve "Nested") [num 0, num 1]] == some (seqv [seqv (atoms [10, 20]), listv [30, 40]])
#guard value [sel (resolve "Nested") [num 2, num 3]] == some (seqv [seqv [], .listValue []])
#guard value [sel (resolve "Nested") [num 2, num 2]] == some (seqv [seqv [], seqv []])

-- Emitted counts (the selection expression itself, `evalCounted`): zero selections and a
-- selected `()` emit nothing; everything else emits one value. The selection keeps no record
-- of how many selectors produced it.
def emitted (e : Expr) : Option Nat := ((runCountedProgram e).toOption).map Prod.snd
def nestedLiteral : Expr :=
  .listLiteral [.capture [num 10, num 20], list [30, 40], .emptySequence 0, .listLiteral []]
#guard emitted (sel (list [10, 20, 30]) []) == some 0
#guard emitted (sel (list [10, 20, 30]) [num 0]) == some 1
#guard emitted (sel (list [10, 20, 30]) [num 0, num 1]) == some 1
#guard emitted (sel nestedLiteral [num 2]) == some 0
#guard emitted (sel nestedLiteral [num 3]) == some 1
#guard emitted (sel nestedLiteral [num 2, num 2]) == some 1

-- Brackets do not remove singleton normalization: a selected pair spreads ITS items.
#guard value [.listLiteral [.sequenceSpread (sel (resolve "Pairs") [num 0])]] == some (listv [10, 20])
-- An exact one-per-index list is written explicitly.
#guard value [.listLiteral [sel (resolve "Pairs") [num 0]]] == some (.listValue [seqv (atoms [10, 20])])

-- Selection results are values, never an argument supply.
#guard fails (innermostIsArityMismatch 2 1) [.call (resolve "Add") [sel data [num 0, num 1]]]
#guard value [.call (resolve "Add") [.sequenceSpread (sel data [num 0, num 1])]] == some (.atom 30)

-- Commas select siblings; chained brackets descend.
#guard value [sel (resolve "Grid") [num 0, num 1]] == some (seqv [listv [10, 20], listv [30, 40]])
#guard value [sel (sel (resolve "Grid") [num 0]) [num 1]] == some (.atom 20)

/-! ## 3. The index supply: explicit spread only -/

def indexes (items : List Int) : Expr := list items
#guard value [sel data [.sequenceSpread (indexes [2, 0, 2])]] == some (seqv (atoms [30, 10, 30]))
#guard value [sel data [.sequenceSpread (indexes [0, 1])]] == some (seqv (atoms [10, 20]))
#guard value [sel data [.sequenceSpread (.listLiteral [])]] == some (seqv [])
#guard value [sel data [.sequenceSpread (.emptySequence 0)]] == some (seqv [])
-- A collection-valued selector is ONE supplied value of the wrong kind.
#guard fails innermostIsAnyTypeMismatch [sel data [.capture [num 0, num 1]]]
#guard fails innermostIsAnyTypeMismatch [sel data [indexes [0, 1]]]
#guard fails innermostIsAnyTypeMismatch [sel data [.emptySequence 0]]
-- Spread slots mix with ordinary slots in written order.
#guard value [sel data [num 1, .sequenceSpread (indexes [2, 0]), num 1]] == some (seqv (atoms [20, 30, 10, 20]))
#guard value [sel data [.sequenceSpread (indexes [2]), .sequenceSpread (indexes [0, 1])]] == some (seqv (atoms [30, 10, 20]))
-- A collector slice is transported and demanded in order.
#guard value [.call (resolve "Pick") [num 2, num 0]] == some (seqv (atoms [30, 10]))
#guard value [.call (resolve "Pick") []] == some (seqv [])
#guard fails innermostIsBadIndex [.call (resolve "Pick") [num 99, num 1 / num 0]]
#guard fails innermostIsDivByZero [.call (resolve "Pick") [num 1 / num 0, num 99]]

/-! ## 1–3. Demand and error order -/

-- The issue's pinned pair: an ordinary later selector is not demanded after a failure, while
-- an explicit spread runs during supply formation, before any ordinary selector.
#guard fails innermostIsBadIndex [sel (list [10, 20]) [num 99, num 1 / num 0]]
#guard fails innermostIsDivByZero [sel (list [10, 20]) [num 99, .sequenceSpread (num 1 / num 0)]]

-- Receiver failure wins before any selector spread runs (distinct kinds; only Bad's call ran).
#guard fails innermostIsDivByZero [sel (resolve "Bad") [.sequenceSpread (resolve "Kind")]]
#guard contexts [sel (resolve "Bad") [.sequenceSpread (resolve "Kind")]] == 1
-- The receiver also precedes an ORDINARY selector (distinct kinds; only Bad's call ran).
#guard fails innermostIsDivByZero [sel (resolve "Bad") [resolve "Kind"]]
#guard contexts [sel (resolve "Bad") [resolve "Kind"]] == 1
-- ... and an empty selection still demands the receiver.
#guard fails innermostIsDivByZero [sel (resolve "Bad") []]
#guard fails innermostIsDivByZero [sel (.call (resolve "Bad") []) []]

-- Every spread runs before the first ordinary selector is demanded.
#guard fails innermostIsDivByZero [sel data [resolve "Kind", .sequenceSpread (resolve "Bad")]]
#guard fails (innermostIsTypeMismatch "Expected a number, got a string")
  [sel data [.stringLiteral "x", .sequenceSpread (indexes [0])]]

-- Ordinary selectors are demanded left to right; the first failure wins.
#guard fails innermostIsAnyTypeMismatch [sel data [resolve "Kind", resolve "Bad"]]
#guard fails innermostIsDivByZero [sel data [resolve "Bad", resolve "Kind"]]
-- A later ordinary selector is never demanded after a failure: only Data's call ran.
#guard fails innermostIsBadIndex [sel data [num 99, .call (resolve "Id") [num 0]]]
#guard contexts [sel data [num 99, .call (resolve "Id") [num 0]]] == 1
-- A successful run demands each selector once: Data's call plus one Id per selector.
#guard contexts [sel data [.call (resolve "Id") [num 0], .call (resolve "Id") [num 1]]] == 3

/-! ## 1. The receiver: once, through its ordinary value path -/

-- A cached property read evaluates the body once across selections (ONE context: the body's
-- `Id` call). An explicit `Data()` is a fresh call each time: TWO contexts per call (the call
-- itself and the body's `Id` call).
#guard contexts [data] == 1
#guard contexts [dataFresh] == 2
#guard contexts [sel data [num 0], sel data [num 1]] == 1
#guard contexts [sel dataFresh [num 0], sel dataFresh [num 1]] == 4
-- Several selectors (repetitions included) select from ONE receiver value: one fresh call.
#guard contexts [sel dataFresh [num 2, num 0, num 2]] == 2
#guard value [sel dataFresh [num 2, num 0, num 2]] == some (seqv (atoms [30, 10, 30]))
#guard contexts [sel dataFresh []] == 2
#guard value [sel dataFresh []] == some (seqv [])
-- `Data()` never reads the ordinary entry, but as the owning zero-supply invocation of an empty
-- entry it ESTABLISHES it (CACHE-PUB-1, superseding "neither reads nor populates", which gave 2 + 1
-- contexts): the later bare reads reuse its value and evaluate nothing (2 contexts) …
#guard contexts [sel dataFresh [num 0], sel data [num 0], sel data [num 1]] == 2
-- … while a bare read first still leaves every later explicit call fresh (1 + 2 contexts).
#guard contexts [sel data [num 0], sel dataFresh [num 0], sel data [num 1]] == 3
-- An otherwise unused selection stays undemanded.
#guard value [.call (resolve "K") [sel (resolve "Bad") [num 0]]] == some (.atom 7)
#guard contexts [.call (resolve "K") [sel (resolve "Bad") [num 0]]] == 1

-- A selection of an empty selection is `()`: `Data[][]`.
#guard value [sel (sel data []) []] == some (seqv [])
-- A host-built capture of the bare `Data` read is ordinary capture (the parser erases `(Data)`):
-- singleton capture yields Data's list value, read through the cache like any bare `Data`.
#guard value [sel (.capture [data]) [num 0]] == some (.atom 10)
#guard contexts [sel (.capture [data]) [num 0], sel data [num 1]] == 1
-- A fresh `Data()` after a published entry neither reads it nor replaces it: one body for the
-- cached read, one fresh call, and the later bare read reuses the first entry.
#guard contexts [sel data [num 0], sel dataFresh [num 0], sel data [num 1]] == 3

/-! ## The shared positional view: scalars and strings -/

#guard value [.call (resolve "count") [.stringLiteral "abc"]] == some (.atom 1)
#guard value [.call (resolve "count") [.stringLiteral ""]] == some (.atom 1)
#guard value [sel (.stringLiteral "") [num 0]] == some (.str "")
#guard value [.call (resolve "first") [.stringLiteral "abc"]] == some (.str "abc")
#guard value [.call (resolve "last") [.stringLiteral "abc"]] == some (.str "abc")
#guard value [sel (.stringLiteral "abc") [num 0]] == some (.str "abc")
#guard fails innermostIsBadIndex [sel (.stringLiteral "abc") [num 1]]
#guard value [.call (resolve "count") [num 42]] == some (.atom 1)
#guard value [sel (num 42) [num 0]] == some (.atom 42)
#guard value [sel (.boolLiteral true) [num 0]] == some (.bool true)
#guard value [.call (resolve "count") [.listLiteral [.stringLiteral "abc", .stringLiteral "def"]]] == some (.atom 2)
#guard value [sel (.listLiteral [.stringLiteral "abc", .stringLiteral "def"]) [num 1]] == some (.str "def")
#guard value [.call (resolve "count") [.listLiteral [.listLiteral [.stringLiteral "a", .stringLiteral "b"]]]] == some (.atom 1)
#guard value [sel (list [10, 20]) [num 0, num 1]] == some (seqv (atoms [10, 20]))
#guard value [.call (resolve "count") [.listLiteral []]] == some (.atom 0)
#guard fails innermostIsBadIndex [.call (resolve "first") [.listLiteral []]]
#guard fails innermostIsBadIndex [sel (.listLiteral []) [num 0]]
#guard fails innermostIsBadIndex [sel (.emptySequence 0) [num 0]]
-- Selector validity is the retired colon form's: negative and past-the-end are `badIndex`,
-- a Boolean selector is a kind failure (no conversion).
#guard fails innermostIsBadIndex [sel data [.unary .minus (num 1)]]
#guard fails innermostIsBadIndex [sel data [num 3]]
#guard fails (innermostIsTypeMismatch "Expected a number, got a Boolean value") [sel data [.boolLiteral true]]

/-! ## first(v) ≡ v[0] and last(v) ≡ v[count(v) - 1] over the evaluator -/

def receivers : List Expr :=
  [ num 42, .boolLiteral false, .stringLiteral "abc", .stringLiteral "", list [10, 20, 30], list [7]
  , .listLiteral [], .emptySequence 0, .capture [num 1, .capture [num 2, num 3]]
  , .listLiteral [.emptySequence 0, .listLiteral []], .listLiteral [.stringLiteral "abc", .stringLiteral "def"] ]

def sameOutcome (a b : Except Error Result) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => innermostIsBadIndex x && innermostIsBadIndex y
  | _, _ => false

def firstAgrees (v : Expr) : Bool :=
  sameOutcome (runResult (root [.call (resolve "first") [v]])) (runResult (root [sel v [num 0]]))

def lastAgrees (v : Expr) : Bool :=
  sameOutcome (runResult (root [.call (resolve "last") [v]]))
    (runResult (root [sel v [Expr.call (resolve "count") [v] - num 1]]))

#guard receivers.all firstAgrees
#guard receivers.all lastAgrees

/-! ## No callable identity -/

#guard fails (innermostIsNotAnAlgorithm "index expression") [.call (sel data [num 0]) []]

/-! ## The single-selector form keeps the retired colon form's outcomes -/

-- With ONE ordinary selector the arm is the former one: receiver, selector, coercion, select.
#guard value [sel (list [1, 2, 3]) [num 2]] == some (.atom 3)
#guard fails innermostIsDivByZero [sel (num 1 / num 0) [num 1 / num 0]]
#guard fails innermostIsAnyTypeMismatch [sel (list [1, 2]) [.stringLiteral "0"]]

end KatLangTests.VariadicSelection
