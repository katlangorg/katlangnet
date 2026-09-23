import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate runFlat runResult Algorithm Error Result)
open KatLang (resolve param num)
open KatLang (runEvalM runResultM bindParameterPatternList EvalState)

--------------------------------------------------------------------------------
-- Zero-argument value demand at builtin VALUE slots (F9)
--------------------------------------------------------------------------------
-- A builtin VALUE slot (the `if` condition and branches, `while`/`repeat`
-- initial state, the `repeat` count, `atoms`, `range`, `reduce`'s initial
-- accumulator) and the ordinary-dot `string` receiver demand their algorithm
-- with zero explicit arguments through the ONE zero-argument demand law
-- (`zeroArgumentDemandError?`), the same law value-position access applies.
-- Consequences pinned here:
--   * a SELECTED parameterized algorithm is rejected from its effective
--     signature at the demand boundary — the ordinary arity rejection — and its
--     body is never entered (the former `unknownName x` from inside `Inc` is
--     gone, and a body that would happen to succeed without its parameter no
--     longer runs);
--   * an UNSELECTED slot is never demanded, so a parameterized algorithm there
--     is harmless (laziness is untouched);
--   * a zero-parameter algorithm is an ordinary value;
--   * a builtin CALLBACK slot that supplies arguments (loop steps, `map`/`reduce`
--     steps) never consults the law.

/-- `K(x) = 5` never reads its parameter: only the demand law can reject it. -/
def ignoringParamAlg : Algorithm := alg ["x"] [] [] [.num 5]

/-- `Collect(*xs) = xs`. -/
def collectingAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]

/-- `Step(s) = s + 1` (a loop step: a callback slot). -/
def loopStepAlg : Algorithm := alg ["s"] [] [] [.binary .add (.param "s") (.num 1)]

/-- `Down(s) = s - 1, s != 0` (a `while` step: next state, then the Boolean continue flag). -/
def whileStepAlg : Algorithm :=
  alg ["s"] [] [] [.binary .sub (.param "s") (.num 1), .compare .ne (.param "s") (.num 0)]

/-- `Add(e, a) = e + a` (a reducer: a callback slot). -/
def reducerAlg : Algorithm := alg ["e", "a"] [] [] [.binary .add (.param "e") (.param "a")]

/-- `A = 7`. -/
def sevenAlg : Algorithm := alg [] [] [] [.num 7]

/-- `ApplyInIf(g) = if(true, g, 0)`: the slot names an algorithm-channel parameter. -/
def applyInIfAlg : Algorithm :=
  alg ["g"] [] [] [.call (resolve "if") [.boolLiteral true, param "g", .num 0]]

/-- `Lib = { Sub(x) = x }`: a navigated structural member. -/
def libWithParameterizedMember : Algorithm :=
  algPrivate [] [] [("Sub", alg ["x"] [] [] [.param "x"])] []

def valueDemandRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Inc", incAlg), ("K", ignoringParamAlg), ("Collect", collectingAlg)
    , ("Step", loopStepAlg), ("Down", whileStepAlg), ("Add", reducerAlg)
    , ("A", sevenAlg), ("ApplyInIf", applyInIfAlg), ("Lib", libWithParameterizedMember) ]
    out)

def innermostIsUnresolvedImplicitParams (names : List KatLang.Ident) : Error -> Bool
  | .withContext _ inner => innermostIsUnresolvedImplicitParams names inner
  | .unresolvedImplicitParams actual => actual = names
  | _ => false

/-- The selected slot's rejection is the property-style arity error — the same
    report the property written as an output row produces — never `unknownName x`. -/
def rejectsAsPropertyArityOf (name : String) (out : List KatLang.Expr) : Bool :=
  match runResult (valueDemandRoot out) with
  | Except.error err =>
      innermostIsArityMismatch 1 0 err && hasContext s!"while evaluating property {name}" err
        && !(innermostIsUnknownName "x" err)
  | _ => false

def rejectsAsPropertyArity (out : List KatLang.Expr) : Bool :=
  rejectsAsPropertyArityOf "Inc" out

def flatOk (out : List KatLang.Expr) (expected : List Int) : Bool :=
  expectFlat (runFlat (valueDemandRoot out)) expected

-- `if(1, Inc, 0)`: the selected true branch.
#guard rejectsAsPropertyArity [.call (resolve "if") [.boolLiteral true, resolve "Inc", .num 0]]

-- `if(0, 0, Inc)`: the selected false branch.
#guard rejectsAsPropertyArity [.call (resolve "if") [.boolLiteral false, .num 0, resolve "Inc"]]

-- `if(Inc, 1, 0)`: the condition slot.
#guard rejectsAsPropertyArity [.call (resolve "if") [resolve "Inc", .num 1, .num 0]]

-- `if(0, Inc, 7)` / `if(1, 7, Inc)`: the unselected slot is never demanded.
#guard flatOk [.call (resolve "if") [.boolLiteral false, resolve "Inc", .num 7]] [7]
#guard flatOk [.call (resolve "if") [.boolLiteral true, .num 7, resolve "Inc"]] [7]

-- `if(1, A, 0)`: a zero-parameter algorithm is an ordinary value.
#guard flatOk [.call (resolve "if") [.boolLiteral true, resolve "A", .num 0]] [7]

-- `if(1, K, 0)`: the decision is the signature's, not the body's — `K(x) = 5`
-- would succeed if entered, and is rejected all the same.
#guard rejectsAsPropertyArityOf "K" [.call (resolve "if") [.boolLiteral true, resolve "K", .num 0]]

-- `if(1, Inc(4), 0)`: an explicit call is a value.
#guard flatOk [.call (resolve "if") [.boolLiteral true, .call (resolve "Inc") [.num 4], .num 0]] [5]

-- `if(1, Collect, 0)` and `if(1, Collect(), 0)` AGREE (September 2026): a
-- collecting parameter requires no supplied slot, so `Collect()` accepts zero
-- supplied arguments and bare `Collect` is therefore a zero-argument value too,
-- with the collecting parameter bound to the exact empty list.
def emptyListRow (row : KatLang.Expr) : Bool :=
  match runResult (valueDemandRoot [row]) with
  | Except.ok (Result.listValue []) => true
  | _ => false

#guard emptyListRow (.call (resolve "if") [.boolLiteral true, resolve "Collect", .num 0])
#guard emptyListRow (.call (resolve "if") [.boolLiteral true, .call (resolve "Collect") [], .num 0])

-- `ApplyInIf(Inc)`: an algorithm-channel parameter in the slot reports the
-- parameter arm's bare arity rejection (no property context) — the same report
-- as reading `g` in value position.
def parameterSlotRejectsBare : Bool :=
  match runResult (valueDemandRoot [.call (resolve "ApplyInIf") [resolve "Inc"]]) with
  | Except.error err =>
      innermostIsArityMismatch 1 0 err && !(hasContext "while evaluating property Inc" err)
        && !(innermostIsUnknownName "x" err)
  | _ => false
#guard parameterSlotRejectsBare

-- `if(1, {x + 1}, 0)` with the block's `x` an (unresolved) parameter: a written
-- brace block reports `unresolvedImplicitParams`, as it does in value position.
def blockSlotReportsUnresolvedImplicitParams : Bool :=
  match runResult (valueDemandRoot [.call (resolve "if")
      [.boolLiteral true, .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]), .num 0]]) with
  | Except.error err => innermostIsUnresolvedImplicitParams ["x"] err
  | _ => false
#guard blockSlotReportsUnresolvedImplicitParams

-- Loop VALUE slots: `repeat(Step, 1, Inc)` (initial state), `repeat(Step, Inc, 0)`
-- (count), `while(Down, Inc)` (initial state); the zero-parameter controls run.
#guard rejectsAsPropertyArity [.call (resolve "repeat") [resolve "Step", .num 1, resolve "Inc"]]
#guard rejectsAsPropertyArity [.call (resolve "repeat") [resolve "Step", resolve "Inc", .num 0]]
#guard rejectsAsPropertyArity [.call (resolve "while") [resolve "Down", resolve "Inc"]]
#guard flatOk [.call (resolve "repeat") [resolve "Step", .num 1, resolve "A"]] [8]
#guard flatOk [.call (resolve "while") [resolve "Down", resolve "A"]] [0]

-- `atoms(Inc)` / `range(1, Inc)` are value slots too; `atoms(A)` is the list `[7]`.
#guard rejectsAsPropertyArity [.call (resolve "atoms") [resolve "Inc"]]
#guard rejectsAsPropertyArity [.call (resolve "range") [.num 1, resolve "Inc"]]
#guard flatOk [.call (resolve "atoms") [resolve "A"]] [7]

-- Callback slots supply arguments and never consult the law: `repeat(Inc, 2, 0)`,
-- `map([1, 2], Inc)`, `reduce([1, 2], Add, 0)`.
#guard flatOk [.call (resolve "repeat") [resolve "Inc", .num 2, .num 0]] [2]
#guard flatOk [.call (resolve "map") [.listLiteral [.num 1, .num 2], resolve "Inc"]] [2, 3]
#guard flatOk [.call (resolve "reduce") [.listLiteral [.num 1, .num 2], resolve "Add", .num 0]] [3]

-- `reduce`'s initial accumulator keeps its dedicated hint, now decided from the
-- signature: `K(x) = 5` is rejected without ever running (it used to yield 8).
def reduceInitialSlotRejectsFromSignature (initial : String) : Bool :=
  match runResult (valueDemandRoot [.call (resolve "reduce")
      [.listLiteral [.num 1, .num 2], resolve "Add", resolve initial]]) with
  | Except.error err =>
      hasContext "while preparing reduce initial accumulator" err && innermostIsBadArity err
  | _ => false
#guard reduceInitialSlotRejectsFromSignature "Inc"
#guard reduceInitialSlotRejectsFromSignature "K"

-- The ordinary-dot `string` receiver is a zero-argument value demand:
-- `Inc.string` is the property arity error, `A.string` the string "7", and a
-- navigated parameterized member `Lib.Sub.string` the bare arity rejection.
#guard rejectsAsPropertyArity [.dotCall (resolve "Inc") "string" none]

def zeroParameterStringReceiver : Bool :=
  match runResult (valueDemandRoot [.dotCall (resolve "A") "string" none]) with
  | Except.ok (Result.str "7") => true
  | _ => false
#guard zeroParameterStringReceiver

def navigatedMemberStringReceiverRejectsBare : Bool :=
  match runResult (valueDemandRoot [.dotCall (.dotCall (resolve "Lib") "Sub" none) "string" none]) with
  | Except.error err =>
      innermostIsArityMismatch 1 0 err && !(innermostIsUnknownName "x" err)
  | _ => false
#guard navigatedMemberStringReceiverRejectsBare

-- Collection binding must keep the shared demand's structured error and name;
-- the neutral category "arity" alone cannot distinguish this from `badArity`.
#guard rejectsAsPropertyArityOf "K" [.call (resolve "count") [resolve "K"]]
#guard rejectsAsPropertyArityOf "K" [.call (resolve "contains") [.listLiteral [.num 1], resolve "K"]]
#guard rejectsAsPropertyArityOf "K" [.call (resolve "take") [.listLiteral [.num 1], resolve "K"]]
#guard rejectsAsPropertyArityOf "K" [.call (resolve "skip") [.listLiteral [.num 1], resolve "K"]]

def valueDemandFamily : Algorithm := .conditional none []
  [ { pattern := .litInt 0, body := alg [] [] [] [.num 10] }
  , { pattern := .bind "x", body := alg [] [] [] [.binary .add (.param "x") (.num 1)] } ]

def familyDemandKeepsName (row : KatLang.Expr) : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
      [("F", valueDemandFamily), ("Add", reducerAlg)] [row])) with
  | .error err => innermostIsNoMatchingBranch "F" err
  | _ => false
#guard familyDemandKeepsName (.call (resolve "count") [resolve "F"])
#guard familyDemandKeepsName (.call (resolve "contains") [.listLiteral [.num 1], resolve "F"])
#guard familyDemandKeepsName (.call (resolve "reduce") [.listLiteral [], resolve "Add", resolve "F"])

-- Callback controls: collecting and conditional algorithms receive actual inputs.
#guard flatOk [.call (resolve "map") [.listLiteral [.num 1, .num 2], resolve "Collect"]] [1, 2]
#guard expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [("F", valueDemandFamily)]
    [.call (resolve "map") [.listLiteral [.num 0, .num 1], resolve "F"]]))) [10, 2]

--------------------------------------------------------------------------------
-- Zero-argument value demand follows ACTUAL call arity (September 2026)
--------------------------------------------------------------------------------
-- A callable may satisfy a zero-argument value demand IF AND ONLY IF an ordinary
-- call supplying zero arguments can bind it
-- (`Algorithm.acceptsZeroSuppliedArguments`, derived from the binder's own
-- `ParameterPattern.minimumSuppliedSlots` rule and from branch dispatch). A
-- COLLECTING parameter contributes ZERO required slots, so `Only(*xs)` is
-- demandable while `Head(x, *rest)` still requires one supplied value. The
-- rejection reports that true minimum, never the flattened declared capture
-- count.

/-- `Only(*xs) = xs`. -/
def onlyAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]

/-- `OnlyCount(*xs) = count(xs)`: a collecting-only callable whose zero-argument
    value is NUMERIC, so the `string` intrinsic's demanded receiver renders. -/
def onlyCountAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.call (resolve "count") [.param "xs"]]

/-- `Head(x, *rest) = x`. -/
def headAlg : Algorithm :=
  algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }] [] []
    [.param "x"]

/-- `Tail(*rest, z) = z`. -/
def tailAlg : Algorithm :=
  algWithParameters [{ name := "rest", kind := .collecting }, { name := "z" }] [] []
    [.param "z"]

/-- `Mid(x, *rest, z) = x`. -/
def midAlg : Algorithm :=
  algWithParameters
    [{ name := "x" }, { name := "rest", kind := .collecting }, { name := "z" }] [] []
    [.param "x"]

/-- `Pair(x, y) = x`. -/
def pairAlg : Algorithm := alg ["x", "y"] [] [] [.param "x"]

/-- `Grouped((x, y)) = x`: ONE supplied slot that the pattern opens. -/
def groupedAlg : Algorithm :=
  algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] []
    [.param "x"]

/-- `GroupedCollecting((x, *rest)) = x`: still ONE supplied slot — a nested
    collector never lowers the OUTER minimum. -/
def groupedCollectingAlg : Algorithm :=
  algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]]
    [] [] [.param "x"]

/-- `GroupedOnly((*xs)) = xs`: the nested collector is inside a group, so the
    callable still requires the ONE slot the group consumes. -/
def groupedOnlyAlg : Algorithm :=
  algWithParameterPatterns
    [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [.param "xs"]

/-- `GroupThenCollecting((a, b), *rest) = a`: a group plus a top-level collector,
    so the minimum is ONE — the count the binder enforces, not the two slots and
    not the three flattened captures. -/
def groupThenCollectingAlg : Algorithm :=
  algWithParameterPatterns
    [ .sequenceValue [.capture { name := "a" }, .capture { name := "b" }]
    , .capture { name := "rest", kind := .collecting } ] [] [] [.param "a"]

/-- `Captureless(()) = 5`: a host-built pattern with ZERO captures. It still
    consumes one supplied slot, so neither spelling accepts an empty supply — the
    decision is the supplied-slot count, never the capture count. -/
def capturelessAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue []] [] [] [.num 5]

/-- `ZeroArityFamily() = 7`: a host-built clause family whose branch pattern has
    top-level arity ZERO, so `ZeroArityFamily()` genuinely dispatches. -/
def zeroArityFamily : Algorithm := .conditional none []
  [ { pattern := .sequenceValue [], body := alg [] [] [] [.num 7] } ] none

def arityRoot (props : List (Prod KatLang.Ident Algorithm)) (out : List KatLang.Expr)
    : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] props out)

def signatureFamilies : List (Prod KatLang.Ident Algorithm) :=
  [ ("Zero", sevenAlg), ("Only", onlyAlg), ("OnlyCount", onlyCountAlg)
  , ("Head", headAlg), ("Tail", tailAlg)
  , ("Mid", midAlg), ("Pair", pairAlg), ("Grouped", groupedAlg)
  , ("GroupedCollecting", groupedCollectingAlg), ("GroupedOnly", groupedOnlyAlg)
  , ("GroupThenCollecting", groupThenCollectingAlg), ("Captureless", capturelessAlg)
  , ("ZeroArityFamily", zeroArityFamily) ]

def demandRow (name : KatLang.Ident) : KatLang.Expr := resolve name
def zeroCallRow (name : KatLang.Ident) : KatLang.Expr := .call (resolve name) []

def rowSucceeds (row : KatLang.Expr) : Bool :=
  match runResult (arityRoot signatureFamilies [row]) with
  | Except.ok _ => true
  | Except.error _ => false

/-- THE METAMORPHIC LAW. For every signature family: bare-`F` zero-argument
    demand eligibility agrees with the legality of the ordinary call `F()`. It
    compares LEGALITY, not cache behavior or evaluation counts, which the rule
    deliberately leaves alone. -/
def zeroDemandEligibilityMatchesZeroCallLegality : Bool :=
  signatureFamilies.all (fun family =>
    rowSucceeds (demandRow family.fst) == rowSucceeds (zeroCallRow family.fst))
#guard zeroDemandEligibilityMatchesZeroCallLegality

-- The eligible side: both spellings produce the same value.
#guard expectFlat (runFlat (arityRoot signatureFamilies [demandRow "Zero"])) [7]
#guard expectFlat (runFlat (arityRoot signatureFamilies [zeroCallRow "Zero"])) [7]
#guard expectFlat (runFlat (arityRoot signatureFamilies [demandRow "ZeroArityFamily"])) [7]
#guard expectFlat (runFlat (arityRoot signatureFamilies [zeroCallRow "ZeroArityFamily"])) [7]

def emptyListRowOf (row : KatLang.Expr) : Bool :=
  match runResult (arityRoot signatureFamilies [row]) with
  | Except.ok (Result.listValue []) => true
  | _ => false

-- A bare collecting-only callable IS a valid value expression, at the root and
-- everywhere a zero-argument value demand happens.
#guard emptyListRowOf (demandRow "Only")
#guard emptyListRowOf (zeroCallRow "Only")
#guard emptyListRowOf (.call (resolve "if") [.boolLiteral true, demandRow "Only", .num 0])
-- `Only.count` / `count(Only)` agree, and both see the demanded EMPTY list.
#guard expectFlat (runFlat (arityRoot signatureFamilies
    [.call (resolve "count") [demandRow "Only"]])) [0]
#guard expectFlat (runFlat (arityRoot signatureFamilies
    [.dotCall (demandRow "Only") "count" none])) [0]
#guard expectFlat (runFlat (arityRoot signatureFamilies
    [.call (resolve "count") [zeroCallRow "Only"]])) [0]
-- The `string` intrinsic receiver is a value-demand position too: the demanded
-- zero-argument value of a collecting-only callable renders.
#guard (match runResult (arityRoot signatureFamilies [.dotCall (demandRow "OnlyCount") "string" none]) with
        | Except.ok (Result.str "0") => true
        | _ => false)
#guard expectFlat (runFlat (arityRoot signatureFamilies [demandRow "OnlyCount"])) [0]

/-- The REJECTED side reports the callable's true MINIMUM supplied count — the
    count its ordinary zero-argument call reports — never the flattened declared
    capture count (`Head` is 1, not 2; `Grouped` is 1, not 2;
    `GroupThenCollecting` is 1, not 3). -/
def demandRejectsWithMinimum (name : KatLang.Ident) (minimum : Nat) : Bool :=
  match runResult (arityRoot signatureFamilies [demandRow name]) with
  | Except.error err =>
      innermostIsArityMismatch minimum 0 err
        && hasContext s!"while evaluating property {name}" err
  | _ => false

#guard demandRejectsWithMinimum "Head" 1
#guard demandRejectsWithMinimum "Tail" 1
#guard demandRejectsWithMinimum "Mid" 2
#guard demandRejectsWithMinimum "Pair" 2
#guard demandRejectsWithMinimum "Grouped" 1
-- A nested pattern's scalar one-item fallback binds ONE supplied value; it never
-- means the callable accepts zero.
#guard demandRejectsWithMinimum "GroupedCollecting" 1
#guard demandRejectsWithMinimum "GroupedOnly" 1
#guard demandRejectsWithMinimum "GroupThenCollecting" 1
-- A pattern with ZERO captures still consumes its supplied slot.
#guard demandRejectsWithMinimum "Captureless" 1

/-- Each rejected callable's ordinary zero-argument CALL reports the SAME
    minimum, so the two reports cannot drift. -/
def zeroCallRejectsWithMinimum (name : KatLang.Ident) (minimum : Nat) : Bool :=
  match runResult (arityRoot signatureFamilies [zeroCallRow name]) with
  | Except.error err => innermostIsArityMismatch minimum 0 err
  | _ => false

#guard zeroCallRejectsWithMinimum "Head" 1
#guard zeroCallRejectsWithMinimum "Tail" 1
#guard zeroCallRejectsWithMinimum "Mid" 2
#guard zeroCallRejectsWithMinimum "Pair" 2
#guard zeroCallRejectsWithMinimum "Grouped" 1
#guard zeroCallRejectsWithMinimum "GroupedCollecting" 1
#guard zeroCallRejectsWithMinimum "GroupedOnly" 1
#guard zeroCallRejectsWithMinimum "GroupThenCollecting" 1
#guard zeroCallRejectsWithMinimum "Captureless" 1

-- The ALGORITHM channel is untouched: `map` still receives `Only` as a callback,
-- so each element is collected, and a callable that cannot accept zero supplied
-- arguments is still a perfectly good callback.
#guard expectFlat (runFlat (arityRoot signatureFamilies
    [.call (resolve "map") [.listLiteral [.num 1, .num 2], resolve "Only"]])) [1, 2]
#guard expectFlat (runFlat (arityRoot signatureFamilies
    [.call (resolve "map") [.listLiteral [.num 1, .num 2], resolve "Head"]])) [1, 2]

-- A BUILTIN accepts no zero-argument supply, and its rejection stays the
-- builtin's own arity error (the very error `sum()` reports) rather than a
-- parameter-list one.
#guard (match runResult (arityRoot signatureFamilies [resolve "sum"]) with
        | Except.error err => innermostIsBadArity err || innermostIsAnyArityMismatch err
        | _ => false)

-- Host-built zero-capture signatures may not take a plain-output shortcut in
-- written slots: the empty group needs one argument and a family must dispatch.
def blockSlotDemandAgrees (a : Algorithm) : Bool :=
  let plain := runResult (arityRoot [] [.algorithmExpr a])
  let captured := runResult (arityRoot [] [.capture [.algorithmExpr a]])
  let listed := runResult (arityRoot [] [.listLiteral [.algorithmExpr a]])
  match plain, captured, listed with
  | .ok value, .ok capturedValue, .ok (.listValue [listedValue]) =>
      value == capturedValue && value == listedValue
  | .error (.unresolvedImplicitParams []), .error (.unresolvedImplicitParams []),
      .error (.unresolvedImplicitParams []) => true
  | _, _, _ => false
#guard blockSlotDemandAgrees capturelessAlg
#guard blockSlotDemandAgrees zeroArityFamily
#guard blockSlotDemandAgrees onlyAlg

-- Connect the acceptance predicate to the ACTUAL binder, independently of body
-- evaluation and across every user-pattern shape in the hand-authored matrix.
#guard signatureFamilies.all (fun (_, a) => match a with
  | .mk _ patterns _ _ _ _ =>
      let binds := match runEvalM (bindParameterPatternList patterns [] true) with
        | .ok _ => true
        | .error _ => false
      binds == Algorithm.acceptsZeroSuppliedArguments a
  | _ => true)

-- Cache insertion order exposes evaluation order without host operations. A
-- newly eligible source is demanded BEFORE the control's ordinary eager attempt.
def collectingSourceBeforeControl : Bool :=
  let source := algWithParameters [{ name := "xs", kind := .collecting }] [] [] [resolve "A"]
  let next := alg [] [] [] [resolve "B"]
  let program := arityRoot
    [("A", alg [] [] [] [.listLiteral [.num 7]]), ("B", alg [] [] [] [.num 1]),
     ("Source", source), ("Next", next)]
    [.call (resolve "take") [resolve "Source", .call (resolve "Next") []]]
  match (runResultM program).run EvalState.empty with
  | .ok (.listValue [.atom 7], state) =>
      state.zeroArgPropertyCache.map (fun entry => entry.fst.propertyName) == ["A", "B"]
  | _ => false
#guard collectingSourceBeforeControl

-- An empty collection never calls its callback. A zero-arity family in that
-- algorithm slot must therefore leave its body's otherwise cacheable read untouched.
def unusedZeroArityCallbackIsNotDemanded (inlineBlock : Bool) : Bool :=
  let family := Algorithm.conditional none []
    [{ pattern := .sequenceValue [], body := alg [] [] [] [resolve "A"] }] none
  let program := arityRoot [("A", sevenAlg), ("F", family)]
    [.call (resolve "map") [.listLiteral [], if inlineBlock then .algorithmExpr family else resolve "F"]]
  match (runResultM program).run EvalState.empty with
  | .ok (.listValue [], state) => state.zeroArgPropertyCache.isEmpty
  | _ => false
#guard unusedZeroArityCallbackIsNotDemanded false
#guard unusedZeroArityCallbackIsNotDemanded true

--------------------------------------------------------------------------------
-- A forwarded callable keeps its ALGORITHM channel in invoking builtin slots
--------------------------------------------------------------------------------
-- A parameter bound to a callable that ALSO satisfies a zero-argument value
-- demand (`OnlyCount(*xs) = count(xs)`) is bound on BOTH channels. A builtin
-- VALUE slot reads the bound value; a slot that INVOKES its argument — the
-- `map` mapper, the `filter` predicate, the `reduce` reducer, a `while` or
-- `repeat` step — invokes the algorithm-channel binding
-- (`ResolvedArgumentAlgorithm.invoked`), so forwarding a callback through a
-- parameter selects the same callable as a direct slot. Ordinary parameter binding
-- may already have demanded its value; slot selection adds no demand.
-- Before, every such slot received the demanded
-- value wrapped as a zero-parameter algorithm and failed with an arity error.

/-- `IsPos(*xs) = count(xs) > 0`. -/
def isPosCollectingAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.compare .gt (.call (resolve "count") [.param "xs"]) (.num 0)]

/-- `SumAll(*xs) = sum(xs)`: a reducer over `(item, accumulator)`. -/
def sumAllAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.call (resolve "sum") [.param "xs"]]

/-- `CountStep(*s) = count(s) + 1`: a `repeat` step. -/
def countStepAlg : Algorithm :=
  algWithParameters [{ name := "s", kind := .collecting }] [] []
    [.binary .add (.call (resolve "count") [.param "s"]) (.num 1)]

/-- `SumWhile(*s) = sum(s) + 1, sum(s) + 1 < 3`: a `while` step. -/
def sumWhileAlg : Algorithm :=
  let next := KatLang.Expr.binary .add (.call (resolve "sum") [.param "s"]) (.num 1)
  algWithParameters [{ name := "s", kind := .collecting }] [] []
    [next, .compare .lt next (.num 3)]

/-- `Forward(f, xs) = builtin(xs, f)` for a one-callback collection builtin. -/
def forwardCallbackAlg (builtin : String) : Algorithm :=
  alg ["f", "xs"] [] [] [.call (resolve builtin) [.param "xs", .param "f"]]

def forwardingRoot (out : List KatLang.Expr) : KatLang.Expr :=
  arityRoot
    [ ("OnlyCount", onlyCountAlg), ("IsPos", isPosCollectingAlg), ("SumAll", sumAllAlg)
    , ("CountStep", countStepAlg), ("SumWhile", sumWhileAlg), ("Add", reducerAlg)
    , ("Only", onlyAlg), ("A", sevenAlg)
    , ("ApplyMap", forwardCallbackAlg "map"), ("ApplyFilter", forwardCallbackAlg "filter")
    , ("ApplyReduce", alg ["f", "xs"] [] []
        [.call (resolve "reduce") [.param "xs", .param "f", .num 0]])
    , ("ApplyRepeat", alg ["g"] [] [] [.call (resolve "repeat") [.param "g", .num 3, .num 9]])
    , ("ApplyWhile", alg ["g"] [] [] [.call (resolve "while") [.param "g", .num 0]])
    , ("ApplyCount", alg ["xs"] [] [] [.call (resolve "count") [.param "xs"]])
    , ("ApplyInitial", alg ["i"] [] []
        [.call (resolve "reduce") [.listLiteral [.num 1, .num 2], resolve "Add", .param "i"]]) ]
    out

def oneTwo : KatLang.Expr := .listLiteral [.num 1, .num 2]

/-- The forwarded spelling produces exactly the direct spelling's value. -/
def forwardedCallbackAgrees (direct forwarded : KatLang.Expr) (expected : List Int) : Bool :=
  expectFlat (runFlat (forwardingRoot [direct])) expected
    && expectFlat (runFlat (forwardingRoot [forwarded])) expected
    && (match runResult (forwardingRoot [direct]), runResult (forwardingRoot [forwarded]) with
        | .ok d, .ok f => d == f
        | _, _ => false)

-- Callbacks: `map`, `filter`, `reduce`.
#guard forwardedCallbackAgrees
  (.call (resolve "map") [oneTwo, resolve "OnlyCount"])
  (.call (resolve "ApplyMap") [resolve "OnlyCount", oneTwo]) [1, 1]
#guard forwardedCallbackAgrees
  (.call (resolve "filter") [oneTwo, resolve "IsPos"])
  (.call (resolve "ApplyFilter") [resolve "IsPos", oneTwo]) [1, 2]
#guard forwardedCallbackAgrees
  (.call (resolve "reduce") [.listLiteral [.num 1, .num 2, .num 3], resolve "SumAll", .num 0])
  (.call (resolve "ApplyReduce") [resolve "SumAll", .listLiteral [.num 1, .num 2, .num 3]]) [6]
-- Loop steps: `repeat` and `while`.
#guard forwardedCallbackAgrees
  (.call (resolve "repeat") [resolve "CountStep", .num 3, .num 9])
  (.call (resolve "ApplyRepeat") [resolve "CountStep"]) [2]
#guard forwardedCallbackAgrees
  (.call (resolve "while") [resolve "SumWhile", .num 0])
  (.call (resolve "ApplyWhile") [resolve "SumWhile"]) [2]
-- A zero-argument-demand-ineligible callable was never bound on the value
-- channel and keeps working (`Add` needs two supplied values).
#guard expectFlat (runFlat (forwardingRoot
  [.call (resolve "ApplyMap") [resolve "Add", .listLiteral []]])) []

-- VALUE slots keep the value side: the `collection` argument and `reduce`'s
-- `initial` accumulator read the forwarded parameter's bound value.
#guard expectFlat (runFlat (forwardingRoot [.call (resolve "ApplyCount") [resolve "Only"]])) [0]
#guard expectFlat (runFlat (forwardingRoot [.call (resolve "ApplyInitial") [resolve "OnlyCount"]])) [3]
#guard expectFlat (runFlat (forwardingRoot [.call (resolve "ApplyInitial") [resolve "A"]])) [10]

-- A parameter bound on the VALUE channel only has no algorithm binding, so an
-- invoking slot still receives its value and rejects it as a zero-parameter
-- callback — exactly what the direct spelling `map([1, 2], 5)` reports; a
-- forwarded zero-parameter property is invoked like the direct one and rejected
-- the same way.
def invokedRejectsLikeDirect (direct forwarded : KatLang.Expr) : Bool :=
  match runResult (forwardingRoot [direct]), runResult (forwardingRoot [forwarded]) with
  | .error d, .error f => innermostIsArityMismatch 0 1 d && innermostIsArityMismatch 0 1 f
  | _, _ => false
#guard invokedRejectsLikeDirect
  (.call (resolve "map") [oneTwo, .num 5])
  (.call (resolve "ApplyMap") [.num 5, oneTwo])
#guard invokedRejectsLikeDirect
  (.call (resolve "map") [oneTwo, resolve "A"])
  (.call (resolve "ApplyMap") [resolve "A", oneTwo])

end KatLangTests
