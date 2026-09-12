import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algPrivate runFlat runResult Algorithm Error Result)
open KatLang (resolve param num)

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

/-- `Down(s) = s - 1, s` (a `while` step: next state, then the continue flag). -/
def whileStepAlg : Algorithm :=
  alg ["s"] [] [] [.binary .sub (.param "s") (.num 1), .param "s"]

/-- `Add(e, a) = e + a` (a reducer: a callback slot). -/
def reducerAlg : Algorithm := alg ["e", "a"] [] [] [.binary .add (.param "e") (.param "a")]

/-- `A = 7`. -/
def sevenAlg : Algorithm := alg [] [] [] [.num 7]

/-- `ApplyInIf(g) = if(1, g, 0)`: the slot names an algorithm-channel parameter. -/
def applyInIfAlg : Algorithm :=
  alg ["g"] [] [] [.call (resolve "if") [.num 1, param "g", .num 0]]

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
#guard rejectsAsPropertyArity [.call (resolve "if") [.num 1, resolve "Inc", .num 0]]

-- `if(0, 0, Inc)`: the selected false branch.
#guard rejectsAsPropertyArity [.call (resolve "if") [.num 0, .num 0, resolve "Inc"]]

-- `if(Inc, 1, 0)`: the condition slot.
#guard rejectsAsPropertyArity [.call (resolve "if") [resolve "Inc", .num 1, .num 0]]

-- `if(0, Inc, 7)` / `if(1, 7, Inc)`: the unselected slot is never demanded.
#guard flatOk [.call (resolve "if") [.num 0, resolve "Inc", .num 7]] [7]
#guard flatOk [.call (resolve "if") [.num 1, .num 7, resolve "Inc"]] [7]

-- `if(1, A, 0)`: a zero-parameter algorithm is an ordinary value.
#guard flatOk [.call (resolve "if") [.num 1, resolve "A", .num 0]] [7]

-- `if(1, K, 0)`: the decision is the signature's, not the body's — `K(x) = 5`
-- would succeed if entered, and is rejected all the same.
#guard rejectsAsPropertyArityOf "K" [.call (resolve "if") [.num 1, resolve "K", .num 0]]

-- `if(1, Inc(4), 0)`: an explicit call is a value.
#guard flatOk [.call (resolve "if") [.num 1, .call (resolve "Inc") [.num 4], .num 0]] [5]

-- `if(1, Collect, 0)` versus `if(1, Collect(), 0)`: a collecting callable still
-- has a parameter, so it is not a zero-argument value; the explicit empty call is.
def collectingSlotRejects : Bool :=
  match runResult (valueDemandRoot [.call (resolve "if") [.num 1, resolve "Collect", .num 0]]) with
  | Except.error err => innermostIsArityMismatch 1 0 err && hasContext "while evaluating property Collect" err
  | _ => false
#guard collectingSlotRejects

def collectingExplicitCallIsValue : Bool :=
  match runResult (valueDemandRoot [.call (resolve "if") [.num 1, .call (resolve "Collect") [], .num 0]]) with
  | Except.ok (Result.listValue []) => true
  | _ => false
#guard collectingExplicitCallIsValue

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
      [.num 1, .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]), .num 0]]) with
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

end KatLangTests
