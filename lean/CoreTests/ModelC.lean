import KatLang
import CoreTests.Common

namespace KatLangTests.ModelC
open KatLang

def bad : Expr := .binary .div (.num 1) (.num 0)
def call (parameters : List Ident) (body : List Expr) (arguments : OutputBundle) : Expr :=
  .algorithmExpr (alg [] [] [] [.call (.algorithmExpr (alg parameters [] [] body)) arguments])

#guard (runResult (call ["x"] [.num 7] [bad])).toOption == some (.atom 7)
#guard (runResult (call ["x", "y"] [.param "x"] [.num 3, bad])).toOption == some (.atom 3)
#guard (runResult (call ["x"] [.binary .add (.param "x") (.param "x")] [.num 4])).toOption == some (.atom 8)
#guard match runResult (call ["x"] [.param "x"] [bad, .num 2]) with
  | .error error => innermostIsArityMismatch 1 2 error
  | _ => false
#guard match runResult (call ["x", "x", "y"] [.num 7] [.num 1, .num 2, bad]) with
  | .error error => innermostIsBadArity error
  | _ => false

def collecting (body : List Expr) : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] body
def collectingCall (body : List Expr) (arguments : OutputBundle) : Expr :=
  .algorithmExpr (alg [] [] [] [.call (.algorithmExpr (collecting body)) arguments])
#guard (runResult (collectingCall [.num 9] [bad])).toOption == some (.atom 9)
#guard match runResult (collectingCall [.call (.resolve "first") [.param "xs"]] [.num 1, bad]) with
  | .error error => innermostIsDivByZero error
  | _ => false
#guard (runResult (.algorithmExpr (alg [] [] [] [.call (.resolve "map") [.listLiteral [], bad]]))).toOption == some (.listValue [])
#guard (runResult (.algorithmExpr (alg [] [] [] [.call (.resolve "filter") [.listLiteral [], bad]]))).toOption == some (.listValue [])
#guard (runResult (.algorithmExpr (alg [] [] [] [.call (.resolve "reduce") [.listLiteral [], bad, .num 4]]))).toOption == some (.atom 4)
#guard (runResult (.algorithmExpr (alg [] [] [] [.call (.resolve "repeat") [.algorithmExpr (alg ["x"] [] [] [.num 8]), .num 1, bad]]))).toOption == some (.atom 8)

def sharesAddress : EvalM Bool := do
  let address <- supplyNeed (.num 7) EvalCtx.empty []
  let transported <- supplyNeed (.param "x") { EvalCtx.empty with needEnv := [("x", address)] } []
  let first <- demandNeed transported
  let second <- demandNeed address
  pure (address == transported && first == second && (<- get).needs.size == 1)
#guard (runEvalM sharesAddress).toOption == some true

def stickyFailure : EvalM Bool := do
  let address <- supplyNeed bad EvalCtx.empty []
  let first <- evalAttempt (demandNeed address)
  let second <- evalAttempt (demandNeed address)
  pure (match first, second with | .error .divByZero, .error .divByZero => true | _, _ => false)
#guard (runEvalM stickyFailure).toOption == some true

def cycle : EvalM CountedResult := do
  let address <- allocateNeed (.expression (.param "x") { EvalCtx.empty with needEnv := [("x", 0)] } [])
  demandNeed address
#guard match runEvalM cycle with | .error .demandCycle => true | _ => false

-- These heap checks pin completion and address sharing independently of final values.
def isSuspended (address : Nat) : EvalM Bool := do
  match (<- get).needs[address]? with
  | some { state := .suspended, .. } => pure true
  | _ => pure false

def unusedSupply : EvalM Bool := do
  let address <- supplyNeed bad EvalCtx.empty []
  let result <- evalNeedUserSupply (alg ["x"] [] [] [.num 7]) [address] EvalCtx.empty [] false
  pure (result == (.atom 7, 1) && (<- isSuspended address))
#guard (runEvalM unusedSupply).toOption == some true

def completionDoesNoFurtherWork : EvalM Bool := do
  let source := Expr.call (.algorithmExpr (alg [] [] [] [.num 7])) []
  let address <- supplyNeed source EvalCtx.empty []
  let first <- demandNeed address
  let afterFirst := (<- get).nextBindingContext
  let second <- demandNeed address
  pure (first == second && afterFirst > 1 && (<- get).nextBindingContext == afterFirst)
#guard (runEvalM completionDoesNoFurtherWork).toOption == some true

def failedCompletionDoesNoFurtherWork : EvalM Bool := do
  let source := Expr.call (.algorithmExpr (alg [] [] [] [bad])) []
  let address <- supplyNeed source EvalCtx.empty []
  let first <- evalAttempt (demandNeed address)
  let afterFirst := (<- get).nextBindingContext
  let second <- evalAttempt (demandNeed address)
  pure (reprStr first == reprStr second && afterFirst > 1 && (<- get).nextBindingContext == afterFirst)
#guard (runEvalM failedCompletionDoesNoFurtherWork).toOption == some true

def attemptsShareCompletion : EvalM Bool := do
  let source := Expr.call (.algorithmExpr (alg [] [] [] [.num 1])) []
  let inspected <- supplyNeed source EvalCtx.empty []
  let ignored <- supplyNeed bad EvalCtx.empty []
  let first <- bindNeedPatterns [.literal (.litInt 0), .bind "x"] [inspected, ignored] true
  let afterFirst := (<- get).nextBindingContext
  let second <- bindNeedPatterns [.literal (.litInt 1), .bind "x"] [inspected, ignored] true
  pure (first.isNone && second.isSome && (<- get).nextBindingContext == afterFirst && (<- isSuspended ignored))
#guard (runEvalM attemptsShareCompletion).toOption == some true

def sliceTransport : EvalM Bool := do
  let element <- supplyNeed bad EvalCtx.empty []
  let collector <- allocateNeed (.collector [element])
  let ctx := { EvalCtx.empty with needEnv := [("xs", collector)] }
  let passed <- supplyNeed (.param "xs") ctx []
  let opened <- formNeedSupply [.sequenceSpread (.param "xs")] ctx []
  pure (passed == collector && opened == [element] && (<- isSuspended collector) && (<- isSuspended element))
#guard (runEvalM sliceTransport).toOption == some true

def projectionLeavesValueSuspended : EvalM Bool := do
  let address <- supplyNeed (.algorithmExpr (alg ["x"] [] [] [bad])) EvalCtx.empty []
  let identity <- projectNeedCallable address
  pure (identity.isSome && (<- isSuspended address))
#guard (runEvalM projectionLeavesValueSuspended).toOption == some true

def forwardingLeavesSupplySuspended : EvalM Bool := do
  let address <- supplyNeed bad EvalCtx.empty []
  let ctx := { EvalCtx.empty with needEnv := [("x", address)] }
  let supply <- formNeedSupply [.param "x"] ctx []
  let result <- evalNeedUserSupply (alg ["x"] [] [] [.num 7]) supply ctx [] false
  pure (supply == [address] && result.fst == .atom 7 && (<- isSuspended address))
#guard (runEvalM forwardingLeavesSupplySuspended).toOption == some true

#guard match runResult (call ["x"] [.num 7] [.sequenceSpread (.listLiteral [bad])]) with
  | .error err => innermostIsDivByZero err
  | _ => false

def choose : Algorithm := .conditional none []
  [ { pattern := .sequenceValue [.litBool true, .bind "yes", .bind "no"], body := alg [] [] [] [.param "yes"] }
  , { pattern := .sequenceValue [.litBool false, .bind "yes", .bind "no"], body := alg [] [] [] [.param "no"] }
  , { pattern := .sequenceValue [.bind "condition", .bind "yes", .bind "no"], body := alg [] [] [] [.unary .not (.param "condition")] } ]
def selector (callee : Expr) (arguments : OutputBundle) : Expr :=
  .algorithmExpr (algPrivate [] [] [("Choose", choose)] [.call callee arguments])
#guard ([ [.boolLiteral true, .num 7, bad], [.boolLiteral false, bad, .num 8], [.num 1, bad, bad] ] : List OutputBundle).all
  (fun arguments => reprStr (runResult (selector (.resolve "if") arguments)) ==
    reprStr (runResult (selector (.resolve "Choose") arguments)) ||
    (match runResult (selector (.resolve "if") arguments), runResult (selector (.resolve "Choose") arguments) with
    | .error left, .error right => innermostIsAnyTypeMismatch left && innermostIsAnyTypeMismatch right
    | _, _ => false))

-- Fresh recursive activations allocate fresh supplies; they are never a cyclic address.
def countdown : Algorithm := .conditional none []
  [ { pattern := .litInt 0, body := alg [] [] [] [.num 0] }
  , { pattern := .bind "n", body := alg [] [] [] [.call (.resolve "Down") [.binary .sub (.param "n") (.num 1)]] } ]
#guard (runResult (.algorithmExpr (algPrivate [] [] [("Down", countdown)] [.call (.resolve "Down") [.num 16]]))).toOption == some (.atom 0)

def aliasDoesNotForce : EvalM Bool := do
  let target := alg ["x"] [] [] [bad]
  let alias := Algorithm.alias none [] [] (.resolve "F")
  let root := algPrivate [] [] [("F", target), ("Alias", alias)] []
  let address <- supplyNeed (.resolve "Alias") (EvalCtx.empty.push root) []
  let identity <- projectNeedCallable address
  pure (identity.isSome && (<- isSuspended address) && (<- get).needs.size == 1)
#guard (runEvalM aliasDoesNotForce).toOption == some true

-- Cell completion and property caching are independent heap domains.
def propertyCacheIsSeparate : EvalM Bool := do
  let root := algPrivate [] [] [("Z", alg [] [] [] [.num 7])] []
  let ctx := EvalCtx.empty.push root
  let unused <- supplyNeed (.resolve "Z") ctx []
  let emptyBefore := (<- get).zeroArgPropertyCache.isEmpty
  let fresh <- supplyNeed (.call (.resolve "Z") []) ctx []
  let _ <- demandNeed fresh
  let emptyAfterCall := (<- get).zeroArgPropertyCache.isEmpty
  let _ <- demandNeed unused
  let count := (<- get).zeroArgPropertyCache.length
  let _ <- demandNeed unused
  pure (emptyBefore && emptyAfterCall && count == 1 && (<- get).zeroArgPropertyCache.length == count)
#guard (runEvalM propertyCacheIsSeparate).toOption == some true

-- Ready data uses the same inspecting binder and never becomes a fake callable.
def readyBindingUsesCanonicalPath : EvalM Bool := do
  let first <- readyNeed (.atom 3, 1)
  let second <- readyNeed (.atom 4, 1)
  let some binding <- bindNeedPatterns [.bind "x", .bind "xs" true] [first, second] | return false
  let some x := lookupAssoc "x" binding | return false
  let some xs := lookupAssoc "xs" binding | return false
  let collected <- demandNeed xs
  let callable <- projectNeedCallable first
  pure (x == first && callable.isNone && collected == (.listValue [.atom 4], 1))
#guard (runEvalM readyBindingUsesCanonicalPath).toOption == some true

/-! Result-value boundary: algorithm results are calculation values. Inputs may expose
    VALUE and CALLABLE; no result construction exports callable identity, and an
    undersupplied call is an arity failure, never a partially applied callable. -/

def returnF : Algorithm := alg ["f"] [] [] [.param "f"]
def applyF : Algorithm := alg ["f", "x"] [] [] [.call (.param "f") [.param "x"]]
def addXY : Algorithm := alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]
def resultRoot (rows : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Inc", incAlg), ("ReturnF", returnF), ("Apply", applyF), ("Choose", choose), ("Add", addXY)] rows)
def selectorOf (callee : Ident) : Expr :=
  .call (.resolve callee) [.boolLiteral true, .resolve "Inc", .resolve "Inc"]

-- Calls, selections, collections and captures project no callable, and projection forces nothing.
def computedSuppliesHaveNoCallable : EvalM Bool := do
  let root := algPrivate [] [] [("Inc", incAlg), ("ReturnF", returnF), ("Choose", choose)] []
  let ctx := EvalCtx.empty.push root
  let sources : List Expr :=
    [ .call (.resolve "ReturnF") [.resolve "Inc"], selectorOf "if", selectorOf "Choose"
    , .listLiteral [.resolve "Inc"], .index (.listLiteral [.resolve "Inc"]) (.num 0)
    , .capture [.resolve "Inc", .num 1] ]
  let addresses <- sources.mapM (fun source => supplyNeed source ctx [])
  let identities <- addresses.mapM projectNeedCallable
  let suspended <- addresses.allM isSuspended
  let named <- projectNeedCallable (<- supplyNeed (.resolve "Inc") ctx [])
  pure (identities.all Option.isNone && suspended && named.isSome)
#guard (runEvalM computedSuppliesHaveNoCallable).toOption == some true

-- A returned callable parameter is VALUE-demanded: the callable's own zero-supply rejection.
#guard match runResult (resultRoot [.call (.resolve "ReturnF") [.resolve "Inc"]]) with
  | .error error => innermostIsArityMismatch 1 0 error
  | _ => false
-- Applying a call result, or an if/Choose selection, finds no callable on the parameter.
#guard [ .call (.resolve "ReturnF") [.resolve "Inc"], selectorOf "if", selectorOf "Choose" ].all
  (fun argument => match runResult (resultRoot [.call (.resolve "Apply") [argument, .num 3]]) with
    | .error error => innermostIsNotAnAlgorithm "param(f)" error
    | _ => false)
-- Selected results agree between builtin `if` and an ordinary clause family.
#guard match runResult (resultRoot [selectorOf "if"]), runResult (resultRoot [selectorOf "Choose"]) with
  | .error left, .error right => innermostIsArityMismatch 1 0 left && innermostIsArityMismatch 1 0 right
  | _, _ => false
-- An undersupplied call is an arity failure and never becomes callable.
#guard match runResult (resultRoot [.call (.resolve "Add") [.num 10]]) with
  | .error error => innermostIsArityMismatch 2 1 error
  | _ => false
#guard match runResult (resultRoot [.call (.resolve "Apply") [.call (.resolve "Add") [.num 10], .num 3]]) with
  | .error error => innermostIsNotAnAlgorithm "param(f)" error
  | _ => false
-- Higher-order inputs and forwarding are unaffected: the INPUT still supplies its callable.
#guard (runResult (resultRoot [.call (.resolve "Apply") [.resolve "Inc", .num 3]])).toOption == some (.atom 4)

end KatLangTests.ModelC
