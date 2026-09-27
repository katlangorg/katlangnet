import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algPrivate privateProp publicProp privateLocalProp runResultWithState Algorithm Error Result)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Zero-parameter property caching does not depend on the consumer
--------------------------------------------------------------------------------
-- THE RULE (`ZeroArgPropertyCacheKey`): a zero-parameter property is evaluated
-- once per run for each resolved property binding; repeated VALUE access to that
-- binding reuses the result; a shadowing property is a different binding with its
-- own entry; `A()` evaluates afresh, neither reading nor replacing the entry.
-- HOW A PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING: a builtin VALUE slot
-- (`sum(A)`, `A.sum`, `if(c, A, B)`, a loop's initial state, `reduce`'s initial
-- accumulator), the `.string` receiver, a user call, a callback, a selection and
-- a collection element all receive the value the property access produced
-- (`resolveArgAlgExpr`, `evalDotStringReceiverValue`); none of them can re-run
-- the property's body.
--
-- Evidence without host operations: `A`'s body is the call `Id([1, 2])` and
-- `N`'s is `Id(7)` (`.string` converts a NUMERIC receiver), and every call opens
-- exactly ONE binding context (`EvalState.nextBindingContext`, allocated by
-- `EvalCtx.bindParameters`), so the contexts a run opens count how often a
-- property's body ran plus the calls the consumer itself makes. Before the
-- consumer-transparency rule, every builtin VALUE slot and the `.string`
-- receiver re-ran the property's body and opened one context more than these
-- guards allow.

/-- `Id(x) = x`. -/
def cacheIdAlg : Algorithm := alg ["x"] [] [] [param "x"]

/-- `A = Id([1, 2])`: exactly one binding context per evaluation of A's body. -/
def cacheCountedAlg : Algorithm :=
  alg [] [] [] [.call (resolve "Id") [.listLiteral [num 1, num 2]]]

/-- `N = Id(7)`: a numeric property for the numeric consumers. -/
def cacheNumericAlg : Algorithm := alg [] [] [] [.call (resolve "Id") [num 7]]

/-- `Stats(xs) = sum(xs), max(xs)`: a user algorithm consuming the value. -/
def cacheStatsAlg : Algorithm :=
  alg ["xs"] [] [] [.call (resolve "sum") [param "xs"], .call (resolve "max") [param "xs"]]

/-- `Show(v) = v.string`: the intrinsic consuming a forwarded value. -/
def cacheShowAlg : Algorithm := alg ["v"] [] [] [.dotCall (param "v") "string" none]

/-- `Keep(s) = s`: a loop step. -/
def cacheKeepAlg : Algorithm := alg ["s"] [] [] [param "s"]

/-- `Big(x) = x > 1`: a filter predicate. -/
def cacheBigAlg : Algorithm := alg ["x"] [] [] [.compare .gt (param "x") (num 1)]

/-- `Add(e, a) = e + a`: a reducer. -/
def cacheAddAlg : Algorithm := alg ["e", "a"] [] [] [.binary .add (param "e") (param "a")]

/-- `Call0(f) = f()`: an EXPLICIT invocation of a forwarded callable. -/
def cacheCall0Alg : Algorithm := alg ["f"] [] [] [.call (param "f") []]

/-- `Box = { public V = Id(5) }`: a structurally navigated member. -/
def cacheBoxAlg : Algorithm :=
  alg [] [] [publicProp "V" (alg [] [] [] [.call (resolve "Id") [num 5]])] []

def cacheRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", cacheIdAlg), ("A", cacheCountedAlg), ("N", cacheNumericAlg), ("Stats", cacheStatsAlg)
    , ("Show", cacheShowAlg), ("Keep", cacheKeepAlg), ("Big", cacheBigAlg)
    , ("Add", cacheAddAlg), ("Call0", cacheCall0Alg), ("Box", cacheBoxAlg) ]
    out)

/-- The binding contexts a SUCCESSFUL run opened. -/
def contextsOpened (out : List KatLang.Expr) : Option Nat :=
  match runResultWithState (cacheRoot out) with
  | .ok (_, state) => some (state.nextBindingContext - 1)
  | .error _ => none

/-- The cache entries a SUCCESSFUL run stored under `name`. -/
def entriesNamed (name : String) (out : List KatLang.Expr) : Option Nat :=
  match runResultWithState (cacheRoot out) with
  | .ok (_, state) => some (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == name)).length
  | .error _ => none

/-- Reading `name` and then consuming it through `consumer` opens exactly the
    contexts of the single read plus the consumer's `ownCalls`: the property's
    body ran ONCE and the consumer received its cached value. -/
def consumerReusesTheReadOf (name : String) (consumer : KatLang.Expr) (ownCalls : Nat) : Bool :=
  contextsOpened [resolve name, consumer] == (contextsOpened [resolve name]).map (· + ownCalls)
    && entriesNamed name [resolve name, consumer] == some 1

def consumerReusesTheRead (consumer : KatLang.Expr) (ownCalls : Nat) : Bool :=
  consumerReusesTheReadOf "A" consumer ownCalls

-- The single read itself runs A's body once and stores one entry.
#guard contextsOpened [resolve "A"] == some 1
#guard entriesNamed "A" [resolve "A"] == some 1
-- Repeated value access: still once.
#guard contextsOpened [resolve "A", resolve "A", resolve "A"] == some 1

-- Builtin VALUE slots, written and dotted: the collection argument.
#guard consumerReusesTheRead (.call (resolve "sum") [resolve "A"]) 0
#guard consumerReusesTheRead (.dotCall (resolve "A") "sum" none) 0
#guard consumerReusesTheRead (.call (resolve "max") [resolve "A"]) 0
#guard consumerReusesTheRead (.dotCall (resolve "A") "max" none) 0
#guard consumerReusesTheRead (.call (resolve "min") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "avg") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "count") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "first") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "last") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "order") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "orderDesc") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "distinct") [resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "take") [resolve "A", num 1]) 0
#guard consumerReusesTheRead (.dotCall (resolve "A") "take" (some [num 1])) 0
#guard consumerReusesTheRead (.call (resolve "skip") [resolve "A", num 1]) 0
#guard consumerReusesTheRead (.call (resolve "contains") [resolve "A", num 2]) 0
#guard consumerReusesTheRead (.call (resolve "atoms") [resolve "A"]) 0
-- The lazy `if`: condition-selected branches, either side.
#guard consumerReusesTheRead (.call (resolve "if") [.boolLiteral true, resolve "A", num 0]) 0
#guard consumerReusesTheRead (.call (resolve "if") [.boolLiteral false, num 0, resolve "A"]) 0
-- Loop initial state and `reduce`'s initial accumulator.
#guard consumerReusesTheRead (.call (resolve "repeat") [resolve "Keep", num 0, resolve "A"]) 0
#guard consumerReusesTheRead (.call (resolve "repeat") [resolve "Keep", num 1, resolve "A"]) 1
#guard consumerReusesTheRead (.call (resolve "reduce") [.listLiteral [], resolve "Add", resolve "A"]) 0
-- Higher-order builtins: the collection is the cached value; the callbacks are
-- their own calls (two elements, two callback invocations).
#guard consumerReusesTheRead (.call (resolve "map") [resolve "A", resolve "Id"]) 2
#guard consumerReusesTheRead (.call (resolve "filter") [resolve "A", resolve "Big"]) 2
#guard consumerReusesTheRead (.call (resolve "reduce") [resolve "A", resolve "Add", num 0]) 2
-- The `.string` intrinsic, and the numeric consumers.
#guard consumerReusesTheReadOf "N" (.dotCall (resolve "N") "string" none) 0
#guard consumerReusesTheReadOf "N" (.call (resolve "if") [.compare .gt (resolve "N") (num 5), resolve "N", num 0]) 0
#guard consumerReusesTheReadOf "N" (.binary .add (resolve "N") (resolve "N")) 0
#guard consumerReusesTheReadOf "N" (.call (resolve "sum") [resolve "N"]) 0
-- User algorithms: one context for the call itself, none for A.
#guard consumerReusesTheRead (.call (resolve "Stats") [resolve "A"]) 1
#guard consumerReusesTheRead (.dotCall (resolve "A") "Stats" none) 1
-- A forwarded value consumed by `.string` inside the callee is that value.
#guard consumerReusesTheReadOf "N" (.call (resolve "Show") [resolve "N"]) 1
#guard consumerReusesTheReadOf "N" (.dotCall (resolve "N") "Show" none) 1
-- Value positions that always read the cache.
#guard consumerReusesTheRead (.index (resolve "A") (num 0)) 0
#guard consumerReusesTheRead (.listLiteral [resolve "A", resolve "A"]) 0
#guard consumerReusesTheRead (.capture [resolve "A", resolve "A"]) 0
#guard consumerReusesTheRead (.compare .eq (resolve "A") (resolve "A")) 0

-- The consumer ORDER does not matter: a builtin slot that reads first stores the
-- entry every later read reuses.
#guard contextsOpened [.call (resolve "sum") [resolve "A"], resolve "A", .dotCall (resolve "A") "max" none] == some 1
#guard contextsOpened [.dotCall (resolve "N") "string" none, resolve "N", .call (resolve "Show") [resolve "N"]] == some 2
#guard contextsOpened [.call (resolve "if") [.boolLiteral true, resolve "A", num 0],
                       .call (resolve "Stats") [resolve "A"], .dotCall (resolve "A") "max" none] == some 2

-- A structurally navigated member: every consumer shares the member's one entry.
#guard contextsOpened [.dotCall (resolve "Box") "V" none] == some 1
#guard contextsOpened [.dotCall (resolve "Box") "V" none,
                       .dotCall (.dotCall (resolve "Box") "V" none) "string" none,
                       .call (resolve "sum") [.dotCall (resolve "Box") "V" none],
                       .call (resolve "if") [.boolLiteral true, .dotCall (resolve "Box") "V" none, num 0],
                       .dotCall (.dotCall (resolve "Box") "V" none) "sum" none] == some 1
-- ... whichever spelling reads it first.
#guard contextsOpened [.dotCall (.dotCall (resolve "Box") "V" none) "string" none,
                       .dotCall (resolve "Box") "V" none] == some 1

--------------------------------------------------------------------------------
-- Explicit invocation bypasses, but never mutates, the entry
--------------------------------------------------------------------------------
-- `A()` is one call context plus A's body's own `Id` call.

-- `A, A(), A`: the ordinary read stores; the explicit call runs afresh; the last
-- read reuses the FIRST entry.
#guard contextsOpened [resolve "A", .call (resolve "A") [], resolve "A"] == some 3
#guard entriesNamed "A" [resolve "A", .call (resolve "A") [], resolve "A"] == some 1
-- `A(), A, A`: the explicit call stores nothing; the first read stores; the second reuses.
#guard contextsOpened [.call (resolve "A") [], resolve "A", resolve "A"] == some 3
#guard entriesNamed "A" [.call (resolve "A") [], resolve "A", resolve "A"] == some 1
-- `A(), A()`: two fresh evaluations, no entry.
#guard contextsOpened [.call (resolve "A") [], .call (resolve "A") []] == some 4
#guard entriesNamed "A" [.call (resolve "A") [], .call (resolve "A") []] == some 0
-- An explicit call inside a builtin slot is still an explicit call.
#guard contextsOpened [resolve "A", .call (resolve "sum") [.call (resolve "A") []]] == some 3
-- Explicitly invoking a FORWARDED callable is an explicit call too: `Call0(A)`
-- reads A's value for the argument (cached) and `f()` runs A's body afresh.
#guard contextsOpened [resolve "A", .call (resolve "Call0") [resolve "A"]] == some 4

--------------------------------------------------------------------------------
-- Cache identity follows the resolved binding, never the spelling
--------------------------------------------------------------------------------
-- `Inner` declares its own `A`, shadowing the root's: two bindings, two entries,
-- two values — each evaluated once however it is consumed.

/-- `Inner = { A = Id(3); A, sum(A), A.string }`. -/
def cacheInnerAlg : Algorithm :=
  algPrivate [] [] [("A", alg [] [] [] [.call (resolve "Id") [num 3]])]
    [resolve "A", .call (resolve "sum") [resolve "A"], .dotCall (resolve "A") "string" none]

def shadowingRoot : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", cacheIdAlg), ("A", cacheCountedAlg), ("Inner", cacheInnerAlg) ]
    [ resolve "A", .call (resolve "sum") [resolve "A"], resolve "Inner",
      .call (resolve "sum") [resolve "A"], resolve "Inner" ])

def shadowedBindingsStaySeparate : Bool :=
  match runResultWithState shadowingRoot with
  | .ok (Result.sequenceValue
      [ Result.listValue [Result.atom 1, Result.atom 2], Result.atom 3,
        Result.sequenceValue [Result.atom 3, Result.atom 3, Result.str "3"],
        Result.atom 3,
        Result.sequenceValue [Result.atom 3, Result.atom 3, Result.str "3"] ], state) =>
      -- root A once, Inner's A once; Inner itself is a cached zero-parameter read
      state.nextBindingContext - 1 == 2
        && (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "A")).length == 2
        && (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "Inner")).length == 1
  | _ => false

#guard shadowedBindingsStaySeparate

-- A LOCAL-ONLY property (its value reads its owner's parameter) keeps its
-- per-activation entry, and within ONE activation a builtin slot shares it with
-- the direct read:
-- `Outer(x) = { P = Id(x); P, sum(P), max(P), if(true, P, 0), P.string }`.
def localOnlyOuterAlg : Algorithm :=
  alg ["x"] [] [
    privateLocalProp "P" (.localCapturedAncestorParams ["x"])
      (alg [] [] [] [.call (resolve "Id") [param "x"]])
  ] [resolve "P", .call (resolve "sum") [resolve "P"], .call (resolve "max") [resolve "P"],
     .call (resolve "if") [.boolLiteral true, resolve "P", num 0],
     .dotCall (resolve "P") "string" none]

def localOnlyActivations (calls : Nat) : Option (Nat × Nat) :=
  let root := algPrivate [] [] [("Id", cacheIdAlg), ("Outer", localOnlyOuterAlg)]
    ((List.range calls).map (fun i => .call (resolve "Outer") [num (Int.ofNat i)]))
  match runResultWithState (.algorithmExpr root) with
  | .ok (_, state) =>
      some (state.nextBindingContext - 1,
            (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "P")).length)
  | .error _ => none

-- One activation: the Outer call plus P's body once; one P entry.
#guard localOnlyActivations 1 == some (2, 1)
-- Two activations: two separate P entries, P's body once per activation.
#guard localOnlyActivations 2 == some (4, 2)

-- A consumer's own bindings never create another entry for the same local P.
def localBindingAcrossConsumers : Bool :=
  let outer := alg ["x"] [] [
    privateLocalProp "P" (.localCapturedAncestorParams ["x"])
      (alg [] [] [] [.call (resolve "Id") [param "x"]]),
    privateLocalProp "F" (.localCapturedAncestorParams ["x"])
      (alg ["y"] [] [] [resolve "P"])
  ] [resolve "P", .call (resolve "F") [num 0], .call (resolve "F") [num 0],
     .dotCall (resolve "Outer") "P" none,
     .call (resolve "map") [.listLiteral [num 1, num 2],
       .algorithmExpr (alg ["y"] [] [] [.binary .add (param "y") (resolve "P")])],
     .dotCall (resolve "P") "string" none]
  let root := algPrivate [] [] [("Id", cacheIdAlg), ("Outer", outer)]
    [.call (resolve "Outer") [num 7], .call (resolve "Outer") [num 7]]
  match runResultWithState (.algorithmExpr root) with
  | .ok (Result.sequenceValue [a, b], state) =>
      let expected := Result.sequenceValue [Result.atom 7, Result.atom 7, Result.atom 7,
        Result.atom 7, Result.listValue [Result.atom 8, Result.atom 9], Result.str "7"]
      a == expected && b == expected && state.nextBindingContext - 1 == 12 &&
        (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "P")).length == 2
  | _ => false

#guard localBindingAcrossConsumers

-- A parameterless declaring owner still has a fresh context on each explicit call.
-- Its nested consumer F must not split that context again.
def parameterlessLocalOwnerCalls : Bool :=
  let inner := alg [] [] [
    privateLocalProp "P" (.localCapturedAncestorParams ["x"])
      (alg [] [] [] [.call (resolve "Id") [param "x"]]),
    privateLocalProp "F" (.localCapturedAncestorParams ["x"])
      (alg ["y"] [] [] [resolve "P"])
  ] [resolve "P", .call (resolve "F") [num 0], resolve "P"]
  let outer := alg ["x"] [] [privateLocalProp "Inner" (.localCapturedAncestorParams ["x"]) inner]
    [.call (resolve "Inner") [], .call (resolve "Inner") []]
  let root := algPrivate [] [] [("Id", cacheIdAlg), ("Outer", outer)] [.call (resolve "Outer") [num 7]]
  match runResultWithState (.algorithmExpr root) with
  | .ok (_, state) => state.nextBindingContext - 1 == 7 &&
      (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "P")).length == 2
  | _ => false

#guard parameterlessLocalOwnerCalls

end KatLangTests
