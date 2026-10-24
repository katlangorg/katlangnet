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
-- a collection element all receive the value the property access produced (a
-- builtin's arguments are the call's ordinary need cells — `formNeedSupply` /
-- `supplyNeed` — whose VALUE demand, `demandNeed`, is that property read, and
-- the `.string` receiver reads through `evalDotStringReceiverValue`); none of
-- them can re-run the property's body.
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
#guard consumerReusesTheRead (.call (resolve "repeat") [.call (resolve "Keep") [resolve "A"], num 0]) 0
#guard consumerReusesTheRead (.call (resolve "repeat") [.call (resolve "Keep") [resolve "A"], num 1]) 1
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
#guard consumerReusesTheRead (.index (resolve "A") [num 0]) 0
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
-- Explicit invocation is fresh; it may establish, but never replaces, the entry
--------------------------------------------------------------------------------
-- `A()` is one call context plus A's body's own `Id` call. CACHE-PUB-1 (October 22
-- 2026): an explicit zero-supply invocation never READS the entry, but the owning one
-- of an EMPTY entry establishes it.

-- `A, A(), A`: the ordinary read stores; the explicit call runs afresh; the last
-- read reuses the FIRST entry.
#guard contextsOpened [resolve "A", .call (resolve "A") [], resolve "A"] == some 3
#guard entriesNamed "A" [resolve "A", .call (resolve "A") [], resolve "A"] == some 1
-- `A(), A, A`: the explicit call establishes the entry; both reads reuse it (formerly
-- the call stored nothing and the first read evaluated again: 3 contexts).
#guard contextsOpened [.call (resolve "A") [], resolve "A", resolve "A"] == some 2
#guard entriesNamed "A" [.call (resolve "A") [], resolve "A", resolve "A"] == some 1
-- `A(), A()`: two fresh evaluations; the first establishes the one entry (formerly none).
#guard contextsOpened [.call (resolve "A") [], .call (resolve "A") []] == some 4
#guard entriesNamed "A" [.call (resolve "A") [], .call (resolve "A") []] == some 1
-- An explicit call inside a builtin slot is still an explicit call.
#guard contextsOpened [resolve "A", .call (resolve "sum") [.call (resolve "A") []]] == some 3
-- Explicitly invoking a FORWARDED callable is an explicit call too: passing A to
-- `Call0` demands no VALUE (Model C, NEED-06), and `f()` runs A's body afresh;
-- the root read of A is the one cached read.
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

--------------------------------------------------------------------------------
-- Implicit lifting follows zero-argument acceptance (Q-03, September 2026)
--------------------------------------------------------------------------------
-- If a callable works with no arguments, its bare name reads its cached value,
-- even when it declares a collecting parameter; only a written call is fresh.
-- The surface pass lifts a bare value reference ONLY when its callee requires
-- supplied arguments (`liftsBareValueReference`, over the binder's own
-- `minimumSuppliedSlots`), so `Twice = Only + Only` with a collecting-only
-- `Only` elaborates to two BARE reads that ONE cached evaluation serves. The
-- superseded elaboration of the same source, `TwiceLifted(*xs) = Only(xs*) +
-- Only(xs*)`, ran Only's body twice and never touched its entry. Lean evaluates
-- whichever tree the surface pass produces; these guards show the two trees'
-- evaluation counts, which is exactly what Q-03 changed.

open KatLang (liftsBareValueReference isCacheableZeroArgPropertyAlgorithm)

-- The decision table: only a signature that REQUIRES a supplied slot lifts.
#guard liftsBareValueReference [] == false
#guard liftsBareValueReference [.capture { name := "xs", kind := .collecting }] == false
#guard liftsBareValueReference [.capture { name := "x" }] == true
#guard liftsBareValueReference
  [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }] == true
#guard liftsBareValueReference
  [.capture { name := "rest", kind := .collecting }, .capture { name := "z" }] == true
#guard liftsBareValueReference [.sequenceValue [.capture { name := "xs", kind := .collecting }]] == true

/-- `Only(*xs) = Id(7)`: each evaluation opens its own binding context (the empty
    supply it binds) plus `Id`'s. -/
def q03OnlyAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.call (resolve "Id") [num 7]]

/-- `Twice = Only + Only` as the surface pass elaborates it since Q-03: two bare reads. -/
def q03TwiceAlg : Algorithm := alg [] [] [] [.binary .add (resolve "Only") (resolve "Only")]

/-- The superseded elaboration of that same `Twice`: `TwiceLifted(*xs) = Only(xs*) + Only(xs*)`. -/
def q03TwiceLiftedAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.binary .add (.call (resolve "Only") [.sequenceSpread (param "xs")])
                  (.call (resolve "Only") [.sequenceSpread (param "xs")])]

def q03Root (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", cacheIdAlg), ("Only", q03OnlyAlg), ("Twice", q03TwiceAlg)
    , ("TwiceLifted", q03TwiceLiftedAlg) ]
    out)

/-- A successful run's value, the binding contexts it opened, and its `Only` entries. -/
def q03Run (out : List KatLang.Expr) : Option (Result × Nat × Nat) :=
  match runResultWithState (q03Root out) with
  | .ok (value, state) =>
      some (value, state.nextBindingContext - 1,
            (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "Only")).length)
  | .error _ => none

-- `Only` accepts zero supplied arguments: the surface pass leaves its references
-- unlifted, and the zero-argument demand law sends them through the cache.
#guard liftsBareValueReference (Algorithm.parameterPatterns q03OnlyAlg) == false
#guard isCacheableZeroArgPropertyAlgorithm q03OnlyAlg
-- The Q-03 tree: 14 from ONE evaluation of Only (its binder and Id), one entry.
#guard q03Run [resolve "Twice"] == some (.atom 14, 2, 1)
-- The superseded tree: the same 14, but TwiceLifted's binder plus TWO fresh
-- evaluations of Only (binder and Id each). Each `Only(xs*)` spreads the EMPTY
-- collected list, so its effective supply is zero: the first is Only's owning
-- zero-supply invocation and establishes ONE entry (CACHE-PUB-1; formerly none).
#guard q03Run [resolve "TwiceLifted"] == some (.atom 14, 5, 1)
-- A bare read beside the formula shares that one evaluation.
#guard q03Run [resolve "Only", resolve "Twice"] == some (.sequenceValue [.atom 7, .atom 14], 2, 1)
-- The explicit call stays fresh and leaves the established entry unchanged: `Only, Only(), Only`.
#guard q03Run [resolve "Only", .call (resolve "Only") [], resolve "Only"]
  == some (.sequenceValue [.atom 7, .atom 7, .atom 7], 4, 1)

--------------------------------------------------------------------------------
-- CACHE-OWNER-D2: every call boundary is a fresh binding context (October 2026)
--------------------------------------------------------------------------------
-- `EvalCtx.bindParameters` allocates a fresh `bindingContext` at EVERY binding
-- boundary, also one that binds no parameter and inherits no cell: a zero-supply
-- call of a parameterless owner made from the root (META `R.Algorithm()`) is its
-- own activation, so the owner's local-only `V` gets one entry per call and two
-- calls never share one. C# was corrected to this production behavior
-- (`Evaluator.BindingContextIdentity`, `MetaCallBindingContextTests`); these
-- guards pin it. The trees are `LeanAstEncoder` output of the C# elaboration of
-- the research witnesses (`experimental/features/cache-owner-f1-research.md`
-- § 2.3) with the effect-free `V = k * 1`, so ENTRY COUNTS witness the contexts.

section CacheOwnerD2
open KatLang

/-- `Capture(meta op) = op`. -/
def d2Capture : PropDef :=
  privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"])

/-- `F(k) = { B = { V = k * 1 ⏎ V } ⏎ Capture(B()) }`: `B` is a parameterless owner whose
    local-only `V` reads `F`'s parameter. -/
def d2F : PropDef :=
  privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.call (.resolve "Capture") [(.call (.resolve "B") [])])])

/-- `R1 = F(3)` / `R2 = F(4)` beside `extra`, `Capture` and `F`, with the root rows `rows`;
    the run's value and how many cache entries `name` has. -/
def d2Run (owner : PropDef) (extra : List PropDef) (rows : List Expr) (name : Ident) : Option (Result × Nat) :=
  let root := alg [] []
    ([privateProp "R1" (alg [] [] [] [(.call (.resolve owner.name) [.num 3])]),
      privateProp "R2" (alg [] [] [] [(.call (.resolve owner.name) [.num 4])])] ++ extra ++ [d2Capture, owner])
    rows
  match runResultWithState (.algorithmExpr root) with
  | .ok (value, state) =>
      some (value, (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == name)).length)
  | .error _ => none

def d2Call (receiver : Ident) : Expr := .dotCall (.resolve receiver) "Algorithm" (some [])

-- D2-PV1: two projected zero-supply calls are two activations, two `V` entries.
#guard d2Run d2F [] [d2Call "R1", d2Call "R2"] "V" == some (.sequenceValue [.atom 3, .atom 4], 2)
-- D2-PV4: the order-reversed variant.
#guard d2Run d2F [] [d2Call "R2", d2Call "R1"] "V" == some (.sequenceValue [.atom 4, .atom 3], 2)
-- D2-PV3: combined in a root property, `304` (never `303`).
#guard d2Run d2F
    [privateProp "X" (alg [] [] [] [(.binary .add (.binary .mul (d2Call "R1") (.num 100)) (d2Call "R2"))])]
    [.resolve "X"] "V" == some (.atom 304, 2)
-- Explicit-call freshness: a second call of the SAME captured activation is a third
-- context, and its parenthesized spelling is the same ordinary call.
#guard d2Run d2F [] [d2Call "R1", d2Call "R2", d2Call "R1"] "V"
  == some (.sequenceValue [.atom 3, .atom 4, .atom 3], 3)
#guard d2Run d2F [] [.call (.dotCall (.resolve "R1") "Algorithm" none) [],
    .call (.dotCall (.resolve "R2") "Algorithm" none) [], .call (.dotCall (.resolve "R1") "Algorithm" none) []] "V"
  == some (.sequenceValue [.atom 3, .atom 4, .atom 3], 3)
-- Controls: `R.Invoke()` replays each captured invocation; the bare projection demands
-- the callable's value.
#guard d2Run d2F [] [.dotCall (.resolve "R1") "Invoke" (some []), .dotCall (.resolve "R2") "Invoke" (some [])] "V"
  == some (.sequenceValue [.atom 3, .atom 4], 2)
#guard d2Run d2F [] [.dotCall (.resolve "R1") "Algorithm" none, .dotCall (.resolve "R2") "Algorithm" none] "V"
  == some (.sequenceValue [.atom 3, .atom 4], 2)
-- A runtime-target alias of a ZERO-PARAMETER callee is its ordinary property (META-S3-2 D4,
-- FWD-02): `A1(), A2(), A1()` leaves TWO `V` entries for three calls. Each `A1()` evaluates
-- the terminal row afresh; the row's bare `R1.Algorithm` is the VALUE of R1's plan callee
-- cell (CR-13/CR-14b), completed once per plan, so the second `A1()` reads that completed
-- VALUE — not a `V` held by A1's binding cell (`AliasD4` below pins the state).
#guard d2Run d2F [privateProp "A1" (.alias none [] [] (.dotCall (.resolve "R1") "Algorithm" none)),
    privateProp "A2" (.alias none [] [] (.dotCall (.resolve "R2") "Algorithm" none))]
    [.call (.resolve "A1") [], .call (.resolve "A2") [], .call (.resolve "A1") []] "V"
  == some (.sequenceValue [.atom 3, .atom 4, .atom 3], 2)

/-! ALIAS-D4 (`experimental/features/alias-d4-1-research.md`): the run state behind a
    zero-parameter runtime alias. `d4Observe` reports the value, the `V`/`B`/alias entry
    counts, the need-cell and alias-cell counts, the binding contexts opened, and whether
    every recorded CR-13 callee cell completed with a VALUE. The trees are the D2 ones; `H`
    and `AM` are hand-encoded like the front end classifies them (`r` is a captured
    ancestor parameter of `A`). Entry counts alone cannot tell a cache HIT from no request;
    the request-level evidence is the C# `MetaCallBindingContextTests` § 5 cache-seam guard. -/

/-- `A1 = R1.Algorithm`. -/
def d4A1 : PropDef := privateProp "A1" (.alias none [] [] (.dotCall (.resolve "R1") "Algorithm" none))

/-- `AM = F(3).Algorithm`: a terminal row with a COMPUTED receiver. -/
def d4AM : PropDef := privateProp "AM" (.alias none [] [] (.dotCall (.call (.resolve "F") [.num 3]) "Algorithm" none))

/-- `H(r) = { A = r.Algorithm ⏎ A() * 100 + A() }`: a new alias in every activation. -/
def d4H : PropDef := privateProp "H" (alg ["r"] []
  [{ (privateLocalProp "A" (.localCapturedAncestorParams ["r"]) (.alias none [] [] (.dotCall (.param "r") "Algorithm" none)))
      with requiredOwnerDepths := some [("r", some 0)] }]
  [.binary .add (.binary .mul (.call (.resolve "A") []) (.num 100)) (.call (.resolve "A") [])])

structure D4Observation where
  value : Result
  v : Nat
  b : Nat
  aliasEntries : Nat
  needs : Nat
  aliasCells : Nat
  contexts : Nat
  calleesCompleted : List Bool
  deriving BEq

def d4Count (state : EvalState) (name : Ident) : Nat :=
  (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == name)).length

def d4Observe (extra : List PropDef) (aliasName : Ident) (rows : List Expr) : Option D4Observation :=
  let root := alg [] []
    ([privateProp "R1" (alg [] [] [] [(.call (.resolve "F") [.num 3])]),
      privateProp "R2" (alg [] [] [] [(.call (.resolve "F") [.num 4])])] ++ extra ++ [d2Capture, d2F])
    rows
  match runResultWithState (.algorithmExpr root) with
  | .ok (value, state) =>
      let callees := (state.needs.toList.filterMap (·.callee)).eraseDups
      some { value, v := d4Count state "V", b := d4Count state "B", aliasEntries := d4Count state aliasName,
             needs := state.needs.size, aliasCells := state.aliasCells.length,
             contexts := state.nextBindingContext,
             calleesCompleted := callees.map fun n =>
               match (state.needs[n]?).map (·.state) with | some (.completed (.ok _)) => true | _ => false }
  | .error _ => none

def d4Calls (name : Ident) (n : Nat) : List Expr := List.replicate n (.call (.resolve name) [])

-- After the first `A1()` completes R1's plan callee VALUE, every later `A1()` adds NO `V`,
-- `B` or alias entry, no need cell and no alias cell, and leaves the one callee cell
-- completed; it opens exactly one binding context, the terminal row's own (a fresh
-- `R1.Algorithm()` would also give `V` a new entry, as the D2 guards above show).
#guard d4Observe [d4A1] "A1" (d4Calls "A1" 1)
  == some { value := .atom 3, v := 1, b := 1, aliasEntries := 1, needs := 6, aliasCells := 1, contexts := 4, calleesCompleted := [true] }
#guard d4Observe [d4A1] "A1" (d4Calls "A1" 2)
  == some { value := .sequenceValue [.atom 3, .atom 3], v := 1, b := 1, aliasEntries := 1, needs := 6, aliasCells := 1, contexts := 5, calleesCompleted := [true] }
#guard d4Observe [d4A1] "A1" (d4Calls "A1" 3)
  == some { value := .sequenceValue [.atom 3, .atom 3, .atom 3], v := 1, b := 1, aliasEntries := 1, needs := 6, aliasCells := 1, contexts := 6, calleesCompleted := [true] }
-- M06: three `H` activations make three alias cells and three `A` entries, but sharing
-- follows the PLAN: two callee cells (R1's, R2's), two `V`/`B` entries.
#guard d4Observe [d4H] "A" [.call (.resolve "H") [.resolve "R1"], .call (.resolve "H") [.resolve "R1"], .call (.resolve "H") [.resolve "R2"]]
  == some { value := .sequenceValue [.atom 303, .atom 303, .atom 404], v := 2, b := 2, aliasEntries := 3, needs := 14, aliasCells := 3, contexts := 14, calleesCompleted := [true, true] }
-- M27: a computed receiver re-runs `F(3)` in the second `AM()`'s fresh row: a second plan
-- with its own completed callee cell and its own `V`/`B` entries; the bare `AM` reads AM's
-- one published entry.
#guard d4Observe [d4AM] "AM" [.call (.resolve "AM") [], .call (.resolve "AM") [], .resolve "AM"]
  == some { value := .sequenceValue [.atom 3, .atom 3, .atom 3], v := 2, b := 2, aliasEntries := 1, needs := 10, aliasCells := 1, contexts := 7, calleesCompleted := [true, true] }

/-- D2-PV6: `G(k) = { F(0) = { V = k * 1 ⏎ V } ⏎ F(x) = 0 ⏎ Capture(F(0)) }`, a literal-only clause
    branch that binds nothing. -/
def d2G : PropDef :=
  privateProp "G" (alg ["k"] [] [{ (privateLocalProp "F" (.localCapturedAncestorParams ["k"]) (.conditional none [] [⟨.litInt 0, (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 2)] }] [.resolve "V"])⟩, ⟨.bind "x", (alg [] [] [] [.num 0])⟩])) with requiredOwnerDepths := some [("k", some 0)] }] [(.call (.resolve "Capture") [(.call (.resolve "F") [.num 0])])])

#guard d2Run d2G [] [.dotCall (.resolve "R1") "Algorithm" (some [.num 0]), .dotCall (.resolve "R2") "Algorithm" (some [.num 0])] "V"
  == some (.sequenceValue [.atom 3, .atom 4], 2)

/-- `F(k) = { B = { a, b = (k * 1, 1) ⏎ a + b + a } ⏎ Capture(B()) }`: one deconstruction source
    per activation, shared by its targets. -/
def d2Decon : PropDef :=
  privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "$deconstruct$0" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.capture [(.binary .mul (.param "k") (.num 1)), .num 1])])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "a" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "b" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.binary .add (.resolve "a") (.resolve "b")) (.resolve "a"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.call (.resolve "Capture") [(.call (.resolve "B") [])])])

#guard d2Run d2Decon [] [d2Call "R1", d2Call "R2"] "$deconstruct$0"
  == some (.sequenceValue [.atom 7, .atom 9], 2)

/-- `F(k) = { B = { E = 100 ⏎ E + k } ⏎ Capture(B()) }`: `E` reads no captured parameter. -/
def d2Exported : PropDef :=
  privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [privateProp "E" (alg [] [] [] [.num 100])] [(.binary .add (.resolve "E") (.param "k"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.call (.resolve "Capture") [(.call (.resolve "B") [])])])

-- An exported property keeps ONE run-wide entry across the three activations.
#guard d2Run d2Exported [] [d2Call "R1", d2Call "R2", d2Call "R1"] "E"
  == some (.sequenceValue [.atom 103, .atom 104, .atom 103], 1)

end CacheOwnerD2

--------------------------------------------------------------------------------
-- CACHE-OWNER-D1: a property read inherits the declaring context (October 2026)
--------------------------------------------------------------------------------
-- A parameterless owner `B` entered by a PROPERTY-STYLE read records the binding
-- context of its declaring activation (`EvalBody.evalPropertyDemandCounted`,
-- `enterPropertyOwnerBody`), never the consumer's: whichever consumer reads `B`
-- first — a callback, a helper call, a loop step — its local-only `V` is keyed on
-- `F`'s activation, the key a structural `B.V` and an opened `V` compute too. Before
-- the correction `V` was published once per consumer context (the research
-- witness R8 left two `V` entries with binding contexts 2 and 1). An explicit `B()`
-- still binds a fresh context. The trees are `LeanAstEncoder` output of the C#
-- elaboration of the research programs (`experimental/features/cache-owner-f1-research.md`
-- § 2.2) with effect-free bodies, so ENTRY COUNTS witness the evaluations; the C#
-- twins with effects are `ParameterlessOwnerEntryContextTests`.

section CacheOwnerD1
open KatLang

/-- The run's value, the cache entries `name` has, and the binding contexts it opened. -/
def d1Run (program : Expr) (name : Ident) : Option (Result × Nat × Nat) :=
  match runResultWithState program with
  | .ok (value, state) =>
      some (value, (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == name)).length,
        state.nextBindingContext - 1)
  | .error _ => none

/-- MIN: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ [0].map{ n + B }[0] + B.V ⏎ } ⏎ F(3)` -/
def d1MIN : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

/-- SWAP: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ B.V + [0].map{ n + B }[0] ⏎ } ⏎ F(3)` -/
def d1SWAP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.dotCall (.resolve "B") "V" none) (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]))])] [(.call (.resolve "F") [.num 3])])

/-- PRE: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ B + [0].map{ n + B }[0] + B.V ⏎ } ⏎ F(3)` -/
def d1PRE : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.resolve "B") (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0])) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

/-- OPEN: `F(k) = { ⏎ open B ⏎ B = { ⏎ public V = k * k ⏎ V + 1 ⏎ } ⏎ [1, 2].map{ n + B }[0] + V ⏎ } ⏎ F(3)` -/
def d1OPEN : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [.resolve "B"] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (publicLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.param "k"))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.resolve "V"))])] [(.call (.resolve "F") [.num 3])])

/-- HELP: `F(k) = { ⏎ B = { ⏎ V = k * k ⏎ V + 1 ⏎ } ⏎ G(x) = x + B ⏎ G(1) + B.V ⏎ } ⏎ F(3)` -/
def d1HELP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.param "k"))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["k"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.resolve "B"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.call (.resolve "G") [.num 1]) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

/-- DECON: `F(k) = { ⏎ B = { ⏎ a, b = k * 1, k + 1 ⏎ a + b ⏎ } ⏎ [1, 2].map{ n + B }[0] + B.a + B.b ⏎ } ⏎ F(3)` -/
def d1DECON : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "$deconstruct$0" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1)), (.binary .add (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "a" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "b" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "a") (.resolve "b"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.dotCall (.resolve "B") "a" none)) (.dotCall (.resolve "B") "b" none))])] [(.call (.resolve "F") [.num 3])])

/-- LOOP: `F(k) = { ⏎ B = { ⏎ V = k * k ⏎ V + 1 ⏎ } ⏎ Step(s) = s + B, s < 5 ⏎ Step(0).while + B.V ⏎ } ⏎ F(3)` -/
def d1LOOP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.param "k"))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }, { (privateLocalProp "Step" (.localCapturedAncestorParams ["k"]) (alg ["s"] [] [] [(.binary .add (.param "s") (.resolve "B")), (.comparison (.param "s") [{ op := .lt, operand := (.num 5) }])])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.dotCall (.call (.resolve "Step") [.num 0]) "while" none) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

/-- ANON: `[3].map{ ⏎ B = { ⏎ V = n * n ⏎ V + 1 ⏎ } ⏎ n * 0 + [1, 2].map{ m + B }[0] + B.V ⏎ }` -/
def d1ANON : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.num 3]) "map" (some [(.algorithmExpr (alg ["n"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["n"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [(.binary .mul (.param "n") (.param "n"))])) with requiredOwnerDepths := some [("n", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.binary .add (.binary .add (.binary .mul (.param "n") (.num 0)) (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["m"] [] [] [(.binary .add (.param "m") (.resolve "B"))]))])) [.num 0])) (.dotCall (.resolve "B") "V" none))]))]))])

/-- X3: `F(k) = { ⏎ B = { ⏎ C = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ C ⏎ } ⏎ [0].map{ n + B }[0] + [0].map{ n + B.C }[0] + B.C.V ⏎ } ⏎ F(3)` -/
def d1X3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "C" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 2)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "C"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.dotCall (.resolve "B") "C" none))]))])) [.num 0])) (.dotCall (.dotCall (.resolve "B") "C" none) "V" none))])] [(.call (.resolve "F") [.num 3])])

/-- PUB: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V + 1 ⏎ } ⏎ B.V() + [1].map{ n * 0 + B }[0] ⏎ } ⏎ F(3)` -/
def d1PUB : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.dotCall (.resolve "B") "V" (some [])) (.index (.dotCall (.listLiteral [.num 1]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.binary .mul (.param "n") (.num 0)) (.resolve "B"))]))])) [.num 0]))])] [(.call (.resolve "F") [.num 3])])

/-- ROOT: `B = { ⏎ V = 7 * 1 ⏎ V + 1 ⏎ } ⏎ [1, 2].map{ n + B }[0] + B.V` -/
def d1ROOT : Expr :=
  .algorithmExpr (alg [] [] [privateProp "B" (alg [] [] [privateProp "V" (alg [] [] [] [(.binary .mul (.num 7) (.num 1))])] [(.binary .add (.resolve "V") (.num 1))])] [(.binary .add (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.dotCall (.resolve "B") "V" none))])

/-- TWO: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ [0].map{ n + B }[0] + B.V ⏎ } ⏎ F(3), F(3)` -/
def d1TWO : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3]), (.call (.resolve "F") [.num 3])])

/-- CALLS: `F(k) = { ⏎ B = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ B() + B() + [0].map{ n + B }[0] + B.V ⏎ } ⏎ F(3)` -/
def d1CALLS : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.binary .add (.call (.resolve "B") []) (.call (.resolve "B") [])) (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0])) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

-- D1-MIN / D1-SWAP: B first read in a callback, then B.V (either order): ONE `V` entry.
#guard d1Run d1MIN "V" == some (.atom 6, 1, 2)
#guard d1Run d1SWAP "V" == some (.atom 6, 1, 2)
-- D1-PRE (control): B first read from F's own body.
#guard d1Run d1PRE "V" == some (.atom 9, 1, 2)
-- D1-OPEN / D1-HELP / D1-LOOP: the opened spelling, a helper call and a `while` step share it.
#guard d1Run d1OPEN "V" == some (.atom 20, 1, 3)
#guard d1Run d1HELP "V" == some (.atom 20, 1, 2)
#guard d1Run d1LOOP "V" == some (.atom 19, 1, 3)
-- D1-DECON: one shared right-hand side for the callback's B and the structural B.a, B.b.
#guard d1Run d1DECON "$deconstruct$0" == some (.atom 15, 1, 5)
-- D1-ANON: the declaring owner is itself an anonymous callback.
#guard d1Run d1ANON "V" == some (.listValue [.atom 20], 1, 3)
-- D1-3X: B in callback 1, B.C in callback 2, B.C.V from F: one entry (formerly three).
#guard d1Run d1X3 "V" == some (.atom 9, 1, 3)
#guard d1Run d1X3 "C" == some (.atom 9, 1, 3)
-- D1-PUB: `B.V()` establishes the entry (CACHE-PUB-1); the callback's B reuses it.
#guard d1Run d1PUB "V" == some (.atom 7, 1, 3)
-- D1-ROOT (control): no enclosing activation; V is exported.
#guard d1Run d1ROOT "V" == some (.atom 16, 1, 2)
-- Two activations of F with EQUAL arguments stay two entries.
#guard d1Run d1TWO "V" == some (.sequenceValue [.atom 6, .atom 6], 2, 4)
-- Explicit calls stay fresh: `B(), B()` are two contexts of their own, F's reads a third entry.
#guard d1Run d1CALLS "V" == some (.atom 12, 3, 4)

/-! The model has no host effects. Like `PropertyCachePublication`, the following VALUE witnesses
    deliberately use a hand-built tree whose V reads an unowned `d` dynamically from its consumer.
    F owns k, B and V capture k, but V does NOT own d: a split key observes the second consumer's
    different d (or a missing binding). This is evaluator evidence, not a surface-language example. -/
def d1DynamicValue (value : Expr) (rows : List Expr) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] []
    [privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] []
      [privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [value])]
      [resolve "V"]),
     privateLocalProp "G" (.localCapturedAncestorParams ["k"]) (alg ["d"] [] []
       [.index (.dotCall (.listLiteral [num 0]) "map" (some
         [.algorithmExpr (alg ["n"] [] [] [.binary .add (param "n") (resolve "B")])])) [num 0]]),
     privateLocalProp "H" (.localCapturedAncestorParams ["k"]) (alg ["d"] [] []
       [.dotCall (resolve "B") "V" none])]
    rows)] [.call (resolve "F") [num 3]])

-- D1-VAL: G(100) first reads B in a callback; H(1000) reads B.V. ONE numerical value (103),
-- so equality is true. Before D1 the second read computed 1003 and equality was false.
#guard (d1Run (d1DynamicValue (.binary .add (param "k") (param "d"))
    [.compare .eq (.call (resolve "G") [num 100]) (.call (resolve "H") [num 1000])]) "V").map
  (fun (value, entries, _) => (value, entries)) == some (.bool true, 1)

-- Q-37 through the D1 routes: G(2)'s callback owns V; the two recursive H reads are re-entrant.
-- Only the OUTER result 5 is published. H(99) must reuse 5, not an inner 3 or a new computation.
def d1ReentrantValue : Expr :=
  .call (resolve "if") [.compare .eq (param "d") (num 0), param "k",
    .binary .add (.call (resolve "H") [.binary .sub (param "d") (num 1)]) (num 1)]
#guard (d1Run (d1DynamicValue d1ReentrantValue
    [.call (resolve "G") [num 2], .call (resolve "H") [num 99]]) "V").map
  (fun (value, entries, _) => (value, entries)) == some (.sequenceValue [.atom 5, .atom 5], 1)

end CacheOwnerD1

--------------------------------------------------------------------------------
-- COLLECT-CACHE-1: a READ of a collecting-only owner inherits the declaring context
--------------------------------------------------------------------------------
-- `Only(*xs)` accepts zero supplied arguments, so a bare `Only` is a PROPERTY-STYLE
-- READ (it uses the zero-argument property cache). CACHE-OWNER-D1 covered owners with
-- no pattern; a collecting-only owner fell through to the ordinary zero-supply demand,
-- whose binder recorded the FRESH bound context on `Only`'s activation, so its
-- local-only `V` was published once under that context and once under `F`'s (the key a
-- structural `Only.V` computes): before the correction CMIN left `V@3, V@1`, CDIRECT
-- `V@2, V@1`, CTWO four `V` entries. `EvalBody.evalPropertyDemandCounted` now binds the
-- empty supply through the ordinary binder and enters the body with the declaring
-- activation's context recorded (`enterPropertyOwnerBody`). The empty collector is still
-- bound (`xs` is `[]`, shadowing an outer `xs`) and an explicit `Only()` is still a
-- fresh context. Trees: `LeanAstEncoder` output of the C# elaboration (effect-free
-- bodies, so ENTRY COUNTS witness evaluations); the C# twins with effects are
-- `CollectingPropertyOwnerContextTests`. An opened collecting owner is not valid source
-- (`open` refuses an algorithm that requires arguments), so there is no OPEN case.

section CollectCache1
open KatLang

/-- CMIN: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ [0].map{ n + Only }[0] + Only.V ⏎ } ⏎ F(3)` -/
def ccCMIN : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0]) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CSWAP: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ Only.V + [0].map{ n + Only }[0] ⏎ } ⏎ F(3)` -/
def ccCSWAP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.dotCall (.resolve "Only") "V" none) (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0]))])] [(.call (.resolve "F") [.num 3])])
/-- CDIRECT: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ Only + Only.V ⏎ } ⏎ F(3)` -/
def ccCDIRECT : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.resolve "Only") (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CPRE: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ Only + [0].map{ n + Only }[0] + Only.V ⏎ } ⏎ F(3)` -/
def ccCPRE : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.resolve "Only") (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0])) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CTWO: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ [0].map{ n + Only }[0] + Only.V ⏎ } ⏎ F(3), F(3)` -/
def ccCTWO : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0]) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3]), (.call (.resolve "F") [.num 3])])
/-- CCALLS: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ Only() + Only() + [0].map{ n + Only }[0] + Only.V ⏎ } ⏎ F(3)` -/
def ccCCALLS : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.binary .add (.call (.resolve "Only") []) (.call (.resolve "Only") [])) (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0])) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CPUB: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V ⏎ } ⏎ Only() + Only + Only() + Only + Only.V ⏎ } ⏎ F(3)` -/
def ccCPUB : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.binary .add (.binary .add (.call (.resolve "Only") []) (.resolve "Only")) (.call (.resolve "Only") [])) (.resolve "Only")) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CXS: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V, xs ⏎ } ⏎ [0].map{ n * 0 + Only.V }[0], Only, Only.V ⏎ } ⏎ F(3)` -/
def ccCXS : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V", .param "xs"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.binary .mul (.param "n") (.num 0)) (.dotCall (.resolve "Only") "V" none))]))])) [.num 0]), .resolve "Only", (.dotCall (.resolve "Only") "V" none)])] [(.call (.resolve "F") [.num 3])])
/-- CSHADOW: `F(k, xs) = { ⏎ Only(*xs) = { ⏎ V = k * 1 ⏎ V, xs ⏎ } ⏎ Only, xs ⏎ } ⏎ F(3, 9)` -/
def ccCSHADOW : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k", "xs"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V", .param "xs"])) with requiredOwnerDepths := some [("k", some 0)] }] [.resolve "Only", .param "xs"])] [(.call (.resolve "F") [.num 3, .num 9])])
/-- CHELP: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * k ⏎ V + 1 ⏎ } ⏎ G(x) = x + Only ⏎ G(1) + Only.V ⏎ } ⏎ F(3)` -/
def ccCHELP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.param "k"))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }, { (privateLocalProp "G" (.localCapturedAncestorParams ["k"]) (alg ["x"] [] [] [(.binary .add (.param "x") (.resolve "Only"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.call (.resolve "G") [.num 1]) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CLOOP: `F(k) = { ⏎ Only(*xs) = { ⏎ V = k * k ⏎ V + 1 ⏎ } ⏎ Step(s) = s + Only, s < 5 ⏎ Step(0).while + Only.V ⏎ } ⏎ F(3)` -/
def ccCLOOP : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.param "k"))])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "V") (.num 1))])) with requiredOwnerDepths := some [("k", some 0)] }, { (privateLocalProp "Step" (.localCapturedAncestorParams ["k"]) (alg ["s"] [] [] [(.binary .add (.param "s") (.resolve "Only")), (.comparison (.param "s") [{ op := .lt, operand := (.num 5) }])])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.dotCall (.call (.resolve "Step") [.num 0]) "while" none) (.dotCall (.resolve "Only") "V" none))])] [(.call (.resolve "F") [.num 3])])
/-- CDECON: `F(k) = { ⏎ Only(*xs) = { ⏎ a, b = k * 1, k + 1 ⏎ a + b ⏎ } ⏎ [1, 2].map{ n + Only }[0] + Only.a + Only.b ⏎ } ⏎ F(3)` -/
def ccCDECON : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "Only" (.localCapturedAncestorParams ["k"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [{ (privateLocalProp "$deconstruct$0" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1)), (.binary .add (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "a" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }, { (privateLocalProp "b" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("k", some 1)] }] [(.binary .add (.resolve "a") (.resolve "b"))])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.binary .add (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0]) (.dotCall (.resolve "Only") "a" none)) (.dotCall (.resolve "Only") "b" none))])] [(.call (.resolve "F") [.num 3])])
/-- CROOT: `Only(*xs) = { ⏎ V = 7 * 1 ⏎ V + 1 ⏎ } ⏎ [1, 2].map{ n + Only }[0] + Only.V` -/
def ccCROOT : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [privateProp "V" (alg [] [] [] [(.binary .mul (.num 7) (.num 1))])] [(.binary .add (.resolve "V") (.num 1))])] [(.binary .add (.index (.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "Only"))]))])) [.num 0]) (.dotCall (.resolve "Only") "V" none))])
def ccBCTRL : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["k"]) (alg [] [] [{ (privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [(.binary .mul (.param "k") (.num 1))])) with requiredOwnerDepths := some [("k", some 1)] }] [.resolve "V"])) with requiredOwnerDepths := some [("k", some 0)] }] [(.binary .add (.index (.dotCall (.listLiteral [.num 0]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .add (.param "n") (.resolve "B"))]))])) [.num 0]) (.dotCall (.resolve "B") "V" none))])] [(.call (.resolve "F") [.num 3])])

-- CMIN / CSWAP: Only first read in a callback, then Only.V (either order): ONE `V` entry.
#guard d1Run ccCMIN "V" == some (.atom 6, 1, 3)
#guard d1Run ccCSWAP "V" == some (.atom 6, 1, 3)
-- CDIRECT / CPRE: a read from F's own body and the structural Only.V share it too.
#guard d1Run ccCDIRECT "V" == some (.atom 6, 1, 2)
#guard d1Run ccCPRE "V" == some (.atom 9, 1, 3)
-- CHELP / CLOOP: a helper call and a `while` step share the declaring activation's entry.
#guard d1Run ccCHELP "V" == some (.atom 20, 1, 3)
#guard d1Run ccCLOOP "V" == some (.atom 19, 1, 4)
-- CDECON: one shared right-hand side for the callback's Only and the structural Only.a, Only.b.
#guard d1Run ccCDECON "$deconstruct$0" == some (.atom 15, 1, 6)
-- CXS: the bare read still binds the EXACT empty list; V is shared by every route.
#guard d1Run ccCXS "V" == some (.sequenceValue [.atom 3, .sequenceValue [.atom 3, .listValue []], .atom 3], 1, 3)
-- CSHADOW: the collector shadows F's own `xs` (9) inside Only.
#guard d1Run ccCSHADOW "V" == some (.sequenceValue [.sequenceValue [.atom 3, .listValue []], .atom 9], 1, 2)
-- CTWO: two activations of F with EQUAL arguments stay two entries.
#guard d1Run ccCTWO "V" == some (.sequenceValue [.atom 6, .atom 6], 2, 6)
-- CCALLS: explicit `Only(), Only()` are two fresh contexts; the read and Only.V share a third.
#guard d1Run ccCCALLS "V" == some (.atom 12, 3, 4)
-- CPUB: the first `Only()` establishes Only's entry (CACHE-PUB-1) with its OWN locals; the bare
-- reads reuse that entry, the second `Only()` is fresh, and Only.V is F's entry.
#guard d1Run ccCPUB "V" == some (.atom 15, 3, 3)
#guard d1Run ccCPUB "Only" == some (.atom 15, 1, 3)
-- CROOT (control): no enclosing activation; V is exported.
#guard d1Run ccCROOT "V" == some (.atom 16, 1, 3)

/-! The VALUE witnesses of the D1 section, with the owner `Only(*xs)` collecting: V reads an unowned
    `d` dynamically from its consumer (a hand-built evaluator witness, not a surface example). -/
def ccDynamicValue (value : Expr) (rows : List Expr) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["k"] []
    [privateLocalProp "Only" (.localCapturedAncestorParams ["k"])
      (algWithParameters [{ name := "xs", kind := .collecting }] []
        [privateLocalProp "V" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [value])]
        [resolve "V"]),
     privateLocalProp "G" (.localCapturedAncestorParams ["k"]) (alg ["d"] [] []
       [.index (.dotCall (.listLiteral [num 0]) "map" (some
         [.algorithmExpr (alg ["n"] [] [] [.binary .add (param "n") (resolve "Only")])])) [num 0]]),
     privateLocalProp "H" (.localCapturedAncestorParams ["k"]) (alg ["d"] [] []
       [.dotCall (resolve "Only") "V" none])]
    rows)] [.call (resolve "F") [num 3]])

-- COLLECT-VAL: G(100) reads Only in a callback, H(1000) reads Only.V: ONE value (103), equality true.
#guard (d1Run (ccDynamicValue (.binary .add (param "k") (param "d"))
    [.compare .eq (.call (resolve "G") [num 100]) (.call (resolve "H") [num 1000])]) "V").map
  (fun (value, entries, _) => (value, entries)) == some (.bool true, 1)

-- Q-37 through the collecting READ: only the OUTER result 5 is published and H(99) reuses it.
#guard (d1Run (ccDynamicValue d1ReentrantValue
    [.call (resolve "G") [num 2], .call (resolve "H") [num 99]]) "V").map
  (fun (value, entries, _) => (value, entries)) == some (.sequenceValue [.atom 5, .atom 5], 1)

end CollectCache1

end KatLangTests
