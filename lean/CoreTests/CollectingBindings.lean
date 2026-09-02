import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Collecting bindings collect exact immutable lists (collectSegment)
--------------------------------------------------------------------------------
-- Required matrix for the collect model: capture / collect / open are distinct
-- operations. C# parity: tests/KatLang.Tests/DeconstructionBindingTests.cs and
-- EvaluatorTests variadic sections; binder laws: KatLangArityLaws.lean.

-- Parser-elaborated deconstruction helper: `targets = RHS` binds through an
-- inline sequence-value parameter pattern over the shared RHS value.
def collectDeconHelper (targets : List KatLang.ParameterPattern) (observed : String)
    : KatLang.Expr :=
  .algorithmExpr (algWithParameterPatterns [.sequenceValue targets] [] [] [.param observed])

def collectFix (name : String) : KatLang.ParameterPattern :=
  .capture { name := name }

def collectVar (name : String) : KatLang.ParameterPattern :=
  .capture { name := name, kind := .collecting }

def runCollectDecon (targets : List KatLang.ParameterPattern) (observed : String)
    (rhs : List KatLang.Expr) : Except KatLang.Error Result :=
  -- Mirror parser elaboration: the RHS is evaluated once into a shared
  -- property, and the pattern helper opens that single shared value.
  runResult (.algorithmExpr (algPrivate [] [] [("sharedRhs", alg [] [] [] rhs)]
    [.call (collectDeconHelper targets observed) [resolve "sharedRhs"]]))

-- Empty, singleton, and multi-item collection: `head, *rest = [1] / [1, 2] / [1, 2, 3]`.
def deconCollectingCollectsEmptySingletonMultiple : Bool :=
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1]] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.atom 2]) => true | _ => false) &&
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false)

#guard deconCollectingCollectsEmptySingletonMultiple

-- Collecting-binding positions: leading `*rest, last` and middle `first, *middle, last`.
def deconCollectingPositionsCollectLists : Bool :=
  (match runCollectDecon [collectVar "rest", collectFix "last"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "middle", collectFix "last"] "middle"
      [.listLiteral [.num 1, .num 2, .num 3, .num 4]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "middle", collectFix "last"] "middle"
      [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard deconCollectingPositionsCollectLists

-- Structured singleton items are preserved exactly: a collected segment of one structured
-- item is a one-element list holding that structure, never the structure
-- itself, and zero items stay distinguishable from one empty structure.
def deconCollectingPreservesStructuredSingletons : Bool :=
  -- first, *rest = [[1, 2], [3, 4]]  =>  rest = [[3, 4]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false) &&
  -- first, *rest = 1, [2, 3]  =>  rest = [[2, 3]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .listLiteral [.num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- first, *rest = 1, (2, 3)  =>  rest = [(2, 3)]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .capture [.num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- first, *rest = 1, []  =>  rest = [[]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .listLiteral []] with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  -- first, *rest = 1, ()  =>  rest = [()]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .emptySequence 0] with
   | Except.ok (Result.listValue [Result.sequenceValue []]) => true | _ => false)

#guard deconCollectingPreservesStructuredSingletons

-- Deconstruction implicit opening agrees with explicit spread:
-- `first, *rest = [1, 2, 3]` and `first, *rest = [1, 2, 3]*`.
def deconCollectingImplicitOpeningMatchesSpread : Bool :=
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false)

#guard deconCollectingImplicitOpeningMatchesSpread

-- The receiver-level item-view law is not an unrestricted source rewrite:
-- a written deconstruction RHS spread first passes through the shared
-- property's ordinary capture boundary. Bare `x, y = [(1, 2)]` opens the
-- outer list once and has only one row for two targets (arity mismatch 2/1),
-- while `x, y = [(1, 2)]*` captures that one row as `(1, 2)` and the
-- deconstruction receiver then opens the row into `x = 1`, `y = 2`.
def deconSpreadCaptureCanOpenSingletonStructuredElementFurther : Bool :=
  (match runCollectDecon [collectFix "x", collectFix "y"] "x"
      [.listLiteral [.capture [.num 1, .num 2]]] with
   | Except.error err => innermostIsArityMismatch 2 1 err
   | _ => false) &&
  (match runCollectDecon [collectFix "x", collectFix "y"] "x"
      [.sequenceSpread (.listLiteral [.capture [.num 1, .num 2]])] with
   | Except.ok (Result.atom 1) => true
   | _ => false)

#guard deconSpreadCaptureCanOpenSingletonStructuredElementFurther

-- Provenance independence: `first, *rest = 1, [2, 3]*, (4, 5)*` collects
-- exactly the assembled item supply, regardless of the spread sources.
def deconCollectingProvenanceIndependent : Bool :=
  match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1,
       .sequenceSpread (.listLiteral [.num 2, .num 3]),
       .sequenceSpread (.capture [.num 4, .num 5])] with
  | Except.ok (Result.listValue [Result.atom 2, Result.atom 3, Result.atom 4, Result.atom 5]) =>
      true
  | _ => false

#guard deconCollectingProvenanceIndependent

def collectInspectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def runCollectInspect (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [("Inspect", collectInspectAlg)]
    [.call (resolve "Inspect") args]))

-- Variadic capture matrix: Inspect(*items) = items.
def variadicCaptureCollectsExactList : Bool :=
  (match runCollectInspect [] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectInspect [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runCollectInspect [.num 1, .num 2, .num 3] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  -- Inspect([1, 2]) => [[1, 2]]; Inspect([1, 2]*) => [1, 2]
  (match runCollectInspect [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.listLiteral [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  -- Inspect((1, 2)) => [(1, 2)]; Inspect((1, 2)*) => [1, 2]
  (match runCollectInspect [.capture [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.capture [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard variadicCaptureCollectsExactList

-- Empty-structure arguments: an unspread `()` or `[]` is ONE visible argument
-- slot (`Inspect(())` collects `[()]`, `Inspect([])` collects `[[]]`), while
-- the spreads contribute zero items (`Inspect(()*)` and `Inspect([]*)`
-- both collect `[]`) — zero-item-spread neutrality at the collect boundary.
def variadicCaptureEmptyStructureArguments : Bool :=
  (match runCollectInspect [.emptySequence 0] with
   | Except.ok (Result.listValue [Result.sequenceValue []]) => true | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.emptySequence 0)] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectInspect [.listLiteral []] with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.listLiteral [])] with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard variadicCaptureEmptyStructureArguments

-- Middle collecting parameter, direct user call: `Middle(first, *middle, last) = middle`.
-- A grouped middle argument stays ONE collected slot with its boundary
-- (`Middle(10, (20, 30), 40)` collects `[(20, 30)]`), while the explicit
-- spread supplies the operand's items (`Middle(10, (20, 30)*, 40)` collects
-- `[20, 30]`).
def collectMiddleAlg : Algorithm :=
  algWithParameters
    [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }]
    [] [] [.param "middle"]

def runCollectMiddle (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [("Middle", collectMiddleAlg)]
    [.call (resolve "Middle") args]))

def middleVariadicGroupedAndSpreadDirectCall : Bool :=
  (match runCollectMiddle
      [.num 10, .capture [.num 20, .num 30], .num 40] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 20, Result.atom 30]]) =>
       true
   | _ => false) &&
  (match runCollectMiddle
      [.num 10, .sequenceSpread (.capture [.num 20, .num 30]), .num 40] with
   | Except.ok (Result.listValue [Result.atom 20, Result.atom 30]) => true | _ => false)

#guard middleVariadicGroupedAndSpreadDirectCall

-- Variadic forwarding through ordinary list spread:
-- Target(*items) = items; Forward(*items) = Target(items*).
def collectTargetAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def collectForwardAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .call (resolve "Target") [sequenceSpread (.param "items")]
  ]

def runCollectForward (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] []
    [("Target", collectTargetAlg), ("Forward", collectForwardAlg)]
    [.call (resolve "Forward") args]))

def collectingForwardingRoundTripsExactList : Bool :=
  (match runCollectForward [] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectForward [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runCollectForward [.num 1, .num 2] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runCollectForward [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectForward [.sequenceSpread (.listLiteral [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard collectingForwardingRoundTripsExactList

-- Forwarding the collected list WITHOUT spread passes one list argument:
-- TargetOne(item) = item; ForwardAsOne(*items) = TargetOne(items).
def variadicForwardAsOnePassesWholeList : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("TargetOne", alg ["item"] [] [] [.param "item"]),
     ("ForwardAsOne", algWithParameters [{ name := "items", kind := .collecting }] [] [] [
       .call (resolve "TargetOne") [.param "items"]
     ])]
    [.call (resolve "ForwardAsOne") [.num 1, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard variadicForwardAsOnePassesWholeList

-- Receiver distinction: the call receiver preserves argument boundaries
-- (`Inspect(A)` is one collected element), while explicit spread supplies the
-- items — for lists and sequence values alike.
def variadicReceiverDistinctionObservable : Bool :=
  let inspect (arg : KatLang.Expr) : Except KatLang.Error Result :=
    runResult (.algorithmExpr (algPrivate [] []
      [("Inspect", collectInspectAlg),
       ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
       ("B", alg [] [] [] [.capture [.num 1, .num 2, .num 3]])]
      [.call (resolve "Inspect") [arg]]))
  (match inspect (resolve "A") with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]]) =>
       true
   | _ => false) &&
  (match inspect (sequenceSpread (resolve "A")) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  (match inspect (resolve "B") with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]]) =>
       true
   | _ => false) &&
  (match inspect (sequenceSpread (resolve "B")) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false)

#guard variadicReceiverDistinctionObservable

-- Dotted receiver injection: `A.Inspect` is `Inspect(A)` — the receiver is one
-- captured argument slot, so the collected list is `[[1, 2]]`.
def variadicDotReceiverCollectsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("Inspect", collectInspectAlg),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.dotCall (resolve "A") "Inspect" none])) with
  | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
  | _ => false

#guard variadicDotReceiverCollectsOneSlot

-- Equality: collected results are exact list values, unequal to sequence values
-- and to differently-nested lists.
def collectedSegmentEqualityIsKindExact : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [("Inspect", collectInspectAlg)] [
    .binary .eq (.call (resolve "Inspect") []) (.listLiteral []),
    .binary .eq (.call (resolve "Inspect") [.num 7]) (.listLiteral [.num 7]),
    .binary .eq (.call (resolve "Inspect") [.num 1, .num 2])
      (.listLiteral [.num 1, .num 2]),
    .binary .eq (.call (resolve "Inspect") [.listLiteral [.num 1, .num 2]])
      (.listLiteral [.listLiteral [.num 1, .num 2]]),
    .binary .eq (.call (resolve "Inspect") [.listLiteral [.num 1, .num 2]])
      (.listLiteral [.num 1, .num 2]),
    .binary .eq (.call (resolve "Inspect") [.num 1, .num 2])
      (.capture [.num 1, .num 2])
  ]))) [1, 1, 1, 1, 0, 0]

#guard collectedSegmentEqualityIsKindExact

-- Collection composition: a collected list built inside a helper body composes with the
-- fixed-collection builtins exactly like a builtin-produced list.
def collectedSegmentComposesWithCollectionBuiltins : Bool :=
  let tailAlg : Algorithm := alg ["source"] [] [] [
    .call (collectDeconHelper [collectFix "first", collectVar "rest"] "rest") [.param "source"]
  ]
  let rows : KatLang.Expr :=
    .listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]
  (match runResult (.algorithmExpr (algPrivate [] [] [("Tail", tailAlg)]
      [.call (resolve "Tail") [rows]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("Tail", tailAlg)]
      [.dotCall (.call (resolve "Tail") [rows]) "count" none])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  -- skip([[1, 2], [3, 4]], 1) agrees with the collected segment of the same source.
  (match runResult (.algorithmExpr (alg [] [] []
      [.call (resolve "skip") [rows, .num 1]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false)

#guard collectedSegmentComposesWithCollectionBuiltins

-- Scalar right-hand side: `first, *rest = 1` binds the empty list.
def deconCollectingScalarRhsCollectsEmptyList : Bool :=
  match runCollectDecon [collectFix "first", collectVar "rest"] "rest" [.num 1] with
  | Except.ok (Result.listValue []) => true
  | _ => false

#guard deconCollectingScalarRhsCollectsEmptyList

-- Ordinary capture is unchanged: `x = 1, 2, 3` captures a canonical sequence
-- value, and `x = [1, 2, 3]*` re-captures the spread items as a sequence —
-- capture and collect stay distinct operations.
def ordinaryCaptureStaysCanonicalSequence : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("x", alg [] [] [] [.num 1, .num 2, .num 3])] [resolve "x"])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("x", alg [] [] [] [.sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])])]
      [resolve "x"])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false)

#guard ordinaryCaptureStaysCanonicalSequence

--------------------------------------------------------------------------------
-- Flat callbacks with collecting parameters bind through the shared binder
--------------------------------------------------------------------------------
-- A flat callee with a top-level collecting parameter routes through
-- bindCountedCallbackParameterPatternList: the callback supply keeps the
-- flat-callback row convention (a lone under-supplied final argument opens
-- into its items), then the shared prefix/collecting/suffix binder COLLECTS the
-- matched segment as one exact immutable list. A single-collecting callee keeps the whole
-- iterated element as one collected slot.
-- C# parity: EvaluatorTests callback sections and CollectingBindingTests.

def callbackCollectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def runCallbackMap (props : List (String × Algorithm)) (collection : KatLang.Expr)
    (callbackName : String) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props
    [.call (resolve "map") [collection, resolve callbackName]]))

-- [7].map(Collect) => [[7]]; [7, 8].map(Collect) => [[7], [8]].
def restOnlyMapCallbackCollectsOneElementSlot : Bool :=
  (match runCallbackMap [("Collect", callbackCollectAlg)] (.listLiteral [.num 7]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.num 7, .num 8]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7],
       Result.listValue [Result.atom 8]]) => true
   | _ => false)

#guard restOnlyMapCallbackCollectsOneElementSlot

-- Structured elements stay one collected slot, preserving their exact kind:
-- [[1, 2]].map(Collect) => [[[1, 2]]]; [(1, 2)].map(Collect) => [[(1, 2)]];
-- [[]].map(Collect) => [[[]]]; [()].map(Collect) => [[()]].
def restOnlyMapCallbackPreservesElementKind : Bool :=
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.listLiteral [.num 1, .num 2]]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]]) =>
       true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.capture [.num 1, .num 2]]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]]) =>
       true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.listLiteral []]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.listValue []]]) => true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.emptySequence 1]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.sequenceValue []]]) => true
   | _ => false)

#guard restOnlyMapCallbackPreservesElementKind

-- Dotted receiver form agrees: [7].map(Collect) via dotCall.
def restOnlyMapCallbackDottedReceiverAgrees : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Collect", callbackCollectAlg)]
    [.dotCall (.listLiteral [.num 7]) "map" (some [resolve "Collect"])])) with
  | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true
  | _ => false

#guard restOnlyMapCallbackDottedReceiverAgrees

-- Mixed flat variadic callbacks: the lone sequence element opens into row slots
-- (the flat-callback row convention), then the shared binder allocates
-- front/collecting/back — agreeing with the structured-pattern form.
def mixedVariadicMapCallbackBindsRowSlots : Bool :=
  let middleFlat : Algorithm := algWithParameters
    [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }]
    [] [] [.param "middle"]
  let middleStructured : Algorithm := algWithParameterPatterns
    [.sequenceValue [collectFix "first", collectVar "middle", collectFix "last"]]
    [] [] [.param "middle"]
  let headFlat : Algorithm := algWithParameters
    [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "rest"]
  let initFlat : Algorithm := algWithParameters
    [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "init"]
  let row4 : KatLang.Expr := .listLiteral [.capture [.num 1, .num 2, .num 3, .num 4]]
  let row3 : KatLang.Expr := .listLiteral [.capture [.num 1, .num 2, .num 3]]
  -- [(1, 2, 3, 4)].map(F) with F(first, *middle, last) = middle => [[2, 3]]
  (match runCallbackMap [("F", middleFlat)] row4 "F" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- ... and the structured form F((first, *middle, last)) agrees.
  (match runCallbackMap [("F", middleStructured)] row4 "F" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- [(1, 2, 3)].map(Head) with Head(first, *rest) = rest => [[2, 3]]
  (match runCallbackMap [("Head", headFlat)] row3 "Head" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- [7].map(Head): the scalar row opens to one slot, the rest is empty => [[]]
  (match runCallbackMap [("Head", headFlat)] (.listLiteral [.num 7]) "Head" with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  -- [(1, 2, 3)].map(Init) with Init(*init, last) = init => [[1, 2]]
  (match runCallbackMap [("Init", initFlat)] row3 "Init" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false)

#guard mixedVariadicMapCallbackBindsRowSlots

-- Filter predicates observe the collected list kind: items == [7] holds only
-- when the collecting parameter collected exactly [7] — scalar 7 vs [7] is distinguishable.
def restOnlyFilterCallbackIsKindSensitive : Bool :=
  let isSingleSeven : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }] [] []
    [.binary .eq (.param "items") (.listLiteral [.num 7])]
  let isSingleSevenList : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }] [] []
    [.binary .eq (.param "items") (.listLiteral [.listLiteral [.num 7]])]
  (match runResult (.algorithmExpr (algPrivate [] [] [("IsSingleSeven", isSingleSeven)]
      [.call (resolve "filter") [.listLiteral [.num 7, .num 8], resolve "IsSingleSeven"]])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("P", isSingleSevenList)]
      [.call (resolve "filter") [.listLiteral [.listLiteral [.num 7], .listLiteral [.num 8]], resolve "P"]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false)

#guard restOnlyFilterCallbackIsKindSensitive

-- Reducer with the collecting parameter in ELEMENT position (before the accumulator boundary):
-- R(*items, acc) collects the projected element as [element] each step.
def reducerElementSideVariadicCollects : Bool :=
  let eqTen : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] []
    [.binary .eq (.param "items") (.listLiteral [.num 10])]
  let track : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] []
    [.capture [.sequenceSpread (.param "acc"), .param "items"]]
  -- reduce([10], R, 99) => 1: the single step observes items = [10], not 10.
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", eqTen)]
      [.call (resolve "reduce") [.listLiteral [.num 10], resolve "R", .num 99]])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  -- reduce((10, 20), R, ()) with R(*items, acc) = (acc*, items)
  -- => (10, [20]): each step appends the collected [element].
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", track)]
      [.call (resolve "reduce") [.capture [.num 10, .num 20], resolve "R", .emptySequence 1]])) with
   | Except.ok (Result.sequenceValue [Result.atom 10, Result.listValue [Result.atom 20]]) => true
   | _ => false)

#guard reducerElementSideVariadicCollects

-- A genuine single-collecting reducer receives the callback's two ordinary slots,
-- element and accumulator, and collects both through the same shared binder.
-- This intentional widening follows the ordinary variadic call rule.
def restOnlyReducerCollectsElementAndAccumulatorSlots : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", callbackCollectAlg)]
      [.call (resolve "reduce") [.listLiteral [.num 10], resolve "R", .num 99]])) with
   | Except.ok (Result.listValue [Result.atom 10, Result.atom 99]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", callbackCollectAlg)]
      [.call (resolve "reduce") [.listLiteral [.listLiteral [.num 1, .num 2]], resolve "R", .listLiteral []]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2],
       Result.listValue []]) => true
   | _ => false)

#guard restOnlyReducerCollectsElementAndAccumulatorSlots

-- Explicit-argument semantics behind implicit forwarding elaboration: an
-- ordinary parameter passed UNSPREAD into a variadic callee stays one
-- argument boundary (`Use(items) = Target(items)`), while a collecting parameter
-- forwarded WITH spread re-supplies its collected items
-- (`Use(*items) = Target(items*)`). The front-end resolver synthesizes
-- exactly these two elaborated forms from the source binding kind.
def forwardingElaborationKindsObservable : Bool :=
  let useOrdinary : Algorithm := alg ["items"] [] [] [
    .call (resolve "Target") [.param "items"]
  ]
  let run (useAlg : Algorithm) (args : List KatLang.Expr) : Except KatLang.Error Result :=
    runResult (.algorithmExpr (algPrivate [] []
      [("Target", collectTargetAlg), ("Use", useAlg)]
      [.call (resolve "Use") args]))
  -- Use(items) = Target(items): Use([1, 2]) => [[1, 2]]; Use((1, 2)) => [(1, 2)].
  (match run useOrdinary [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match run useOrdinary [.capture [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match run useOrdinary [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  -- Use(*items) = Target(items*): Use([1, 2]) => [[1, 2]] (round trip).
  (match run collectForwardAlg [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false)

#guard forwardingElaborationKindsObservable

end KatLangTests
