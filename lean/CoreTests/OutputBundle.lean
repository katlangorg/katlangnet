import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- OutputBundle split: algorithmExpr vs capture
--------------------------------------------------------------------------------
-- These guards pin the split itself: a capture is a normalized value boundary
-- over an OutputBundle, an algorithmExpr exposes algorithm identity, and the
-- two coincide observationally exactly on declaration-free content.

/-- A capture row captures its bundle canonically: `(1, 2)` grouping
    still observes the pair. -/
def captureValueBoundaryObservesPair : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.capture [.num 1, .num 2]])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard captureValueBoundaryObservesPair

/-- An empty bundle captures the empty sequence value (host-only shape:
    written `()` parses to the emptySequence node). -/
def emptyCaptureIsEmptySequence : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.capture []])) with
  | .ok (Result.sequenceValue []) => true
  | _ => false

#guard emptyCaptureIsEmptySequence

/-- Declaration-free content evaluates identically through both constructors —
    the shared output-row loop is the single implementation. -/
def captureAndZeroDeclBlockCoincide : Bool :=
  let rows : List KatLang.Expr := [.num 1, .capture [.num 2, .num 3], .emptySequence 0]
  match runResult (.algorithmExpr (alg [] [] [] [.capture rows])),
        runResult (.algorithmExpr (alg [] [] [] [.algorithmExpr (alg [] [] [] rows)])) with
  | .ok a, .ok b => a == b
  | _, _ => false

#guard captureAndZeroDeclBlockCoincide

/-- Capture is not algorithm identity: a grouped named callable argument stays
    on the value channel, so evaluating `(Increment)` calls the one-parameter
    property with zero arguments and fails with that arity error — Increment's
    callable identity never crosses the capture boundary. -/
def captureSuppressesCallableIdentity : Bool :=
  let increment := alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]
  let apply := alg ["f"] [] [] [.call (.param "f") [.num 9]]
  let root := algPrivate [] [] [("Apply", apply), ("Increment", increment)]
    [.call (resolve "Apply") [.capture [.resolve "Increment"]]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 1 0 e
  | _ => false

#guard captureSuppressesCallableIdentity

/-- The algorithm channel sees only a zero-parameter value thunk for a capture:
    calling a captured expression as a function is an arity error against the
    thunk, never a call of the inner algorithm. -/
def captureCalleeIsAValueThunk : Bool :=
  let f := alg ["x"] [] [] [.param "x"]
  let root := algPrivate [] [] [("F", f)]
    [.call (.capture [.resolve "F"]) [.num 1]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 0 1 e
  | _ => false

#guard captureCalleeIsAValueThunk

/-- `open` consumes algorithm/namespace identity, and a capture is a value
    boundary that never exposes the identity of what it encloses: a captured
    open target is rejected with the structured badOpenForm error (exactly
    like a spread-marked target), while a direct algorithm target opens. -/
def openCaptureTargetIsRejected : Bool :=
  let m := alg [] [] [] [.num 5]
  let lib := Algorithm.mk none [] [] [publicProp "C" (alg [] [] [] [.num 5])] []
  let direct := algPrivate [] [.algorithmExpr lib] [("M", m)] [.resolve "C"]
  let viaCapture := algPrivate [] [.capture [.resolve "M"]] [("M", m)] [.resolve "C"]
  (match runResult (.algorithmExpr direct) with
   | .ok (Result.atom 5) => true | _ => false) &&
  (match runResult (.algorithmExpr viaCapture) with
   | .error (Error.badOpenForm _) => true
   | .error (Error.withContext _ (Error.badOpenForm _)) => true
   | _ => false)

#guard openCaptureTargetIsRejected

--------------------------------------------------------------------------------
-- Boundary-policy contrast pins: capture never exposes enclosed identity
-- (open targets, higher-order arguments, receivers); algorithm blocks always
-- expose their contained algorithm.
--------------------------------------------------------------------------------

/-- `open ((M))` — a NESTED capture target is rejected identically: no
    capture depth restores the enclosed algorithm identity. -/
def openNestedCaptureTargetIsRejected : Bool :=
  let m := alg [] [] [] [.num 5]
  let viaNested := algPrivate [] [.capture [.capture [.resolve "M"]]] [("M", m)] [.resolve "C"]
  match runResult (.algorithmExpr viaNested) with
  | .error (Error.badOpenForm _) => true
  | .error (Error.withContext _ (Error.badOpenForm _)) => true
  | _ => false

#guard openNestedCaptureTargetIsRejected

/-- Nested grouping suppresses callable identity at every depth:
    `Apply(((Increment)))` fails with the same arity error as
    `Apply((Increment))` — the inner identity never crosses any capture layer. -/
def nestedCaptureStillSuppressesCallableIdentity : Bool :=
  let increment := alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]
  let apply := alg ["f"] [] [] [.call (.param "f") [.num 9]]
  let root := algPrivate [] [] [("Apply", apply), ("Increment", increment)]
    [.call (resolve "Apply") [.capture [.capture [.resolve "Increment"]]]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 1 0 e
  | _ => false

#guard nestedCaptureStillSuppressesCallableIdentity

/-- `(Obj).V` — a capture receiver exposes NO structural members. Structural
    lookup sees only the capture's value thunk (which owns nothing), the
    lexical fallback finds no `V`, and the member stays unresolved — capture
    is not algorithm identity on the receiver channel either. C# parity: the
    probe matrix pins the same failure ("Property 'V' was not found ...").
    Direct dot access on the NAMED property (`Obj.V`) still reaches the
    member. -/
def captureReceiverDoesNotExposeStructuralMembers : Bool :=
  let obj := Algorithm.mk none [] [] [publicProp "V" (alg [] [] [] [.num 7])] []
  let direct := algPrivate [] [] [("Obj", obj)] [.dotCall (.resolve "Obj") "V" none]
  let grouped := algPrivate [] [] [("Obj", obj)] [.dotCall (.capture [.resolve "Obj"]) "V" none]
  (match runResult (.algorithmExpr direct) with
   | .ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr grouped) with
   | .error _ => true
   | .ok _ => false)

#guard captureReceiverDoesNotExposeStructuralMembers

/-- The named/inline zero-parameter agreement family: a NAMED zero-parameter
    property crosses the higher-order boundary, the INLINE algorithm block
    crosses identically (test19SingleOutputBlockCrossesHigherOrderBoundary),
    and a CAPTURE of the named property does not cross — identity is
    structural (node kind), never a declaration-count taxonomy. -/
def namedZeroParamAlgorithmCrossesHigherOrderBoundary : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runFlat (.algorithmExpr (algPrivate [] []
    [("Apply", apply), ("Const", alg [] [] [] [.num 42])] [
    .call (resolve "Apply") [.resolve "Const"]
  ])) with
  | Except.ok [42] => true
  | _ => false

#guard namedZeroParamAlgorithmCrossesHigherOrderBoundary

def capturedNamedZeroParamAlgorithmDoesNotCross : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runResult (.algorithmExpr (algPrivate [] []
    [("Apply", apply), ("Const", alg [] [] [] [.num 42])] [
    .call (resolve "Apply") [.capture [.resolve "Const"]]
  ])) with
  | Except.error e => innermostIsNotAnAlgorithm "param(f)" e
  | _ => false

#guard capturedNamedZeroParamAlgorithmDoesNotCross

/-- Host-AST core invariant: a capture AROUND an algorithm block still
    suppresses the block's identity — source parentheses around braces
    normalize away, so this boundary is only reachable on the AST channel,
    and it must behave like every other capture. -/
def capturedAlgorithmExprDoesNotExposeInnerIdentity : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runResult (.algorithmExpr (algPrivate [] [] [("Apply", apply)] [
    .call (resolve "Apply") [.capture [.algorithmExpr (alg [] [] [] [.num 42])]]
  ])) with
  | Except.error e => innermostIsNotAnAlgorithm "param(f)" e
  | _ => false

#guard capturedAlgorithmExprDoesNotExposeInnerIdentity

/-- Host-AST open invariant: a capture around an algorithm block is not an
    openable target either — the outer capture is the semantic boundary. -/
def openCapturedAlgorithmExprIsRejected : Bool :=
  let lib := Algorithm.mk none [] [] [publicProp "C" (alg [] [] [] [.num 5])] []
  let viaCapture := algPrivate [] [.capture [.algorithmExpr lib]] [] [.resolve "C"]
  match runResult (.algorithmExpr viaCapture) with
  | .error (Error.badOpenForm _) => true
  | .error (Error.withContext _ (Error.badOpenForm _)) => true
  | _ => false

#guard openCapturedAlgorithmExprIsRejected

end KatLangTests
