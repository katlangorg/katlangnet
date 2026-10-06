import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate publicProp publicLocalProp runFlat runResult runResultWithState Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Dot identity — law system U (decided 2026-10-05: Q-17 S-C, Q-18 C-B3, Q-75 F-A)
--
-- ROUTE. A dot edge decides its route member-first at every edge (DOT-01): ONE
-- structural lookup selects a declared member — whatever its spelling, a member
-- named `string` included (Q-17 S-C) — with accessibility checked after
-- selection; a member declared only in clause branches is the local-only error;
-- and only a structural MISS takes the edge's miss route: the number-to-text
-- intrinsic for `string` (DOT-08), the extension call `n(R, args)` otherwise. A
-- lexical `string` is never consulted by `.string`.
--
-- IDENTITY. The route decides CALLABLE identity, ONE projection for every
-- algorithm-capable position (DOT-09): an argumentless structural path is its
-- member's own callable — supplied (`projectNeedCallable`) and callee
-- (`resolveCalleeAlg`) read the SAME `projectNeedStructuralMember` — and every
-- other dot expression is a computed value with no callable identity. Grouping
-- never changes identity: `(Box.G)(2)` is the member call `Box.G(2)` and
-- `(Box.V)()` the explicit fresh call `Box.V()`.
--
-- The C# parser's call gate (C-B3: no call after an argument-bearing dot edge)
-- and the closed-body fallback-name check (Q-75 F-A) are front-end rules
-- (FORMAL-02) with no Lean counterpart; a host-built call after an
-- argument-bearing edge reaches the runtime law below as a computed callee.
-- C#: `DotSemanticsDecisionTests`.
--------------------------------------------------------------------------------

def dotIdRun (props : List (KatLang.Ident × Algorithm)) (out : List KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props out))

def dotIdFlat (props : List (KatLang.Ident × Algorithm)) (out : List KatLang.Expr) : Except Error (List Int) :=
  runFlat (.algorithmExpr (algPrivate [] [] props out))

/-- `Obj = { public string = 5 ⏎ 7 }`. -/
def dotIdObjStringValue : Algorithm :=
  alg [] [] [publicProp "string" (alg [] [] [] [num 5])] [num 7]

/-- `Obj = { public string(x) = x * 2 ⏎ 7 }`. -/
def dotIdObjStringCallable : Algorithm :=
  alg [] [] [publicProp "string" (alg ["x"] [] [] [.binary .mul (param "x") (num 2)])] [num 7]

/-- `Obj = { public V = 1 ⏎ 7 }`: no member named `string`. -/
def dotIdObjWithoutString : Algorithm :=
  alg [] [] [publicProp "V" (alg [] [] [] [num 1])] [num 7]

/-- `Apply(f, v) = f(v)`. -/
def dotIdApply : Algorithm :=
  alg ["f", "v"] [] [] [.call (param "f") [param "v"]]

-- ── Q-17 S-C: a declared member named `string` wins ─────────────────────────

-- `Obj.string` reads the declared zero-parameter member (5), never the intrinsic's text "7".
def dotStringDeclaredZeroParamMemberWins : Bool :=
  match dotIdRun [("Obj", dotIdObjStringValue)] [.dotCall (resolve "Obj") "string" none] with
  | .ok (.atom 5) => true
  | _ => false

#guard dotStringDeclaredZeroParamMemberWins

-- `Obj.string(5)` calls the declared callable member (10), never the intrinsic's arity error.
def dotStringDeclaredCallableMemberWins : Bool :=
  match dotIdRun [("Obj", dotIdObjStringCallable)] [.dotCall (resolve "Obj") "string" (some [num 5])] with
  | .ok (.atom 10) => true
  | _ => false

#guard dotStringDeclaredCallableMemberWins

-- On a structural MISS the edge is the intrinsic: `Obj.string` converts Obj's value 7.
def dotStringIntrinsicOnStructuralMiss : Bool :=
  match dotIdRun [("Obj", dotIdObjWithoutString)] [.dotCall (resolve "Obj") "string" none] with
  | .ok (.str "7") => true
  | _ => false

#guard dotStringIntrinsicOnStructuralMiss

-- A value receiver declares no member: `7.string` is the intrinsic.
def dotStringValueReceiverIsTheIntrinsic : Bool :=
  match dotIdRun [] [.dotCall (num 7) "string" none] with
  | .ok (.str "7") => true
  | _ => false

#guard dotStringValueReceiverIsTheIntrinsic

-- The intrinsic takes the extension call's place: a lexical `string(x) = 99` is never
-- consulted by `3.string` ("3"), while the written call `string(3)` uses it (99).
def dotStringLexicalStringIsNeverConsulted : Bool :=
  match dotIdRun [("string", alg ["x"] [] [] [num 99])] [.dotCall (num 3) "string" none],
        dotIdRun [("string", alg ["x"] [] [] [num 99])] [.call (resolve "string") [num 3]] with
  | .ok (.str "3"), .ok (.atom 99) => true
  | _, _ => false

#guard dotStringLexicalStringIsNeverConsulted

-- Navigation goes through a declared `string` member: Obj = { public string = { public Q = 3 ⏎ 4 } ⏎ 7 },
-- `Obj.string.Q` is 3 (the intrinsic's text would have no member Q).
def dotStringNavigatesTheDeclaredMember : Bool :=
  let obj := alg [] [] [publicProp "string" (alg [] [] [publicProp "Q" (alg [] [] [] [num 3])] [num 4])] [num 7]
  match dotIdRun [("Obj", obj)] [.dotCall (.dotCall (resolve "Obj") "string" none) "Q" none] with
  | .ok (.atom 3) => true
  | _ => false

#guard dotStringNavigatesTheDeclaredMember

-- The CALLABLE projection includes a `string` member: `Apply(Obj.string, 5)` is 10.
def dotStringMemberProjectsItsCallable : Bool :=
  match dotIdFlat [("Obj", dotIdObjStringCallable), ("Apply", dotIdApply)]
      [.call (resolve "Apply") [.dotCall (resolve "Obj") "string" none, num 5]] with
  | .ok [10] => true
  | _ => false

#guard dotStringMemberProjectsItsCallable

-- A member named `string` declared only in a clause branch is SELECTED as the local-only
-- error, never a miss: F(0) = { string = 1 ⏎ 0 }, F(n) = n, `F.string` is localOnlyProperty.
def dotStringBranchOnlyMemberIsLocalOnly : Bool :=
  let family := Algorithm.conditional none [] [
    { pattern := .litInt 0, body := alg [] [] [publicProp "string" (alg [] [] [] [num 1])] [num 0] },
    { pattern := .bind "n", body := alg [] [] [] [param "n"] }
  ]
  match dotIdRun [("F", family)] [.dotCall (resolve "F") "string" none] with
  | .error err => innermostIsLocalOnlyProperty "F" "string" .localConditional err
  | .ok _ => false

#guard dotStringBranchOnlyMemberIsLocalOnly

-- Accessibility is checked AFTER selection, never a fall-through to the intrinsic:
-- G(x) = { public Sub = { public string = x + 1 ⏎ 0 } ⏎ 0 } (string captures x), `G.Sub.string`.
def dotStringInaccessibleMemberIsLocalOnly : Bool :=
  let sub := alg [] [] [publicLocalProp "string" (.localCapturedAncestorParams ["x"])
    (alg [] [] [] [.binary .add (param "x") (num 1)])] [num 0]
  let g := alg ["x"] [] [publicProp "Sub" sub] [num 0]
  match dotIdRun [("G", g)] [.dotCall (.dotCall (resolve "G") "Sub" none) "string" none] with
  | .error err => innermostIsLocalOnlyProperty "G.Sub" "string" (.localCapturedAncestorParams ["x"]) err
  | .ok _ => false

#guard dotStringInaccessibleMemberIsLocalOnly

-- ── Q-18 C-B3: one callable identity in callee position ──────────────────────

/-- `Box = { public G(x) = x * 10 }`. -/
def dotIdBox : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .mul (param "x") (num 10)])] []

-- A grouped structural callee IS the member call: `(Box.G)(2)` is `Box.G(2)` (20 both).
def groupedStructuralCalleeIsTheMemberCall : Bool :=
  match dotIdFlat [("Box", dotIdBox)] [
    .call (.dotCall (resolve "Box") "G" none) [num 2],
    .dotCall (resolve "Box") "G" (some [num 2])
  ] with
  | .ok [20, 20] => true
  | _ => false

#guard groupedStructuralCalleeIsTheMemberCall

-- Supplied projection = grouped callee projection for the SAME structural AST:
-- `Apply(Box.G, 2)` and `(Box.G)(2)` both call the member (20 both).
def suppliedProjectionIsTheCalleeProjection : Bool :=
  match dotIdFlat [("Box", dotIdBox), ("Apply", dotIdApply)] [
    .call (resolve "Apply") [.dotCall (resolve "Box") "G" none, num 2],
    .call (.dotCall (resolve "Box") "G" none) [num 2]
  ] with
  | .ok [20, 20] => true
  | _ => false

#guard suppliedProjectionIsTheCalleeProjection

/-- `Id(x) = x` and `Cached = { public V = Id(5) }`: every evaluation of V's body opens one
    binding context (`EvalState.nextBindingContext`), so the contexts a run opens count how
    often V's body ran (the property-cache evidence idiom of `PropertyCacheConsumers`). -/
def dotIdCacheProps : List (KatLang.Ident × Algorithm) :=
  [ ("Id", alg ["x"] [] [] [param "x"]),
    ("Cached", alg [] [] [publicProp "V" (alg [] [] [] [.call (resolve "Id") [num 5]])] []) ]

def dotIdContexts (out : List KatLang.Expr) : Option Nat :=
  match runResultWithState (.algorithmExpr (algPrivate [] [] dotIdCacheProps out)) with
  | .ok (_, state) => some (state.nextBindingContext - 1)
  | .error _ => none

def dotIdCacheEntries (out : List KatLang.Expr) : Option Nat :=
  match runResultWithState (.algorithmExpr (algPrivate [] [] dotIdCacheProps out)) with
  | .ok (_, state) => some (state.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "V")).length
  | .error _ => none

def dotIdMemberRead : KatLang.Expr := .dotCall (resolve "Cached") "V" none
def dotIdMemberCall : KatLang.Expr := .dotCall (resolve "Cached") "V" (some [])
def dotIdGroupedMemberCall : KatLang.Expr := .call (.dotCall (resolve "Cached") "V" none) []

-- `(Cached.V)()` is the explicit FRESH call `Cached.V()`: after a read it runs V's body again
-- exactly like `Cached.V()` (a second read is the cached value and runs nothing).
def groupedZeroArgMemberCallIsFresh : Bool :=
  dotIdContexts [dotIdMemberRead, dotIdGroupedMemberCall] == dotIdContexts [dotIdMemberRead, dotIdMemberCall]
    && dotIdContexts [dotIdMemberRead, dotIdMemberRead] == dotIdContexts [dotIdMemberRead]
    && (dotIdContexts [dotIdMemberRead, dotIdGroupedMemberCall]).getD 0 > (dotIdContexts [dotIdMemberRead]).getD 0

#guard groupedZeroArgMemberCallIsFresh

-- The grouped call neither reads nor populates the property cache: alone it stores no entry,
-- while the property read stores exactly one.
def groupedZeroArgMemberCallNeverTouchesTheCache : Bool :=
  dotIdCacheEntries [dotIdGroupedMemberCall] == some 0
    && dotIdCacheEntries [dotIdMemberCall] == some 0
    && dotIdCacheEntries [dotIdMemberRead] == some 1

#guard groupedZeroArgMemberCallNeverTouchesTheCache

-- A computed dot value has NO callable identity: `(5.Inc)()` (an extension call's result)
-- and `(5.string)()` (the intrinsic's text) are notAnAlgorithm, never a wrapper invocation.
def computedDotCalleeIsNotCallable : Bool :=
  let inc := ("Inc", alg ["x"] [] [] [.binary .add (param "x") (num 1)])
  match dotIdRun [inc] [.call (.dotCall (num 5) "Inc" none) []],
        dotIdRun [] [.call (.dotCall (num 5) "string" none) []] with
  | .error first, .error second =>
      innermostIsNotAnAlgorithm KatLang.computedDotCalleeDescription first
        && innermostIsNotAnAlgorithm KatLang.computedDotCalleeDescription second
  | _, _ => false

#guard computedDotCalleeIsNotCallable

-- An argument-bearing dot edge is a call RESULT: a (host-built) call written after it,
-- `X.Mk(1)()`, is notAnAlgorithm (the C# parser rejects the spelling outright, C-B3).
def argumentBearingDotCalleeIsNotCallable : Bool :=
  let x := alg [] [] [publicProp "Mk" (alg ["k"] [] [] [.binary .add (param "k") (num 1)])] []
  match dotIdRun [("X", x)] [.call (.dotCall (resolve "X") "Mk" (some [num 1])) []] with
  | .error err => innermostIsNotAnAlgorithm KatLang.computedDotCalleeDescription err
  | .ok _ => false

#guard argumentBearingDotCalleeIsNotCallable

-- An alias member is normalized to its target: Inc(x) = x * 10, Obj = { public M = Inc ⏎ 7 },
-- `(Obj.M)(5)` is 50 — never an alias-shaped wrapper.
def groupedAliasMemberCalleeIsItsTarget : Bool :=
  let obj := alg [] [] [publicProp "M" (.alias none [] [] (resolve "Inc"))] [num 7]
  match dotIdFlat [("Inc", alg ["x"] [] [] [.binary .mul (param "x") (num 10)]), ("Obj", obj)]
      [.call (.dotCall (resolve "Obj") "M" none) [num 5]] with
  | .ok [50] => true
  | _ => false

#guard groupedAliasMemberCalleeIsItsTarget

-- A selected callable member keeps its members in every position:
-- Lib = { public M(x) = { public Q = 7 ⏎ x } }, `(Lib.M)(3)` is 3 and `Lib.M.Q` is 7.
def groupedCalleeKeepsMembersOfMembers : Bool :=
  let lib := alg [] [] [publicProp "M" (alg ["x"] [] [publicProp "Q" (alg [] [] [] [num 7])] [param "x"])] []
  match dotIdFlat [("Lib", lib)] [
    .call (.dotCall (resolve "Lib") "M" none) [num 3],
    .dotCall (.dotCall (resolve "Lib") "M" none) "Q" none
  ] with
  | .ok [3, 7] => true
  | _ => false

#guard groupedCalleeKeepsMembersOfMembers

-- Accessibility is part of the projection: G(p) = { public Sub = { public M(x) = x * p ⏎ 0 } ⏎ 0 }
-- (M captures p), `(G.Sub.M)(5)` is the local-only error, never a call.
def groupedInaccessibleCalleeIsLocalOnly : Bool :=
  let sub := alg [] [] [publicLocalProp "M" (.localCapturedAncestorParams ["p"])
    (alg ["x"] [] [] [.binary .mul (param "x") (param "p")])] [num 0]
  let g := alg ["p"] [] [publicProp "Sub" sub] [num 0]
  match dotIdRun [("G", g)] [.call (.dotCall (.dotCall (resolve "G") "Sub" none) "M" none) [num 5]] with
  | .error err => innermostIsLocalOnlyProperty "G.Sub" "M" (.localCapturedAncestorParams ["p"]) err
  | .ok _ => false

#guard groupedInaccessibleCalleeIsLocalOnly

-- The spelling exception must not return at an intermediate structural edge: the nested
-- member named string has the same identity when supplied and when used as a callee.
def nestedStringMemberHasOneCallableIdentity : Bool :=
  let member := alg ["x"] [] [] [.binary .mul (param "x") (num 3)]
  let sub := alg [] [] [publicProp "string" member] []
  let lib := alg [] [] [publicProp "Sub" sub] []
  let apply := alg ["f", "x"] [] [] [.call (param "f") [param "x"]]
  let path := KatLang.Expr.dotCall (.dotCall (resolve "Lib") "Sub" none) "string" none
  match dotIdFlat [("Lib", lib), ("Apply", apply)]
      [.call (resolve "Apply") [path, num 5], .call path [num 5]] with
  | .ok [15, 15] => true
  | _ => false

#guard nestedStringMemberHasOneCallableIdentity

end KatLangTests
