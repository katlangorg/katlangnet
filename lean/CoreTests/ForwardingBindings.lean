import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (OwnerLevel OwnedDeclaration selectOwnedDeclaration elaboratesToParameter conflictingOwnedNames
  validOwnedDeclarations ForwardingSource forwardingSource forwardParameter alg algPrivate privateProp privateLocalProp
  PropExposure runResult Result Expr)

--------------------------------------------------------------------------------
-- Automatic parameter forwarding preserves existing bindings (Q-04, decided 2026-09-28)
--------------------------------------------------------------------------------
-- THE LAW: automatic parameter forwarding must not change what an existing name
-- refers to. Forwarding reuses PARAMETER bindings only — the referencing body's own,
-- or an accessible captured parameter of an enclosing owner, a clause-branch binder
-- included — and a property, an opened name, a module member or a prelude builtin is
-- never forwarded as a parameter. A new (forwarded) parameter is added only when no
-- parameter binding exists, and it is never what a written name denotes.
--
-- Part 1 pins `forwardingSource` on the owner chains of the C# regression matrix
-- (AutomaticForwardingBindingTests), innermost level first; the prelude is the
-- outermost property level. Part 2 evaluates hand-written ELABORATED trees — the tree
-- the decided rule produces beside the one the superseded rule produced — so the
-- observable difference is pinned in Lean too. (Lean has no surface parser: the
-- derived `forwarding-*` cases of LanguageSpecCases.lean compare the real C#
-- elaborations.)

def fwdLevel (parameters properties : List String) (forwarded : List String := []) : OwnerLevel :=
  { parameters := parameters, properties := properties, forwarded := forwarded }

/-- The prelude's names the matrix meets. -/
def fwdPrelude : OwnerLevel := fwdLevel [] ["pi", "count", "min", "max", "abs", "if"]

-- ── 1. Which binding forwarding reuses ─────────────────────────────────────────

/-- PV-01: `A = y + 1` / `F(y) = { G = y * 1000 + A ⏎ H(y) = G ⏎ H(100) }`. G (level 0)
    forwards A's `y`; F (level 1) binds it, and the written `y` in G denotes that very
    binding. -/
def chainPv01 : List OwnerLevel :=
  [fwdLevel [] [], fwdLevel ["y"] ["G", "H"], fwdLevel [] ["A", "F"], fwdPrelude]

#guard forwardingSource chainPv01 true "y" == .capturedParameter 1
#guard selectOwnedDeclaration chainPv01 "y" == .parameter 1
-- The superseded rule lifted `y` into G's own parameters, and the written `y` then
-- selected G's (level 0) instead of F's (level 1): the rebinding PV-01 observed.
#guard selectOwnedDeclaration ((fwdLevel ["y"] []) :: chainPv01.drop 1) "y" == .parameter 0

-- The body's own written or inferred parameter is reused as before.
#guard forwardingSource [fwdLevel ["y"] [], fwdLevel [] ["A"], fwdPrelude] true "y" == .ownParameter
-- Explicit shadowing stays intentional: `Inner(y)` inside `Outer(y)` forwards its own.
#guard forwardingSource [fwdLevel ["y"] [], fwdLevel ["y"] ["Inner"], fwdLevel [] ["A", "Outer"], fwdPrelude] false "y"
  == .ownParameter

-- Several nested levels: the original binding survives every forwarding layer.
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["Inner"], fwdLevel ["y"] ["Mid"], fwdLevel [] ["A", "Outer"], fwdPrelude]
  true "y" == .capturedParameter 2

-- A clause-branch binder is a parameter binding like any other.
#guard forwardingSource [fwdLevel [] [], fwdLevel ["n"] ["G"], fwdLevel [] ["A", "F"], fwdPrelude] true "n"
  == .capturedParameter 1

-- A CLOSED body (`F(x) = A` inside G, whose rows use `y`) forwards the captured `y`
-- too; with no parameter binding of the name it forwards nothing.
#guard forwardingSource [fwdLevel ["x"] [], fwdLevel ["y"] ["F"], fwdLevel [] ["A", "G"], fwdPrelude] false "y"
  == .capturedParameter 1
#guard forwardingSource [fwdLevel ["m", "d", "t"] [], fwdLevel [] ["Speed", "KE"], fwdPrelude] false "distance"
  == .unavailable

-- A genuinely unbound dependency still becomes a forwarded parameter of an
-- inferring body.
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["A", "G"], fwdPrelude] true "y" == .forwardedParameter

-- A same-named PROPERTY is never forwarded: `v = 99` / `Need(v) = v` /
-- `Outer = Need + 1` still gives Outer a forwarded `v`.
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["v", "Need", "Outer"], fwdPrelude] true "v" == .forwardedParameter
#guard forwardingSource [fwdLevel ["q"] [], fwdLevel [] ["v", "Need", "Outer"], fwdPrelude] false "v" == .unavailable

-- A PRELUDE builtin is never forwarded: `Clamp(x, min, max)` / `Safe = Clamp + 0`
-- gives Safe forwarded `min` and `max`.
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["Clamp", "Safe"], fwdPrelude] true "min" == .forwardedParameter
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["Clamp", "Safe"], fwdPrelude] true "max" == .forwardedParameter

-- An OPENED name is never forwarded: opens are not owner levels, so the walk finds
-- nothing and the body receives a forwarded parameter.
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["Lib", "Need", "Outer"], fwdPrelude] true "v" == .forwardedParameter

-- The never-called root's own inferred names are parameter bindings of the walk, but
-- a nearer property decides first (the root's phantom exemption): then the body
-- forwards its own.
#guard forwardingSource [fwdLevel [] [], fwdLevel ["y"] ["G"], fwdPrelude] true "y" == .capturedParameter 1
#guard forwardingSource [fwdLevel [] [], fwdLevel [] ["y"], fwdLevel ["y"] ["M"], fwdPrelude] true "y" == .forwardedParameter

-- ── 2. A forwarded parameter changes no written binding ────────────────────────

/-- `v = 99` / `Need(v) = v` / `Outer = { Inner = v ⏎ Inner + Need }`: Outer (level 1
    from Inner) receives a forwarded `v`; Inner's written `v` still selects the root
    property (level 2), never Outer's forwarded parameter. -/
def chainPropertyReference : List OwnerLevel :=
  [fwdLevel [] [], fwdLevel [] ["Inner"] ["v"], fwdLevel [] ["v", "Need", "Outer"], fwdPrelude]

#guard selectOwnedDeclaration chainPropertyReference "v" == .property 2
#guard !elaboratesToParameter chainPropertyReference "v"
-- The same chain before forwarding added Outer's `v`: identical selection.
#guard selectOwnedDeclaration (chainPropertyReference.set 1 (fwdLevel [] ["Inner"])) "v" == .property 2
-- The superseded rule made the forwarded name an ordinary owner parameter, and the
-- written `v` then selected Outer's (level 1): 14 where the rule gives 106.
#guard selectOwnedDeclaration (chainPropertyReference.set 1 (fwdLevel ["v"] ["Inner"])) "v" == .parameter 1

-- `forwardParameter` itself: adding a forwarded name to the referencing body leaves
-- every selection of that chain unchanged.
#guard [ "v", "y", "min", "absent" ].all fun name =>
  selectOwnedDeclaration (forwardParameter chainPv01 name) name == selectOwnedDeclaration chainPv01 name
#guard [ "v", "y", "min", "absent" ].all fun name =>
  selectOwnedDeclaration (forwardParameter chainPropertyReference name) name
    == selectOwnedDeclaration chainPropertyReference name

-- A builtin reference stays the builtin: `NeedMin(min) = min + 1` /
-- `Safe = NeedMin + min((3, 4))` — Safe's forwarded `min` is not what `min(...)` calls.
#guard selectOwnedDeclaration [fwdLevel [] [] ["min"], fwdLevel [] ["NeedMin", "Safe"], fwdPrelude] "min" == .property 2

-- ── 3. Declaration validity still sees forwarded parameters ────────────────────

-- `A = y + 1` / `F = { y = 3 ⏎ A }`: the property `y` is never forwarded, so F
-- receives a forwarded `y`, and the two collide exactly as before.
#guard !validOwnedDeclarations [fwdLevel [] ["y"] ["y"], fwdLevel [] ["A", "F"]]
#guard conflictingOwnedNames (fwdLevel [] ["y"] ["y"]) == ["y"]
-- A nested property named like an enclosing forwarded parameter collides too.
#guard !validOwnedDeclarations [fwdLevel [] ["v"], fwdLevel [] ["Mid"] ["v"], fwdLevel [] ["Need", "Outer"]]

-- ── 4. The observable difference, on elaborated trees ──────────────────────────

/-- `A = y + 1`, shared by every tree below. -/
def fwdA : KatLang.Algorithm := alg ["y"] [] [] [.binary .add (.param "y") (.num 1)]

/-- F's body for `G = y * 1000 + <helper>` / `H(y) = G` / `H(100)`. When G reads F's
    `y` (the decided rule, and the inlined helper) it is local to F's activation. -/
def fwdPv01Body (g : KatLang.PropDef) (h : KatLang.PropDef) : KatLang.Algorithm :=
  alg ["y"] [] [g, h] [.call (.resolve "H") [.num 100]]

def fwdLocal (name : String) (body : KatLang.Algorithm) : KatLang.PropDef :=
  { privateLocalProp name (.localCapturedAncestorParams ["y"]) body with requiredOwnerDepths := some [("y", some 0)] }

/-- The decided elaboration: G has no parameter; A receives F's `y`. -/
def fwdPv01Decided : Expr :=
  .algorithmExpr (algPrivate [] [] [("A", fwdA), ("F", fwdPv01Body
    (fwdLocal "G" (alg [] [] [] [.binary .add (.binary .mul (.param "y") (.num 1000)) (.call (.resolve "A") [.param "y"])]))
    (fwdLocal "H" (alg ["y"] [] [] [.resolve "G"])))]
    [.call (.resolve "F") [.num 3]])

/-- The superseded elaboration: G lifted its own `y`, the written `y` followed it, and
    H forwarded ITS `y` (100) into G. -/
def fwdPv01Superseded : Expr :=
  .algorithmExpr (algPrivate [] [] [("A", fwdA), ("F", fwdPv01Body
    (privateProp "G" (alg ["y"] [] [] [.binary .add (.binary .mul (.param "y") (.num 1000)) (.call (.resolve "A") [.param "y"])]))
    (privateProp "H" (alg ["y"] [] [] [.call (.resolve "G") [.param "y"]])))]
    [.call (.resolve "F") [.num 3]])

/-- The helper inlined: `G = y * 1000 + (y + 1)` — the extraction-invariance control. -/
def fwdPv01Inlined : Expr :=
  .algorithmExpr (algPrivate [] [] [("F", fwdPv01Body
    (fwdLocal "G" (alg [] [] [] [.binary .add (.binary .mul (.param "y") (.num 1000)) (.binary .add (.param "y") (.num 1))]))
    (fwdLocal "H" (alg ["y"] [] [] [.resolve "G"])))]
    [.call (.resolve "F") [.num 3]])

#guard match runResult fwdPv01Decided with | .ok (Result.atom 3004) => true | _ => false
#guard match runResult fwdPv01Inlined with | .ok (Result.atom 3004) => true | _ => false
#guard match runResult fwdPv01Superseded with | .ok (Result.atom 100101) => true | _ => false

/-- `Area = width * height` / `Report(width, height) = { Doubled = Area * 2 ⏎
    if(width > 1, Doubled, 0) }` / `Report(3, 4)`: the reused helper is an ordinary
    zero-parameter property, so a neutral `if` argument reads it (24); the superseded
    helper took parameters, and the same argument was an arity error. -/
def fwdReport (doubled : KatLang.PropDef) : Expr :=
  let area := alg ["width", "height"] [] [] [.binary .mul (.param "width") (.param "height")]
  let report := alg ["width", "height"] [] [doubled]
    [.call (.resolve "if") [.compare .gt (.param "width") (.num 1), .resolve "Doubled", .num 0]]
  .algorithmExpr (algPrivate [] [] [("Area", area), ("Report", report)] [.call (.resolve "Report") [.num 3, .num 4]])

def fwdReportDecided : Expr :=
  fwdReport { privateLocalProp "Doubled" (.localCapturedAncestorParams ["height", "width"])
      (alg [] [] [] [.binary .mul (.call (.resolve "Area") [.param "width", .param "height"]) (.num 2)])
    with requiredOwnerDepths := some [("height", some 0), ("width", some 0)] }

def fwdReportSuperseded : Expr :=
  fwdReport (privateProp "Doubled"
    (alg ["width", "height"] [] [] [.binary .mul (.call (.resolve "Area") [.param "width", .param "height"]) (.num 2)]))

#guard match runResult fwdReportDecided with | .ok (Result.atom 24) => true | _ => false
#guard match runResult fwdReportSuperseded with | .error err => innermostIsAnyArityMismatch err | _ => false

/-- `v = 99` / `Need(v) = v` / `Outer = { Inner = v ⏎ Inner + Need }` / `Outer(7)`:
    Inner's `v` keeps the root property (106); the superseded rebinding read Outer's
    forwarded `v` (14). -/
def fwdPropertyReference (inner : KatLang.Algorithm) : Expr :=
  let outer := alg ["v"] [] [privateProp "Inner" inner]
    [.binary .add (.resolve "Inner") (.call (.resolve "Need") [.param "v"])]
  .algorithmExpr (algPrivate [] []
    [("v", alg [] [] [] [.num 99]), ("Need", alg ["v"] [] [] [.param "v"]), ("Outer", outer)]
    [.call (.resolve "Outer") [.num 7]])

#guard match runResult (fwdPropertyReference (alg [] [] [] [.resolve "v"])) with
  | .ok (Result.atom 106) => true | _ => false
#guard match runResult (fwdPropertyReference (alg [] [] [] [.param "v"])) with
  | .ok (Result.atom 14) => true | _ => false

/-- `v = 99` / `Need(v) = v` / `Outer = Need + 1` / `Outer(7)`: the root property is
    not forwarded; Outer's forwarded `v` receives the argument (8). -/
def fwdRootPropertyNotForwarded : Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("v", alg [] [] [] [.num 99]), ("Need", alg ["v"] [] [] [.param "v"])
    , ("Outer", alg ["v"] [] [] [.binary .add (.call (.resolve "Need") [.param "v"]) (.num 1)]) ]
    [.call (.resolve "Outer") [.num 7]])

#guard match runResult fwdRootPropertyNotForwarded with | .ok (Result.atom 8) => true | _ => false

/-- Explicit shadowing stays intentional: `Outer(y) = { Inner(y) = y * 2 ⏎
    Inner(10) + y }` / `Outer(3)` is 23. -/
def fwdExplicitShadowing : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Outer", alg ["y"] [] [privateProp "Inner" (alg ["y"] [] [] [.binary .mul (.param "y") (.num 2)])]
      [.binary .add (.call (.resolve "Inner") [.num 10]) (.param "y")])]
    [.call (.resolve "Outer") [.num 3]])

#guard match runResult fwdExplicitShadowing with | .ok (Result.atom 23) => true | _ => false

end KatLangTests
