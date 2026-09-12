import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (OwnerLevel OwnedDeclaration selectOwnedDeclaration elaboratesToParameter elaborateOpenHead validOwnedDeclarations conflictingOwnedNames Expr Error Result alg algPrivate publicProp runResult)

--------------------------------------------------------------------------------
-- Surface-layer owner walk (selectOwnedDeclaration / elaboratesToParameter)
--------------------------------------------------------------------------------
-- Search outward by owning scope: the first level that DECLARES the name wins,
-- and within an invalid recovery level a PARAMETER beats a property. Validity
-- rejects properties matching parameters in the same or an enclosing owner. Opens are consulted after
-- the owner chain; the prelude is its outermost property level.
--
-- Each chain is written innermost-first, exactly as the surface layer supplies
-- it: index 0 is the body containing the reference, and the chain — not any
-- separately counted depth — is what says which owner is nearer.
--
-- Valid elaborated PROGRAMS are guarded separately by the derived `ownership-*`
-- cases in LanguageSpecCases.lean. These guards pin selection and declaration
-- validity independently, including recovery shapes excluded from evaluation.

def level (parameters properties : List String) : OwnerLevel :=
  { parameters := parameters, properties := properties }

/-- `v = 99` / `Outer(v) = { Inner = v + 1  Inner }`: the reference sits in
    `Inner`, `Outer` binds the parameter, and the root — plus the prelude beyond
    it — declares a property of that name. -/
def chainCapturedParameter : List OwnerLevel :=
  [level [] [], level ["v"] [], level [] ["v"], level [] ["pi", "count"]]

#guard selectOwnedDeclaration chainCapturedParameter "v" == OwnedDeclaration.parameter 1
#guard elaboratesToParameter chainCapturedParameter "v" == true

/-- `Outer(v) = { v = 5  Inner = v + 1  Inner + v }`: ONE owner declares both, so
    validity rejects the source. Recovery selects the parameter for the nested
    reference, and by the same rule for the
    reference written directly in that owner's body (the chain without its
    innermost level). -/
def chainSameOwner : List OwnerLevel :=
  [level [] [], level ["v"] ["v"], level [] []]

#guard selectOwnedDeclaration chainSameOwner "v" == OwnedDeclaration.parameter 1
#guard selectOwnedDeclaration (chainSameOwner.drop 1) "v" == OwnedDeclaration.parameter 0

/-- In invalid recovery source a NEARER property is reached before the outer parameter. -/
def chainNearerProperty : List OwnerLevel :=
  [level [] [], level [] ["v"], level ["v"] [], level [] ["v"]]

#guard selectOwnedDeclaration chainNearerProperty "v" == OwnedDeclaration.property 1
#guard elaboratesToParameter chainNearerProperty "v" == false

/-- With several enclosing parameters of one name, the nearest is reached first. -/
def chainNestedParameters : List OwnerLevel :=
  [level [] [], level ["v"] [], level ["v"] [], level [] ["v"]]

#guard selectOwnedDeclaration chainNestedParameters "v" == OwnedDeclaration.parameter 1

/-- The prelude is just the outermost property level, so a parameter is always
    nearer than a builtin or a Math alias of the same name, while a name nobody
    binds still resolves there. -/
def chainPreludeAlias : List OwnerLevel :=
  [level [] [], level ["pi"] [], level [] [], level [] ["pi", "count"]]

#guard selectOwnedDeclaration chainPreludeAlias "pi" == OwnedDeclaration.parameter 1
#guard selectOwnedDeclaration chainPreludeAlias "count" == OwnedDeclaration.property 3

/-- SYN-05: every builtin CALLABLE sits at that same outermost property level
    (`preludeAlg` declares `if` with one `publicProp`, exactly like `count`), so
    the walk treats `if` as an ordinary name. A nearer property wins, a nearer
    parameter wins, and with neither the prelude still provides it. Arity plays
    no part: selection happens before any signature is consulted, so a user
    `if` of ANY arity — including the builtin's own three — is what a call to
    that name denotes. -/
def chainShadowedBuiltin : List OwnerLevel :=
  [level [] [], level [] ["if"], level [] [], level [] ["if", "count"]]

#guard selectOwnedDeclaration chainShadowedBuiltin "if" == OwnedDeclaration.property 1
#guard selectOwnedDeclaration chainShadowedBuiltin "count" == OwnedDeclaration.property 3

/-- The same through a parameter, which is how `Apply(if, x) = if(x)` binds. -/
def chainBuiltinNameAsParameter : List OwnerLevel :=
  [level [] [], level ["if"] [], level [] ["if", "count"]]

#guard selectOwnedDeclaration chainBuiltinNameAsParameter "if" == OwnedDeclaration.parameter 1
#guard elaboratesToParameter chainBuiltinNameAsParameter "if" == true

/-- Nothing nearer declares it, so the prelude level provides the builtin. -/
def chainUnshadowedBuiltin : List OwnerLevel :=
  [level [] [], level [] [], level [] ["if", "count"]]

#guard selectOwnedDeclaration chainUnshadowedBuiltin "if" == OwnedDeclaration.property 2
#guard elaboratesToParameter chainUnshadowedBuiltin "if" == false

/-- A binder-owning branch body behaves exactly like a parameter-owning
    algorithm: the binder level decides for its own body and every body nested
    in it. -/
def chainBranchBinder : List OwnerLevel :=
  [level [] [], level ["n"] ["n"], level [] ["n"]]

#guard selectOwnedDeclaration chainBranchBinder "n" == OwnedDeclaration.parameter 1

-- Nothing owns the name: the caller then applies the unchanged lookup policy
-- and — for a body that infers implicit parameters —
-- `shouldTreatAsImplicitParam`.
#guard selectOwnedDeclaration chainCapturedParameter "absent" == OwnedDeclaration.none
#guard elaboratesToParameter chainCapturedParameter "absent" == false
#guard selectOwnedDeclaration [] "v" == OwnedDeclaration.none

-- Hand-written conformance inputs, also read by OwnershipConformanceTests.cs.
-- A mask projects ONE spelling at each real owner: 0 = neither declaration,
-- 1 = parameter, 2 = property, 3 = both. Unrelated names and opens cannot affect
-- this selection. The C# test checks these masks against actual elaboration
-- contexts, then checks the selected owner, property/binder identity, executable
-- node and editor queries. Expectations are NOT obtained from C# selection or
-- from evaluation of an already elaborated AST.
-- The final field is SOURCE VALIDITY. Selection remains defined for invalid
-- recovery trees, but those trees must never be evaluated as valid source.
def ownershipConformanceInputs : List (String × List Nat × OwnedDeclaration × Bool) := [
  ("captured", [0, 1, 2], .parameter 1, true),
  ("same-owner-nested", [0, 3, 0], .parameter 1, false),
  ("same-owner-direct", [3, 0], .parameter 0, false),
  ("nearer-property", [0, 2, 1, 2], .property 1, false),
  ("nearest-parameter", [0, 1, 1, 2], .parameter 1, true),
  ("inferred-later-row", [0, 1, 0], .parameter 1, true),
  ("lifted-later-reference", [0, 1, 0], .parameter 1, true),
  ("lifted-collision", [0, 3, 0], .parameter 1, false),
  ("lifted-ancestor-collision", [0, 2, 1, 0], .property 1, false),
  ("inferred-ancestor-collision", [2, 1, 0], .property 0, false),
  ("collecting-collision", [0, 3, 0], .parameter 1, false),
  ("branch-binder", [0, 3, 2], .parameter 1, false),
  ("branch-nearer-property", [0, 2, 1, 2], .property 1, false),
  ("grouped-parameter", [0, 1, 2], .parameter 1, true),
  ("collecting-parameter", [0, 1, 2], .parameter 1, true),
  ("grouped-branch-binder", [0, 3, 2], .parameter 1, false),
  ("ancestor-property", [0, 0, 2], .property 2, true)
]

def ownershipMaskLevel (mask : Nat) : OwnerLevel :=
  level (if mask % 2 == 1 then ["v"] else [])
        (if mask / 2 == 1 then ["v"] else [])

#guard ownershipConformanceInputs.length == 17
#guard ownershipConformanceInputs.all fun (_, masks, expected, valid) =>
  validOwnedDeclarations (masks.map ownershipMaskLevel) == valid &&
  masks.all (· < 4) &&
  selectOwnedDeclaration (masks.map ownershipMaskLevel) "v" == expected &&
  elaboratesToParameter (masks.map ownershipMaskLevel) "v" ==
    (match expected with | .parameter _ => true | _ => false)

#guard conflictingOwnedNames (level ["v", "w"] ["v", "x", "v"]) == ["v", "v"]
#guard validOwnedDeclarations [level ["v"] [], level [] ["v"]]
#guard !validOwnedDeclarations [level ["v"] ["v"]]
#guard !validOwnedDeclarations chainNearerProperty
#guard !validOwnedDeclarations [level [] ["v"], level [] [], level ["v"] []]
#guard conflictingOwnedNames (level ["w"] ["v", "w", "x", "v"])
  [level ["v"] [], level [] ["x"]] == ["v", "w", "v"]

--------------------------------------------------------------------------------
-- Static-open ownership (SYN-03 / F2): an open target's head uses the SAME walk
--------------------------------------------------------------------------------
-- `open` is static, and lexical ownership still applies to the target name. The
-- head of a static open target is a bare-name occurrence like any other, so
-- `elaborateOpenHead` classifies it with `selectOwnedDeclaration`: a
-- parameter-owned head elaborates to `.param`, which is NOT an open form, so
-- open resolution rejects it and can never reach a farther property of the
-- same name. The chains carry callable bindings only (the never-called program
-- root's phantom signature is omitted by the surface layer).

/-- The two head forms `elaborateOpenHead` can produce, made decidable without a
    structural `Expr` equality: the parameter form and the lexical form, each
    carrying exactly the classified name. -/
def isParameterHead (name : String) : Expr -> Bool
  | .param n => n == name
  | _ => false

def isLexicalHead (name : String) : Expr -> Bool
  | .resolve n => n == name
  | _ => false

/-- `Lib = { public X = 7 }` / `Other = { public X = 8 }` / `F(Lib) = { open Lib  X }`:
    the open sits in F's own body, F binds the parameter, and the root declares
    the farther property of that name. -/
def chainOpenHeadParameter : List OwnerLevel :=
  [level ["Lib"] [], level [] ["Lib", "Other"], level [] ["pi", "count"]]

#guard isParameterHead "Lib" (elaborateOpenHead chainOpenHeadParameter "Lib")
#guard Expr.isOpenForm (elaborateOpenHead chainOpenHeadParameter "Lib") == false

/-- Farther-declaration independence: the same chain without the root's `Lib`
    classifies the head identically — the nearer parameter owns the name, and
    whether a farther declaration exists changes nothing. -/
def chainOpenHeadParameterNoFarther : List OwnerLevel :=
  [level ["Lib"] [], level [] ["Other"], level [] ["pi", "count"]]

#guard isParameterHead "Lib" (elaborateOpenHead chainOpenHeadParameterNoFarther "Lib")
#guard Expr.isOpenForm (elaborateOpenHead chainOpenHeadParameterNoFarther "Lib")
  == Expr.isOpenForm (elaborateOpenHead chainOpenHeadParameter "Lib")

/-- `Outer(Lib) = { Inner = { open Lib ... }  Inner }` beside a root `Lib`: the
    enclosing owner's parameter owns the head of the nested body's open. -/
def chainOpenHeadCapturedParameter : List OwnerLevel :=
  [level [] [], level ["Lib"] [], level [] ["Lib"], level [] ["pi", "count"]]

#guard isParameterHead "Lib" (elaborateOpenHead chainOpenHeadCapturedParameter "Lib")

/-- A binder-owning branch body (`F(0) = 0` / `F(Lib) = { open Lib  X }`) is a
    parameter owner like any other. -/
def chainOpenHeadBranchBinder : List OwnerLevel :=
  [level ["Lib"] [], level [] ["Lib", "F"], level [] ["pi", "count"]]

#guard isParameterHead "Lib" (elaborateOpenHead chainOpenHeadBranchBinder "Lib")

/-- `F = { open Lib  X }` beside a root `Lib`: a property-owned head stays the
    ordinary static open target, and so does a head no owner declares (left to
    the unchanged open policy). -/
def chainOpenHeadProperty : List OwnerLevel :=
  [level [] [], level [] ["Lib"], level [] ["pi", "count"]]

#guard isLexicalHead "Lib" (elaborateOpenHead chainOpenHeadProperty "Lib")
#guard Expr.isOpenForm (elaborateOpenHead chainOpenHeadProperty "Lib") == true
#guard isLexicalHead "Absent" (elaborateOpenHead chainOpenHeadProperty "Absent")

-- One decision, two positions: the elaborated head is an open form exactly when
-- the ordinary occurrence would NOT elaborate to a parameter.
#guard [chainOpenHeadParameter, chainOpenHeadParameterNoFarther, chainOpenHeadCapturedParameter,
        chainOpenHeadBranchBinder, chainOpenHeadProperty, chainCapturedParameter,
        chainNearerProperty, chainNestedParameters].all fun chain =>
  Expr.isOpenForm (elaborateOpenHead chain "Lib") == !elaboratesToParameter chain "Lib"
  && Expr.isOpenForm (elaborateOpenHead chain "v") == !elaboratesToParameter chain "v"

def innermostIsAnyBadOpenForm : Error -> Bool
  | .withContext _ inner => innermostIsAnyBadOpenForm inner
  | .badOpenForm _ => true
  | _ => false

/-- Evaluation half. The elaborated program of
    `Lib = { public X = 7 }` / `Other = { public X = 8 }` / `F(Lib) = { open Lib  X }` /
    `F(Other)`: F's open head is the `.param` the surface layer produced, so
    resolving `X` through F's opens is rejected as a bad open form — neither the
    farther root `Lib`'s 7 nor the argument's 8 is ever reached. -/
def parameterOwnedOpenHeadIsRejected : Bool :=
  let lib := alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []
  let other := alg [] [] [publicProp "X" (alg [] [] [] [.num 8])] []
  let f := alg ["Lib"] [.param "Lib"] [] [.resolve "X"]
  let program := algPrivate [] [] [("Lib", lib), ("Other", other), ("F", f)]
    [.call (.resolve "F") [.resolve "Other"]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostIsAnyBadOpenForm err
  | _ => false

#guard parameterOwnedOpenHeadIsRejected

/-- The same for a qualified target whose first segment is parameter-owned:
    `open Root.Sub` inside `F(Root)` fails at the head, never through the
    farther root `Root`. -/
def parameterOwnedQualifiedOpenHeadIsRejected : Bool :=
  let sub := alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []
  let root := alg [] [] [publicProp "Sub" sub] []
  let f := alg ["Root"] [Expr.dotCall (.param "Root") "Sub" none] [] [.resolve "X"]
  let program := algPrivate [] [] [("Root", root), ("F", f)]
    [.call (.resolve "F") [.resolve "Root"]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostIsAnyBadOpenForm err
  | _ => false

#guard parameterOwnedQualifiedOpenHeadIsRejected

/-- Control: the `.resolve` head of a property-owned target still opens the
    declared algorithm (`F = { open Lib  X }` is 7), unchanged. -/
def propertyOwnedOpenHeadStillOpens : Bool :=
  let lib := alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []
  let f := alg [] [.resolve "Lib"] [] [.resolve "X"]
  let program := algPrivate [] [] [("Lib", lib), ("F", f)] [.resolve "F"]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 7) => true
  | _ => false

#guard propertyOwnedOpenHeadStillOpens

end KatLangTests
