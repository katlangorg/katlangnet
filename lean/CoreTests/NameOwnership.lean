import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (OwnerLevel OwnedDeclaration selectOwnedDeclaration elaboratesToParameter elaborateOpenHead validOwnedDeclarations conflictingOwnedNames Algorithm Expr Error Pattern CondBranch PropExposure Result alg algPrivate privateProp publicProp privateLocalProp publicLocalProp runResult)

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

--------------------------------------------------------------------------------
-- Member accessibility and the open PROVIDER rule (K1-08)
--------------------------------------------------------------------------------
-- Two independent rules, pinned separately here.
--
-- SELECTION NEVER DEPENDS ON EXPOSURE. `open` selects a provider's PUBLIC
-- members and structural dot access selects DECLARED members, so a public
-- local-only member takes part in precedence and ambiguity like any provided
-- name. The ONE accessibility law (`memberAccessible?`) is then applied to the
-- member that was already selected, and it asks a purely LEXICAL question: does
-- the SITE — the algorithm whose body is being evaluated — lie inside the owner
-- of every parameter name the member captures? So a captured member is reachable
-- from every body under that owner, and from nowhere else; a dynamic binding
-- that merely happens to be live is never consulted.
--
-- An `open` PROVIDER must need no call, because `open` imports a namespace and
-- never creates the activation its members would read. Only the RESOLVED
-- provider is judged, so a dotted target may travel through a parameterized head.

def innermostIsAmbiguousOpen (name : String) : Error -> Bool
  | .withContext _ inner => innermostIsAmbiguousOpen name inner
  | .ambiguousOpen actual _ => actual = name
  | _ => false

/-- The member-name and captured-requirement half of a local-only refusal. The
    object description is diagnostics-only rendering, pinned by the structural
    guard below where the renderer's output is unambiguous. -/
def innermostRefusesCapturedMember (name : String) (required : List String) : Error -> Bool
  | .withContext _ inner => innermostRefusesCapturedMember name required inner
  | .localOnlyProperty _ actualName exposure =>
      actualName = name && exposure = PropExposure.localCapturedAncestorParams required
  | _ => false

/-- `Inner = { public X = n }` exactly as the front end elaborates it inside
    `Outer(n)`: `X` reads a parameter owned by an ancestor of its container, so
    it is local-only and RECORDS the required name. -/
def capturedMemberLibrary : Algorithm :=
  alg [] [] [publicLocalProp "X" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.param "n"])] []

/-- `Outer(n) = { Inner = { public X = n }  Inner.X }` / `Outer(5)`: the site is
    `Outer` itself, which owns `n`, so the structurally selected member is
    accessible and reads the activation's argument. -/
def memberAccessStructuralInsideOwner : Bool :=
  let outer := alg ["n"] [] [privateProp "Inner" capturedMemberLibrary]
    [Expr.dotCall (.resolve "Inner") "X" none]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 5) => true
  | _ => false

#guard memberAccessStructuralInsideOwner

/-- `Outer(n) = { open Inner  Inner = { public X = n }  X }` / `Outer(5)`: the
    same member reached through an `open`-provided name. `open` exposes public
    members whatever their exposure, and accessibility is decided afterwards from
    the same site, so this agrees with the structural spelling. -/
def memberAccessOpenInsideOwner : Bool :=
  let outer := alg ["n"] [.resolve "Inner"] [privateProp "Inner" capturedMemberLibrary]
    [.resolve "X"]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 5) => true
  | _ => false

#guard memberAccessOpenInsideOwner

/-- `Outer(n) = { Inner = { public X = n }  Deep = { Inner.X }  Deep }`: the site
    is the nested `Deep`, an ancestor of which is the owner of `n`, so being
    INSIDE the owner — not being the owner — is what admits the access. `Deep`
    itself reads a captured member, so it is local-only in turn. -/
def memberAccessFromNestedBody : Bool :=
  let deep := alg [] [] [] [Expr.dotCall (.resolve "Inner") "X" none]
  let outer := alg ["n"] []
    [privateProp "Inner" capturedMemberLibrary,
     { name := "Deep", alg := deep, isPublic := false,
       exposure := .localCapturedAncestorParams ["n"] }]
    [.resolve "Deep"]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 5) => true
  | _ => false

#guard memberAccessFromNestedBody

/-- The escape the law exists to refuse: the root writes `Outer.Inner.X` with no
    activation of `Outer` anywhere. Navigation still SELECTS `X` — `Inner` is an
    ordinary exported member and selection ignores exposure — and the refusal
    happens at the access, naming the member and what it requires. -/
def memberAccessOutsideOwnerRefused : Bool :=
  let outer := alg ["n"] [] [privateProp "Inner" capturedMemberLibrary]
    [Expr.dotCall (.resolve "Inner") "X" none]
  let program := algPrivate [] [] [("Outer", outer)]
    [Expr.dotCall (Expr.dotCall (.resolve "Outer") "Inner" none) "X" none]
  match runResult (.algorithmExpr program) with
  | .error err => innermostIsLocalOnlyProperty "Outer.Inner" "X" (.localCapturedAncestorParams ["n"]) err
  | _ => false

#guard memberAccessOutsideOwnerRefused

/-- The same escape through `open Outer.Inner` written at the root, with `Inner`
    declared `public` so the dotted step's own visibility rule is satisfied and
    the provider is genuinely reached. The provider needs no call, so the open
    itself is legal; the refusal is the ordinary member-accessibility one at the
    name it provides. -/
def memberAccessOpenOutsideOwnerRefused : Bool :=
  let outer := alg ["n"] [] [publicProp "Inner" capturedMemberLibrary]
    [Expr.dotCall (.resolve "Inner") "X" none]
  let program := algPrivate [] [Expr.dotCall (.resolve "Outer") "Inner" none]
    [("Outer", outer)] [.resolve "X"]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["n"] err
  | _ => false

#guard memberAccessOpenOutsideOwnerRefused

/-- A member captured in a BLOCK is owned by the algorithm that wrote the block, and a
    callee that merely receives it is outside that owner even when it binds the same
    parameter NAMES on the same parent: `Take(n, m) = n.X` beside
    `Outer(n, m) = { Take({ public X = m }, n) }` must not read `X`, which would resolve
    the captured `m` against TAKE's own binding and answer 5 instead of 7. Declaration
    identity separates these owners even if their output rows are also shared;
    output rows are retained for scope reconstruction, not used as owner identity. -/
def memberAccessBlockCannotEscapeIntoASameShapedCallee : Bool :=
  let block := alg [] []
    [publicLocalProp "X" (.localCapturedAncestorParams ["m"]) (alg [] [] [] [.param "m"])] []
  let take := alg ["n", "m"] [] [] [Expr.dotCall (.param "n") "X" none]
  let outer := alg ["n", "m"] [] []
    [.call (.resolve "Take") [.algorithmExpr block, .param "n"]]
  let program := algPrivate [] [] [("Take", take), ("Outer", outer)]
    [.call (.resolve "Outer") [.num 5, .num 7]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["m"] err
  | _ => false

#guard memberAccessBlockCannotEscapeIntoASameShapedCallee

/-- A required name no scope on the member's own chain binds can never be
    satisfied, so the access is refused rather than reaching an unrelated
    binding. Only a host can build this shape; the front end never does. -/
def memberAccessUnownedRequirementRefused : Bool :=
  let lib := alg [] []
    [publicLocalProp "X" (.localCapturedAncestorParams ["ghost"]) (alg [] [] [] [.num 7])] []
  let program := algPrivate [] [] [("Lib", lib)]
    [Expr.dotCall (.resolve "Lib") "X" none]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["ghost"] err
  | _ => false

#guard memberAccessUnownedRequirementRefused

/-- Selection is by declaration, so a local-only member is a genuine SECOND
    provider: `Lib = { public X = 1 }` beside `Inner = { public X = n }` under
    `open Lib, Inner` is AMBIGUOUS, never a silent fallback to the exported one.
    (Exposure-filtered selection would have answered 1 here.) -/
def openSelectionIgnoresExposure : Bool :=
  let lib := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let helper := alg [] [.resolve "Lib", .resolve "Inner"] [] [.resolve "X"]
  let outer := alg ["n"] []
    [privateProp "Inner" capturedMemberLibrary,
     { name := "Helper", alg := helper, isPublic := false,
       exposure := .localCapturedAncestorParams ["n"] }]
    [.resolve "Helper"]
  let program := algPrivate [] [] [("Lib", lib), ("Outer", outer)]
    [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostIsAmbiguousOpen "X" err
  | _ => false

#guard openSelectionIgnoresExposure

/-- `Lib(p) = { public X = p + 101  X }` / `A = { open Lib  X }`: the provider
    needs a call, and `open` never makes one, so the TARGET is refused — `X` is
    never reinterpreted as an input of `A`, and `Lib` is never instantiated. -/
def openParameterizedProviderRejected : Bool :=
  let lib := alg ["p"] []
    [publicLocalProp "X" (.localCapturedAncestorParams ["p"])
      (alg [] [] [] [.binary .add (.param "p") (.num 101)])]
    [.resolve "X"]
  let a := alg [] [.resolve "Lib"] [] [.resolve "X"]
  let program := algPrivate [] [] [("Lib", lib), ("A", a)] [.resolve "A"]
  match runResult (.algorithmExpr program) with
  | .error err =>
      innermostIsIllegalInOpen "'Lib' cannot be opened because it requires arguments (p); open imports only an algorithm that needs no call." err
  | _ => false

#guard openParameterizedProviderRejected

/-- A clause family is refused for the same reason: every alternative takes
    arguments, so there is nothing to import without calling it. -/
def openClauseFamilyProviderRejected : Bool :=
  let family : Algorithm := .conditional none [] [
    ⟨ .sequenceValue [.litInt 0], alg [] [] [] [.num 0] ⟩,
    ⟨ .sequenceValue [.bind "x"], alg [] [] [] [.param "x"] ⟩
  ]
  let a := alg [] [.resolve "F"] [] [.resolve "X"]
  let program := algPrivate [] [] [("F", family), ("A", a)] [.resolve "A"]
  match runResult (.algorithmExpr program) with
  | .error err =>
      innermostIsIllegalInOpen "'F' cannot be opened because it is a clause family that requires arguments; open imports only an algorithm that needs no call." err
  | _ => false

#guard openClauseFamilyProviderRejected

/-- Only the RESOLVED provider is judged: `open Lib.Sub` travels through the
    parameterized `Lib` to the self-contained `Sub`, which needs no call, so the
    open is legal and `X` is 7. Static `open` stays static — nothing calls `Lib`. -/
def openThroughParameterizedHeadIsAllowed : Bool :=
  let sub := alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []
  let lib := alg ["p"] [] [publicProp "Sub" sub] [.param "p"]
  let a := alg [] [Expr.dotCall (.resolve "Lib") "Sub" none] [] [.resolve "X"]
  let program := algPrivate [] [] [("Lib", lib), ("A", a)] [.resolve "A"]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 7) => true
  | _ => false

#guard openThroughParameterizedHeadIsAllowed

/-- An open head is an identity; its unused output creates no capture requirement. -/
def openDoesNotEvaluateProviderOutput : Bool :=
  let lib := alg [] [] [publicProp "X" (alg [] [] [] [.num 10])] [.param "n"]
  let p := alg [] [.resolve "Lib"] [] [.resolve "X"]
  let q := alg [] [] [] [Expr.dotCall (.resolve "Lib") "X" none]
  let outer := alg ["n"] [] [privateLocalProp "Lib" (.localCapturedAncestorParams ["n"]) lib,
    privateProp "P" p, privateProp "Q" q] [.num 0]
  let program := algPrivate [] [] [("Outer", outer)] [
    Expr.dotCall (.resolve "Outer") "P" none, Expr.dotCall (.resolve "Outer") "Q" none]
  match runResult (.algorithmExpr program) with
  | .ok value => value == Result.sequenceValue [Result.atom 10, Result.atom 10]
  | _ => false

#guard openDoesNotEvaluateProviderOutput

/-- Visibility rejects a private dotted-open step before its capture accessibility. -/
def privateDottedOpenMemberUsesVisibilityError : Bool :=
  let lib := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.param "n"]
  let outer := alg ["n"] [] [privateLocalProp "Lib" (.localCapturedAncestorParams ["n"]) lib] [.num 0]
  let pub := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] []
  let program := algPrivate [] [Expr.dotCall (.resolve "Outer") "Lib" none, .resolve "Pub"]
    [("Outer", outer), ("Pub", pub)] [.resolve "Y"]
  let rec isPrivate : Error -> Bool
    | .withContext _ inner => isPrivate inner
    | .notPublicProperty _ "Lib" => true
    | _ => false
  match runResult (.algorithmExpr program) with
  | .error error => isPrivate error
  | _ => false

#guard privateDottedOpenMemberUsesVisibilityError

/-- A navigated owner's unavailable activation is not supplied by an unrelated n. -/
def navigatedCaptureKeepsUnavailableOwner (outerName : String) : Bool :=
  let mid := alg ["n"] [] [publicLocalProp "X" (.localCapturedAncestorParams ["n"])
    (alg [] [] [] [.param "n"])] [.num 0]
  let p := { privateLocalProp "P" (.localCapturedAncestorParams ["n"])
      (alg [] [] [] [.call (.resolve "if") [.num 0, Expr.dotCall (.resolve "Mid") "X" none, .num 10]])
    with requiredOwnerDepths := some [("n", none)] }
  let read := alg [] [] [] [Expr.dotCall (.resolve "Outer") "P" none]
  let outer := alg [outerName] [] [privateProp "Mid" mid, p, privateProp "Read" read] [.resolve "Read"]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .error error => innermostRefusesCapturedMember "P" ["n"] error
  | _ => false

#guard navigatedCaptureKeepsUnavailableOwner "n"
#guard navigatedCaptureKeepsUnavailableOwner "m"

/-- Static navigation can name the enclosing active declaration, including through opens. -/
def navigatedCaptureUsesActiveOwner (outerName : String) (throughOpen : Bool) : Bool :=
  let lib := alg [] [] [publicLocalProp "X" (.localCapturedAncestorParams ["n"])
    (alg [] [] [] [.param "n"])] []
  let path := Expr.dotCall (Expr.dotCall (.resolve "Outer") "Mid" none) "Lib" none
  let read := if throughOpen then alg [] [path] [] [.resolve "X"]
    else alg [] [] [] [Expr.dotCall path "X" none]
  let mid := alg ["n"] [] [publicProp "Lib" lib, privateLocalProp "Read"
    (.localCapturedAncestorParams ["n"]) read] [.resolve "Read"]
  let outer := alg [outerName] [] [publicProp "Mid" mid] [.call (.resolve "Mid") [.num 7]]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .ok value => value == .atom 7
  | _ => false

#guard navigatedCaptureUsesActiveOwner "n" false
#guard navigatedCaptureUsesActiveOwner "m" false
#guard navigatedCaptureUsesActiveOwner "n" true
#guard navigatedCaptureUsesActiveOwner "m" true

-- A family declaration's active binder view remains part of the owning scope.
#guard !KatLang.sameDeclaringScope
  (.mk none ["n"] [] [] [] [] none (some (.shared 0)))
  (.mk none ["m"] [] [] [] [] none (some (.shared 0)))


/-- A shadowing callee cannot replace a lexical capture with its own same-named value. -/
def memberCaptureKeepsLexicalBinding (throughOpen : Bool) : Bool :=
  let read := if throughOpen then alg ["n"] [.resolve "Inner"] [] [.resolve "X"]
    else alg ["n"] [] [] [Expr.dotCall (.resolve "Inner") "X" none]
  let outer := alg ["n"] [] [privateProp "Inner" capturedMemberLibrary, privateProp "Read" read]
    [.call (.resolve "Read") [.num 7]]
  let program := algPrivate [] [] [("Outer", outer)]
    [.call (.resolve "Outer") [.num 5], .call (.resolve "Outer") [.num 9]]
  match runResult (.algorithmExpr program) with
  | .ok value => value == Result.sequenceValue [Result.atom 5, Result.atom 9]
  | _ => false

#guard memberCaptureKeepsLexicalBinding false
#guard memberCaptureKeepsLexicalBinding true

/-- Transitive Q belongs to Outer even though Mid binds another n. -/
def memberTransitiveOwnerBypassesShadow : Bool :=
  let q := privateLocalProp "Q" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.param "n"])
  let x := { publicLocalProp "X" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.resolve "Q"])
    with requiredOwnerDepths := some [("n", some 1)] }
  let mid := alg ["n"] [] [x] [.resolve "X"]
  let outer := alg ["n"] [] [q, privateLocalProp "Mid" (.localCapturedAncestorParams ["n"]) mid]
    [Expr.dotCall (.resolve "Mid") "X" none]
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .ok (Result.atom 5) => true
  | _ => false

#guard memberTransitiveOwnerBypassesShadow

/-- H's next activation cannot receive the previous activation's captured provider. -/
def memberSameDeclarationDifferentActivationRefused : Bool :=
  let block := alg [] [] [publicLocalProp "X" (.localCapturedAncestorParams ["n"])
    (alg [] [] [] [.param "n"])] []
  let h := alg ["f", "n"] [] [] [.call (.resolve "if") [.param "n",
    .call (.resolve "H") [.algorithmExpr block, .num 0], Expr.dotCall (.param "f") "X" none]]
  let initial := alg [] [] [publicProp "X" (alg [] [] [] [.num 0])] []
  let program := algPrivate [] [] [("H", h)] [.call (.resolve "H") [.algorithmExpr initial, .num 5]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["n"] err
  | _ => false

#guard memberSameDeclarationDifferentActivationRefused

/-- A static nested declaration retains its already captured ancestor activation. -/
def memberStaticNestedProviderKeepsAncestorActivation : Bool :=
  let x := publicLocalProp "X" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.param "n"])
  let lib := alg ["n"] [] [x] [Expr.dotCall (.param "f") "X" none]
  let outer := alg ["f", "k"] [] [privateLocalProp "Lib" (.localCapturedAncestorParams ["f"]) lib]
    [.call (.resolve "if") [.param "k", .call (.resolve "Outer") [.resolve "Lib", .num 0],
      .call (.resolve "Lib") [.num 7]]]
  let initial := alg [] [] [publicProp "X" (alg [] [] [] [.num 0])] []
  let program := algPrivate [] [] [("Outer", outer)] [.call (.resolve "Outer") [.algorithmExpr initial, .num 1]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["n"] err
  | _ => false

#guard memberStaticNestedProviderKeepsAncestorActivation

/-- Two distinct clause families on one parent bind n; F's provider cannot escape into G. -/
def memberClauseFamiliesHaveDistinctActivations : Bool :=
  let block := alg [] [] [publicLocalProp "X" (.localCapturedAncestorParams ["n"])
    (alg [] [] [] [.param "n"])] []
  let f : Algorithm := .conditional none [] [
    ⟨.sequenceValue [.litInt 0], alg [] [] [] [.num 0]⟩,
    ⟨.sequenceValue [.bind "n"], alg [] [] [] [.call (.resolve "H") [.algorithmExpr block, .num 0]]⟩]
  let g : Algorithm := .conditional none [] [
    ⟨.sequenceValue [.litInt 0], alg [] [] [] [.num 0]⟩,
    ⟨.sequenceValue [.bind "n"], alg [] [] [] [Expr.dotCall (.param "f") "X" none]⟩]
  let h := alg ["f", "k"] [] [privateProp "F" f,
    privateLocalProp "G" (.localCapturedAncestorParams ["f"]) g]
    [.call (.resolve "if") [.param "k", .call (.resolve "F") [.param "k"], .call (.resolve "G") [.num 7]]]
  let initial := alg [] [] [publicProp "X" (alg [] [] [] [.num 0])] []
  let program := algPrivate [] [] [("H", h)] [.call (.resolve "H") [.algorithmExpr initial, .num 5]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["n"] err
  | _ => false

#guard memberClauseFamiliesHaveDistinctActivations

/-- Sharing body components is not sharing the parameter owner declaration. -/
def memberSharedComponentsKeepDistinctOwners : Bool :=
  let x := { publicLocalProp "X" (.localCapturedAncestorParams ["n"])
      ((alg [] [] [] [.param "n"]).withDeclarationId (some (.shared 1)))
    with identity := some (.shared 1) }
  let f := alg ["n"] [] [x] [Expr.dotCall (.resolve "G") "X" none]
  let g := alg ["n"] [] [x] [Expr.dotCall (.resolve "G") "X" none]
  let program := algPrivate [] [] [("F", f), ("G", g)] [.call (.resolve "F") [.num 5]]
  match runResult (.algorithmExpr program) with
  | .error err => innermostRefusesCapturedMember "X" ["n"] err
  | _ => false

#guard memberSharedComponentsKeepDistinctOwners

/-- Family-owned opens use the same static member surface as user-body opens. Exposure
    is a front-end input; the selected member, not Lib's unused output, determines it. -/
def familyOwnedOpenStaticSurface (captures : Bool) : Bool :=
  let x := if captures then publicLocalProp "X" (.localCapturedAncestorParams ["n"])
      (alg [] [] [] [.param "n"])
    else publicProp "X" (alg [] [] [] [.num 10])
  let lib := alg [] [] [x] [if captures then .num 0 else .param "n"]
  let family := Algorithm.conditional none [.resolve "Lib"] [
    ⟨.litInt 0, alg [] [] [] [.num 10]⟩,
    ⟨.bind "k", alg [] [] [] [.resolve "X"]⟩]
  let f := if captures then privateLocalProp "F" (.localCapturedAncestorParams ["n"]) family
    else privateProp "F" family
  let outer := alg ["n"] [] [privateProp "Lib" lib, f] [.num 0]
  let program := algPrivate [] [] [("Outer", outer)] [Expr.dotCall (.resolve "Outer") "F" (some [.num 0])]
  match runResult (.algorithmExpr program) with
  | .ok value => !captures && value == .atom 10
  | .error error => captures && innermostRefusesCapturedMember "F" ["n"] error

#guard familyOwnedOpenStaticSurface false
#guard familyOwnedOpenStaticSurface true

end KatLangTests
