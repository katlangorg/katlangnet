import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (OwnerLevel OwnedDeclaration selectOwnedDeclaration elaboratesToParameter validOwnedDeclarations conflictingOwnedNames)

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

end KatLangTests
