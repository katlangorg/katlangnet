import KatLang
import CoreTests.Common

/-!
HOST-LEAN-O6 (October 2026): Lean host-scope identity aligned with C#'s by-reference identity of
ownerless host `ScopeCtx` objects (OD-1(a): every relevant level of the resolving ancestry).

A host level carries its ORIGINAL object's token in its identity slot (`PropertyIdentity.host`).
Every identity built from a scope chain reads it at every depth: the property-cache owner
(`ZeroArgPropertyCacheKey.hostOwners`), the runtime-alias binding cell and chase visit
(`aliasCellKey`, `aliasChaseKey`), and the declaring-scope relation of NEED-04 callables, Q-19 open
providers and member accessibility (`sameDeclaringScope`). Declaration provenance (`shared`) is a
separate dimension: one declaration placed under two host objects is two bindings.

The fixtures below are COHERENT encodings of C# host graphs (one token per host object, the
declarations under a level reached twice carrying their `shared` identities), except the
deliberately malformed ones in section 6, which pin the enforceable half of the input contract
(`hostProvenanceViolation?`). The executable C# correspondence lives in the generated
`CoreTests/HostParentDifferential.lean` (HP-08, HP-09, HP-12, HP-14); the kernel-checked laws in
`KatLangArityLaws/HostScopeIdentity.lean`.
-/

namespace KatLangTests.HostScopeIdentity
open KatLang

/-- An ownerless host level with the host-scope token `token`. -/
def hostAt (token : Nat) (props : List PropDef := []) (parent : Option ScopeCtx := none) : ScopeCtx :=
  .mk parent [] [] props [] [] none (some (.host token))

def pDyn : PropDef := privateProp "P" (alg [] [] [] [.param "x"])
/-- `P = x` as ONE declaration (`shared`, its value too, as the encoder emits it), wherever it is placed. -/
def pShared : PropDef :=
  { privateProp "P" ((alg [] [] [] [.param "x"]).withDeclarationId (some (.shared 887))) with identity := some (.shared 888) }
def gReader : PropDef := publicProp "G" (alg ["x"] [] [] [.resolve "P"])

/-- Two opened blocks: `RunA = G(1)` under `a`, `RunB = G(2)` under `b`, each with its own `G(x) = P`. -/
def twoOpened (a b : ScopeCtx) : Expr :=
  .algorithmExpr (alg []
    [.algorithmExpr (.mk (some a) [] [] [publicProp "RunA" (alg [] [] [] [.call (.resolve "G") [.num 1]]), gReader] []),
     .algorithmExpr (.mk (some b) [] [] [publicProp "RunB" (alg [] [] [] [.call (.resolve "G") [.num 2]]), gReader] [])]
    [] [.resolve "RunA", .resolve "RunB"])

/-- The run's value and its number of published `P` entries. -/
def observeP (e : Expr) : Option (Result × Nat) :=
  match runResultWithState e with
  | .ok (value, state) => some (value, (state.zeroArgPropertyCache.filter (·.1.propertyName == "P")).length)
  | .error _ => none

def pair (a b : Int) : Result := .sequenceValue [.atom a, .atom b]

/-- The innermost error is `illegalInEval message`. -/
def innermostIllegal (message : String) : Error -> Bool
  | .withContext _ inner => innermostIllegal message inner
  | .illegalInEval actual => actual == message
  | _ => false

def refusedWith (e : Expr) (message : String) : Bool :=
  match runResult e with
  | .error err => innermostIllegal message err
  | .ok _ => false

--------------------------------------------------------------------------------
-- 1. Kind disjointness: a host token is never a declaration, module or runtime identity.
--------------------------------------------------------------------------------

#guard PropertyIdentity.hostToken? (some (.host 3)) == some 3
#guard PropertyIdentity.hostToken? (some (.shared 3)) == none
#guard PropertyIdentity.hostToken? (some (.syntax 3)) == none
#guard PropertyIdentity.hostToken? (some (.module 3)) == none
#guard PropertyIdentity.hostToken? (some (.runtime 3)) == none
#guard !sameDeclaringScope (hostAt 0) (.mk none [] [] [] [] [] none (some (.shared 0)))
#guard !sameDeclaringScope (hostAt 0) (.mk none [] [] [] [] [] none (some (.syntax 0)))
#guard !sameDeclaringScope (hostAt 0) (.mk none [] [] [] [] [] none (some (.module 0)))
#guard !sameDeclaringScope (hostAt 0) (.mk none [] [] [] [] [] none (some (.runtime 0)))
-- An unannotated (legacy) level is never the host level either: the anonymous fallback compares the
-- printed declarations, which carry the token.
#guard !sameDeclaringScope (hostAt 0) (.mk none [] [] [] [] [] none none)

--------------------------------------------------------------------------------
-- 2. Guard 5b, provenance-aware (W5b). The OLD guard 5b (`HostScopePropertyCache.lean`) is an
--    UNANNOTATED value — one `shared` declaration under two token-less levels — and keeps its merging
--    meaning as an abstract Lean value; it is no evidence about C# objects. With provenance:
--------------------------------------------------------------------------------

-- (a) ONE host object reached through two edges: one token, one declaration — ONE owner, the first
--     caller's x (C#: HP-09a).
#guard observeP (twoOpened (hostAt 0 [pShared]) (hostAt 0 [pShared])) == some (pair 1 1, 1)
-- (b) TWO host objects sharing one declaration: two tokens — TWO owners (C#: HP-08b..d).
#guard observeP (twoOpened (hostAt 0 [pShared]) (hostAt 1 [pShared])) == some (pair 1 2, 2)
-- (c) A scope token ALONE is not provenance: one token reused over a level whose declarations carry no
--     shared identity would be split per occurrence by identification, so it is refused, never
--     evaluated as two owners.
#guard refusedWith (twoOpened (hostAt 0 [pDyn]) (hostAt 0 [pDyn])) (hostProvenanceIncoherentMessage 0)
-- (d) A declaration token ALONE (no host token) merges the two objects: the former boundary.
#guard observeP (twoOpened (.mk none [] [] [pShared] [] [] none none) (.mk none [] [] [pShared] [] [] none none))
  == some (pair 1 1, 1)

--------------------------------------------------------------------------------
-- 3. Ancestors: identity only an EMPTY host ancestor distinguishes (HOST-NESTED-1).
--    One evaluator-owned block, ONE declaration with shared members, pre-wired under an empty host
--    level and opened by its own wrapper.
--------------------------------------------------------------------------------

def dynBlock : Algorithm :=
  (alg [] [] [{ pDyn with identity := some (.shared 901) }, { gReader with identity := some (.shared 902) }] [])
    |>.withDeclarationId (some (.shared 900))

def wrapper (block : Algorithm) (parent : ScopeCtx) (members : List PropDef) : Expr :=
  .algorithmExpr (alg [] [.algorithmExpr (Algorithm.withParent (some parent) block)] members [])

def ancestorCache (first second : ScopeCtx) : Expr :=
  .algorithmExpr (alg []
    [wrapper dynBlock first [publicProp "RunA" (alg [] [] [] [.call (.resolve "G") [.num 1]])],
     wrapper dynBlock second [publicProp "RunB" (alg [] [] [] [.call (.resolve "G") [.num 2]])]]
    [] [.resolve "RunA", .resolve "RunB"])

-- Two empty host ancestors: two owners of P (C#: HP-14e). Fails if only declaring-level tokens count.
#guard observeP (ancestorCache (hostAt 1) (hostAt 2)) == some (pair 1 2, 2)
-- One empty host ancestor object reached twice: one owner (C#: HP-14f).
#guard observeP (ancestorCache (hostAt 1) (hostAt 1)) == some (pair 1 1, 1)

-- The cache key's typed host component: the owner chain's host marks, at depth 1 here.
def blockLevel (parent : ScopeCtx) : ScopeCtx := .mk (some parent) [] [] [] [] [] none (some (.shared 951))
#guard hostMarks 0 (blockLevel (hostAt 4)).hostChain == [(1, 4)]
#guard hostMarks 0 (blockLevel (hostAt 4 [] (some (hostAt 6)))).hostChain == [(1, 4), (2, 6)]
#guard hostMarks 0 (blockLevel (.mk none [] [] [] [] [] none none)).hostChain == []
#guard (zeroArgPropertyCacheKey .lexical (dynBlock.withParent (some (hostAt 4))) pDyn { callStack := [] } []).hostOwners
  == [(1, 4)]

--------------------------------------------------------------------------------
-- 4. Runtime-alias identity: binding cell and chase visit keys read the whole declaring chain.
--------------------------------------------------------------------------------

def aliasUnder (scope : ScopeCtx) : Algorithm :=
  .alias (some scope) [] [] (.dotCall (.resolve "R") "Algorithm" none) (some (.shared 950))

-- Declaring host level (HOST-ALIAS-R14): one object one cell, two objects two cells.
#guard aliasCellKey (aliasUnder (hostAt 1)) == aliasCellKey (aliasUnder (hostAt 1))
#guard aliasCellKey (aliasUnder (hostAt 1)) != aliasCellKey (aliasUnder (hostAt 2))
-- Host ANCESTOR (HOST-NESTED-1): only the ancestor's token tells the two cells apart …
#guard aliasCellShapeKey (aliasUnder (blockLevel (hostAt 1))) == aliasCellShapeKey (aliasUnder (blockLevel (hostAt 2)))
#guard aliasCellKey (aliasUnder (blockLevel (hostAt 1))) != aliasCellKey (aliasUnder (blockLevel (hostAt 2)))
#guard aliasCellKey (aliasUnder (blockLevel (hostAt 1))) == aliasCellKey (aliasUnder (blockLevel (hostAt 1)))
-- … and the chase visit key extends the cell key, so two hosts' aliases are two chase steps.
#guard aliasChaseKey (aliasUnder (blockLevel (hostAt 1))) != aliasChaseKey (aliasUnder (blockLevel (hostAt 2)))
-- A chain with no host level keeps its structural key behind the constant prefix.
#guard aliasCellKey (aliasUnder (blockLevel (.mk none [] [] [] [] [] none none)))
  == "@@" ++ aliasCellShapeKey (aliasUnder (blockLevel (.mk none [] [] [] [] [] none none)))

-- End to end: `A = R.Algorithm` declared in two host objects sharing ONE member list (one declaration
-- each): two binding cells and two R owners; one object reached twice: one of each (C#: HP-12c/HP-12d).
def aliasMembers : List PropDef :=
  [ { privateProp "F" ((alg [] [] [] [.num 7]).withDeclarationId (some (.shared 960))) with identity := some (.shared 961) },
    { privateProp "Capture" ((algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]).withDeclarationId (some (.shared 962)))
        with identity := some (.shared 963) },
    { privateProp "R" ((alg [] [] [] [.call (.resolve "Capture") [.call (.resolve "F") []]]).withDeclarationId (some (.shared 964)))
        with identity := some (.shared 965) },
    { privateProp "A" (.alias none [] [] (.dotCall (.resolve "R") "Algorithm" none) (some (.shared 966))) with identity := some (.shared 967) } ]

def aliasTwice (a b : ScopeCtx) : Expr :=
  .algorithmExpr (alg []
    [.algorithmExpr (.mk (some a) [] [] [publicProp "RunA" (alg [] [] [] [.resolve "A"])] []),
     .algorithmExpr (.mk (some b) [] [] [publicProp "RunB" (alg [] [] [] [.call (.resolve "A") []])] [])]
    [] [.resolve "RunA", .resolve "RunB"])

def aliasObservation (e : Expr) : Option (Result × Nat × Nat) :=
  match runResultWithState e with
  | .ok (value, state) =>
      some (value, state.aliasCells.length, (state.zeroArgPropertyCache.filter (·.1.propertyName == "R")).length)
  | .error _ => none

#guard aliasObservation (aliasTwice (hostAt 0 aliasMembers) (hostAt 1 aliasMembers)) == some (pair 7 7, 2, 2)
#guard aliasObservation (aliasTwice (hostAt 0 aliasMembers) (hostAt 0 aliasMembers)) == some (pair 7 7, 1, 1)

--------------------------------------------------------------------------------
-- 5. The declaring-scope relation: NEED-04 callables, Q-19 providers, accessibility.
--------------------------------------------------------------------------------

#guard sameDeclaringScope (hostAt 1) (hostAt 1)
#guard !sameDeclaringScope (hostAt 1) (hostAt 2)
#guard sameDeclaringScope (blockLevel (hostAt 1)) (blockLevel (hostAt 1))
#guard !sameDeclaringScope (blockLevel (hostAt 1)) (blockLevel (hostAt 2))

-- Q-19 over EMPTY host levels (C#: HP-14a/HP-14b): one provider declaration opened under one empty
-- host object twice is one provider; under two empty host objects it is two, and `F` is ambiguous.
def provider : Algorithm :=
  (alg [] [] [publicProp "F" (alg [] [] [] [.num 7])] []).withDeclarationId (some (.shared 970))
def openTwice (first second : ScopeCtx) : Expr :=
  .algorithmExpr (alg [] [.algorithmExpr (Algorithm.withParent (some first) provider),
    .algorithmExpr (Algorithm.withParent (some second) provider)] [] [.resolve "F"])
def ambiguousF : Error -> Bool
  | .withContext _ inner => ambiguousF inner
  | .ambiguousOpen name _ => name == "F"
  | _ => false
#guard match runResult (openTwice (hostAt 0) (hostAt 0)) with | .ok (.atom 7) => true | _ => false
#guard match runResult (openTwice (hostAt 0) (hostAt 1)) with | .error e => ambiguousF e | .ok _ => false

-- NEED-04 (C#: HP-14g/HP-14h): `P(f, f) = 0` binds one callable, so one F declaration reached under two
-- empty host ancestors is a type mismatch, under one ancestor object accepted.
def callableBlock : Algorithm :=
  (alg [] [] [{ publicProp "F" ((algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7]).withDeclarationId
      (some (.shared 980))) with identity := some (.shared 981) }] []).withDeclarationId (some (.shared 982))
def need04 (first second : ScopeCtx) : Expr :=
  .algorithmExpr (alg []
    [wrapper callableBlock first [publicProp "FA" (.alias none [] [] (.resolve "F"))],
     wrapper callableBlock second [publicProp "FB" (.alias none [] [] (.resolve "F"))]]
    [privateProp "P" (alg ["f", "f"] [] [] [.num 0])] [.call (.resolve "P") [.resolve "FA", .resolve "FB"]])
def typeMismatch : Error -> Bool
  | .withContext _ inner => typeMismatch inner
  | .typeMismatch _ => true
  | _ => false
#guard match runResult (need04 (hostAt 1) (hostAt 1)) with | .ok (.atom 0) => true | _ => false
#guard match runResult (need04 (hostAt 1) (hostAt 2)) with | .error e => typeMismatch e | .ok _ => false

-- Accessibility shares the relation: an unactivated declaring scope finds its ACTIVE declaration on
-- the site's chain only under the SAME host ancestry (`activeDeclaration?`, `scopeChainContains`,
-- used by `memberAccessible?`). No differential case reaches a cross-host owner here (host levels are
-- never activated, HP-05d..i); this pins the shared helper, not a reproduced C# defect.
#guard (activeDeclaration? (blockLevel (hostAt 1)) (some (ScopeCtx.withActivation 5 (blockLevel (hostAt 1))))).isSome
#guard (activeDeclaration? (blockLevel (hostAt 1)) (some (ScopeCtx.withActivation 5 (blockLevel (hostAt 2))))).isNone
#guard scopeChainContains (some (ScopeCtx.withActivation 5 (blockLevel (hostAt 1)))) (blockLevel (hostAt 1))
#guard !scopeChainContains (some (ScopeCtx.withActivation 5 (blockLevel (hostAt 2)))) (blockLevel (hostAt 1))

--------------------------------------------------------------------------------
-- 6. Malformed provenance: the enforceable half of the input contract (`hostProvenanceViolation?`).
--    Lean cannot detect ONE token given to two equal C# objects; the encoder's reference map owns that.
--------------------------------------------------------------------------------

def openedUnder (scope : ScopeCtx) : Expr :=
  .algorithmExpr (alg [] [.algorithmExpr (.mk (some scope) [] [] [publicProp "Run" (alg [] [] [] [.num 1])] [])] [] [.resolve "Run"])

-- A host token on an algorithm or a property is refused …
#guard refusedWith (.algorithmExpr ((alg [] [] [] [.num 1]).withDeclarationId (some (.host 0)))) hostIdentityMisplacedMessage
#guard refusedWith (.algorithmExpr (alg [] [] [{ privateProp "P" (alg [] [] [] [.num 1]) with identity := some (.host 0) }] [.resolve "P"]))
  hostIdentityMisplacedMessage
-- … and so is a host level carrying an owner body (an input level's activation never survives identification).
#guard refusedWith (openedUnder (.mk none [] [] [] [.num 1] [] none (some (.host 0)))) hostIdentityMisplacedMessage
-- One token on two different levels, or on one level under two different ancestries, is incoherent.
#guard refusedWith (twoOpened (hostAt 0 [pShared]) (hostAt 0)) (hostProvenanceIncoherentMessage 0)
#guard refusedWith (twoOpened (hostAt 0 [] (some (hostAt 1))) (hostAt 0 [] (some (hostAt 2)))) (hostProvenanceIncoherentMessage 0)
-- Ordinary programs and coherent host programs pass the check.
#guard hostProvenanceViolation? (twoOpened (hostAt 0 [pShared]) (hostAt 0 [pShared])) == none
#guard hostProvenanceViolation? (.algorithmExpr (alg [] [] [pDyn] [.resolve "P"])) == none

--------------------------------------------------------------------------------
-- 7. Preparation and derived owners.
--------------------------------------------------------------------------------

def identified (e : Expr) : Expr := (identifyPropertyExpr e).run' 0

-- Identification keeps every level's token, at every depth, and never mints one.
#guard match identified (.algorithmExpr (.mk (some (hostAt 3 [pDyn] (some (hostAt 8)))) [] [] [] [])) with
  | .algorithmExpr a => a.parent.map ScopeCtx.hostChain == some [some 3, some 8]
  | _ => false
#guard match identified (.algorithmExpr (alg [] [] [pDyn] [.resolve "P"])) with
  | .algorithmExpr (.mk none _ _ [p] _ (some (.syntax 0))) => p.identity == some (.syntax 1)
  | _ => false
-- A misplaced host identity survives identification for validation to refuse (never silently renamed).
#guard match identified (.algorithmExpr ((alg [] [] [] [.num 1]).withDeclarationId (some (.host 0)))) with
  | .algorithmExpr a => a.declarationId == some (.host 0)
  | _ => false

-- The derived owner rebuilt from a host level carries the level's token as its own identity, and its
-- scope is the level's whole host chain.
#guard match lookupInParentsStructuralProperty (hostAt 4 [pDyn] (some (hostAt 9))) "P" with
  | some r => r.owner.declarationId == some (.host 4) && r.owner.asScopeCtx.hostChain == [some 4, some 9]
  | none => false

--------------------------------------------------------------------------------
-- 8. Token renaming: a coherent injective renaming preserves every observation.
--------------------------------------------------------------------------------

#guard observeP (twoOpened (hostAt 7 [pShared]) (hostAt 3 [pShared])) == observeP (twoOpened (hostAt 0 [pShared]) (hostAt 1 [pShared]))
#guard observeP (twoOpened (hostAt 5 [pShared]) (hostAt 5 [pShared])) == observeP (twoOpened (hostAt 0 [pShared]) (hostAt 0 [pShared]))
#guard observeP (ancestorCache (hostAt 40) (hostAt 12)) == observeP (ancestorCache (hostAt 1) (hostAt 2))
#guard aliasObservation (aliasTwice (hostAt 9 aliasMembers) (hostAt 2 aliasMembers))
  == aliasObservation (aliasTwice (hostAt 0 aliasMembers) (hostAt 1 aliasMembers))

--------------------------------------------------------------------------------
-- 9. Evaluator-owned list views. Declaration and resolving-scope identity stay separate.
--    The encoder supplies view provenance when record copies replace nonempty lists;
--    per-binding ids still preserve their reference-sensitive declaring context in cache shapes.
--------------------------------------------------------------------------------

def ownedView (view : Nat) : Algorithm :=
  (alg ["x"] [.algorithmExpr (alg [] [] [] [.num 9])] [] [.param "x"]).withDeclarationId (some (.sharedView 42 view))

#guard !sameDeclaringScope (ownedView 1).asScopeCtx (ownedView 2).asScopeCtx
#guard sameRepeatedCallableIdentity (ownedView 1) (ownedView 2)
#guard aliasCellKey (aliasUnder (ownedView 1).asScopeCtx) != aliasCellKey (aliasUnder (ownedView 2).asScopeCtx)
#guard aliasChaseKey (aliasUnder (ownedView 1).asScopeCtx) != aliasChaseKey (aliasUnder (ownedView 2).asScopeCtx)
#guard aliasCellKey (aliasUnder (ownedView 1).asScopeCtx) ==
  aliasCellKey (aliasUnder ((ownedView 1).withDeclarationId (some (.sharedView 43 1))).asScopeCtx)
#guard (zeroArgPropertyCacheKey .lexical (ownedView 1) pShared { callStack := [] } []).componentOwners == [(0, 1)]
#guard PropertyIdentity.componentToken? (some (.sharedView 42 0)) == none
#guard aliasCellKey (aliasUnder ((alg [] [] [] []).withDeclarationId (some (.sharedView 42 0))).asScopeCtx) ==
  aliasCellKey (aliasUnder ((alg [] [] [] []).withDeclarationId (some (.runtime 3))).asScopeCtx)
#guard aliasCellKey ((aliasUnder (hostAt 1)).withDeclarationId (some (.sharedView 950 1)))
  == aliasCellKey ((aliasUnder (hostAt 1)).withDeclarationId (some (.shared 950)))
#guard preparedAlgorithmIdentity (some (.sharedView 42 1)) 9 == (.sharedView 42 1, 9)
#guard preparedAlgorithmIdentity (some (.moduleView 42 1)) 9 == (.moduleView 42 1, 9)
#guard ((alg [] [] [] [.num 1]).withDeclarationId (some (.moduleView 42 0))).isModuleRoot
#guard (((alg [] [] [] [.num 1]).withDeclarationId (some (.moduleView 42 0))).withParent
    (some (hostAt 2 [] (some (hostAt 3))))).parent.map ScopeCtx.hostChain == some [some 3]

-- Exercise the actual accessibility consumer, including its selected active-owner snapshot.
def capturedMember : PropDef :=
  { privateLocalProp "V" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x"]) with
    requiredOwnerDepths := some [("x", some 0)] }
def atView (view : Nat) : EvalCtx :=
  { callStack := [], headScope := some ((ownedView view).asScopeCtx.withActivation 5) }
#guard memberAccessible? (atView 1) (ownedView 1) capturedMember
#guard !memberAccessible? (atView 2) (ownedView 1) capturedMember

-- A shared runtime alias LITERAL has no binding property in its parents. Their component
-- provenance alone preserves the two cells; the same-list control must retain exactly one.
def literalHost : ScopeCtx := hostAt 0 (aliasMembers ++
  [{ privateProp "Ignore" ((alg [] [] [] []).withDeclarationId (some (.shared 998))) with identity := some (.shared 999) }])
def literalOwner (declaration components : Nat) : Expr :=
  .algorithmExpr (.mk (some literalHost) [] [.resolve "Ignore"] []
    [.algorithmExpr (.alias none [] [] (.dotCall (.resolve "R") "Algorithm" none) (some (.shared 996)))]
    (some (.sharedView declaration components)))
def literalPair (first second : Nat) : Expr :=
  .algorithmExpr (alg [] [] literalHost.props [literalOwner 990 first, literalOwner 991 second])
#guard aliasObservation (literalPair 1 2) == some (pair 7 7, 2, 1)
#guard aliasObservation (literalPair 1 1) == some (pair 7 7, 1, 1)

-- C#'s flat-family adapter is a record view of the branch body. It preserves both declaration
-- and list-component provenance while replacing the binder view.
def flatViewFamily : Algorithm := .conditional none []
  [⟨.sequenceValue [.bind "x", .bind "y"], (ownedView 1)⟩]
#guard (flatBinderUserEquivalent? flatViewFamily).bind Algorithm.declarationId == some (.sharedView 42 1)
#guard (flatBinderUserEquivalent? flatViewFamily).map Algorithm.params == some ["x", "y"]

end KatLangTests.HostScopeIdentity
