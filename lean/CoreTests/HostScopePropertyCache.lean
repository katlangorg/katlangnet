import KatLang
import CoreTests.Common

/-!
CACHE-OWNER-D3 (owner decisions O-2/O-3/O-4, October 23 2026): zero-parameter properties declared
in a HOST-BUILT, OWNERLESS parent scope (`ScopeCtx.mk … none none`: no activation, no declaration
identity — C# `new ScopeCtx(…)`, internal `Owner` null) take part in the ordinary property cache,
Q-37 outermost publication and CACHE-PUB-1 invocation publication. The one route that keeps a host
parent at run time is an `open` block target with a pre-set parent (`wireOpenBlockToGlobalScope`);
`lookupInParentsStructuralProperty` rebuilds the declaring owner from that level with
`declarationId = none`, so its key's owner string starts with `none`.

These guards pass under the EXISTING semantics: Lean always cached these properties. The C# evaluator
bypassed its cache for them until CACHE-OWNER-D3, which identifies an ownerless host level by the
REFERENCE of the `ScopeCtx` object (D3-B). The levels here are UNANNOTATED (no host-scope token): abstract
Lean values keyed structurally, with no claim about C# objects. Since HOST-LEAN-O6 a host level that
stands for a C# object carries that object's token (`PropertyIdentity.host`), and Lean separates exactly
what C# separates — see `CoreTests/HostScopeIdentity.lean` (guard 5b with provenance) and the generated
`CoreTests/HostParentDifferential.lean`. C# twin: `tests/KatLang.Tests/HostScopePropertyCacheTests.cs`.

Evidence technique (EXPORTED-DETACHED, November 2026): `P = tick()`. Each EVALUATION of `P` returns
the next tick, so a cache hit returns the first evaluation's `1` and a second owner returns `2`: the
value says how many times the binding was evaluated, and for which reader. `P` is self-contained, as
an `exported` property must be: the evaluator runs an exported property DETACHED, so the former
technique — `P = x`, reading a name it does not bind from whichever caller read it first — is now
`unknownName` (guard 6). A host chain carries no prelude, so `tick` and `if` are the builtins
themselves.
-/

namespace KatLangTests.HostScopePropertyCache
open KatLang (alg privateProp publicProp privateLocalProp runResultWithState Algorithm Result ScopeCtx PropDef)
open KatLang (resolve param num)

/-- A host-built level: no activation, no declaration identity. -/
def hostLevel (props : List PropDef) (params : List String := []) : ScopeCtx :=
  .mk none params [] props [] [] none none

/-- `open { public Run = rows; own }` whose opened block carries `scope`; the program's row is `Run`. -/
def openedThrough (scope : ScopeCtx) (rows : List KatLang.Expr) (own : List PropDef) : KatLang.Expr :=
  .algorithmExpr (alg [] [.algorithmExpr (.mk (some scope) [] [] (publicProp "Run" (alg [] [] [] rows) :: own) [])]
    [] [resolve "Run"])

/-- `tick()`, called as the builtin itself (a host chain carries no prelude). -/
def tick : KatLang.Expr := .call (.algorithmExpr (Algorithm.builtin .tickBuiltin)) []

/-- `P = tick()`: one evaluation per owner — the witness of how many owners a run has. -/
def pDyn : PropDef := privateProp "P" (alg [] [] [] [tick])
def gReader : PropDef := publicProp "G" (alg ["x"] [] [] [resolve "P"])
def gRows : List KatLang.Expr := [.call (resolve "G") [num 1], .call (resolve "G") [num 2]]

/-- The run's value and its `P` entries as (owner declared?, bindingContext, valEnv present?). -/
def pEntries (e : KatLang.Expr) : Option (Result × List (Bool × Option Nat × Bool)) :=
  match runResultWithState e with
  | .ok (value, state) =>
      some (value, (state.zeroArgPropertyCache.filter (·.1.propertyName == "P")).map fun entry =>
        (!entry.1.owner.startsWith "none", entry.1.bindingContext, entry.1.valEnv.isSome))
  | .error _ => none

def pair11 : Result := .sequenceValue [.atom 1, .atom 1]

-- 1. An EXPORTED zero-parameter property of an ownerless host scope is cached once per run like any
--    other binding: `G(1), G(2)` is `(1, 1)`, with ONE run-wide entry whose owner carries no
--    declaration identity (C# H6e: an exported host property is evaluated as self-contained, O-4) …
#guard pEntries (openedThrough (hostLevel [pDyn]) gRows [gReader]) == some (pair11, [(false, none, false)])
-- … exactly as the same P declared by the evaluator-owned opened block (an identified owner).
#guard pEntries (openedThrough (hostLevel []) gRows [gReader, pDyn]) == some (pair11, [(true, none, false)])

-- 2. CACHE-PUB-1 through a host binding. `H(x) = P()` owns P's empty entry and publishes it; the
--    bare read through `G(2)` reuses it: `H(1), G(2)` is `(1, 1)` (C# H7).
#guard pEntries (openedThrough (hostLevel [pDyn])
    [.call (resolve "H") [num 1], .call (resolve "G") [num 2]]
    [publicProp "H" (alg ["x"] [] [] [.call (resolve "P") []]), gReader])
  == some (pair11, [(false, none, false)])

-- 3. Q-37 through a host binding: P = if(tick() > 1, 1, G(0) + 100), G(x) = P. G(1)'s read owns P's
--    key (tick 1); the read inside it is RE-ENTRANT (tick 2: returns 1, publishes nothing); the owner
--    publishes 101, which G(5) reuses (C# H8). The same holds with the owning access an explicit
--    `H(x) = P()`.
def pRecursive : PropDef :=
  privateProp "P" (alg [] [] [] [.call (.algorithmExpr (Algorithm.builtin .ifBuiltin))
    [.compare .gt tick (num 1), num 1,
     .binary .add (.call (resolve "G") [num 0]) (num 100)]])
def atoms (values : List Int) : Result := .sequenceValue (values.map Result.atom)
--    (P's own body names G, so the host level declares both.)
#guard pEntries (openedThrough (hostLevel [pRecursive, gReader]) [.call (resolve "G") [num 1], .call (resolve "G") [num 5]] [])
  == some (atoms [101, 101], [(false, none, false)])
#guard pEntries (openedThrough (hostLevel [pRecursive, gReader]) [.call (resolve "H") [num 1], .call (resolve "G") [num 5]]
    [publicProp "H" (alg ["x"] [] [] [.call (resolve "P") []])])
  == some (atoms [101, 101], [(false, none, false)])
-- The owned control publishes the same values.
#guard (pEntries (openedThrough (hostLevel []) [.call (resolve "G") [num 1], .call (resolve "G") [num 5]] [gReader, pRecursive])).map (·.1)
  == some (atoms [101, 101])

-- 4. An unactivated LOCAL-ONLY host property. No activation binds its required input, so the key falls
--    back to the ACCESS binding context and value environment: one entry per G call — `G(1), G(2)` is
--    `(1, 2)`, two evaluations (C# H6l) — …
def pLocal : PropDef := privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [tick])
#guard match pEntries (openedThrough (hostLevel [pLocal] ["x"]) gRows [gReader]) with
  | some (.sequenceValue [.atom 1, .atom 2], entries) =>
      entries.length == 2 && entries.all (fun (owned, context, env) => !owned && context.isSome && env)
  | _ => false
-- … while two reads within ONE access binding context share it: P + P inside one `G2(x) = P + P` is
-- one evaluation read twice (1 + 1), with one entry.
#guard (pEntries (openedThrough (hostLevel [pLocal] ["x"]) [.call (resolve "G2") [num 3]]
    [publicProp "G2" (alg ["x"] [] [] [.binary .add (resolve "P") (resolve "P")])])).map
  (fun (value, entries) => (value == Result.atom 2, entries.length)) == some (true, 1)

-- 5. Distinct host declaring scopes. Two host scopes, each with its own (structurally equal) P, never
--    share an entry: each PropDef occurrence has its own `syntax` identity (C# D3-B agrees: two scope
--    objects are two owners).
def twoScopes (a b : PropDef) : KatLang.Expr :=
  .algorithmExpr (alg []
    [.algorithmExpr (.mk (some (hostLevel [a])) [] [] [publicProp "RunA" (alg [] [] [] [.call (resolve "G") [num 1]]), gReader] []),
     .algorithmExpr (.mk (some (hostLevel [b])) [] [] [publicProp "RunB" (alg [] [] [] [.call (resolve "G") [num 2]]), gReader] [])]
    [] [resolve "RunA", resolve "RunB"])
#guard (pEntries (twoScopes pDyn pDyn)).map (·.1) == some (.sequenceValue [.atom 1, .atom 2])
#guard (pEntries (twoScopes pDyn pDyn)).map (·.2.length) == some 2
-- 5b. AN UNANNOTATED VALUE, not a C# graph. With ONE explicitly `shared` PropDef identity, equal chains
--     and NO host-scope token, the two levels are one Lean value and their keys coincide, so B reads A's
--     value. It is retained with that abstract meaning only: it says nothing about two C# host objects.
--     The provenance-aware pair (HOST-LEAN-O6) is `CoreTests/HostScopeIdentity.lean` § 2 — ONE object
--     (one token) reuses the owner, TWO objects sharing the declaration (two tokens) are two owners, as
--     C# keeps them (`HostScopePropertyCacheTests.DistinctHostScopeObjects_NeverShareAnOwner_*`, HP-08b).
def pShared : PropDef := { pDyn with identity := some (.shared 888) }
#guard (pEntries (twoScopes pShared pShared)).map (·.1) == some (.sequenceValue [.atom 1, .atom 1])

-- 6. THE FORMER TECHNIQUE IS REFUSED (EXPORTED-DETACHED, November 2026). An exported host property is
--    evaluated DETACHED — no inherited need cell, no inherited value — so a body that reads a name it
--    does not bind finds nothing, whoever reads it: formerly `G(1), G(2)` was `(1, 1)`, the first
--    caller's `x` shared run-wide. A host level that lists the name among its PARAMETERS is its
--    lexical owner, and one no call activated: the read is unbound there too (formerly `(1, 2)`,
--    each caller's own `x`).
def unknownX (e : KatLang.Expr) : Bool :=
  match KatLang.runResult e with
  | .error err => innermostIsUnknownName "x" err
  | .ok _ => false
def pReadsCaller : PropDef := privateProp "P" (alg [] [] [] [param "x"])
def pReadsOwner : PropDef := privateLocalProp "P" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [param "x"])
#guard unknownX (openedThrough (hostLevel [pReadsCaller]) gRows [gReader])
#guard unknownX (openedThrough (hostLevel []) gRows [gReader, pReadsCaller])
#guard unknownX (openedThrough (hostLevel [pReadsOwner] ["x"]) gRows [gReader])

end KatLangTests.HostScopePropertyCache
