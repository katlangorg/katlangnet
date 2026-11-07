import KatLangArityLaws.CallableIdentityClosure

open KatLang KatLang.RepeatedNameLaws KatLang.NestedRepeatedNames KatLang.CallableIdentityDomain
open KatLang.CallableIdentityProvenance KatLang.CallableIdentityClosure

/-!
# Evidence for `CallableIdentityProvenance` (FG-I1)

REAL RUNS (§ Real runs): each program goes through the public `runResultM`, and the checks read the
CALLABLE outcomes the run published in its final heap. `identitiesFollowATable` is the executable
form of "some `PresenceTable` is followed by all of them"; `allWalkAligned` the executable
`IdentityWalkAligned`. CONSTRUCTED VALUES (§ Constructed values) are raw scopes, never a claim about
reachability. A concrete caller of the kernel use-site theorem is in § A kernel caller.
Guards and differential tests supplement the proofs; they discharge no quantified premise.
-/

namespace KatLang.CallableIdentityProvenanceGuards

/-! ## Executable readings of the domain -/

/-- The table entries an algorithm's own wiring and its parent chain require. -/
def chainEntries : Option ScopeCtx → List (Option PropertyIdentity × Bool)
  | none => []
  | some (.mk p _ _ _ _ _ _ id) =>
      (if id.isSome then [(declKey id, parentAnonymous p)] else []) ++ chainEntries p

def identityEntries (a : Algorithm) : List (Option PropertyIdentity × Bool) :=
  if a.isBuiltin then [] else (declKey a.declarationId, parentAnonymous a.parent) :: chainEntries a.parent

/-- All the given identities follow ONE table: no key is required at both presences. -/
def identitiesFollowATable (identities : List Algorithm) : Bool :=
  let entries := identities.flatMap identityEntries
  entries.all fun x => entries.all fun y => x.1 != y.1 || x.2 == y.2

def walkAligned : ScopeCtx → ScopeCtx → Bool
  | .mk xp xps _ _ _ _ _ (some a), .mk yp yps _ _ _ _ _ (some b) =>
      if a == b && xps == yps then
        match xp, yp with
        | some p, some q => walkAligned p q
        | _, _ => true
      else true
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none => true
  | _, _ => false

def identityWalkAligned (a b : Algorithm) : Bool :=
  if declKey a.declarationId == declKey b.declarationId then
    match a.parent, b.parent with
    | some p, some q => walkAligned p q
    | _, _ => true
  else true

def allWalkAligned (identities : List Algorithm) : Bool :=
  identities.all fun a => identities.all fun b => identityWalkAligned a b

/-! ## Real runs -/

def run (e : Expr) : Except Error Result × EvalState := (runResultM e).runState.run EvalState.empty

/-- The published successful CALLABLE outcomes of a run's final heap. -/
def published (s : EvalState) : List Algorithm :=
  s.needs.toList.filterMap fun cell =>
    match cell.callable with
    | .projected (.ok (some a)) => some a
    | _ => none

/-- The binder's callable-conflict verdict, through its call-context wrappers. -/
def isCallableConflict : Error → Bool
  | .withContext _ inner => isCallableConflict inner
  | .typeMismatch message => message == "Repeated bind equality requires the same callable identity"
  | _ => false

def callableConflict : Except Error Result → Bool
  | .error err => isCallableConflict err
  | .ok _ => false

def yields (r : Except Error Result) (expected : Result) : Bool :=
  match r with
  | .ok value => value == expected
  | .error _ => false

/-- The run's identities are inside the provenance domain, with at least `count` of them. -/
def inDomain (s : EvalState) (count : Nat) : Bool :=
  let identities := published s
  count ≤ identities.length && identitiesFollowATable identities && allWalkAligned identities

def cap (x : String) : ParameterPattern := .capture { name := x }

/-- `Same(f, f, f) = 1`: a three-contribution repeated group, its VALUE never demanded. -/
def same3 : Algorithm := .mk none [cap "f", cap "f", cap "f"] [] [] [.num 1] none

def callName (n : String) (args : List Expr) : Expr := .call (.resolve n) args

def program (props : List PropDef) (out : List Expr) (opens : List Expr := []) : Expr :=
  .algorithmExpr (alg [] opens (publicProp "Same" same3 :: props) out)

def inc : Algorithm := alg ["x"] [] [] [.param "x"]

-- One retained declaration forwarded through a parameter: agreement, nothing evaluated.
def forwarded : Expr :=
  program [publicProp "Inc" inc, publicProp "Fwd" (alg ["g"] [] [] [callName "Same" [.param "g", .param "g", .param "g"]])]
    [callName "Fwd" [.resolve "Inc"]]
#guard yields (run forwarded).1 (.atom 1)
#guard inDomain (run forwarded).2 1

-- Two declarations with the same body: similarity grants nothing, in any position.
def similar (a b c : String) : Expr :=
  program [publicProp "A" inc, publicProp "B" inc] [callName "Same" [.resolve a, .resolve b, .resolve c]]
#guard callableConflict (run (similar "A" "B" "A")).1
#guard callableConflict (run (similar "A" "A" "B")).1
#guard callableConflict (run (similar "B" "A" "A")).1
#guard inDomain (run (similar "A" "B" "A")).2 2
#guard yields (run (similar "A" "A" "A")).1 (.atom 1)

/-- `W(n, k) = k(L)` with a local `L(x) = n`: `L` under `W`'s activation. -/
def withLocal : Algorithm :=
  alg ["n", "k"] [] [privateProp "L" (alg ["x"] [] [] [.param "n"])] [.call (.param "k") [.resolve "L"]]

-- One declaration under two activations with EQUAL observed values: different identities.
def twoActivations : Expr :=
  program
    [ publicProp "W" withLocal
    , publicProp "A" (alg ["g"] []
        [publicProp "C" (alg ["h"] [] [] [callName "Same" [.param "g", .param "h", .param "g"]])]
        [callName "W" [.num 1, .resolve "C"]]) ]
    [callName "W" [.num 1, .resolve "A"]]
#guard callableConflict (run twoActivations).1
#guard inDomain (run twoActivations).2 2

-- One declaration in ONE activation: the group agrees.
def oneActivation : Expr :=
  program
    [ publicProp "W" (alg ["n"] [] [publicProp "L" (alg ["x"] [] [] [.param "n"])]
        [callName "Same" [.resolve "L", .resolve "L", .resolve "L"]]) ]
    [callName "W" [.num 1]]
#guard yields (run oneActivation).1 (.atom 1)
#guard inDomain (run oneActivation).2 1

-- A transparent reference is its target; a carrier is its own declaration.
def transparent : Algorithm := .alias none [] [] (.resolve "Inc") none true
def carrier : Algorithm := .alias none [] [] (.resolve "Inc") none false
def aliases (a b c : String) : Expr :=
  program [publicProp "Inc" inc, publicProp "R" transparent, publicProp "K" carrier]
    [callName "Same" [.resolve a, .resolve b, .resolve c]]
#guard yields (run (aliases "Inc" "R" "Inc")).1 (.atom 1)
#guard yields (run (aliases "R" "R" "R")).1 (.atom 1)
#guard callableConflict (run (aliases "Inc" "K" "Inc")).1
#guard callableConflict (run (aliases "K" "R" "K")).1
#guard yields (run (aliases "K" "K" "K")).1 (.atom 1)
#guard inDomain (run (aliases "Inc" "R" "Inc")).2 1
#guard inDomain (run (aliases "K" "R" "K")).2 2

-- Builtins compare by builtin identity.
def builtins (a b c : String) : Expr := program [] [callName "Same" [.resolve a, .resolve b, .resolve c]]
#guard yields (run (builtins "map" "map" "map")).1 (.atom 1)
#guard callableConflict (run (builtins "map" "filter" "map")).1
#guard callableConflict (run (builtins "map" "map" "filter")).1

-- Mixed value/callable group: the value-only contribution neither supplies nor hides an identity.
def mixedGroup (a b : String) : Expr :=
  program [publicProp "One" (alg [] [] [] [.num 1]), publicProp "Uno" (alg [] [] [] [.num 1])]
    [callName "Same" [.resolve a, .num 1, .resolve b]]
#guard yields (run (mixedGroup "One" "One")).1 (.atom 1)
#guard callableConflict (run (mixedGroup "One" "Uno")).1
#guard inDomain (run (mixedGroup "One" "One")).2 1
#guard inDomain (run (mixedGroup "One" "Uno")).2 2

-- An anonymous ANCESTOR, with the identified member at a different depth from a local callable:
-- an inline `open` block is wired under the anonymous prelude level.
def openBlock : Expr :=
  program [publicProp "Local" inc] [callName "Same" [.resolve "F", .resolve "F", .resolve "F"]]
    [.algorithmExpr (alg [] [] [publicProp "F" inc] [])]
#guard yields (run openBlock).1 (.atom 1)
#guard inDomain (run openBlock).2 1
def openBlockAgainstLocal : Expr :=
  program [publicProp "Local" inc] [callName "Same" [.resolve "F", .resolve "Local", .resolve "F"]]
    [.algorithmExpr (alg [] [] [publicProp "F" inc] [])]
#guard callableConflict (run openBlockAgainstLocal).1
#guard inDomain (run openBlockAgainstLocal).2 2

/-! ### The boundary of the domain: a real run -/

-- A HOST-BUILT tree where one `shared` block is both an inline `open` target (wired under the
-- anonymous prelude) and a property (wired under the identified root): the same member reached both
-- ways has one declaration, equal identified levels, and then a MIXED pair, so the run reaches the
-- printed fallback at a repeated-name comparison. The printer does NOT decide this pair: the two
-- chains have unequal depth, so `compatibleActivations` refuses it whatever the text says (guard
-- below). § An equal-depth fork is the shape the printer alone decides. Source text cannot build
-- this (a written block has one declaration); it is admitted host input.
def sharedMember : Algorithm := inc.withDeclarationId (some (.shared 3))
def sharedBlock : Algorithm :=
  (alg [] [] [publicProp "F" sharedMember] []).withDeclarationId (some (.shared 1))
def sharedAcrossPresence : Expr :=
  program [publicProp "N" sharedBlock]
    [callName "Same" [.resolve "F", .dotCall (.resolve "N") "F" none, .resolve "F"]]
    [.algorithmExpr sharedBlock]
#guard callableConflict (run sharedAcrossPresence).1
#guard (published (run sharedAcrossPresence).2).length == 2
#guard !identitiesFollowATable (published (run sharedAcrossPresence).2)
#guard !allWalkAligned (published (run sharedAcrossPresence).2)
#guard match published (run sharedAcrossPresence).2 with
  | [a, b] => !compatibleActivations a.parent b.parent
  | _ => false

/-! ### The boundary of the kernel: a mixed decision in a plain source program

`Mid = { Lib = ..., open Lib.Sub, Inner = Same(X, X, X), Inner }`, with no `shared` input. `Inner`
reads `X` through `Mid`'s opens from the anonymous lookup wrapper `Algorithm.forOpens`, and wiring
`Sub` asks `activeDeclaration?` whether `Lib`'s level is that wrapper's level. The two chains have
compatible activations, so the printed fallback alone answers. (An instrumented private copy of the
production definition logged these mixed decisions in this run, FG-I1, November 2026.) This is why
`SitePresence` stays a premise of contextual wiring: without a printer fact the kernel cannot exclude
`Sub` being wired under the wrapper. -/

def midOwnedDottedOpen : Expr :=
  .algorithmExpr (alg [] []
    [ publicProp "Same" same3
    , publicProp "Mid" (alg [] [.dotCall (.resolve "Lib") "Sub" none]
        [ publicProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "X" inc] [])] [])
        , publicProp "Inner" (alg [] [] [] [callName "Same" [.resolve "X", .resolve "X", .resolve "X"]]) ]
        [.resolve "Inner"]) ]
    [.resolve "Mid"])
#guard yields (run midOwnedDottedOpen).1 (.atom 1)
#guard inDomain (run midOwnedDottedOpen).2 1

def midLevel : ScopeCtx := .mk none [] [] [] [] [] none (some (.syntax 0))
def wrapperScope : ScopeCtx := (Algorithm.forOpens midLevel).asScopeCtx
def libScope : ScopeCtx := .mk (some midLevel) [] [] [] [] [] none (some (.syntax 1))
#guard wrapperScope.declarationId.isNone && libScope.declarationId.isSome
#guard compatibleActivations (some libScope) (some wrapperScope)
#guard !sameDeclaringScope libScope wrapperScope
#guard (activeDeclaration? libScope (some wrapperScope)).isNone

/-! ### An equal-depth fork: a verdict only the printer gives

One `shared` block, pre-wired under two host levels and left unwired once. An unwired open block goes
under the anonymous prelude, a pre-wired one keeps its parent, so `F` has three chains of EQUAL depth:
`block > host 0`, `block > prelude`, `block > host 1`. Activations are compatible, declarations and
block levels agree, and the two outer levels decide alone: the first pair is mixed. C# runs the same
tree as HP-14t, and the provenance check admits it. -/

def forkMember : Algorithm := inc.withDeclarationId (some (.shared 3))
def forkBlock : Algorithm :=
  (alg [] [] [publicProp "F" forkMember] []).withDeclarationId (some (.shared 1))
def hostScope (n : Nat) : ScopeCtx := .mk none [] [] [] [] [] none (some (.host n))
def openerOf (block : Algorithm) : Algorithm :=
  alg [] [.algorithmExpr block] [publicProp "G" (.alias none [] [] (.resolve "F") none true)] []
def forkRead (name : String) : Expr := .dotCall (.resolve name) "G" none
def forkHolders : List PropDef :=
  [ publicProp "P" (openerOf (forkBlock.withParent (some (hostScope 0))))
  , publicProp "Q" (openerOf forkBlock)
  , publicProp "R" (openerOf (forkBlock.withParent (some (hostScope 1)))) ]

/-- The group `Same(P.G, Q.G, R.G)`. -/
def equalDepthFork : Expr :=
  program forkHolders [callName "Same" [forkRead "P", forkRead "Q", forkRead "R"]]

-- The group stops at the first conflict: the printed text of the mixed pair refused it.
#guard (hostProvenanceViolation? equalDepthFork).isNone
#guard callableConflict (run equalDepthFork).1
#guard (published (run equalDepthFork).2).length == 2
#guard !identitiesFollowATable (published (run equalDepthFork).2)

/-- Three uses of three callables: all three identities in ONE heap, no comparison between them. -/
def each3 : Algorithm := alg ["f", "g", "h"] [] [] [.call (.param "f") [.num 1],
  .call (.param "g") [.num 1], .call (.param "h") [.num 1]]
def allThree : Expr :=
  program (publicProp "Each" each3 :: forkHolders)
    [callName "Each" [forkRead "P", forkRead "Q", forkRead "R"]]

/-- The executable reading of `CallableFork`. -/
def isFork (a b c : Algorithm) : Bool :=
  match a.parent, b.parent, c.parent with
  | some x, some y, some z =>
      match forkOf? x y z with
      | some (u, _, w) =>
          (asBuiltin? a).isNone && (asBuiltin? b).isNone && (asBuiltin? c).isNone &&
            PropertyIdentity.callableDeclaration a.declarationId ==
              PropertyIdentity.callableDeclaration b.declarationId &&
            PropertyIdentity.callableDeclaration b.declarationId ==
              PropertyIdentity.callableDeclaration c.declarationId &&
            compatibleActivations (some x) (some y) && compatibleActivations (some y) (some x) &&
            compatibleActivations (some y) (some z) && compatibleActivations (some z) (some y) &&
            !sameDeclaringScope u w
      | none => false
  | _, _, _ => false

-- THE REAL RUN: the three published identities of one heap are a fork, with the real printer's
-- verdicts. The mixed pairs are refused, by the printed text alone.
#guard match (run allThree).1 with
  | .ok _ => true
  | .error _ => false
#guard match published (run allThree).2 with
  | [a, b, c] => isFork a b c && !sameRepeatedCallableIdentity a b &&
      !sameRepeatedCallableIdentity b c && !sameRepeatedCallableIdentity a c
  | _ => false

/-! The same fork as kernel terms: the theorems of `CallableIdentityClosure` have an inhabitant. -/

def blockScope (p : ScopeCtx) : ScopeCtx := .mk (some p) [] [] [] [] [] none (some (.shared 1))
def forkCallable (p : ScopeCtx) : Algorithm :=
  .mk (some (blockScope p)) [] [] [] [] (some (.shared 3))

theorem kernel_fork : CallableFork (forkCallable (hostScope 0)) (forkCallable preludeAlg.asScopeCtx)
    (forkCallable (hostScope 1)) (blockScope (hostScope 0)) (blockScope preludeAlg.asScopeCtx)
    (blockScope (hostScope 1)) (hostScope 0) preludeAlg.asScopeCtx (hostScope 1) where
  builtin_a := rfl
  builtin_b := rfl
  builtin_c := rfl
  declaration_ab := rfl
  declaration_bc := rfl
  parent_a := rfl
  parent_b := rfl
  parent_c := rfl
  compatible_xy := by simp [compatibleActivations, blockScope, hostScope, preludeAlg, Algorithm.asScopeCtx, Algorithm.parent]
  compatible_yx := by simp [compatibleActivations, blockScope, hostScope, preludeAlg, Algorithm.asScopeCtx, Algorithm.parent]
  compatible_yz := by simp [compatibleActivations, blockScope, hostScope, preludeAlg, Algorithm.asScopeCtx, Algorithm.parent]
  compatible_zy := by simp [compatibleActivations, blockScope, hostScope, preludeAlg, Algorithm.asScopeCtx, Algorithm.parent]
  fork := rfl
  apart := rfl

/-- THE OBSTRUCTION, on the concrete fork: the use-site obligation for these three callables is a
    statement about two strings of the core printer. -/
theorem concrete_use_site_is_a_printer_fact (l : List Contribution)
    (ha : Present l (forkCallable (hostScope 0)))
    (hb : Present l (forkCallable preludeAlg.asScopeCtx))
    (hc : Present l (forkCallable (hostScope 1))) (ht : CallableTransOn l) :
    ¬ (reprStr (hostScope 0).declaration = reprStr preludeAlg.asScopeCtx.declaration ∧
        reprStr preludeAlg.asScopeCtx.declaration = reprStr (hostScope 1).declaration) :=
  use_site_is_a_printer_fact kernel_fork l ha hb hc ht

/-- With the accept-all fallback the concrete fork is intransitive. -/
theorem concrete_fork_intransitive_under_another_fallback :
    sameIdentityVia acceptAll (forkCallable (hostScope 0)) (forkCallable preludeAlg.asScopeCtx) = true ∧
    sameIdentityVia acceptAll (forkCallable preludeAlg.asScopeCtx) (forkCallable (hostScope 1)) = true ∧
    sameIdentityVia acceptAll (forkCallable (hostScope 0)) (forkCallable (hostScope 1)) = false :=
  some_fallback_is_intransitive kernel_fork rfl

-- The real printer is on the good side of it, as an executed check that discharges nothing.
#guard !(printed (hostScope 0) preludeAlg.asScopeCtx)
#guard !(printed preludeAlg.asScopeCtx (hostScope 1))

-- The candidate agrees with production on the fork.
#guard !candidateIdentity (forkCallable (hostScope 0)) (forkCallable preludeAlg.asScopeCtx)
#guard candidateIdentity (forkCallable (hostScope 0)) (forkCallable (hostScope 0))
#guard candidateIdentity (forkCallable preludeAlg.asScopeCtx) (forkCallable preludeAlg.asScopeCtx)

/-! ## Constructed values (no reachability claim) -/

def lvl (parent : Option ScopeCtx) (id : Option PropertyIdentity) (activation : Option Nat := none) :
    ScopeCtx :=
  .mk parent [] [] [] [] [] activation id

def named : ScopeCtx := lvl none (some (.syntax 1))
def anon : ScopeCtx := lvl none none
def under (p : ScopeCtx) (d : Nat := 9) : Algorithm := .mk (some p) [] [] [] [] (some (.syntax d))

-- The top level mixed: outside the domain, and refused by the printer.
#guard !identityWalkAligned (under named) (under anon)
#guard !identitiesFollowATable [under named, under anon]
#guard !sameRepeatedCallableIdentity (under named) (under anon)
-- Different declarations at any presence: the domain says nothing, the comparison refuses them.
#guard identityWalkAligned (under named 8) (under anon 9)
#guard !sameRepeatedCallableIdentity (under named 8) (under anon 9)
-- Equal identified tops over a mixed ANCESTOR: the decision path meets the mixed pair.
#guard !walkAligned (lvl (some named) (some (.syntax 2))) (lvl (some anon) (some (.syntax 2)))
#guard !sameDeclaringScope (lvl (some named) (some (.syntax 2))) (lvl (some anon) (some (.syntax 2)))
-- Different identified tops over a mixed ancestor: the walk stops first. `WalkAligned` admits this
-- pair; `NoCrossFallback` asks about the printed text below the failed level.
#guard walkAligned (lvl (some named) (some (.syntax 2))) (lvl (some anon) (some (.syntax 3)))
-- Anonymous tops over a mixed ancestor: the walk stops at the anonymous pair.
#guard walkAligned (lvl (some named) none) (lvl (some anon) none)
#guard !sameRepeatedCallableIdentity (under (lvl (some named) none)) (under (lvl (some anon) none))
-- Unequal depths, all identified, one table: the comparison fails without a mixed level.
#guard identitiesFollowATable [under named, under (lvl (some named) (some (.syntax 2)))]
#guard !sameRepeatedCallableIdentity (under named) (under (lvl (some named) (some (.syntax 2))))
-- Activations are no part of the domain: one table, two identities.
#guard identitiesFollowATable [under (lvl (some anon) (some (.syntax 1)) (some 0)),
  under (lvl (some anon) (some (.syntax 1)) (some 1))]
#guard !sameRepeatedCallableIdentity (under (lvl (some anon) (some (.syntax 1)) (some 0)))
  (under (lvl (some anon) (some (.syntax 1)) (some 1)))
#guard sameRepeatedCallableIdentity (under (lvl (some anon) (some (.syntax 1)) (some 0)))
  (under (lvl (some anon) (some (.syntax 1)) (some 0)))

-- Host provenance and owned views. A table key erases a callable's own view, as the comparison
-- does; a PARENT's view stays in `sameDeclaringScope`. Same token: one scope; distinct tokens: two.
def host (n : Nat) : ScopeCtx := lvl none (some (.host n))
def viewed (view : Nat) : Algorithm :=
  .mk (some (host 1)) [] [] [] [] (some (.sharedView 4 view))
#guard declKey (viewed 1).declarationId == declKey (viewed 2).declarationId
#guard sameRepeatedCallableIdentity (viewed 1) (viewed 2)
#guard identitiesFollowATable [viewed 1, viewed 2]
#guard sameRepeatedCallableIdentity (under (host 1)) (under (host 1))
#guard !sameRepeatedCallableIdentity (under (host 1)) (under (host 2))
#guard identitiesFollowATable [under (host 1), under (host 2)]
def viewParent (view : Nat) : ScopeCtx := lvl none (some (.sharedView 4 view))
#guard !sameRepeatedCallableIdentity (under (viewParent 1)) (under (viewParent 2))
#guard sameRepeatedCallableIdentity (under (viewParent 1)) (under (viewParent 1))
-- A module member is wired under the chain root, wherever it is reached.
def moduleAlg : Algorithm := .mk none [] [] [] [] (some (.module 5))
#guard (moduleAlg.withParent (some (lvl (some anon) (some (.syntax 1)) (some 3)))).parent.map
  ScopeCtx.declarationId == some none
#guard sameRepeatedCallableIdentity
  (moduleAlg.withParent (some (lvl (some anon) (some (.syntax 1)))))
  (moduleAlg.withParent (some (lvl (some anon) (some (.syntax 2)))))

/-- Minted runtime wrappers, through the production operation: forwarding one retained wrapper
    agrees, a second mint of the same algorithm does not. -/
def mintTwice : Algorithm × Algorithm :=
  let base := under named
  match (identifyRuntimeAlgorithm base).runState EvalState.empty with
  | (.ok first, next) =>
      match (identifyRuntimeAlgorithm base).runState next with
      | (.ok second, _) => (first, second)
      | _ => (base, base)
  | _ => (base, base)
#guard sameRepeatedCallableIdentity mintTwice.1 mintTwice.1
#guard !sameRepeatedCallableIdentity mintTwice.1 mintTwice.2
#guard identitiesFollowATable [mintTwice.1, mintTwice.2]

/-! ## A kernel caller -/

/-- A real parent chain: an activated identified level over an anonymous root. -/
def rootLevel : ScopeCtx := lvl none none
def activated (activation : Nat) : ScopeCtx := lvl (some rootLevel) (some (.syntax 1)) (some activation)
def callee (activation : Nat) : Algorithm := under (activated activation) 2

/-- The table of the example: only declaration 1 is wired under an anonymous level. -/
def exampleTable : PresenceTable := fun k => k == some (.syntax 1)

/-- Three observed callables: one declaration, two of them in one activation. -/
def exampleModel : Model where
  view a :=
    if a = 0 then some (((.atom 1, 1) : CountedResult), some (callee 0))
    else if a = 1 then some (((.atom 1, 1) : CountedResult), some (callee 0))
    else if a = 2 then some (((.atom 1, 1) : CountedResult), some (callee 1))
    else none
  plan _ := false
  size := 3

theorem callee_follows (activation : Nat) : Follows exampleTable (callee activation) := by
  refine Or.inr ⟨rfl, ?_⟩
  intro p hp
  cases hp
  exact ⟨fun _ => rfl, fun h => by simp at h⟩

theorem example_model_follows : ModelFollows exampleTable exampleModel := by
  rintro a ⟨address, v, hv⟩
  simp only [exampleModel] at hv
  split at hv
  · cases hv; exact callee_follows 0
  · split at hv
    · cases hv; exact callee_follows 0
    · split at hv
      · cases hv; exact callee_follows 1
      · cases hv

/-- THE CONCRETE CALLER: for the example's real parents and activations, the transitivity premise of
    the permutation laws is DERIVED, for every defined head walk and every final contribution list. -/
theorem example_head_callable_trans_on (ps : List NeedPattern) (cells : List Nat) (family : Bool)
    (w : Walk) (hwf : exampleModel.WF) (h : walkHead exampleModel ps cells family = some w)
    (addresses : List Nat) : CallableTransOn (addresses.map (contrib w.2.1.obs)) :=
  head_callable_trans_on_of_success_aligned exampleModel ps cells family w hwf h
    (model_success_aligned_of_follows exampleTable exampleModel example_model_follows) addresses

-- The example is not vacuous: its two activations are different identities, each agrees with itself.
#guard sameRepeatedCallableIdentity (callee 0) (callee 0)
#guard !sameRepeatedCallableIdentity (callee 0) (callee 1)

/-! ## Proof dependency audit

These guards reject accidental proof holes or extra axioms in the headline result and production
corollary. They do not discharge the corollary's explicit provenance and observation premises.
-/

/-- info: 'KatLang.CallableIdentityProvenance.same_identity_trans_of_follows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_identity_trans_of_follows

/-- info: 'KatLang.CallableIdentityProvenance.production_head_walk_follows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms production_head_walk_follows

/-- info: 'KatLang.CallableIdentityClosure.use_site_is_a_printer_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms use_site_is_a_printer_fact

/-- info: 'KatLang.CallableIdentityClosure.candidate_identity_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms candidate_identity_trans

/-- info: 'KatLang.CallableIdentityClosure.candidate_eq_production_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms candidate_eq_production_iff

end KatLang.CallableIdentityProvenanceGuards
