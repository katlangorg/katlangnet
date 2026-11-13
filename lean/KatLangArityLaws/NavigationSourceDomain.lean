import KatLang

open KatLang

/-!
# Candidate static input domain of navigation admissibility (ledger E-18, F1 DEFER)

`NavigationContract` reduces "a reachable production navigation is a navigation-core run" to one
per-body obligation of a call contract. The cell clause of that contract rests on STATIC facts of
the evaluated tree which the evaluator's pre-evaluation validation does not check
(`validateExprTree` accepts any `.param`; nothing reads `PropDef.exposure` before evaluation).
This module states binding and exposure as DECIDABLE predicates of a program expression, so that a
theorem can carry them as hypotheses. Nothing here is evaluated by the evaluator, and no evaluator
definition changes: these are predicates ON the input domain, never a rejecting check.

## The static scope stack

A program is walked with the stack of the scope levels the evaluator will wire around each
position, innermost first (`Level`: the names the level binds, the members it declares, its
`open` targets, the property whose body it is, and its static KEY — the path of declaration names
from the program root, the static identity of what it declares):

* `Algorithm.mk` pushes its own level (its parameter names, its properties, its opens); a LOADED
  MODULE (`Algorithm.isModuleRoot`) is rooted at the prelude (`Algorithm.withParent`): its level
  starts a fresh stack;
* `Algorithm.alias` pushes its own level (no parameters, its own properties) — the alias is the head
  when its row is resolved (`resolveAliasStepWith`, `aliasBindingCell`);
* a clause family pushes, for each branch, the BINDER level of the branch's pattern (the family
  scope `wireSelectedBranchBody` publishes: the family's identity and opens, the binders as
  parameters) under the branch body's own level;
* an inline block (`Expr.algorithmExpr`) is an algorithm at its written position (`wireToCaller`).

The prelude level is not on the stack: it binds no parameter and declares only builtins, which the
lookup reaches after every level's own declarations and BEFORE any `open` (`preludeDeclares`).

## The predicates

* `paramsBound` — every `.param x` occurrence is bound by a level of its stack. (An unbound
  occurrence has no owner: `requiredParameterOwner?` finds none, the read falls to the reading
  context's own tier, and a parameter-row alias over it allocates on every chase.)
* `exposureFull` — STATIC EXPOSURE (value level): for every declared member, every
  enclosing-level input collected below is among its declared requirements (`PropDef.exposure`, at
  the owner positions of `PropDef.requiredOwnerDepths` when present, else the nearest owner of each
  name), and every selection on the way is DECIDED. A row reaches
  - a parameter it names (`.param`);
  - what the declaration a NAME selects declares, by the evaluator's full lookup
    (`lookupLexicalPropertyRaw`): the direct lexical chain, then the prelude, then the opens level
    by level (`lookupOpenPropertiesInChain`): at each level the targets' PROVIDERS, each counted once
    by static identity (`dedupKeys`, the static `resolveAllOpens` deduplication: the resolved
    declaration's key, normalized through transparent references, never the spelling; a written
    block keyed by its position); the first level some provider provides the name publicly
    decides — exactly one provider selects its member, two or more select NOTHING
    (`ambiguousOpen`) and the search stops, a target that fails fails the level;
  - what the declaration a STATIC DOTTED PATH selects declares (`resolveDotReceiver?`,
    `selectDotEdge`): the head by the same full lookup, each receiver read through its STRUCTURE
    (`resolveAliasStructure`: a transparent reference is what its target selects in the reference's
    OWN scope by the full lookup, opens included — `staticPathSelectWith` — a carrier is itself, a
    runtime row has none), each step a DECLARED member (private included). The receiver's value is
    not read when the path selects a declaration; an edge that selects none (a structural miss, a
    parameter or computed receiver: the fallback MAY be selected) requires its receiver and its
    fallback.
  - An `open` target is resolved as `resolveOpen` does: a direct-lexical head (`resolveAlgForOpen`),
    PUBLIC steps, the provider read through `openStructure` (a reference's head direct-lexically; a
    carrier, a runtime row, an `.Algorithm` link: its own namespace); a block at the prelude; a
    builtin or argument-requiring provider refused.

  Every selection returns its TRAIL (`Hit`): every declaration the evaluator access-checks on the
  way (`memberAccessible?`) — each member a path step selects (an intermediate one included:
  `Lib.Sub.Q` charges `Sub` and `Q`), the selections of every transparent reference's target walk it
  crosses (made in the reference's own scope, through chains), the providers' walks of EVERY open
  level a lookup consults up to and including the deciding one (`resolveAllOpens` resolves all of a
  level's opens before the name is looked up, so a target that does not provide the name is on the
  trail too), and an open-provided member. A name the owner walk finds, a reference found that way,
  and a block head are not on it: their VALUE is not read when a member is selected. A selected
  member's requirement counts at the level its position names; when the reader is not inside that
  level (the anchoring of a container's chain, `75c3f1f2`), it is not the reader's. This is the
  owner decision of 2026-11-13 (exposure charges exactly the access checks and value reads the
  evaluator performs on static selections), which the C# front end now implements
  (`PropertyExposureResolver`; ledger E-18, F1). The F1 review's R1 (intermediate members dropped)
  and R2 (reference target walks, inline-block heads and consulted open levels under-charged by C#)
  have their functional repairs; the counterfactuals are `NavigationSourceDomainGuards.AccessChecks`.
  The C1 follow-up (2026-11-13) made the C# open-walk charging linear for readers with bound owners
  (one settlement per consulted level) with unchanged metadata, and removed the candidate's I28
  over-charge: opening a runtime reference charges nothing, as `structureOf`'s open mode already gave
  (`AccessChecks.runtimeReferenceOpen_sourceDomain`). No predicate or evaluator rule changed.

  INDEPENDENT C1/I28 REVIEW (2026-11-14): F1 DEFER; exposure acceptance STOPPED. The C1 sharing is
  conditional: scaling the `Lib.Mid.Sub` discharge witness still repeats the walks per reader
  (3,522 / 11,972 / 43,872 settlement frames at widths 25 / 50 / 100). The claimed full selection
  trail also has a counterexample: opening `L = Lib.Sub.Algorithm` on the intrinsic route checks
  `Sub` before reaching the runtime link, but `walkSteps` returns `runtime` without its prefix,
  and `structureOf` in open mode replaces it by an empty trail. Thus `SourceDomain` admits a
  host-built tree whose reader omits that check's requirement. The C# front end correctly charges
  this source, and both evaluators agree. This is a predicate gap, not a language change.
  Evidence: `artifacts/validation/e18-c1-i28-20261114-review/`. The historical closure claim above
  is superseded; this module remains a candidate fragment. C# correspondence is still ASSUMED.

  Runtime-only routes — parameter and computed heads, `.Algorithm` links, runtime reference rows —
  contribute nothing statically (`Sel.runtime`). A chase meeting a key it already passed is the
  alias cycle production refuses (nothing is read), or, deciding an `.Algorithm` row's route, the
  runtime route (`aliasStepIsRuntime`). A selection the model cannot decide — the fuel `selFuel`
  (derived from the program) exhausted — is `Sel.stuck`, and makes the member's check FALSE, never
  "requires nothing". The metadata is required to be closed under these rules (a post-fixed point),
  never least.
* `exposureComplete` — the DIRECT-LEXICAL FRAGMENT (no dotted or opened selection, every dot edge
  charging its receiver and fallback), kept because the B2 preparation's results are stated over it.
* `exposureDeep` — the direct-lexical closure over the member's WHOLE subtree, the bodies of the
  members it declares and its open targets included: a container that declares a capturing member
  is itself local-only.

A requirement is `(name, depth)`: the parameter and the level that binds it, counted from the
member's DECLARING level (depth 0), as `PropDef.requiredOwnerDepths` counts.

## Termination

Every selection function takes fuel; `selFuel R e` is derived from the selection's stack and
expression. The argument: along one recursion path, a value-mode chase passes each transparent
reference at most once (its key joins `visited`; a repeat is the cycle), so at most `A + 1` alias hops,
`A` the alias declarations reachable; between hops it spends one frame on the path, at most
`|S|` frames on the open levels of the head lookup (each level's providers in a fresh open-mode
subtree of at most `(A + 1)(2L + 4) + 1` frames: open targets never consult an open), and at most
`2L + 2` frames on the steps, `L` the longest written path. The trail adds no call: each function
returns what its calls returned, appended, so the recursion and its frame count are unchanged. Reachable declarations lie in the
declarations and open targets of the reader's stack and in the written expression, so `A`, `L` and
every stack length are bounded by `n` (`selFuel`), and `4 n³ + 16` exceeds the count. This
SUFFICIENCY is argued, NOT PROVED: a proof needs the invariant that every located algorithm is a
subterm of the stack's declarations with a key no other alias declaration shares, which the
model does not carry. Exhaustion is fail-closed either way: a selection never silently drops.

## What is and is not claimed

`SourceDomain` (bound parameters and static exposure over every static selection the model covers)
is the static input-domain contract of ledger E-18 F1 (closed 2026-11-13). C# correspondence is
ASSUMED, not proved:
`NavigationSourceDomainGuards` checks it on source-derived trees (C# fidelity tests,
`NavigationSourceDomainWitnessTests`) and rejects host-built trees with a requirement removed on
the guarded routes (`HostBuilt`, `ExposureFragment`, `OpenedFragment`, `SelectionGaps`,
`SelectionRoutes`, `AccessChecks`), and every encoded corpus case satisfies it; Lean has no model of
`ParameterDetector` or `PropertyExposureResolver`, and the selection rules above are this module's
model of the evaluator's static selections, not the evaluator's own lookup functions (those are
monadic over runtime contexts; agreement is the assumption, exercised by the guards).

The parameter-row consequence used by the gate lemma (`NavigationOwnership`): under any exposure
mode, a member whose algorithm is a parameter-row alias `.param y` declares `(y, k)`, `k` the
NEAREST level of its declaring stack that binds `y` (`declared_paramRow`).

Whether `SourceDomain` gives the proposed navigation invariant is NOT proved here. The B2
preparation (2026-11-12) found `SourceLike` source programs on which production reached a
parameter-row alias wired under an UNACTIVATED owner (`OutsideContainer`) and one whose navigation
allocated on every run (`EscapedContainer`); since the anchoring of a container's chain (owner
decision 2026-11-13) both reach an owned member, and the second is re-read
(`NavigationSourceDomainGuards`). Both fail `exposureDeep`; `DeepSourceLike` excludes programs a
front end accepts, so it is a restriction of the source domain, not a description of it.
-/

namespace KatLang.NavigationSourceDomain

/-- One level of the static scope stack: the names it binds, the members it declares, its `open`
    targets, the property whose body it is (`none` for a block, a branch body, the root), and its
    static KEY — the path of declaration names from the program root (an anonymous level is `"#"`),
    the static identity of what it declares (provider identity, alias cycles). -/
structure Level where
  params : List Ident
  props : List PropDef
  opens : List Expr := []
  self : Option Ident := none
  key : List String := []

/-- The static scope stack of a position, innermost level first. -/
abbrev Stack := List Level

/-- A required input of a member: the parameter and the depth of the level that binds it, counted
    from the member's declaring level. -/
abbrev Requirement := Ident × Nat

/-- What a walk collects: `deep` walks declared members' bodies and open targets too; `full` counts
    the dotted and opened selections. -/
structure Mode where
  deep : Bool
  full : Bool

/-- The nearest level of `stack` that binds `name`. -/
def ownerIndex? : Stack → Ident → Option Nat
  | [], _ => none
  | level :: rest, name =>
      if level.params.contains name then some 0 else (ownerIndex? rest name).map (· + 1)

/-- The nearest level of `stack` that declares a property `name`, with that property: the direct
    lexical chain of `lookupLexicalPropertyRaw` (own properties, then the parents'). -/
def propIndex? : Stack → Ident → Option (Nat × PropDef)
  | [], _ => none
  | level :: rest, name =>
      match lookupPropDefAny? level.props name with
      | some p => some (0, p)
      | none => (propIndex? rest name).map (fun found => (found.1 + 1, found.2))

/-- Whether the PRELUDE declares `name`. Every source chain ends at the prelude (a program's root and
    a loaded module are wired under it), and the ownership-first lookup reaches it before any `open`:
    a name it declares is a builtin, never an opened member. -/
def preludeDeclares (name : Ident) : Bool := (Algorithm.lookupPropDefAny? preludeAlg name).isSome

/-- The key of a level pushed on `stack` for the body of `self` (`"#"`: an anonymous level). -/
def childKey (stack : Stack) (self : Option Ident) : List String :=
  (match stack with | level :: _ => level.key | [] => []) ++ [self.getD "#"]

/-- A clause family's level pushed on `stack` (`params` its binders, none for the family's own
    open-target level): the family's identity and opens. -/
def familyLevel (params : List Ident) (opens : List Expr) (self : Option Ident) (stack : Stack) : Level :=
  { params := params, props := [], opens := opens, self := self, key := childKey stack self }

/-- The requirements a member DECLARES, as owner positions from its declaring level (the head of
    `stack`): the retained positions when the tree carries them, else the nearest owner of each
    named input — the convention `memberAccessible?` reads. -/
def declared (stack : Stack) (p : PropDef) : List Requirement :=
  match p.exposure with
  | .exported => []
  | .localConditional => []
  | .localCapturedAncestorParams required =>
      match p.requiredOwnerDepths with
      | some positions => positions.filterMap (fun entry => entry.2.map (fun depth => (entry.1, depth)))
      | none => required.filterMap (fun name => (ownerIndex? stack name).map (fun depth => (name, depth)))

/-- A requirement written at index `index` of the stack `inner ++ outer`, as seen from OUTSIDE
    `inner`: nothing when a level of `inner` supplies it. -/
def escaping (inner : Stack) (name : Ident) (index : Nat) : List Requirement :=
  if index < inner.length then [] else [(name, index - inner.length)]

/-- What a reference to the property `name` requires of the levels outside `inner`: the declared
    requirements of the member the direct lexical chain selects, re-based. A name no level declares
    requires nothing here (see `openedRequirements`). -/
def referenceRequirements (outer inner : Stack) (name : Ident) : List Requirement :=
  match propIndex? (inner ++ outer) name with
  | none => []
  | some (index, p) =>
      (declared ((inner ++ outer).drop index) p).flatMap fun requirement =>
        escaping inner requirement.1 (index + requirement.2)

/-! ## Static selection (the `full` mode) -/

/-- The own level of an algorithm, `key` its static key, `self` naming the property whose body it is. -/
def levelOf (key : List String) (self : Option Ident) : Algorithm → Level
  | .mk _ patterns opens props _ _ =>
      { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
        opens := opens, self := self, key := key }
  | .alias _ opens props _ _ _ => { params := [], props := props, opens := opens, self := self, key := key }
  | .conditional _ opens _ _ => { params := [], props := [], opens := opens, self := self, key := key }
  | .builtin _ => { params := [], props := [], self := self, key := key }

/-- An algorithm a static selection reaches, located relative to a READER's stack `R`: the property
    whose body it is, the static stack of the level that declares it (its parent chain), for each
    level of that stack its index on `R` when the reader is inside that level, the index on `R` of
    its OWN level when the reader is inside it, its static KEY (the declaring level's key and its
    name: the static identity of the declaration, never its spelling), and the declaration. -/
structure Located where
  name : Option Ident
  alg : Algorithm
  stack : Stack
  map : List (Option Nat)
  self : Option Nat
  key : List String := []
  prop : Option PropDef := none

/-- The positions of `R`'s own levels from index `i`. -/
def readerMap (R : Stack) (i : Nat) : List (Option Nat) :=
  (List.range (R.length - i)).map fun k => some (i + k)

/-- The index on `R` of the own level of property `name` declared at index `declaredAt` of `R`: the
    level just inside, when it is that property's body (the reader is inside the property). -/
def insideIndex (R : Stack) (declaredAt : Option Nat) (name : Ident) : Option Nat :=
  match declaredAt with
  | some (.succ k) => if (R[k]?.bind Level.self) = some name then some k else none
  | _ => none

/-- The property `p` found at index `i` of a scope stack `S` whose levels sit at `M` on `R`. -/
def foundAt (R S : Stack) (M : List (Option Nat)) (i : Nat) (p : PropDef) : Located :=
  { name := some p.name, alg := p.alg, stack := S.drop i, map := M.drop i,
    self := insideIndex R (M[i]?.join) p.name,
    key := (match S[i]? with | some level => level.key | none => []) ++ [p.name], prop := some p }

/-- The member `p` of a located container `c`. A LOADED MODULE is rooted at the prelude
    (`Algorithm.withParent`): its members' chain is cut at its own level. -/
def memberOf (R : Stack) (c : Located) (p : PropDef) : Located :=
  let own := levelOf c.key c.name c.alg
  { name := some p.name, alg := p.alg,
    stack := if c.alg.isModuleRoot then [own] else own :: c.stack,
    map := if c.alg.isModuleRoot then [c.self] else c.self :: c.map,
    self := insideIndex R c.self p.name, key := c.key ++ [p.name], prop := some p }

/-- The OUTCOME of a static selection. -/
inductive Sel (α : Type) where
  /-- The selection reaches this. -/
  | found (a : α)
  /-- It selects nothing, as production: a structural miss, an undeclared name, a builtin, or a
      production refusal (an ambiguous open level, a failing open target). -/
  | miss
  /-- Decided only at run time: a parameter or computed receiver, an `.Algorithm` link, a runtime
      reference row. Contributes nothing statically. -/
  | runtime
  /-- The model cannot decide (the fuel ended): the member's check FAILS CLOSED. -/
  | stuck
  deriving Inhabited

/-- What a selection reaches, with its TRAIL: every declaration the evaluator ACCESS-CHECKS on the way
    (`memberAccessible?`), in order — each member a path step selects, the selections of every
    transparent reference's target walk crossed (made in the reference's own scope), the providers'
    walks of every open level a lookup consults (`resolveAllOpens` resolves them all, used or not),
    and the member an open provides. A name the owner walk finds and a block head are not on it: their
    VALUE is not read when a member is selected. -/
structure Hit where
  loc : Located
  trail : List Located

/-- Continue a selection with what it found. -/
def Sel.bind {α β : Type} : Sel α → (α → Sel β) → Sel β
  | .found a, f => f a
  | .miss, _ => .miss
  | .runtime, _ => .runtime
  | .stuck, _ => .stuck

/-- All of a level's providers, or the first outcome that is not one (a stuck provider first:
    fail closed; then a failing target, which fails the whole open level in production). -/
def Sel.all {α : Type} (xs : List (Sel α)) : Sel (List α) :=
  if xs.any (fun x => match x with | .stuck => true | _ => false) then .stuck
  else
    let found := xs.filterMap fun x => match x with | .found a => some a | _ => none
    if found.length = xs.length then .found found else .miss

/-- The hits of one open level, each provider once: by the provider's static KEY (the semantic
    provider identity `resolveAllOpens` deduplicates by — declaration and declaring scope — never the
    written spelling; a written block is keyed by its position). -/
def dedupKeys (seen : List (List String)) : List Located → List Located
  | [] => []
  | x :: rest => if seen.contains x.key then dedupKeys seen rest else x :: dedupKeys (x.key :: seen) rest

/-- The positions of a list's elements. -/
def indexed {α : Type} : Nat → List α → List (α × Nat)
  | _, [] => []
  | i, x :: rest => (x, i) :: indexed (i + 1) rest

/-- What a path's walk reads: a VALUE or alias-target path (the full lookup, opens included, at the
    head; declared members), the target path of a REFERENCE inside `openStructure` (direct-lexical
    head; declared members), or an open TARGET (direct-lexical head; PUBLIC members). -/
inductive Walk where
  | value
  | reference
  | target
  deriving DecidableEq

mutual
  /-- The STRUCTURE of a located algorithm, with the trail of the target walks it crosses. In the value
      mode (`opn = false`) it is the structure chase (`resolveAliasChase false true`): a transparent
      reference is the structure of what its target selects in the reference's own scope
      (`staticPathSelectWith`: the full lookup, opens included), a carrier is itself, a runtime row is
      `runtime`. In the open mode it is `openStructure`: the target's head is resolved direct-lexically
      only, a runtime or non-static target is the reference's own namespace. Every member a target walk
      selects is access-checked (`aliasStepNavigateWith`, `openNavigateWith`), so it joins the trail. A
      key met twice on one chase is the alias cycle production refuses (`miss`), or — deciding an
      `.Algorithm` row's route — the runtime route. -/
  def structureOf (R : Stack) (opn : Bool) : Nat → List (List String) → Located → Sel Hit
    | 0, _, c =>
        match c.alg with
        | .alias _ _ _ _ _ true => .stuck
        | _ => .found ⟨c, []⟩
    | .succ fuel, visited, c =>
        match c.alg with
        | .alias _ _ _ target _ true =>
            -- A repeated key is an alias cycle: production refuses it (`illegalInEval`; in the open
            -- mode `openStructure`'s exhausted fuel), unless it is met deciding an `.Algorithm` row's
            -- route, where every failure is the runtime route (`aliasStepIsRuntime`).
            let failed : Sel Hit := if !opn && target.isRuntimeAliasRow then .runtime else .miss
            if visited.contains c.key then failed
            else
              match Expr.staticAliasPath? target with
              | none => if opn then .found ⟨c, []⟩ else failed
              | some (head, steps) =>
                  match walkPath R (if opn then .reference else .value) fuel (c.key :: visited)
                      (levelOf c.key c.name c.alg :: c.stack) (c.self :: c.map) head steps (c.key ++ ["#target"]) with
                  | .found v =>
                      (structureOf R opn fuel (c.key :: visited) v.loc).bind fun s => .found ⟨s.loc, v.trail ++ s.trail⟩
                  | .runtime => if opn then .found ⟨c, []⟩ else .runtime
                  | .miss => failed
                  | .stuck => .stuck
        | _ => .found ⟨c, []⟩

  /-- A static path from the scope stack `S` (its levels at `M` on `R`): its head — a name by the
      full lookup (`value`: the direct chain, then the prelude, then the opens level by level) or the
      direct chain only (`reference`, `target`), or a block (wired at `S`; an open target's block at
      the prelude) — then its member steps. A head the owner walk finds, and a block head, are not on
      the trail; an opened head is (with the walks of the open levels consulted). -/
  def walkPath (R : Stack) (w : Walk) : Nat → List (List String) → Stack → List (Option Nat) → Expr →
      List Ident → List String → Sel Hit
    | 0, _, _, _, _, _, _ => .stuck
    | .succ fuel, visited, S, M, head, steps, blockKey =>
        let start : Sel Hit :=
          match head with
          | .resolve name =>
              match propIndex? S name with
              | some (i, p) => .found ⟨foundAt R S M i p, []⟩
              | none => if w = .value && !preludeDeclares name then openedAt R fuel name S M else .miss
          | .algorithmExpr block =>
              if w = .target then .found ⟨{ name := none, alg := block, stack := [], map := [], self := none, key := blockKey }, []⟩
              else .found ⟨{ name := none, alg := block, stack := S, map := M, self := none, key := blockKey }, []⟩
          | _ => .miss
        start.bind fun h => (walkSteps R w fuel visited steps h.loc).bind fun s => .found ⟨s.loc, h.trail ++ s.trail⟩

  /-- The member steps of a static path, each receiver read through its structure (the open mode's
      for `reference` and `target`), each selected member on the trail after the target walks its
      receiver's structure crossed. A missing step `Algorithm` is the runtime link (the reference's
      own namespace in the open mode); an open target's step must be public. -/
  def walkSteps (R : Stack) (w : Walk) : Nat → List (List String) → List Ident → Located → Sel Hit
    | _, _, [], c => .found ⟨c, []⟩
    | 0, _, _ :: _, _ => .stuck
    | .succ fuel, visited, m :: rest, c =>
        (structureOf R (w != .value) fuel visited c).bind fun container =>
          match lookupPropDefAny? (levelOf container.loc.key container.loc.name container.loc.alg).props m with
          | some p =>
              if w = .target && !p.isPublic then .miss
              else
                let member := memberOf R container.loc p
                (walkSteps R w fuel visited rest member).bind fun s =>
                  .found ⟨s.loc, container.trail ++ member :: s.trail⟩
          | none => if m == "Algorithm" && w != .target then .runtime else .miss

  /-- The member a name an `open` provides, searched from the levels `S` (at `M` on `R`) outward:
      at each level its targets' PROVIDERS, each once by static identity (`dedupKeys`); the first
      level some provider provides the name publicly decides — one provider selects its member, two
      or more select nothing (`ambiguousOpen`) — and a target that fails fails the level. Every
      provider's walk of every level consulted, up to and including the deciding one, is on the
      trail (`resolveAllOpens` resolves them all before the name is looked up), then the member. -/
  def openedAt (R : Stack) : Nat → Ident → Stack → List (Option Nat) → Sel Hit
    | 0, _, _, _ => .stuck
    | .succ _, _, [], _ => .miss
    | .succ fuel, name, level :: rest, M =>
        match Sel.all ((indexed 0 level.opens).map fun (e, j) => openProvider R fuel (level :: rest) M level.key j e) with
        | .found providers =>
            let walks := providers.flatMap Hit.trail
            match dedupKeys [] (providers.filterMap fun provider =>
                (lookupPropDefPublic? (levelOf provider.loc.key provider.loc.name provider.loc.alg).props name).map
                  (memberOf R provider.loc)) with
            | [] => (openedAt R fuel name rest (M.drop 1)).bind fun h => .found ⟨h.loc, walks ++ h.trail⟩
            | [hit] => .found ⟨hit, walks ++ [hit]⟩
            | _ => .miss
        | .stuck => .stuck
        | _ => .miss

  /-- The provider an `open` target of the level `S` (at `M` on `R`; its key `levelKey`, the target
      the `j`-th) opens (`resolveOpen`), with the trail of its walk: an inline block at the prelude, or
      a static path resolved from that level (`resolveAlgForOpen`), read through `openStructure`; a
      builtin or an argument-requiring provider is refused (`illegalInOpen`). -/
  def openProvider (R : Stack) : Nat → Stack → List (Option Nat) → List String → Nat → Expr → Sel Hit
    | 0, _, _, _, _, _ => .stuck
    | .succ fuel, S, M, levelKey, j, e =>
        let check : Hit → Sel Hit := fun provider =>
          if provider.loc.alg.isBuiltin || provider.loc.alg.requiresArguments then .miss else .found provider
        match e with
        | .algorithmExpr block =>
            check ⟨{ name := none, alg := block, stack := [], map := [], self := none,
                     key := levelKey ++ ["#open" ++ toString j] }, []⟩
        | _ =>
            match Expr.staticAliasPath? e with
            | none => .miss
            | some (head, steps) =>
                ((walkPath R .target fuel [] S M head steps (levelKey ++ ["#open" ++ toString j])).bind fun h =>
                  (structureOf R true fuel [] h.loc).bind fun s => .found ⟨s.loc, h.trail ++ s.trail⟩).bind check
end

/-! ## The fuel, derived from the program -/

mutual
  /-- The SELECTION WEIGHT of an expression: its algorithm nodes and dot edges. -/
  def weightExpr : Expr → Nat
    | .param _ => 0
    | .resolve _ => 0
    | .num _ => 0
    | .stringLiteral _ => 0
    | .boolLiteral _ => 0
    | .emptySequence _ => 0
    | .unary _ e => weightExpr e
    | .binary _ a b => weightExpr a + weightExpr b
    | .comparison first links => weightExpr first + weightLinks links
    | .index a selectors => weightExpr a + weightExprs selectors
    | .sequenceConstruct a b => weightExpr a + weightExpr b
    | .sequenceSpread e => weightExpr e
    | .listLiteral items => weightExprs items
    | .capture rows => weightExprs rows
    | .algorithmExpr a => weightAlg a
    | .call f args => weightExpr f + weightExprs args
    | .dotMember target _ fallback none => 1 + weightExpr target + weightExpr fallback
    | .dotMember target _ fallback (some args) => 1 + weightExpr target + weightExpr fallback + weightExprs args

  def weightExprs : List Expr → Nat
    | [] => 0
    | e :: rest => weightExpr e + weightExprs rest

  def weightLinks : List ComparisonLink → Nat
    | [] => 0
    | ⟨_, operand⟩ :: rest => weightExpr operand + weightLinks rest

  def weightAlg : Algorithm → Nat
    | .builtin _ => 1
    | .mk _ _ opens props output _ => 1 + weightExprs opens + weightProps props + weightExprs output
    | .conditional _ opens branches _ => 1 + weightExprs opens + weightBranches branches
    | .alias _ opens props target _ _ => 1 + weightExprs opens + weightProps props + weightExpr target

  def weightProps : List PropDef → Nat
    | [] => 0
    | ⟨_, a, _, _, _, _⟩ :: rest => weightAlg a + weightProps rest

  def weightBranches : List CondBranch → Nat
    | [] => 0
    | ⟨_, body⟩ :: rest => weightAlg body + weightBranches rest
end

/-- **THE SELECTION FUEL** of a selection written as `e` at the stack `R`, derived from the program:
    with `n` the levels of `R` plus the weight (algorithm nodes and dot edges) of every declaration
    and `open` target of `R` and of `e` — a bound on the alias declarations `A`, the path length `L`
    and the length of any stack a selection can build — `4 n³ + 16`, above the frame count of the
    module note's termination argument. Exhaustion is `stuck`: the member's check fails, never
    "requires nothing". -/
def selFuel (R : Stack) (e : Expr) : Nat :=
  let n := (R.map fun level => weightProps level.props + weightExprs level.opens + 1).sum + weightExpr e + 2
  4 * n * n * n + 16

/-! ## Requirements of a selection -/

/-- What the reader (inside `inner`) requires of a selected declaration `L`: each declared requirement
    at the level its position names, when the reader is inside that level. A block requires nothing. -/
def selectedRequirements (inner : Stack) (L : Located) : List Requirement :=
  match L.prop with
  | none => []
  | some p =>
      (declared L.stack p).flatMap fun requirement =>
        match L.map[requirement.2]?.join with
        | some index => escaping inner requirement.1 index
        | none => []

/-- What a walk collects: the requirements, and whether every selection was DECIDED (`false` when
    one is `stuck`: the check fails closed). -/
abbrev Reqs := List Requirement × Bool

/-- Two collections, together. -/
def Reqs.cat (a b : Reqs) : Reqs := (a.1 ++ b.1, a.2 && b.2)

/-- A selection's requirements as a collection: nothing selected requires nothing, `stuck` is undecided. -/
def Reqs.ofSel : Sel (List Requirement) → Reqs
  | .found requirements => (requirements, true)
  | .miss => ([], true)
  | .runtime => ([], true)
  | .stuck => ([], false)

/-- What the reader requires of every declaration a selection's trail access-checks. -/
def trailRequirements (inner : Stack) (h : Hit) : List Requirement :=
  h.trail.flatMap (selectedRequirements inner)

/-- What a static DOTTED path (value position, argumentless edge) requires of the reader: every
    declaration its selection access-checks — each member of the path, the target-walk selections
    of every reference it crosses, an opened head with the walks of the open levels consulted;
    `miss`/`runtime` when it selects no declaration. -/
def dottedRequirements (outer inner : Stack) (e : Expr) : Sel (List Requirement) :=
  let R := inner ++ outer
  match Expr.staticAliasPath? e with
  | none => .miss
  | some (head, steps) =>
      (walkPath R .value (selFuel R e) [] R (readerMap R 0) head steps (childKey R (some "#block"))).bind
        fun h => .found (trailRequirements inner h)

/-- What a name an `open` provides requires of the reader: the provided member and the walks of
    every open level the lookup consulted. -/
def openedRequirements (outer inner : Stack) (name : Ident) : Sel (List Requirement) :=
  let R := inner ++ outer
  (openedAt R (selFuel R (.resolve name)) name R (readerMap R 0)).bind
    fun h => .found (trailRequirements inner h)

/-- The requirements of a dot edge's selection (`full` mode): the selected declaration's only, or —
    when the edge selects none — its receiver's and its fallback's (`receiverAndFallback`). -/
def dotRequirements (outer inner : Stack) (e : Expr) (receiverAndFallback : Reqs) : Reqs :=
  match dottedRequirements outer inner e with
  | .found requirements => (requirements, true)
  | .stuck => ([], false)
  | _ => receiverAndFallback

/-! ## The walk -/

mutual
  /-- The enclosing-level inputs the expression requires of the levels outside `inner`, and whether
      every selection was decided. An `open` target is a NAMESPACE use (`openStructure` reads the
      target's declarations, never its rows), so at the value level it requires nothing itself. With
      `full`, a name requires what the declaration the full lookup selects declares (an opened one
      included), and a dot edge whose static path selects a declaration requires that declaration
      ONLY — the evaluator reads the selected member, never the receiver's value — while an edge
      selecting nothing (a miss, a runtime receiver: the fallback MAY be selected) requires its
      receiver and its fallback. With `deep`, the open targets and the bodies of declared members
      are walked too. A loaded module sees nothing outside itself. -/
  def collectExpr (mode : Mode) (outer inner : Stack) : Expr → Reqs
    | .param x =>
        match ownerIndex? (inner ++ outer) x with
        | some index => (escaping inner x index, true)
        | none => ([], true)
    | .resolve name =>
        Reqs.cat (referenceRequirements outer inner name, true)
          (if mode.full && (propIndex? (inner ++ outer) name).isNone && !preludeDeclares name then
            Reqs.ofSel (openedRequirements outer inner name)
          else ([], true))
    | .num _ => ([], true)
    | .stringLiteral _ => ([], true)
    | .boolLiteral _ => ([], true)
    | .emptySequence _ => ([], true)
    | .unary _ e => collectExpr mode outer inner e
    | .binary _ a b => Reqs.cat (collectExpr mode outer inner a) (collectExpr mode outer inner b)
    | .comparison first links => Reqs.cat (collectExpr mode outer inner first) (collectLinks mode outer inner links)
    | .index a selectors => Reqs.cat (collectExpr mode outer inner a) (collectExprs mode outer inner selectors)
    | .sequenceConstruct a b => Reqs.cat (collectExpr mode outer inner a) (collectExpr mode outer inner b)
    | .sequenceSpread e => collectExpr mode outer inner e
    | .listLiteral items => collectExprs mode outer inner items
    | .capture rows => collectExprs mode outer inner rows
    | .algorithmExpr a => collectAlg mode outer inner none a
    | .call f args => Reqs.cat (collectExpr mode outer inner f) (collectExprs mode outer inner args)
    | .dotMember target n fallback none =>
        let receiverAndFallback := Reqs.cat (collectExpr mode outer inner target) (collectExpr mode outer inner fallback)
        if mode.full then dotRequirements outer inner (.dotMember target n fallback none) receiverAndFallback
        else receiverAndFallback
    | .dotMember target n fallback (some args) =>
        let receiverAndFallback := Reqs.cat (collectExpr mode outer inner target) (collectExpr mode outer inner fallback)
        Reqs.cat
          (if mode.full then dotRequirements outer inner (.dotMember target n fallback none) receiverAndFallback
          else receiverAndFallback)
          (collectExprs mode outer inner args)

  def collectExprs (mode : Mode) (outer inner : Stack) : List Expr → Reqs
    | [] => ([], true)
    | e :: rest => Reqs.cat (collectExpr mode outer inner e) (collectExprs mode outer inner rest)

  def collectLinks (mode : Mode) (outer inner : Stack) : List ComparisonLink → Reqs
    | [] => ([], true)
    | ⟨_, operand⟩ :: rest => Reqs.cat (collectExpr mode outer inner operand) (collectLinks mode outer inner rest)

  /-- The requirements of an algorithm written at the stack `inner ++ outer`; `self` names the
      property whose body it is. A loaded module's chain is cut at its own level. -/
  def collectAlg (mode : Mode) (outer inner : Stack) (self : Option Ident) : Algorithm → Reqs
    | .builtin _ => ([], true)
    | a@(.mk _ patterns opens props output _) =>
        let level : Level :=
          { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
            opens := opens, self := self, key := childKey (inner ++ outer) self }
        let outer' := if a.isModuleRoot then [] else outer
        let inner' := if a.isModuleRoot then [] else inner
        Reqs.cat (collectExprs mode outer' (level :: inner') output)
          (if mode.deep then
            Reqs.cat (collectExprs mode outer' (level :: inner') opens) (collectProps mode outer' (level :: inner') props)
          else ([], true))
    | .conditional _ opens branches _ =>
        Reqs.cat
          (if mode.deep then collectExprs mode outer (familyLevel [] opens self (inner ++ outer) :: inner) opens
          else ([], true))
          (collectBranches mode outer inner self opens branches)
    | .alias _ opens props target _ _ =>
        let level : Level :=
          { params := [], props := props, opens := opens, self := self, key := childKey (inner ++ outer) self }
        Reqs.cat (collectExpr mode outer (level :: inner) target)
          (if mode.deep then
            Reqs.cat (collectExprs mode outer (level :: inner) opens) (collectProps mode outer (level :: inner) props)
          else ([], true))

  def collectProps (mode : Mode) (outer inner : Stack) : List PropDef → Reqs
    | [] => ([], true)
    | ⟨name, a, _, _, _, _⟩ :: rest => Reqs.cat (collectAlg mode outer inner (some name) a) (collectProps mode outer inner rest)

  /-- A family's branches: each body under its binder level, the family's scope. -/
  def collectBranches (mode : Mode) (outer inner : Stack) (self : Option Ident) (opens : List Expr) :
      List CondBranch → Reqs
    | [] => ([], true)
    | ⟨pattern, body⟩ :: rest =>
        Reqs.cat
          (collectAlg mode outer (familyLevel pattern.boundNames opens self (inner ++ outer) :: inner) none body)
          (collectBranches mode outer inner self opens rest)
end

/-- The enclosing-level inputs an expression requires (`collectExpr`'s requirements). -/
def reqExpr (mode : Mode) (outer inner : Stack) (e : Expr) : List Requirement := (collectExpr mode outer inner e).1

/-- The enclosing-level inputs an algorithm requires (`collectAlg`'s requirements). -/
def reqAlg (mode : Mode) (outer inner : Stack) (self : Option Ident) (a : Algorithm) : List Requirement :=
  (collectAlg mode outer inner self a).1

/-- What a traversal of the program checks. -/
inductive Check where
  /-- Every `.param` occurrence is bound by a level of its stack. -/
  | bound
  /-- Every member's declared requirements cover what it requires, in the mode given. -/
  | exposure (mode : Mode)

/-- One member's metadata against what the member requires: every selection is decided, every
    requirement is declared, and every declared position names a level that binds the name. -/
def memberExposed (mode : Mode) (stack : Stack) (p : PropDef) : Bool :=
  (collectAlg mode stack [] (some p.name) p.alg).2 &&
    ((reqAlg mode stack [] (some p.name) p.alg).all (fun requirement => (declared stack p).contains requirement) &&
      (declared stack p).all fun requirement =>
        match stack[requirement.2]? with
        | some level => level.params.contains requirement.1
        | none => false)

mutual
  def chkExpr (check : Check) (stack : Stack) : Expr → Bool
    | .param x =>
        match check with
        | .bound => (ownerIndex? stack x).isSome
        | .exposure _ => true
    | .resolve _ => true
    | .num _ => true
    | .stringLiteral _ => true
    | .boolLiteral _ => true
    | .emptySequence _ => true
    | .unary _ e => chkExpr check stack e
    | .binary _ a b => chkExpr check stack a && chkExpr check stack b
    | .comparison first links => chkExpr check stack first && chkLinks check stack links
    | .index a selectors => chkExpr check stack a && chkExprs check stack selectors
    | .sequenceConstruct a b => chkExpr check stack a && chkExpr check stack b
    | .sequenceSpread e => chkExpr check stack e
    | .listLiteral items => chkExprs check stack items
    | .capture rows => chkExprs check stack rows
    | .algorithmExpr a => chkAlg check stack none a
    | .call f args => chkExpr check stack f && chkExprs check stack args
    | .dotMember target _ fallback none => chkExpr check stack target && chkExpr check stack fallback
    | .dotMember target _ fallback (some args) =>
        chkExpr check stack target && chkExpr check stack fallback && chkExprs check stack args

  def chkExprs (check : Check) (stack : Stack) : List Expr → Bool
    | [] => true
    | e :: rest => chkExpr check stack e && chkExprs check stack rest

  def chkLinks (check : Check) (stack : Stack) : List ComparisonLink → Bool
    | [] => true
    | ⟨_, operand⟩ :: rest => chkExpr check stack operand && chkLinks check stack rest

  def chkAlg (check : Check) (stack : Stack) (self : Option Ident) : Algorithm → Bool
    | .builtin _ => true
    | a@(.mk _ patterns opens props output _) =>
        let level : Level :=
          { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
            opens := opens, self := self, key := childKey stack self }
        let stack' := if a.isModuleRoot then [] else stack
        chkExprs check (level :: stack') opens && chkProps check (level :: stack') props &&
          chkExprs check (level :: stack') output
    | .conditional _ opens branches _ =>
        chkExprs check (familyLevel [] opens self stack :: stack) opens &&
          chkBranches check stack self opens branches
    | .alias _ opens props target _ _ =>
        let level : Level := { params := [], props := props, opens := opens, self := self, key := childKey stack self }
        chkExprs check (level :: stack) opens && chkProps check (level :: stack) props &&
          chkExpr check (level :: stack) target

  /-- The members a level declares, each in that level's stack. -/
  def chkProps (check : Check) (stack : Stack) : List PropDef → Bool
    | [] => true
    | ⟨name, a, isPublic, exposure, identity, positions⟩ :: rest =>
        chkAlg check stack (some name) a &&
          (match check with
            | .bound => true
            | .exposure mode => memberExposed mode stack ⟨name, a, isPublic, exposure, identity, positions⟩) &&
          chkProps check stack rest

  def chkBranches (check : Check) (stack : Stack) (self : Option Ident) (opens : List Expr) :
      List CondBranch → Bool
    | [] => true
    | ⟨pattern, body⟩ :: rest =>
        chkAlg check (familyLevel pattern.boundNames opens self stack :: stack) none body &&
          chkBranches check stack self opens rest
end

/-- **BOUND PARAMETERS.** Every `.param x` occurrence of the program is bound by an enclosing
    parameter list or clause binder. -/
def paramsBound (program : Expr) : Bool := chkExpr .bound [] program

/-- **STATIC EXPOSURE (value level).** Every member declares the enclosing-level inputs collected
    by the selection model: every declaration a static selection access-checks (its trail) and every
    value it reads. Fuel exhaustion fails closed. -/
def exposureFull (program : Expr) : Bool := chkExpr (.exposure ⟨false, true⟩) [] program

/-- **DIRECT-LEXICAL EXPOSURE CLOSURE (value level)**: no dotted or opened selection, every dot edge
    charging its receiver and fallback — a fragment, not full completeness
    (`NavigationSourceDomainGuards.ExposureFragment`). -/
def exposureComplete (program : Expr) : Bool := chkExpr (.exposure ⟨false, false⟩) [] program

/-- **DEEP EXPOSURE.** Every member declares the enclosing-level inputs its whole subtree requires
    on the direct lexical chain: a container that declares a capturing member is itself local-only. -/
def exposureDeep (program : Expr) : Bool := chkExpr (.exposure ⟨true, false⟩) [] program

/-- **STATIC SOURCE DOMAIN**: bound parameters and static exposure. C# correspondence is ASSUMED,
    not proved; model/evaluator agreement and fuel sufficiency are argued (module note). -/
structure SourceDomain (program : Expr) : Prop where
  bound : paramsBound program = true
  exposed : exposureFull program = true

/-- The direct-lexical FRAGMENT of the source domain (the B2 preparation's `SourceLike`). -/
structure SourceLike (program : Expr) : Prop where
  bound : paramsBound program = true
  exposed : exposureComplete program = true

/-- The RESTRICTED domain: bound parameters and deep exposure. It excludes programs a source front
    end accepts (`NavigationSourceDomainGuards.OutsideContainer`). -/
structure DeepSourceLike (program : Expr) : Prop where
  bound : paramsBound program = true
  exposed : exposureDeep program = true

instance (program : Expr) : Decidable (SourceDomain program) :=
  if hb : paramsBound program = true then
    if he : exposureFull program = true then isTrue ⟨hb, he⟩
    else isFalse (fun h => he h.exposed)
  else isFalse (fun h => hb h.bound)

instance (program : Expr) : Decidable (SourceLike program) :=
  if hb : paramsBound program = true then
    if he : exposureComplete program = true then isTrue ⟨hb, he⟩
    else isFalse (fun h => he h.exposed)
  else isFalse (fun h => hb h.bound)

instance (program : Expr) : Decidable (DeepSourceLike program) :=
  if hb : paramsBound program = true then
    if he : exposureDeep program = true then isTrue ⟨hb, he⟩
    else isFalse (fun h => he h.exposed)
  else isFalse (fun h => hb h.bound)

/-! ## The parameter-row consequence -/

/-- What a parameter-row alias requires, in every mode: its row's parameter, at the NEAREST level
    of its declaring stack that binds it. -/
theorem reqAlg_paramRow (mode : Mode) (stack : Stack) (self : Option Ident) (parent : Option ScopeCtx)
    (opens : List Expr) (props : List PropDef) (y : Ident) (id : Option PropertyIdentity) (reference : Bool)
    (k : Nat) (hk : ownerIndex? stack y = some k) :
    (y, k) ∈ reqAlg mode stack [] self (.alias parent opens props (.param y) id reference) := by
  have hown : ∀ key : List String,
      ownerIndex? ({ params := [], props := props, opens := opens, self := self, key := key } :: stack) y =
        some (k + 1) := by
    intro key
    simp only [ownerIndex?, hk, Option.map_some]
    rfl
  simp only [reqAlg, collectAlg, collectExpr, Reqs.cat, escaping, List.singleton_append, hown]
  simp

/-- **THE PARAMETER-ROW CONSEQUENCE OF EXPOSURE.** A member whose algorithm is a parameter-row alias
    and whose metadata passes `memberExposed` (any mode) declares its row's parameter at the nearest
    level of its declaring stack that binds it. -/
theorem declared_paramRow {mode : Mode} {stack : Stack} {p : PropDef} (h : memberExposed mode stack p = true)
    {parent : Option ScopeCtx} {opens : List Expr} {props : List PropDef} {y : Ident}
    {id : Option PropertyIdentity} {reference : Bool}
    (halg : p.alg = .alias parent opens props (.param y) id reference) {k : Nat}
    (hk : ownerIndex? stack y = some k) : (y, k) ∈ declared stack p := by
  unfold memberExposed at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.2.1 (y, k) (by rw [halg]; exact reqAlg_paramRow mode stack _ _ _ _ y _ _ k hk)
  exact List.elem_iff.mp (by simpa using hall)

end KatLang.NavigationSourceDomain
