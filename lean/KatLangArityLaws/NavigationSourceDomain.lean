import KatLang

open KatLang

/-!
# The static input domain of navigation admissibility (ledger E-18, step 1, B2 preparation)

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
`open` targets, and the property whose body it is):

* `Algorithm.mk` pushes its own level (its parameter names, its properties, its opens);
* `Algorithm.alias` pushes its own level (no parameters, its own properties) — the alias is the head
  when its row is resolved (`resolveAliasStepWith`, `aliasBindingCell`);
* a clause family pushes, for each branch, the BINDER level of the branch's pattern (the family
  scope `wireSelectedBranchBody` publishes: the family's identity and opens, the binders as
  parameters) under the branch body's own level;
* an inline block (`Expr.algorithmExpr`) is an algorithm at its written position (`wireToCaller`).

The prelude level is not on the stack: it binds no parameter and declares only builtins.

## The predicates

* `paramsBound` — every `.param x` occurrence is bound by a level of its stack. (An unbound
  occurrence has no owner: `requiredParameterOwner?` finds none, the read falls to the reading
  context's own tier, and a parameter-row alias over it allocates on every chase.)
* `exposureFull` — a BOUNDED SELECTION EXTENSION of the value-level exposure fragment: for every
  declared member, every enclosing-level input the model collects is among its declared requirements
  (`PropDef.exposure`, at the owner positions of `PropDef.requiredOwnerDepths` when present, else
  the nearest owner of each name), where a row reads
  - a parameter it names (`.param`),
  - what a member a SUPPORTED selection reaches declares: a name on the direct lexical chain
    (`lookupInParentsStructuralProperty`), a STATIC
    DOTTED PATH (`A.B.Q`: each receiver read through its STRUCTURE — a transparent reference is its
    static target, resolved in the reference's own scope, as `openStructure` and the structure
    chase do), and a name an `open` provides (`lookupOpenPropertiesInChain`: the innermost level
    whose open targets provide it publicly, exactly one written hit in the model).

  A selected member's requirement counts at the level its position names. When the reader is not
  inside that level (the selected member's owner is a container's own level the reader is not
  inside), the requirement is not the reader's. A path or an open the MODEL does not resolve
  (a parameter or computed head, `selFuel` exhausted, multiple written open hits) contributes
  nothing. This is an under-approximation, NOT a claim that production refuses the access.
  Production also resolves dotted heads through opens and deduplicates semantic providers, which
  this model omits. The metadata is required to be closed under the modeled rules (a post-fixed
  point), never least; that is not complete member exposure.
* `exposureComplete` — the DIRECT-LEXICAL FRAGMENT of `exposureFull` (no dotted or opened
  selection), kept because the B2 preparation's results are stated over it.
* `exposureDeep` — the direct-lexical closure over the member's WHOLE subtree, the bodies of the
  members it declares and its open targets included: a container that declares a capturing member
  is itself local-only.

A requirement is `(name, depth)`: the parameter and the level that binds it, counted from the
member's DECLARING level (depth 0), as `PropDef.requiredOwnerDepths` counts.

## What is and is not claimed

`SourceDomain` (bound parameters and the bounded selection extension) is a CANDIDATE FRAGMENT,
not the completed static input-domain contract requested by B2 preparation. Its source correspondence
is assumed, not proved: `NavigationSourceDomainGuards` checks it on source-derived trees and rejects
the host-built `MisExposed` tree and the `ExposureFragment` / `OpenedFragment` trees whose dotted or
opened dependency was removed — trees the direct-lexical fragment (`SourceLike`) accepts. It is NOT
proved of the C# front end (`ParameterDetector`, `PropertyExposureResolver`); Lean has no model of
either, and the selection rules above are this module's model of the evaluator's static
selections, checked only against the corpora. `NavigationSourceDomainGuards.SelectionGaps` proves
that exported readers with missing ancestor dependencies are still admitted on three source-valid
routes: a repeated open provider, an open-provided dotted head, and a long reference chain. The
source front end marks their uncorrupted counterparts local-only (`NavigationSourceDomainWitnessTests`).
Full static exposure completeness (the earlier review's F1) therefore remains OPEN.

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
    targets, and the property whose body it is (`none` for a block, a branch body, the root). -/
structure Level where
  params : List Ident
  props : List PropDef
  opens : List Expr := []
  self : Option Ident := none

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

/-! ## Static selection: dotted paths and opened names (the `full` mode) -/

/-- The own level of an algorithm, `self` naming the property whose body it is. -/
def levelOf (self : Option Ident) : Algorithm → Level
  | .mk _ patterns opens props _ _ =>
      { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
        opens := opens, self := self }
  | .alias _ opens props _ _ _ => { params := [], props := props, opens := opens, self := self }
  | .conditional _ opens _ _ => { params := [], props := [], opens := opens, self := self }
  | .builtin _ => { params := [], props := [], self := self }

/-- An algorithm a static selection reaches, located relative to a READER's stack `R`: the property
    whose body it is, the static stack of the level that declares it (its parent chain), for each
    level of that stack its index on `R` when the reader is inside that level, and the index on `R`
    of its OWN level when the reader is inside it. -/
structure Located where
  name : Option Ident
  alg : Algorithm
  stack : Stack
  map : List (Option Nat)
  self : Option Nat

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
    self := insideIndex R (M[i]?.join) p.name }

/-- The member `p` of a located container `c`. -/
def memberOf (R : Stack) (c : Located) (p : PropDef) : Located :=
  { name := some p.name, alg := p.alg, stack := levelOf c.name c.alg :: c.stack, map := c.self :: c.map,
    self := insideIndex R c.self p.name }

mutual
  /-- The STRUCTURE of a located algorithm, statically (`openStructure`, the structure chase): a
      transparent reference is its static target's structure, resolved in the reference's own
      scope; anything else is itself. `none` when the target does not resolve or the fuel ends. -/
  def structureOf (R : Stack) : Nat → Located → Option Located
    | 0, c =>
        match c.alg with
        | .alias _ _ _ _ _ true => none
        | _ => some c
    | .succ fuel, c =>
        match c.alg with
        | .alias _ _ _ target _ true =>
            match Expr.staticAliasPath? target with
            | none => some c
            | some (head, steps) =>
                (walkPath R fuel (levelOf c.name c.alg :: c.stack) (c.self :: c.map) head steps).bind
                  (structureOf R fuel)
        | _ => some c

  /-- A static path with a DIRECT-LEXICAL head in `S` (its levels at `M` on `R`). A head provided
      through an open is not modeled here. -/
  def walkPath (R : Stack) : Nat → Stack → List (Option Nat) → Expr → List Ident → Option Located
    | 0, _, _, _, _ => none
    | .succ fuel, S, M, head, steps =>
        let start : Option Located := match head with
          | .resolve name => (propIndex? S name).map fun found => foundAt R S M found.1 found.2
          | .algorithmExpr block => some { name := none, alg := block, stack := S, map := M, self := none }
          | _ => none
        start.bind (walkSteps R fuel steps)

  /-- The member steps of a static path, each receiver read through its structure. -/
  def walkSteps (R : Stack) : Nat → List Ident → Located → Option Located
    | _, [], c => some c
    | 0, _ :: _, _ => none
    | .succ fuel, m :: rest, c =>
        (structureOf R fuel c).bind fun container =>
          (lookupPropDefAny? (levelOf container.name container.alg).props m).bind fun p =>
            walkSteps R fuel rest (memberOf R container p)
end

/-- Fixed search fuel of the model, not a production limit or a proved completeness bound. -/
def selFuel : Nat := 64

/-- What the reader requires of a member `p` selected from the located container `c`: each
    declared requirement at the level its position names, when the reader is inside that level. -/
def selectedRequirements (inner : Stack) (c : Located) (p : PropDef) : List Requirement :=
  let map := c.self :: c.map
  (declared (levelOf c.name c.alg :: c.stack) p).flatMap fun requirement =>
    match map[requirement.2]?.join with
    | some index => escaping inner requirement.1 index
    | none => []

/-- The member a static DOTTED path selects, and what the reader requires of it. -/
def dottedRequirements (outer inner : Stack) (e : Expr) : List Requirement :=
  let R := inner ++ outer
  match Expr.staticAliasPath? e with
  | none => []
  | some (head, steps) =>
      match steps.reverse with
      | [] => []
      | last :: before =>
          match (walkPath R selFuel R (readerMap R 0) head before.reverse).bind (structureOf R selFuel) with
          | none => []
          | some container =>
              match lookupPropDefAny? (levelOf container.name container.alg).props last with
              | none => []
              | some p => selectedRequirements inner container p

/-- An `open` target of the level at index `k` of `R`, as a provider: a static path resolved from
    that level (`resolveAlgForOpen`: `lookupInParentsDirect` from the level itself), through its
    structure; an inline block is wired at the global scope, which binds nothing. -/
def openProvider (R : Stack) (k : Nat) : Expr → Option Located
  | .algorithmExpr block => some { name := none, alg := block, stack := [], map := [], self := none }
  | e =>
      match Expr.staticAliasPath? e with
      | none => none
      | some (head, steps) =>
          (walkPath R selFuel (R.drop k) (readerMap R k) head steps).bind (structureOf R selFuel)

/-- The modeled open hit for `name` at the levels `levels` (from index `k` of `R`): one written
    target hit at the first level with hits. No provider deduplication: multiple hits return `none`,
    even when production resolves them to one provider (`SelectionGaps` in the guards). -/
def openedAt (R : Stack) (name : Ident) : Nat → Stack → Option (Located × PropDef)
  | _, [] => none
  | k, level :: rest =>
      let hits := level.opens.filterMap fun e =>
        (openProvider R k e).bind fun provider =>
          (lookupPropDefPublic? (levelOf provider.name provider.alg).props name).map fun p => (provider, p)
      match hits with
      | [] => openedAt R name (k + 1) rest
      | [hit] => some hit
      | _ => none

/-- What a name an `open` provides requires of the reader. -/
def openedRequirements (outer inner : Stack) (name : Ident) : List Requirement :=
  let R := inner ++ outer
  match openedAt R name 0 R with
  | none => []
  | some (provider, p) => selectedRequirements inner provider p

/-! ## The walk -/

mutual
  /-- The enclosing-level inputs the expression requires of the levels outside `inner`. An `open`
      target is a NAMESPACE use (`openStructure` reads the target's declarations, never its rows),
      so at the value level it requires nothing itself; with `full`, a name it provides requires
      what the provided member declares. With `deep`, the open targets and the bodies of declared
      members are walked too. -/
  def reqExpr (mode : Mode) (outer inner : Stack) : Expr → List Requirement
    | .param x =>
        match ownerIndex? (inner ++ outer) x with
        | some index => escaping inner x index
        | none => []
    | .resolve name =>
        referenceRequirements outer inner name ++
          (if mode.full && (propIndex? (inner ++ outer) name).isNone then openedRequirements outer inner name
            else [])
    | .num _ => []
    | .stringLiteral _ => []
    | .boolLiteral _ => []
    | .emptySequence _ => []
    | .unary _ e => reqExpr mode outer inner e
    | .binary _ a b => reqExpr mode outer inner a ++ reqExpr mode outer inner b
    | .comparison first links => reqExpr mode outer inner first ++ reqLinks mode outer inner links
    | .index a selectors => reqExpr mode outer inner a ++ reqExprs mode outer inner selectors
    | .sequenceConstruct a b => reqExpr mode outer inner a ++ reqExpr mode outer inner b
    | .sequenceSpread e => reqExpr mode outer inner e
    | .listLiteral items => reqExprs mode outer inner items
    | .capture rows => reqExprs mode outer inner rows
    | .algorithmExpr a => reqAlg mode outer inner none a
    | .call f args => reqExpr mode outer inner f ++ reqExprs mode outer inner args
    | .dotMember target n fallback none =>
        reqExpr mode outer inner target ++ reqExpr mode outer inner fallback ++
          (if mode.full then dottedRequirements outer inner (.dotMember target n fallback none) else [])
    | .dotMember target n fallback (some args) =>
        reqExpr mode outer inner target ++ reqExpr mode outer inner fallback ++ reqExprs mode outer inner args ++
          (if mode.full then dottedRequirements outer inner (.dotMember target n fallback none) else [])

  def reqExprs (mode : Mode) (outer inner : Stack) : List Expr → List Requirement
    | [] => []
    | e :: rest => reqExpr mode outer inner e ++ reqExprs mode outer inner rest

  def reqLinks (mode : Mode) (outer inner : Stack) : List ComparisonLink → List Requirement
    | [] => []
    | ⟨_, operand⟩ :: rest => reqExpr mode outer inner operand ++ reqLinks mode outer inner rest

  /-- The requirements of an algorithm written at the stack `inner ++ outer`; `self` names the
      property whose body it is. -/
  def reqAlg (mode : Mode) (outer inner : Stack) (self : Option Ident) : Algorithm → List Requirement
    | .builtin _ => []
    | .mk _ patterns opens props output _ =>
        let level : Level :=
          { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
            opens := opens, self := self }
        reqExprs mode outer (level :: inner) output ++
          (if mode.deep then reqExprs mode outer (level :: inner) opens ++ reqProps mode outer (level :: inner) props
            else [])
    | .conditional _ opens branches _ =>
        (if mode.deep then reqExprs mode outer ({ params := [], props := [], opens := opens, self := self } :: inner) opens
          else []) ++
          reqBranches mode outer inner self opens branches
    | .alias _ opens props target _ _ =>
        let level : Level := { params := [], props := props, opens := opens, self := self }
        reqExpr mode outer (level :: inner) target ++
          (if mode.deep then reqExprs mode outer (level :: inner) opens ++ reqProps mode outer (level :: inner) props
            else [])

  def reqProps (mode : Mode) (outer inner : Stack) : List PropDef → List Requirement
    | [] => []
    | ⟨name, a, _, _, _, _⟩ :: rest => reqAlg mode outer inner (some name) a ++ reqProps mode outer inner rest

  /-- A family's branches: each body under its binder level, the family's scope. -/
  def reqBranches (mode : Mode) (outer inner : Stack) (self : Option Ident) (opens : List Expr) :
      List CondBranch → List Requirement
    | [] => []
    | ⟨pattern, body⟩ :: rest =>
        reqAlg mode outer ({ params := pattern.boundNames, props := [], opens := opens, self := self } :: inner) none body ++
          reqBranches mode outer inner self opens rest
end

/-- What a traversal of the program checks. -/
inductive Check where
  /-- Every `.param` occurrence is bound by a level of its stack. -/
  | bound
  /-- Every member's declared requirements cover what it requires, in the mode given. -/
  | exposure (mode : Mode)

/-- One member's metadata against what the member requires: every requirement is declared, and
    every declared position names a level that binds the name. -/
def memberExposed (mode : Mode) (stack : Stack) (p : PropDef) : Bool :=
  (reqAlg mode stack [] (some p.name) p.alg).all (fun requirement => (declared stack p).contains requirement) &&
    (declared stack p).all fun requirement =>
      match stack[requirement.2]? with
      | some level => level.params.contains requirement.1
      | none => false

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
    | .mk _ patterns opens props output _ =>
        let level : Level :=
          { params := patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props := props,
            opens := opens, self := self }
        chkExprs check (level :: stack) opens && chkProps check (level :: stack) props &&
          chkExprs check (level :: stack) output
    | .conditional _ opens branches _ =>
        chkExprs check ({ params := [], props := [], opens := opens, self := self } :: stack) opens &&
          chkBranches check stack self opens branches
    | .alias _ opens props target _ _ =>
        let level : Level := { params := [], props := props, opens := opens, self := self }
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
        chkAlg check ({ params := pattern.boundNames, props := [], opens := opens, self := self } :: stack) none body &&
          chkBranches check stack self opens rest
end

/-- **BOUND PARAMETERS.** Every `.param x` occurrence of the program is bound by an enclosing
    parameter list or clause binder. -/
def paramsBound (program : Expr) : Bool := chkExpr .bound [] program

/-- **BOUNDED SELECTION EXTENSION (value level).** Every member declares the enclosing-level
    inputs the model collects from its rows. Despite its historical name, this is NOT full exposure
    completeness: `SelectionGaps` in the guards pins valid selection routes the model omits. -/
def exposureFull (program : Expr) : Bool := chkExpr (.exposure ⟨false, true⟩) [] program

/-- **DIRECT-LEXICAL EXPOSURE CLOSURE (value level)**: `exposureFull` without the dotted and opened
    selections — a necessary fragment, not full completeness (`NavigationSourceDomainGuards.ExposureFragment`). -/
def exposureComplete (program : Expr) : Bool := chkExpr (.exposure ⟨false, false⟩) [] program

/-- **DEEP EXPOSURE.** Every member declares the enclosing-level inputs its whole subtree requires
    on the direct lexical chain: a container that declares a capturing member is itself local-only. -/
def exposureDeep (program : Expr) : Bool := chkExpr (.exposure ⟨true, false⟩) [] program

/-- **CANDIDATE SOURCE-DOMAIN FRAGMENT**: bound parameters and the bounded selection extension.
    C# front-end correspondence is unproved; the predicate also admits incorrectly exposed host
    trees (`NavigationSourceDomainGuards.SelectionGaps`). Full exposure remains an open prerequisite. -/
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
  have hown : ownerIndex? ({ params := [], props := props, opens := opens, self := self } :: stack) y =
      some (k + 1) := by
    simp only [ownerIndex?, hk, Option.map_some]
    rfl
  simp only [reqAlg, reqExpr, escaping, List.singleton_append]
  rw [hown]
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
  rw [Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1 (y, k) (by rw [halg]; exact reqAlg_paramRow mode stack _ _ _ _ y _ _ k hk)
  exact List.elem_iff.mp (by simpa using hall)

end KatLang.NavigationSourceDomain
