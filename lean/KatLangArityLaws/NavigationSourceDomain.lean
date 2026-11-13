import KatLang

open KatLang

/-!
# The static input domain of navigation admissibility (ledger E-18, step 1, B2 preparation)

`NavigationContract` reduces "a reachable production navigation is a navigation-core run" to one
per-body obligation of a call contract. The cell clause of that contract rests on STATIC facts of
the evaluated tree which the evaluator's pre-evaluation validation does not check
(`validateExprTree` accepts any `.param`; nothing reads `PropDef.exposure` before evaluation).
This module states binding and a DECIDABLE DIRECT-LEXICAL FRAGMENT of exposure as predicates of a
program expression, so that a theorem can carry them as hypotheses. It does not yet formalize full
exposure completeness: selected dotted and opened members' dependencies are missing
(`NavigationSourceDomainGuards.ExposureFragment`). Nothing here is evaluated by the evaluator, and no evaluator
definition changes: these are predicates ON the input domain, never a rejecting check.

## The static scope stack

A program is walked with the stack of the scope levels the evaluator will wire around each
position, innermost first (`Level`: the names the level binds, the members it declares):

* `Algorithm.mk` pushes its own level (its parameter names, its properties);
* `Algorithm.alias` pushes its own level (no parameters, its own properties) — the alias is the head
  when its row is resolved (`resolveAliasStepWith`, `aliasBindingCell`);
* a clause family pushes, for each branch, the BINDER level of the branch's pattern (the family
  scope `wireSelectedBranchBody` publishes) under the branch body's own level;
* an inline block (`Expr.algorithmExpr`) is an algorithm at its written position (`wireToCaller`).

The prelude level is not on the stack: it binds no parameter and declares only builtins.

## The three predicates

* `paramsBound` — every `.param x` occurrence is bound by a level of its stack. (An unbound
  occurrence has no owner: `requiredParameterOwner?` finds none, the read falls to the reading
  context's own tier, and a parameter-row alias over it allocates on every chase.)
* `exposureComplete` — DIRECT-LEXICAL VALUE-level closure of the exposure metadata: for every declared
  member, every enclosing-level parameter its ROWS read — directly, or through a member its rows
  reference by name on the direct lexical chain (that member's declared requirements) — is among
  the member's declared requirements (`PropDef.exposure`, with the owner positions of
  `PropDef.requiredOwnerDepths` when present, else the nearest owner of each name). The metadata is
  only required to be CLOSED under these rules (a post-fixed point), never to be least.
* `exposureDeep` — the same closure over the member's WHOLE subtree, the bodies of the members it
  declares included: a container that declares a capturing member is itself local-only.

A requirement is `(name, depth)`: the parameter and the level that binds it, counted from the
member's DECLARING level (depth 0), as `PropDef.requiredOwnerDepths` counts.

## What is and is not claimed

`SourceLike` (bound parameters and the direct-lexical exposure fragment) is a necessary domain a SOURCE front end is
ASSUMED to produce: `NavigationSourceDomainGuards` checks it on source-derived trees, and shows
it false on the host-built `MisExposed` tree. It is NOT proved of the C# front end
(`ParameterDetector`, `PropertyExposureResolver`); Lean has no model of either.

It is not a sufficient certificate of correct exposure, even on a host tree whose parameters are
bound: the `ExposureFragment` witness passes it after a dotted dependency's requirement is removed.
The name `exposureComplete` refers only to its stated closure rules; full static exposure remains
an unresolved input-domain obligation, including selection through opens and dotted paths.

Whether `SourceLike` gives the proposed navigation invariant is NOT proved here. The B2 preparation
(2026-11-12) found source programs on which production reached a parameter-row alias wired under an
UNACTIVATED owner (`OutsideContainer`) and one whose navigation allocated on every run
(`EscapedContainer`); since the anchoring of a container's chain (owner decision 2026-11-13) both
reach an owned member, and the second is re-read (`NavigationSourceDomainGuards`). Both satisfy
`SourceLike` and fail `exposureDeep`; `DeepSourceLike` excludes programs a front end accepts, so it
is a restriction of the source domain, not a description of it.
-/

namespace KatLang.NavigationSourceDomain

/-- One level of the static scope stack: the names it binds and the members it declares. -/
structure Level where
  params : List Ident
  props : List PropDef

/-- The static scope stack of a position, innermost level first. -/
abbrev Stack := List Level

/-- A required input of a member: the parameter and the depth of the level that binds it, counted
    from the member's declaring level. -/
abbrev Requirement := Ident × Nat

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
    (a builtin, an opened name — whose member is checked for accessibility when it is read) requires
    nothing here. -/
def referenceRequirements (outer inner : Stack) (name : Ident) : List Requirement :=
  match propIndex? (inner ++ outer) name with
  | none => []
  | some (index, p) =>
      (declared ((inner ++ outer).drop index) p).flatMap fun requirement =>
        escaping inner requirement.1 (index + requirement.2)

mutual
  /-- The enclosing-level inputs the expression requires of the levels outside `inner`. An `open`
      target is a NAMESPACE use (`openStructure` reads the target's declarations, never its rows; the
      member an opened name selects is checked for accessibility where it is read), so at the value
      level it requires nothing. With `deep`, the open targets and the bodies of declared members
      are walked too. -/
  def reqExpr (deep : Bool) (outer inner : Stack) : Expr → List Requirement
    | .param x =>
        match ownerIndex? (inner ++ outer) x with
        | some index => escaping inner x index
        | none => []
    | .resolve name => referenceRequirements outer inner name
    | .num _ => []
    | .stringLiteral _ => []
    | .boolLiteral _ => []
    | .emptySequence _ => []
    | .unary _ e => reqExpr deep outer inner e
    | .binary _ a b => reqExpr deep outer inner a ++ reqExpr deep outer inner b
    | .comparison first links => reqExpr deep outer inner first ++ reqLinks deep outer inner links
    | .index a selectors => reqExpr deep outer inner a ++ reqExprs deep outer inner selectors
    | .sequenceConstruct a b => reqExpr deep outer inner a ++ reqExpr deep outer inner b
    | .sequenceSpread e => reqExpr deep outer inner e
    | .listLiteral items => reqExprs deep outer inner items
    | .capture rows => reqExprs deep outer inner rows
    | .algorithmExpr a => reqAlg deep outer inner a
    | .call f args => reqExpr deep outer inner f ++ reqExprs deep outer inner args
    | .dotMember target _ fallback none => reqExpr deep outer inner target ++ reqExpr deep outer inner fallback
    | .dotMember target _ fallback (some args) =>
        reqExpr deep outer inner target ++ reqExpr deep outer inner fallback ++ reqExprs deep outer inner args

  def reqExprs (deep : Bool) (outer inner : Stack) : List Expr → List Requirement
    | [] => []
    | e :: rest => reqExpr deep outer inner e ++ reqExprs deep outer inner rest

  def reqLinks (deep : Bool) (outer inner : Stack) : List ComparisonLink → List Requirement
    | [] => []
    | ⟨_, operand⟩ :: rest => reqExpr deep outer inner operand ++ reqLinks deep outer inner rest

  def reqAlg (deep : Bool) (outer inner : Stack) : Algorithm → List Requirement
    | .builtin _ => []
    | .mk _ patterns opens props output _ =>
        let level : Level := ⟨patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props⟩
        reqExprs deep outer (level :: inner) output ++
          (if deep then reqExprs deep outer (level :: inner) opens ++ reqProps deep outer (level :: inner) props
            else [])
    | .conditional _ opens branches _ =>
        (if deep then reqExprs deep outer (⟨[], []⟩ :: inner) opens else []) ++
          reqBranches deep outer inner branches
    | .alias _ opens props target _ _ =>
        let level : Level := ⟨[], props⟩
        reqExpr deep outer (level :: inner) target ++
          (if deep then reqExprs deep outer (level :: inner) opens ++ reqProps deep outer (level :: inner) props
            else [])

  def reqProps (deep : Bool) (outer inner : Stack) : List PropDef → List Requirement
    | [] => []
    | ⟨_, a, _, _, _, _⟩ :: rest => reqAlg deep outer inner a ++ reqProps deep outer inner rest

  def reqBranches (deep : Bool) (outer inner : Stack) : List CondBranch → List Requirement
    | [] => []
    | ⟨pattern, body⟩ :: rest =>
        reqAlg deep outer (⟨pattern.boundNames, []⟩ :: inner) body ++ reqBranches deep outer inner rest
end

/-- What a traversal of the program checks. -/
inductive Check where
  /-- Every `.param` occurrence is bound by a level of its stack. -/
  | bound
  /-- Every member's declared requirements cover what it requires (`deep`: of its whole subtree). -/
  | exposure (deep : Bool)

/-- One member's metadata against what the member requires: every requirement is declared, and
    every declared position names a level that binds the name. -/
def memberExposed (deep : Bool) (stack : Stack) (p : PropDef) : Bool :=
  (reqAlg deep stack [] p.alg).all (fun requirement => (declared stack p).contains requirement) &&
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
    | .algorithmExpr a => chkAlg check stack a
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

  def chkAlg (check : Check) (stack : Stack) : Algorithm → Bool
    | .builtin _ => true
    | .mk _ patterns opens props output _ =>
        let level : Level := ⟨patterns.flatMap (fun pattern => pattern.captures.map (·.name)), props⟩
        chkExprs check (level :: stack) opens && chkProps check (level :: stack) props &&
          chkExprs check (level :: stack) output
    | .conditional _ opens branches _ =>
        chkExprs check (⟨[], []⟩ :: stack) opens && chkBranches check stack branches
    | .alias _ opens props target _ _ =>
        let level : Level := ⟨[], props⟩
        chkExprs check (level :: stack) opens && chkProps check (level :: stack) props &&
          chkExpr check (level :: stack) target

  /-- The members a level declares, each in that level's stack. -/
  def chkProps (check : Check) (stack : Stack) : List PropDef → Bool
    | [] => true
    | ⟨name, a, isPublic, exposure, identity, positions⟩ :: rest =>
        chkAlg check stack a &&
          (match check with
            | .bound => true
            | .exposure deep => memberExposed deep stack ⟨name, a, isPublic, exposure, identity, positions⟩) &&
          chkProps check stack rest

  def chkBranches (check : Check) (stack : Stack) : List CondBranch → Bool
    | [] => true
    | ⟨pattern, body⟩ :: rest =>
        chkAlg check (⟨pattern.boundNames, []⟩ :: stack) body && chkBranches check stack rest
end

/-- **BOUND PARAMETERS.** Every `.param x` occurrence of the program is bound by an enclosing
    parameter list or clause binder. -/
def paramsBound (program : Expr) : Bool := chkExpr .bound [] program

/-- **DIRECT-LEXICAL EXPOSURE CLOSURE (value level).** Every member declares the enclosing-level inputs
    collected by `reqAlg`, transitively through the members referenced on the direct lexical chain.
    Selected dotted/opened member requirements are not collected; this is not full completeness. -/
def exposureComplete (program : Expr) : Bool := chkExpr (.exposure false) [] program

/-- **DEEP EXPOSURE.** Every member declares the enclosing-level inputs its whole subtree requires:
    a container that declares a capturing member is itself local-only. -/
def exposureDeep (program : Expr) : Bool := chkExpr (.exposure true) [] program

/-- **THE ASSUMED SOURCE-DOMAIN FRAGMENT**: bound parameters and direct-lexical exposure closure.
    The C# front end is assumed, not proved, to produce it; full exposure needs a stronger predicate. -/
structure SourceLike (program : Expr) : Prop where
  bound : paramsBound program = true
  exposed : exposureComplete program = true

/-- The RESTRICTED domain: bound parameters and deep exposure. It excludes programs a source front
    end accepts (`NavigationSourceDomainGuards.OutsideContainer`). -/
structure DeepSourceLike (program : Expr) : Prop where
  bound : paramsBound program = true
  exposed : exposureDeep program = true

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

end KatLang.NavigationSourceDomain
