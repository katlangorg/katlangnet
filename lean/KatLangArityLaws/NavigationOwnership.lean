import KatLangArityLaws.NavigationSourceDomain
import KatLangArityLaws.NavigationWiring

open KatLang KatLang.NavigationContract KatLang.NavigationSourceDomain

/-!
# Where the cell clause comes from: the local-only premise, STATED (ledger E-18, step 1, B2 preparation)

`NavigationContract`'s cell clause asks every chased parameter-row alias to be `ParamRowOwned`: the
nearest level of its own chain that binds the row's parameter is ACTIVATED. The B2 preparation
(2026-11-12) found it false on source programs; the anchoring of a container's chain (owner
decision 2026-11-13) added an OWNER-ACTIVATED GATE to `memberAccessible?` (each required owner,
read on the container's chain in context — the chain the member is then wired under — must be
activated). This module states the premise under which that gate gives the cell clause, and the
invariant B2 would keep for the routes no gate checks.

## 1. Member selection: the gate gives the cell clause (`paramRowOwned_of_exposed`)

A member `p` of `container`, accessible from `ctx`, whose algorithm is a parameter-row alias
`.param y`, is wired by `childOfInContext` under `sc := scopeInContext container ctx`. It is owned
when

* STATIC: its metadata passes the exposure check at its declaring stack `S`
  (`NavigationSourceDomain.memberExposed`, any mode), so it declares `(y, k)` with `k` the nearest
  level of `S` binding `y` (`NavigationSourceDomain.declared_paramRow`); and
* RUNTIME: the chain `sc` agrees with `S` level by level in the names it binds (`ShapeAgrees`) —
  needed only when the metadata carries owner POSITIONS: the gate then checks the level at
  depth `k`, and shape agreement makes it the NEAREST binder on `sc` (`nearest_of_shape`). With
  names only, the gate checks the nearest binder itself (`paramRowOwned_of_accessible_names`).

So the local-only premise is now statable: `memberExposed` (a decidable fact of the program, held
by every corpus program) and `ShapeAgrees` (a fact of the runtime chain: PROVENANCE — the chain
mirrors the static stack of the level it was wired from). `ShapeAgrees` is NOT proved to hold of
every chain the evaluator builds; it is the open half (§ 3).

## 2. The routes no gate checks: the proposed invariant (`ReqActivated`)

A direct lexical hit is never gated (`memberAccessible?`'s documentation: a name found on the site's
own chain is inside every owner of what it captures). For it the proposed invariant is
`ReqActivated C S name a`: the algorithm `a`, on the runtime chain `C` that agrees with its static
stack `S`, has every requirement collected by the candidate static selection model
(`reqAlg ⟨false, true⟩`, the requirements `exposureFull` checks; the independent E-18 F1 review found
omitted intermediate selections and fired the front-end stop rule) on an ACTIVATED level of `C`. It gives the cell
clause directly (`paramRowOwned_of_reqActivated`), with no gate.

## 3. NOT proved here

That every chain production builds agrees with a static stack (`ShapeAgrees`: through
`anchorChain`, an activated level of the same declaration replaces a static one, so shape
agreement needs "one declaration identity, one static stack" across the run), and that every body
keeps `ReqActivated` of the algorithms it evaluates (through lexical lookup, which needs the
reader's requirements to cover what it selects — `exposureFull` — and through body entry and
family dispatch, which activate the entered level). Nothing here is about C#.
-/

namespace KatLang.NavigationOwnership

/-! ## Wiring a parameter-row member -/

/-- An identity slot that is no module root: `Algorithm.withParent` keeps the parent it is given (a
    module root is re-parented onto the chain's root). -/
def NotModule : Option PropertyIdentity → Prop
  | some (.module _) => False
  | some (.moduleView _ _) => False
  | _ => True

theorem withParent_alias (sc parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (h : NotModule id) :
    Algorithm.withParent sc (.alias parent opens props target id reference) =
      .alias sc opens props target id reference := by
  cases id with
  | none => rfl
  | some pid => cases pid <;> first | rfl | (simp [NotModule] at h)

/-- The wired parameter-row member, explicitly. -/
theorem childOfInContext_paramRow (container : Algorithm) (ctx : EvalCtx) {p : PropDef}
    {parent : Option ScopeCtx} {opens : List Expr} {props : List PropDef} {y : Ident}
    {id : Option PropertyIdentity} {reference : Bool}
    (halg : p.alg = .alias parent opens props (.param y) id reference) (hid : NotModule id) :
    childOfInContext container p.alg ctx =
      .alias (some (scopeInContext container ctx)) opens props (.param y) id reference := by
  unfold childOfInContext
  rw [halg, withParent_alias _ _ _ _ _ _ _ hid]

/-! ## The gate, in its two metadata forms -/

/-- What the owner-activated gate checks of one required NAME (names-only metadata). -/
theorem gate_names {ctx : EvalCtx} {container : Algorithm} {p : PropDef} {required : List Ident}
    (hexp : p.exposure = .localCapturedAncestorParams required) (hpos : p.requiredOwnerDepths = none)
    {y : Ident} (hy : y ∈ required) (hacc : memberAccessible? ctx container p = true) :
    ∃ owner, requiredParameterOwner? (scopeInContext container ctx) y = some owner ∧
      owner.activation.isSome = true := by
  unfold memberAccessible? at hacc
  rw [hexp] at hacc
  dsimp only at hacc
  split at hacc
  · cases hacc
  · rw [hpos] at hacc
    dsimp only at hacc
    have hall := List.all_eq_true.mp hacc y hy
    split at hall
    · rename_i owner hown
      exact ⟨owner, hown, (Bool.and_eq_true _ _ ▸ hall).1⟩
    · cases hall

/-- What the owner-activated gate checks of one required POSITION. -/
theorem gate_positions {ctx : EvalCtx} {container : Algorithm} {p : PropDef} {required : List Ident}
    (hexp : p.exposure = .localCapturedAncestorParams required)
    {positions : List (Ident × Option Nat)} (hpos : p.requiredOwnerDepths = some positions)
    {y : Ident} {k : Nat} (hy : (y, some k) ∈ positions) (hacc : memberAccessible? ctx container p = true) :
    ∃ owner, (scopeInContext container ctx).ancestor? k = some owner ∧ owner.params.contains y = true ∧
      owner.activation.isSome = true := by
  unfold memberAccessible? at hacc
  rw [hexp] at hacc
  dsimp only at hacc
  split at hacc
  · cases hacc
  · rw [hpos] at hacc
    dsimp only at hacc
    have hall := List.all_eq_true.mp hacc (y, some k) hy
    dsimp only at hall
    split at hall
    · rename_i owner hown
      simp only [Bool.and_eq_true] at hall
      exact ⟨owner, hown, hall.1.1, hall.1.2⟩
    · cases hall

/-- **THE GATE GIVES THE CELL CLAUSE, names-only metadata.** -/
theorem paramRowOwned_of_accessible_names {ctx : EvalCtx} {container : Algorithm} {p : PropDef}
    {required : List Ident} (hexp : p.exposure = .localCapturedAncestorParams required)
    (hpos : p.requiredOwnerDepths = none) {y : Ident} (hy : y ∈ required)
    {parent : Option ScopeCtx} {opens : List Expr} {props : List PropDef} {id : Option PropertyIdentity}
    {reference : Bool} (halg : p.alg = .alias parent opens props (.param y) id reference) (hid : NotModule id)
    (hacc : memberAccessible? ctx container p = true) :
    ParamRowOwned (childOfInContext container p.alg ctx) := by
  rw [childOfInContext_paramRow container ctx halg hid]
  obtain ⟨owner, hown, hact⟩ := gate_names hexp hpos hy hacc
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hact
  exact ⟨_, owner, i, rfl, hown, hi⟩

/-- **THE GATE GIVES THE CELL CLAUSE, positions metadata** — when the position checked is the
    nearest binder of the row's parameter on the wired chain. -/
theorem paramRowOwned_of_accessible_positions {ctx : EvalCtx} {container : Algorithm} {p : PropDef}
    {required : List Ident} (hexp : p.exposure = .localCapturedAncestorParams required)
    {positions : List (Ident × Option Nat)} (hpos : p.requiredOwnerDepths = some positions)
    {y : Ident} {k : Nat} (hy : (y, some k) ∈ positions)
    (hnearest : requiredParameterOwner? (scopeInContext container ctx) y = (scopeInContext container ctx).ancestor? k)
    {parent : Option ScopeCtx} {opens : List Expr} {props : List PropDef} {id : Option PropertyIdentity}
    {reference : Bool} (halg : p.alg = .alias parent opens props (.param y) id reference) (hid : NotModule id)
    (hacc : memberAccessible? ctx container p = true) :
    ParamRowOwned (childOfInContext container p.alg ctx) := by
  rw [childOfInContext_paramRow container ctx halg hid]
  obtain ⟨owner, hanc, _, hact⟩ := gate_positions hexp hpos hy hacc
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hact
  exact ⟨_, owner, i, rfl, hnearest.trans hanc, hi⟩

/-! ## Shape agreement: the runtime chain mirrors a static stack -/

/-- **SHAPE AGREEMENT.** Level by level, the runtime chain binds the names the static stack's levels
    bind (as far as the stack reaches). -/
def ShapeAgrees : Option ScopeCtx → Stack → Prop
  | _, [] => True
  | none, _ :: _ => False
  | some sc, level :: rest => (∀ y, sc.params.contains y = level.params.contains y) ∧ ShapeAgrees sc.parent rest

/-- On an agreeing chain, the nearest static binder is the nearest runtime binder. -/
theorem nearest_of_shape : ∀ (stack : Stack) (sc : ScopeCtx) (y : Ident) (k : Nat),
    ShapeAgrees (some sc) stack → ownerIndex? stack y = some k →
      requiredParameterOwner? sc y = sc.ancestor? k
  | [], _, _, _, _, hk => by simp [ownerIndex?] at hk
  | level :: rest, sc, y, k, hs, hk => by
      simp only [ShapeAgrees] at hs
      rw [KatLang.TotalLeaves.requiredParameterOwner?_equation]
      simp only [ownerIndex?] at hk
      by_cases hl : level.params.contains y = true
      · rw [ite_eq_left hl] at hk
        cases hk
        rw [ite_eq_left ((hs.1 y).trans hl)]
        rfl
      · rw [ite_eq_right hl] at hk
        rw [ite_eq_right (by rw [hs.1 y]; exact hl)]
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
        cases rest with
        | nil => simp [ownerIndex?] at hk'
        | cons next more =>
          cases hp : ScopeCtx.parent sc with
          | none => rw [hp] at hs; exact absurd hs.2 (by simp [ShapeAgrees])
          | some par =>
            rw [hp] at hs
            show _ = sc.parent >>= fun p => p.ancestor? k'
            rw [hp]
            exact nearest_of_shape (next :: more) par y k' hs.2 hk'

/-! ## The local-only premise, stated -/

/-- **THE LOCAL-ONLY PREMISE GIVES THE CELL CLAUSE AT A MEMBER SELECTION.** A member `p` selected
    from `container`, accessible from `ctx`, whose algorithm is a parameter-row alias of `y`: when its
    metadata passes the exposure check at its static declaring stack `S` (any mode; `y` bound in
    `S` at `k`) and the chain it is wired under agrees with `S`, it is owned. -/
theorem paramRowOwned_of_exposed {mode : Mode} {S : Stack} {ctx : EvalCtx} {container : Algorithm}
    {p : PropDef} (hexposed : memberExposed mode S p = true)
    (hshape : ShapeAgrees (some (scopeInContext container ctx)) S)
    {parent : Option ScopeCtx} {opens : List Expr} {props : List PropDef} {y : Ident}
    {id : Option PropertyIdentity} {reference : Bool}
    (halg : p.alg = .alias parent opens props (.param y) id reference) (hid : NotModule id)
    {k : Nat} (hk : ownerIndex? S y = some k) (hacc : memberAccessible? ctx container p = true) :
    ParamRowOwned (childOfInContext container p.alg ctx) := by
  have hdecl := declared_paramRow hexposed halg hk
  unfold declared at hdecl
  split at hdecl
  · cases hdecl
  · cases hdecl
  · rename_i required hexp
    split at hdecl
    · rename_i positions hpos
      obtain ⟨entry, hmem, hentry⟩ := List.mem_filterMap.mp hdecl
      obtain ⟨depth, hdepth, hpair⟩ := Option.map_eq_some_iff.mp hentry
      obtain ⟨name, d⟩ := entry
      simp only at hdepth hpair
      cases hpair
      subst hdepth
      exact paramRowOwned_of_accessible_positions hexp hpos hmem
        (nearest_of_shape S _ y k hshape hk) halg hid hacc
    · rename_i hpos
      obtain ⟨name, hmem, hname⟩ := List.mem_filterMap.mp hdecl
      obtain ⟨_, _, hpair⟩ := Option.map_eq_some_iff.mp hname
      cases hpair
      exact paramRowOwned_of_accessible_names hexp hpos hmem halg hid hacc

/-! ## The proposed invariant for the routes no gate checks -/

/-- The level at depth `i` of the chain `C` is activated. -/
def LevelActivated (C : Option ScopeCtx) (i : Nat) : Prop :=
  ∃ sc, C.bind (fun c => c.ancestor? i) = some sc ∧ sc.activation.isSome = true

/-- **THE PROPOSED B2 INVARIANT** (stated; that every body keeps it is NOT proved): the algorithm
    `a`, written at the static stack `S` (`name`: the property whose body it is) and wired on the
    runtime chain `C` that agrees with `S`, has every modeled requirement of its rows on an ACTIVATED
    level of `C`. -/
structure ReqActivated (C : Option ScopeCtx) (S : Stack) (name : Option Ident) (a : Algorithm) : Prop where
  shape : ShapeAgrees C S
  activated : ∀ r ∈ reqAlg ⟨false, true⟩ S [] name a, LevelActivated C r.2

/-- **THE INVARIANT GIVES THE CELL CLAUSE, with no gate**: a parameter-row alias whose parameter
    is bound in its static stack is owned when it keeps `ReqActivated`. -/
theorem paramRowOwned_of_reqActivated (sc : ScopeCtx) (S : Stack) (name : Option Ident)
    (opens : List Expr) (props : List PropDef) (y : Ident) (id : Option PropertyIdentity) (reference : Bool)
    {k : Nat} (hk : ownerIndex? S y = some k)
    (h : ReqActivated (some sc) S name (.alias (some sc) opens props (.param y) id reference)) :
    ParamRowOwned (.alias (some sc) opens props (.param y) id reference) := by
  obtain ⟨owner, hanc, hact⟩ := h.activated (y, k) (reqAlg_paramRow _ S name _ opens props y id reference k hk)
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hact
  exact ⟨sc, owner, i, rfl, (nearest_of_shape S sc y k h.shape hk).trans hanc, hi⟩

/-! ## The member-navigation verification condition of the pilot, for the navigation contract -/

/-- An algorithm that is no parameter-row alias is owned wherever it is wired. -/
theorem paramRowOwned_withParent_of_not_row (sc : Option ScopeCtx) (a : Algorithm)
    (h : ∀ parent opens props y id reference, a ≠ .alias parent opens props (.param y) id reference) :
    ParamRowOwned (a.withParent sc) := by
  cases a with
  | «alias» parent opens props target id reference =>
    cases target with
    | param y => exact absurd rfl (h parent opens props y id reference)
    | _ =>
      cases id with
      | none => exact trivial
      | some pid => cases pid <;> exact trivial
  | mk parent patterns opens props output id =>
    cases id with
    | none => exact trivial
    | some pid => cases pid <;> exact trivial
  | builtin b => exact trivial
  | conditional parent opens branches id => exact trivial

/-- **THE MEMBER EDGE'S VERIFICATION CONDITION, REDUCED.** For the navigation contract, the receiver
    probe's member edge must hand the structure chase a USABLE member (`AlgOK`: a backed chain, and
    the cell clause). It is one when the container's chain and the site chain are backed (the
    probe's result contract and the call's input) and, for a parameter-row member, the local-only
    premise holds: its metadata passes the exposure check at its static declaring stack `S`, and
    the in-context chain agrees with `S` (PROVENANCE, not proved in general). -/
theorem algOK_member {acts : Array ParameterActivation} {ctx : EvalCtx} {container : Algorithm} {p : PropDef}
    (hc : Backed acts container.parent) (hs : Backed acts (siteScope? ctx))
    (hrow : ∀ parent opens props y id reference, p.alg = .alias parent opens props (.param y) id reference →
      NotModule id ∧ ∃ (mode : Mode) (S : Stack) (k : Nat), memberExposed mode S p = true ∧
        ShapeAgrees (some (scopeInContext container ctx)) S ∧ ownerIndex? S y = some k)
    (hacc : memberAccessible? ctx container p = true) :
    AlgOK acts (childOfInContext container p.alg ctx) := by
  refine ⟨KatLang.NavigationWiring.backed_childOfInContext container p.alg ctx hc hs, ?_⟩
  by_cases hr : ∃ parent opens props y id reference, p.alg = .alias parent opens props (.param y) id reference
  · obtain ⟨parent, opens, props, y, id, reference, halg⟩ := hr
    obtain ⟨hid, mode, S, k, hexp, hshape, hk⟩ := hrow parent opens props y id reference halg
    exact paramRowOwned_of_exposed hexp hshape halg hid hk hacc
  · exact paramRowOwned_withParent_of_not_row _ _ (fun parent opens props y id reference h =>
      hr ⟨parent, opens, props, y, id, reference, h⟩)

end KatLang.NavigationOwnership
