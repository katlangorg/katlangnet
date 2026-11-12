import KatLangArityLaws.MemberStability

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.EvaluatorCacheLaws
open KatLang.WhileRoundProduction (production_of_answer_free)

/-!
# Settled receiver navigation, DERIVED from the production probe (ledger E-18, step 1, M1)

`MemberStability.member_bridge_navSettled` is the member bridge for EVERY bundle over a receiver
whose navigation is `NavSettled` at the probe's exit state. This module DERIVES that premise from
facts of the production probe, compositionally, and states the bridge with the probe as its
premise.

## State-free lookup (names, opened names)

`StateFree m`: one outcome from every state, the state unchanged. It is closed under the monad's
combinators (`sf_bind`, `sf_attempt`, `sf_withCtx`, `sf_forIn`, `sf_mapM`, …), and — proved by
unfolding the production definitions — THE LEXICAL LOOKUP IS STATE-FREE
(`sf_lookupLexicalPropertyRaw`): the local hit, the structural parent walk, and the whole `open`
resolution (`resolveAllOpens`, `resolveOpen`, `resolveAlgForOpen`, `openStructure`,
`openNavigateWith`, the per-level and per-chain open lookups). So a lookup observed ONCE — inside the
production probe — is the lookup from every state (`lookup_everywhere`): a name selected through
`open` is no different from a name the scope declares.

## Compositional settledness

* `HeadSettled target ctx selected t` — from every navigation extension of `t`, the plan's
  structural projection of the receiver HEAD is `selected`, unchanged state;
* `StructSettled selected ctx owner t` — likewise the STRUCTURE chase of `selected` is `owner`;
* `navSettled_of` — the two give `NavSettled`.

Heads: a name (`headSettled_name`, any lookup route), an inline block (`headSettled_block`), a
PARAMETER after its first production projection (`headSettled_param`: the memo is read back, the
captured activation being recorded), a MEMBER STEP over a settled receiver (`headSettled_member`:
nested member paths and parameter-rooted paths, by induction on the path). Structures: a
structure-normal algorithm (`structSettled_normal`), and — `structSettled_of_stateFree` — any
algorithm whose structure chase is state-free.

## From the probe

`probe_name` unfolds the production probe of a name into its lookup — the same from every state —
and the structure chase of the binding it selects. From it:

* `navSettled_plain_name_of_probe`, `member_bridge_name_of_probe` — a name (declared, inherited or
  OPENED) selecting a declaration that is no transparent reference: settled from the probe alone;
* `resolveAliasStructure_reference`, `navSettled_reference_of_probe`,
  `member_bridge_reference_of_probe` — a name selecting a TRANSPARENT REFERENCE whose row is a name
  that selects a non-alias target (`AB = Box`): the production alias chase is UNFOLDED (the route
  decision of a name row, the row's lookup in the reference's own scope, the chase of the target)
  and is the same from every state;
* `navSettled_name_of_probe` — any name, relative to the settled structure of the selected binding;
* `navSettled_param_of_probe` — a parameter, after its first projection;
* `navSettled_member` — a member step over a settled receiver (nested and parameter-rooted paths);
* `member_bridge_of_settled` — the member bridge for EVERY bundle from settledness assembled so.

`MemberSettledInstances` applies them to genuine source programs.

## What is NOT derived here

(Derived since by the M1 completion pass, in general and without unfolding:
`NavigationReread.navigation_reread`, `NavigationSettled.navSettled_of_navRuns`, `probe_member`,
`member_bridge_of_probe`; structure-normality in `StoredCallableNormal`. The list below records
what THIS module's shape-by-shape unfoldings do not reach.)

* The STRUCTURE CHASE of a RUNTIME-TARGET ALIAS (`RTA = RC.Algorithm`), and of a transparent
  reference whose row is a member path (`ALS = Lib.Sub`) or whose chase has several steps
  (`AB2 = AB`), is not unfolded: `StructSettled` for those is a PREMISE (`hstruct`), established on
  concrete reached states by the theorem-level instances (`MemberBridgeSourceAliases`:
  `settled_origin`) but not derived from the probe for every navigation extension. Deriving it for
  a runtime-target alias needs the read-back of `aliasStepIsRuntime` / `aliasBindingCell` / the
  binding cell's projection through `NavExt` (the alias record by `NavExt.aliasCell`, the
  projection by `projectNeedCallable_memo`), and — for a route decision whose failure the chase
  catches — the survival of in-flight CALLABLE marks, which `LinkKept` did not state then (it does since the
  M1 completion pass: `LinkKept.projecting`).
* A member step's own facts (the receiver's probe, the declared member, its accessibility) are
  premises of `navSettled_member`; they are not extracted from the PATH's probe (which would use
  the non-minting condition: a structural miss mints).
* Structure-normality of a parameter's projected CALLABLE stays the decidable premise `hnormal`
  of `member_bridge_of_settled`; the captured activation's validity stays the premise `hact`.
* The minting class (`MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`) is outside every
  theorem: exact equality fails there.
-/

namespace KatLang.MemberSettled

/-! ## State-free computations -/

/-- `m` neither reads nor writes the state: ONE outcome from every state, the state unchanged. -/
def StateFree {α : Type} (m : EvalM α) : Prop := ∃ o : Except Error α, ∀ s, m.runState s = (o, s)

theorem sf_pure {α : Type} (a : α) : StateFree (pure a : EvalM α) := ⟨.ok a, fun _ => rfl⟩
theorem sf_throw {α : Type} (e : Error) : StateFree (throw e : EvalM α) := ⟨.error e, fun _ => rfl⟩
theorem sf_evalError {α : Type} (e : Error) : StateFree (EvalM.error e : EvalM α) := ⟨.error e, fun _ => rfl⟩
theorem sf_throwOf {α : Type} (e : Error) : StateFree (MonadExceptOf.throw e : EvalM α) :=
  ⟨.error e, fun _ => rfl⟩
theorem sf_raw_throw {α : Type} (e : Error) : StateFree (⟨throw e⟩ : EvalM α) := ⟨.error e, fun _ => rfl⟩
theorem sf_raw_pure {α : Type} (a : α) : StateFree (⟨pure a⟩ : EvalM α) := ⟨.ok a, fun _ => rfl⟩
theorem sf_lift {α : Type} (o : Except Error α) : StateFree (monadLift o : EvalM α) := ⟨o, fun s => lift_run o s⟩

theorem sf_bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : StateFree m) (hf : ∀ x, StateFree (f x)) : StateFree (m >>= f) := by
  obtain ⟨o, ho⟩ := hm
  cases o with
  | error e => exact ⟨.error e, fun s => by rw [bind_run, ho s]⟩
  | ok a =>
    obtain ⟨o', ho'⟩ := hf a
    exact ⟨o', fun s => by rw [bind_run, ho s]; exact ho' s⟩

theorem sf_map {α β : Type} (f : α → β) {m : EvalM α} (hm : StateFree m) : StateFree (f <$> m) :=
  sf_bind (f := Function.comp pure f) hm (fun x => sf_pure (f x))

theorem sf_attempt {α : Type} {m : EvalM α} (hm : StateFree m) : StateFree (evalAttempt m) := by
  obtain ⟨o, ho⟩ := hm
  refine ⟨if o.isIncomplete then .error .fuelExhausted else .ok o, fun s => ?_⟩
  rw [evalAttempt_run, ho s]
  dsimp only
  split <;> rfl

theorem sf_withCtx {α : Type} (c : String) {m : EvalM α} (hm : StateFree m) : StateFree (withCtx c m) := by
  unfold withCtx
  refine sf_bind (sf_attempt hm) (fun r => ?_)
  cases r with
  | ok x => exact sf_pure x
  | error e => exact sf_evalError _

theorem sf_mapM {α β : Type} (f : α → EvalM β) (h : ∀ x, StateFree (f x)) (xs : List α) :
    StateFree (xs.mapM f) := by
  suffices ∀ acc, StateFree (List.mapM.loop f xs acc) by exact this []
  induction xs with
  | nil => intro acc; exact sf_pure _
  | cons x xs ih => intro acc; exact sf_bind (h x) (fun y => ih _)

theorem sf_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, StateFree (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), StateFree (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact sf_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply sf_bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact sf_pure _
    | yield b => exact sf_forIn'_loop as f hf as' b _

theorem sf_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, StateFree (f a b)) : StateFree (forIn xs init f) :=
  sf_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem sf_forM {α : Type} (xs : List α) (f : α → EvalM PUnit) (h : ∀ a, StateFree (f a)) :
    StateFree (xs.forM f) := by
  induction xs with
  | nil => exact sf_pure _
  | cons x xs ih => unfold List.forM; exact sf_bind (h x) (fun _ => ih)

open Lean Meta Elab Tactic in
/-- The computation of a `StateFree` goal. -/
def sfComputation? (ty : Lean.Expr) : Option Lean.Expr :=
  if ty.isAppOf ``KatLang.MemberSettled.StateFree then some ty.appArg! else none

open Lean Meta Elab Tactic in
elab "sf_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := sfComputation? ty | throwError "sf_unfold_head: not a state-free goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "sf_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM,
        ``KatLang.withCtx, ``throw, ``MonadExcept.throw, ``MonadExceptOf.throw, ``throwThe,
        ``KatLang.EvalM.error] then
      throwError "sf_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "sf_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
elab "sf_zeta" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := sfComputation? ty | throwError "sf_zeta: not a state-free goal"
    let mut e := m
    let mut n := 0
    for _ in [0:10000] do
      match e with
      | Lean.Expr.letE _ _ v b _ => e := b.instantiate1 v; n := n + 1
      | Lean.Expr.mdata _ e' => e := e'
      | _ => break
    if n == 0 then throwError "sf_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! e)]

open Lean Meta Elab Tactic in
elab "sf_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := sfComputation? ty | throwError "sf_whnf_core: not a state-free goal"
    let m' ← whnfCore m
    if m' == m then throwError "sf_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

set_option hygiene false in
/-- Syntax-directed state-freeness: the combinator lemmas, case splits and unfolding. It fails on any
    read or write of the state (`get`, `set`, `modify` have no rule). -/
macro "sf_tac" : tactic => `(tactic| without_info_trees ((try dsimp only at *) <;> repeat' (first
  | pres_hyp
  | pres_absurd
  | (with_reducible apply sf_withCtx)
  | (with_reducible apply sf_attempt)
  | (with_reducible apply sf_map)
  | (with_reducible apply sf_bind)
  | (with_reducible apply sf_pure)
  | (with_reducible apply sf_throw)
  | (with_reducible apply sf_throwOf)
  | (with_reducible apply sf_raw_throw)
  | (with_reducible apply sf_raw_pure)
  | (with_reducible apply sf_evalError)
  | (with_reducible apply sf_lift)
  | (with_reducible apply sf_mapM)
  | (with_reducible apply sf_forIn)
  | (with_reducible apply sf_forM)
  | split
  | pres_intro
  | sf_zeta
  | sf_whnf_core
  | sf_unfold_head)))

/-! ## The lexical lookup is state-free -/

theorem sf_openNavigateWith (structureOf : Algorithm → EvalM Algorithm)
    (h : ∀ a, StateFree (structureOf a)) (ctx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (receiverName : String) (steps : List Ident) :
    StateFree (openNavigateWith structureOf ctx notStatic value receiverName steps) := by
  induction steps generalizing value receiverName with
  | nil => unfold openNavigateWith; sf_tac
  | cons member rest ih => unfold openNavigateWith; sf_tac

theorem sf_openStructure (fuel : Nat) (ctx : EvalCtx) (a : Algorithm) :
    StateFree (openStructure fuel ctx a) := by
  induction fuel generalizing a with
  | zero => simp only [openStructure]; sf_tac
  | succ n ih =>
    have := sf_openNavigateWith (fun value => openStructure n ctx value) ih
    simp only [openStructure]; sf_tac

theorem sf_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : StateFree (resolveAlgForOpen e ctx) := by
  have := sf_openStructure
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; sf_tac
  | _ => unfold resolveAlgForOpen; sf_tac

theorem sf_resolveOpen (e : Expr) (ctx : EvalCtx) : StateFree (resolveOpen e ctx) := by
  have := sf_resolveAlgForOpen
  have := sf_openStructure
  unfold resolveOpen; sf_tac

theorem sf_resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : StateFree (resolveAllOpens a ctx) := by
  have := sf_resolveOpen
  have := sf_resolveAlgForOpen
  unfold resolveAllOpens; sf_tac

theorem sf_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    StateFree (lookupOpenProperties a name ctx) := by
  have := sf_resolveAllOpens
  unfold lookupOpenProperties; sf_tac

theorem sf_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    StateFree (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := sf_lookupOpenProperties
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> sf_tac

theorem sf_lookupOpenPropertiesInChain (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    StateFree (lookupOpenPropertiesInChain a name ctx) := by
  have := sf_lookupOpenProperties
  have := sf_lookupOpenPropertiesInParentChain
  unfold lookupOpenPropertiesInChain; sf_tac

/-- **THE LEXICAL LOOKUP IS STATE-FREE**: the local hit, the structural parent walk and the whole
    `open` resolution read and write nothing of the run state. -/
theorem sf_lookupLexicalPropertyRaw (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    StateFree (lookupLexicalPropertyRaw a name ctx) := by
  have := sf_lookupOpenPropertiesInChain
  unfold lookupLexicalPropertyRaw; sf_tac

/-- **A lookup observed once is the lookup from every state** — whatever route selected the name:
    a declaration of the scope, of an enclosing scope, or of an opened namespace. -/
theorem lookup_everywhere (a : Algorithm) (name : Ident) (ctx : EvalCtx) (s s' : EvalState)
    (o : Except Error ResolvedProperty) (h : (lookupLexicalPropertyRaw a name ctx).runState s = (o, s')) :
    s' = s ∧ ∀ t, (lookupLexicalPropertyRaw a name ctx).runState t = (o, t) := by
  obtain ⟨o', ho'⟩ := sf_lookupLexicalPropertyRaw a name ctx
  rw [ho' s] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  subst h1
  exact ⟨h2.symm, ho'⟩

/-! ## Compositional settledness -/

open KatLang.WhileRoundProduction (production_eq_of_finite finite_call)

/-- **A settled receiver HEAD.** From every navigation extension of `t`, the plan's structural
    projection of `target` is `selected`, and reading it changes nothing. -/
def HeadSettled (target : Expr) (ctx : EvalCtx) (selected : Algorithm) (t : EvalState) : Prop :=
  ∀ u, NavExt t u → (projectNeedStructuralMember target ctx).runState u = (.ok (some selected), u)

/-- **A settled STRUCTURE.** From every navigation extension of `t`, the structure chase of
    `selected` is `owner`, and running it changes nothing. -/
def StructSettled (selected : Algorithm) (ctx : EvalCtx) (owner : Algorithm) (t : EvalState) : Prop :=
  ∀ u, NavExt t u → (resolveAliasStructure selected ctx).runState u = (.ok (some owner), u)

theorem HeadSettled.mono {target : Expr} {ctx : EvalCtx} {selected : Algorithm} {t u : EvalState}
    (h : HeadSettled target ctx selected t) (he : NavExt t u) : HeadSettled target ctx selected u :=
  fun v hv => h v (he.trans hv)

theorem StructSettled.mono {selected : Algorithm} {ctx : EvalCtx} {owner : Algorithm} {t u : EvalState}
    (h : StructSettled selected ctx owner t) (he : NavExt t u) : StructSettled selected ctx owner u :=
  fun v hv => h v (he.trans hv)

/-- **A settled head and a settled structure are a settled navigation.** -/
theorem navSettled_of {target : Expr} {ctx : EvalCtx} {selected owner : Algorithm} {t : EvalState}
    (hh : HeadSettled target ctx selected t) (hs : StructSettled selected ctx owner t) :
    NavSettled target ctx owner t := by
  intro u hu
  unfold projectedStructure
  rw [bind_run, hh u hu]
  exact hs u hu

/-- A structure-normal algorithm IS its structure, at every state. -/
theorem structSettled_normal (g : Algorithm) (ctx : EvalCtx) (t : EvalState) (h : structureNormal g = true) :
    StructSettled g ctx g t := by
  intro u _
  rw [resolveAliasStructure_normal g ctx h]
  rfl

/-- A structure chase that is the same from every state is settled at every state. -/
theorem structSettled_of_everywhere {selected : Algorithm} {ctx : EvalCtx} {owner : Algorithm}
    (h : ∀ u, (resolveAliasStructure selected ctx).runState u = (.ok (some owner), u)) (t : EvalState) :
    StructSettled selected ctx owner t := fun u _ => h u

/-- An inline block is its own head, from every state. -/
theorem headSettled_block (block : Algorithm) (ctx : EvalCtx) (t : EvalState) :
    HeadSettled (.algorithmExpr block) ctx (wireToCaller ctx block) t := by
  intro u _
  apply production_of_answer_free _ u
  · intro rec; rfl
  · nofun

/-- A NAME is settled as the binding its lexical lookup selects — whatever route selected it. -/
theorem headSettled_name (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm)
    (r : ResolvedProperty) (hcs : ctx.callStack = top :: rest)
    (hl : ∀ t, (lookupLexicalPropertyRaw top n ctx).runState t = (.ok r, t)) (t : EvalState) :
    HeadSettled (.resolve n) ctx r.alg t := by
  intro u _
  apply production_of_answer_free _ u
  · intro rec
    show (EvalBody.projectNeedStructuralMember rec (.resolve n) ctx).runState u = _
    unfold EvalBody.projectNeedStructuralMember
    rw [hcs]
    dsimp only
    rw [bind_run, hl u]
    rfl
  · nofun

/-- A PARAMETER is settled as its projected CALLABLE after its first production projection: the
    cell's memo is read back from every navigation extension (the captured activation, if any,
    being recorded). -/
theorem headSettled_param (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (owner : Algorithm)
    (hrun : (projectParameterCallable x ctx).runState s = (.ok (some owner), s'))
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size) :
    HeadSettled (.param x) ctx owner s' := by
  intro u hu
  have hcall := projectParameterCallable_stable x ctx s s' owner hrun hact u hu.memo
  have hcb : ProductionCompletes ((fun rec : EvalRec => rec (.projectParameterCallable x ctx)) evalUnbounded) u := by
    unfold ProductionCompletes
    show ((projectParameterCallable x ctx).runState u).1 ≠ _
    rw [hcall]; nofun
  exact (production_eq_of_finite (.projectNeedStructuralMember (.param x) ctx)
    (fun rec => rec (.projectParameterCallable x ctx)) (fun _ => rfl) (finite_call _) u hcb).trans hcall

/-- **A MEMBER STEP over a settled receiver is a settled head**: nested member paths and
    parameter-rooted paths, one declared, accessible member at a time. -/
theorem headSettled_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (a : Algorithm) (q : PropDef)
    (t : EvalState) (h : NavSettled o ctx a t) (hl : Algorithm.lookupPropDefAny? a n = some q)
    (hacc : memberAccessible? ctx a q = true) :
    HeadSettled (.dotMember o n fb none) ctx (childOfInContext a q.alg ctx) t :=
  fun u hu => member_projection_run o n fb ctx u u a q (h u hu) hl hacc

/-- A member step over a settled receiver, with the member's structure settled. -/
theorem navSettled_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (a : Algorithm) (q : PropDef)
    (owner : Algorithm) (t : EvalState) (h : NavSettled o ctx a t)
    (hl : Algorithm.lookupPropDefAny? a n = some q) (hacc : memberAccessible? ctx a q = true)
    (hs : StructSettled (childOfInContext a q.alg ctx) ctx owner t) :
    NavSettled (.dotMember o n fb none) ctx owner t :=
  navSettled_of (headSettled_member o n fb ctx a q t h hl hacc) hs

/-! ## From the production probe -/

/-- **The production probe of a NAME is its lexical lookup — the same from every state — and the
    structure chase of the binding it selects.** -/
theorem probe_name (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm) (s s' : EvalState)
    (owner : Algorithm) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s')) :
    ∃ r, (∀ t, (lookupLexicalPropertyRaw top n ctx).runState t = (.ok r, t)) ∧
      (resolveAliasStructure r.alg ctx).runState s = (.ok (some owner), s') := by
  have hc : ProductionCompletes (resolveDotReceiver? (.resolve n) ctx) s := by
    unfold ProductionCompletes; rw [hprobe]; nofun
  have hu := production_unfolds (.resolveDotReceiver? (.resolve n) ctx) s hc
  have hbody : (EvalBody.resolveDotReceiver? evalUnbounded (.resolve n) ctx).runState s = (.ok (some owner), s') :=
    hu.trans hprobe
  unfold EvalBody.resolveDotReceiver? at hbody
  rw [hcs] at hbody
  dsimp only at hbody
  rw [bind_run] at hbody
  obtain ⟨o, ho⟩ := sf_lookupLexicalPropertyRaw top n ctx
  rw [ho s] at hbody
  cases o with
  | error e => cases hbody
  | ok r => exact ⟨r, ho, hbody⟩

/-- **A NAME, from its probe, relative to the settled structure of the binding it selects.** After
    a production probe of the name `n` completing at `(some owner, s')`: when the structure chase of
    the selected binding is settled at `s'` (`hstruct`, a premise about THAT binding and THAT chase
    — the lookup itself is derived), the receiver's navigation is settled at `s'`. The name may be
    declared by the scope, by an enclosing scope, or selected through `open`. -/
theorem navSettled_name_of_probe (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm)
    (s s' : EvalState) (owner : Algorithm) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hstruct : ∀ r, (∀ t, (lookupLexicalPropertyRaw top n ctx).runState t = (.ok r, t)) →
      (resolveAliasStructure r.alg ctx).runState s = (.ok (some owner), s') → StructSettled r.alg ctx owner s') :
    NavSettled (.resolve n) ctx owner s' := by
  obtain ⟨r, hl, hrun⟩ := probe_name n ctx top rest s s' owner hcs hprobe
  exact navSettled_of (headSettled_name n ctx top rest r hcs hl s') (hstruct r hl hrun)

/-- **A NAME selecting a declaration that is no transparent reference, from its probe alone.**
    The probe changed nothing (`s' = s`), the identity is the selected declaration, and the
    navigation is settled — for a name the scope declares, an enclosing scope declares, or an
    opened namespace provides. No lookup premise: the lookup is state-free. -/
theorem navSettled_plain_name_of_probe (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm)
    (s s' : EvalState) (owner : Algorithm) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hnormal : ∀ r, (lookupLexicalPropertyRaw top n ctx).runState s = (.ok r, s) → structureNormal r.alg = true) :
    s' = s ∧ NavSettled (.resolve n) ctx owner s' := by
  obtain ⟨r, hl, hrun⟩ := probe_name n ctx top rest s s' owner hcs hprobe
  have hn := hnormal r (hl s)
  rw [resolveAliasStructure_normal r.alg ctx hn] at hrun
  have hrun' : ((Except.ok (some r.alg) : Except Error (Option Algorithm)), s) = (.ok (some owner), s') := hrun
  obtain ⟨h1, h2⟩ := Prod.mk.inj hrun'
  have h3 : r.alg = owner := Option.some.inj (Except.ok.inj h1)
  subst h2
  subst h3
  exact ⟨rfl, navSettled_of (headSettled_name n ctx top rest r hcs hl s) (structSettled_normal r.alg ctx s hn)⟩

/-- **A PARAMETER, from its probe.** After the production probe of the parameter `x` completing at
    `(some owner, s')` — its FIRST CALLABLE projection, or a read of the memo — the navigation is
    settled at `s'` relative to the settled structure of the projected identity. -/
theorem navSettled_param_of_probe (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (selected owner : Algorithm)
    (hprobe : (resolveDotReceiver? (.param x) ctx).runState s = (.ok (some selected), s'))
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size)
    (hstruct : StructSettled selected ctx owner s') :
    NavSettled (.param x) ctx owner s' :=
  navSettled_of (headSettled_param x ctx s s' selected (probe_param x ctx s s' (some selected) hprobe) hact) hstruct

/-! ## The member bridge with the PROBE as its navigation premise -/

/-- **THE MEMBER BRIDGE over a NAME, every bundle, from the probe.** For a receiver name `n` — a
    declaration of the scope, of an enclosing scope, or of an OPENED namespace — that selects a
    declaration which is no transparent reference: after the production probe and the dot decision
    selecting the declared member `p`, the member-route ordinary call IS the re-counted production
    dot evaluation `n.N(args)`, both run from the SAME state — for the empty bundle, a spread-first
    bundle (whatever the spread runs, a failing spread included) and every other written list. The
    only navigation premise is the probe itself. -/
theorem member_bridge_name_of_probe (a : Nat) (n N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (top : Algorithm) (rest : List Algorithm) (s s' : EvalState)
    (owner : Algorithm) (p : PropDef) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hsel : selectDotEdge ctx (.resolve n) N (some owner) = .ok (.member owner p))
    (hnormal : ∀ r, (lookupLexicalPropertyRaw top n ctx).runState s = (.ok r, s) → structureNormal r.alg = true)
    (hprod : ProductionCompletes (evalCounted (.dotMember (.resolve n) N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a
        ⟨.dotMember (.resolve n) N fallback none, args, ctx, env, .dot (.resolve n) N fallback⟩ .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember (.resolve n) N fallback (some args)) ctx env).runState s :=
  member_bridge_navSettled a (.resolve n) N fallback args ctx env s s' (some owner) owner p hprobe hsel
    (member_projection_of_selection (.resolve n) N fallback ctx s s' (some owner) owner p hprobe hsel
      (fun x _ _ hx => by simp [headParam?] at hx))
    (navSettled_plain_name_of_probe n ctx top rest s s' owner hcs hprobe hnormal).2 hprod

/-- **THE MEMBER BRIDGE over ANY receiver, every bundle, from settledness assembled at the probe's
    exit**: `member_bridge_navSettled` with the receiver premise discharged by the probe and the
    selection (a parameter-rooted receiver needs `hnorm`). The settledness is assembled from
    `navSettled_of`, `headSettled_*`, `navSettled_member` and `StructSettled`. -/
theorem member_bridge_of_settled (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hnorm : ∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true)
    (hsettled : NavSettled target ctx owner s')
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_navSettled a target N fallback args ctx env s s' alg? owner p hprobe hsel
    (member_projection_of_selection target N fallback ctx s s' alg? owner p hprobe hsel hnorm) hsettled hprod

/-! ## Transparent references: the production alias chase, unfolded

A TRANSPARENT REFERENCE whose row is a NAME (`AB = Box`): its structure chase is one static step —
the route decision of a row that is no runtime row (`aliasStepIsRuntime`, answering `false` without
reading anything), the lookup of the row in the alias's OWN scope (state-free), and the chase of the
selected target, which is no alias. Nothing is read from the state and nothing is written: the
chase is the same from EVERY state. -/

open KatLang.PlanConservativity (isAliasAlg)

/-- A completed core run at fuel `n + 1` is the body's over the core at fuel `n`. -/
theorem fuel_succ_of_body (n : Nat) (c : EvalCall) (u : EvalState) (r : Except Error c.Ret × EvalState)
    (h : (evalStep (evalFuel n) c).runState u = r) (hr : r.1 ≠ .error .fuelExhausted) :
    (evalFuel (n + 1) c).runState u = r := by
  rw [evalFuel_succ, normalize_of_complete _ u (by rw [h]; exact hr), h]

/-- A completed core run IS the production run. -/
theorem production_of_fuel (n : Nat) (c : EvalCall) (u : EvalState) (r : Except Error c.Ret × EvalState)
    (h : (evalFuel n c).runState u = r) (hr : r.1 ≠ .error .fuelExhausted) :
    (evalUnbounded c).runState u = r :=
  ((production_completes_iff c u r).2 ⟨n, h, (evalFuel_completes_iff n c u).2 (by rw [h]; exact hr)⟩).1

/-- The route decision of a row that is a NAME: no runtime step, nothing read. -/
theorem aliasStepIsRuntime_name (rec : EvalRec) (step : Algorithm) (m : Ident) (ctx : EvalCtx)
    (visited : List String) (u : EvalState) :
    (EvalBody.aliasStepIsRuntime rec step (.resolve m) ctx visited).runState u = (.ok false, u) := rfl

/-- The chase of an algorithm that is no alias ends at once, at itself. -/
theorem chase_not_alias (rec : EvalRec) (fc pr : Bool) (g : Algorithm) (ctx : EvalCtx) (visited : List String)
    (last : Option (Algorithm × PropDef)) (u : EvalState) (hg : isAliasAlg g = false) :
    (EvalBody.resolveAliasChase rec fc pr g ctx visited last).runState u = (.ok (.identity g last), u) := by
  cases g with
  | «alias» p op pr' t id reference => simp [isAliasAlg] at hg
  | mk p pp op pr' out id => rfl
  | builtin b => rfl
  | conditional p op bs id => rfl

/-- One static step over a row that is a NAME selects what the lookup in the alias's own scope
    selects, whatever the structure reader. -/
theorem resolveAliasStep_name (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm)) (step : Algorithm)
    (m : Ident) (ctx : EvalCtx) (r : ResolvedProperty) (u : EvalState)
    (hl : (lookupLexicalPropertyRaw step m (ctx.push step)).runState u = (.ok r, u)) :
    (resolveAliasStepWith structureOf step (.resolve m) ctx).runState u = (.ok r, u) := by
  unfold resolveAliasStepWith staticPathSelectWith
  simp only [Expr.staticAliasPath?, bind_run, hl, aliasStepNavigateWith]
  rfl

/-- **THE STRUCTURE CHASE OF A TRANSPARENT REFERENCE TO A NAMED, NON-ALIAS TARGET, from every
    state.** For a transparent reference whose row is the name `m`, when the lexical lookup of `m`
    in the reference's own scope selects `r` and `r.alg` is no alias: the production structure
    chase returns `r.alg` and changes nothing — from EVERY state. -/
theorem resolveAliasStructure_reference (parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef)
    (m : Ident) (id : Option PropertyIdentity) (ctx : EvalCtx) (r : ResolvedProperty)
    (hl : ∀ t, (lookupLexicalPropertyRaw (.alias parent opens props (.resolve m) id true) m
      (ctx.push (.alias parent opens props (.resolve m) id true))).runState t = (.ok r, t))
    (hg : isAliasAlg r.alg = false) (u : EvalState) :
    (resolveAliasStructure (.alias parent opens props (.resolve m) id true) ctx).runState u =
      (.ok (some r.alg), u) := by
  -- the route decision, at fuel 1
  have h1 : ∀ vis, (evalFuel 1 (.aliasStepIsRuntime (.alias parent opens props (.resolve m) id true)
      (.resolve m) ctx vis)).runState u = (.ok false, u) := fun vis =>
    fuel_succ_of_body 0 (.aliasStepIsRuntime (.alias parent opens props (.resolve m) id true) (.resolve m) ctx vis) u _
      (aliasStepIsRuntime_name (evalFuel 0) (.alias parent opens props (.resolve m) id true) m ctx vis u) nofun
  -- the chase of the target, at fuel 1
  have h2 : ∀ vis last, (evalFuel 1 (.resolveAliasChase false true r.alg ctx vis last)).runState u =
      (.ok (.identity r.alg last), u) := fun vis last =>
    fuel_succ_of_body 0 (.resolveAliasChase false true r.alg ctx vis last) u _
      (chase_not_alias (evalFuel 0) false true r.alg ctx vis last u hg) nofun
  -- the chase of the reference, at fuel 2
  have h3 : (evalFuel 2 (.resolveAliasChase false true (.alias parent opens props (.resolve m) id true)
      ctx [] none)).runState u = (.ok (.identity r.alg (some (r.owner, r.binding))), u) := by
    refine fuel_succ_of_body 1 (.resolveAliasChase false true (.alias parent opens props (.resolve m) id true) ctx []
      none) u (.ok (.identity r.alg (some (r.owner, r.binding))), u) ?_ nofun
    show (EvalBody.resolveAliasChase (evalFuel 1) false true (.alias parent opens props (.resolve m) id true)
      ctx [] none).runState u = _
    unfold EvalBody.resolveAliasChase
    simp only [Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.contains_nil,
      bind_run]
    rw [show (EvalRec.aliasStepIsRuntime (evalFuel 1) (.alias parent opens props (.resolve m) id true)
        (.resolve m) ctx (aliasStructureContext false (aliasChaseKey (.alias parent opens props (.resolve m) id true))
          [])).runState u = (.ok false, u) from h1 _]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_run]
    rw [resolveAliasStep_name _ _ m ctx r u (hl u)]
    exact h2 _ _
  -- the structure chase, at fuel 3
  have h4 : (evalFuel 3 (.resolveAliasStructure (.alias parent opens props (.resolve m) id true) ctx)).runState u =
      (.ok (some r.alg), u) := by
    refine fuel_succ_of_body 2 (.resolveAliasStructure (.alias parent opens props (.resolve m) id true) ctx) u
      (.ok (some r.alg), u) ?_ nofun
    show (EvalBody.resolveAliasStructure (evalFuel 2) (.alias parent opens props (.resolve m) id true) ctx).runState u = _
    unfold EvalBody.resolveAliasStructure
    rw [bind_run]
    rw [show (EvalRec.resolveAliasChase (evalFuel 2) false true (.alias parent opens props (.resolve m) id true)
        ctx [] none).runState u = (.ok (.identity r.alg (some (r.owner, r.binding))), u) from h3]
    rfl
  exact production_of_fuel 3 _ u _ h4 nofun

/-- **A NAME selecting a TRANSPARENT REFERENCE to a named, non-alias target, from its probe.** After
    the production probe of the name `n`, which selects the reference `AB = m`: when the row `m`
    selects, in the reference's own scope, a declaration that is no alias, the navigation is settled
    at the probe's exit — the probe changed nothing and the identity is that declaration. The two
    lookups are derived from one observation each (`lookup_everywhere`). -/
theorem navSettled_reference_of_probe (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm)
    (s s' : EvalState) (owner : Algorithm) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef) (m : Ident) (id : Option PropertyIdentity)
    (hsel : ∀ r, (lookupLexicalPropertyRaw top n ctx).runState s = (.ok r, s) →
      r.alg = .alias parent opens props (.resolve m) id true)
    (target : ResolvedProperty)
    (htarget : (lookupLexicalPropertyRaw (.alias parent opens props (.resolve m) id true) m
      (ctx.push (.alias parent opens props (.resolve m) id true))).runState s = (.ok target, s))
    (hg : isAliasAlg target.alg = false) :
    s' = s ∧ owner = target.alg ∧ NavSettled (.resolve n) ctx owner s' := by
  obtain ⟨r, hl, hrun⟩ := probe_name n ctx top rest s s' owner hcs hprobe
  have hr := hsel r (hl s)
  have hlt := (lookup_everywhere _ m _ s s _ htarget).2
  have hstruct := resolveAliasStructure_reference parent opens props m id ctx target hlt hg
  rw [hr, hstruct s] at hrun
  obtain ⟨h1, h2⟩ := Prod.mk.inj hrun
  have h3 : target.alg = owner := Option.some.inj (Except.ok.inj h1)
  subst h2
  subst h3
  refine ⟨rfl, rfl, navSettled_of (headSettled_name n ctx top rest r hcs hl s) ?_⟩
  rw [hr]
  exact structSettled_of_everywhere hstruct s

/-- **THE MEMBER BRIDGE over a TRANSPARENT REFERENCE, every bundle, from the probe.** For a receiver
    name `n` that selects a transparent reference whose row is a name selecting a declaration that
    is no alias (`AB = Box`): after the production probe and the dot decision selecting the declared
    member `p`, the member-route ordinary call IS the re-counted production dot evaluation
    `n.N(args)`, both run from the SAME state, for EVERY bundle. -/
theorem member_bridge_reference_of_probe (a : Nat) (n N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (top : Algorithm) (rest : List Algorithm) (s s' : EvalState)
    (owner : Algorithm) (p : PropDef) (hcs : ctx.callStack = top :: rest)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hselect : selectDotEdge ctx (.resolve n) N (some owner) = .ok (.member owner p))
    (parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef) (m : Ident) (id : Option PropertyIdentity)
    (hsel : ∀ r, (lookupLexicalPropertyRaw top n ctx).runState s = (.ok r, s) →
      r.alg = .alias parent opens props (.resolve m) id true)
    (target : ResolvedProperty)
    (htarget : (lookupLexicalPropertyRaw (.alias parent opens props (.resolve m) id true) m
      (ctx.push (.alias parent opens props (.resolve m) id true))).runState s = (.ok target, s))
    (hg : isAliasAlg target.alg = false)
    (hprod : ProductionCompletes (evalCounted (.dotMember (.resolve n) N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a
        ⟨.dotMember (.resolve n) N fallback none, args, ctx, env, .dot (.resolve n) N fallback⟩ .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember (.resolve n) N fallback (some args)) ctx env).runState s :=
  member_bridge_of_settled a (.resolve n) N fallback args ctx env s s' (some owner) owner p hprobe hselect
    (fun x _ _ hx => by simp [headParam?] at hx)
    (navSettled_reference_of_probe n ctx top rest s s' owner hcs hprobe parent opens props m id hsel target
      htarget hg).2.2 hprod

end KatLang.MemberSettled
