import KatLangArityLaws.PlanRouteBridge
import KatLangArityLaws.EvaluatorMemoLinks
import KatLangArityLaws.OwnerContextStability

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# Plan conservativity, step 1: the member route over every bundle (ledger E-18, M1)

`PlanRouteBridge.member_bridge` identifies the member-route ordinary call with ordinary dot
evaluation for a bundle with a plain first slot, `member_bridge_inert` for every bundle over a
receiver whose navigation is state-inert from EVERY state (`NavInert`). The remaining class — an
empty or spread-first bundle (`t.N()`, `t.N(xs*)`) over a receiver whose first navigation WRITES
(a parameter's first CALLABLE projection, a runtime-target alias's binding cell and projection) —
is closed here relative to ONE whole-run invariant, and that invariant is proved for parameters.

* **The memo extension `MemoExt s t`** assembles the whole-run relations the evaluator already
  preserves: every existing cell's suspension, completed VALUE, prepared supply and recorded route
  (`HeapKept`, `EvaluatorDiscipline`), its completed CALLABLE outcome and recorded callee/receiver
  cells (`LinkHeapKept`, `EvaluatorMemoLinks`), and the recorded parameter activations
  (`ActivationPrefix`, `OwnerContextStability`). Every production operation and the production
  supply formation relate their entry state to their exit state by it (`production_memoExt`,
  `form_memoExt`) — alias resolution, supply formation with arbitrary spread code, allocations and
  memo writes included.
* **The stability invariant `NavStable target ctx owner t`**: from every memo extension of `t`, the
  receiver's structure as the plan's callee law reads it (`projectedStructure`) is `owner`, and
  reading it changes nothing. It is upward closed (`NavStable.mono`), hence preserved by every
  production operation and by supply formation (`navStable_production`, `navStable_form`); it is
  ESTABLISHED at the probe's exit state by `NavStable.of_inert` (every `NavInert` receiver),
  `navStable_param` (a parameter whose CALLABLE is structure-normal: the first projection's memo,
  `projectNeedCallable_publishes`, read back from every extension) and `navStable_member` (a
  declared member step over a stable receiver).
* **The member bridge over every bundle**: `member_bridge_settled` is the exact statement — the
  run equality holds whenever the receiver's navigation is settled at the ONE state where the
  callee origin is read (after alias resolution and supply formation); `member_bridge_stable`
  discharges that from `NavStable` at the probe's exit; `member_bridge_param_stable` is the closed
  instance for a parameter receiver `b.N(args)`, every bundle, with no `NavInert` premise.

## Boundary

The premise is NECESSARY: `MemberStabilityGuards.memberOriginRemintsRuntimeIdentity` is a permanent
witness of a reached state on which exact run equality FAILS for an empty and for a spread-first
bundle — a runtime-target alias whose `.Algorithm` receiver is a dot result (`MTA = 5.MkFM.Algorithm`)
re-decides its route at every navigation, and that decision mints a fresh runtime declaration
identity (`identifyRuntimeAlgorithm`). The outcomes agree; the plan's final state has one more
minted identity (`EvalState.nextRuntimeDeclaration`). The member bridge above establishes exact run
equality wherever the receiver's navigation is settled.

## The strengthened extension (review repair, November 2026)

The independent review showed `MemoExt` too weak for the missing instances: it does not constrain
`aliasCells` at all (`MemoExt.withoutAliasCells`), and `MemberStabilityGuards.aliasMemosNotProtected`
starts at the successful probe of `RTA` and shows that deleting its recorded alias memo — an
allowed `MemoExt`, NOT a production transition — makes navigation allocate again. REPAIRED in the
last section of this module:

* `NavKept` — every recorded alias binding cell is still recorded, under its key and at its
  address, and the runtime-declaration counter has not gone back — is a WHOLE-RUN relation:
  `production_navKept` (every production operation, every state, every outcome), `navKept_core`
  (every completed core run), `form_navKept` (supply formation, whatever spread code it runs). It
  rests on `EvaluatorCacheLaws.WriteFrame`, extended for it: a framed write now also keeps the
  alias table and the counter, and their two writers are accepted as what they are
  (`aliasBindingCellRecorded` records only a key its own lookup did not find;
  `identifyRuntimeAlgorithm` advances the counter by one).
* `NavExt` is `MemoExt` with `NavKept`; the deletion is not one (`NavExt.not_withoutAliasCells`).
* `NavSettled` is stability over `NavExt` only, and `member_bridge_navSettled` is the member bridge
  for EVERY bundle from it. Every `NavStable` receiver is `NavSettled` (`NavStable.navSettled`).

NOT proved in this module: `NavSettled` FROM THE PROBE for the receiver classes beyond state-inert
names and parameters. The closing pass does part of it in `MemberSettled.lean`: the lexical lookup
is state-free (so a name selected through `open` is derived like a declared one), a transparent
reference whose row is a name selecting a non-alias target has its alias chase unfolded, and
member steps and parameter heads compose (nested member paths, parameter-rooted paths);
`MemberBridgeSourceInstances` (and three companions) apply `member_bridge_settled` to genuine
source programs over every class and bundle kind, and `MemberSettledInstances` applies the derived
theorems. M1 STAYS PARTIAL on what is still missing: the unfolding of the chase of a RUNTIME-TARGET
alias (`aliasStepIsRuntime`, `aliasBindingCell`, the binding cell's CALLABLE) and of a reference
whose row is a member path or whose chase has several steps, to the statement that a completed
first navigation is read back from every navigation extension — the guards decide the settledness
premise on those classes (`MemberStabilityGuards.settledAt`) and the instances establish it on the
run's own states; the survival of an in-flight CALLABLE mark; and structure-normality of every
stored CALLABLE as a heap invariant (the parameter theorems take it as the decidable premise
`structureNormal owner`).

THE M1 COMPLETION PASS (same month) proves what that paragraph lists as missing, in other modules:
`NavigationReread.navigation_reread` — a completed, non-minting identity navigation is re-read from
every navigation extension, WITHOUT unfolding any shape and without deciding an alias key —
`NavigationSettled.navSettled_of_navRuns` / `member_bridge_of_probe` (settled navigation and the
member bridge from the probe, every non-minting receiver class) and `probe_member`; the in-flight
mark is `MemoLinks.LinkKept.projecting`; structure-normality is derived for written arguments in
`StoredCallableNormal`. What stays unproved is stated there: that every reachable probe reads only
recorded data (`NavigationAdmission`: each clause of that admission is necessary; the activation
clause is reduced to a recorded site chain). Normality of EVERY published CALLABLE on a reached
state — link-bound and already-projected cells included — is a whole-run theorem since the
independent review pass (`PublishedCallableNormal`). The minting class (`memberOriginRemintsRuntimeIdentity`) is a genuine
counterexample to exact run equality and is outside every theorem here; whether a weaker relation
(equality up to a renaming of later-minted runtime identities) should replace exact equality there
is an OWNER DECISION that is pending (`MemberStabilityGuards`, § Is the minted identity observable?).
Only completed runs.
-/

namespace KatLang.MemberStability

open KatLang.PlanRouteBridge
open KatLang.PlanConservativity (isAliasAlg resolveAliasTarget_not_alias resolved_body_not_alias)
open KatLang.WhileRoundProduction (Finite finite_const finite_call finite_bind production_eq_of_finite
  production_of_answer_free)
open KatLang.MemoLinks (LinkHeapKept LinkKept evalUnbounded_linkDisc linkDisc_form)
open KatLang.OwnerContextStability (ActivationPrefix production_retained Retained)

/-! ## The memo extension -/

/-- **The memo extension.** Everything a settled navigation reads at `s` is still there at `t`:
    every cell with its suspension, completed VALUE, prepared supply and recorded route
    (`HeapKept`), its completed CALLABLE outcome and recorded callee/receiver cells
    (`LinkHeapKept`), and every recorded parameter activation (`ActivationPrefix`). -/
structure MemoExt (s t : EvalState) : Prop where
  heap : HeapKept s.needs t.needs
  links : LinkHeapKept s.needs t.needs
  activations : ActivationPrefix s t

theorem MemoExt.refl (s : EvalState) : MemoExt s s :=
  ⟨HeapKept.refl _, LinkHeapKept.refl _, ActivationPrefix.refl s⟩

theorem MemoExt.trans {s t u : EvalState} (h₁ : MemoExt s t) (h₂ : MemoExt t u) : MemoExt s u :=
  ⟨h₁.heap.trans h₂.heap, h₁.links.trans h₂.links, h₁.activations.trans h₂.activations⟩

/-- Diagnostic of the current relation's boundary: it allows losing every recorded alias memo.
    This is not a production transition; a stability proof for aliases needs a stronger relation. -/
theorem MemoExt.withoutAliasCells (s : EvalState) : MemoExt s { s with aliasCells := [] } :=
  ⟨HeapKept.refl _, LinkHeapKept.refl _, ActivationPrefix.of_eq rfl⟩

/-- **Every production operation extends the memos** — from every state, whatever its outcome
    (`evalUnbounded_disciplined`, `evalUnbounded_linkDisc`, `production_retained`). -/
theorem production_memoExt (c : EvalCall) (s : EvalState) : MemoExt s ((evalUnbounded c).runState s).2 :=
  ⟨KatLang.EvaluatorDiscipline.evalUnbounded_disciplined c s, evalUnbounded_linkDisc c s,
    (production_retained c s).1⟩

/-- **Production supply formation extends the memos**, whatever spread code it runs. -/
theorem form_memoExt (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) (s : EvalState) :
    MemoExt s ((NeedSupply.form evalSupplySpread ctx env args).runState s).2 :=
  ⟨disciplined_form evalSupplySpread
      (fun e c v => KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.evalSupplySpread e c v)) ctx env args s,
    linkDisc_form evalSupplySpread (fun e c v => evalUnbounded_linkDisc (.evalSupplySpread e c v)) ctx env args s,
    (KatLang.EvaluatorCacheLaws.pres_form (R := Retained) evalSupplySpread
      (fun e c v => production_retained (.evalSupplySpread e c v)) ctx env args s).1⟩

/-! ## The stability invariant -/

/-- **Stable receiver navigation.** From every memo extension of `t`, the receiver's structure as
    the plan's callee law reads it is `owner`, and reading it changes nothing: every first-time
    write of the navigation (a CALLABLE memo, a recorded cell) has been made, and is read back. -/
def NavStable (target : Expr) (ctx : EvalCtx) (owner : Algorithm) (t : EvalState) : Prop :=
  ∀ u, MemoExt t u → (projectedStructure target ctx).runState u = (.ok (some owner), u)

/-- Stability is upward closed along memo extension. -/
theorem NavStable.mono {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t u : EvalState}
    (h : NavStable target ctx owner t) (he : MemoExt t u) : NavStable target ctx owner u :=
  fun v hv => h v (he.trans hv)

/-- A stable navigation is settled at its own state. -/
theorem NavStable.settled {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavStable target ctx owner t) : (projectedStructure target ctx).runState t = (.ok (some owner), t) :=
  h t (MemoExt.refl t)

/-- **Stability is a whole-run invariant**: every production operation preserves it, whatever the
    operation's outcome. -/
theorem navStable_production {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavStable target ctx owner t) (c : EvalCall) :
    NavStable target ctx owner ((evalUnbounded c).runState t).2 :=
  h.mono (production_memoExt c t)

/-- Production supply formation preserves stability. -/
theorem navStable_form {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavStable target ctx owner t) (c : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    NavStable target ctx owner ((NeedSupply.form evalSupplySpread c env args).runState t).2 :=
  h.mono (form_memoExt c env args t)

/-- A state-inert navigation (`NavInert`) is stable at every state. -/
theorem NavStable.of_inert {target : Expr} {ctx : EvalCtx} {owner : Algorithm}
    (h : NavInert target ctx owner) (t : EvalState) : NavStable target ctx owner t :=
  fun u _ => h u

/-- One declared, accessible, structure-normal member step keeps the navigation stable. -/
theorem navStable_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (a : Algorithm) (q : PropDef)
    (t : EvalState) (h : NavStable o ctx a t) (hl : Algorithm.lookupPropDefAny? a n = some q)
    (hacc : memberAccessible? ctx a q = true)
    (hn : structureNormal (childOfInContext a q.alg ctx) = true) :
    NavStable (.dotMember o n fb none) ctx (childOfInContext a q.alg ctx) t := by
  intro u hu
  have hstep := member_projection_run o n fb ctx u u a q (h u hu) hl hacc
  unfold projectedStructure
  rw [bind_run, hstep]
  dsimp only
  rw [resolveAliasStructure_normal _ ctx hn]
  rfl

/-! ## The callee origin, read at one state -/

/-- **Where the receiver's navigation is settled, the written origin IS the bound origin**: at a
    state `t` from which the receiver's projected structure is `owner` without any state change,
    the property binding the argumentless path `target.N` names is the selected member's.
    (`PlanRouteBridge.written_origin_is_bound` is this at every state of a `NavInert` receiver.) -/
theorem written_origin_is_bound_at (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx)
    (owner : Algorithm) (p : PropDef) (t : EvalState)
    (hn : (projectedStructure target ctx).runState t = (.ok (some owner), t))
    (hlook : Algorithm.lookupPropDefAny? owner N = some p) :
    (EvalBody.originBinding? evalUnbounded (.written (.dotMember target N fallback none) ctx) ctx).runState t =
      (EvalBody.originBinding? evalUnbounded (.bound owner p) ctx).runState t := by
  unfold projectedStructure at hn
  rw [bind_run] at hn
  rcases hh : (projectNeedStructuralMember target ctx).runState t with ⟨o, t1⟩
  rw [hh] at hn
  cases o with
  | error e => cases hn
  | ok container =>
    cases container with
    | none => cases hn
    | some selected =>
      have hs : (resolveAliasStructure selected ctx).runState t1 = (.ok (some owner), t) := hn
      have hh' : (EvalRec.projectNeedStructuralMember evalUnbounded target ctx).runState t =
          (.ok (some selected), t1) := hh
      have hs' : (EvalRec.resolveAliasStructure evalUnbounded selected ctx).runState t1 = (.ok (some owner), t) := hs
      unfold EvalBody.originBinding?
      dsimp only
      unfold EvalBody.writtenCalleeBinding?
      dsimp only
      rw [bind_run, evalAttempt_runState_of_complete _ t t1 _ hh' rfl]
      dsimp only
      rw [bind_run, evalAttempt_runState_of_complete _ t1 t _ hs' rfl]
      dsimp only
      rw [hlook]

/-- Two origins whose property bindings read alike at the state supply formation leaves make the
    resolved call of a normalized callee alike, over ANY bundle. (`resolved_origin_agrees` asks for
    the agreement at every state.) -/
theorem resolved_origin_agrees_at (o₁ o₂ : CalleeOrigin) (g : Algorithm) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (t : EvalState) (hg : isAliasAlg g = false)
    (hagree : ∀ cells u, (NeedSupply.form evalSupplySpread ctx env args).runState t = (.ok cells, u) →
      (EvalBody.originBinding? evalUnbounded o₁ ctx).runState u =
        (EvalBody.originBinding? evalUnbounded o₂ ctx).runState u)
    (hc : ProductionCompletes (evalResolvedCallCounted g args ctx env name o₂) t) :
    (evalResolvedCallCounted g args ctx env name o₁).runState t =
      (evalResolvedCallCounted g args ctx env name o₂).runState t := by
  have hu₂ := production_unfolds (.evalResolvedCallCounted g args ctx env name o₂) t hc
  have hb₂ : (evalResolvedCallCounted g args ctx env name o₂).runState t =
      (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t := by
    show (evalUnbounded (.evalResolvedCallCounted g args ctx env name o₂)).runState t = _
    rw [← hu₂]
    show (EvalBody.evalResolvedCallCounted evalUnbounded g args ctx env name o₂).runState t = _
    rw [resolved_body_not_alias _ _ _ _ _ _ _ hg]
    rfl
  have hbody : (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₁ g cells ctx env name).runState t =
      (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t := by
    have hc' : ((NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t).1 ≠ .error .fuelExhausted := by
      rw [← hb₂]; exact hc
    rw [bind_run] at hc' ⊢
    rw [bind_run]
    rcases hf : (NeedSupply.form evalSupplySpread ctx env args).runState t with ⟨fo, t2⟩
    rw [hf] at hc'
    cases fo with
    | error e => rfl
    | ok cells => exact supplied_origin_agrees o₁ o₂ g cells ctx env name t2 hg (hagree cells t2 hf) hc'
  have hstep : ∀ rec, evalStep rec (.evalResolvedCallCounted g args ctx env name o₁) =
      (NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
        rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) := by
    intro rec
    show EvalBody.evalResolvedCallCounted rec g args ctx env name o₁ = _
    rw [resolved_body_not_alias _ _ _ _ _ _ _ hg]
    rfl
  have hfin : Finite (fun rec : EvalRec => NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
      rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) :=
    finite_bind (finite_form ctx env args) (fun _ => finite_call _)
  have hc₁ : ProductionCompletes ((fun rec : EvalRec => NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
      rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) evalUnbounded) t := by
    unfold ProductionCompletes
    show ((NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₁ g cells ctx env name).runState t).1 ≠ _
    rw [hbody, ← hb₂]; exact hc
  have h₁ := production_eq_of_finite (.evalResolvedCallCounted g args ctx env name o₁) _ hstep hfin t hc₁
  exact h₁.trans (hbody.trans hb₂.symm)

/-- Two origins whose property bindings read alike at the ONE state where the member run reads its
    origin — after the selected member's alias resolution and the supply formation — make the member
    run alike, over any bundle. -/
theorem memberRun_origin_agrees_at (owner : Algorithm) (p : PropDef) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (o₁ o₂ : CalleeOrigin) (s' : EvalState)
    (hagree : ∀ g t cells u,
      (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' = (.ok g, t) →
      (NeedSupply.form evalSupplySpread ctx env args).runState t = (.ok cells, u) →
      (EvalBody.originBinding? evalUnbounded o₁ ctx).runState u =
        (EvalBody.originBinding? evalUnbounded o₂ ctx).runState u)
    (hc : ProductionCompletes (memberRun owner p args ctx env name o₂) s') :
    (memberRun owner p args ctx env name o₁).runState s' = (memberRun owner p args ctx env name o₂).runState s' := by
  unfold memberRun at hc ⊢
  unfold ProductionCompletes at hc
  rw [bind_run] at hc ⊢
  rw [bind_run]
  rcases hr : (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' with ⟨ro, t1⟩
  rw [hr] at hc
  cases ro with
  | error e => rfl
  | ok g =>
    exact resolved_origin_agrees_at o₁ o₂ g args ctx env name t1
      (resolveAliasTarget_not_alias _ ctx s' t1 g hr) (fun cells u hf => hagree g t1 cells u hr hf) hc

/-! ## The member bridge over every bundle -/

theorem lookup_of_selection (ctx : EvalCtx) (target : Expr) (N : Ident) (alg? : Option Algorithm)
    (owner : Algorithm) (p : PropDef) (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p)) :
    Algorithm.lookupPropDefAny? owner N = some p := by
  cases alg? with
  | none => simp [selectDotEdge] at hsel
  | some owner' =>
    obtain ⟨rfl, hlook, -⟩ := select_member ctx target N owner' owner p hsel
    exact hlook

/-- **THE MEMBER BRIDGE, every bundle, relative to settled navigation at the origin read.** After a
    receiver probe completing at `(.ok alg?, s')` that selects the declared member `p` of `owner`,
    with the plan's structural projection of the argumentless path reaching that member at `s'`:
    whenever the receiver's navigation is SETTLED at the state the member run reads its callee
    origin in — after the member's alias resolution and the supply formation, each completed —
    the member-route ordinary call IS the re-counted production dot evaluation `target.N(args)`,
    both run from the SAME state `s`: outcome, error context, final state and the CACHE-PUB-1
    publication an empty supply makes. No restriction on the bundle. The premise is necessary
    (`MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`). -/
theorem member_bridge_settled (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hsettled : ∀ g t cells u,
      (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' = (.ok g, t) →
      (NeedSupply.form evalSupplySpread ctx env args).runState t = (.ok cells, u) →
      (projectedStructure target ctx).runState u = (.ok (some owner), u))
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s := by
  have hlook := lookup_of_selection ctx target N alg? owner p hsel
  exact member_bridge_of_origin a target N fallback args ctx env s s' alg? owner p hprobe hsel hproj
    (memberRun_origin_agrees_at owner p args ctx env N _ _ s'
      (fun g t cells u hr hf =>
        written_origin_is_bound_at target N fallback ctx owner p u (hsettled g t cells u hr hf) hlook)
      (memberRun_completes_of_dot target N fallback args ctx env s s' alg? owner p hprobe hsel hprod)) hprod

/-- A stable navigation at the probe's exit is settled where the member run reads its origin. -/
theorem settled_of_stable (target : Expr) (ctx : EvalCtx) (owner : Algorithm) (wired : Algorithm)
    (env : ValEnv) (args : OutputBundle) (s' : EvalState) (hstable : NavStable target ctx owner s')
    (g : Algorithm) (t : EvalState) (cells : List NeedSupply.Sourced) (u : EvalState)
    (hr : (resolveAliasTarget wired ctx).runState s' = (.ok g, t))
    (hf : (NeedSupply.form evalSupplySpread ctx env args).runState t = (.ok cells, u)) :
    (projectedStructure target ctx).runState u = (.ok (some owner), u) := by
  have h1 : MemoExt s' t := by
    have := production_memoExt (.resolveAliasTarget wired ctx) s'
    have hrun : (evalUnbounded (.resolveAliasTarget wired ctx)).runState s' = (.ok g, t) := hr
    rw [hrun] at this
    exact this
  have h2 : MemoExt t u := by
    have := form_memoExt ctx env args t
    rw [hf] at this
    exact this
  exact hstable u (h1.trans h2)

/-- **THE MEMBER BRIDGE over a stable receiver, for EVERY bundle** — `t.N()`, `t.N(xs*)` and every
    other written list. After a probe completing at `(.ok alg?, s')` that selects the declared member
    `p` of `owner`, with the plan's projection reaching it at `s'`: when the receiver's navigation is
    STABLE at `s'` (`NavStable` — a whole-run invariant, preserved by the member's alias resolution
    and by the supply formation whatever spread code it runs), the member-route ordinary call IS the
    re-counted production dot evaluation, both run from the SAME state `s`. `NavInert` is the
    special case of a navigation that writes nothing (`NavStable.of_inert`). -/
theorem member_bridge_stable (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hstable : NavStable target ctx owner s')
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_settled a target N fallback args ctx env s s' alg? owner p hprobe hsel hproj
    (fun g t cells u hr hf =>
      settled_of_stable target ctx owner _ env args s' hstable g t cells u hr hf) hprod

/-- `member_bridge_stable` with the receiver premise discharged by the probe and the selection
    (`member_projection_of_selection`; a parameter-rooted receiver needs `hnorm`). -/
theorem member_bridge_stable_of_selection (a : Nat) (target : Expr) (N : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hnorm : ∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true)
    (hstable : NavStable target ctx owner s')
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_stable a target N fallback args ctx env s s' alg? owner p hprobe hsel
    (member_projection_of_selection target N fallback ctx s s' alg? owner p hprobe hsel hnorm) hstable hprod

/-! ## Parameter receivers: the first projection's memo -/

/-- **A completed CALLABLE projection is published.** After a production projection of cell `a`
    that returns `r`, the cell's CALLABLE state is `projected (.ok r)` at the exit state — whether
    this run projected it or found it projected. -/
theorem projectNeedCallable_publishes (a : Nat) (s t : EvalState) (r : Option Algorithm)
    (h : (projectNeedCallable a).runState s = (.ok r, t)) :
    ∃ cell, t.needs[a]? = some cell ∧ cell.callable = .projected (.ok r) := by
  have hc : ProductionCompletes (projectNeedCallable a) s := by
    unfold ProductionCompletes; rw [h]; nofun
  have hu := production_unfolds (.projectNeedCallable a) s hc
  have h' : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
      (.ok r, t) := hu.trans h
  cases hcell : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Projection.invalid_address _ a s hcell] at h'
    cases h'
  | some cell =>
    cases hcal : cell.callable with
    | projected outcome =>
      rw [KatLang.NeedControl.Projection.projected_sticky _ a s cell outcome hcell hcal] at h'
      injection h' with h1 h2
      subst h1 h2
      exact ⟨cell, hcell, hcal⟩
    | projecting =>
      rw [KatLang.NeedControl.Projection.projecting_reentry_cycle _ a s cell hcell hcal] at h'
      cases h'
    | unprojected =>
      -- the cell survives the whole projection (discipline), so the final write lands on it
      obtain ⟨c', hc', -⟩ := KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.projectNeedCallable a) s a cell hcell
      have hfin : ((evalUnbounded (.projectNeedCallable a)).runState s).2 = t := by
        show ((projectNeedCallable a).runState s).2 = t
        rw [h]
      rw [hfin] at hc'
      rcases hrun : (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a) cell.suspension).runState
          (KatLang.NeedControl.Projection.setCallable a .projecting s) with ⟨outcome, t₀⟩
      cases hinc : outcome.isIncomplete with
      | true =>
        have hoe := Except.isIncomplete_eq_true hinc
        subst hoe
        have hstep : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
            (.error .fuelExhausted, t₀) := by
          simp only [NeedProjection.step, bind_run, get_run, hcell, hcal, EvalM.modify_runState]
          simp only [KatLang.NeedControl.Projection.setCallable] at hrun
          rw [evalAttempt_runState_of_incomplete _ _ _ hrun]
        rw [hstep] at h'
        cases h'
      | false =>
        rw [KatLang.NeedControl.Projection.unprojected_publishes _ a s t₀ cell outcome hcell hcal hrun hinc] at h'
        injection h' with h1 h2
        subst h1
        have hget : (KatLang.NeedControl.Projection.setCallable a (.projected (.ok r)) t₀).needs[a]? = some c' := by
          rw [h2]; exact hc'
        simp only [KatLang.NeedControl.Projection.setCallable, Array.getElem?_modify, ite_true] at hget
        cases hcur : t₀.needs[a]? with
        | none => rw [hcur] at hget; cases hget
        | some current =>
          rw [hcur] at hget
          simp only [Option.map_some] at hget
          injection hget with hget
          refine ⟨c', hc', ?_⟩
          rw [← hget]

/-- **A published CALLABLE is read back.** From any state where cell `a` holds the completed
    projection outcome `.ok r`, the production projection returns `r` and changes nothing. -/
theorem projectNeedCallable_memo (a : Nat) (u : EvalState) (cell : NeedCell) (r : Option Algorithm)
    (hc : u.needs[a]? = some cell) (hm : cell.callable = .projected (.ok r)) :
    (projectNeedCallable a).runState u = (.ok r, u) := by
  apply production_of_answer_free (.projectNeedCallable a) u (.ok r, u)
  · intro rec
    show (NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt a)) a).runState u = _
    exact KatLang.NeedControl.Projection.projected_sticky _ a u cell (.ok r) hc hm
  · nofun

/-- The lexical activation a parameter is captured in, read from the context alone
    (`capturedParameterActivation?` without its one state read). -/
def capturedId? (name : Ident) (ctx : EvalCtx) : Option Nat :=
  match ctx.head?, siteScope? ctx with
  | some site, some scope =>
      if site.params.contains name then none
      else scope.parent >>= fun parent => (requiredParameterOwner? parent name).bind ScopeCtx.activation
  | _, _ => none

/-- `capturedParameterActivation?` reads ONE record of the activation array and writes nothing. -/
theorem captured_run (name : Ident) (ctx : EvalCtx) (s : EvalState) :
    (capturedParameterActivation? name ctx).runState s =
      (.ok ((capturedId? name ctx).bind (fun id => s.lexicalActivations[id]?)), s) := by
  unfold capturedParameterActivation? capturedId?
  cases ctx.head? with
  | none => rfl
  | some site =>
    cases siteScope? ctx with
    | none => rfl
    | some scope =>
      dsimp only
      cases site.params.contains name with
      | true => rfl
      | false =>
        generalize (scope.parent >>= fun parent => (requiredParameterOwner? parent name).bind ScopeCtx.activation) = id
        cases id <;> rfl

/-- The supplied cell of a parameter over an activation array (`projectParameterWith`'s lookup). -/
def parameterAddressIn (acts : Array ParameterActivation) (x : Ident) (ctx : EvalCtx) : Option Nat :=
  lookupAssoc x (((capturedId? x ctx).bind (fun id => acts[id]?)).map ParameterActivation.needs |>.getD ctx.needEnv)

theorem projectParameterWith_run (project : Nat → EvalM (Option Algorithm)) (x : Ident) (ctx : EvalCtx)
    (s : EvalState) :
    (projectParameterWith project x ctx).runState s =
      (match parameterAddressIn s.lexicalActivations x ctx with
       | some address => (project address).runState s
       | none => (.ok none, s)) := by
  unfold projectParameterWith parameterAddressIn
  rw [bind_run, captured_run]
  dsimp only
  split <;> rename_i h <;> simp only [h] <;> rfl

/-- A recorded activation keeps a parameter's supplied cell across every activation extension. -/
theorem parameterAddressIn_stable (x : Ident) (ctx : EvalCtx) (s u : EvalState) (h : ActivationPrefix s u)
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size) :
    parameterAddressIn u.lexicalActivations x ctx = parameterAddressIn s.lexicalActivations x ctx := by
  unfold parameterAddressIn
  cases hid : capturedId? x ctx with
  | none => rfl
  | some id =>
    simp only [Option.bind_some]
    rw [h.lookup (hact id hid)]

theorem finite_projectParameter (x : Ident) (ctx : EvalCtx) :
    Finite (fun rec : EvalRec => projectParameterWith rec.projectNeedCallable x ctx) := by
  unfold projectParameterWith
  refine finite_bind (finite_const _) (fun activation => ?_)
  split
  · exact finite_call _
  · exact finite_const _

/-- **A parameter's CALLABLE is stable once projected.** After a production projection of the
    parameter `x` that returns the identity `owner` (the probe of a parameter receiver), from every
    memo extension of the exit state the projection returns `owner` again and changes nothing: the
    supplied cell is found through the same recorded activation, and its memo is read back. -/
theorem projectParameterCallable_stable (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (owner : Algorithm)
    (hrun : (projectParameterCallable x ctx).runState s = (.ok (some owner), s'))
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size) :
    ∀ u, MemoExt s' u → (projectParameterCallable x ctx).runState u = (.ok (some owner), u) := by
  have hc : ProductionCompletes (projectParameterCallable x ctx) s := by
    unfold ProductionCompletes; rw [hrun]; nofun
  have hu := production_unfolds (.projectParameterCallable x ctx) s hc
  have hbody : (projectParameterWith (EvalRec.projectNeedCallable evalUnbounded) x ctx).runState s = (.ok (some owner), s') :=
    hu.trans hrun
  rw [projectParameterWith_run] at hbody
  have hext : MemoExt s s' := by
    have := production_memoExt (.projectParameterCallable x ctx) s
    have hr : (evalUnbounded (.projectParameterCallable x ctx)).runState s = (.ok (some owner), s') := hrun
    rw [hr] at this
    exact this
  cases haddr : parameterAddressIn s.lexicalActivations x ctx with
  | none => rw [haddr] at hbody; cases hbody
  | some address =>
    rw [haddr] at hbody
    have hproj : (projectNeedCallable address).runState s = (.ok (some owner), s') := hbody
    obtain ⟨cell, hcell, hmemo⟩ := projectNeedCallable_publishes address s s' (some owner) hproj
    intro u hu'
    obtain ⟨cell', hcell', hk⟩ := hu'.links address cell hcell
    have hread := projectNeedCallable_memo address u cell' (some owner) hcell' (hk.callable _ hmemo)
    have haddr' : parameterAddressIn u.lexicalActivations x ctx = some address := by
      rw [parameterAddressIn_stable x ctx s u (hext.activations.trans hu'.activations) hact, haddr]
    have hbody' : (projectParameterWith (EvalRec.projectNeedCallable evalUnbounded) x ctx).runState u = (.ok (some owner), u) := by
      rw [projectParameterWith_run, haddr']
      exact hread
    have hcb : ProductionCompletes ((fun rec : EvalRec => projectParameterWith rec.projectNeedCallable x ctx) evalUnbounded) u := by
      unfold ProductionCompletes; rw [hbody']; nofun
    exact (production_eq_of_finite (.projectParameterCallable x ctx)
      (fun rec => projectParameterWith rec.projectNeedCallable x ctx) (fun _ => rfl)
      (finite_projectParameter x ctx) u hcb).trans hbody'

/-- **A parameter receiver's navigation is stable after its first projection.** When the production
    projection of the parameter `x` returns the structure-normal identity `owner` at `s'`, the
    receiver `x` is stable at `s'`: the plan's later navigation — at the origin read — finds `owner`
    through the cell's CALLABLE memo, whatever ran in between. -/
theorem navStable_param (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (owner : Algorithm)
    (hrun : (projectParameterCallable x ctx).runState s = (.ok (some owner), s'))
    (hnormal : structureNormal owner = true)
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size) :
    NavStable (.param x) ctx owner s' := by
  intro u hu
  have hcall := projectParameterCallable_stable x ctx s s' owner hrun hact u hu
  have hhead : (projectNeedStructuralMember (.param x) ctx).runState u = (.ok (some owner), u) := by
    have hcb : ProductionCompletes ((fun rec : EvalRec => rec (.projectParameterCallable x ctx)) evalUnbounded) u := by
      unfold ProductionCompletes
      show ((projectParameterCallable x ctx).runState u).1 ≠ _
      rw [hcall]; nofun
    exact (production_eq_of_finite (.projectNeedStructuralMember (.param x) ctx)
      (fun rec => rec (.projectParameterCallable x ctx)) (fun _ => rfl)
      (finite_call _) u hcb).trans hcall
  unfold projectedStructure
  rw [bind_run, hhead]
  dsimp only
  rw [resolveAliasStructure_normal owner ctx hnormal]
  rfl

/-- The probe of a parameter receiver IS that parameter's CALLABLE projection. -/
theorem probe_param (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (alg? : Option Algorithm)
    (hprobe : (resolveDotReceiver? (.param x) ctx).runState s = (.ok alg?, s')) :
    (projectParameterCallable x ctx).runState s = (.ok alg?, s') := by
  have hpc : ProductionCompletes (resolveDotReceiver? (.param x) ctx) s := by
    unfold ProductionCompletes; rw [hprobe]; nofun
  exact (production_unfolds (.resolveDotReceiver? (.param x) ctx) s hpc).trans hprobe

/-- **A parameter receiver's PROBE is stable once it has run.** After the receiver probe of the
    parameter `x` answers `owner` at `s'`, from every memo extension of `s'` the probe answers
    `owner` again and changes nothing. So the route a plan RECORDED for `x.N(args)` or
    `x.Algorithm(args)` is the route production selects at any later state of the run: the route
    premise of a bridge over a parameter receiver follows from the classification's own probe. (Over
    other receivers it stays explicit: a probe can mint a runtime identity —
    `MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`.) -/
theorem probe_param_stable (x : Ident) (ctx : EvalCtx) (s s' : EvalState) (owner : Algorithm)
    (hprobe : (resolveDotReceiver? (.param x) ctx).runState s = (.ok (some owner), s'))
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size) :
    ∀ u, MemoExt s' u → (resolveDotReceiver? (.param x) ctx).runState u = (.ok (some owner), u) := by
  intro u hu
  have hcall := projectParameterCallable_stable x ctx s s' owner (probe_param x ctx s s' (some owner) hprobe) hact u hu
  have hcb : ProductionCompletes ((fun rec : EvalRec => rec (.projectParameterCallable x ctx)) evalUnbounded) u := by
    unfold ProductionCompletes
    show ((projectParameterCallable x ctx).runState u).1 ≠ _
    rw [hcall]; nofun
  exact (production_eq_of_finite (.resolveDotReceiver? (.param x) ctx)
    (fun rec => rec (.projectParameterCallable x ctx)) (fun _ => rfl)
    (finite_call _) u hcb).trans hcall

/-- **THE MEMBER BRIDGE for a parameter receiver `b.N(args)`, EVERY bundle** — `b.N()` and
    `b.N(xs*)` included, with no state-inertness premise. After the probe of the parameter completes
    at `(.ok (some owner), s')` — its first CALLABLE projection, or a read of the memo — and selects
    the declared member `p`, when the projected CALLABLE is structure-normal and the parameter's
    captured activation, if it has one, is recorded: the member-route ordinary call IS the re-counted
    production dot evaluation, both run from the SAME state `s` — outcome, error context, final
    state and publication. -/
theorem member_bridge_param_stable (a : Nat) (x : Ident) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? (.param x) ctx).runState s = (.ok (some owner), s'))
    (hsel : selectDotEdge ctx (.param x) N (some owner) = .ok (.member owner p))
    (hnormal : structureNormal owner = true)
    (hact : ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size)
    (hprod : ProductionCompletes (evalCounted (.dotMember (.param x) N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a
        ⟨.dotMember (.param x) N fallback none, args, ctx, env, .dot (.param x) N fallback⟩ .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember (.param x) N fallback (some args)) ctx env).runState s := by
  have hcall := probe_param x ctx s s' (some owner) hprobe
  refine member_bridge_stable_of_selection a (.param x) N fallback args ctx env s s' (some owner) owner p
    hprobe hsel ?_ (navStable_param x ctx s s' owner hcall hnormal hact) hprod
  intro y o t hy hrun
  have hxy : y = x := by
    simp only [headParam?, Option.some.injEq] at hy
    exact hy.symm
  subst hxy
  rw [hcall] at hrun
  injection hrun with h1 _
  injection h1 with h1
  injection h1 with h1
  subst h1
  exact hnormal

/-! ## The navigation extension: recorded alias cells and the runtime-identity counter protected

`MemoExt` says nothing of `EvalState.aliasCells`: it relates a state to the same state with every
recorded alias binding cell DELETED (`MemoExt.withoutAliasCells`), from which a runtime-target
alias navigates by allocating again (`MemberStabilityGuards.aliasMemosNotProtected`). No
production operation deletes a record; the relation was too weak to say so. `NavKept` says it, as
a WHOLE-RUN relation: every recorded alias binding cell is still recorded — under its key, at its
address — and the runtime-declaration counter has not gone back. It is write-framed
(`EvaluatorCacheLaws.WriteFrame`, whose `keep` now also keeps these two fields, with the alias
table's one writer `aliasBindingCellRecorded` accepted as a record under a key ABSENT at an earlier
related state and the counter's one writer `identifyRuntimeAlgorithm` as one advance), so every
evaluator body preserves it whenever its recursive answer does, and with it every production
operation and the production supply formation, whatever spread code it runs. `NavExt` is `MemoExt`
with `NavKept`; the deletion is NOT a navigation extension (`NavExt.not_withoutAliasCells`).

`NavSettled` is `NavStable` over `NavExt`: it quantifies over FEWER later states (only those that
keep the alias records and the counter), so every `NavStable` receiver is `NavSettled`, and it is
all `member_bridge_settled` needs — the two computations between the probe and the origin read
(`resolveAliasTarget`, the supply formation) are navigation extensions. -/

open KatLang.EvaluatorCacheLaws (StateRel WriteFrame evalStep_preserves evalAttempt_cases)

/-- **Recorded alias binding cells survive, and the runtime-declaration counter never goes back.** -/
def NavKept (s t : EvalState) : Prop :=
  (∀ (key : String) (a : Nat), lookupAssoc key s.aliasCells = some a → lookupAssoc key t.aliasCells = some a) ∧
  s.nextRuntimeDeclaration ≤ t.nextRuntimeDeclaration

theorem NavKept.refl (s : EvalState) : NavKept s s := ⟨fun _ _ h => h, Nat.le_refl _⟩

theorem NavKept.trans {s t u : EvalState} (h₁ : NavKept s t) (h₂ : NavKept t u) : NavKept s u :=
  ⟨fun key a h => h₂.1 key a (h₁.1 key a h), Nat.le_trans h₁.2 h₂.2⟩

theorem NavKept.of_fields {s t : EvalState} (ha : t.aliasCells = s.aliasCells)
    (hn : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) : NavKept s t :=
  ⟨fun key a h => by rw [ha]; exact h, by rw [hn]; exact Nat.le_refl _⟩

instance : StateRel NavKept := ⟨NavKept.refl, NavKept.trans⟩

instance : WriteFrame NavKept :=
  ⟨fun _ _ _ _ _ ha hn => NavKept.of_fields ha hn,
   fun _ _ => NavKept.of_fields rfl rfl,
   fun s t key address h hfresh =>
     ⟨fun k a hk => by
        have hne : ¬ k = key := fun e => by rw [e, hfresh] at hk; cases hk
        show (if k = key then some address else lookupAssoc k t.aliasCells) = some a
        rw [ite_eq_right hne]
        exact h.1 k a hk,
      h.2⟩,
   fun _ => ⟨fun _ _ h => h, Nat.le_succ _⟩⟩

/-- The property access writes only the cache and the owner set: its own writes keep the alias
    table and the counter, its calculation is covered by the recursive answer. -/
theorem navKept_property_step (rec : EvalRec) (hrec : ∀ c, Preserves NavKept (rec c))
    (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Preserves NavKept
      (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc := KatLang.EvaluatorCacheLaws.EvalBody.zeroArgPropertyCalculation_pres (R := NavKept) rec hrec request
    resolvedAlgorithm ctx env
  intro s
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · simp only [EvalM.bind_runState, KatLang.EvaluatorCacheLaws.get_runState]
    split
    · cases request with
      | read => exact NavKept.refl s
      | invoke _ => exact hcalc s
    · split
      · exact hcalc s
      · simp only [EvalM.bind_runState, KatLang.EvaluatorCacheLaws.set_runState]
        obtain ⟨o, t2, hm, hc⟩ := evalAttempt_cases (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)
          { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        have hk := hcalc { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        rw [hm] at hk
        have hstart : NavKept s
            { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties } :=
          NavKept.of_fields rfl rfl
        have hk' := hstart.trans hk
        rcases hc with ⟨hrun, _⟩ | ⟨hrun, _⟩
        · rw [hrun]; exact hk'
        · rw [hrun]
          simp only [KatLang.EvaluatorCacheLaws.get_runState]
          cases o with
          | ok counted =>
            simp only [EvalM.bind_runState, KatLang.EvaluatorCacheLaws.set_runState, KatLang.EvaluatorCacheLaws.pure_runState]
            exact hk'.trans (NavKept.of_fields rfl rfl)
          | error err =>
            simp only [EvalM.bind_runState, KatLang.EvaluatorCacheLaws.set_runState, KatLang.EvaluatorCacheLaws.throw_runState]
            exact hk'.trans (NavKept.of_fields rfl rfl)
  · exact hcalc s

/-- **WHOLE RUN (production).** Every production operation, from every state, whatever its outcome,
    keeps every recorded alias binding cell and never moves the runtime-declaration counter back. -/
theorem production_navKept (c : EvalCall) : Preserves NavKept (evalUnbounded c) :=
  production_preserves NavKept NavKept.refl
    (fun rec hrec => evalStep_preserves navKept_property_step rec hrec) c

/-- **WHOLE RUN (core).** Every COMPLETED run of the total core, at every fuel. -/
theorem navKept_core (n : Nat) (c : EvalCall) (s : EvalState) (hc : Completes (evalFuel n c) s) :
    NavKept s ((evalFuel n c).runState s).2 :=
  invariant_transfer NavKept NavKept.refl
    (fun rec hrec => evalStep_preserves navKept_property_step rec hrec) n c s hc

/-- Production supply formation keeps the alias records and the counter, whatever spread code it runs. -/
theorem form_navKept (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) (s : EvalState) :
    NavKept s ((NeedSupply.form evalSupplySpread ctx env args).runState s).2 :=
  KatLang.EvaluatorCacheLaws.pres_form (R := NavKept) evalSupplySpread
    (fun e c v => production_navKept (.evalSupplySpread e c v)) ctx env args s

/-- **THE NAVIGATION EXTENSION.** The memo extension, with every recorded alias binding cell kept
    and the runtime-declaration counter not moved back. -/
structure NavExt (s t : EvalState) : Prop where
  memo : MemoExt s t
  kept : NavKept s t

theorem NavExt.refl (s : EvalState) : NavExt s s := ⟨MemoExt.refl s, NavKept.refl s⟩

theorem NavExt.trans {s t u : EvalState} (h₁ : NavExt s t) (h₂ : NavExt t u) : NavExt s u :=
  ⟨h₁.memo.trans h₂.memo, h₁.kept.trans h₂.kept⟩

/-- A recorded alias binding cell is read back from every navigation extension. -/
theorem NavExt.aliasCell {s t : EvalState} (h : NavExt s t) {key : String} {a : Nat}
    (hk : lookupAssoc key s.aliasCells = some a) : lookupAssoc key t.aliasCells = some a :=
  h.kept.1 key a hk

/-- The runtime-declaration counter of a navigation extension is at least the earlier one: an
    identity minted before is never minted again. -/
theorem NavExt.runtime_mono {s t : EvalState} (h : NavExt s t) :
    s.nextRuntimeDeclaration ≤ t.nextRuntimeDeclaration := h.kept.2

/-- **The deletion `MemoExt` allowed is NOT a navigation extension**: a state with a recorded alias
    binding cell is not extended by the state without its alias table. -/
theorem NavExt.not_withoutAliasCells {s : EvalState} {key : String} {a : Nat}
    (h : lookupAssoc key s.aliasCells = some a) : ¬ NavExt s { s with aliasCells := [] } := by
  intro e
  have := e.aliasCell h
  cases this

/-- **Every production operation is a navigation extension** — from every state, whatever its
    outcome. -/
theorem production_navExt (c : EvalCall) (s : EvalState) : NavExt s ((evalUnbounded c).runState s).2 :=
  ⟨production_memoExt c s, production_navKept c s⟩

/-- **Production supply formation is a navigation extension**, whatever spread code it runs. -/
theorem form_navExt (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) (s : EvalState) :
    NavExt s ((NeedSupply.form evalSupplySpread ctx env args).runState s).2 :=
  ⟨form_memoExt ctx env args s, form_navKept ctx env args s⟩

/-- **Settled receiver navigation.** From every NAVIGATION extension of `t`, the receiver's
    structure as the plan's callee law reads it is `owner`, and reading it changes nothing. -/
def NavSettled (target : Expr) (ctx : EvalCtx) (owner : Algorithm) (t : EvalState) : Prop :=
  ∀ u, NavExt t u → (projectedStructure target ctx).runState u = (.ok (some owner), u)

/-- A receiver stable over every memo extension is settled over every navigation extension. -/
theorem NavStable.navSettled {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavStable target ctx owner t) : NavSettled target ctx owner t :=
  fun u hu => h u hu.memo

theorem NavSettled.mono {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t u : EvalState}
    (h : NavSettled target ctx owner t) (he : NavExt t u) : NavSettled target ctx owner u :=
  fun v hv => h v (he.trans hv)

theorem NavSettled.settled {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavSettled target ctx owner t) : (projectedStructure target ctx).runState t = (.ok (some owner), t) :=
  h t (NavExt.refl t)

/-- **Settledness is a whole-run invariant**: every production operation preserves it. -/
theorem navSettled_production {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavSettled target ctx owner t) (c : EvalCall) :
    NavSettled target ctx owner ((evalUnbounded c).runState t).2 :=
  h.mono (production_navExt c t)

/-- Supply formation preserves settledness, whatever spread code it runs. -/
theorem navSettled_form {target : Expr} {ctx : EvalCtx} {owner : Algorithm} {t : EvalState}
    (h : NavSettled target ctx owner t) (c : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    NavSettled target ctx owner ((NeedSupply.form evalSupplySpread c env args).runState t).2 :=
  h.mono (form_navExt c env args t)

/-- **THE MEMBER BRIDGE over a settled receiver, for EVERY bundle.** As `member_bridge_stable`, with
    the weaker premise `NavSettled` at the probe's exit: the navigation need only be settled over
    the later states that keep the recorded alias cells and the runtime-declaration counter — which
    the member's alias resolution and the supply formation do. -/
theorem member_bridge_navSettled (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hsettled : NavSettled target ctx owner s')
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_settled a target N fallback args ctx env s s' alg? owner p hprobe hsel hproj
    (fun g t cells u hr hf => by
      have h1 : NavExt s' t := by
        have := production_navExt (.resolveAliasTarget (childOfInContext owner p.alg ctx) ctx) s'
        have hrun : (evalUnbounded (.resolveAliasTarget (childOfInContext owner p.alg ctx) ctx)).runState s' =
            (.ok g, t) := hr
        rw [hrun] at this
        exact this
      have h2 : NavExt t u := by
        have := form_navExt ctx env args t
        rw [hf] at this
        exact this
      exact hsettled u (h1.trans h2)) hprod

end KatLang.MemberStability
