import KatLangArityLaws.EvaluatorPublications
import KatLangArityLaws.StoredCallableNormal

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.NavigationReread KatLang.NavigationSettled KatLang.StoredCallableNormal
open KatLang.Publications
open KatLang.MemoLinks (LinkHeapKept LinkKept)

/-!
# Published CALLABLE identities are structure-normal on every reached state (ledger E-18, step 1, M1)

`StoredCallableNormal` derived structure-normality of a published CALLABLE for a cell supplied with
a written name, block or dot expression, and left two classes open: a cell whose argument is itself
a PARAMETER (`F(b)` inside `G(b)`) and an intrinsic `.Algorithm` LINK — their published CALLABLE is
ANOTHER cell's outcome, so the claim is about the run's earlier publications. This module closes
both, as a WHOLE-RUN theorem of the production evaluator:

* `EvaluatorPublications.PubHeapKept h h'` — every identity published in `h'` is structure-normal or
  was already a published identity of `h` — is the relation. It needs no premise on the entry heap.
* `CallRes` is the RESULT contract of the eight calls an identity flows through: a structure chase
  and the structure of anything return structure-normal identities (`ChaseNormal`, `OptNormal`,
  from `StoredCallableNormal`, unconditionally); a CALLABLE projection, a parameter's projection, a
  link's CALLABLE, the written projection (at an address or not) and `resolveAlg` of a parameter
  return an identity ACCOUNTED FOR in their exit heap (`Publications.Accounted`: structure-normal,
  or a published identity of that heap).
* `evalStep_recRes` — every body keeps the result contract whenever its recursive answer does.
  With `Publications.evalStep_pubDisc` it is the per-body step of ONE fuel induction
  (`fuel_published`), transferred to production (`production_published`): for EVERY production
  operation, from EVERY state and whatever its outcome, the exit heap's published identities are
  accounted for in the entry heap, and a successful result satisfies its contract.

## Consequences on normal heaps

`Publications.NormalHeap h` — every completed CALLABLE identity of `h` is structure-normal — holds of
the empty heap and is preserved by every production operation (`production_normalHeap`), by the
production supply formation whatever spread code it runs (`form_normalHeap`), and by every finite
sequence of production operations (`runOps_normalHeap`): it is an invariant of every state a run
reaches, NOT of every state (`StoredCallableNormal.storedCallableNeedNotBeNormal` stays a
counterexample for a crafted heap). On a normal heap:

* `projection_normal` — EVERY identity a production CALLABLE projection returns is structure-normal:
  first projections and memo reads, written arguments, FORWARDED parameters at any depth (through
  captured-ancestor contexts too: the projection of the forwarded cell is the same call) and
  intrinsic `.Algorithm` links;
* `param_head_normal_reached` — the premise `hnorm` of `NavigationSettled.member_bridge_of_probe`
  for EVERY parameter head, with no condition on what the parameter's cell was supplied with;
* `member_bridge_of_probe_reached` — the member bridge with `hnorm` DISCHARGED: its premises are the
  probe's navigation run, the no-mint fact, production's selection and completion, and that the
  entry heap is normal.

NOT claimed: `NavRuns` from production (captured-activation validity as a whole-run invariant is
still unproved; see `NavigationReread`); anything about a navigation that mints; anything about C#.
-/

namespace KatLang.PublishedCallableNormal

/-! ## Structure-normality of the identities `resolveAlg` builds -/

theorem structureNormal_withDeclarationId (id : Option PropertyIdentity) (a : Algorithm) :
    structureNormal (a.withDeclarationId id) = structureNormal a := by
  cases a <;> rfl

theorem structureNormal_withParent (p : Option ScopeCtx) (a : Algorithm) :
    structureNormal (a.withParent p) = structureNormal a := by
  cases a with
  | builtin b => rfl
  | conditional q op bs id => rfl
  | mk q pp op pr out id =>
    cases id with
    | none => rfl
    | some i => cases i <;> rfl
  | «alias» q op pr target id r =>
    cases id with
    | none => rfl
    | some i => cases i <;> rfl

theorem structureNormal_wireToCaller (ctx : EvalCtx) (a : Algorithm) :
    structureNormal (wireToCaller ctx a) = structureNormal a := by
  unfold wireToCaller
  split
  · exact structureNormal_withParent _ a
  · rfl

/-- The identity `identifyRuntimeAlgorithm` mints for a structure-normal algorithm is structure-normal. -/
theorem identifyRuntime_normal (a : Algorithm) (ha : structureNormal a = true) (s t : EvalState)
    (g : Algorithm) (h : (identifyRuntimeAlgorithm a).runState s = (.ok g, t)) : structureNormal g = true := by
  have hrun : (identifyRuntimeAlgorithm a).runState s =
      (.ok (a.withDeclarationId (some (.runtime s.nextRuntimeDeclaration))),
        { s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 }) := rfl
  rw [hrun] at h
  cases h
  rw [structureNormal_withDeclarationId]
  exact ha

/-! ## The result contract -/

/-- **THE RESULT CONTRACT** of the calls an identity flows through; every other call has none. -/
def CallRes : (c : EvalCall) → c.Ret → Array NeedCell → Prop
  | .resolveAliasChase false _ _ _ _ _, e, _ => ChaseNormal e
  | .resolveAliasStructure _ _, o, _ => OptNormal o
  | .projectNeedCallable _, o, h => OptAccounted h o
  | .projectNeedWrittenAt _ _ _, o, h => OptAccounted h o
  | .linkCallable _, o, h => OptAccounted h o
  | .projectParameterCallable _ _, o, h => OptAccounted h o
  | .projectNeedWritten _ _, o, h => OptAccounted h o
  | .resolveAlg (.resolve _) _, _, _ => True
  | .resolveAlg (.algorithmExpr _) _, _, _ => True
  | .resolveAlg _ _, g, h => Accounted h g
  | _, _, _ => True

/-- An answer whose every successful result satisfies its contract in the heap it leaves. -/
def RecRes (rec : EvalRec) : Prop :=
  ∀ (c : EvalCall) (s : EvalState) (x : c.Ret) (t : EvalState), (rec c).runState s = (.ok x, t) → CallRes c x t.needs

theorem RecRes.chase {rec : EvalRec} (h : RecRes rec) (pr : Bool) (a : Algorithm) (ctx : EvalCtx)
    (vis : List String) (last : Option (Algorithm × PropDef)) :
    Post ChaseNormal (rec (.resolveAliasChase false pr a ctx vis last)) :=
  fun s e t hr => h (.resolveAliasChase false pr a ctx vis last) s e t hr

theorem RecRes.structure {rec : EvalRec} (h : RecRes rec) (a : Algorithm) (ctx : EvalCtx) :
    Post OptNormal (rec (.resolveAliasStructure a ctx)) :=
  fun s o t hr => h (.resolveAliasStructure a ctx) s o t hr

/-- The written-projection callback of the publishing writer satisfies ITS result contract. -/
theorem RecRes.resSusp {rec : EvalRec} (h : RecRes rec) : ResSusp rec := by
  intro a x s g t hr
  cases x with
  | ready v => cases hr
  | collector sl => cases hr
  | expression source caller values =>
    simp only [NeedProjection.suspended] at hr
    split at hr
    · cases hr
    · exact h (.projectNeedWrittenAt a source caller) s (some g) t hr g rfl

/-! ## The bodies keep the result contract -/

section Bodies
variable (rec : EvalRec) (hres : RecRes rec)
include hres

theorem body_structure_normal (a : Algorithm) (ctx : EvalCtx) :
    Post OptNormal (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure
  refine post_bind (hres.chase true a ctx [] none) (fun e he => ?_)
  split
  · rename_i target l
    exact post_pure (fun g hg => by cases hg; exact he target l rfl)
  · exact post_pure (fun g hg => by cases hg)
  · exact post_pure (fun g hg => by cases hg)

/-- The alias arm of `projectNeedWritten`, over any answer keeping the contract. -/
theorem post_throughAlias_rec (alias : Algorithm) (caller : EvalCtx) :
    Post OptNormal (do
      match ← evalAttempt (EvalRec.resolveAliasChase rec false false alias caller [] none) with
      | .ok (.runtime _) => EvalRec.resolveAliasStructure rec alias caller
      | _ =>
          match ← evalAttempt (EvalRec.resolveAliasStructure rec alias caller) with
          | .ok identity => pure identity
          | .error err => if isLiftableArgResolutionError err then pure none else throw err) := by
  refine post_bind_any (fun r => ?_)
  split
  · exact hres.structure alias caller
  · refine post_bind (post_attempt (hres.structure alias caller)) (fun r' hr' => ?_)
    split
    · rename_i identity
      exact post_pure (hr' identity rfl)
    · split
      · exact post_pure (fun g hg => by cases hg)
      · exact post_throw _

/-- A written NAME, inline BLOCK or DOT expression: structure-normal, over any such answer. -/
theorem body_projectNeedWritten_static (source : Expr) (caller : EvalCtx) (hsrc : staticSource source = true) :
    Post OptNormal (EvalBody.projectNeedWritten rec source caller) := by
  cases source with
  | dotMember target name fb args =>
    unfold EvalBody.projectNeedWritten
    refine post_bind_any (fun selected => ?_)
    split
    · exact hres.structure _ caller
    · exact post_pure (fun g hg => by cases hg)
  | resolve n =>
    unfold EvalBody.projectNeedWritten
    dsimp only
    split
    · refine post_bind_any (fun r => ?_)
      split
      · split
        · exact post_throughAlias_rec rec hres _ caller
        · rename_i other hne
          exact post_pure (fun g hg => by cases hg; exact not_alias_normal (fun p o pr t i r he => hne p o pr t i r he))
      · split
        · exact post_pure (fun g hg => by cases hg)
        · exact post_throw _
    · exact post_error _
  | algorithmExpr a =>
    unfold EvalBody.projectNeedWritten
    dsimp only
    split
    · exact post_throughAlias_rec rec hres _ caller
    · rename_i wired hne
      exact post_pure (fun g hg => by cases hg; exact not_alias_normal (fun p o pr t i r he => hne p o pr t i r he))
  | _ => cases hsrc

omit hres in
/-- What `projectNeedWritten`'s lifting of a resolution returns: no identity, or the resolution's
    own successful result, in the state the resolution left. -/
theorem lifted_run {m : EvalM Algorithm} {k : Except Error Algorithm → EvalM (Option Algorithm)}
    (hok : ∀ g, k (.ok g) = pure (some g))
    (herr : ∀ err, k (.error err) = if isLiftableArgResolutionError err then pure none else throw err)
    {s t : EvalState} {o : Option Algorithm} (h : (evalAttempt m >>= k).runState s = (.ok o, t)) :
    o = none ∨ ∃ g, o = some g ∧ m.runState s = (.ok g, t) := by
  rw [bind_run] at h
  rcases hr : m.runState s with ⟨r, t1⟩
  cases hinc : r.isIncomplete with
  | true =>
    have hr' := Except.isIncomplete_eq_true hinc
    subst hr'
    rw [evalAttempt_runState_of_incomplete m s t1 hr] at h
    cases h
  | false =>
    rw [evalAttempt_runState_of_complete m s t1 r hr hinc] at h
    cases r with
    | ok g =>
      dsimp only at h
      rw [hok g] at h
      cases h
      exact .inr ⟨g, rfl, rfl⟩
    | error err =>
      dsimp only at h
      rw [herr err] at h
      split at h
      · cases h
        exact .inl rfl
      · cases h

/-- **`projectNeedWritten` keeps the contract**: a name, block or dot expression is
    structure-normal; any other written source is `resolveAlg`'s own result, lifted. -/
theorem body_projectNeedWritten_res (source : Expr) (caller : EvalCtx) (s : EvalState) (o : Option Algorithm)
    (t : EvalState) (h : (EvalBody.projectNeedWritten rec source caller).runState s = (.ok o, t)) :
    OptAccounted t.needs o := by
  by_cases hsrc : staticSource source = true
  · exact fun g hg => .inl (body_projectNeedWritten_static rec hres source caller hsrc s o t h g hg)
  · have key : o = none ∨ ∃ g, o = some g ∧ (rec.resolveAlg source caller).runState s = (.ok g, t) := by
      cases source <;> first
        | (exact absurd rfl hsrc)
        | (unfold EvalBody.projectNeedWritten at h
           dsimp only at h
           exact lifted_run (fun _ => rfl) (fun _ => rfl) h)
    rcases key with rfl | ⟨g, rfl, hg⟩
    · exact OptAccounted.none
    · have hc := hres (.resolveAlg source caller) s g t hg
      refine OptAccounted.some ?_
      cases source <;> first
        | (exact absurd rfl hsrc)
        | exact hc

theorem body_projectNeedWrittenAt_res (a : Nat) (source : Expr) (caller : EvalCtx) (s : EvalState)
    (o : Option Algorithm) (t : EvalState)
    (h : (EvalBody.projectNeedWrittenAt rec a source caller).runState s = (.ok o, t)) :
    OptAccounted t.needs o := by
  unfold EvalBody.projectNeedWrittenAt at h
  split at h
  · rw [bind_run] at h
    rename_i receiver fb heq
    rcases hr : (rec.algorithmIntrinsicRoute receiver caller).runState s with ⟨r, t1⟩
    rw [hr] at h
    cases r with
    | error e => cases h
    | ok b =>
      dsimp only at h
      split at h
      · exact hres (.linkCallable a) t1 o t h
      · exact hres (.projectNeedWritten source caller) t1 o t h
  · exact hres (.projectNeedWritten source caller) s o t h

theorem body_linkCallable_res (a : Nat) (s : EvalState) (o : Option Algorithm) (t : EvalState)
    (h : (EvalBody.linkCallable rec a).runState s = (.ok o, t)) : OptAccounted t.needs o := by
  unfold EvalBody.linkCallable NeedLink.callable at h
  rw [bind_run] at h
  rcases hr : (NeedLink.decodeCallee rec.planRoute.classify rec.demandNeedRecursive a).runState s with ⟨r, t1⟩
  rw [hr] at h
  cases r with
  | error e => cases h
  | ok callee => exact hres (.projectNeedCallable callee) t1 o t h

omit hres in
/-- An identity accounted for before the publication at `a` is accounted for after it. -/
theorem accounted_setCallable {t : EvalState} {g : Algorithm} (a : Nat) (hg : Accounted t.needs g) :
    Accounted (KatLang.NeedControl.Projection.setCallable a (.projected (.ok (some g))) t).needs g := by
  rcases hg with hn | ⟨b, c, hc, hp⟩
  · exact .inl hn
  · refine .inr ⟨b, ?_⟩
    show ∃ c', (t.needs.modify a (fun c => { c with callable := .projected (.ok (some g)) }))[b]? = some c' ∧ _
    rw [modify_get]
    by_cases hab : a = b
    · subst hab
      exact ⟨{ c with callable := .projected (.ok (some g)) }, by simp [hc], rfl⟩
    · exact ⟨c, by simp [hab, hc], hp⟩

/-- **THE PUBLISHING WRITER keeps the contract**: an identity it returns is the cell's completed
    CALLABLE — found projected, or published by this run. -/
theorem body_projectNeedCallable_res (a : Nat) (s : EvalState) (o : Option Algorithm) (t : EvalState)
    (h : (EvalBody.projectNeedCallable rec a).runState s = (.ok o, t)) : OptAccounted t.needs o := by
  have hstep : (NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt a)) a).runState s =
      (.ok o, t) := h
  cases hc : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Projection.invalid_address _ a s hc] at hstep
    cases hstep
  | some cell =>
    cases hs : cell.callable with
    | projected outcome =>
      rw [KatLang.NeedControl.Projection.projected_sticky _ a s cell outcome hc hs] at hstep
      cases hstep
      exact fun g hg => by subst hg; exact Accounted.published hc hs
    | projecting =>
      rw [KatLang.NeedControl.Projection.projecting_reentry_cycle _ a s cell hc hs] at hstep
      cases hstep
    | unprojected =>
      rcases hr : (NeedProjection.suspended (rec.projectNeedWrittenAt a) cell.suspension).runState
          (KatLang.NeedControl.Projection.setCallable a .projecting s) with ⟨outcome, t₀⟩
      cases hinc : outcome.isIncomplete with
      | true =>
        have hoe := Except.isIncomplete_eq_true hinc
        subst hoe
        have hbad : (NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt a)) a).runState s =
            (.error .fuelExhausted, t₀) := by
          simp only [NeedProjection.step, bind_run, get_run, hc, hs, EvalM.modify_runState]
          simp only [KatLang.NeedControl.Projection.setCallable] at hr
          rw [evalAttempt_runState_of_incomplete _ _ _ hr]
        rw [hbad] at hstep
        cases hstep
      | false =>
        rw [KatLang.NeedControl.Projection.unprojected_publishes _ a s t₀ cell outcome hc hs hr hinc] at hstep
        have ho : outcome = .ok o := (Prod.mk.inj hstep).1
        have ht : KatLang.NeedControl.Projection.setCallable a (.projected outcome) t₀ = t := (Prod.mk.inj hstep).2
        subst ho
        intro g hg
        subst hg
        rw [← ht]
        exact accounted_setCallable a (hres.resSusp a cell.suspension _ g t₀ hr)

theorem body_projectParameterCallable_res (x : Ident) (ctx : EvalCtx) (s : EvalState) (o : Option Algorithm)
    (t : EvalState) (h : (EvalBody.projectParameterCallable rec x ctx).runState s = (.ok o, t)) :
    OptAccounted t.needs o := by
  have h' : (projectParameterWith rec.projectNeedCallable x ctx).runState s = (.ok o, t) := h
  rw [projectParameterWith_run] at h'
  split at h'
  · rename_i address _
    exact hres (.projectNeedCallable address) s o t h'
  · cases h'
    exact OptAccounted.none

/-- **`resolveAlg` keeps the contract**: a parameter is its cell's projection; a capture and a dot
    result are freshly minted plain algorithms. -/
theorem body_resolveAlg_res (e : Expr) (ctx : EvalCtx) (s : EvalState) (g : Algorithm) (t : EvalState)
    (h : (EvalBody.resolveAlg rec e ctx).runState s = (.ok g, t)) : CallRes (.resolveAlg e ctx) g t.needs := by
  cases e with
  | resolve n => exact trivial
  | algorithmExpr a => exact trivial
  | param x =>
    show Accounted t.needs g
    have h' : (rec.projectParameterCallable x ctx >>= fun r =>
        match r with
        | some algorithm => pure algorithm
        | none => EvalM.error (Error.notAnAlgorithm s!"param({x})")).runState s = (.ok g, t) := h
    rw [bind_run] at h'
    rcases hr : (rec.projectParameterCallable x ctx).runState s with ⟨r, t1⟩
    rw [hr] at h'
    cases r with
    | error err => cases h'
    | ok o =>
      cases o with
      | none => cases h'
      | some algorithm =>
        cases h'
        exact hres (.projectParameterCallable x ctx) s (some g) t hr g rfl
  | capture rows =>
    exact .inl (identifyRuntime_normal _ (by rw [structureNormal_wireToCaller]; rfl) s t g h)
  | dotMember o n fallback args =>
    exact .inl (identifyRuntime_normal _ (by rw [structureNormal_wireToCaller]; rfl) s t g h)
  | _ => cases h

/-- **THE PER-BODY STEP of the result contract.** -/
theorem evalStep_recRes : RecRes (evalStep rec) := by
  intro c s x t h
  cases c with
  | resolveAliasChase fc pr a ctx vis last =>
    cases fc with
    | true => exact trivial
    | false => exact body_chase_normal rec (hres.chase) pr a ctx vis last s x t h
  | resolveAliasStructure a ctx => exact body_structure_normal rec hres a ctx s x t h
  | projectNeedCallable a => exact body_projectNeedCallable_res rec hres a s x t h
  | projectNeedWrittenAt a source caller => exact body_projectNeedWrittenAt_res rec hres a source caller s x t h
  | linkCallable a => exact body_linkCallable_res rec hres a s x t h
  | projectParameterCallable y ctx => exact body_projectParameterCallable_res rec hres y ctx s x t h
  | projectNeedWritten source caller => exact body_projectNeedWritten_res rec hres source caller s x t h
  | resolveAlg e ctx => exact body_resolveAlg_res rec hres e ctx s x t h
  | _ => exact trivial

end Bodies

/-! ## Transfer: the fuel core and production -/

/-- **WHOLE RUN (core).** Every COMPLETED run of the total core, at every fuel and from every state:
    the identities published in its exit heap are accounted for in its entry heap, and a successful
    result satisfies its contract in the exit heap. -/
theorem fuel_published : ∀ (n : Nat) (c : EvalCall) (s : EvalState), Completes (evalFuel n c) s →
    PubHeapKept s.needs ((evalFuel n c).runState s).2.needs ∧
    ∀ x, ((evalFuel n c).runState s).1 = .ok x → CallRes c x ((evalFuel n c).runState s).2.needs := by
  intro n
  induction n with
  | zero => intro c s hc; exact absurd rfl hc
  | succ n ih =>
    intro c s hc
    have hpub : ∀ c, PubDisc (completedPart n c) := by
      intro c' s'
      by_cases hc' : Completes (evalFuel n c') s'
      · simp only [completedPart, ite_eq_left hc']; exact (ih c' s' hc').1
      · simp only [completedPart, ite_eq_right hc']; exact PubHeapKept.refl _
    have hres : RecRes (completedPart n) := by
      intro c' s' x t h
      by_cases hc' : Completes (evalFuel n c') s'
      · simp only [completedPart, ite_eq_left hc'] at h
        have := (ih c' s' hc').2 x (by rw [h])
        rw [h] at this
        exact this
      · simp only [completedPart, ite_eq_right hc'] at h
        cases h
    have hstep := evalStep_monotone _ _ (evalFuel_approx_completedPart n) c s
    have hne := (evalFuel_completes_iff (n + 1) c s).1 hc
    rw [evalFuel_succ] at hne ⊢
    by_cases hraw : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hraw] at hne; exact absurd rfl hne
    · rw [normalize_of_complete _ s hraw]
      rcases hstep with hi | he
      · exfalso; apply hraw; unfold EvalM.IsIncompleteAt at hi; rw [hi]
      · rw [he]
        refine ⟨evalStep_pubDisc (completedPart n) hpub hres.resSusp c s, fun x hx => ?_⟩
        exact evalStep_recRes (completedPart n) hres c s x _ (Prod.ext hx rfl)

/-- **WHOLE RUN (production).** For EVERY production operation, from EVERY state, whatever its
    outcome: every identity published in the exit heap is structure-normal or was already a
    published identity of the entry heap; and a successful result satisfies its contract. -/
theorem production_published (c : EvalCall) (s : EvalState) :
    PubHeapKept s.needs ((evalUnbounded c).runState s).2.needs ∧
    ∀ x, ((evalUnbounded c).runState s).1 = .ok x → CallRes c x ((evalUnbounded c).runState s).2.needs := by
  by_cases hc : ProductionCompletes (evalUnbounded c) s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    rw [← hr]
    exact fuel_published m c s hm
  · rw [production_incomplete_state c s hc]
    exact ⟨PubHeapKept.refl _, fun _ h => by cases h⟩

/-- Every production operation publishes only accounted identities. -/
theorem production_pubDisc (c : EvalCall) : PubDisc (evalUnbounded c) := fun s => (production_published c s).1

/-- The production answer keeps the result contract. -/
theorem production_recRes : RecRes evalUnbounded := by
  intro c s x t h
  have := (production_published c s).2 x (by rw [h])
  rw [h] at this
  exact this

/-- Production supply formation publishes only accounted identities, whatever spread code it runs. -/
theorem form_pubDisc (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    PubDisc (NeedSupply.form evalSupplySpread ctx env args) :=
  pubDisc_form evalSupplySpread (fun e c v => production_pubDisc (.evalSupplySpread e c v)) ctx env args

/-! ## Normal heaps are a whole-run invariant -/

/-- **WHOLE RUN.** Every production operation keeps a normal heap normal, whatever its outcome. -/
theorem production_normalHeap (c : EvalCall) (s : EvalState) (hn : NormalHeap s.needs) :
    NormalHeap ((evalUnbounded c).runState s).2.needs := (production_pubDisc c).normal s hn

theorem form_normalHeap (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) (s : EvalState)
    (hn : NormalHeap s.needs) : NormalHeap ((NeedSupply.form evalSupplySpread ctx env args).runState s).2.needs :=
  (form_pubDisc ctx env args).normal s hn

/-- Every finite sequence of production operations, each run from the state the previous one left. -/
theorem runOps_normalHeap : ∀ (ops : List EvalCall) (s : EvalState), NormalHeap s.needs →
    NormalHeap (KatLang.MemoLinks.runOps ops s).needs
  | [], _, hn => hn
  | c :: cs, s, hn => runOps_normalHeap cs _ (production_normalHeap c s hn)

/-- The empty state — where every run starts — has a normal heap. -/
theorem empty_normalHeap : NormalHeap EvalState.empty.needs := NormalHeap.empty

/-- A write that keeps every cell's CALLABLE field keeps the heap normal (the VALUE shell's marks,
    a plan's supply, route, callee and receiver records). -/
theorem normalHeap_modify {h : Array NeedCell} (hn : NormalHeap h) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, (f c).callable = c.callable) : NormalHeap (h.modify a f) :=
  (PubHeapKept.modify h a f (fun c _ => pubKept_of_callable _ _ (hf c))).normal hn

/-! ## What a production projection returns on a normal heap -/

/-- An identity a production CALLABLE projection returns is accounted for in its exit heap. -/
theorem projection_accounted (a : Nat) (s t : EvalState) (g : Algorithm)
    (h : (projectNeedCallable a).runState s = (.ok (some g), t)) : Accounted t.needs g :=
  production_recRes (.projectNeedCallable a) s (some g) t h g rfl

/-- **EVERY IDENTITY A PRODUCTION CALLABLE PROJECTION RETURNS ON A NORMAL HEAP IS STRUCTURE-NORMAL** —
    a first projection or a memo read; a cell supplied with a written name, block or dot expression,
    with a PARAMETER (forwarding another cell's CALLABLE, at any depth), or with an intrinsic
    `.Algorithm` LINK (the plan's callee cell's CALLABLE). -/
theorem projection_normal (a : Nat) (s t : EvalState) (g : Algorithm) (hn : NormalHeap s.needs)
    (h : (projectNeedCallable a).runState s = (.ok (some g), t)) : structureNormal g = true := by
  have hexit : NormalHeap t.needs := by
    have := production_normalHeap (.projectNeedCallable a) s hn
    have hrun : (evalUnbounded (.projectNeedCallable a)).runState s = (.ok (some g), t) := h
    rw [hrun] at this
    exact this
  exact hexit.accounted (projection_accounted a s t g h)

/-- The same for a parameter's projection. -/
theorem parameter_projection_normal (x : Ident) (ctx : EvalCtx) (s t : EvalState) (g : Algorithm)
    (hn : NormalHeap s.needs) (h : (projectParameterCallable x ctx).runState s = (.ok (some g), t)) :
    structureNormal g = true := by
  have hexit : NormalHeap t.needs := by
    have := production_normalHeap (.projectParameterCallable x ctx) s hn
    have hrun : (evalUnbounded (.projectParameterCallable x ctx)).runState s = (.ok (some g), t) := h
    rw [hrun] at this
    exact this
  exact hexit.accounted (production_recRes (.projectParameterCallable x ctx) s (some g) t h g rfl)

/-- A link's CALLABLE on a normal heap is structure-normal. -/
theorem link_callable_normal (a : Nat) (s t : EvalState) (g : Algorithm) (hn : NormalHeap s.needs)
    (h : (linkCallable a).runState s = (.ok (some g), t)) : structureNormal g = true := by
  have hexit : NormalHeap t.needs := by
    have := production_normalHeap (.linkCallable a) s hn
    have hrun : (evalUnbounded (.linkCallable a)).runState s = (.ok (some g), t) := h
    rw [hrun] at this
    exact this
  exact hexit.accounted (production_recRes (.linkCallable a) s (some g) t h g rfl)

/-- **THE PARAMETER-HEAD PREMISE ON EVERY REACHED STATE.** On a normal heap every identity a
    parameter's production projection returns is structure-normal — the premise `hnorm` of
    `NavigationSettled.member_bridge_of_probe`, for EVERY receiver and EVERY supplied argument:
    written, forwarded or a link. (`StoredCallableNormal.param_head_normal` needed the cell to
    await its first projection and to be supplied with a written name, block or dot expression.) -/
theorem param_head_normal_reached (ctx : EvalCtx) (s : EvalState) (hn : NormalHeap s.needs) :
    ∀ x o v, (projectParameterCallable x ctx).runState s = (.ok (some o), v) → structureNormal o = true :=
  fun x o v h => parameter_projection_normal x ctx s v o hn h

/-! ## The member bridge on a reached state -/

/-- **THE MEMBER BRIDGE, structure-normality DISCHARGED.** `NavigationSettled.member_bridge_of_probe`
    whose premise on the parameter head's CALLABLE is replaced by a fact of the ENTRY HEAP that
    every production run keeps: its published identities are structure-normal (`NormalHeap`, true of
    the empty state and preserved by every production operation, `production_normalHeap`). The
    remaining premises: the receiver path, the probe's navigation run and that it minted nothing,
    production's own dot decision, and that production completes. -/
theorem member_bridge_of_probe_reached (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hshape : receiverPath target = true)
    (hnav : NavRuns (.resolveDotReceiver? target ctx) s (.ok (some owner), s'))
    (hmint : s'.nextRuntimeDeclaration = s.nextRuntimeDeclaration)
    (hsel : selectDotEdge ctx target N (some owner) = .ok (.member owner p))
    (hheap : NormalHeap s.needs)
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_of_probe a target N fallback args ctx env s s' owner p hshape hnav hmint hsel
    (fun x o v _ h => param_head_normal_reached ctx s hheap x o v h) hprod

/-- Settled navigation from the probe on a reached state: `navSettled_of_navRuns` without `hnorm`. -/
theorem navSettled_of_navRuns_reached (target : Expr) (ctx : EvalCtx) (s t : EvalState) (owner : Algorithm)
    (hshape : receiverPath target = true)
    (hnav : NavRuns (.resolveDotReceiver? target ctx) s (.ok (some owner), t))
    (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) (hheap : NormalHeap s.needs) :
    NavSettled target ctx owner t :=
  navSettled_of_navRuns target ctx s t owner hshape hnav hmint
    (fun x o v _ h => param_head_normal_reached ctx s hheap x o v h)

/-! ## Negative controls: the invariant is of REACHED states, and the relation is not trivial -/

/-- The crafted heap of `StoredCallableNormal` (one cell holding a transparent reference as its
    completed CALLABLE) is not normal: `NormalHeap` is a property of the states a run reaches, not
    of every state. -/
theorem crafted_not_normal : ¬ NormalHeap craftedState.needs := by
  intro h
  have := h 0 _ referenceAlias rfl rfl
  cases this

/-- **`projection_normal` needs its premise.** From the crafted heap the production projection
    returns a transparent reference: the unconditional statement is false. -/
theorem unconditional_projection_normal_is_false :
    ¬ ∀ (a : Nat) (s t : EvalState) (g : Algorithm),
      (projectNeedCallable a).runState s = (.ok (some g), t) → structureNormal g = true := by
  intro h
  have := h 0 craftedState craftedState referenceAlias storedCallableNeedNotBeNormal.1
  rw [storedCallableNeedNotBeNormal.2] at this
  cases this

/-- **The publication relation is not vacuous**: it refuses a heap that holds a reference no cell
    of the earlier heap published. -/
theorem pubHeapKept_refuses_unaccounted : ¬ PubHeapKept EvalState.empty.needs craftedState.needs := by
  intro h
  rcases h 0 _ referenceAlias rfl rfl with hn | ⟨b, c, hc, _⟩
  · cases hn
  · simp [EvalState.empty] at hc

/-- … while the SAME reference, read back from the crafted heap, is accounted for by the cell that
    holds it: the relation needs no premise on the entry heap. -/
theorem crafted_projection_accounted :
    Accounted craftedState.needs referenceAlias ∧ structureNormal referenceAlias = false :=
  ⟨projection_accounted 0 craftedState craftedState referenceAlias storedCallableNeedNotBeNormal.1,
    storedCallableNeedNotBeNormal.2⟩

end KatLang.PublishedCallableNormal
