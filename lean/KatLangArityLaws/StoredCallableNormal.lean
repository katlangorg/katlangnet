import KatLangArityLaws.NavigationSettled

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.NavigationReread KatLang.NavigationSettled

/-!
# Structure-normality of stored CALLABLEs, from the production bodies (ledger E-18, step 1, M1)

The member bridge over a PARAMETER receiver reads the parameter's projected CALLABLE as the
receiver's structure, so that CALLABLE must be structure-normal (`PlanRouteBridge.structureNormal`:
no transparent reference). Earlier passes took that as a decidable premise on each instance. This
module derives it from what production actually stores:

* `chase_identity_normal`, `structure_result_normal` — **EVERY identity a structure chase returns is
  structure-normal**, at every fuel, from every state, whatever the chase read (the identity of a
  completed runtime projection included: it is chased again, and that chase ends at a normal
  algorithm). Proved by fuel induction over the production body `EvalBody.resolveAliasChase` with
  `followCarriers = false`; no heap invariant is used.
* `projectNeedWritten_normal` — the identity production reads for a written NAME, inline BLOCK or
  DOT expression is structure-normal: each arm of `EvalBody.projectNeedWritten` ends in a structure
  chase, or returns a selected declaration that is no alias.
* `first_projection_normal` — **the CALLABLE a production projection PUBLISHES for a cell supplied
  with a name, a block or a dot expression (no `.Algorithm` link) is structure-normal**: the
  projection shell runs `projectNeedWrittenAt` over the cell's own suspension.
* `param_head_normal` — the premise `hnorm` of `NavigationSettled.member_bridge_of_probe`, from
  facts of the reached heap: the parameter's cell is unprojected at the probe's entry and its
  suspension is such a written expression (`staticUnprojected`, a Bool an instance evaluates).

## What is NOT an invariant, and what remains

The UNCONDITIONAL statement "every stored CALLABLE of every state is structure-normal" is false of
arbitrary states: `storedCallableNeedNotBeNormal` is a two-line counterexample (a heap may hold any
algorithm as a completed projection; neither `AddressInvariant.Inv` nor a navigation extension
says otherwise). On states REACHED by production it follows from the three facts above for every
cell whose CALLABLE was first projected from a written name, block or dot expression. Two supplied
shapes forward ANOTHER cell's CALLABLE and are not closed here: a parameter argument (`F(b)` inside
`G(b)`: the projection is `projectParameterCallable`, the forwarded cell's own outcome) and an
`.Algorithm` link on the intrinsic route (`linkCallable`: the plan's callee cell's outcome). For
those, normality of the published CALLABLE is normality of the forwarded cell's — a statement about
an EARLIER publication, i.e. an induction over the run's publications, which needs a whole-run
result contract of the projection bodies (the shape of `AddressInvariant`'s `CallPost`, not a
`WriteFrame` relation). That whole-run invariant is not proved HERE; `param_head_normal` therefore
covers a parameter whose cell awaits its first projection and was supplied with a written name,
block or dot expression.

CLOSED since the independent review pass (same month), in `EvaluatorPublications` and
`PublishedCallableNormal`: every identity a production operation publishes is structure-normal or
was already published (`Publications.PubHeapKept`, `production_published`), so a heap whose
published identities are structure-normal stays so (`production_normalHeap`) and EVERY identity a
projection returns on it is structure-normal (`projection_normal`, `param_head_normal_reached`) —
link-bound cells, memo reads and parameter sources included.
-/

namespace KatLang.StoredCallableNormal

/-! ## Results of a computation -/

/-- Every successful result of `m` satisfies `Q`. -/
def Post {α : Type} (Q : α → Prop) (m : EvalM α) : Prop := ∀ s a t, m.runState s = (.ok a, t) → Q a

theorem post_bind {α β : Type} {P : α → Prop} {Q : β → Prop} {m : EvalM α} {f : α → EvalM β}
    (hm : Post P m) (hf : ∀ a, P a → Post Q (f a)) : Post Q (m >>= f) := by
  intro s b t h
  rw [bind_run] at h
  rcases hr : m.runState s with ⟨o, t1⟩
  rw [hr] at h
  cases o with
  | error e => cases h
  | ok a => exact hf a (hm s a t1 hr) t1 b t h

theorem post_any {α : Type} (m : EvalM α) : Post (fun _ => True) m := fun _ _ _ _ => trivial

theorem post_bind_any {α β : Type} {Q : β → Prop} {m : EvalM α} {f : α → EvalM β}
    (hf : ∀ a, Post Q (f a)) : Post Q (m >>= f) := post_bind (post_any m) (fun a _ => hf a)

theorem post_pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) : Post Q (pure a : EvalM α) := by
  intro s b t hr
  cases hr
  exact h

theorem post_error {α : Type} {Q : α → Prop} (e : Error) : Post Q (EvalM.error e : EvalM α) := by
  intro s b t hr; cases hr

theorem post_throw {α : Type} {Q : α → Prop} (e : Error) : Post Q (throw e : EvalM α) := by
  intro s b t hr; cases hr

/-- A caught outcome: a successful one is a successful result of the computation. -/
theorem post_attempt {α : Type} {Q : α → Prop} {m : EvalM α} (hm : Post Q m) :
    Post (fun r : Except Error α => ∀ a, r = .ok a → Q a) (evalAttempt m) := by
  intro s r t h a ha
  subst ha
  rw [evalAttempt_run] at h
  split at h
  · cases h
  · rcases hr : m.runState s with ⟨o, t1⟩
    rw [hr] at h
    cases h
    exact hm s a t1 hr

/-- A normalized run that succeeded is the raw run. -/
theorem normalize_ok {α : Type} {m : EvalM α} {s t : EvalState} {a : α}
    (h : m.normalizeIncomplete.runState s = (.ok a, t)) : m.runState s = (.ok a, t) := by
  by_cases hraw : (m.runState s).1 = .error .fuelExhausted
  · rw [normalize_of_incomplete m s hraw] at h; cases h
  · rw [normalize_of_complete m s hraw] at h; exact h

/-! ## Every identity of a structure chase is structure-normal -/

/-- The result contract of a structure chase: an identity it returns is structure-normal. -/
def ChaseNormal (e : AliasChaseEnd) : Prop := ∀ g l, e = .identity g l → structureNormal g = true

/-- The body step: the chase with `followCarriers = false` returns normal identities whenever its
    recursive chases do. -/
theorem body_chase_normal (rec : EvalRec)
    (hrec : ∀ pr a ctx vis last, Post ChaseNormal (rec (.resolveAliasChase false pr a ctx vis last)))
    (pr : Bool) (a : Algorithm) (ctx : EvalCtx) (vis : List String) (last : Option (Algorithm × PropDef)) :
    Post ChaseNormal (EvalBody.resolveAliasChase rec false pr a ctx vis last) := by
  cases a with
  | mk p pp op pr' out id => exact post_pure (fun g l h => by cases h; rfl)
  | builtin b => exact post_pure (fun g l h => by cases h; rfl)
  | conditional p op bs id => exact post_pure (fun g l h => by cases h; rfl)
  | «alias» parent opens props target id reference =>
    cases reference with
    | false => exact post_pure (fun g l h => by cases h; rfl)
    | true =>
      unfold EvalBody.resolveAliasChase
      simp only [Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      split
      · exact post_error _
      · refine post_bind_any (fun b => ?_)
        split
        · split
          · exact post_pure (fun g l h => by cases h)
          · refine post_bind_any (fun step => ?_)
            split
            · exact post_pure (fun g l h => by cases h)
            · exact hrec _ _ _ _ _
        · exact post_bind_any (fun next => hrec _ _ _ _ _)

/-- **EVERY IDENTITY A STRUCTURE CHASE RETURNS IS STRUCTURE-NORMAL**, at every fuel. -/
theorem chase_identity_normal_core (n : Nat) : ∀ (pr : Bool) (a : Algorithm) (ctx : EvalCtx) (vis : List String)
    (last : Option (Algorithm × PropDef)), Post ChaseNormal (evalFuel n (.resolveAliasChase false pr a ctx vis last)) := by
  induction n with
  | zero => intro pr a ctx vis last s e t h; cases h
  | succ n ih =>
    intro pr a ctx vis last s e t h
    rw [evalFuel_succ] at h
    exact body_chase_normal (evalFuel n) ih pr a ctx vis last s e t (normalize_ok h)

/-- Over production. -/
theorem chase_identity_normal (pr : Bool) (a : Algorithm) (ctx : EvalCtx) (vis : List String)
    (last : Option (Algorithm × PropDef)) : Post ChaseNormal (resolveAliasChase false pr a ctx vis last) := by
  intro s e t h
  have h' : (evalUnbounded (.resolveAliasChase false pr a ctx vis last)).runState s = (.ok e, t) := h
  obtain ⟨m, hm, -⟩ := (production_completes_iff (.resolveAliasChase false pr a ctx vis last) s (.ok e, t)).1
    ⟨h', by unfold ProductionCompletes; rw [h']; nofun⟩
  exact chase_identity_normal_core m pr a ctx vis last s e t hm

/-- The result contract of a structure: an algorithm is structure-normal. -/
def OptNormal (o : Option Algorithm) : Prop := ∀ g, o = some g → structureNormal g = true

/-- **THE STRUCTURE OF ANYTHING IS STRUCTURE-NORMAL**: every algorithm the production structure
    chase returns, from every state. -/
theorem structure_result_normal (a : Algorithm) (ctx : EvalCtx) : Post OptNormal (resolveAliasStructure a ctx) := by
  intro s o t h
  have hc : ProductionCompletes (resolveAliasStructure a ctx) s := by unfold ProductionCompletes; rw [h]; nofun
  have hbody : (EvalBody.resolveAliasStructure evalUnbounded a ctx).runState s = (.ok o, t) :=
    (production_unfolds (.resolveAliasStructure a ctx) s hc).trans h
  have hpost : Post OptNormal (EvalBody.resolveAliasStructure evalUnbounded a ctx) := by
    unfold EvalBody.resolveAliasStructure
    refine post_bind (chase_identity_normal true a ctx [] none) (fun e he => ?_)
    split
    · rename_i target l
      exact post_pure (fun g hg => by cases hg; exact he target l rfl)
    · exact post_pure (fun g hg => by cases hg)
    · exact post_pure (fun g hg => by cases hg)
  exact hpost s o t hbody

/-! ## What production reads for a written name, block or dot expression -/

/-- A written expression whose identity is read without forwarding another cell's CALLABLE. -/
def staticSource : Expr → Bool
  | .resolve _ => true
  | .algorithmExpr _ => true
  | .dotMember _ _ _ _ => true
  | _ => false

theorem not_alias_normal {g : Algorithm} (h : ∀ p o pr t i r, g ≠ .alias p o pr t i r) : structureNormal g = true := by
  cases g with
  | «alias» p o pr t i r => exact absurd rfl (h p o pr t i r)
  | mk p pp op pr' out id => rfl
  | builtin b => rfl
  | conditional p op bs id => rfl

/-- The alias arm of `projectNeedWritten`: a structure chase either way. -/
theorem post_throughAlias (alias : Algorithm) (caller : EvalCtx) :
    Post OptNormal (do
      match ← evalAttempt (EvalRec.resolveAliasChase evalUnbounded false false alias caller [] none) with
      | .ok (.runtime _) => EvalRec.resolveAliasStructure evalUnbounded alias caller
      | _ =>
          match ← evalAttempt (EvalRec.resolveAliasStructure evalUnbounded alias caller) with
          | .ok identity => pure identity
          | .error err => if isLiftableArgResolutionError err then pure none else throw err) := by
  refine post_bind_any (fun r => ?_)
  split
  · exact structure_result_normal alias caller
  · refine post_bind (post_attempt (structure_result_normal alias caller)) (fun r' hr' => ?_)
    split
    · rename_i identity
      exact post_pure (hr' identity rfl)
    · split
      · exact post_pure (fun g hg => by cases hg)
      · exact post_throw _

/-- **The identity production reads for a written NAME, inline BLOCK or DOT expression is
    structure-normal.** -/
theorem projectNeedWritten_normal (source : Expr) (caller : EvalCtx) (hsrc : staticSource source = true) :
    Post OptNormal (projectNeedWritten source caller) := by
  intro s o t h
  have hc : ProductionCompletes (projectNeedWritten source caller) s := by unfold ProductionCompletes; rw [h]; nofun
  have hbody : (EvalBody.projectNeedWritten evalUnbounded source caller).runState s = (.ok o, t) :=
    (production_unfolds (.projectNeedWritten source caller) s hc).trans h
  have hpost : Post OptNormal (EvalBody.projectNeedWritten evalUnbounded source caller) := by
    cases source with
    | dotMember target name fb args =>
      unfold EvalBody.projectNeedWritten
      refine post_bind_any (fun selected => ?_)
      split
      · exact structure_result_normal _ caller
      · exact post_pure (fun g hg => by cases hg)
    | resolve n =>
      unfold EvalBody.projectNeedWritten
      dsimp only
      split
      · refine post_bind_any (fun r => ?_)
        split
        · split
          · exact post_throughAlias _ caller
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
      · exact post_throughAlias _ caller
      · rename_i wired hne
        exact post_pure (fun g hg => by cases hg; exact not_alias_normal (fun p o pr t i r he => hne p o pr t i r he))
    | _ => cases hsrc
  exact hpost s o t hbody

/-! ## What a production projection publishes -/

/-- The cell at `a` awaits its FIRST projection and was supplied with a written name, inline block
    or dot expression that is no `.Algorithm` link. A fact of the heap, decided by evaluation. -/
def staticUnprojected (s : EvalState) (a : Nat) : Bool :=
  match s.needs[a]? with
  | some cell =>
      (match cell.callable with
       | .unprojected => true
       | _ => false) &&
      (match cell.suspension with
       | .expression source _ _ => staticSource source && (linkEdge? source).isNone
       | _ => false)
  | none => false

/-- **THE CALLABLE A PRODUCTION PROJECTION PUBLISHES for a cell supplied with a written name, block
    or dot expression is structure-normal.** The projection shell runs `projectNeedWrittenAt` over
    the cell's own suspension, which — the source being no link — is `projectNeedWritten`. -/
theorem first_projection_normal (a : Nat) (s t : EvalState) (o : Option Algorithm)
    (hstat : staticUnprojected s a = true) (h : (projectNeedCallable a).runState s = (.ok o, t)) :
    OptNormal o := by
  unfold staticUnprojected at hstat
  cases hcell : s.needs[a]? with
  | none => rw [hcell] at hstat; cases hstat
  | some cell =>
    rw [hcell] at hstat
    simp only [Bool.and_eq_true] at hstat
    obtain ⟨hun, hsus⟩ := hstat
    cases hcal : cell.callable with
    | projected outcome => rw [hcal] at hun; cases hun
    | projecting => rw [hcal] at hun; cases hun
    | unprojected =>
      cases hsusp : cell.suspension with
      | ready v => rw [hsusp] at hsus; cases hsus
      | collector sl => rw [hsusp] at hsus; cases hsus
      | expression source caller values =>
        rw [hsusp] at hsus
        simp only [Bool.and_eq_true] at hsus
        obtain ⟨hsrc, hlink⟩ := hsus
        have hc : ProductionCompletes (projectNeedCallable a) s := by unfold ProductionCompletes; rw [h]; nofun
        have hstep : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
            (.ok o, t) := (production_unfolds (.projectNeedCallable a) s hc).trans h
        rcases hrun : (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a) cell.suspension).runState
            (KatLang.NeedControl.Projection.setCallable a .projecting s) with ⟨outcome, t₀⟩
        cases hinc : outcome.isIncomplete with
        | true =>
          have hoe := Except.isIncomplete_eq_true hinc
          subst hoe
          have hbad : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
              (.error .fuelExhausted, t₀) := by
            simp only [NeedProjection.step, bind_run, get_run, hcell, hcal, EvalM.modify_runState]
            simp only [KatLang.NeedControl.Projection.setCallable] at hrun
            rw [evalAttempt_runState_of_incomplete _ _ _ hrun]
          rw [hbad] at hstep
          cases hstep
        | false =>
          rw [KatLang.NeedControl.Projection.unprojected_publishes _ a s t₀ cell outcome hcell hcal hrun hinc] at hstep
          have ho : outcome = .ok o := (Prod.mk.inj hstep).1
          subst ho
          rw [hsusp] at hrun
          simp only [NeedProjection.suspended] at hrun
          split at hrun
          · cases hrun
            intro g hg; cases hg
          · have hw : (evalUnbounded (.projectNeedWrittenAt a source caller)).runState
                (KatLang.NeedControl.Projection.setCallable a .projecting s) = (.ok o, t₀) := hrun
            have hcw : ProductionCompletes (evalUnbounded (.projectNeedWrittenAt a source caller))
                (KatLang.NeedControl.Projection.setCallable a .projecting s) := by
              unfold ProductionCompletes; rw [hw]; nofun
            have hb : (EvalBody.projectNeedWrittenAt evalUnbounded a source caller).runState
                (KatLang.NeedControl.Projection.setCallable a .projecting s) = (.ok o, t₀) :=
              (production_unfolds (.projectNeedWrittenAt a source caller) _ hcw).trans hw
            have hnone : linkEdge? source = none := by
              cases hl : linkEdge? source with
              | none => rfl
              | some pr => rw [hl] at hlink; cases hlink
            unfold EvalBody.projectNeedWrittenAt at hb
            rw [hnone] at hb
            exact projectNeedWritten_normal source caller hsrc _ o t₀ hb

/-- **THE PARAMETER-HEAD PREMISE, FROM THE HEAP.** When the parameter's supplied cell awaits its
    first projection and was supplied with a written name, block or dot expression, every identity
    the parameter's production projection returns is structure-normal — the premise `hnorm` of
    `NavigationSettled.member_bridge_of_probe`, derived instead of assumed. -/
theorem param_head_normal (x : Ident) (ctx : EvalCtx) (s : EvalState) (a : Nat)
    (haddr : parameterAddressIn s.lexicalActivations x ctx = some a) (hstat : staticUnprojected s a = true) :
    ∀ o v, (projectParameterCallable x ctx).runState s = (.ok (some o), v) → structureNormal o = true := by
  intro o v hrun
  have hc : ProductionCompletes (projectParameterCallable x ctx) s := by unfold ProductionCompletes; rw [hrun]; nofun
  have hbody : (projectParameterWith (EvalRec.projectNeedCallable evalUnbounded) x ctx).runState s = (.ok (some o), v) :=
    (production_unfolds (.projectParameterCallable x ctx) s hc).trans hrun
  rw [projectParameterWith_run, haddr] at hbody
  exact first_projection_normal a s v (some o) hstat hbody o rfl

/-! ## The unconditional statement is false -/

/-- A transparent reference (`X = Y`). -/
def referenceAlias : Algorithm := .alias none [] [] (.resolve "Y") none true

/-- A heap whose one cell holds that reference as a completed CALLABLE. -/
def craftedState : EvalState :=
  { needs := #[{ suspension := .ready (.atom 0, 1), callable := .projected (.ok (some referenceAlias)) }] }

/-- **NEGATIVE CONTROL: structure-normality of stored CALLABLEs is not a property of every state.**
    From a crafted heap the production projection returns a transparent reference, which is not
    structure-normal. Synthetic: it bounds the invariant (it is about REACHED states, and has to be
    proved from what production publishes), and shows no reachable language bug. -/
theorem storedCallableNeedNotBeNormal :
    (projectNeedCallable 0).runState craftedState = (.ok (some referenceAlias), craftedState) ∧
      structureNormal referenceAlias = false :=
  ⟨projectNeedCallable_memo 0 craftedState _ (some referenceAlias) rfl rfl, rfl⟩

end KatLang.StoredCallableNormal
