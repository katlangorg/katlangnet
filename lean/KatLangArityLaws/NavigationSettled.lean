import KatLangArityLaws.NavigationReread

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.NavigationReread KatLang.EvaluatorCacheLaws
open KatLang.WhileRoundProduction (production_eq_of_finite finite_call production_of_answer_free)

/-!
# Settled receiver navigation FROM THE PROBE, every receiver class (ledger E-18, step 1, M1)

`NavigationReread.navigation_reread` re-reads a completed identity navigation from every navigation
extension of its exit state. This module turns it into the premise of the member bridge:

* `probe_member` — THE MEMBER-PATH PROBE DECOMPOSED. From the path's own successful, non-minting
  production probe `resolveDotReceiver? (o.n) ctx`: the receiver's probe and its exit state, the
  DECLARED member `n` of the receiver's structure, its accessibility from the site, the member's own
  structure chase from that exit state, and the state relations (each step a navigation extension,
  none minting). The alternative — a dot RESULT carrier — is excluded by the no-mint premise, not
  assumed away: every such branch runs `identifyRuntimeAlgorithm` (`resolveAlg_dot_mints`).
  `navRuns_probe_member` is the same over the navigation core.
* `structSettled_of_navRuns` — a completed, non-minting structure chase is a settled structure.
* `navSettled_of_navRuns` — **SETTLED NAVIGATION FROM THE PROBE**, by induction on the receiver
  path: a name (declared, inherited, opened; selecting a plain declaration, a transparent reference
  with any row and any chain length, or a RUNTIME-TARGET alias), an inline block, a parameter, and
  any argumentless member path over them. The only premises are the probe's navigation run, the
  no-mint fact, and — for a parameter head — structure-normality of the CALLABLE that parameter's
  cell projected (see `StoredCallableNormal`, which derives it from the cell's own suspension).
* `member_bridge_of_probe` — THE MEMBER BRIDGE for EVERY bundle with the probe as its navigation
  premise: no `NavSettled`, `StructSettled`, activation or alias-key premise.

`NavRuns` is the probe's own run over recorded data (`NavigationReread`, § The navigation core): an
instance establishes it by evaluation; it is implied by the production probe wherever the
evaluator's reachable states make no dangling read (not proved as a whole-run invariant).
-/

namespace KatLang.NavigationSettled

/-! ## Reading a navigation-core run through its body -/

/-- A completed navigation-core run of a call that is no projection is one step of the body over
    the navigation core at the fuel below, from a state where the call is admitted. -/
theorem navFuel_body {c : EvalCall} {s : EvalState} {r : Except Error c.Ret × EvalState} {n : Nat}
    (h : (navFuel n c).runState s = r) (hne : r.1 ≠ .error .fuelExhausted) (hproj : isProjection c = false) :
    ∃ k, n = k + 1 ∧ navAdmits c s = true ∧ (evalStep (navFuel k) c).runState s = r := by
  cases n with
  | zero => subst h; exact absurd rfl hne
  | succ k =>
    refine ⟨k, rfl, ?_⟩
    rw [navFuel_succ_run] at h
    by_cases hadm : navAdmits c s = true
    · refine ⟨hadm, ?_⟩
      rw [ite_eq_left hadm] at h
      simp only [hproj, Bool.false_eq_true, ite_false] at h
      by_cases hraw : ((evalStep (navFuel k) c).runState s).1 = .error .fuelExhausted
      · rw [normalize_of_incomplete _ s hraw] at h
        subst h; exact absurd rfl hne
      · rw [normalize_of_complete _ s hraw] at h
        exact h
    · rw [ite_eq_right hadm] at h
      subst h; exact absurd rfl hne

/-- Every completed answer of the navigation core is a navigation extension. -/
theorem navFuel_navExt (n : Nat) (c : EvalCall) (s : EvalState)
    (h : ((navFuel n c).runState s).1 ≠ .error .fuelExhausted) : NavExt s ((navFuel n c).runState s).2 :=
  (navFuel_rr n c s h).1

/-! ## The dot-result carrier mints -/

/-- `resolveAlg` on a dot expression is the carrier of a dot RESULT: it mints a runtime identity. -/
theorem body_resolveAlg_dot (rec : EvalRec) (o : Expr) (n : Ident) (fb : Expr) (args : Option OutputBundle)
    (ctx : EvalCtx) (s : EvalState) :
    ((EvalBody.resolveAlg rec (.dotMember o n fb args) ctx).runState s).2.nextRuntimeDeclaration =
      s.nextRuntimeDeclaration + 1 := rfl

/-- Over production: a completed `resolveAlg` of a dot expression advanced the counter. -/
theorem resolveAlg_dot_mints (o : Expr) (n : Ident) (fb : Expr) (args : Option OutputBundle) (ctx : EvalCtx)
    (s : EvalState) (hc : ProductionCompletes (resolveAlg (.dotMember o n fb args) ctx) s) :
    ((resolveAlg (.dotMember o n fb args) ctx).runState s).2.nextRuntimeDeclaration =
      s.nextRuntimeDeclaration + 1 := by
  have hu := production_unfolds (.resolveAlg (.dotMember o n fb args) ctx) s hc
  have : (resolveAlg (.dotMember o n fb args) ctx).runState s =
      (EvalBody.resolveAlg evalUnbounded (.dotMember o n fb args) ctx).runState s := hu.symm
  rw [this]
  exact body_resolveAlg_dot evalUnbounded o n fb args ctx s

/-! ## The member-path probe, decomposed -/

/-- **The body of the receiver probe over a member path**, for any evaluator answer: a successful
    probe either navigated a DECLARED, accessible member whose structure chase gave the answer, or
    took a dot-result branch — `resolveAlg` of the edge, run from the probe's exit state or from
    the exit state of a member structure chase that found no structure. -/
theorem body_probe_member (rec : EvalRec) (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (s t : EvalState)
    (member : Algorithm)
    (h : (EvalBody.resolveDotReceiver? rec (.dotMember o n fb none) ctx).runState s = (.ok (some member), t)) :
    (∃ a p t₁, (rec (.resolveDotReceiver? o ctx)).runState s = (.ok (some a), t₁) ∧
        Algorithm.lookupPropDefAny? a n = some p ∧ memberAccessible? ctx a p = true ∧
        (rec (.resolveAliasStructure (childOfInContext a p.alg ctx) ctx)).runState t₁ = (.ok (some member), t)) ∨
    (∃ r t₁ t₂, (rec (.resolveDotReceiver? o ctx)).runState s = (.ok r, t₁) ∧
        (t₂ = t₁ ∨ ∃ g, (rec (.resolveAliasStructure g ctx)).runState t₁ = (.ok none, t₂)) ∧
        (rec (.resolveAlg (.dotMember o n fb none) ctx)).runState t₂ = (.ok member, t)) := by
  have hmap : ∀ (v : EvalState),
      (some <$> EvalRec.resolveAlg rec (.dotMember o n fb none) ctx).runState v = (.ok (some member), t) →
      (rec (.resolveAlg (.dotMember o n fb none) ctx)).runState v = (.ok member, t) := by
    intro v hv
    rw [map_run] at hv
    rcases hr : (EvalRec.resolveAlg rec (.dotMember o n fb none) ctx).runState v with ⟨ro, tv⟩
    rw [hr] at hv
    cases ro with
    | error e => cases hv
    | ok g =>
      cases hv
      exact hr
  unfold EvalBody.resolveDotReceiver? at h
  simp only [bind_run] at h
  rcases hp : (EvalRec.resolveDotReceiver? rec o ctx).runState s with ⟨po, t₁⟩
  rw [hp] at h
  cases po with
  | error e => cases h
  | ok r =>
    cases r with
    | none => exact .inr ⟨none, t₁, t₁, hp, .inl rfl, hmap t₁ h⟩
    | some a =>
      dsimp only at h
      cases hl : Algorithm.lookupPropDefAny? a n with
      | none =>
        rw [hl] at h
        dsimp only at h
        split at h
        · cases h
        · exact .inr ⟨some a, t₁, t₁, hp, .inl rfl, hmap t₁ h⟩
      | some p =>
        rw [hl] at h
        dsimp only at h
        cases hacc : memberAccessible? ctx a p with
        | false =>
          simp only [hacc, Bool.not_false, ite_true] at h
          cases h
        | true =>
          simp only [hacc, Bool.not_true, Bool.false_eq_true, ite_false, bind_run] at h
          rcases hs : (EvalRec.resolveAliasStructure rec (childOfInContext a p.alg ctx) ctx).runState t₁ with ⟨so, t₂⟩
          rw [hs] at h
          cases so with
          | error e => cases h
          | ok g =>
            cases g with
            | none => exact .inr ⟨some a, t₁, t₂, hp, .inr ⟨_, hs⟩, hmap t₂ h⟩
            | some m =>
              have h' : ((Except.ok (some m) : Except Error (Option Algorithm)), t₂) = (.ok (some member), t) := h
              cases h'
              exact .inl ⟨a, p, t₁, hp, hl, hacc, hs⟩

/-- **`probe_member`: THE MEMBER-PATH PROBE DECOMPOSED (production).** From the path's own
    successful production probe that minted no runtime identity: the receiver's probe (its
    identity `a` and exit state `t₁`), the DECLARED member `n` of `a`, its accessibility from the
    site, and the member's structure chase from `t₁` giving the path's identity — with the state
    relations: each step is a navigation extension and mints nothing. The dot-result branches are
    refuted by the counter, not assumed absent. -/
theorem probe_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (s t : EvalState) (member : Algorithm)
    (hprobe : (resolveDotReceiver? (.dotMember o n fb none) ctx).runState s = (.ok (some member), t))
    (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) :
    ∃ a p t₁, (resolveDotReceiver? o ctx).runState s = (.ok (some a), t₁) ∧
      Algorithm.lookupPropDefAny? a n = some p ∧ memberAccessible? ctx a p = true ∧
      (resolveAliasStructure (childOfInContext a p.alg ctx) ctx).runState t₁ = (.ok (some member), t) ∧
      t₁.nextRuntimeDeclaration = s.nextRuntimeDeclaration ∧ NavExt s t₁ ∧ NavExt t₁ t := by
  have hc : ProductionCompletes (resolveDotReceiver? (.dotMember o n fb none) ctx) s := by
    unfold ProductionCompletes; rw [hprobe]; nofun
  have hbody : (EvalBody.resolveDotReceiver? evalUnbounded (.dotMember o n fb none) ctx).runState s =
      (.ok (some member), t) := (production_unfolds (.resolveDotReceiver? (.dotMember o n fb none) ctx) s hc).trans hprobe
  rcases body_probe_member evalUnbounded o n fb ctx s t member hbody with
    ⟨a, p, t₁, hp, hl, hacc, hs⟩ | ⟨r, t₁, t₂, hp, hmid, halg⟩
  · have e1 : NavExt s t₁ := by
      have := production_navExt (.resolveDotReceiver? o ctx) s; rw [hp] at this; exact this
    have e2 : NavExt t₁ t := by
      have := production_navExt (.resolveAliasStructure (childOfInContext a p.alg ctx) ctx) t₁
      rw [hs] at this; exact this
    have h1 := e1.runtime_mono
    have h2 := e2.runtime_mono
    exact ⟨a, p, t₁, hp, hl, hacc, hs, by omega, e1, e2⟩
  · exfalso
    have e1 : NavExt s t₁ := by
      have := production_navExt (.resolveDotReceiver? o ctx) s; rw [hp] at this; exact this
    have e2 : t₁.nextRuntimeDeclaration ≤ t₂.nextRuntimeDeclaration := by
      rcases hmid with rfl | ⟨g, hg⟩
      · exact Nat.le_refl _
      · have := production_navExt (.resolveAliasStructure g ctx) t₁; rw [hg] at this; exact this.runtime_mono
    have hm := resolveAlg_dot_mints o n fb none ctx t₂ (by
      unfold ProductionCompletes
      show ((evalUnbounded (.resolveAlg (.dotMember o n fb none) ctx)).runState t₂).1 ≠ _
      rw [halg]; nofun)
    have hm' : t.nextRuntimeDeclaration = t₂.nextRuntimeDeclaration + 1 := by
      have : (resolveAlg (.dotMember o n fb none) ctx).runState t₂ = (.ok member, t) := halg
      rw [this] at hm; exact hm
    have h1 := e1.runtime_mono
    omega

/-- **`probe_member` over the navigation core.** The same decomposition, every piece a navigation
    run. -/
theorem navRuns_probe_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (s t : EvalState) (member : Algorithm)
    (hnav : NavRuns (.resolveDotReceiver? (.dotMember o n fb none) ctx) s (.ok (some member), t))
    (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) :
    ∃ a p t₁, NavRuns (.resolveDotReceiver? o ctx) s (.ok (some a), t₁) ∧
      Algorithm.lookupPropDefAny? a n = some p ∧ memberAccessible? ctx a p = true ∧
      NavRuns (.resolveAliasStructure (childOfInContext a p.alg ctx) ctx) t₁ (.ok (some member), t) ∧
      t₁.nextRuntimeDeclaration = s.nextRuntimeDeclaration ∧ NavExt s t₁ ∧ NavExt t₁ t := by
  obtain ⟨m, hrun, hne⟩ := hnav
  obtain ⟨k, rfl, -, hbody⟩ := navFuel_body hrun hne rfl
  have hext : ∀ (c : EvalCall) (v : EvalState) (x : c.Ret) (w : EvalState),
      (navFuel k c).runState v = (.ok x, w) → NavExt v w := by
    intro c v x w hr
    have := navFuel_navExt k c v (by rw [hr]; nofun)
    rw [hr] at this; exact this
  rcases body_probe_member (navFuel k) o n fb ctx s t member hbody with
    ⟨a, p, t₁, hp, hl, hacc, hs⟩ | ⟨r, t₁, t₂, hp, hmid, halg⟩
  · have e1 := hext _ s _ t₁ hp
    have e2 := hext _ t₁ _ t hs
    have h1 := e1.runtime_mono
    have h2 := e2.runtime_mono
    exact ⟨a, p, t₁, ⟨k, hp, nofun⟩, hl, hacc, ⟨k, hs, nofun⟩, by omega, e1, e2⟩
  · exfalso
    have e1 := (hext _ s _ t₁ hp).runtime_mono
    have e2 : t₁.nextRuntimeDeclaration ≤ t₂.nextRuntimeDeclaration := by
      rcases hmid with rfl | ⟨g, hg⟩
      · exact Nat.le_refl _
      · exact (hext _ t₁ _ t₂ hg).runtime_mono
    obtain ⟨j, rfl, -, hb⟩ := navFuel_body halg (by nofun) rfl
    have hm := body_resolveAlg_dot (navFuel j) o n fb none ctx t₂
    have hb' : (EvalBody.resolveAlg (navFuel j) (.dotMember o n fb none) ctx).runState t₂ = (.ok member, t) := hb
    rw [hb'] at hm
    simp only at hm
    omega

/-! ## Settled structure and settled navigation, from the run -/

/-- **A completed, non-minting structure chase is a settled structure**: whatever the chase read —
    a static step, a member-path row, a chain, a runtime-target alias's route decision, binding cell
    and projection — it is re-read from every navigation extension. -/
theorem structSettled_of_navRuns (a : Algorithm) (ctx : EvalCtx) (s t : EvalState) (owner : Algorithm)
    (hnav : NavRuns (.resolveAliasStructure a ctx) s (.ok (some owner), t))
    (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) : StructSettled a ctx owner t :=
  fun u hu => ((navigation_reread _ s t _ hnav hmint).2 u hu).1

/-- The receiver shapes with a navigable identity: a name, an inline block, a parameter, and an
    argumentless member edge over one. -/
def receiverPath : Expr → Bool
  | .resolve _ => true
  | .algorithmExpr _ => true
  | .param _ => true
  | .dotMember receiver _ _ none => receiverPath receiver
  | _ => false

/-- **SETTLED NAVIGATION FROM THE PROBE.** For a receiver path — a name, an inline block, a
    parameter, or an argumentless member path over them: when the production probe's navigation
    run from `s` answers `owner` at `t` and minted no runtime identity, the receiver's navigation
    is SETTLED at `t`. Whatever the name selects — a plain declaration, a transparent reference
    with a name or member-path row, a reference chain of any length, a runtime-target alias — and
    without any alias-key fact. For a parameter head, the CALLABLE its cell projected must be
    structure-normal (`hnorm`; derived from the cell's suspension by `StoredCallableNormal`). -/
theorem navSettled_of_navRuns : ∀ (target : Expr) (ctx : EvalCtx) (s t : EvalState) (owner : Algorithm),
    receiverPath target = true →
    NavRuns (.resolveDotReceiver? target ctx) s (.ok (some owner), t) →
    t.nextRuntimeDeclaration = s.nextRuntimeDeclaration →
    (∀ x o v, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), v) →
      structureNormal o = true) →
    NavSettled target ctx owner t
  | .resolve n, ctx, s, t, owner, _, hnav, hmint, _ => by
    obtain ⟨m, hrun, hne⟩ := hnav
    obtain ⟨k, rfl, -, hbody⟩ := navFuel_body hrun hne rfl
    have hbody' : (EvalBody.resolveDotReceiver? (navFuel k) (.resolve n) ctx).runState s = (.ok (some owner), t) := hbody
    unfold EvalBody.resolveDotReceiver? at hbody'
    cases hcs : ctx.callStack with
    | nil => rw [hcs] at hbody'; cases hbody'
    | cons top rest =>
      rw [hcs] at hbody'
      dsimp only at hbody'
      rw [bind_run] at hbody'
      obtain ⟨lo, hlo⟩ := sf_lookupLexicalPropertyRaw top n ctx
      rw [hlo s] at hbody'
      cases lo with
      | error e => cases hbody'
      | ok r =>
        exact navSettled_of (headSettled_name n ctx top rest r hcs hlo t)
          (structSettled_of_navRuns r.alg ctx s t owner ⟨k, hbody', nofun⟩ hmint)
  | .algorithmExpr block, ctx, s, t, owner, _, hnav, hmint, _ => by
    obtain ⟨m, hrun, hne⟩ := hnav
    obtain ⟨k, rfl, -, hbody⟩ := navFuel_body hrun hne rfl
    have hbody' : (navFuel k (.resolveAliasStructure (wireToCaller ctx block) ctx)).runState s =
        (.ok (some owner), t) := hbody
    exact navSettled_of (headSettled_block block ctx t)
      (structSettled_of_navRuns _ ctx s t owner ⟨k, hbody', nofun⟩ hmint)
  | .param x, ctx, s, t, owner, _, hnav, hmint, hnorm => by
    have hprod := hnav.production
    obtain ⟨m, hrun, hne⟩ := hnav
    obtain ⟨k, rfl, -, hbody⟩ := navFuel_body hrun hne rfl
    have hcall : NavRuns (.projectParameterCallable x ctx) s (.ok (some owner), t) := ⟨k, hbody, nofun⟩
    have hnormal : structureNormal owner = true := hnorm x owner t rfl hcall.production
    have hre := (navigation_reread _ s t _ hcall hmint).2
    refine navSettled_of (selected := owner) (fun u hu => ?_) (structSettled_normal owner ctx t hnormal)
    have hcu : (projectParameterCallable x ctx).runState u = (.ok (some owner), u) := (hre u hu).1
    have hcb : ProductionCompletes ((fun rec : EvalRec => rec (.projectParameterCallable x ctx)) evalUnbounded) u := by
      unfold ProductionCompletes
      show ((projectParameterCallable x ctx).runState u).1 ≠ _
      rw [hcu]; nofun
    exact (production_eq_of_finite (.projectNeedStructuralMember (.param x) ctx)
      (fun rec => rec (.projectParameterCallable x ctx)) (fun _ => rfl) (finite_call _) u hcb).trans hcu
  | .dotMember o n fb none, ctx, s, t, owner, hshape, hnav, hmint, hnorm => by
    obtain ⟨a, p, t₁, hp, hl, hacc, hs, hc1, _, e2⟩ := navRuns_probe_member o n fb ctx s t owner hnav hmint
    have ih := navSettled_of_navRuns o ctx s t₁ a hshape hp hc1 (fun x o' v hx => hnorm x o' v hx)
    exact navSettled_member o n fb ctx a p owner t (ih.mono e2) hl hacc
      (structSettled_of_navRuns _ ctx t₁ t owner hs (by omega))
  | .dotMember _ _ _ (some _), _, _, _, _, h, _, _, _ => by cases h
  | .num _, _, _, _, _, h, _, _, _ => by cases h
  | .emptySequence _, _, _, _, _, h, _, _, _ => by cases h
  | .listLiteral _, _, _, _, _, h, _, _, _ => by cases h
  | .unary _ _, _, _, _, _, h, _, _, _ => by cases h
  | .binary _ _ _, _, _, _, _, h, _, _, _ => by cases h
  | .comparison _ _, _, _, _, _, h, _, _, _ => by cases h
  | .index _ _, _, _, _, _, h, _, _, _ => by cases h
  | .call _ _, _, _, _, _, h, _, _, _ => by cases h
  | .stringLiteral _, _, _, _, _, h, _, _, _ => by cases h
  | .boolLiteral _, _, _, _, _, h, _, _, _ => by cases h
  | .sequenceConstruct _ _, _, _, _, _, h, _, _, _ => by cases h
  | .sequenceSpread _, _, _, _, _, h, _, _, _ => by cases h
  | .capture _, _, _, _, _, h, _, _, _ => by cases h

/-! ## The member bridge with the probe as its navigation premise -/

/-- **THE MEMBER BRIDGE, EVERY BUNDLE, EVERY NON-MINTING RECEIVER CLASS, FROM THE PROBE.** For a
    receiver path `target`: after the production probe — its navigation run from `s` answering
    `owner` at `s'` without minting — and production's own dot decision selecting the DECLARED
    member `p`, the member-route ordinary call IS the re-counted production dot evaluation
    `target.N(args)`, both run from the SAME state `s`: outcome, error context, final state and the
    CACHE-PUB-1 publication an empty supply makes — for the empty bundle, a spread-first bundle
    (whatever the spread runs, a failing spread included) and every other written list.

    Covered by this ONE statement: a declared, inherited or opened name; a transparent reference
    with a name row, a member-path row or a chain of any length; a RUNTIME-TARGET alias; an inline
    block; a parameter; nested and parameter-rooted member paths. No settledness, alias-key or
    activation premise. `hnorm` concerns a parameter head only. The minting class is outside
    (`hmint`; `MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`). -/
theorem member_bridge_of_probe (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hshape : receiverPath target = true)
    (hnav : NavRuns (.resolveDotReceiver? target ctx) s (.ok (some owner), s'))
    (hmint : s'.nextRuntimeDeclaration = s.nextRuntimeDeclaration)
    (hsel : selectDotEdge ctx target N (some owner) = .ok (.member owner p))
    (hnorm : ∀ x o v, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), v) →
      structureNormal o = true)
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s :=
  member_bridge_of_settled a target N fallback args ctx env s s' (some owner) owner p hnav.production hsel hnorm
    (navSettled_of_navRuns target ctx s s' owner hshape hnav hmint hnorm) hprod

end KatLang.NavigationSettled
