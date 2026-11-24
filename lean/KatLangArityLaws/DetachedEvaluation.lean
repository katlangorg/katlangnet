import KatLang

open KatLang

/-!
# EXPORTED-DETACHED: the evaluator enforces the exposure classification (November 2026)

`PropExposure` is an INPUT of this model: the front end classifies a property `exported` when its
value depends on no input an enclosing owner's call binds, and the evaluator used to TRUST that —
an exported entry is run-wide (`zeroArgPropertyCacheKey`), and an exported member is accessible
everywhere (`memberAccessible?`). A wrong flag therefore produced a value shared across calls, or a
read of whatever a dynamically live caller had bound under the same name. Since November 2026 the
evaluator ENFORCES the flag:

* **Exported means detached.** `EvalBody.evalZeroArgPropertyAccessCounted` runs every request of an
  exported binding over `EvalCtx.detach`: no inherited need cell, no inherited value, and a
  WATERMARK (`EvalCtx.detachedBefore`) under which every lexical activation recorded so far is
  detached. A detached activation stays an identity and supplies no input.
* **Captured reads are lexical-only.** `capturedParameter` decides how a parameter read finds its
  binding from the context's lexical chain alone. A name whose lexical owner has no usable
  activation is UNAVAILABLE: every executed operation on the written occurrence — its VALUE read,
  its CALLABLE projection, the lookup of its cell and its direct TRANSPORT as a supplied argument,
  callee, link receiver or alias row — is refused with `unknownName`, and none falls back to the
  context's inherited tiers.

So a wrong `exported` flag is a deterministic refusal on the paths these laws cover —
`unknownName` at the parameter operation, `localOnlyProperty` at a navigation or at a local-only
read — never a value read from a pre-existing input. A retained runtime-alias binding cell is reached
by the alias chase instead; its reuse is judged against the reader BEFORE its channel runs (ledger row
R-1, qualified, November 2026: `KatLangArityLaws/RetainedCellReuse.lean`), and inside a retained cell's
computation an input read that lands below a reader admitted to the cell, while a detached evaluation
that detaches the activation is served, is the same refusal (`activation_late_refused`,
`noteLocalOnlyRead_run`).

What is proved here, over the production definitions of `KatLang.lean`:

* § 1 **The watermark.** Nothing is detached by default (`nothing_detached_by_default`,
  `usableActivation_attached`: the former `Option.isSome` test). `EvalCtx.detach` detaches every
  activation recorded so far (`detach_detaches_recorded`), keeps every later one usable
  (`detach_keeps_later`), never lowers the watermark (`detach_never_lowers`), empties the need tier
  and changes nothing else (`detach_keeps_identity`); a pushed head and a bound callee inherit it
  (`push_inherits_watermark`, `bindParameters_inherits_watermark`).
* § 2 **Captured reads.** The classifier's three outcomes (`captured_own_of_head`,
  `captured_own_without_owner`, `captured_activation`, `captured_unavailable_static`,
  `captured_unavailable_detached`); the lookup of an unavailable parameter is the `unknownName`
  REFUSAL in the state it started from (`unavailable_lookup_refused`), and so is every executed
  operation on the written occurrence: its VALUE read (**`detached_param_read_refused`**, with the
  static-owner case `static_owner_read_refused`; `unavailable_context_refused`), its direct
  TRANSPORT as a supplied computation (`unavailable_transport_refused` — nothing is allocated,
  whether or not the receiver would demand it), its CALLABLE projection
  (`unavailable_projection_refused` — never the absence a usable valueless binding reports), the
  lookup of its cell (`unavailable_cell_lookup_refused`, `unavailable_cell_test_refused`), a
  spread of it (`unavailable_spread_refused`) and a parameter-row alias's binding cell
  (`unavailable_alias_row_refused`). The other two outcomes are untouched: an `own` name still
  reads the context's tiers (`own_reads_the_context`, `own_transport_uses_the_context`: the
  host/free-parameter lookup), and an available one transports its existing cell without
  allocating or demanding (`available_transport_is_lazy`).
  **`captured_read_is_lexical`**: whenever a level of the head's lexical chain binds the name, the
  outcome of the read's lookup is a function of that chain and the state — the same refusal, or the
  same tiers — and the context's own need tier and value environment take no part.
* § 3 **Accessibility.** A local-only member whose required owner's activation is detached is
  inaccessible, by owner name and by owner depth (**`detached_access_refused`**,
  `detached_access_refused_at_depth`); an exported member stays accessible under every watermark
  (`exported_member_accessible`), and at the default watermark the law is the former one
  (`memberAccessible_attached`).
* § 4 **The zero-argument access.** A request of an exported binding IS the publication law over
  the detached context (`exported_access_is_detached`); a READ of a local-only binding keyed on a
  detached activation is refused before the cache is consulted — hit or miss
  (**`detached_local_only_read_refused`**); every other local-only request is the publication law
  in its own context (`local_only_access_is_attached`), in particular every local-only request at
  the default watermark (`local_only_access_attached_by_default`).
  **`exported_request_ignores_reader_tiers`**: two readers that differ only in their need tier and
  value environment issue THE SAME request of an exported binding.
* § 5 **Alias cells.** An exported alias's binding cell is supplied in the detached context, a
  local-only one's at the watermark of its declaring level (`aliasCellContext_exported`,
  `aliasCellContext_local`, `reattach_not_detached`, `aliasCellContext_local_attached`).

NOT claimed here (ledger row E-22): that an exported request is independent of the reader's
BINDING CONTEXT and of the CONTENTS of the detached activations. Both are identities by design —
they key local-only entries and alias cells, and CACHE-OWNER-D1 inherits one — so that statement is
a whole-evaluator non-interference theorem over the fuel-indexed core, and it is open. Nor is the
front end's classification itself modelled: exposure stays an input.
C# mirrors the rule (`Evaluator.DetachedEvaluation`, `Evaluator.CapturedParameterActivation`,
`Evaluator.IsAccessibleFrom`, `Evaluator.DetachedLocalOnlyRead`); `DetachedExportedEvaluationTests`
and the host-built `HostParentDifferential` guards run both sides on mis-exposed trees.
-/

namespace KatLang.DetachedEvaluation

theorem bind_run {α β : Type} (m : EvalM α) (f : α → EvalM β) (s : EvalState) :
    (m >>= f).runState s =
      (match m.runState s with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) :=
  EvalM.bind_runState m f s

theorem get_run (s : EvalState) : (get : EvalM EvalState).runState s = (.ok s, s) := rfl
theorem pure_run {α : Type} (a : α) (s : EvalState) : (pure a : EvalM α).runState s = (.ok a, s) := rfl
theorem throw_run {α : Type} (e : Error) (s : EvalState) :
    (throw e : EvalM α).runState s = (.error e, s) := rfl

/-! ## 1. The watermark -/

theorem isDetached_iff (ctx : EvalCtx) (id : Nat) :
    ctx.isDetached id = true ↔ id < ctx.detachedBefore := by
  simp [EvalCtx.isDetached]

/-- At the default watermark no activation is detached. -/
theorem nothing_detached_by_default (ctx : EvalCtx) (h : ctx.detachedBefore = 0) (id : Nat) :
    ctx.isDetached id = false := by
  simp [EvalCtx.isDetached, h]

/-- At the default watermark the usable-activation test is the former `Option.isSome`. -/
theorem usableActivation_attached (ctx : EvalCtx) (h : ctx.detachedBefore = 0) (activation : Option Nat) :
    ctx.usableActivation activation = activation.isSome := by
  cases activation <;> simp [EvalCtx.usableActivation, EvalCtx.isDetached, h]

/-- A usable activation exists: the watermark only ever removes owners. -/
theorem usableActivation_isSome (ctx : EvalCtx) (activation : Option Nat)
    (h : ctx.usableActivation activation = true) : activation.isSome = true := by
  cases activation with
  | none => simp [EvalCtx.usableActivation] at h
  | some _ => rfl

theorem usableActivation_detached (ctx : EvalCtx) (id : Nat) (h : id < ctx.detachedBefore) :
    ctx.usableActivation (some id) = false := by
  simp [EvalCtx.usableActivation, EvalCtx.isDetached, h]

/-- **Detachment detaches every activation recorded so far.** -/
theorem detach_detaches_recorded (ctx : EvalCtx) (activations id : Nat) (h : id < activations) :
    (ctx.detach activations).isDetached id = true := by
  rw [isDetached_iff]
  show id < max ctx.detachedBefore activations
  omega

/-- An activation recorded later, and not already detached, stays usable. -/
theorem detach_keeps_later (ctx : EvalCtx) (activations id : Nat)
    (hctx : ctx.detachedBefore ≤ id) (h : activations ≤ id) :
    (ctx.detach activations).isDetached id = false := by
  have hnot : ¬ id < (ctx.detach activations).detachedBefore := by
    show ¬ id < max ctx.detachedBefore activations
    omega
  simpa [EvalCtx.isDetached] using hnot

/-- A nested detachment never lowers the watermark: detached stays detached. -/
theorem detach_never_lowers (ctx : EvalCtx) (activations : Nat) :
    ctx.detachedBefore ≤ (ctx.detach activations).detachedBefore := by
  show ctx.detachedBefore ≤ max ctx.detachedBefore activations
  omega

/-- Detachment keeps every IDENTITY of the context: its call stack, head scope and binding context. -/
theorem detach_keeps_identity (ctx : EvalCtx) (activations : Nat) :
    (ctx.detach activations).callStack = ctx.callStack
      ∧ (ctx.detach activations).headScope = ctx.headScope
      ∧ (ctx.detach activations).bindingContext = ctx.bindingContext :=
  ⟨rfl, rfl, rfl⟩

theorem detach_empties_the_need_tier (ctx : EvalCtx) (activations : Nat) :
    (ctx.detach activations).needEnv = [] := rfl

/-- A pushed head inherits the watermark. -/
theorem push_inherits_watermark (ctx : EvalCtx) (a : Algorithm) :
    (ctx.push a).detachedBefore = ctx.detachedBefore := rfl

/-- A bound callee inherits the watermark: every binding boundary keeps it. -/
theorem bindParameters_inherits_watermark (names : List Ident) (ctx : EvalCtx) (s : EvalState) :
    ∃ c t, (ctx.bindParameters names).runState s = (.ok c, t) ∧ c.detachedBefore = ctx.detachedBefore :=
  ⟨_, _, rfl, rfl⟩

/-! ## 2. Captured reads are lexical-only -/

/-- The head binds the name itself: the read uses the context's own tiers. -/
theorem captured_own_of_head (name : Ident) (ctx : EvalCtx) (site : Algorithm) (scope : ScopeCtx)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hown : site.params.contains name = true) :
    capturedParameter name ctx = .own := by
  simp only [capturedParameter, hhead, hscope, hown, ite_true]

/-- No level of the head's lexical chain binds the name: the read uses the context's own tiers. -/
theorem captured_own_without_owner (name : Ident) (ctx : EvalCtx) (site : Algorithm) (scope : ScopeCtx)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hnone : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = none) :
    capturedParameter name ctx = .own := by
  simp only [capturedParameter, hhead, hscope, hnot, hnone]
  rfl

/-- The lexical owner is activated and not detached: the read uses its activation. -/
theorem captured_activation (name : Ident) (ctx : EvalCtx) (site : Algorithm) (scope owner : ScopeCtx)
    (id : Nat)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hid : owner.activation = some id) (husable : ctx.detachedBefore ≤ id) :
    capturedParameter name ctx = .activation id := by
  have hd : ctx.isDetached id = false := by
    have hnot' : ¬ id < ctx.detachedBefore := by omega
    simpa [EvalCtx.isDetached] using hnot'
  simp only [capturedParameter, hhead, hscope, hnot, hown, hid, hd]
  rfl

/-- The lexical owner is STATIC (no activation): the name is unbound at the site. -/
theorem captured_unavailable_static (name : Ident) (ctx : EvalCtx) (site : Algorithm) (scope owner : ScopeCtx)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hid : owner.activation = none) :
    capturedParameter name ctx = .unavailable := by
  simp only [capturedParameter, hhead, hscope, hnot, hown, hid]
  rfl

/-- The lexical owner's activation is DETACHED: the name is unbound at the site. -/
theorem captured_unavailable_detached (name : Ident) (ctx : EvalCtx) (site : Algorithm) (scope owner : ScopeCtx)
    (id : Nat)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hid : owner.activation = some id) (hdetached : id < ctx.detachedBefore) :
    capturedParameter name ctx = .unavailable := by
  have hd : ctx.isDetached id = true := (isDetached_iff ctx id).mpr hdetached
  simp only [capturedParameter, hhead, hscope, hnot, hown, hid, hd]
  rfl

/-- THE INVERSE of `captured_activation`: a read that uses an activation has a lexical owner — the
    nearest level of the site scope's parent chain binding the name — that carries exactly that
    activation, usable in the context; and the head does not bind the name itself. -/
theorem captured_activation_inv (name : Ident) (ctx : EvalCtx) (id : Nat)
    (h : capturedParameter name ctx = .activation id) :
    ∃ site scope parent owner, ctx.head? = some site ∧ siteScope? ctx = some scope
      ∧ site.params.contains name = false ∧ scope.parent = some parent
      ∧ requiredParameterOwner? parent name = some owner ∧ owner.activation = some id
      ∧ ctx.detachedBefore ≤ id := by
  unfold capturedParameter at h
  cases hh : ctx.head? with
  | none => rw [hh] at h; cases h
  | some site =>
    cases hs : siteScope? ctx with
    | none => rw [hh, hs] at h; cases h
    | some scope =>
      rw [hh, hs] at h
      dsimp only at h
      cases hp : site.params.contains name with
      | true => rw [hp] at h; cases h
      | false =>
        rw [hp] at h
        cases hpar : scope.parent with
        | none => rw [hpar] at h; cases h
        | some parent =>
          rw [hpar] at h
          cases ho : requiredParameterOwner? parent name with
          | none =>
            have : (some parent >>= fun parent => requiredParameterOwner? parent name) = none := ho
            simp only [Bool.false_eq_true, ite_false, this] at h
            cases h
          | some owner =>
            have hbind : (some parent >>= fun parent => requiredParameterOwner? parent name) = some owner := ho
            simp only [Bool.false_eq_true, ite_false, hbind] at h
            cases ha : owner.activation with
            | none => rw [ha] at h; cases h
            | some i =>
              rw [ha] at h
              dsimp only at h
              cases hd : ctx.isDetached i with
              | true => rw [hd] at h; cases h
              | false =>
                rw [hd] at h
                simp only [Bool.false_eq_true, ite_false, CapturedParameter.activation.injEq] at h
                subst h
                refine ⟨site, scope, parent, owner, rfl, rfl, hp, hpar, ho, ha, ?_⟩
                have hnot : ¬ i < ctx.detachedBefore := by
                  intro hlt
                  rw [(isDetached_iff ctx i).mpr hlt] at hd
                  cases hd
                omega

/-- **The lookup of an unavailable parameter is REFUSED**: `unknownName`, in the state the lookup
    started from. No state is read and none changes. -/
theorem unavailable_lookup_refused (name : Ident) (ctx : EvalCtx) (s : EvalState)
    (h : capturedParameter name ctx = .unavailable) :
    (capturedParameterActivation? name ctx).runState s = (.error (Error.unknownName name), s) := by
  simp only [capturedParameterActivation?, h]
  rfl

/-- An `own` read uses no activation. -/
theorem own_reads_the_context (name : Ident) (ctx : EvalCtx) (s : EvalState)
    (h : capturedParameter name ctx = .own) :
    (capturedParameterActivation? name ctx).runState s = (.ok none, s) := by
  simp only [capturedParameterActivation?, h]
  rfl

/-- An `activation` read uses the recorded activation, read from the state. It changes the state
    only by recording the read as an input of the retained cell whose computation `ctx` belongs to
    (`EvalState.noteInput`, ledger R-1; nothing outside every cell's computation) — unless the read
    lands below a reader already admitted to that cell (`activation_late_refused`). -/
theorem activation_reads_the_record (name : Ident) (ctx : EvalCtx) (s : EvalState) (id : Nat)
    (h : capturedParameter name ctx = .activation id) (hl : s.lateRefusedFor ctx id = false) :
    (capturedParameterActivation? name ctx).runState s =
      (.ok s.lexicalActivations[id]?, s.noteInput ctx id) := by
  have hn : (noteCellInput ctx id (Error.unknownName name)).runState s =
      (.ok (), s.noteInput ctx id) := by
    rw [noteCellInput_run, hl]; rfl
  simp only [capturedParameterActivation?, h, bind_run, hn, get_run, pure_run,
    EvalState.noteInput_lexicalActivations]

/-- DEFERRED READS (ledger R-1): an `activation` read that lands below a reader already ADMITTED to
    the retained cell whose computation `ctx` belongs to (`EvalState.lateRefusedFor`) is the same
    `unknownName` refusal as an unavailable parameter's, in the state it started from — the refusal
    that reader's own detached context reports for the read. -/
theorem activation_late_refused (name : Ident) (ctx : EvalCtx) (s : EvalState) (id : Nat)
    (h : capturedParameter name ctx = .activation id) (hl : s.lateRefusedFor ctx id = true) :
    (capturedParameterActivation? name ctx).runState s = (.error (Error.unknownName name), s) := by
  have hn : (noteCellInput ctx id (Error.unknownName name)).runState s = (.error (Error.unknownName name), s) := by
    rw [noteCellInput_run, hl]; rfl
  simp only [capturedParameterActivation?, h, bind_run, hn]

/-- An unavailable parameter has NO read context: the refusal, before any tier is consulted. -/
theorem unavailable_context_refused (name : Ident) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (h : capturedParameter name ctx = .unavailable) :
    (parameterContext name ctx env).runState s = (.error (Error.unknownName name), s) := by
  simp only [parameterContext, bind_run, unavailable_lookup_refused name ctx s h]

/-- **`detached_param_read_refused`.** The VALUE read of a parameter that is unavailable at the
    site — its lexical owner is static, or its activation is detached — is `unknownName`, in the
    state the read started from: nothing is demanded, evaluated or written, and the context's own
    tiers are never consulted, whatever they bind under that name. -/
theorem detached_param_read_refused (rec : EvalRec) (name : Ident) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (h : capturedParameter name ctx = .unavailable) :
    (EvalBody.evalCounted rec (.param name) ctx env).runState s = (.error (Error.unknownName name), s) := by
  show ((do
      let (ctx, env) <- parameterContext name ctx env
      if let some address := lookupAssoc name ctx.needEnv then
        return <- rec.demandNeedRecursive address
      match env.lookup name with
      | some v => pure (v, Result.valueCount v)
      | none => .error (Error.unknownName name)) : EvalM CountedResult).runState s = _
  simp only [bind_run, unavailable_context_refused name ctx env s h]

/-- The detached case of `detached_param_read_refused`, stated on the chain: the nearest level
    binding the name was activated BEFORE the exported evaluation the context is inside started. -/
theorem detached_owner_read_refused (rec : EvalRec) (name : Ident) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (site : Algorithm) (scope owner : ScopeCtx) (id : Nat)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hid : owner.activation = some id) (hdetached : id < ctx.detachedBefore) :
    (EvalBody.evalCounted rec (.param name) ctx env).runState s = (.error (Error.unknownName name), s) :=
  detached_param_read_refused rec name ctx env s
    (captured_unavailable_detached name ctx site scope owner id hhead hscope hnot hown hid hdetached)

/-- The static case: a read through an owner that no call of it activated is `unknownName` — it is
    no longer answered by a dynamically live caller's binding of the same name. -/
theorem static_owner_read_refused (rec : EvalRec) (name : Ident) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (site : Algorithm) (scope owner : ScopeCtx)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hid : owner.activation = none) :
    (EvalBody.evalCounted rec (.param name) ctx env).runState s = (.error (Error.unknownName name), s) :=
  detached_param_read_refused rec name ctx env s
    (captured_unavailable_static name ctx site scope owner hhead hscope hnot hown hid)

/-- **The TRANSPORT of an unavailable parameter is refused.** Supplying the written parameter
    directly — as an argument, a callee, a link receiver or an alias row, each through the ONE
    supplier — is `unknownName` in the state the supply started from: NOTHING is allocated, and the
    refusal does not wait for a demand, so a receiver that ignores the argument (`Ignore(y)`) is
    refused all the same. (A supplied computation that merely CONTAINS the parameter, `F(y + 1)`,
    stays a suspended cell: `supply_nonparameter`.) -/
theorem unavailable_transport_refused (name : Ident) (caller : EvalCtx) (values : ValEnv) (s : EvalState)
    (h : capturedParameter name caller = .unavailable) :
    (supplyNeed (.param name) caller values).runState s = (.error (Error.unknownName name), s) := by
  simp only [supplyNeed, bind_run, unavailable_lookup_refused name caller s h]

/-- **The CALLABLE projection of an unavailable parameter is refused**: `unknownName`, never the
    absence a usable valueless binding reports and never a caller's callable. The projector is
    never run. So invoking such a parameter (`y(5)`) reports the unavailable NAME, not a missing
    callable capability. -/
theorem unavailable_projection_refused (project : Nat → EvalM (Option Algorithm)) (name : Ident)
    (ctx : EvalCtx) (s : EvalState) (h : capturedParameter name ctx = .unavailable) :
    (projectParameterWith project name ctx).runState s = (.error (Error.unknownName name), s) := by
  simp only [projectParameterWith, bind_run, unavailable_lookup_refused name ctx s h]

/-- The lookup of the cell an unavailable parameter would hold is refused (the written-callee
    origin, a parameter-row alias's own cell). -/
theorem unavailable_cell_lookup_refused (name : Ident) (caller : EvalCtx) (s : EvalState)
    (h : capturedParameter name caller = .unavailable) :
    (parameterNeedAddress? name caller).runState s = (.error (Error.unknownName name), s) := by
  simp only [parameterNeedAddress?, bind_run, unavailable_lookup_refused name caller s h]

/-- The supplied-cell test of an unavailable parameter receiver is refused (the `string` intrinsic's
    receiver read). -/
theorem unavailable_cell_test_refused (name : Ident) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (h : capturedParameter name ctx = .unavailable) :
    (hasSuppliedParameterCell (.param name) ctx env).runState s = (.error (Error.unknownName name), s) := by
  simp only [hasSuppliedParameterCell, bind_run, unavailable_context_refused name ctx env s h]

/-- A spread of an unavailable parameter is refused where its known slice is looked up. -/
theorem unavailable_spread_refused (name : Ident) (caller : EvalCtx) (s : EvalState)
    (h : capturedParameter name caller = .unavailable) :
    (spreadCollectorSlice? (.param name) caller).runState s = (.error (Error.unknownName name), s) := by
  simp only [spreadCollectorSlice?, bind_run, unavailable_cell_lookup_refused name caller s h]

/-- A PARAMETER-ROW alias whose row is unavailable in the alias's own head context has no binding
    cell: establishing it is the transport refusal, and nothing is recorded. -/
theorem unavailable_alias_row_refused (wired : Algorithm) (name : Ident) (ctx : EvalCtx) (s : EvalState)
    (h : capturedParameter name (ctx.push wired) = .unavailable) :
    (aliasBindingCell wired (.param name) ctx).runState s = (.error (Error.unknownName name), s) :=
  unavailable_transport_refused name (ctx.push wired) [] s h

/-- AN ABSENT LEXICAL OWNER KEEPS THE CONTEXT LOOKUP: an `own` parameter — the head's own, or one no
    level of its lexical chain binds (a builtin wrapper's argument, a host-built free parameter) —
    is supplied from the context's own need tier: its cell when the tier binds it. -/
theorem own_transport_uses_the_context (name : Ident) (caller : EvalCtx) (values : ValEnv) (s : EvalState)
    (address : Nat) (h : capturedParameter name caller = .own)
    (hbound : lookupAssoc name caller.needEnv = some address) :
    (supplyNeed (.param name) caller values).runState s = (.ok address, s) := by
  have hc : (capturedParameterActivation? name caller).runState s = (.ok none, s) := by
    simp only [capturedParameterActivation?, h]
    rfl
  simp only [supplyNeed, bind_run, hc, Option.map_none, Option.getD_none, hbound]
  rfl

/-- AVAILABLE CELLS TRANSPORT LAZILY: a parameter whose lexical owner's activation is usable and
    binds it is supplied as that activation's existing cell — nothing is allocated, demanded or
    projected, and the state changes only by the input record of the retained cell whose
    computation the transport belongs to (`EvalState.noteInput`; ledger R-1). -/
theorem available_transport_is_lazy (name : Ident) (caller : EvalCtx) (values : ValEnv) (s : EvalState)
    (id address : Nat) (activation : ParameterActivation)
    (h : capturedParameter name caller = .activation id)
    (hrecord : s.lexicalActivations[id]? = some activation)
    (hbound : lookupAssoc name activation.needs = some address)
    (hl : s.lateRefusedFor caller id = false) :
    (supplyNeed (.param name) caller values).runState s =
      (.ok address, s.noteInput caller id) := by
  have hc := activation_reads_the_record name caller s id h hl
  rw [hrecord] at hc
  simp only [supplyNeed, bind_run, hc, Option.map_some, Option.getD_some, hbound]
  rfl

/-- The classifier reads the context's call stack, head scope and watermark only. -/
theorem capturedParameter_ignores_tiers (name : Ident) (ctx : EvalCtx) (needs : NeedEnv) (binding : Nat) :
    capturedParameter name { ctx with needEnv := needs, bindingContext := binding } = capturedParameter name ctx :=
  rfl

/-- **`captured_read_is_lexical`.** Whenever a level of the head's lexical chain binds the name
    (and the head does not bind it itself), the outcome of its read's lookup (`parameterContext`)
    is a function of that chain, the watermark and the state: the reading context's OWN need tier,
    binding context and value environment take no part. Two readers that differ only in those are
    BOTH refused with `unknownName` — the owner is static or detached — or obtain the SAME tiers,
    the owner activation's. This is the statement the E-18 premise `ParamRowOwned`
    (`NavigationContract`) asked of a parameter-row alias, now a property of every captured read:
    an owner that is not activated yields the refusal (`captured_unavailable_static`) instead of
    the chasing context's binding. Both readers also leave the SAME state: the input record of the
    retained cell whose computation they belong to, if any, takes the same read (ledger R-1). -/
theorem captured_read_is_lexical (name : Ident) (ctx : EvalCtx) (env env' : ValEnv) (needs' : NeedEnv)
    (binding' : Nat) (s : EvalState) (site : Algorithm) (scope owner : ScopeCtx)
    (hhead : ctx.head? = some site) (hscope : siteScope? ctx = some scope)
    (hnot : site.params.contains name = false)
    (hown : (scope.parent >>= fun parent => requiredParameterOwner? parent name) = some owner)
    (hvalid : ∀ id, owner.activation = some id → id < s.lexicalActivations.size) :
    ((parameterContext name ctx env).runState s = (.error (Error.unknownName name), s)
      ∧ (parameterContext name { ctx with needEnv := needs', bindingContext := binding' } env').runState s =
          (.error (Error.unknownName name), s))
    ∨ ∃ tier values t,
      (parameterContext name ctx env).runState s = (.ok ({ ctx with needEnv := tier }, values), t)
      ∧ (parameterContext name { ctx with needEnv := needs', bindingContext := binding' } env').runState s =
          (.ok ({ ctx with needEnv := tier, bindingContext := binding' }, values), t) := by
  cases hid : owner.activation with
  | none =>
    have hu := captured_unavailable_static name ctx site scope owner hhead hscope hnot hown hid
    refine .inl ⟨unavailable_context_refused name ctx env s hu, ?_⟩
    exact unavailable_context_refused name _ env' s (by rw [capturedParameter_ignores_tiers]; exact hu)
  | some id =>
    by_cases hd : id < ctx.detachedBefore
    · have hu := captured_unavailable_detached name ctx site scope owner id hhead hscope hnot hown hid hd
      refine .inl ⟨unavailable_context_refused name ctx env s hu, ?_⟩
      exact unavailable_context_refused name _ env' s (by rw [capturedParameter_ignores_tiers]; exact hu)
    · have ha := captured_activation name ctx site scope owner id hhead hscope hnot hown hid (by omega)
      have ha' : capturedParameter name { ctx with needEnv := needs', bindingContext := binding' } = .activation id := by
        rw [capturedParameter_ignores_tiers]; exact ha
      have hq : s.lateRefusedFor { ctx with needEnv := needs', bindingContext := binding' } id =
          s.lateRefusedFor ctx id := rfl
      cases hl : s.lateRefusedFor ctx id with
      | true =>
        -- A read below an admitted reader of the cell both readers belong to: both refused alike.
        refine .inl ⟨?_, ?_⟩
        · simp only [parameterContext, bind_run, activation_late_refused name ctx s id ha hl]
        · simp only [parameterContext, bind_run, activation_late_refused name _ s id ha' (hq.trans hl)]
      | false =>
      have hlt := hvalid id hid
      have hget : s.lexicalActivations[id]? = some s.lexicalActivations[id] := by
        simp [hlt]
      refine .inr ⟨s.lexicalActivations[id].needs, s.lexicalActivations[id].values,
        s.noteInput ctx id, ?_, ?_⟩
      · simp only [parameterContext, bind_run, activation_reads_the_record name ctx s id ha hl, hget]
        rfl
      · simp only [parameterContext, bind_run, activation_reads_the_record name _ s id ha' (hq.trans hl), hget]
        rfl

/-! ## 3. Accessibility -/

/-- An exported member is accessible under every watermark: detachment refuses INPUTS, and an
    exported member has none. -/
theorem exported_member_accessible (ctx : EvalCtx) (container : Algorithm) (p : PropDef)
    (h : p.exposure = .exported) : memberAccessible? ctx container p = true := by
  simp only [memberAccessible?, h]

/-- **`detached_access_refused`.** A local-only member one of whose required owners — found by the
    nearest-owner walk on the container's chain in context — has a DETACHED activation is
    inaccessible: the access is the existing `localOnlyProperty` refusal. -/
theorem detached_access_refused (ctx : EvalCtx) (container : Algorithm) (p : PropDef)
    (required : List Ident) (site owner : ScopeCtx) (name : Ident) (id : Nat)
    (hexposure : p.exposure = .localCapturedAncestorParams required)
    (hsite : siteScope? ctx = some site)
    (hdepths : p.requiredOwnerDepths = none)
    (hname : name ∈ required)
    (hown : requiredParameterOwner? (scopeInContext container ctx) name = some owner)
    (hid : owner.activation = some id) (hdetached : id < ctx.detachedBefore) :
    memberAccessible? ctx container p = false := by
  simp only [memberAccessible?, hexposure, hsite, hdepths]
  rw [List.all_eq_false]
  refine ⟨name, hname, ?_⟩
  simp [hown, hid, usableActivation_detached ctx id hdetached]

/-- `detached_access_refused` for a member whose requirements carry exact owner depths. -/
theorem detached_access_refused_at_depth (ctx : EvalCtx) (container : Algorithm) (p : PropDef)
    (required : List Ident) (requirements : List (Ident × Option Nat)) (site owner : ScopeCtx)
    (name : Ident) (depth : Option Nat) (id : Nat)
    (hexposure : p.exposure = .localCapturedAncestorParams required)
    (hsite : siteScope? ctx = some site)
    (hdepths : p.requiredOwnerDepths = some requirements)
    (hname : (name, depth) ∈ requirements)
    (hown : (depth >>= (scopeInContext container ctx).ancestor?) = some owner)
    (hid : owner.activation = some id) (hdetached : id < ctx.detachedBefore) :
    memberAccessible? ctx container p = false := by
  simp only [memberAccessible?, hexposure, hsite, hdepths]
  rw [List.all_eq_false]
  refine ⟨(name, depth), hname, ?_⟩
  simp [hown, hid, usableActivation_detached ctx id hdetached]

/-- At the default watermark the accessibility law is the one it was: every `usableActivation`
    test is the former `Option.isSome`. -/
theorem memberAccessible_attached (ctx : EvalCtx) (h : ctx.detachedBefore = 0) (container : Algorithm)
    (p : PropDef) :
    memberAccessible? ctx container p =
      (match p.exposure with
       | .exported => true
       | .localConditional => false
       | .localCapturedAncestorParams required =>
           match siteScope? ctx with
           | none => false
           | some _ =>
               let declaringScope := scopeInContext container ctx
               match p.requiredOwnerDepths with
               | some requirements => requirements.all fun (name, depth) =>
                   match depth >>= declaringScope.ancestor? with
                   | some owner =>
                       owner.params.contains name && owner.activation.isSome && lexicalChainContains ctx owner
                   | none => false
               | none => required.all fun name =>
                   match requiredParameterOwner? declaringScope name with
                   | some owner => owner.activation.isSome && lexicalChainContains ctx owner
                   | none => false) := by
  simp only [memberAccessible?, usableActivation_attached ctx h]
  rfl

/-! ## 4. The zero-argument access -/

/-- **Exported means detached.** Every request of an exported binding — a read and an invocation
    alike — IS the publication law over the detached context and no inherited values, at the
    number of activations recorded when the request starts, run while the input records SERVE that
    context's watermark (`servingDetached`, ledger R-1): an input read the request demands in a
    retained cell's computation is judged against it. -/
theorem exported_access_is_detached (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest) (s : EvalState) (h : binding.exposure.isExported = true) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request).runState s =
      (servingDetached (ctx.detach s.lexicalActivations.size).detachedBefore
        (EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm
          (ctx.detach s.lexicalActivations.size) [] request)).runState s := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, h, ite_true, bind_run, get_run]

/-- When the input records already serve the request's watermark — a request made inside the
    evaluation it would serve — the exported access IS the publication law over the detached context,
    in the same state. -/
theorem exported_access_is_detached_served (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest) (s : EvalState) (h : binding.exposure.isExported = true)
    (hs : (ctx.detach s.lexicalActivations.size).detachedBefore ≤ s.cellInputs.serving) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request).runState s =
      (EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm
        (ctx.detach s.lexicalActivations.size) [] request).runState s := by
  rw [exported_access_is_detached rec accessKind owner binding resolvedAlgorithm ctx env request s h,
    servingDetached_runState]
  simp only [hs, ↓reduceIte]

/-- **`detached_local_only_read_refused`.** A property-style READ of a local-only binding whose
    key names a detached activation — the nearest activated level of its declaring chain was
    recorded before the watermark — is `localOnlyProperty`, in the state the read started from. No
    premise mentions the cache: an established entry is refused exactly like a miss. -/
theorem detached_local_only_read_refused (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (id : Nat)
    (hlocal : binding.exposure.isExported = false)
    (hnearest : nearestActivation? resolvedAlgorithm.parent = some id)
    (hdetached : id < ctx.detachedBefore) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env .read).runState s =
      (.error (Error.localOnlyProperty detachedReadDescription binding.name binding.exposure), s) := by
  have hrefused : localOnlyReadRefused binding resolvedAlgorithm ctx = true := by
    simp only [localOnlyReadRefused, hlocal, hnearest, (isDetached_iff ctx id).mpr hdetached, Bool.not_false,
      Bool.and_self]
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hlocal, hrefused, ZeroArgPropertyRequest.isRead,
    Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
  rfl

/-- A local-only request that is not a refused read is the publication law in its own context,
    after a READ has recorded its input read through the key's activation on the retained cell
    whose computation it belongs to (`noteLocalOnlyRead`, ledger R-1). -/
theorem local_only_access_is_attached (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest)
    (hlocal : binding.exposure.isExported = false)
    (hadmitted : (request.isRead && localOnlyReadRefused binding resolvedAlgorithm ctx) = false) :
    EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request =
      (do
        if request.isRead then noteLocalOnlyRead binding resolvedAlgorithm ctx
        EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hlocal, hadmitted, Bool.false_eq_true, ite_false]

/-- Outside every retained cell's computation the read's note is nothing. -/
theorem noteLocalOnlyRead_unmarked (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
    (h : ctx.inputRecord = none) : noteLocalOnlyRead binding resolvedAlgorithm ctx = pure () := by
  unfold noteLocalOnlyRead noteCellInput
  split <;> simp [h]

/-- An admitted local-only request outside every retained cell's computation is the publication
    law in its own context, read or invocation alike. -/
theorem local_only_access_is_attached_unmarked (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest)
    (hlocal : binding.exposure.isExported = false)
    (hadmitted : (request.isRead && localOnlyReadRefused binding resolvedAlgorithm ctx) = false)
    (hunmarked : ctx.inputRecord = none) :
    EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request =
      EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request := by
  rw [local_only_access_is_attached rec accessKind owner binding resolvedAlgorithm ctx env request hlocal hadmitted,
    noteLocalOnlyRead_unmarked binding resolvedAlgorithm ctx hunmarked]
  split <;> rfl

/-- The read's note writes the input records only — or, when the read lands below a reader already
    admitted to the retained cell whose computation `ctx` belongs to (ledger R-1, deferred reads), it
    is the read's own `localOnlyProperty` refusal, in the state it started from. -/
theorem noteLocalOnlyRead_run (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (s : EvalState) :
    (noteLocalOnlyRead binding resolvedAlgorithm ctx).runState s =
        (.error (Error.localOnlyProperty detachedReadDescription binding.name binding.exposure), s) ∨
      ∃ t, (noteLocalOnlyRead binding resolvedAlgorithm ctx).runState s = (.ok (), t) ∧
        t = { s with cellInputs := t.cellInputs } := by
  unfold noteLocalOnlyRead
  split
  · rename_i id _
    rcases noteCellInput_outcome ctx id
        (Error.localOnlyProperty detachedReadDescription binding.name binding.exposure) s with h | h
    · exact .inl h
    · exact .inr ⟨_, h, EvalState.noteInput_eq _ _ _⟩
  · exact .inr ⟨s, rfl, rfl⟩

/-- The admitted local-only arm is the publication law run from the state the read's note left,
    which differs from the entry state in its input records only (ledger R-1). -/
theorem note_then_publication (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest) (s : EvalState) :
    ((do
        if request.isRead then noteLocalOnlyRead binding resolvedAlgorithm ctx
        EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request) :
          EvalM CountedResult).runState s =
        (.error (Error.localOnlyProperty detachedReadDescription binding.name binding.exposure), s) ∨
    ∃ t, t = { s with cellInputs := t.cellInputs } ∧
      ((do
        if request.isRead then noteLocalOnlyRead binding resolvedAlgorithm ctx
        EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request) :
          EvalM CountedResult).runState s =
        (EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request).runState t := by
  have hsplit : ((do
      if request.isRead then noteLocalOnlyRead binding resolvedAlgorithm ctx
      EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request) :
        EvalM CountedResult)
      = ((if request.isRead then noteLocalOnlyRead binding resolvedAlgorithm ctx else pure ()) >>= fun _ =>
          EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request) := by
    split <;> rfl
  rw [hsplit, bind_run]
  cases hr : request.isRead with
  | false => exact .inr ⟨s, rfl, rfl⟩
  | true =>
    rcases noteLocalOnlyRead_run binding resolvedAlgorithm ctx s with ht | ⟨t, ht, hframe⟩
    · refine .inl ?_
      simp only [ite_true]
      rw [ht]
    · refine .inr ⟨t, hframe, ?_⟩
      simp only [ite_true]
      rw [ht]

/-- No local-only read is refused at the default watermark. -/
theorem nothing_refused_by_default (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
    (h : ctx.detachedBefore = 0) : localOnlyReadRefused binding resolvedAlgorithm ctx = false := by
  unfold localOnlyReadRefused
  cases nearestActivation? resolvedAlgorithm.parent with
  | none => simp
  | some id => simp [nothing_detached_by_default ctx h id]

/-- At the default watermark, outside every retained cell's computation, every local-only request
    is the publication law in its own context: outside every exported evaluation a local-only
    binding is read as it always was. -/
theorem local_only_access_attached_by_default (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (request : ZeroArgPropertyRequest)
    (hlocal : binding.exposure.isExported = false) (h : ctx.detachedBefore = 0)
    (hunmarked : ctx.inputRecord = none) :
    EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request =
      EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env request :=
  local_only_access_is_attached_unmarked rec accessKind owner binding resolvedAlgorithm ctx env request hlocal
    (by rw [nothing_refused_by_default binding resolvedAlgorithm ctx h, Bool.and_false]) hunmarked

/-- An explicit invocation of a local-only binding is never refused up front: it is its own fresh
    calculation, which the two read rules confine (and it records no read of its own). -/
theorem local_only_invocation_is_attached (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (calleeName : String) (hlocal : binding.exposure.isExported = false) :
    EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env (.invoke calleeName) =
      EvalBody.zeroArgPropertyPublication rec accessKind owner binding resolvedAlgorithm ctx env (.invoke calleeName) := by
  rw [local_only_access_is_attached rec accessKind owner binding resolvedAlgorithm ctx env (.invoke calleeName) hlocal rfl]
  rfl

/-- The detached context does not depend on the reader's need tier. -/
theorem detach_ignores_the_need_tier (ctx : EvalCtx) (needs : NeedEnv) (activations : Nat) :
    ({ ctx with needEnv := needs } : EvalCtx).detach activations = ctx.detach activations := rfl

/-- **`exported_request_ignores_reader_tiers`.** Two readers that differ only in their inherited
    need tier and value environment issue THE SAME request of an exported binding: the same
    program, hence the same outcome, state, charges and publication from every state. The
    dynamic-scoping channel — a caller's bindings reaching an exported body through the inherited
    tiers — is closed by construction. (Independence of the reader's binding context and of the
    contents of the detached activations is the open part: ledger row E-22.) -/
theorem exported_request_ignores_reader_tiers (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
    (env env' : ValEnv) (needs' : NeedEnv) (request : ZeroArgPropertyRequest)
    (h : binding.exposure.isExported = true) :
    EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm
        { ctx with needEnv := needs' } env' request =
      EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, h, ite_true, detach_ignores_the_need_tier]

/-! ## 5. Alias cells -/

/-- An EXPORTED alias's binding cell is supplied in the detached context: its row is evaluated where
    an exported property is. -/
theorem aliasCellContext_exported (wired : Algorithm) (ctx : EvalCtx) (state : EvalState)
    (h : aliasCellIsExported wired = true) :
    aliasCellContext wired ctx state = ctx.detach state.lexicalActivations.size := by
  simp only [aliasCellContext, h, ite_true]

/-- A local-only alias's binding cell is supplied AT THE WATERMARK OF ITS DECLARING LEVEL (ledger R-1):
    the using context reattached at the nearest activation of the alias's declaring chain — the
    activation its key names — and the using context itself when the chain has none. -/
theorem aliasCellContext_local (wired : Algorithm) (ctx : EvalCtx) (state : EvalState)
    (h : aliasCellIsExported wired = false) :
    aliasCellContext wired ctx state =
      match nearestActivation? wired.parent with
      | some activation => ctx.reattach activation
      | none => ctx := by
  simp only [aliasCellContext, h, Bool.false_eq_true, ite_false]
  cases nearestActivation? wired.parent <;> rfl

/-- The watermark reattaching selects never detaches the activation. -/
theorem attachedLevel_le (activation : Nat) :
    ∀ (outer : List Nat) (level : Nat), (EvalCtx.attachedLevel activation level outer).fst ≤ activation
  | [], level => by
      unfold EvalCtx.attachedLevel
      split
      · rename_i h; exact h
      · exact Nat.zero_le _
  | next :: rest, level => by
      unfold EvalCtx.attachedLevel
      split
      · rename_i h; exact h
      · exact attachedLevel_le activation rest next

/-- **The reattached context does not detach the activation**: the row of a local-only alias may use
    the inputs of its declaring level, whichever reader supplies it. -/
theorem reattach_not_detached (ctx : EvalCtx) (activation : Nat) :
    (ctx.reattach activation).isDetached activation = false := by
  have h := attachedLevel_le activation ctx.outerDetached ctx.detachedBefore
  simp only [EvalCtx.reattach, EvalCtx.isDetached]
  exact decide_eq_false (by omega)

/-- A context that does not detach the activation is unchanged by reattaching at it. -/
theorem reattach_attached (ctx : EvalCtx) (activation : Nat) (h : ctx.isDetached activation = false) :
    ctx.reattach activation = ctx := by
  have hle : ctx.detachedBefore ≤ activation := by
    simp only [EvalCtx.isDetached, decide_eq_false_iff_not] at h
    omega
  have hlevel : EvalCtx.attachedLevel activation ctx.detachedBefore ctx.outerDetached =
      (ctx.detachedBefore, ctx.outerDetached) := by
    cases ctx.outerDetached <;> simp [EvalCtx.attachedLevel, hle]
  unfold EvalCtx.reattach
  rw [hlevel]

/-- Reattaching changes the watermark alone: the call stack, the need tier, the binding context, the
    head scope and the input record are the using context's. -/
theorem reattach_fields (ctx : EvalCtx) (activation : Nat) :
    (ctx.reattach activation).callStack = ctx.callStack ∧
    (ctx.reattach activation).needEnv = ctx.needEnv ∧
    (ctx.reattach activation).bindingContext = ctx.bindingContext ∧
    (ctx.reattach activation).headScope = ctx.headScope ∧
    (ctx.reattach activation).inputRecord = ctx.inputRecord :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A reader that does not detach the alias's declaring level — every reader of a correctly
    classified program — supplies a local-only alias's row in the using context, as before. -/
theorem aliasCellContext_local_attached (wired : Algorithm) (ctx : EvalCtx) (state : EvalState)
    (h : aliasCellIsExported wired = false)
    (ha : ∀ activation, nearestActivation? wired.parent = some activation → ctx.isDetached activation = false) :
    aliasCellContext wired ctx state = ctx := by
  rw [aliasCellContext_local wired ctx state h]
  cases hn : nearestActivation? wired.parent with
  | none => rfl
  | some activation => exact reattach_attached ctx activation (ha activation hn)

end KatLang.DetachedEvaluation
