import KatLangArityLaws.OwnerContextStability

open KatLang KatLang.EvaluatorCore KatLang.EvaluatorCacheLaws KatLang.WhileRoundProduction
open KatLang.PropertyOwnerContext KatLang.WhileRoundLaws KatLang.BinderTrace

/-!
# INNER-PROPERTY LIFETIME: storage follows the declaring binding and its owning invocation (November 2026)

Until November 2026 the EXPOSURE of a property decided how long its value lived: an `exported`
(self-contained) property had ONE entry per run, shared by every call of its owner, and a
local-only one had one per activation of its declaring owner. The owner decision of the
EXPORTED-DETACHED follow-up separates the two questions. Exposure still governs ACCESSIBILITY
(`memberAccessible?`) and DETACHMENT (`EvalBody.evalZeroArgPropertyAccessCounted`); the STORAGE of
a property-style binding — a zero-argument property entry and a runtime-alias binding cell alike —
is chosen by the resolved declaring binding and its OWNING INVOCATION:

* every ACTUAL CALL of an owner has fresh bindings for the owner's inner properties, whether their
  definitions use the call's arguments or are self-contained;
* reads in the same owning invocation share that invocation's result or cell;
* where no call owns the declaring chain — a member read from outside its owner's call, a root or
  module property — the binding is the separate RUN-SCOPED one.

What is proved here, over the production definitions of `KatLang.lean`:

* § 1 **The invocation mark.** A body entry made under the mark ALWAYS records an activation, marked
  `ownsInvocation`, with the entry's binding context (`invoked_entry_records`), and the mark is consumed
  by the push (`push_consumes_the_mark`, `entered_ctx_is_unmarked`); an entry without the mark
  records exactly as before and never an invoked activation (`unmarked_entry_never_invokes`); a
  property-style read's entry is unmarked, whatever context it is made in
  (`read_entry_is_unmarked`): a read gives a binding no new lifetime.
* § 2 **The owning invocation.** `propertyOwnerInvocation` is the binding context of the nearest
  INVOKED level of the declaring chain (`ownerInvocation_invoked`), skips a level a read activated
  (`ownerInvocation_read_level`) and an unactivated one (`ownerInvocation_unactivated`), and is
  `none` on a chain no level of which is activated (`ownerInvocation_static`): the run-scoped
  binding. On a chain whose search stays inside the activation array (`InvocationSearchValid`) it
  is stable under every extension of that array (`ownerInvocation_stable`), so the binding a read
  resolves is the one every later read of the same declaring chain resolves, whatever ran in
  between. The production entries establish such chains with no premise on the incoming one: a
  call's own entry (`invoked_entry_owns_its_scope`) and a selected clause's family level
  (`family_activation_owns_its_scope`) each own the chain below them, at the call's binding context.
* § 3 **The key.** An exported binding's key carries exactly the owning invocation
  (`exported_key_bindingContext`) and no value environment (`exported_key_has_no_valEnv`); it
  does not depend on the reader's context, value environment or declaring binding context
  (`exported_key_ignores_the_reader`: no callback, helper, open or referring caller gives the
  binding another lifetime), two different owning invocations have two different keys
  (`exported_keys_of_distinct_invocations_differ`: every call has fresh bindings) and a call's
  key is never the run-scoped one (`call_key_is_not_the_run_scoped_key`). A local-only binding's
  key is the former one: the owning invocation takes no part in it (`local_only_key_unchanged`).
  THE PRODUCTION THEOREM is `exported_entry_reused_after_production`: an entry held for a chain's
  owning invocation is what every later read through that chain returns, after any production
  operation, in any consumer context, without evaluating; `other_invocation_reads_another_key` is
  its converse on keys.
* § 4 **Alias cells.** A runtime alias's binding cell has the same component
  (`aliasCell_exported_follows_the_owning_invocation`, `aliasCell_local_only_unchanged`), so the
  cell and the entry of the same row written as a property keep one lifetime.

NOT claimed here: that the front end's classification is right (exposure stays an input); that a
miss publishes under the key a later read uses (the cache entry is a premise of the production
theorem; the owner publishes under its entry-state key, `CacheReentrancy.owner_success_establishes`);
`InvocationSearchValid` for a chain that mixes read-activated levels below a call's entry (the two
establishing laws cover the entry's own level; a level a read activates on top of a valid chain is
not derived here); which chain a given production read resolves (`scopeInContext`'s selection
fidelity, ledger E-12); anything about C#. C# mirrors the rule (`Evaluator.DeclaringInvocationIdentity`,
`ParameterActivation.OwnsInvocation`, `ZeroArgPropertyCacheKey.EnvironmentIdentity`);
`InnerPropertyLifetimeTests` and the `inner-property-lifetime-*` spec cases run both sides on the
acceptance witnesses.
-/

namespace KatLang.InnerPropertyLifetime

open KatLang.OwnerContextStability KatLang.WhileRoundProduction

/-! ## 1. The invocation mark -/

/-- The push consumes the mark: nothing below an entered head inherits it. -/
theorem push_consumes_the_mark (a : Algorithm) (ctx : EvalCtx) : (ctx.push a).enteringInvocation = false := rfl

/-- The context a body entry returns never carries the mark. -/
theorem entered_ctx_is_unmarked (a : Algorithm) (ctx : EvalCtx) (s : EvalState) :
    (enteredCtx a ctx s).enteringInvocation = false := by
  unfold enteredCtx
  split <;> rfl

/-- **Every actual call records an activation.** A body entry made under the invocation mark
    records ONE activation, whatever the body declares — parameterless, with exported members only
    — marked `ownsInvocation` and holding the entry's binding context; the entered head scope carries it. -/
theorem invoked_entry_records (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (h : ctx.enteringInvocation = true) :
    (enterAlgorithmBody a ctx env).runState s =
      (.ok { ctx.push a with headScope := some (a.asScopeCtx.withActivation s.lexicalActivations.size) },
        { s with lexicalActivations := s.lexicalActivations.push (enteredActivation a ctx env) })
      ∧ (enteredActivation a ctx env).ownsInvocation = true
      ∧ (enteredActivation a ctx env).bindingContext = ctx.bindingContext := by
  refine ⟨?_, h, rfl⟩
  rw [enter_run]
  simp only [enteredCtx, enteredState, entryRecords_of_invocation a h, ite_true]

/-- An entry without the mark never records an invoked activation. -/
theorem unmarked_entry_never_invokes (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (h : ctx.enteringInvocation = false) : (enteredActivation a ctx env).ownsInvocation = false := h

/-- An entry without the mark records exactly when the former rule says so. -/
theorem unmarked_entry_records_as_before (a : Algorithm) (ctx : EvalCtx)
    (h : ctx.enteringInvocation = false) : entryRecords a ctx = recordsActivation a :=
  entryRecords_unmarked a h

/-- **A read is never a call.** The entry of a property-style read is made without the mark,
    whatever context the read is made in: it is the entry over the context with the mark cleared,
    so an activation it records is not invoked. -/
theorem read_entry_is_unmarked (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (n : Nat) (s : EvalState) :
    ((enterPropertyOwnerBody a ctx env n).runState s).2 =
      enteredState a { ctx with bindingContext := n, enteringInvocation := false } env s
      ∧ (enteredActivation a { ctx with bindingContext := n, enteringInvocation := false } env).ownsInvocation = false := by
  refine ⟨?_, rfl⟩
  unfold enterPropertyOwnerBody
  rw [EvalM.bind_runState, enter_run]
  rfl

/-! ## 2. The owning invocation -/

theorem ownerInvocation_root (s : EvalState) : propertyOwnerInvocation none s = none := rfl

/-- **The equation of the search at one level**: an activated level whose record owns an invocation
    answers with that record's binding context; every other level — activated by a read, activated
    at a missing record, or unactivated — passes the question to its parent chain. -/
theorem ownerInvocation_level (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (activation : Option Nat)
    (decl : Option PropertyIdentity) (s : EvalState) :
    propertyOwnerInvocation (some (.mk parent params opens props output branches activation decl)) s =
      (match activation.bind (fun id => s.lexicalActivations[id]?) with
       | some found => if found.ownsInvocation then some found.bindingContext else propertyOwnerInvocation parent s
       | none => propertyOwnerInvocation parent s) := by
  cases parent <;>
    (simp only [propertyOwnerInvocation, ScopeCtx.owningInvocation]
     cases activation.bind (fun id => s.lexicalActivations[id]?) <;> rfl)

/-- An INVOKED level owns the chain below it: its call's binding context. -/
theorem ownerInvocation_invoked (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (id : Nat)
    (decl : Option PropertyIdentity) (s : EvalState) (act : ParameterActivation)
    (h : s.lexicalActivations[id]? = some act) (hinvoked : act.ownsInvocation = true) :
    propertyOwnerInvocation (some (.mk parent params opens props output branches (some id) decl)) s =
      some act.bindingContext := by
  rw [ownerInvocation_level]
  simp only [Option.bind_some, h, hinvoked, ite_true]

/-- A level a property-style READ activated owns nothing: the search continues above it. -/
theorem ownerInvocation_read_level (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (id : Nat)
    (decl : Option PropertyIdentity) (s : EvalState) (act : ParameterActivation)
    (h : s.lexicalActivations[id]? = some act) (hread : act.ownsInvocation = false) :
    propertyOwnerInvocation (some (.mk parent params opens props output branches (some id) decl)) s =
      propertyOwnerInvocation parent s := by
  rw [ownerInvocation_level]
  simp only [Option.bind_some, h, hread, Bool.false_eq_true, ite_false]

/-- An unactivated level is skipped. -/
theorem ownerInvocation_unactivated (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch)
    (decl : Option PropertyIdentity) (s : EvalState) :
    propertyOwnerInvocation (some (.mk parent params opens props output branches none decl)) s =
      propertyOwnerInvocation parent s := by
  rw [ownerInvocation_level]
  simp only [Option.bind_none]

/-- **A static chain is run-scoped.** A declaring chain no level of which is activated — the root,
    a module, a host scope, an owner reached by navigation from outside its call — has NO owning
    invocation, in every state: its bindings are the run-scoped ones, independent of every
    activation recorded before or after. -/
theorem ownerInvocation_static : ∀ (chain : Option ScopeCtx) (s : EvalState),
    nearestActivation? chain = none → propertyOwnerInvocation chain s = none
  | none, _, _ => rfl
  | some (.mk parent _ _ _ _ _ activation _), s, h => by
      cases activation with
      | some id => simp only [nearestActivation?] at h; cases h
      | none =>
        simp only [nearestActivation?] at h
        rw [ownerInvocation_level]
        simp only [Option.bind_none]
        exact ownerInvocation_static parent s h

/-- The owning-invocation search of `propertyOwnerInvocation` over a chain stays inside the
    activation array: every ACTIVATED level it visits names an existing record, down to the first
    level whose record owns an invocation (where the search stops) or to the root. Unlike the owner
    CONTEXT search (`OwnerContextStability.OwnerSearchValid`), this one walks past a level a
    property-style read activated, so those levels must exist too. It rules out a dangling level,
    the one thing a later append can turn from "skipped" into "selected". -/
def InvocationSearchValid : Option ScopeCtx → EvalState → Prop
  | none, _ => True
  | some (.mk parent _ _ _ _ _ activation _), s =>
      match activation with
      | some id => ∃ act, s.lexicalActivations[id]? = some act ∧
          (act.ownsInvocation = true ∨ InvocationSearchValid parent s)
      | none => InvocationSearchValid parent s

theorem InvocationSearchValid.mono {s t : EvalState} (h : ActivationPrefix s t) :
    ∀ {chain : Option ScopeCtx}, InvocationSearchValid chain s → InvocationSearchValid chain t
  | none, _ => by simp only [InvocationSearchValid]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      cases activation with
      | some id =>
        simp only [InvocationSearchValid] at hv ⊢
        obtain ⟨act, hact, hrest⟩ := hv
        have hid : id < s.lexicalActivations.size := (Array.getElem?_eq_some_iff.1 hact).1
        refine ⟨act, (h.lookup hid).trans hact, ?_⟩
        rcases hrest with hown | hvalid
        · exact Or.inl hown
        · exact Or.inr (InvocationSearchValid.mono h (chain := parent) hvalid)
      | none =>
        simp only [InvocationSearchValid] at hv ⊢
        exact InvocationSearchValid.mono h (chain := parent) hv

/-- **The owning invocation is stable.** Over a chain whose owning-invocation search is valid,
    every extension of the activation array answers the same owning invocation: what ran between
    two reads of one declaring chain cannot move the binding to another lifetime. -/
theorem ownerInvocation_stable {s t : EvalState} (h : ActivationPrefix s t) :
    ∀ {chain : Option ScopeCtx}, InvocationSearchValid chain s →
      propertyOwnerInvocation chain t = propertyOwnerInvocation chain s
  | none, _ => rfl
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      cases activation with
      | some id =>
        simp only [InvocationSearchValid] at hv
        obtain ⟨act, hact, hrest⟩ := hv
        have hid : id < s.lexicalActivations.size := (Array.getElem?_eq_some_iff.1 hact).1
        rw [ownerInvocation_level, ownerInvocation_level]
        simp only [Option.bind_some, h.lookup hid, hact]
        cases hown : act.ownsInvocation with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          rcases hrest with htrue | hvalid
          · rw [hown] at htrue; cases htrue
          · exact ownerInvocation_stable h (chain := parent) hvalid
      | none =>
        simp only [InvocationSearchValid] at hv
        rw [ownerInvocation_level, ownerInvocation_level]
        simp only [Option.bind_none]
        exact ownerInvocation_stable h (chain := parent) hv

/-- A static chain's search is valid vacuously, in every state. -/
theorem static_chain_valid : ∀ (chain : Option ScopeCtx) (s : EvalState),
    nearestActivation? chain = none → InvocationSearchValid chain s
  | none, _, _ => by simp only [InvocationSearchValid]
  | some (.mk parent _ _ _ _ _ activation _), s, h => by
      cases activation with
      | some id => simp only [nearestActivation?] at h; cases h
      | none =>
        simp only [nearestActivation?] at h
        simp only [InvocationSearchValid]
        exact static_chain_valid parent s h

/-- **A call owns the chain below its entry.** The head scope an entry made under the invocation
    mark installs has a valid search in the entered state, with NO premise on the incoming chain,
    and its owning invocation is the call's own binding context. -/
theorem invoked_entry_owns_its_scope (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (h : ctx.enteringInvocation = true) :
    InvocationSearchValid (some (enteredScope a s)) (enteredState a ctx env s) ∧
    propertyOwnerInvocation (some (enteredScope a s)) (enteredState a ctx env s) = some ctx.bindingContext := by
  have hrecord := entered_record a ctx env s (entryRecords_of_invocation a h)
  have hown : (enteredActivation a ctx env).ownsInvocation = true := h
  constructor
  · show InvocationSearchValid (some (a.asScopeCtx.withActivation s.lexicalActivations.size)) _
    cases hscope : a.asScopeCtx with
    | mk parent params opens props output branches activation decl =>
      simp only [ScopeCtx.withActivation, InvocationSearchValid]
      exact ⟨_, hrecord, Or.inl hown⟩
  · show propertyOwnerInvocation (some (a.asScopeCtx.withActivation s.lexicalActivations.size)) _ = _
    cases hscope : a.asScopeCtx with
    | mk parent params opens props output branches activation decl =>
      simp only [ScopeCtx.withActivation]
      exact ownerInvocation_invoked parent params opens props output branches _ decl _ _ hrecord hown

/-- **A read-owned level owns nothing.** After a read-owned entry of `a`, the recording entry's
    level and the unactivated level a structural `B.V` or an opened `V` rebuilds over the SAME
    declaring chain have the same owning invocation — the chain's: a property-style read gives the
    bindings below it no new lifetime, whichever spelling reaches them. -/
theorem read_entry_invocations_agree (a : Algorithm) (boundCtx ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hrec : recordsActivation a = true)
    (params : List Ident) (opens : List Expr) (props : List PropDef) (output : List Expr)
    (branches : List CondBranch) (decl : Option PropertyIdentity) :
    propertyOwnerInvocation (some (enteredScope a s))
        (enteredState a { boundCtx with bindingContext := KatLang.PropertyOwnerContext.inheritedContext a ctx s,
                                        enteringInvocation := false } env s) =
      propertyOwnerInvocation (some (.mk a.parent params opens props output branches none decl))
        (enteredState a { boundCtx with bindingContext := KatLang.PropertyOwnerContext.inheritedContext a ctx s,
                                        enteringInvocation := false } env s) :=
  (ownerInvocation_read_level a.parent a.params a.opens a.props a.output a.branches _ a.declarationId _ _
      (entered_record a _ env s (entryRecords_of_records _ hrec)) rfl).trans
    (ownerInvocation_unactivated a.parent params opens props output branches decl _).symm

/-- **A selected clause is a call of its family.** The family level a selected clause is wired
    under (`wireSelectedBranchBody`) owns the chain below it: its search is valid in the activation's
    exit state and its owning invocation is the FRESH binding context of this activation. -/
theorem family_activation_owns_its_scope (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) (s : EvalState) :
    InvocationSearchValid (some (familyScope callee (bindings.map Prod.fst) s.lexicalActivations.size))
      (runEval (needActivateBranch callee ctx env branch bindings) s).2 ∧
    propertyOwnerInvocation (some (familyScope callee (bindings.map Prod.fst) s.lexicalActivations.size))
      (runEval (needActivateBranch callee ctx env branch bindings) s).2 = some s.nextBindingContext := by
  rw [KatLang.FamilyDispatch.activation_run]
  unfold familyScope
  have hrecord := pushed_record (s := s)
    (t := { s with
      nextBindingContext := s.nextBindingContext + 1,
      lexicalActivations := s.lexicalActivations.push
        { values := (ValEnv.shadow env (bindings.map Prod.fst)).filter
            (fun entry => (bindings.map Prod.fst).contains entry.fst)
          needs := (KatLang.FamilyDispatch.activatedContext callee ctx bindings s.nextBindingContext).needEnv.filter
            (fun entry => (bindings.map Prod.fst).contains entry.fst)
          bindingContext := s.nextBindingContext
          ownsInvocation := true } }) rfl
  constructor
  · simp only [InvocationSearchValid]
    exact ⟨_, hrecord, Or.inl rfl⟩
  · exact ownerInvocation_invoked _ _ _ _ _ _ _ _ _ _ hrecord rfl

/-! ## 3. The key -/

/-- An exported binding's key carries exactly the owning invocation. -/
theorem exported_key_bindingContext (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (ownerContext ownerInvocation : Option Nat)
    (h : binding.exposure.isExported = true) :
    (zeroArgPropertyCacheKey k owner binding ctx env ownerContext ownerInvocation).bindingContext =
      ownerInvocation := by
  simp only [zeroArgPropertyCacheKey, propertyKeyBindingContext, h, ite_true]

/-- An exported binding's key carries no value environment. -/
theorem exported_key_has_no_valEnv (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (ownerContext ownerInvocation : Option Nat)
    (h : binding.exposure.isExported = true) :
    (zeroArgPropertyCacheKey k owner binding ctx env ownerContext ownerInvocation).valEnv = none := by
  simp only [zeroArgPropertyCacheKey, h, Bool.true_or, ite_true]

/-- **No consumer gives a binding another lifetime.** The key of an exported binding is decided by
    its owner, the binding and the owning invocation alone: the reader's context, its value
    environment, its access kind and the declaring binding context take no part. A callback, a
    helper, an open or a referring caller that resolves the same binding under the same owning
    invocation computes the SAME key. -/
theorem exported_key_ignores_the_reader (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (ctx ctx' : EvalCtx) (env env' : ValEnv) (ownerContext ownerContext' : Option Nat)
    (ownerInvocation : Option Nat) (h : binding.exposure.isExported = true) :
    zeroArgPropertyCacheKey k owner binding ctx env ownerContext ownerInvocation =
      zeroArgPropertyCacheKey k' owner binding ctx' env' ownerContext' ownerInvocation := by
  simp only [zeroArgPropertyCacheKey, propertyKeyBindingContext, h, Bool.true_or, ite_true]

/-- **Every call has fresh bindings.** Two different owning invocations give two different keys of
    the same exported binding, so neither call can read or replace the other's entry. -/
theorem exported_keys_of_distinct_invocations_differ (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (ctx ctx' : EvalCtx) (env env' : ValEnv) (ownerContext ownerContext' : Option Nat)
    (invocation invocation' : Option Nat) (h : binding.exposure.isExported = true)
    (hne : invocation ≠ invocation') :
    zeroArgPropertyCacheKey k owner binding ctx env ownerContext invocation ≠
      zeroArgPropertyCacheKey k owner binding ctx' env' ownerContext' invocation' := by
  intro heq
  have hb := congrArg ZeroArgPropertyCacheKey.bindingContext heq
  rw [exported_key_bindingContext k owner binding ctx env ownerContext invocation h,
    exported_key_bindingContext k owner binding ctx' env' ownerContext' invocation' h] at hb
  exact hne hb

/-- The key a call owns is never the run-scoped key of the same binding: the outside entry is
    independent of every activation of the owner. -/
theorem call_key_is_not_the_run_scoped_key (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (ctx ctx' : EvalCtx) (env env' : ValEnv) (ownerContext ownerContext' : Option Nat)
    (call : Nat) (h : binding.exposure.isExported = true) :
    zeroArgPropertyCacheKey k owner binding ctx env ownerContext (some call) ≠
      zeroArgPropertyCacheKey k owner binding ctx' env' ownerContext' none :=
  exported_keys_of_distinct_invocations_differ k owner binding ctx ctx' env env' ownerContext ownerContext'
    (some call) none h (by intro e; cases e)

/-- A local-only binding's key is the former one: the owning invocation takes no part in it. -/
theorem local_only_key_unchanged (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (ownerContext : Option Nat) (invocation invocation' : Option Nat)
    (h : binding.exposure.isExported = false) :
    zeroArgPropertyCacheKey k owner binding ctx env ownerContext invocation =
      zeroArgPropertyCacheKey k owner binding ctx env ownerContext invocation' := by
  simp only [zeroArgPropertyCacheKey, propertyKeyBindingContext, h, Bool.false_eq_true, ite_false]

/-- **One invocation, one entry (the production theorem).** Let the declaring chain of `resolved`
    have a valid owning-invocation search at `s`, and let the cache hold `v` for this owner and
    EXPORTED binding under that chain's owning invocation. After ANY production operation from `s`
    — its actual exit state, whatever its outcome, whatever nested calls, activations and
    publications it made — a cacheable READ of that binding through the same declaring chain, in
    ANY consumer context and environment, returns `v` and leaves the state unchanged: no callback,
    helper, open or referring caller evaluates it again. Reads only: an explicit invocation stays
    fresh. -/
theorem exported_entry_reused_after_production (c : EvalCall) (k k' : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (hexp : binding.exposure.isExported = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (oc : Option Nat) (s : EvalState) (v : CountedResult)
    (hvalid : InvocationSearchValid resolved.parent s)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ oc (propertyOwnerInvocation resolved.parent s)) = some v)
    (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState
        ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) :=
  exported_publication_reused k k' owner binding hexp resolved hcache ctx₀ env₀ oc _ s _ v hentry
    (production_retained c s).2 ctx env (ownerInvocation_stable (production_retained c s).1 hvalid)

/-- **Another call never reads it.** An entry published for one owning invocation is not the key a
    read through a chain owned by ANOTHER invocation looks up — in particular a later call of the
    same owner, and the run-scoped read from outside every call. -/
theorem other_invocation_reads_another_key (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (hexp : binding.exposure.isExported = true)
    (ctx ctx' : EvalCtx) (env env' : ValEnv) (oc oc' : Option Nat) (invocation invocation' : Option Nat)
    (hne : invocation ≠ invocation') :
    zeroArgPropertyCacheKey k owner binding ctx env oc invocation ≠
      zeroArgPropertyCacheKey k' owner binding ctx' env' oc' invocation' := by
  rw [exported_key_ignores_the_reader k' k owner binding ctx' ctx env' env oc' oc invocation' hexp]
  exact exported_keys_of_distinct_invocations_differ k owner binding ctx ctx env env oc oc
    invocation invocation' hexp hne

/-! ## 4. Alias cells -/

/-- An EXPORTED alias's binding cell is keyed by the owning invocation of its declaring chain: one
    cell per call of its owner, and one run-scoped cell where no call owns the chain. -/
theorem aliasCell_exported_follows_the_owning_invocation (wired : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (h : aliasCellIsExported wired = true) :
    aliasCellBindingContext wired ctx s = propertyOwnerInvocation wired.parent s := by
  simp only [aliasCellBindingContext, propertyKeyBindingContext, h, ite_true]

/-- A local-only alias's binding cell is keyed as before, by its declaring binding context. -/
theorem aliasCell_local_only_unchanged (wired : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (h : aliasCellIsExported wired = false) :
    aliasCellBindingContext wired ctx s =
      some ((propertyOwnerBindingContext wired.parent s).getD ctx.bindingContext) := by
  simp only [aliasCellBindingContext, propertyKeyBindingContext, h, Bool.false_eq_true, ite_false]

end KatLang.InnerPropertyLifetime
