import KatLangArityLaws.AlgorithmProjection
import KatLangArityLaws.CallableIdentityProvenance
import KatLangArityLaws.InnerPropertyLifetime
import KatLangArityLaws.OwnerContextStability
import KatLangArityLaws.TotalLeaves

open KatLang KatLang.CallPlan KatLang.AlgorithmProjectionLaws

/-! R7 checkpoint: alias recursion goes through the total `EvalBody`/`evalFuel` core and its
production fuel search, and the installation this header describes is a body equation of that core
(`EvaluatorInstallation.alias_chase_installs`, `alias_value_installs`).
`EvaluatorCore.production_unfolds` covers completed operations; reachable alias
bindings and end-to-end alias refinement remain open. (M4★, ALIAS-UNIFY-1,
October 2026, retired D4's first-observation claims and FWD-02's runtime eligibility gate; the
whole-algorithm transport laws are `WholeAlgorithmTransport.lean`. ALIAS-CELL-LIFETIME, November
2026, replaced the activation-keyed cell by the property-lifetime key `aliasBindingCellKey`.) -/

/-!
# META-S3-2: runtime-target callable aliases (October 2026)

A RUNTIME-TARGET ALIAS (FWD-02; owner decisions D1 = yes, D2 = Option A, D3 = fresh invocation; L-RUN,
M4★) is an `Algorithm.alias` whose row is a RUNTIME ROW (`Expr.isRuntimeAliasRow`): a parameter
reference, an argumentless `.Algorithm` link, or an argumentless parameter-rooted member path. Its
STRUCTURE and its INVOCATION target are the identity its ONE binding cell projects, at ANY arity (no
eligibility gate); a cell that projects NO identity makes it a VALUE VIEW
(`Algorithm.aliasPropertyView`): no members, no CALLABLE, a zero-supply invocation returns the binding
cell's VALUE (`valueViewCell?`) and a non-empty supply is the binder's cardinality failure. Its bare
read is the binding cell's VALUE (`aliasValue`). The authoritative definitions are in `lean/KatLang.lean`:

* `aliasBindingCell` — the binding cell, supplied in the alias's own declaring context through the one
  supplier (`supplyNeed`) and recorded in `EvalState.aliasCells` under `aliasBindingCellKey`: the
  alias's declaration, the structure of its declaring scope chain (`aliasBindingCellScopeKey`) and the
  binding-context component a property-style read of the alias's own property would carry
  (`aliasCellBindingContext` = `propertyKeyBindingContext`, the function `zeroArgPropertyCacheKey`
  uses) — PROPERTY LIFETIME (ALIAS-CELL-LIFETIME, owner decision 2026-11-15);
* `runtimeAliasStepWith` — one runtime step of the chase over a CALLABLE capability;
* `Algorithm.aliasPropertyView` and `valueViewCell?` — the value view and the cell its invocation reads.

The evaluator core installs them: `resolveAliasChase` takes the runtime step as
`runtimeAliasStepWith projectNeedCallable` when `aliasStepIsRuntime` holds; the VALUE chase stops at the
runtime alias, whose bare read `aliasValue` demands the SAME binding cell. That installation is a theorem
(`EvaluatorInstallation.alias_chase_installs`, `alias_value_installs`), and executable guards run whole
programs through it (`RuntimeAliasGuards.lean`, the `runtime-alias-*` LanguageSpec cases, and
`CoreTests/AliasForwarding`).

Proved here, over the total definitions:

* the binding cell is CANONICAL PER KEY (`aliasBindingCellKey`): a recorded key is read
  (`aliasBindingCell_recorded`), and once a use established or read a cell, EVERY use whose key is that
  key — the same wiring again (`aliasBindingCell_canonical`, on a declaring chain whose searches are
  valid) or another wiring, context or route (`aliasBindingCell_shared`) — returns the same cell and
  changes nothing: the bare VALUE and every CALLABLE projection alike. Its establishment is INERT
  (`aliasBindingCell_inert`: every existing cell keeps its suspension, VALUE state, CALLABLE state and
  plan supply), and a PARAMETER row is that parameter's own cell, allocating nothing
  (`aliasBindingCell_parameter_transport`, NEED-01);
* THE KEY HAS ITS PROPERTY'S LIFETIME, with the alias's exposure as an INPUT (the front end's
  classification, read from the alias's own property, `aliasOwnProperty?`; nothing here concerns how
  it is inferred): its binding-context component is the property cache key's own
  (`aliasCellBindingContext_is_the_property_key_component`); two uses whose declaring chains have the
  same owner binding context and the same structural scope have ONE key
  (`aliasBindingCellKey_agree`, read/structural agreement; at a property-style read of the owner,
  `aliasBindingCellKey_read_entry`: the alias wired under the read-entered head scope and under the
  owner's unactivated scope), hence one cell (`aliasBindingCell_agree`); an EXPORTED alias's key is
  the structural scope key and the OWNING INVOCATION of its declaring chain, in every access context
  (`aliasBindingCellKey_exported`; the inner-property lifetime rule, November 2026): one key per
  owning invocation (`aliasBindingCellKey_exported_same_invocation`) and one run-scoped key where no
  actual call entered the chain (`aliasBindingCellKey_exported_run_scoped`); the scope key reads no
  activation at any depth (`aliasBindingCellScopeKey_declaration`,
  `aliasBindingCellScopeKey_withActivation`); the key is stable under every activation-prefix
  extension of a valid chain (`aliasBindingCellKey_stable`);
* one runtime step keeps FAILURE apart from ABSENCE: a projection failure propagates with its error
  (`runtimeAliasStep_failure_propagates`), as does a failure to establish the cell
  (`runtimeAliasStep_cell_failure_propagates`), absence ends the chase as the value view
  (`runtimeAliasStep_absence_is_terminal`) and a supplied identity is passed on unchanged, whatever its
  arity (`runtimeAliasStep_identity`);
* the value view is never the unresolved alias again — no alias-to-self redispatch
  (`aliasPropertyView_is_the_open_body`, `aliasPropertyView_is_no_alias`), it takes no supply
  (`aliasPropertyView_takes_no_supply`), and its zero-supply invocation reads EXACTLY the alias's binding
  cell (`valueView_reads_the_binding_cell`, `valueViewCell_reads_only`): the supplied computation never
  reruns;
* a runtime reference is its own (empty) open namespace (`runtime_reference_opens_itself`);
* the row classification (`runtime_rows`, `static_name_is_no_runtime_row`).

NOT claimed here (open statements about whole evaluations with executable guards, or C#-only): that a
call through the alias is the identity's FRESH call with exactly the written
new supply (D3) and that a chain or cycle behaves as the guards show — properties of whole chases on
reachable bindings, beyond the one-step equation above; the C# front end's Option A
classification and Q-75 inference (front-end facts, FORMAL-02: no theorem here concerns inference);
C# concurrency, first-wins establishment, the CALLABLE single flight, Guard B, run pre-marking,
asynchronous resolution and cancellation (C#-only, `RuntimeCallableAliasMechanismTests`); that the C#
cell store (`ZeroArgPropertyCacheKey.ForAliasBindingCell`, the identity-partitioned
`EvaluationBudget.AliasBindingCells`) realizes this key — the C# differential
(`RuntimeAliasCellLifetimeTests`, the spec cases); that a reachable production state gives the
premises of the agreement laws (which chain `scopeInContext` selects is guard-pinned, ledger E-12);
and anything about re-entrancy beyond the cell's own `demandCycle` (a property's Q-37 re-entrant read
is deliberately not an alias's).
-/

namespace KatLang.RuntimeAliasLaws

/-! ## The runtime rows -/

theorem runtime_rows (x : Ident) (receiver fallback : Expr) (member : Ident) :
    (Expr.param x).isRuntimeAliasRow = true
      ∧ (Expr.dotMember receiver "Algorithm" fallback none).isRuntimeAliasRow = true
      ∧ (Expr.dotMember (.param x) member fallback none).isRuntimeAliasRow = true := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [Expr.isRuntimeAliasRow, Expr.isParamHeaded]

/-- A static name is never a runtime row: a chain link takes the ordinary static step. -/
theorem static_name_is_no_runtime_row (n : Ident) : (Expr.resolve n).isRuntimeAliasRow = false := rfl

/-! ## The binding cell -/

/-- A non-parameter row's binding cell is its RECORDED cell (`aliasBindingCellRecorded`). -/
theorem aliasBindingCell_nonparameter (wired : Algorithm) (target : Expr) (ctx : EvalCtx)
    (hnp : ∀ n, target ≠ .param n) :
    aliasBindingCell wired target ctx = aliasBindingCellRecorded wired target ctx := by
  cases target <;> first | exact absurd rfl (hnp _) | rfl

/-! ### The key (ALIAS-CELL-LIFETIME: property lifetime) -/

/-- The structural owner used by the cell key is the property cache's own owner component,
    including its declaration even for distinct owners that share their property list. -/
theorem propertyKeyOwner_is_the_property_cache_owner (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (property : PropDef) (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat) :
    (zeroArgPropertyCacheKey k owner property ctx env obc).owner = propertyKeyOwner owner.asScopeCtx := rfl

/-- The key reads the state ONLY through the two searches of the declaring chain — the owner
    context (`propertyOwnerBindingContext`) and the owning invocation (`propertyOwnerInvocation`):
    no activation index, no cell, no cache entry. -/
theorem aliasBindingCellKey_of_owner_context (wired : Algorithm) (ctx : EvalCtx) (s t : EvalState)
    (h : propertyOwnerBindingContext wired.parent t = propertyOwnerBindingContext wired.parent s)
    (hi : propertyOwnerInvocation wired.parent t = propertyOwnerInvocation wired.parent s) :
    aliasBindingCellKey wired ctx t = aliasBindingCellKey wired ctx s := by
  simp only [aliasBindingCellKey, aliasCellBindingContext, h, hi]

/-- **The key is stable on a valid chain**: every activation-prefix extension of a state in which
    the declaring chain's two searches are valid (`OwnerSearchValid`, `InvocationSearchValid`: no
    dangling level a search could later select) computes the same key. Production only appends
    activations (`OwnerContextStability.activations_kept`). -/
theorem aliasBindingCellKey_stable (wired : Algorithm) (ctx : EvalCtx) {s t : EvalState}
    (hp : KatLang.OwnerContextStability.ActivationPrefix s t)
    (hv : KatLang.OwnerContextStability.OwnerSearchValid wired.parent s)
    (hi : KatLang.InnerPropertyLifetime.InvocationSearchValid wired.parent s) :
    aliasBindingCellKey wired ctx t = aliasBindingCellKey wired ctx s :=
  aliasBindingCellKey_of_owner_context wired ctx s t (KatLang.OwnerContextStability.owner_context_stable hp hv)
    (KatLang.InnerPropertyLifetime.ownerInvocation_stable hp hi)

/-- **The binding-context component IS the property key's.** For an alias that is a property of its
    declaring scope, the context component of its cell key is the `bindingContext` field of the
    zero-argument cache key of that property (`zeroArgPropertyCacheKey`), read with the declaring
    chain's owner context and owning invocation: the two lifetimes come from one function and
    cannot drift. -/
theorem aliasCellBindingContext_is_the_property_key_component (wired : Algorithm) (property : PropDef)
    (hown : aliasOwnProperty? wired = some property) (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    aliasCellBindingContext wired ctx s =
      (zeroArgPropertyCacheKey k owner property ctx env (propertyOwnerBindingContext wired.parent s)
        (propertyOwnerInvocation wired.parent s)).bindingContext := by
  unfold aliasCellBindingContext aliasCellIsExported
  rw [hown]
  rfl

/-- **(b) An exported alias's key carries its OWNING INVOCATION and nothing else of the use**: the
    structural scope key (`aliasBindingCellScopeKey`) and the owning invocation of its declaring
    chain (`propertyOwnerInvocation`; `none` where no actual call entered the chain), whatever the
    access context (the inner-property lifetime rule, November 2026). -/
theorem aliasBindingCellKey_exported (wired : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (hexp : aliasCellIsExported wired = true) :
    aliasBindingCellKey wired ctx s =
      aliasBindingCellScopeKey wired ++ "@" ++ reprStr (propertyOwnerInvocation wired.parent s) := by
  unfold aliasBindingCellKey aliasCellBindingContext propertyKeyBindingContext
  rw [hexp]
  rfl

/-- **(b) One exported cell per declaration, structural declaring scope and OWNING INVOCATION**: two
    exported wirings with one structural scope key whose declaring chains have the same owning
    invocation have one cell key in ANY two contexts — a read of the owner, a callback, a helper, an
    open and a structural path inside one call of the owner alike. Two calls of the owner have two
    owning invocations, hence two keys (`aliasBindingCellKey_exported_calls_differ`). -/
theorem aliasBindingCellKey_exported_same_invocation (wired wired' : Algorithm) (ctx ctx' : EvalCtx) (s s' : EvalState)
    (hexp : aliasCellIsExported wired = true) (hexp' : aliasCellIsExported wired' = true)
    (hscope : aliasBindingCellScopeKey wired = aliasBindingCellScopeKey wired')
    (hinv : propertyOwnerInvocation wired.parent s = propertyOwnerInvocation wired'.parent s') :
    aliasBindingCellKey wired ctx s = aliasBindingCellKey wired' ctx' s' := by
  rw [aliasBindingCellKey_exported wired ctx s hexp, aliasBindingCellKey_exported wired' ctx' s' hexp', hscope, hinv]

/-- **(b) The run-scoped cell.** Where no actual call entered either declaring chain — a root or
    module alias, a member reached from outside its owner's call — two exported wirings with one
    structural scope key have ONE key, in any two contexts and states: the one outside cell of a run. -/
theorem aliasBindingCellKey_exported_run_scoped (wired wired' : Algorithm) (ctx ctx' : EvalCtx) (s s' : EvalState)
    (hexp : aliasCellIsExported wired = true) (hexp' : aliasCellIsExported wired' = true)
    (hscope : aliasBindingCellScopeKey wired = aliasBindingCellScopeKey wired')
    (hnone : propertyOwnerInvocation wired.parent s = none)
    (hnone' : propertyOwnerInvocation wired'.parent s' = none) :
    aliasBindingCellKey wired ctx s = aliasBindingCellKey wired' ctx' s' :=
  aliasBindingCellKey_exported_same_invocation wired wired' ctx ctx' s s' hexp hexp' hscope (hnone.trans hnone'.symm)

/-- The binding-context component of an exported alias's key IS the owning invocation. -/
theorem aliasCellBindingContext_exported (wired : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (hexp : aliasCellIsExported wired = true) :
    aliasCellBindingContext wired ctx s = propertyOwnerInvocation wired.parent s :=
  KatLang.InnerPropertyLifetime.aliasCell_exported_follows_the_owning_invocation wired ctx s hexp

/-- `ScopeCtx.declaration` (the chain without its activations, at every depth) keeps host provenance. -/
theorem hostChain_declaration : ∀ scope : ScopeCtx, scope.declaration.hostChain = scope.hostChain
  | .mk none _ _ _ _ _ _ _ => rfl
  | .mk (some p) ps op pr out br act id => by
      have ih := hostChain_declaration p
      simp only [ScopeCtx.declaration, ScopeCtx.hostChain, ih]

/-- `ScopeCtx.declaration` keeps component provenance. -/
theorem componentChain_declaration : ∀ scope : ScopeCtx, scope.declaration.componentChain = scope.componentChain
  | .mk none _ _ _ _ _ _ _ => rfl
  | .mk (some p) ps op pr out br act id => by
      have ih := componentChain_declaration p
      simp only [ScopeCtx.declaration, ScopeCtx.componentChain, ih]

/-- `cacheScopeShape` reads no activation, at any depth. -/
theorem cacheScopeShape_declaration : ∀ scope : ScopeCtx, cacheScopeShape scope.declaration = cacheScopeShape scope
  | .mk none ps op pr out br act id => by
      rw [show (ScopeCtx.mk none ps op pr out br act id).declaration = .mk none ps op pr out br none id from rfl,
        KatLang.TotalLeaves.cacheScopeShape_equation (.mk none ps op pr out br none id),
        KatLang.TotalLeaves.cacheScopeShape_equation (.mk none ps op pr out br act id)]
  | .mk (some p) ps op pr out br act id => by
      have ih := cacheScopeShape_declaration p
      rw [show (ScopeCtx.mk (some p) ps op pr out br act id).declaration
            = .mk (some p.declaration) ps op pr out br none id from rfl,
        KatLang.TotalLeaves.cacheScopeShape_equation (.mk (some p.declaration) ps op pr out br none id),
        KatLang.TotalLeaves.cacheScopeShape_equation (.mk (some p) ps op pr out br act id)]
      simp only [Option.map_some, ih]

/-- **(b) The structural scope key reads no activation, at any depth**: an alias wired under a scope
    chain and under that chain with every activation erased (`ScopeCtx.declaration`) has one scope
    key. With `aliasBindingCellKey_exported`: an exported alias's cell key has no activation
    component at all. -/
theorem aliasBindingCellScopeKey_declaration (scope : ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    aliasBindingCellScopeKey (.alias (some scope.declaration) op pr target id reference) =
      aliasBindingCellScopeKey (.alias (some scope) op pr target id reference) := by
  have hown : aliasOwnProperty? (.alias (some scope.declaration) op pr target id reference) =
      aliasOwnProperty? (.alias (some scope) op pr target id reference) := by
    cases scope with
    | mk parent ps sop spr out br act sid =>
      cases parent <;> cases hd : PropertyIdentity.callableDeclaration id <;>
        simp only [aliasOwnProperty?, Algorithm.parent, Algorithm.declarationId, ScopeCtx.declaration, hd]
  simp only [aliasBindingCellScopeKey, aliasBindingCellScopeOwnerKey, hown,
    Algorithm.parent, Algorithm.declarationId, ScopeCtx.hostChainOf,
    ScopeCtx.componentChainOf, Option.map_some, hostChain_declaration, componentChain_declaration,
    propertyKeyOwner, cacheScopeShape_declaration,
    show scope.declaration.declarationId = scope.declarationId from by
      cases scope with
      | mk parent ps sop spr out br act sid => cases parent <;> rfl]

/-- The declaring level's own activation is invisible to the scope key: the head scope a body entry
    activates and the unactivated level a structural path or an `open` rebuilds are one scope. -/
theorem aliasBindingCellScopeKey_withActivation (scope : ScopeCtx) (v : Nat) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    aliasBindingCellScopeKey (.alias (some (scope.withActivation v)) op pr target id reference) =
      aliasBindingCellScopeKey (.alias (some scope) op pr target id reference) := by
  rw [← aliasBindingCellScopeKey_declaration (scope.withActivation v),
    ← aliasBindingCellScopeKey_declaration scope,
    KatLang.CallableIdentityProvenance.declaration_withActivation]

/-- The alias's own property — hence its exposure — is read from the declaring level's property list
    and declaration identities only: the level's activation is invisible to it. -/
theorem aliasCellIsExported_withActivation (scope : ScopeCtx) (v : Nat) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    aliasCellIsExported (.alias (some (scope.withActivation v)) op pr target id reference) =
      aliasCellIsExported (.alias (some scope) op pr target id reference) := by
  cases scope with
  | mk p ps sop spr out br act sid =>
    cases hd : PropertyIdentity.callableDeclaration id <;>
      simp only [aliasCellIsExported, aliasOwnProperty?, Algorithm.parent, Algorithm.declarationId,
        ScopeCtx.withActivation, hd]

/-- **(a) Read/structural agreement.** Two uses of an alias — two wirings, in two contexts — whose
    declaring chains have the same structural scope (`aliasBindingCellScopeKey`), the same exposure,
    the same owner binding context (`propertyOwnerBindingContext`) and the same owning invocation
    (`propertyOwnerInvocation`) have ONE cell key. On a chain
    with an activated level the two access contexts are irrelevant; on an unactivated chain they must
    agree (the property cache's own fallback). -/
theorem aliasBindingCellKey_agree (wired wired' : Algorithm) (ctx ctx' : EvalCtx) (s : EvalState)
    (hscope : aliasBindingCellScopeKey wired = aliasBindingCellScopeKey wired')
    (hexp : aliasCellIsExported wired = aliasCellIsExported wired')
    (hctx : propertyOwnerBindingContext wired.parent s = propertyOwnerBindingContext wired'.parent s)
    (hinv : propertyOwnerInvocation wired.parent s = propertyOwnerInvocation wired'.parent s)
    (hfound : (propertyOwnerBindingContext wired.parent s).isSome = true ∨ ctx.bindingContext = ctx'.bindingContext) :
    aliasBindingCellKey wired ctx s = aliasBindingCellKey wired' ctx' s := by
  unfold aliasBindingCellKey aliasCellBindingContext propertyKeyBindingContext
  rw [hscope, hexp, ← hctx, ← hinv]
  cases aliasCellIsExported wired' with
  | true => rfl
  | false =>
    rcases hfound with hsome | hsame
    · cases hown : propertyOwnerBindingContext wired.parent s with
      | none => rw [hown] at hsome; cases hsome
      | some n => rfl
    · rw [hsame]

/-- **(a), at a property-style read (CACHE-OWNER-D1, COLLECT-CACHE-1).** After a read-owned entry of
    the owner `a` (`enterPropertyOwnerBody` with the inherited context, on a declaring chain that
    retains a context `m`), a member alias of `a` wired under the ENTERED head scope and the same
    alias wired under `a`'s UNACTIVATED scope — a structural `B.A`, an opened `A`, a lexical read in a
    body entered without a record — have ONE cell key, in any two access contexts. The read's fresh
    activation neither splits the cell (the former defect: a cell per minted activation) nor merges
    two declaring contexts. -/
theorem aliasBindingCellKey_read_entry (a : Algorithm) (boundCtx ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    {m : Nat} (hrec : KatLang.WhileRoundProduction.recordsActivation a = true)
    (hr : KatLang.OwnerContextStability.RetainedAt a.parent s m)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool)
    (use use' : EvalCtx) :
    aliasBindingCellKey (.alias (some (KatLang.OwnerContextStability.enteredScope a s)) op pr target id reference) use
        (KatLang.WhileRoundProduction.enteredState a
          { boundCtx with bindingContext := KatLang.PropertyOwnerContext.inheritedContext a ctx s,
                          enteringInvocation := false } env s) =
      aliasBindingCellKey (.alias (some a.asScopeCtx) op pr target id reference) use'
        (KatLang.WhileRoundProduction.enteredState a
          { boundCtx with bindingContext := KatLang.PropertyOwnerContext.inheritedContext a ctx s,
                          enteringInvocation := false } env s) := by
  have hsite := KatLang.OwnerContextStability.property_entry_retains_declaring_context a boundCtx ctx env s hr
  simp only [KatLang.OwnerContextStability.enteredSite,
    KatLang.WhileRoundProduction.entryRecords_of_records _ hrec, ite_true] at hsite
  apply aliasBindingCellKey_agree
  · exact aliasBindingCellScopeKey_withActivation a.asScopeCtx _ op pr target id reference
  · exact aliasCellIsExported_withActivation a.asScopeCtx _ op pr target id reference
  · exact KatLang.OwnerContextStability.read_entry_levels_agree a boundCtx ctx env s hrec hr
      a.params a.opens a.props a.output a.branches a.declarationId
  · exact KatLang.InnerPropertyLifetime.read_entry_invocations_agree a boundCtx ctx env s hrec
      a.params a.opens a.props a.output a.branches a.declarationId
  · left
    show (propertyOwnerBindingContext (some (KatLang.OwnerContextStability.enteredScope a s)) _).isSome = true
    rw [hsite.context]
    rfl

/-! ### The recorded cell -/

/-- A recorded binding cell is read: nothing is supplied, allocated, entered or written. -/
theorem aliasBindingCell_recorded (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : lookupAssoc (aliasBindingCellKey wired ctx s) s.aliasCells = some a) :
    (aliasBindingCell wired target ctx).runState s = (.ok a, s) := by
  rw [aliasBindingCell_nonparameter wired target ctx hnp]
  simp only [aliasBindingCellRecorded, bind_run, get_run, h]
  rfl

/-- Entering an alias body succeeds and never touches the cell heap or the binding-cell record; it
    only appends to the activation array. -/
theorem enterAlgorithmBody_keeps_cells (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ∃ c t, (enterAlgorithmBody a ctx env).runState s = (.ok c, t)
      ∧ t.needs = s.needs ∧ t.aliasCells = s.aliasCells
      ∧ KatLang.OwnerContextStability.ActivationPrefix s t := by
  unfold enterAlgorithmBody recordParameterActivation
  split
  · exact ⟨_, _, rfl, rfl, rfl, KatLang.OwnerContextStability.ActivationPrefix.refl s⟩
  · exact ⟨_, _, rfl, rfl, rfl, KatLang.OwnerContextStability.ActivationPrefix.push s _⟩

/-- The first use of a non-parameter row's binding cell: the row supplied in the entered body context,
    MARKED with the new cell (`EvalCtx.inputRecord`: the cell is the next address), the cell's INPUT
    RECORD opened under the activations recorded when the use started (ledger R-1), and the cell
    recorded under the alias's key (read in the state the use started from). -/
theorem aliasBindingCell_establishes (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState)
    (hnp : ∀ n, target ≠ .param n)
    (hl : lookupAssoc (aliasBindingCellKey wired ctx s) s.aliasCells = none) :
    ∃ c u, (enterAlgorithmBody wired (aliasCellContext wired ctx s) []).runState s = (.ok c, u)
      ∧ u.needs = s.needs ∧ u.aliasCells = s.aliasCells
      ∧ KatLang.OwnerContextStability.ActivationPrefix s u
      ∧ (aliasBindingCell wired target ctx).runState s =
          (.ok u.needs.size, { u with
            needs := u.needs.push { suspension := .expression target { c with inputRecord := some u.needs.size } [] },
            cellInputs := { u.cellInputs with records :=
              (u.needs.size, { watermark := s.lexicalActivations.size, refusal := aliasReuseRefusal wired }) ::
                u.cellInputs.records },
            aliasCells := (aliasBindingCellKey wired ctx s, u.needs.size) :: u.aliasCells }) := by
  obtain ⟨c, u, he, hneeds, hcells, hprefix⟩ := enterAlgorithmBody_keeps_cells wired (aliasCellContext wired ctx s) [] s
  refine ⟨c, u, he, hneeds, hcells, hprefix, ?_⟩
  rw [aliasBindingCell_nonparameter wired target ctx hnp]
  simp only [aliasBindingCellRecorded, bind_run, get_run, hl, he,
    KatLang.NeedControl.Allocation.supply_nonparameter target { c with inputRecord := some u.needs.size } [] u hnp,
    recordCellInputs, cellInputsStep_run, modify_run]
  rfl

/-- **One cell per key.** Whatever cell a successful use of a runtime alias's binding cell returns,
    ANY use whose key in the resulting state is that use's key — another wiring of the alias, another
    context, another route — returns the SAME cell from the resulting state and changes nothing. With
    `aliasBindingCellKey_agree` this is the read/structural agreement of cells; with
    `aliasBindingCellKey_exported_same_invocation`, the one exported cell of an owning invocation. -/
theorem aliasBindingCell_shared (wired wired' : Algorithm) (target : Expr) (ctx ctx' : EvalCtx)
    (s t : EvalState) (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t))
    (hkey : aliasBindingCellKey wired' ctx' t = aliasBindingCellKey wired ctx s) :
    (aliasBindingCell wired' target ctx').runState t = (.ok a, t) := by
  cases hl : lookupAssoc (aliasBindingCellKey wired ctx s) s.aliasCells with
  | some a0 =>
    rw [aliasBindingCell_recorded wired target ctx s a0 hnp hl] at h
    cases h
    exact aliasBindingCell_recorded wired' target ctx' s _ hnp (hkey ▸ hl)
  | none =>
    obtain ⟨c, u, _, _, _, _, hrun⟩ := aliasBindingCell_establishes wired target ctx s hnp hl
    rw [hrun] at h
    cases h
    apply aliasBindingCell_recorded wired' target ctx' _ _ hnp
    rw [hkey]
    simp [lookupAssoc]

/-- A successful use of a binding cell only appends to the activation array. -/
theorem aliasBindingCell_run_extends (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s t : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t)) :
    KatLang.OwnerContextStability.ActivationPrefix s t := by
  cases hl : lookupAssoc (aliasBindingCellKey wired ctx s) s.aliasCells with
  | some a0 =>
    rw [aliasBindingCell_recorded wired target ctx s a0 hnp hl] at h
    cases h
    exact KatLang.OwnerContextStability.ActivationPrefix.refl s
  | none =>
    obtain ⟨c, u, _, _, _, hprefix, hrun⟩ := aliasBindingCell_establishes wired target ctx s hnp hl
    rw [hrun] at h
    cases h
    exact hprefix.trans (KatLang.OwnerContextStability.ActivationPrefix.of_eq rfl)

/-- **Canonical binding cell.** Whatever cell the first successful use of a runtime alias's binding
    cell returns, using it again from the resulting state — for the bare VALUE or for any CALLABLE
    projection — returns the SAME cell and changes nothing: one binding cell per key
    (`aliasBindingCellKey`: the declaration, the structural declaring scope and the property-lifetime
    binding context — never an activation index). The premises are the validity of the declaring
    chain's two searches at the first use (`OwnerSearchValid`, `InvocationSearchValid`; a synthetic
    dangling level is the one thing an append could re-key,
    `OwnerContextStability.dangling_reference_breaks_stability`). A parameter row
    is its parameter's own cell instead (`aliasBindingCell_parameter_transport`). -/
theorem aliasBindingCell_canonical (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s t : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (hv : KatLang.OwnerContextStability.OwnerSearchValid wired.parent s)
    (hi : KatLang.InnerPropertyLifetime.InvocationSearchValid wired.parent s)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t)) :
    (aliasBindingCell wired target ctx).runState t = (.ok a, t) :=
  aliasBindingCell_shared wired wired target ctx ctx s t a hnp h
    (aliasBindingCellKey_stable wired ctx (aliasBindingCell_run_extends wired target ctx s t a hnp h) hv hi)

/-- An exported alias needs only its owning-invocation search: its key reads nothing else of the state. -/
theorem aliasBindingCell_canonical_exported (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s t : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n) (hexp : aliasCellIsExported wired = true)
    (hi : KatLang.InnerPropertyLifetime.InvocationSearchValid wired.parent s)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t)) :
    (aliasBindingCell wired target ctx).runState t = (.ok a, t) :=
  aliasBindingCell_shared wired wired target ctx ctx s t a hnp h
    (aliasBindingCellKey_exported_same_invocation wired wired ctx ctx t s hexp hexp rfl
      (KatLang.InnerPropertyLifetime.ownerInvocation_stable
        (aliasBindingCell_run_extends wired target ctx s t a hnp h) hi))

/-- **(a) Read/structural agreement of CELLS.** After one use established or read the cell, a second
    use — another wiring, another context — whose declaring chain has, in the resulting state, the
    same structural scope, exposure, owner binding context and owning invocation as the first use's
    key was computed from, reads the SAME cell and writes nothing. The first key's stability from `s` to `t` is
    `aliasBindingCellKey_stable` on a valid chain. -/
theorem aliasBindingCell_agree (wired wired' : Algorithm) (target : Expr) (ctx ctx' : EvalCtx)
    (s t : EvalState) (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t))
    (hstable : aliasBindingCellKey wired ctx t = aliasBindingCellKey wired ctx s)
    (hscope : aliasBindingCellScopeKey wired' = aliasBindingCellScopeKey wired)
    (hexp : aliasCellIsExported wired' = aliasCellIsExported wired)
    (hctx : propertyOwnerBindingContext wired'.parent t = propertyOwnerBindingContext wired.parent t)
    (hinv : propertyOwnerInvocation wired'.parent t = propertyOwnerInvocation wired.parent t)
    (hfound : (propertyOwnerBindingContext wired'.parent t).isSome = true ∨ ctx'.bindingContext = ctx.bindingContext) :
    (aliasBindingCell wired' target ctx').runState t = (.ok a, t) :=
  aliasBindingCell_shared wired wired' target ctx ctx' s t a hnp h
    ((aliasBindingCellKey_agree wired' wired ctx' ctx t hscope hexp hctx hinv hfound).trans hstable)

/-- **Inert establishment.** Establishing (or reading) a binding cell evaluates, prepares, projects
    and demands nothing: every existing cell keeps its suspension, VALUE state, CALLABLE state and plan
    supply, whatever the row. -/
theorem aliasBindingCell_inert (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState) :
    HeapCore s.needs ((aliasBindingCell wired target ctx).runState s).2.needs := by
  by_cases hp : ∃ n, target = .param n
  · obtain ⟨n, rfl⟩ := hp
    show HeapCore s.needs ((supplyNeed (.param n) (ctx.push wired) []).runState s).2.needs
    rcases hs : (supplyNeed (.param n) (ctx.push wired) []).runState s with ⟨o, t⟩
    cases o with
    | ok r => exact (supply_heap_core _ _ _ s r t hs).1
    | error e =>
      -- A parameter row fails only as the refusal of an UNAVAILABLE parameter, in the entry state.
      rcases supply_shape (.param n) (ctx.push wired) [] s with ⟨e', he⟩ | ⟨r, t', hr, _⟩
      · rw [he] at hs
        cases hs
        exact HeapCore.refl _
      · rw [hr] at hs
        cases hs
  · have hnp : ∀ n, target ≠ .param n := fun n h => hp ⟨n, h⟩
    cases hl : lookupAssoc (aliasBindingCellKey wired ctx s) s.aliasCells with
    | some a0 =>
      rw [aliasBindingCell_recorded wired target ctx s a0 hnp hl]
      exact HeapCore.refl _
    | none =>
      obtain ⟨c, u, _, hneeds, _, _, hrun⟩ := aliasBindingCell_establishes wired target ctx s hnp hl
      rw [hrun]
      show HeapCore s.needs (u.needs.push _)
      rw [hneeds]
      exact HeapCore.push _ _

/-- **Parameter transport (NEED-01).** The binding cell of an alias whose row is a PARAMETER bound to a
    supplied cell `p` IS `p` — the parameter's own cell, never a replacement: nothing is allocated,
    entered or recorded, so the alias's VALUE and CALLABLE are that parameter's own channels. -/
theorem aliasBindingCell_parameter_transport (wired : Algorithm) (name : Ident) (ctx : EvalCtx)
    (s : EvalState) (activation : Option ParameterActivation) (p : Nat)
    (hact : (capturedParameterActivation? name (ctx.push wired)).runState s = (.ok activation, s))
    (hfind : lookupAssoc name (activation.map ParameterActivation.needs |>.getD (ctx.push wired).needEnv) = some p) :
    (aliasBindingCell wired (.param name) ctx).runState s = (.ok p, s) := by
  simp only [aliasBindingCell]
  exact KatLang.NeedControl.Allocation.supply_param_transports name (ctx.push wired) [] s s activation p hact hfind

/-! ## One runtime step: failure is never absence -/

theorem runtimeAliasStep_cell_failure_propagates (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u : EvalState) (e : Error)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.error e, u)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.error e, u) := by
  simp only [runtimeAliasStepWith, bind_run, hcell]

/-- **Failure propagates.** A projection FAILURE of the binding cell — whatever its kind — is the
    step's failure, with the same error: never the alias's ordinary property, never absence, never a
    retry. The reader is judged first (ledger R-1); for a reader the judgment admits the projection
    runs SERVED from the state the judgment left, and its state is the step's. -/
theorem runtimeAliasStep_failure_propagates (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u u' t : EvalState) (a : Nat) (e : Error)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hjudge : (judgeRetainedCellReuse a ctx).runState u = (.ok (), u'))
    (hfail : (servingDetached ctx.servingOwners (project a)).runState u' = (.error e, t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.error e, t) := by
  simp only [runtimeAliasStepWith, reuseRetainedCell, bind_run, hcell, hjudge, hfail]

/-- **A refused reuse is a failure, and the projection does not run.** A reader that detaches an input
    the cell is known to have read is refused with the cell's refusal in the state the cell's
    establishment left: the judgment comes BEFORE the projection (ledger R-1). -/
theorem runtimeAliasStep_refused (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u u' : EvalState) (a : Nat) (refusal : Error)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hjudge : (judgeRetainedCellReuse a ctx).runState u = (.error refusal, u')) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.error refusal, u') := by
  simp only [runtimeAliasStepWith, reuseRetainedCell, bind_run, hcell, hjudge]

/-- **Absence ends the chase.** A binding cell that projects NO callable identity makes the alias a
    VALUE VIEW (`terminal`), never a failure and never another chase step — for a reader the reuse
    judgment admits (ledger R-1), whose projection runs served. -/
theorem runtimeAliasStep_absence_is_terminal (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u u' t : EvalState) (a : Nat)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hjudge : (judgeRetainedCellReuse a ctx).runState u = (.ok (), u'))
    (hnone : (servingDetached ctx.servingOwners (project a)).runState u' = (.ok none, t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.ok .terminal, t) := by
  simp only [runtimeAliasStepWith, reuseRetainedCell, bind_run, hcell, hjudge, hnone]
  rfl

/-- A supplied identity is passed on unchanged: the chase continues with exactly it (for a reader the
    reuse judgment admits, whose projection runs served). -/
theorem runtimeAliasStep_identity (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u u' t : EvalState) (a : Nat) (identity : Algorithm)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hjudge : (judgeRetainedCellReuse a ctx).runState u = (.ok (), u'))
    (hsome : (servingDetached ctx.servingOwners (project a)).runState u' = (.ok (some identity), t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.ok (.continue identity), t) := by
  simp only [runtimeAliasStepWith, reuseRetainedCell, bind_run, hcell, hjudge, hsome]
  rfl

/-! ## The value view (L-RUN, M4★) -/

/-- The value view is exactly the open body the alias was elaborated from: the same declaration,
    scope, opens and declarations, no parameter, the alias's row as its one output. -/
theorem aliasPropertyView_is_the_open_body (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    (Algorithm.alias p op pr target id reference).aliasPropertyView = .mk p [] op pr [target] id := rfl

/-- **No alias-to-self redispatch.** The value view is never an alias, so no consumer can normalize the
    same unresolved alias again. -/
theorem aliasPropertyView_is_no_alias (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (q : Option ScopeCtx)
    (op' : List Expr) (pr' : List PropDef) (target' : Expr) (id' : Option PropertyIdentity) (r' : Bool) :
    (Algorithm.alias p op pr target id reference).aliasPropertyView ≠ .alias q op' pr' target' id' r' := by
  simp [Algorithm.aliasPropertyView]

/-- The value view takes no supply: a non-empty supply is the binder's own cardinality failure, and a
    zero-supply invocation binds nothing. -/
theorem aliasPropertyView_takes_no_supply (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    (Algorithm.alias p op pr target id reference).aliasPropertyView.parameterPatterns = [] := rfl

/-- **The value view reads the binding cell.** The value view keeps the alias's declaration and scope, so
    its cell key IS the alias's (`aliasBindingCellKey`, in the same context and state): a zero-supply
    invocation of the view demands exactly the binding cell the chase projected, never a rerun of the row. -/
theorem valueView_reads_the_binding_cell (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) (s : EvalState) :
    aliasBindingCellKey (Algorithm.alias p op pr target id reference).aliasPropertyView ctx s
      = aliasBindingCellKey (Algorithm.alias p op pr target id reference) ctx s := rfl

/-- The value view's cell is a READ: it changes no state, and returns the recorded binding cell. -/
theorem valueViewCell_reads_only (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) (s : EvalState) :
    (valueViewCell? (Algorithm.alias p op pr target id reference).aliasPropertyView ctx).runState s
      = (.ok (lookupAssoc (aliasBindingCellKey (Algorithm.alias p op pr target id reference) ctx s) s.aliasCells), s) := by
  simp only [Algorithm.aliasPropertyView, valueViewCell?, bind_run, get_run]
  rfl

/-- **A runtime reference is its own open namespace (OD-C).** A transparent reference whose row is a
    parameter has no static path: `openStructure` returns it unchanged — its own, empty, namespace; nothing
    is opened dynamically. -/
theorem runtime_reference_opens_itself (fuel : Nat) (ctx : EvalCtx) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (x : Ident) (id : Option PropertyIdentity) (s : EvalState) :
    (openStructure (fuel + 1) ctx (.alias p op pr (.param x) id true)).runState s
      = (.ok (.alias p op pr (.param x) id true), s) := by
  simp only [openStructure, Expr.staticAliasPath?]
  rfl

end KatLang.RuntimeAliasLaws
