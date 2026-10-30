import KatLangArityLaws.AlgorithmProjection

open KatLang KatLang.CallPlan KatLang.AlgorithmProjectionLaws

/-! R7 checkpoint: alias recursion now goes through the total `EvalBody`/`evalFuel` core and its
production fuel search. The source-only descriptions below are historical limitations of these
local theorems. `EvaluatorCore.production_unfolds` covers completed operations; reachable alias
bindings, declaring activations and end-to-end alias refinement remain open. (M4★, ALIAS-UNIFY-1,
October 2026, retired D4's first-observation claims and FWD-02's runtime eligibility gate; the
whole-algorithm transport laws are `WholeAlgorithmTransport.lean`.) -/

/-!
# META-S3-2: runtime-target callable aliases (October 2026)

A RUNTIME-TARGET ALIAS (FWD-02; owner decisions D1 = yes, D2 = Option A, D3 = fresh invocation; L-RUN,
M4★) is an `Algorithm.alias` whose row is a RUNTIME ROW (`Expr.isRuntimeAliasRow`): a parameter
reference, an argumentless `.Algorithm` link, or an argumentless parameter-rooted member path. Its
STRUCTURE and its INVOCATION target are the identity its ONE binding cell projects in its declaring
activation, at ANY arity (no eligibility gate); a cell that projects NO identity makes it a VALUE VIEW
(`Algorithm.aliasPropertyView`): no members, no CALLABLE, a zero-supply invocation returns the binding
cell's VALUE (`valueViewCell?`) and a non-empty supply is the binder's cardinality failure. Its bare
read is the binding cell's VALUE (`aliasValue`). The authoritative definitions are in `lean/KatLang.lean`:

* `aliasBindingCell` — the binding cell, supplied in the alias's own declaring context through the one
  supplier (`supplyNeed`) and recorded in `EvalState.aliasCells` under `aliasCellKey` (the alias's
  declaration and its declaring activations);
* `runtimeAliasStepWith` — one runtime step of the chase over a CALLABLE capability;
* `Algorithm.aliasPropertyView` and `valueViewCell?` — the value view and the cell its invocation reads.

The evaluator core installs them: `resolveAliasChase` takes the runtime step as
`runtimeAliasStepWith projectNeedCallable` when `aliasStepIsRuntime` holds; the VALUE chase stops at the
runtime alias, whose bare read `aliasValue` demands the SAME binding cell. That installation is pinned by
executable guards (`RuntimeAliasGuards.lean`, the `runtime-alias-*` LanguageSpec cases, and
`CoreTests/AliasForwarding`).

Proved here, over the total definitions:

* the binding cell is CANONICAL per declaration and declaring activation
  (`aliasBindingCell_recorded`, `aliasBindingCell_canonical`: once established, every later use — the
  bare VALUE and every CALLABLE projection alike — reads the recorded cell and changes nothing), its
  establishment is INERT (`aliasBindingCell_inert`: every existing cell keeps its suspension, VALUE
  state, CALLABLE state and plan supply), and a PARAMETER row is that parameter's own cell, allocating
  nothing (`aliasBindingCell_parameter_transport`, NEED-01);
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

NOT claimed here (source facts with executable guards, or C#-only): that the `partial` evaluator calls
these definitions; that a call through the alias is the identity's FRESH call with exactly the written
new supply (D3) and that a chain or cycle behaves as the guards show; the C# front end's Option A
classification and Q-75 inference (front-end facts, FORMAL-02: no theorem here concerns inference);
C# concurrency, first-wins establishment, the CALLABLE single flight, Guard B, run pre-marking,
asynchronous resolution and cancellation (C#-only, `RuntimeCallableAliasMechanismTests`).
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

/-- A recorded binding cell is read: nothing is supplied, allocated, entered or written. -/
theorem aliasBindingCell_recorded (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : lookupAssoc (aliasCellKey wired) s.aliasCells = some a) :
    (aliasBindingCell wired target ctx).runState s = (.ok a, s) := by
  rw [aliasBindingCell_nonparameter wired target ctx hnp]
  simp only [aliasBindingCellRecorded, bind_run, get_run, h]
  rfl

/-- Entering an alias body succeeds and never touches the cell heap or the binding-cell record. -/
theorem enterAlgorithmBody_keeps_cells (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ∃ c t, (enterAlgorithmBody a ctx env).runState s = (.ok c, t)
      ∧ t.needs = s.needs ∧ t.aliasCells = s.aliasCells := by
  unfold enterAlgorithmBody recordParameterActivation
  split
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl, rfl⟩

/-- The first use of a non-parameter row's binding cell: the row supplied in the entered body context,
    then recorded under the alias's key. -/
theorem aliasBindingCell_establishes (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState)
    (hnp : ∀ n, target ≠ .param n)
    (hl : lookupAssoc (aliasCellKey wired) s.aliasCells = none) :
    ∃ c u, (enterAlgorithmBody wired ctx []).runState s = (.ok c, u)
      ∧ u.needs = s.needs ∧ u.aliasCells = s.aliasCells
      ∧ (aliasBindingCell wired target ctx).runState s =
          (.ok u.needs.size, { u with
            needs := u.needs.push { suspension := .expression target c [] },
            aliasCells := (aliasCellKey wired, u.needs.size) :: u.aliasCells }) := by
  obtain ⟨c, u, he, hneeds, hcells⟩ := enterAlgorithmBody_keeps_cells wired ctx [] s
  refine ⟨c, u, he, hneeds, hcells, ?_⟩
  rw [aliasBindingCell_nonparameter wired target ctx hnp]
  simp only [aliasBindingCellRecorded, bind_run, get_run, hl, he,
    KatLang.NeedControl.Allocation.supply_nonparameter target c [] u hnp, modify_run]
  rfl

/-- **Canonical binding cell.** Whatever cell the first successful use of a runtime alias's binding
    cell returns, using it again from the resulting state — for the bare VALUE or for any CALLABLE
    projection — returns the SAME cell and changes nothing: one binding cell per declaration and
    declaring activation (`aliasCellKey`). A parameter row is its parameter's own cell instead
    (`aliasBindingCell_parameter_transport`). -/
theorem aliasBindingCell_canonical (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s t : EvalState)
    (a : Nat) (hnp : ∀ n, target ≠ .param n)
    (h : (aliasBindingCell wired target ctx).runState s = (.ok a, t)) :
    (aliasBindingCell wired target ctx).runState t = (.ok a, t) := by
  cases hl : lookupAssoc (aliasCellKey wired) s.aliasCells with
  | some a0 =>
    rw [aliasBindingCell_recorded wired target ctx s a0 hnp hl] at h
    cases h
    exact aliasBindingCell_recorded wired target ctx s _ hnp hl
  | none =>
    obtain ⟨c, u, _, _, _, hrun⟩ := aliasBindingCell_establishes wired target ctx s hnp hl
    rw [hrun] at h
    cases h
    apply aliasBindingCell_recorded wired target ctx _ _ hnp
    simp [lookupAssoc]

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
      obtain ⟨r, hr⟩ := supply_shape (.param n) (ctx.push wired) [] s
      rcases hr with hr | ⟨hr, _⟩ <;> rw [hr] at hs <;> cases hs
  · have hnp : ∀ n, target ≠ .param n := fun n h => hp ⟨n, h⟩
    cases hl : lookupAssoc (aliasCellKey wired) s.aliasCells with
    | some a0 =>
      rw [aliasBindingCell_recorded wired target ctx s a0 hnp hl]
      exact HeapCore.refl _
    | none =>
      obtain ⟨c, u, _, hneeds, _, hrun⟩ := aliasBindingCell_establishes wired target ctx s hnp hl
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
  exact KatLang.NeedControl.Allocation.supply_param_transports name (ctx.push wired) [] s activation p hact hfind

/-! ## One runtime step: failure is never absence -/

theorem runtimeAliasStep_cell_failure_propagates (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u : EvalState) (e : Error)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.error e, u)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.error e, u) := by
  simp only [runtimeAliasStepWith, bind_run, hcell]

/-- **Failure propagates.** A projection FAILURE of the binding cell — whatever its kind — is the
    step's failure, with the same error and state: never the alias's ordinary property, never absence,
    never a retry. -/
theorem runtimeAliasStep_failure_propagates (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u t : EvalState) (a : Nat) (e : Error)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hfail : (project a).runState u = (.error e, t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.error e, t) := by
  simp only [runtimeAliasStepWith, bind_run, hcell, hfail]

/-- **Absence ends the chase.** A binding cell that projects NO callable identity makes the alias a
    VALUE VIEW (`terminal`), never a failure and never another chase step. -/
theorem runtimeAliasStep_absence_is_terminal (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u t : EvalState) (a : Nat)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hnone : (project a).runState u = (.ok none, t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.ok .terminal, t) := by
  simp only [runtimeAliasStepWith, bind_run, hcell, hnone]
  rfl

/-- A supplied identity is passed on unchanged: the chase continues with exactly it. -/
theorem runtimeAliasStep_identity (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u t : EvalState) (a : Nat) (identity : Algorithm)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hsome : (project a).runState u = (.ok (some identity), t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.ok (.continue identity), t) := by
  simp only [runtimeAliasStepWith, bind_run, hcell, hsome]
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
    its cell key IS the alias's (`aliasCellKey`): a zero-supply invocation of the view demands exactly the
    binding cell the chase projected, never a rerun of the row. -/
theorem valueView_reads_the_binding_cell (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) :
    aliasCellKey (Algorithm.alias p op pr target id reference).aliasPropertyView
      = aliasCellKey (Algorithm.alias p op pr target id reference) := rfl

/-- The value view's cell is a READ: it changes no state, and returns the recorded binding cell. -/
theorem valueViewCell_reads_only (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (s : EvalState) :
    (valueViewCell? (Algorithm.alias p op pr target id reference).aliasPropertyView).runState s
      = (.ok (lookupAssoc (aliasCellKey (Algorithm.alias p op pr target id reference)) s.aliasCells), s) := by
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
