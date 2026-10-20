import KatLangArityLaws.AlgorithmProjection

open KatLang KatLang.CallPlan KatLang.AlgorithmProjectionLaws

/-! R7 checkpoint: alias recursion now goes through the total `EvalBody`/`evalFuel` core and its
production fuel search. The source-only descriptions below are historical limitations of these
local theorems. `EvaluatorCore.production_unfolds` covers completed operations; reachable alias
bindings, declaring activations, D4 ownership and end-to-end alias refinement remain open. -/

/-!
# META-S3-2: runtime-target callable aliases (October 2026)

A RUNTIME-TARGET ALIAS (FWD-02; owner decisions D1 = yes, D2 = Option A, D3 = fresh invocation) is an
`Algorithm.alias` whose row is a RUNTIME ROW (`Expr.isRuntimeAliasRow`): a parameter reference, an
argumentless `.Algorithm` link, or an argumentless parameter-rooted member path. Its callable is the
identity its ONE binding cell projects in its declaring activation when that identity declares
parameterized callable structure; otherwise the alias is exactly its ordinary zero-parameter property.
The authoritative definitions are in `lean/KatLang.lean`:

* `aliasBindingCell` — the binding cell, supplied in the alias's own declaring context through the one
  supplier (`supplyNeed`) and recorded in `EvalState.aliasCells` under `aliasCellKey` (the alias's
  declaration and its declaring activations);
* `runtimeAliasStepWith` — one runtime step of the chase over a CALLABLE capability;
* `runtimeAliasFinish` — FWD-02 eligibility applied to the identity the run supplied;
* `Algorithm.aliasPropertyView` — the alias's ordinary zero-parameter property.

The `partial` evaluator installs them: `resolveAliasChase` takes the runtime step as
`runtimeAliasStepWith projectNeedCallable` when `aliasStepIsRuntime` holds and ends a projected chase
with `runtimeAliasFinish`; the VALUE chase (`resolveAliasValueTarget`) stops at the runtime alias, whose
bare read `aliasValue` demands the SAME binding cell. That installation is a SOURCE FACT of the
`partial` definitions (Lean keeps them opaque), pinned by executable guards
(`RuntimeAliasGuards.lean`, the `runtime-alias-*` LanguageSpec cases, and `CoreTests/AliasForwarding`).

Proved here, over the total definitions:

* the binding cell is CANONICAL per declaration and declaring activation
  (`aliasBindingCell_recorded`, `aliasBindingCell_canonical`: once established, every later use — the
  bare VALUE and every CALLABLE projection alike — reads the recorded cell and changes nothing), its
  establishment is INERT (`aliasBindingCell_inert`: every existing cell keeps its suspension, VALUE
  state, CALLABLE state and plan supply), and a PARAMETER row is that parameter's own cell, allocating
  nothing (`aliasBindingCell_parameter_transport`, NEED-01);
* one runtime step keeps FAILURE apart from ABSENCE: a projection failure propagates with its error
  (`runtimeAliasStep_failure_propagates`), as does a failure to establish the cell
  (`runtimeAliasStep_cell_failure_propagates`), absence is the alias's ordinary property
  (`runtimeAliasStep_absence_is_property`) and a supplied identity is passed on unchanged
  (`runtimeAliasStep_identity`);
* the terminal outcome is never the unresolved alias again — no alias-to-self redispatch
  (`aliasPropertyView_is_the_open_body`, `aliasPropertyView_is_no_alias`), it is an ordinary
  zero-parameter property (`aliasPropertyView_declares_no_parameters`), and FWD-02's eligibility keeps an
  identity that declares parameterized structure and turns every other one into that property
  (`runtimeAliasFinish_eligible`, `runtimeAliasFinish_ineligible`);
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

/-- **Absence is the ordinary property.** A binding cell that projects NO callable identity leaves the
    alias its ordinary zero-parameter property. -/
theorem runtimeAliasStep_absence_is_property (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm)
    (target : Expr) (ctx : EvalCtx) (s u t : EvalState) (a : Nat)
    (hcell : (aliasBindingCell owner target ctx).runState s = (.ok a, u))
    (hnone : (project a).runState u = (.ok none, t)) :
    (runtimeAliasStepWith project owner target ctx).runState s = (.ok (.terminal owner.aliasPropertyView), t) := by
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

/-! ## The terminal ordinary property and FWD-02 eligibility -/

/-- The property view is exactly the open body the alias was elaborated from: the same declaration,
    scope, opens and declarations, no parameter, the alias's row as its one output. -/
theorem aliasPropertyView_is_the_open_body (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) :
    (Algorithm.alias p op pr target id).aliasPropertyView = .mk p [] op pr [target] id := rfl

/-- **No alias-to-self redispatch.** The terminal outcome is never an alias, so no consumer can
    normalize the same unresolved alias again. -/
theorem aliasPropertyView_is_no_alias (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (q : Option ScopeCtx) (op' : List Expr)
    (pr' : List PropDef) (target' : Expr) (id' : Option PropertyIdentity) :
    (Algorithm.alias p op pr target id).aliasPropertyView ≠ .alias q op' pr' target' id' := by
  simp [Algorithm.aliasPropertyView]

/-- The property view declares no parameterized structure: it is an ordinary zero-parameter property,
    so a call with arguments is its own arity rejection and an explicit `()` its fresh body. -/
theorem aliasPropertyView_declares_no_parameters (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) :
    (Algorithm.alias p op pr target id).aliasPropertyView.isEligibleRuntimeAliasTarget = false := rfl

theorem runtimeAliasFinish_eligible (owner final : Algorithm) (h : final.isEligibleRuntimeAliasTarget = true) :
    runtimeAliasFinish owner final = final := by
  simp [runtimeAliasFinish, h]

theorem runtimeAliasFinish_ineligible (owner final : Algorithm) (h : final.isEligibleRuntimeAliasTarget = false) :
    runtimeAliasFinish owner final = owner.aliasPropertyView := by
  simp [runtimeAliasFinish, h]

/-- FWD-02's eligibility over the identities a run supplies: every builtin and clause family, a user
    algorithm exactly when it declares a parameter pattern, never an alias. -/
theorem eligibility (b : Builtin) (p : Option ScopeCtx) (ps : List ParameterPattern) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) (bs : List CondBranch) :
    (Algorithm.builtin b).isEligibleRuntimeAliasTarget = true
      ∧ (Algorithm.conditional p op bs id).isEligibleRuntimeAliasTarget = true
      ∧ (Algorithm.mk p ps op pr out id).isEligibleRuntimeAliasTarget = !ps.isEmpty := ⟨rfl, rfl, rfl⟩

/-- D4: claiming eligibility work is one-shot and preserves the Need channels. -/
theorem terminal_initial_claim_once (cell claimed : NeedCell)
    (h : claimTerminalAliasInitial cell = some claimed) :
    claimTerminalAliasInitial claimed = none ∧ claimed.suspension = cell.suspension
      ∧ claimed.state = cell.state ∧ claimed.callable = cell.callable ∧ claimed.plan = cell.plan := by
  unfold claimTerminalAliasInitial at h
  split at h
  · cases h
    simp [claimTerminalAliasInitial]
  · contradiction

/-- A preceding bare observation excludes reusing that computation for a terminal call. -/
theorem bare_value_excludes_terminal_reuse (cell : NeedCell) :
    claimTerminalAliasInitial { cell with aliasUse := 1 } = none := by
  simp [claimTerminalAliasInitial]

/-- A terminal invocation that claimed first excludes every later terminal invocation (D4: explicit
    calls never share a completed terminal invocation). -/
theorem terminal_claim_excludes_later_terminal_reuse (cell : NeedCell) :
    claimTerminalAliasInitial { cell with aliasUse := 2 } = none := by
  simp [claimTerminalAliasInitial]

/-- An unclaimed cell is claimed by the first terminal invocation whatever operation performed its
    projection: the claim reads only the cell's own observation state (D4: eligibility checking never
    duplicates a receiver evaluation). -/
theorem unclaimed_cell_is_claimed_once (cell : NeedCell) (h : cell.aliasUse = 0) :
    claimTerminalAliasInitial cell = some { cell with aliasUse := 2 } := by
  simp [claimTerminalAliasInitial, h]

/-- An eligible target still bypasses the terminal property view (D3). -/
theorem eligible_target_keeps_declared_parameters (owner : Algorithm) (p : Option ScopeCtx)
    (ps : List ParameterPattern) (op : List Expr) (pr : List PropDef) (out : OutputBundle)
    (id : Option PropertyIdentity) (h : ps.isEmpty = false) :
    runtimeAliasFinish owner (.mk p ps op pr out id) = .mk p ps op pr out id := by
  simp [runtimeAliasFinish, Algorithm.isEligibleRuntimeAliasTarget, h]

/-- Namespace classification admits a runtime row without any target projection. -/
theorem runtime_namespace_direct (fuel : Nat) (chain : List Algorithm) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity)
    (h : target.isRuntimeAliasRow = true)
    (hs : namespaceStaticPath? ((reprStr chain).length + (reprStr (Algorithm.alias p op pr target id)).length + 1)
      (chain ++ [.alias p op pr target id]) target = none) :
    Algorithm.runtimeAliasNamespace (fuel + 1) chain (.alias p op pr target id) = true := by
  simp [Algorithm.runtimeAliasNamespace, hs, h]

end KatLang.RuntimeAliasLaws
