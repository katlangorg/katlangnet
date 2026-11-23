import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction

/-!
# Evaluator installation: the former "source facts" as theorems (November 2026)

The total helpers of `lean/KatLang.lean` (`NeedDemand.step`, `NeedProjection.step`, `NeedSupply.form`,
`bindNeedPatterns`, `selectWith`, `openSpreadItems`, `reCountValueBoundary`, …) carry the laws of the
other modules. That the evaluator CALLS them — "installs" them — used to be a fact of its source: until
R7 (October 2026) the evaluator operations were `partial` definitions, opaque constants of the kernel,
so no theorem could mention their bodies and each law recorded the call as a "source fact" pinned by
executable guards.

Since R7 every evaluator operation is a body `EvalBody.<name> rec …` of the total fuel-indexed core
(`evalStep`), a kernel term over the evaluator answer `rec`, and since E-6 Tier 3 no `partial`
definition remains in `KatLang.lean`. An installation is therefore an EQUATION of that body, and it
is stated here, for EVERY evaluator answer `rec`:

* § 0 — the transfer to production: a completed production operation is its installed body over the
  production operations (`production_installed`, a restatement of `EvaluatorCore.production_unfolds`),
  and a body that never consults the answer is production's outcome outright
  (`WhileRoundProduction.production_of_answer_free`; `emptySequence_production`);
* § 1 — the arms of `evalCounted`: the empty sequence, the parameter read, the capture and the spread
  arm, postfix selection, the call and the dot edge;
* § 2 — the VALUE and CALLABLE shells: the recursive VALUE edge, the address-indexed expression
  evaluation, the `.Algorithm` link channels, the CALLABLE projection and the typed parameter
  projection with its three readers;
* § 3 — callee resolution, the written-argument projection, the alias chase and the bare read of a
  runtime-target alias;
* § 4 — supply formation and the binder: the ordinary call, the resolved-call dispatch, the callback
  route, the user and family supplied-call arms, zero-argument and property demand, and both
  loop-step arms all bind through `rec.bindingChannels` (production: `EvaluatorCore.bindingChannels_is_core`);
* § 5 — builtins: the sequence-builtin dispatch and its arity gate, `count`/`first`/`last`, the empty
  policy, collection binding and per-slot demand, the callback item and the `reduce` step, the
  invoking slot, `atoms`, `if`, `filter` and the logical operators (the readers of the Boolean view),
  a VALUE slot over a cell;
* § 6 — the call-reference intrinsics: `Invoke`, `Arguments`, `.Algorithm`, the spread evaluation,
  the spread capability and the dot route's member-read and intrinsic arms;
* § 7 — rows and captures: the shared output-row loop;
* § 8 — two heap-size premises formerly supported by source inspection, as consequences of the
  whole-run heap discipline: no production operation shrinks the heap.

The installation equations are the body's own text, proved by `rfl` or one unfolding under their
stated arm conditions; § 8 derives heap-size consequences from the existing discipline theorem.
Nothing here is a new semantic law: the theorems connect the laws proved elsewhere to the operation
that uses them. What a body equation does NOT give is a property of whole runs (that every evaluated value is canonical,
that an operation completes, that a reachable state satisfies a premise): those stay with the modules
that state them, and with the ledger (`docs/design/formal-correspondence-ledger.md`). C# is not a
subject of any theorem here.
-/

namespace KatLang.EvaluatorInstallation

/-! ## 0. From a body equation to production -/

/-- **Installation transfers to production.** An operation whose core body is `B` (for every
    evaluator answer) has, on every completed production run, exactly `B` over the production
    operations. This is `production_unfolds` read through the body equation. -/
theorem production_installed (c : EvalCall) (B : EvalRec → EvalM c.Ret)
    (hstep : ∀ rec, evalStep rec c = B rec) (s : EvalState)
    (hc : ProductionCompletes (evalUnbounded c) s) :
    (evalUnbounded c).runState s = (B evalUnbounded).runState s := by
  have h := production_unfolds c s hc
  rw [hstep] at h
  exact h.symm

/-! ## 1. The arms of `evalCounted` -/

/-- The `.emptySequence` arm IS `buildEmptySequenceValue`, emitted with its `Result.valueCount`. -/
theorem emptySequence_arm (rec : EvalRec) (depth : Nat) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.emptySequence depth) ctx env =
      pure (buildEmptySequenceValue depth, Result.valueCount (buildEmptySequenceValue depth)) := rfl

/-- Production: a written empty sequence evaluates to that value from every state, changing
    nothing (the arm consults no evaluator answer). -/
theorem emptySequence_production (depth : Nat) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (evalCounted (.emptySequence depth) ctx env).runState s =
      (.ok (buildEmptySequenceValue depth, Result.valueCount (buildEmptySequenceValue depth)), s) :=
  production_of_answer_free (.evalCounted (.emptySequence depth) ctx env) s _ (fun _ => rfl)
    (by intro h; cases h)

/-- AT-MOST-ONCE ARGUMENT VALUE (Q-01), the read: the `.param` arm reads a Model-C parameter
    through its need cell — ONE recursive VALUE demand of the bound address — and a value-tier
    parameter at its value boundary. -/
theorem param_arm (rec : EvalRec) (x : Ident) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.param x) ctx env = ((do
      let (ctx, env) <- parameterContext x ctx env
      if let some address := lookupAssoc x ctx.needEnv then
        return <- rec.demandNeedRecursive address
      match env.lookup x with
      | some v => pure (v, Result.valueCount v)
      | none => .error (Error.unknownName x)) : EvalM CountedResult) := rfl

/-- A capture in value position is a VALUE BOUNDARY: its captured value, emitted with
    `Result.valueCount`. -/
theorem capture_arm (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.capture rows) ctx env = ((do
      let r <- rec.evalCaptureValue rows ctx env
      pure (r, Result.valueCount r)) : EvalM CountedResult) := rfl

/-- The spread arm is the one spread evaluation, of the whole spread node. -/
theorem spread_arm (rec : EvalRec) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.sequenceSpread operand) ctx env =
      rec.evalSequenceSpreadCounted (.sequenceSpread operand) ctx env := rfl

/-- The call arm is the one expression-position call dispatch. -/
theorem call_arm (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.call f args) ctx env = rec.evalCallCountedExpr f args ctx env := rfl

/-- The dot arm is the one dot-call evaluation under its `dotCall` frame. -/
theorem dot_arm (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCounted rec (.dotMember target name fallback args?) ctx env =
      withCtx (CtxMsg.dotCall target name) (rec.evalDotCallCounted target name fallback args? ctx env) := rfl

/-- VARIADIC POSTFIX SELECTION, installed: the `.index` arm reads a retained collector receiver
    without a VALUE demand, otherwise demands the receiver ONCE; forms the selector supply like a
    call's (`NeedSupply.addresses` over the evaluator's spread capability); and instantiates the
    total selection core (`selectPositionsWith` over the receiver's positions — a pending list
    discovered up to the selected position, only that position read (issue #204) —, or
    `selectViewWith` for an argument view and a retained slice) with the recursive VALUE demand of a
    selector cell, returning `selectionResult`. -/
theorem index_arm (rec : EvalRec) (receiver : Expr) (selectors : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) :
    EvalBody.evalCounted rec (.index receiver selectors) ctx env = withNestedMissingOutput ((do
      if let some slice <- EvalBody.writtenCollectorSlice? rec receiver ctx then
        let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env selectors
        let demandCell := fun cell => Prod.fst <$> rec.demandNeedRecursive cell
        return selectionResult (<- selectViewWith demandCell (pure (retainedSourced slice)) demandCell cells)
      let value <- rec.eval receiver ctx env
      let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env selectors
      let selected <-
        match value with
        | .argView a =>
            selectViewWith (fun cell => Prod.fst <$> rec.demandNeedRecursive cell)
              (rec.argumentViewCells a) (fun cell => Prod.fst <$> rec.demandNeedRecursive cell) cells
        | _ =>
            selectPositionsWith (fun cell => Prod.fst <$> rec.demandNeedRecursive cell)
              (fun n => do
                pure (<- discoveredPositions rec.demandNeedRecursive (some (n + 1)) value)[n]?)
              (forcePosition rec.demandNeedRecursive) cells
      pure (selectionResult selected)) : EvalM CountedResult) := rfl

/-! ## 2. The VALUE and CALLABLE shells -/

/-- **The recursive VALUE edge installs the one demand shell**, over the evaluator's own
    address-indexed expression evaluation, plan route and recursive demand. Production:
    `EvaluatorCore.production_demand_unfolds`; the public `demandNeed` is the same shell by
    definition (`NeedControl.Production.demand_specialization`). -/
theorem demand_installs (rec : EvalRec) (address : Nat) :
    EvalBody.demandNeedRecursive rec address =
      NeedDemand.step (rec.evalSuppliedAt address) rec.planRoute rec.demandNeedRecursive address := rfl

/-- Every supplied expression that is no `X.Algorithm` link is evaluated by `evalCounted`. -/
theorem supplied_expression_is_evalCounted (rec : EvalRec) (address : Nat) (e : Expr)
    (ctx : EvalCtx) (env : ValEnv) (h : linkEdge? e = none) :
    EvalBody.evalSuppliedAt rec address e ctx env = rec.evalCounted e ctx env := by
  unfold EvalBody.evalSuppliedAt
  simp only [h]

/-- A supplied `X.Algorithm` link: the retained receiver cell of a planned invocation is the
    ordinary invocation receiver read; on the intrinsic route the link's VALUE is `linkValue`;
    a declared member `Algorithm` keeps the ordinary evaluation. -/
theorem supplied_link (rec : EvalRec) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv)
    (receiver fallback : Expr) (h : linkEdge? e = some (receiver, fallback)) :
    EvalBody.evalSuppliedAt rec address e ctx env = ((do
      if <- NeedLink.isInvocationReceiver address then
        let value <- EvalBody.invocationReceiverValue rec receiver ctx env
        pure (value, Result.valueCount value)
      else if <- rec.algorithmIntrinsicRoute receiver ctx then rec.linkValue address
      else rec.evalCounted e ctx env) : EvalM CountedResult) := by
  unfold EvalBody.evalSuppliedAt
  simp only [h]

/-- The link's VALUE channel installs `NeedLink.value` over the recursive VALUE demand. -/
theorem linkValue_installs (rec : EvalRec) (address : Nat) :
    EvalBody.linkValue rec address =
      NeedLink.value rec.planRoute.classify rec.demandNeedRecursive address := rfl

/-- The link's CALLABLE channel installs `NeedLink.callable` over the recursive VALUE demand and
    the CALLABLE projection. -/
theorem linkCallable_installs (rec : EvalRec) (address : Nat) :
    EvalBody.linkCallable rec address =
      NeedLink.callable rec.planRoute.classify rec.demandNeedRecursive rec.projectNeedCallable address := rfl

/-- **The CALLABLE projection installs the one projection shell** over the written projection at
    the cell's own address. -/
theorem projection_installs (rec : EvalRec) (address : Nat) :
    EvalBody.projectNeedCallable rec address =
      NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt address)) address := rfl

/-- The CALLABLE of a written expression that is no `X.Algorithm` link is `projectNeedWritten`. -/
theorem written_projection_of_non_link (rec : EvalRec) (address : Nat) (source : Expr)
    (caller : EvalCtx) (h : linkEdge? source = none) :
    EvalBody.projectNeedWrittenAt rec address source caller = rec.projectNeedWritten source caller := by
  unfold EvalBody.projectNeedWrittenAt
  simp only [h]

/-- The CALLABLE of a supplied `X.Algorithm` link is `linkCallable` on the intrinsic route. -/
theorem written_projection_of_link (rec : EvalRec) (address : Nat) (source : Expr) (caller : EvalCtx)
    (receiver fallback : Expr) (h : linkEdge? source = some (receiver, fallback)) :
    EvalBody.projectNeedWrittenAt rec address source caller = ((do
      if <- rec.algorithmIntrinsicRoute receiver caller then rec.linkCallable address
      else rec.projectNeedWritten source caller) : EvalM (Option Algorithm)) := by
  unfold EvalBody.projectNeedWrittenAt
  simp only [h]

/-- The typed parameter projection (L2) is installed over the CALLABLE projection. -/
theorem parameter_projection_installs (rec : EvalRec) (x : Ident) (ctx : EvalCtx) :
    EvalBody.projectParameterCallable rec x ctx = projectParameterWith rec.projectNeedCallable x ctx := rfl

/-- A parameter head of a structural path is that typed projection. -/
theorem structural_member_parameter_head (rec : EvalRec) (x : Ident) (ctx : EvalCtx) :
    EvalBody.projectNeedStructuralMember rec (.param x) ctx = rec.projectParameterCallable x ctx := rfl

/-- A parameter head of a dot receiver is the same typed projection. -/
theorem dot_receiver_parameter_head (rec : EvalRec) (x : Ident) (ctx : EvalCtx) :
    EvalBody.resolveDotReceiver? rec (.param x) ctx = rec.projectParameterCallable x ctx := rfl

/-- A higher-order parameter resolves to its cell's projected identity; a cell without one is
    `notAnAlgorithm`, never a VALUE demand. -/
theorem resolve_parameter (rec : EvalRec) (x : Ident) (ctx : EvalCtx) :
    EvalBody.resolveAlg rec (.param x) ctx = ((do
      match <- rec.projectParameterCallable x ctx with
      | some algorithm => pure algorithm
      | none => .error (Error.notAnAlgorithm s!"param({x})")) : EvalM Algorithm) := rfl

/-! ## 3. Callee resolution, the written-argument projection and the alias chase -/

/-- **The callee law is installed** at the evaluator's structural projection, alias normalization
    and canonical resolution (DOT-09; Q-18 C-B3). -/
theorem callee_installs (rec : EvalRec) (f : Expr) (ctx : EvalCtx) :
    EvalBody.resolveCalleeAlg rec f ctx =
      resolveCalleeAlgWith rec.projectNeedStructuralMember rec.resolveAliasTarget rec.resolveAlg f ctx := rfl

/-- The supplied-argument projection of a dot expression reads the SAME structural projection the
    callee law reads (`callee_installs`), then the selected member's STRUCTURE. The callee
    normalizes its selection with `resolveAliasTarget`, the argument with
    `resolveAliasStructure`: one structural selection in both positions, not one normalizer. -/
theorem written_projection_dot_arm (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (caller : EvalCtx) :
    EvalBody.projectNeedWritten rec (.dotMember target name fallback args?) caller = ((do
      let selected <- rec.projectNeedStructuralMember (.dotMember target name fallback args?) caller
      match selected with
      | some algorithm => rec.resolveAliasStructure algorithm caller
      | none => pure none) : EvalM (Option Algorithm)) := rfl

/-- **THE ALIAS CHASE installs the runtime step over the CALLABLE projection** (META-S3-2): a step
    that `aliasStepIsRuntime` classifies as runtime is `runtimeAliasStepWith` at the evaluator's
    `projectNeedCallable` — absence ends the chase as the value view, an identity continues it —
    unless the chase projects no runtime step (the VALUE chase stops AT the alias); every other step
    is the static `resolveAliasStepWith` over the static-only structure chase. -/
theorem alias_chase_installs (rec : EvalRec) (followCarriers projectRuntime : Bool)
    (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (target : Expr)
    (d : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) (visited : List String)
    (last : Option (Algorithm × PropDef)) :
    EvalBody.resolveAliasChase rec followCarriers projectRuntime (.alias p o pr target d reference) ctx
        visited last =
      (if !followCarriers && !reference then pure (.identity (.alias p o pr target d reference) last)
       else do
        let key := aliasChaseKey (.alias p o pr target d reference)
        if visited.contains key then
          .error (Error.illegalInEval aliasCycleMessage)
        else if (<- rec.aliasStepIsRuntime (.alias p o pr target d reference) target ctx
            (aliasStructureContext followCarriers key visited)) then
          if !projectRuntime then pure (.runtime (.alias p o pr target d reference))
          else
            match <- runtimeAliasStepWith rec.projectNeedCallable (.alias p o pr target d reference) target ctx with
            | .terminal => pure (.valueView (.alias p o pr target d reference))
            | .continue identity =>
                rec.resolveAliasChase followCarriers projectRuntime identity ctx (key :: visited) none
        else do
          let staticStructure : Algorithm → EvalCtx → EvalM (Option Algorithm) := fun receiver stepCtx => do
            match <- rec.resolveAliasChase false false receiver stepCtx
                (aliasStructureContext followCarriers key visited) none with
            | .identity found _ => pure (some found)
            | _ => pure none
          let next <- resolveAliasStepWith staticStructure (.alias p o pr target d reference) target ctx
          rec.resolveAliasChase followCarriers projectRuntime next.alg ctx (key :: visited)
            (some (next.owner, next.binding)) : EvalM AliasChaseEnd) := rfl

/-- THE BARE READ of a runtime-target alias whose row is no parameter is the VALUE demand of its ONE
    binding cell (`aliasBindingCell`) — the cell its CALLABLE projects. -/
theorem alias_value_installs (rec : EvalRec) (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef)
    (target : Expr) (d : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) (env : ValEnv)
    (h : ∀ x, target ≠ .param x) :
    EvalBody.aliasValue rec (.alias p o pr target d reference) ctx env = ((do
      rec.demandNeedRecursive (<- aliasBindingCell (.alias p o pr target d reference) target ctx)) :
        EvalM CountedResult) := by
  cases target with
  | param x => exact absurd rfl (h x)
  | _ => rfl

/-! ## 4. Supply formation and the binder -/

/-- An ORDINARY user call forms its supply with the total former over the evaluator's spread
    capability, then runs the supplied-call arm. -/
theorem user_call_installs (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) :
    EvalBody.evalUserCallCounted rec callee args ctx env = ((do
      let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env args
      rec.evalNeedUserSupply callee cells ctx env) : EvalM CountedResult) := rfl

/-- An ordinary clause-family call likewise, into the family supplied-call arm. -/
theorem family_call_installs (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (calleeName : String) :
    EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName = ((do
      let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env args
      rec.evalNeedFamilySupply callee cells ctx env calleeName) : EvalM CountedResult) := rfl

/-- THE RESOLVED-CALL DISPATCH forms the sourced supply with the same total former — every callee
    that is no unnormalized alias receives the ordinary supply cells, each with its written source —
    and then runs the ONE supplied-call dispatch. -/
theorem resolved_call_forms_supply (rec : EvalRec) (callee : Algorithm) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin)
    (h : ∀ p o pr t d r, callee ≠ .alias p o pr t d r) :
    EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin = ((do
      let cells <- NeedSupply.form rec.evalSupplySpread ctx env args
      rec.evalSuppliedCallCounted origin callee cells ctx env calleeName) : EvalM CountedResult) := by
  cases callee with
  | alias p o pr t d r => exact absurd rfl (h p o pr t d r)
  | _ => rfl

/-- A CALLBACK user invocation allocates one Ready cell per counted argument and runs THE SAME
    supplied-call arm as the ordinary call (`user_call_installs`). -/
theorem user_callback_installs (rec : EvalRec) (callee : Algorithm) (args : List CountedResult)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalUserCallbackCallCounted rec callee args ctx env = ((do
      let cells <- args.mapM readyNeed
      rec.evalNeedUserSupply callee cells ctx env) : EvalM CountedResult) := rfl

/-- A CALLBACK clause-family invocation likewise (`family_call_installs`). -/
theorem family_callback_installs (rec : EvalRec) (callee : Algorithm) (args : List CountedResult)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName = ((do
      let cells <- args.mapM readyNeed
      rec.evalNeedFamilySupply callee cells ctx env calleeName) : EvalM CountedResult) := rfl

/-- **The user supplied-call arm binds through the ONE binder at the evaluator's channels**, checks
    the output, enters a fresh binding context and evaluates the body AS AN ACTUAL CALL (the
    invocation mark `EvalCtx.enteringInvocation`: the body's entry records the activation that owns
    the call's inner bindings — or demands a value view's binding cell); the ordinary driver turns
    the binder's unexpected `none` into `badArity` itself. -/
theorem user_supply_binds (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx)
    (env : ValEnv) :
    EvalBody.evalNeedUserSupplyOutput rec callee cells ctx env = ((do
      let patterns := (Algorithm.parameterPatterns callee).map NeedPattern.ofParameter
      let some bindings <- withNestedMissingOutput (bindNeedPatterns (rec.bindingChannels) patterns cells)
        | throw Error.badArity
      if (Algorithm.output callee).isEmpty then throw (Error.missingOutput .own)
      let next <- needBindingContext ctx bindings
      if let some address ← valueViewCell? callee ctx then
        return (← rec.demandNeedRecursive address)
      rec.evalAlgOutputCounted callee { next with enteringInvocation := true }
        (ValEnv.shadow env (Algorithm.params callee))) :
        EvalM CountedResult) := rfl

/-- The user supplied-call arm's result is the call's VALUE BOUNDARY (`reCountValueBoundary`). -/
theorem user_supply_is_a_value_boundary (rec : EvalRec) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalNeedUserSupply rec callee cells ctx env = ((do
      let result <- EvalBody.evalNeedUserSupplyOutput rec callee cells ctx env
      pure (reCountValueBoundary result)) : EvalM CountedResult) := rfl

/-- **The family supplied-call arm dispatches through the ONE dispatcher at the evaluator's
    channels**, then evaluates the selected body at the call's value boundary. -/
theorem family_supply_selects (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx)
    (env : ValEnv) (calleeName : String) :
    EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName = ((do
      let (body, next, values) <- withNestedMissingOutput
        (selectNeedFamilyBranch (rec.bindingChannels) callee cells ctx env calleeName)
      let result <- rec.evalAlgOutputCounted body next values
      pure (reCountValueBoundary result)) : EvalM CountedResult) := rfl

/-- A user LOOP STEP binds its state cells through the same binder at the same channels and reads
    its body as the actual call a round is (the invocation mark). -/
theorem user_step_binds {α : Type} (rec : EvalRec) (read : Algorithm → EvalCtx → ValEnv → EvalM α)
    (atomic : CountedResult → EvalM α) (again : Algorithm → EvalM α)
    (p : Option ScopeCtx) (pp : List ParameterPattern) (op : List Expr) (pr : List PropDef)
    (o : List Expr) (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv)
    (cells : List NeedSupply.Sourced) (stepName : String) :
    EvalBody.runNeedStepWith rec read atomic again (.mk p pp op pr o d) ctx env cells stepName = ((do
      let some bindings <- bindNeedPatterns (rec.bindingChannels)
          ((Algorithm.parameterPatterns (.mk p pp op pr o d)).map NeedPattern.ofParameter) (cells.map Prod.fst)
        | throw Error.badArity
      let next <- needBindingContext ctx bindings
      read (.mk p pp op pr o d) { next with enteringInvocation := true }
        (ValEnv.shadow env (Algorithm.params (.mk p pp op pr o d)))) :
        EvalM α) := rfl

/-- A clause-family LOOP STEP selects through the same dispatcher at the same channels, under its
    ordinary call frame. This is the family arm of the shared row-reader dispatch. -/
theorem family_step_selects {α : Type} (rec : EvalRec)
    (read : Algorithm → EvalCtx → ValEnv → EvalM α) (atomic : CountedResult → EvalM α)
    (again : Algorithm → EvalM α) (p : Option ScopeCtx) (op : List Expr) (branches : List CondBranch)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv)
    (cells : List NeedSupply.Sourced) (stepName : String) :
    EvalBody.runNeedStepWith rec read atomic again (.conditional p op branches d) ctx env cells stepName =
      withCtx s!"while evaluating call to {stepName}" ((do
        let (body, next, values) <- selectNeedFamilyBranch rec.bindingChannels
          (.conditional p op branches d) (cells.map Prod.fst) ctx env stepName
        read body next values) : EvalM α) := rfl

/-- THE ZERO-ARGUMENT DEMAND of a user callable that declares a parameter pattern binds the EMPTY
    supply through the same binder at the same channels, over the same pattern list (so the
    `badArity` it raises for a non-match is the ordinary driver's). -/
theorem zero_argument_demand_binds (rec : EvalRec) (p : Option ScopeCtx) (pp : List ParameterPattern)
    (op : List Expr) (pr : List PropDef) (o : List Expr) (d : Option PropertyIdentity) (ctx : EvalCtx)
    (env : ValEnv) (h : (Algorithm.parameterPatterns (.mk p pp op pr o d)).isEmpty = false) :
    EvalBody.evalZeroArgumentDemandOutputCounted rec (.mk p pp op pr o d) ctx env = ((do
      let some bindings <- bindNeedPatterns (rec.bindingChannels)
          ((Algorithm.parameterPatterns (.mk p pp op pr o d)).map NeedPattern.ofParameter) []
        | throw Error.badArity
      let newCtx <- needBindingContext ctx bindings
      rec.evalAlgOutputCounted (.mk p pp op pr o d) newCtx
        (ValEnv.shadow env (Algorithm.params (.mk p pp op pr o d)))) : EvalM CountedResult) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A property-style READ of a user with patterns binds the empty supply with the same channels,
    then enters the body with its declaring binding context (CACHE-OWNER-D1). -/
theorem property_demand_binds (rec : EvalRec) (p : Option ScopeCtx) (head : ParameterPattern)
    (tail : List ParameterPattern) (op : List Expr) (pr : List PropDef) (o : List Expr)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalPropertyDemandCounted rec (.mk p (head :: tail) op pr o d) ctx env = ((do
      let some bindings <- bindNeedPatterns rec.bindingChannels
          ((Algorithm.parameterPatterns (.mk p (head :: tail) op pr o d)).map NeedPattern.ofParameter) []
        | throw Error.badArity
      let boundCtx <- needBindingContext ctx bindings
      let boundEnv := ValEnv.shadow env (Algorithm.params (.mk p (head :: tail) op pr o d))
      ActivatedBody.check (.mk p (head :: tail) op pr o d)
      let inherited := (propertyOwnerBindingContext p (<- get)).getD ctx.bindingContext
      let pushedCtx <- enterPropertyOwnerBody (.mk p (head :: tail) op pr o d) boundCtx boundEnv inherited
      let out <- rec.evalOutputRowsPreparedCore o pushedCtx boundEnv
      pure out.counted) : EvalM CountedResult) := rfl

/-- The production channels are the evaluator's channels at the production answer: every binder
    call site above passes `bindingChannels` under production. -/
theorem production_channels : bindingChannels = EvalRec.bindingChannels evalUnbounded :=
  bindingChannels_is_core

/-! ## 5. Builtins -/

/-- A collection builtin's application is its sequence dispatch (a missing output escaping it is
    nested). -/
theorem sequence_builtin_installs (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (h : sequenceBuiltinMetadata? b = some metadata) :
    EvalBody.applyBuiltinCounted rec b args ctx env =
      withNestedMissingOutput (rec.applyBuiltinCountedSequence b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCounted
  simp only [h]

/-- Collection binding installs the post-binding one-level value view (`collectionPositions`: a
    builtin that reads positions gets them as stored, a strict builtin reads every position in
    order — issue #204), the pending-list transport of a lazy stage and the argument-view and
    retained-collector readers. Ordinary VALUE/control slots use the same per-slot demand; callback
    slots are transported. The cardinality gate precedes every demand. -/
theorem sequence_builtin_binding_installs (rec : EvalRec) (b : Builtin)
    (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env = ((do
      let items := collectSequenceCallableCallItems args
      let expectedArgCount := 1 + metadata.suffixArgs.length
      if items.length != expectedArgCount then
        .error (Error.arityMismatch expectedArgCount items.length)
      match items with
      | [] => .error (Error.arityMismatch expectedArgCount 0)
      | collectionItem :: controlItems => do
          let prepareControls := EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env
          if b.readsRetainedCollector then
            if let some address := collectionItem.need? then
              if let some slice <- EvalBody.retainedSliceAt? rec address then
                let suffixArgs <- prepareControls metadata.suffixArgs controlItems
                return { preparedInput := { items := [] }, iterationItems := [], suffixArgs := suffixArgs, slice? := some slice }
          let collectionItem <- rec.demandSequenceBuiltinCallItemValue collectionItem ctx env
          let collectionValue <- match collectionItem.value? with
            | some value => pure value
            | none => match sequenceBuiltinValueDemandError? collectionItem with
              | some err => .error err
              | none => .error Error.badArity
          if let .argView a := collectionValue then
            if b.readsArgumentView then
              return { preparedInput := { items := [] }, iterationItems := [], suffixArgs := [], view? := some a }
            else
              .error (Error.typeMismatch (argumentViewUnsupportedMessage (builtinDisplayName b)))
          if let some candidates := pendingStageCandidates? b collectionValue then
            let suffixArgs <- prepareControls metadata.suffixArgs controlItems
            return { preparedInput := { items := [] }, iterationItems := [], suffixArgs := suffixArgs, pending? := some candidates }
          let collectionValues <- collectionPositions rec.demandNeedRecursive b collectionValue
          let collected : CollectedSequenceBuiltinInput := { items := collectionValues }
          let preparedInput <- prepareSequenceBuiltinInput b metadata collected
          let suffixArgs <- prepareControls metadata.suffixArgs controlItems
          pure {
            preparedInput := preparedInput
            iterationItems := collectionValues.map (fun value => (value, 1))
            suffixArgs := suffixArgs
          }) :
        EvalM BoundSequenceBuiltinArguments) := rfl

/-- The installed control-preparation helper transports a callback slot, retains a DEFERRED value
    control undemanded (`reduce`'s `initial`) and demands every other executed VALUE/control slot
    through the one per-slot demand, before preparing the next control. -/
theorem sequence_builtin_control_step (rec : EvalRec) (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptor : SequenceBuiltinSuffixArgDescriptor) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (item : CallableCallItem) (rest : List CallableCallItem) :
    EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env
        (descriptor :: descriptors) (item :: rest) = ((do
      let item <- match descriptor.kind with
        | .algorithm => pure item
        | _ => if descriptor.deferred then pure item else rec.demandSequenceBuiltinCallItemValue item ctx env
      let prepared <- prepareSequenceBuiltinSuffixArgItem b descriptor item
      let tail <- EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors rest
      pure (prepared :: tail)) : EvalM (List PreparedSequenceBuiltinSuffixArg)) := rfl

/-- A collection builtin's per-slot VALUE demand installs the recursive demand and its existing
    error-report projection. Completed slots are returned unchanged; a capability failure never
    starts another VALUE demand. -/
theorem sequence_builtin_item_demand_installs (rec : EvalRec) (item : CallableCallItem)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env = ((do
      if let some address := item.need? then
        if item.value?.isSome || item.error?.isSome then return item
        match <- evalAttempt (rec.demandNeedRecursive address) with
        | .ok value => return { item with value? := some value.fst }
        | .error err =>
            match item.source? with
            | some (.param _) => return { item with error? := some err }
            | _ =>
                let named? <- match <- evalAttempt (rec.projectNeedCallable address) with
                  | .ok (some carrier@(.alias _ _ _ _ _ false)) =>
                      match <- evalAttempt (rec.resolveAliasValueTarget carrier ctx) with
                      | .ok (.runtime _ _) => pure (some carrier)
                      | .ok terminal => pure (some terminal.alg)
                      | .error _ => pure (some carrier)
                  | .ok projected => pure projected
                  | .error _ => pure none
                return { item with error? := some err, callable? := named? }
      match item.value?, item.error?, item.algorithm? with
      | none, none, some alg =>
          if acceptsZeroArgumentValueDemand (item.callable?.getD alg) then
            match <- evalAttempt (rec.evalZeroArgumentDemandOutputCounted alg ctx env) with
            | .ok counted => pure { item with value? := some counted.fst }
            | .error err => pure { item with error? := some err }
          else pure item
      | _, _, _ => pure item) : EvalM CallableCallItem) := rfl

/-- The `first` dispatch: an argument view and a retained collector are read through their own
    selective readers; every other bound collection is `evalFirstCounted` of its prepared
    positions, the first one read (`forcePosition`, issue #204). A pending list is never bound
    pending to it (`pendingStageCandidates?`). -/
theorem first_arm (rec : EvalRec) (metadata : SequenceBuiltinMetadata)
    (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCountedSequence rec .firstBuiltin metadata args ctx env = ((do
      let bound <- rec.bindSequenceBuiltinArguments .firstBuiltin metadata args ctx env
      if let some a := bound.view? then
        return <- rec.evalArgumentViewBuiltin .firstBuiltin a
      if let some slice := bound.slice? then
        return <- retainedCollectorBuiltin rec.demandNeedRecursive .firstBuiltin metadata bound.suffixArgs slice
      if let some _ := bound.pending? then
        .error (builtinArityError .firstBuiltin args.length)
      match bound.preparedInput.items with
      | first :: rest => do evalFirstCounted ((<- forcePosition rec.demandNeedRecursive first) :: rest)
      | [] => evalFirstCounted []) : EvalM CountedResult) := rfl

/-- The `count` dispatch, likewise: an argument view and a retained collector are counted without a
    VALUE demand of their cells; every other bound collection is `evalCountCounted` of its prepared
    items. -/
theorem count_arm (rec : EvalRec) (metadata : SequenceBuiltinMetadata)
    (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCountedSequence rec .countBuiltin metadata args ctx env = ((do
      let bound <- rec.bindSequenceBuiltinArguments .countBuiltin metadata args ctx env
      if let some a := bound.view? then
        return <- rec.evalArgumentViewBuiltin .countBuiltin a
      if let some slice := bound.slice? then
        return <- retainedCollectorBuiltin rec.demandNeedRecursive .countBuiltin metadata bound.suffixArgs slice
      if let some _ := bound.pending? then
        .error (builtinArityError .countBuiltin args.length)
      evalCountCounted bound.preparedInput.items) : EvalM CountedResult) := rfl

/-- The `last` twin of `first_arm`. -/
theorem last_arm (rec : EvalRec) (metadata : SequenceBuiltinMetadata)
    (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCountedSequence rec .lastBuiltin metadata args ctx env = ((do
      let bound <- rec.bindSequenceBuiltinArguments .lastBuiltin metadata args ctx env
      if let some a := bound.view? then
        return <- rec.evalArgumentViewBuiltin .lastBuiltin a
      if let some slice := bound.slice? then
        return <- retainedCollectorBuiltin rec.demandNeedRecursive .lastBuiltin metadata bound.suffixArgs slice
      if let some _ := bound.pending? then
        .error (builtinArityError .lastBuiltin args.length)
      match bound.preparedInput.items.getLast? with
      | some last => do evalLastCounted [<- forcePosition rec.demandNeedRecursive last]
      | none => evalLastCounted []) : EvalM CountedResult) := rfl

/-- The prepared input of a collection builtin passes its EMPTY POLICY first: an empty collection
    under `requireSelectablePosition` (`first`, `last`) is `badIndex` under the "selects from an
    empty collection" context, before any helper runs. -/
theorem empty_selection_is_refused_by_the_policy (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput) (s : EvalState)
    (hp : metadata.emptyPolicy = .requireSelectablePosition) (h0 : collected.totalItemCount = 0) :
    (prepareSequenceBuiltinInput b metadata collected).runState s =
      (.error (Error.withContext
        s!"{builtinDisplayName b} selects from an empty collection, which has no position to select"
        Error.badIndex), s) := by
  unfold prepareSequenceBuiltinInput applySequenceBuiltinEmptyPolicy
  simp only [hp, h0]
  rfl

/-- The item the `map` transform and the `filter` predicate receive is `countedSequenceCallbackItem`
    of the iterated item, as ONE callback argument. -/
theorem callback_item_installs (rec : EvalRec) (callee : Algorithm) (item : CountedResult)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    rec.evalSequenceCallbackCallCounted callee item ctx env calleeName =
      rec.evalResolvedCallbackCallCounted callee [countedSequenceCallbackItem item] ctx env calleeName := rfl

/-- A DEFERRED APPLICATION's VALUE (lazy `reduce` accumulators, November 2026) is ONE dispatch of its
    resolved callee over its formed supply, with no callee origin, its own missing output stored
    as nested, at the call's value boundary — whatever the written-expression evaluator and the
    recursive demand are: neither is read. -/
theorem deferred_application_installs (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat) (callee : Algorithm)
    (cells : List NeedSupply.Sourced) (caller : EvalCtx) (values : ValEnv) (calleeName : String) :
    NeedDemand.suspendedValue ev route demand a (.applied callee cells caller values calleeName) =
      reCountValueBoundary <$> withNestedMissingOutput
        (route.dispatch .none callee cells caller values calleeName) := rfl

/-- ... and the production route's dispatch is the ordinary dispatch of a formed supply: a user
    algorithm's binder, a clause family's dispatch, a builtin's argument roles, an alias as its
    target (`evalSuppliedCallCounted`). -/
theorem deferred_application_dispatch_installs (rec : EvalRec) :
    rec.planRoute.dispatch = rec.evalSuppliedCallCounted := rfl

/-- A deferred application has no CALLABLE identity, whatever the written resolver is. -/
theorem deferred_application_has_no_callable (written : Expr → EvalCtx → EvalM (Option Algorithm))
    (callee : Algorithm) (cells : List NeedSupply.Sourced) (caller : EvalCtx) (values : ValEnv)
    (calleeName : String) :
    NeedProjection.suspended written (.applied callee cells caller values calleeName) = pure none := rfl

/-- ... and is no invocation plan, so META capture refuses it. -/
theorem deferred_application_is_no_plan (callee : Algorithm) (cells : List NeedSupply.Sourced)
    (caller : EvalCtx) (values : ValEnv) (calleeName : String) :
    NeedPlan.ofSuspension? (.applied callee cells caller values calleeName) = none := rfl

/-- One link of a fold's chain evaluates nothing: the element's Ready cell, then the DEFERRED
    APPLICATION of the reducer to that cell and the preceding accumulator cell. -/
theorem reduce_chain_step (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (accumulator : Nat)
    (item : CountedResult) (rest : List CountedResult) :
    EvalBody.evalReduceCounted.chain stepAlg ctx env accumulator (item :: rest) = ((do
      let element <- readyNeed (countedSequenceCallbackItem item)
      let step <- allocateNeed
        (.applied stepAlg [(element, none), (accumulator, none)] ctx env "reduce step")
      EvalBody.evalReduceCounted.chain stepAlg ctx env step rest) : EvalM Nat) := rfl

/-- The chain of no items is its accumulator. -/
theorem reduce_chain_end (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (accumulator : Nat) :
    EvalBody.evalReduceCounted.chain stepAlg ctx env accumulator [] = pure accumulator := rfl

/-- THE LAZY FOLD installs: the START is the deferred application of `reduce` itself to an empty
    collection and the supplied `initial` cell with its written slot — so its VALUE is `reduce`'s
    own empty case, and the reducer slot it carries is never projected —, the chain allocates one
    deferred step per element, and ONLY THE LAST cell is demanded: under the one reduce step frame
    when the collection has an element, as the start itself when it has none. -/
theorem reduce_fold_installs (rec : EvalRec) (collection : List CountedResult) (stepAlg : Algorithm)
    (start : NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalReduceCounted rec collection stepAlg start ctx env = ((do
      let empty <- readyNeed (Result.sequenceValue [], 0)
      let initial <- allocateNeed
        (.applied (.builtin .reduceBuiltin) [(empty, none), (empty, none), start] ctx env "reduce")
      let last <- EvalBody.evalReduceCounted.chain stepAlg ctx env initial collection
      let result <-
        if collection.isEmpty then rec.demandNeedRecursive last
        else withCtx reduceStepContext (rec.demandNeedRecursive last)
      pure (reCountValueBoundary result)) : EvalM CountedResult) := rfl

/-- THE INVOKING SLOT of a `while` round: the step is the loop step cell's CALLABLE read through
    `projectInvokingSlot`, then ONE condition-first round (`WhileRound.advance`). The `repeat`
    round reads its step the same way (`FiniteLoop.repeatDriver_succ`, `FiniteLoopCorrespondence.lean`), and the
    callback slots through `expectPreparedSequenceBuiltinAlgorithmSuffixArg`. -/
theorem while_round_installs (rec : EvalRec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx)
    (env : ValEnv) (stepName : String) (cells : List NeedSupply.Sourced) :
    EvalBody.whileLoop rec step ctx env stepName cells = ((do
      let algorithm <- projectInvokingSlot (invokingSlotRole .whileBuiltin) (<- rec.invokeNeed step)
      match <- WhileRound.advance (fun cells => rec.runNeedWhileRound algorithm ctx env cells stepName) cells with
      | .inl final => pure final
      | .inr next => rec.whileLoop step ctx env stepName (retainedSourced next)) :
        EvalM (List NeedSupply.Sourced)) := rfl

/-- A callback slot's supplied cell is read through its CALLABLE projection and the same
    invoking-slot rule; nothing is demanded for its VALUE. -/
theorem callback_slot_installs (rec : EvalRec) (b : Builtin)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg)
    (index : Nat) :
    EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index =
      expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .algorithm fun descriptor arg =>
        match arg with
        | .needAlgorithm address => do
            projectInvokingSlot (invokingSlotRole b) (<- rec.projectNeedCallable address)
        | .algorithm algorithm =>
            projectInvokingSlot (invokingSlotRole b) (some algorithm)
        | _ =>
            internalSequenceBuiltinSuffixArgMetadataError b
              s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .algorithm}" := rfl

/-- The `atoms` arm returns `atomsBuiltinResultForLaw` of its argument's VALUE, materialized
    (issue #204: `atoms` reads the whole value; an argument view is refused first). -/
theorem atoms_arm (rec : EvalRec) (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .atomsBuiltin [a] ctx env = withNestedMissingOutput ((do
      let r <- rec.evalArgumentValue a ctx env
      if let .argView _ := r then
        .error (Error.typeMismatch (argumentViewUnsupportedMessage "atoms"))
      let r <- materializeVia rec.demandNeedRecursive r
      pure (atomsBuiltinResultForLaw r)) : EvalM CountedResult) := rfl

/-- The `if` arm reads its condition through the Boolean view `Result.asBool?` — a number is a
    value-kind error, never a truth test — and re-counts the selected branch at its value
    boundary. -/
theorem if_arm (rec : EvalRec) (c t e : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .ifBuiltin [c, t, e] ctx env = withNestedMissingOutput ((do
      let cr <- rec.evalArgumentValue c ctx env
      match Result.asBool? cr with
      | some false => do
          let r <- rec.evalArgumentValueCounted e ctx env
          pure (r.fst, Result.valueCount r.fst)
      | some true => do
          let r <- rec.evalArgumentValueCounted t ctx env
          pure (r.fst, Result.valueCount r.fst)
      | none => .error (Error.typeMismatch (booleanRequiredMessage "if condition" cr))) :
        EvalM CountedResult) := rfl

/-- `and` / `or` SHORT-CIRCUIT. The left operand is evaluated and read through the Boolean view
    (`requireBooleanOperand`, which is `Result.asBool?`) BEFORE the right operand is looked at. When
    it decides the operator (`BinaryOp.leftOperandDecides`: `false and _`, `true or _`) the result is
    that Boolean and the right operand is not evaluated; otherwise the right operand is evaluated,
    read through the same view, and is the result. -/
theorem logical_arm (rec : EvalRec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
    (h : op = .and ∨ op = .or) :
    EvalBody.evalBinaryCounted rec op a b ctx env = ((do
      let lr <- rec.eval a ctx env
      let binaryContext := s!"while evaluating `{binaryExprDiagnosticName op a b}`"
      let x <- withCtx binaryContext (requireBooleanOperand op "left" lr)
      if op.leftOperandDecides x then
        pure (Result.bool x, 1)
      else do
        let rr <- rec.eval b ctx env
        let y <- withCtx binaryContext (requireBooleanOperand op "right" rr)
        pure (Result.bool y, 1)) : EvalM CountedResult) := by
  rcases h with rfl | rfl <;> rfl

/-- `xor` needs both operands: both are evaluated, left then right, and only then is each read
    through the Boolean view (`requireBooleanOperand`), the left one first. -/
theorem xor_arm (rec : EvalRec) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalBinaryCounted rec .xor a b ctx env = ((do
      let lr <- rec.eval a ctx env
      let rr <- rec.eval b ctx env
      let binaryContext := s!"while evaluating `{binaryExprDiagnosticName .xor a b}`"
      let x <- withCtx binaryContext (requireBooleanOperand .xor "left" lr)
      let y <- withCtx binaryContext (requireBooleanOperand .xor "right" rr)
      pure (Result.bool (x != y), 1)) : EvalM CountedResult) := rfl

/-- THE SKIPPED OPERAND HAS NO EFFECT. When the left operand of `and` / `or` completes with a
    Boolean that decides the operator, the expression completes with that Boolean in the state
    the LEFT operand left: whatever the right operand is, nothing of it ran. -/
theorem logical_arm_decided (rec : EvalRec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
    (h : op = .and ∨ op = .or) (s s' : EvalState) (lr : Result) (x : Bool)
    (hleft : (rec.eval a ctx env).runState s = (.ok lr, s'))
    (hbool : Result.asBool? lr = some x) (hdecides : op.leftOperandDecides x = true) :
    (EvalBody.evalBinaryCounted rec op a b ctx env).runState s = (.ok (Result.bool x, 1), s') := by
  -- The left operand's Boolean check completes with `x` and leaves the state alone.
  have hcheck : ∀ c : String,
      (withCtx c (requireBooleanOperand op "left" lr)).runState s' = (.ok x, s') := by
    intro c
    have hrequire : (requireBooleanOperand op "left" lr).runState s' = (.ok x, s') := by
      simp only [requireBooleanOperand, hbool]
      rfl
    unfold withCtx
    rw [EvalM.bind_runState, evalAttempt_runState_of_complete _ s' s' (.ok x) hrequire rfl]
    rfl
  rw [logical_arm rec op a b ctx env h, EvalM.bind_runState, hleft]
  dsimp only
  rw [EvalM.bind_runState, hcheck]
  simp only [hdecides, if_true]
  rfl

/-- A failing left operand of `and` / `or` is the expression's outcome, in the state the left
    operand left: the right operand is not evaluated. -/
theorem logical_arm_left_failure (rec : EvalRec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
    (h : op = .and ∨ op = .or) (s s' : EvalState) (err : Error)
    (hleft : (rec.eval a ctx env).runState s = (.error err, s')) :
    (EvalBody.evalBinaryCounted rec op a b ctx env).runState s = (.error err, s') := by
  rw [logical_arm rec op a b ctx env h, EvalM.bind_runState, hleft]

/-- One `filter` step: the predicate is the callback call on the item as collected, and its result
    is read through the Boolean view — a non-Boolean result is a value-kind error, never a truth
    test. -/
theorem filter_step (rec : EvalRec) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (item : CountedResult) (rest : List CountedResult) :
    EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index (item :: rest) = ((do
      match <- evalAttempt (withCtx (s!"while evaluating filter predicate for item {index}: {resultDiagnosticString item.fst} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)") <|
        rec.evalSequenceCallbackCall predicateAlg item ctx env "filter predicate") with
        | .error err =>
            .error err
        | .ok pr =>
            match Result.asBool? pr with
            | some true => do
                let kept <- EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env (index + 1) rest
                pure (item.fst :: kept)
            | some false =>
                EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env (index + 1) rest
            | none =>
                .error (Error.typeMismatch
                  (booleanRequiredMessage "filter predicate result" pr))) : EvalM (List Result)) := by
  rw [EvalBody.evalFilterCounted.filterLoop]
  rfl

/-- The ARITY GATE of a collection builtin: a supply whose length is not one collection plus the
    fixed controls is `arityMismatch`, before any argument is demanded and with the state unchanged.
    It reads the metadata's control count only (never `slotRole`). -/
theorem sequence_builtin_arity_gate (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (h : (collectSequenceCallableCallItems args).length ≠ 1 + metadata.suffixArgs.length) :
    (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env).runState s =
      (.error (Error.arityMismatch (1 + metadata.suffixArgs.length)
        (collectSequenceCallableCallItems args).length), s) := by
  unfold EvalBody.bindSequenceBuiltinArguments
  simp only [bne_iff_ne, ne_eq, h, not_false_eq_true, ↓reduceIte]
  rfl

/-- A VALUE slot of a builtin over a supplied cell is that cell's ONE recursive VALUE demand. -/
theorem argument_value_of_a_cell (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx)
    (env : ValEnv) (address : Nat) (h : arg.need? = some address) :
    EvalBody.evalArgumentValueCounted rec arg ctx env = rec.demandNeedRecursive address := by
  unfold EvalBody.evalArgumentValueCounted
  simp only [h]

/-! ## 6. The call-reference intrinsics, the argument view and the spread capability -/

/-- `Invoke` over a call reference installs `NeedPlan.invoke` at the evaluator's plan route. -/
theorem invoke_installs (rec : EvalRec) (a : Nat) :
    EvalBody.invokeCallReferenceValue rec (.callRef a) = NeedPlan.invoke rec.planRoute ⟨a⟩ := rfl

/-- Production: a completed `Invoke` of a call reference is `invokeNeedCall` of it — the plan's
    fresh execution at `productionPlanRoute`. -/
theorem invoke_production (a : Nat) (s : EvalState)
    (hc : ProductionCompletes (invokeCallReferenceValue (.callRef a)) s) :
    (invokeCallReferenceValue (.callRef a)).runState s = (invokeNeedCall ⟨a⟩).runState s :=
  production_installed (.invokeCallReferenceValue (.callRef a))
    (fun rec => NeedPlan.invoke rec.planRoute ⟨a⟩) (fun _ => rfl) s hc

/-- The argument view's cells install `NeedPlan.viewCells` over the evaluator's spread capability
    and route classifier. -/
theorem view_cells_installs (rec : EvalRec) (a : Nat) :
    EvalBody.argumentViewCells rec a = NeedPlan.viewCells rec.evalSupplySpread rec.planRoute.classify a := rfl

/-- `count`/`first`/`last` over an argument view install `argumentViewBuiltin` over those cells and
    the recursive VALUE demand. -/
theorem view_builtin_installs (rec : EvalRec) (b : Builtin) (a : Nat) :
    EvalBody.evalArgumentViewBuiltin rec b a =
      argumentViewBuiltin (rec.argumentViewCells a) (fun cell => Prod.fst <$> rec.demandNeedRecursive cell) b := rfl

/-- The `.Algorithm` intrinsic over its receiver's VALUE: the decoded plan's canonical callee cell
    (`NeedPlan.calleeCell`) — bare, its VALUE at the value boundary; with arguments, a FRESH
    ordinary call of its CALLABLE with exactly the written arguments. -/
theorem algorithm_intrinsic_installs (rec : EvalRec) (val : Result) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.algorithmOfValue rec val args? ctx env = ((do
      let plan <- decodeCallRef val
      let callee <- NeedPlan.calleeCell rec.planRoute.classify plan
      match args? with
      | none => reCountValueBoundary <$> rec.demandNeedRecursive callee
      | some args =>
          let algorithm <- rec.capturedCallee callee
          rec.evalResolvedCallCounted algorithm args ctx env (<- NeedPlan.calleeName plan) (.cell callee)) :
        EvalM CountedResult) := rfl

/-- The spread evaluation: the operand is evaluated ONCE (one `evalSequenceSpreadOperandValue` of
    the peeled operand), every level a written star opens is read in order (`peelSpreadLayers` over
    `forceLevel`, issue #204), and the opening is the total checked `openSpreadItems`; the result
    is `spreadSupplyResult`. -/
theorem spread_installs (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalSequenceSpreadCounted rec e ctx env = ((do
      let (operand, layers) := peelSequenceSpreadLayers e 0
      let value <- rec.evalSequenceSpreadOperandValue operand ctx env
      let (remaining, opened) <- peelSpreadLayers (forceLevel rec.demandNeedRecursive) (layers - 1) value
      let supplied <- openSpreadItems remaining opened
      pure (spreadSupplyResult supplied)) : EvalM CountedResult) := rfl

/-- The spread capability of supply formation: a transparent reference to a retained collector
    contributes that collector's cells and evaluates nothing; a computed spread evaluates its
    operand ONCE and opens it with `openSupplySpread`, an argument view contributing its ORIGINAL
    cells (`NeedPlan.viewSupply`). -/
theorem supply_spread_installs (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalSupplySpread rec e ctx env = ((do
      match <- EvalBody.transparentCollectorSlice? rec e ctx with
      | some slice =>
        pure (.cells (<- slice.mapM (fun a => do pure (a, <- needWrittenSource? a))))
      | none =>
        let (operand, layers) := peelSequenceSpreadLayers e 0
        let value <- rec.evalSequenceSpreadOperandValue operand ctx env
        let (remaining, opened) <- peelSpreadLayers (forceLevel rec.demandNeedRecursive) (layers - 1) value
        match <- openSupplySpread remaining opened with
        | .items supplied => pure (.items (countedTopLevelValues (spreadSupplyResult supplied)))
        | .view a => NeedPlan.viewSupply rec.evalSupplySpread rec.planRoute.classify a) :
        EvalM SpreadSupply) := rfl

/-- An argumentless structural member read installs the ordinary zero-argument demand and
    re-counts its result, including a runtime alias's VALUE terminal. Selection and the receiver
    probe remain explicit arm conditions, as in the intrinsic arms below. -/
theorem dot_member_read_installs (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (receiver? : Option Algorithm)
    (owner : Algorithm) (binding : PropDef)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.ok receiver?, s'))
    (hmember : selectDotEdge ctx target name receiver? = .ok (.member owner binding)) :
    (EvalBody.evalDotCallCounted rec target name fallback none ctx env).runState s = ((do
      match <- rec.resolveAliasValueTarget (childOfInContext owner binding.alg ctx) ctx with
      | terminal@(.runtime _ _) => reCountValueBoundary <$> EvalBody.terminalAccess rec terminal ctx env
      | terminal =>
        let wired := terminal.alg
        match flatBinderUserEquivalent? wired with
        | some simple =>
            if acceptsZeroArgumentValueDemand simple then
              reCountValueBoundary <$> withMissingOutputNesting terminal.nested
                (rec.evalZeroArgPropertyAccessCounted .structural (terminal.ownerOr owner)
                  (terminal.bindingOr binding) simple ctx env)
            else
              .error (Error.arityMismatch
                (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns simple)) 0)
        | none =>
            if acceptsZeroArgumentValueDemand wired then
              reCountValueBoundary <$> withMissingOutputNesting terminal.nested
                (rec.evalZeroArgPropertyAccessCounted .structural (terminal.ownerOr owner)
                  (terminal.bindingOr binding) wired ctx env)
            else
              match wired with
              | .conditional _ _ _ _ => .error (Error.noMatchingBranch name)
              | _ => .error (Error.arityMismatch
                  (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns wired)) 0)) :
        EvalM CountedResult).runState s' := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]
  simp only [hmember]
  rfl

/-- The dot route's `Invoke` arm over a value receiver: the argument-list route fact, ONE read of
    the receiver, then `invokeCallReferenceValue`. -/
theorem dot_invoke_arm (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.ok none, s'))
    (hmiss : selectDotEdge ctx target name none = .ok (.miss .invoke)) :
    (EvalBody.evalDotCallCounted rec target name fallback args? ctx env).runState s =
      ((do
        rec.rejectInvokeIntrinsicArguments args? ctx env
        let val <- withNestedMissingOutput (rec.eval target ctx env)
        rec.invokeCallReferenceValue val) : EvalM CountedResult).runState s' := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]
  simp only [hmiss]

/-- The dot route's `Arguments` arm over a value receiver: the argument-list route fact, ONE read
    of the receiver, then the view (`argumentsOfValue`). Nothing else runs. -/
theorem dot_arguments_arm (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.ok none, s'))
    (hmiss : selectDotEdge ctx target name none = .ok (.miss .arguments)) :
    (EvalBody.evalDotCallCounted rec target name fallback args? ctx env).runState s =
      ((do
        rejectArgumentsIntrinsicArguments args?
        let val <- withNestedMissingOutput (rec.eval target ctx env)
        argumentsOfValue val) : EvalM CountedResult).runState s' := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]
  simp only [hmiss]

/-- The dot route's `Algorithm` arm over a value receiver: ONE read of the receiver, then the
    intrinsic (`algorithm_intrinsic_installs`). -/
theorem dot_algorithm_arm (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.ok none, s'))
    (hmiss : selectDotEdge ctx target name none = .ok (.miss .algorithm)) :
    (EvalBody.evalDotCallCounted rec target name fallback args? ctx env).runState s =
      ((do
        let val <- withNestedMissingOutput (rec.eval target ctx env)
        rec.algorithmOfValue val args? ctx env) : EvalM CountedResult).runState s' := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]
  simp only [hmiss]

/-- The link arm of a written call: a callee `X.Algorithm` on the intrinsic route is the captured
    callee (`algorithmCalleeOf`), called FRESH with the written arguments under the callee cell's
    origin; every other callee is the ONE callee law (`callee_installs`). -/
theorem written_call_installs (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) :
    EvalBody.evalCallCountedExpr rec f args ctx env = ((do
      if let some (receiver, _) := linkEdge? f then
        if <- withCtx (CtxMsg.call f) (rec.algorithmIntrinsicRoute receiver ctx) then
          let (callee, calleeName, calleeCell) <- withCtx (CtxMsg.call f) (rec.algorithmCalleeOf receiver ctx env)
          return <- withCtx (CtxMsg.call f) <| rec.evalResolvedCallCounted callee args ctx env calleeName (.cell calleeCell)
      let callee <- withCtx (CtxMsg.call f) <| rec.resolveCalleeAlg f ctx
      withCtx (CtxMsg.call f) <| rec.evalResolvedCallCounted callee args ctx env (openExprName f) (.written f ctx)) :
        EvalM CountedResult) := rfl

/-! ## 7. Rows and captures -/

/-- The shared output-row loop, at its end: the collected slots are combined SHALLOWLY by
    `combineOutputSlots` and returned with the emitted count the rows accumulated. -/
theorem rows_combine_shallowly (rec : EvalRec) (rowCtx : EvalCtx) (env : ValEnv) (acc : List Result)
    (emitted : Nat) :
    EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env [] acc emitted =
      pure { counted := (combineOutputSlots acc.reverse, emitted), outputSlots := acc.reverse } := by
  unfold EvalBody.evalOutputRowsPreparedCore.collect
  rfl

/-- The shared output-row loop, one row: the row is ONE counted evaluation (a subordinate
    computation); a SPREAD row contributes its recovered top-level values
    (`countedTopLevelValues`) and its emitted count, a non-spread row exactly ONE slot — `()`
    included, whose zero count is emitted as one. -/
theorem rows_step (rec : EvalRec) (rowCtx : EvalCtx) (env : ValEnv) (expr : Expr) (rest : List Expr)
    (acc : List Result) (emitted : Nat) :
    EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env (expr :: rest) acc emitted = ((do
      let out <- withNestedMissingOutput (rec.evalCounted expr rowCtx env)
      match expr with
      | .sequenceSpread _ =>
          EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rest
            ((countedTopLevelValues out).reverse ++ acc) (emitted + out.snd)
      | _ =>
          let slotCount := if out.snd = 0 then 1 else out.snd
          EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rest (out.fst :: acc)
            (emitted + slotCount)) : EvalM PreparedAlgorithmOutput) := by
  rw [EvalBody.evalOutputRowsPreparedCore.collect]
  rfl

/-- A capture's rows run that loop in the SURROUNDING context (a capture owns no scope). -/
theorem capture_rows_install (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalOutputRowsPreparedCore rec rows ctx env =
      EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rows [] 0 := rfl

/-! ## 8. The heap never shrinks under production

`NeedControl.lean` composes heap-size contracts over a supply formation and a collector traversal
under a premise on the callbacks (`formation_nonshrinking`, `collector_nonshrinking`), and
`BinderCorrespondence.lean` reads "the channels never shrink the heap" as support for its schedule
freshness premise. For the production callbacks these are consequences of the whole-run heap
discipline (`EvaluatorDiscipline.evalUnbounded_disciplined`): an operation that keeps every existing
cell keeps the heap's size. -/

open KatLang.CallPlan KatLang.NeedControl.Allocation in
/-- A disciplined computation never shrinks the heap. -/
theorem nonshrinking_of_disciplined {α : Type} (m : EvalM α) (h : Disciplined m) : Nonshrinking m := by
  intro s
  rcases Nat.eq_zero_or_pos s.needs.size with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hlt : s.needs.size - 1 < s.needs.size := Nat.sub_lt hpos Nat.one_pos
    obtain ⟨c', hc', -⟩ := h s (s.needs.size - 1) s.needs[s.needs.size - 1] (Array.getElem?_eq_getElem hlt)
    have hlt' : s.needs.size - 1 < (m.runState s).2.needs.size := by
      rcases Nat.lt_or_ge (s.needs.size - 1) (m.runState s).2.needs.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hc'; cases hc'
    omega

open KatLang.NeedControl.Allocation in
/-- **Every production evaluator operation keeps the heap's size or grows it**, from every state. -/
theorem production_nonshrinking (c : EvalCall) : Nonshrinking (evalUnbounded c) :=
  nonshrinking_of_disciplined _ (KatLang.EvaluatorDiscipline.evalUnbounded_disciplined c)

open KatLang.NeedControl.Allocation in
/-- The recursive VALUE edge never shrinks the heap: the callback premise of
    `NeedControl.Production.collector_nonshrinking`, at production. -/
theorem production_demand_nonshrinking (address : Nat) : Nonshrinking (demandNeedRecursive address) :=
  production_nonshrinking (.demandNeedRecursive address)

open KatLang.NeedControl.Allocation in
/-- The production supply formation never shrinks the heap: `formation_nonshrinking` with its slot
    premise discharged for the evaluator's spread capability. -/
theorem production_formation_nonshrinking (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Nonshrinking (formNeedSupplySourced args ctx env) :=
  nonshrinking_of_disciplined _
    (KatLang.CallPlan.disciplined_form evalSupplySpread
      (fun e c v => KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.evalSupplySpread e c v)) ctx env args)

end KatLang.EvaluatorInstallation
