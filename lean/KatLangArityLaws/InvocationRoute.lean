import KatLangArityLaws.MetaLoop
import KatLangArityLaws.EvaluatorDiscipline

open KatLang KatLang.CallPlan

/-!
# META-S3-4: the generalized invocation domain and the plan ROUTE (October 2026)

META captures every WRITTEN invocation — `f(args)` with a name, parameter or argumentless dot-path
callee, and every argument-bearing dot edge `t.N(args)` — independently of how the callee is
reached. The authoritative definitions are in `lean/KatLang.lean`:

* `NeedPlan.callShape?` — the syntactic, total, evaluation-free invocation domain (CR-2, D-2A);
* `selectDotEdge` — THE dot-edge route decision over the receiver's typed identity, used by
  ordinary dot evaluation (`evalDotCallCounted`), the `.Algorithm` route fact
  (`algorithmIntrinsicRoute`) and the plan route (`classifyPlanRouteWith`) alike;
* `NeedPlan.routeOf` — the plan's ONE route, classified by the first route-dependent operation and
  recorded in `NeedCell.route` (first writer wins);
* `NeedPlan.effective` — the shape a route invokes (an extension is `F(t, args)`, D-5);
* `NeedPlan.calleeCell` / `viewCells` / `execute` / `executeAlong` / `NeedDemand.suspendedValue` —
  the route-aware callee cell (CR-13), argument view (CR-9, D-4), invocation and original VALUE
  (D-1A for non-callable intrinsics).

Proved here over those definitions (the general plan laws are in `InvocationPlan.lean`,
`AlgorithmProjection.lean` and `ArgumentView.lean`):

* **Domain** — exactly the written invocation forms are plans (`callShape_supported`), an
  argumentless dot edge never is (`argumentless_edge_not_plan`), and capture of every new form is
  the same pure read (`dot_capture_inert`).
* **Route stickiness** — a recorded route is returned as it is (`routeOf_recorded`), a successful
  first classification records exactly its result (`routeOf_records`), and no disciplined
  computation ever rewrites the record (`route_survives`).
* **Route agreement with ordinary dot dispatch** — the dot-form route is the plan-route image of
  the SAME `selectDotEdge` decision ordinary evaluation branches on (`classify_dot`,
  `evalDotCallCounted_selects`), member-first whatever the spelling (`declared_member_wins`), with a
  selection failure the route's failure (`selection_failure_is_route_failure`); the call form
  consults the `.Algorithm` route fact exactly when its callee is an `X.Algorithm` edge
  (`classify_call_link`, `classify_call_plain` — the latter evaluates nothing).
* **Callee identity and supply** — each route's callee and effective bundle
  (`member_effective`, `algorithm_effective`, `extension_effective`: the receiver is the FIRST
  supplied argument, D-5), and the extension's effective shape is the shape of the written call
  `F(t, args)` (`extension_is_written_call`).
* **D-1A** — an intrinsic route has no callee cell, no argument supply and no invocation
  (`calleeCell_intrinsic`, `viewCells_intrinsic`, `execute_intrinsic`), while its original VALUE is
  the ordinary evaluation (`suspended_intrinsic_is_ordinary`).
* **Failure preservation** — a route failure is the execution's failure, with nothing executed
  (`execute_route_failure`).
* **Establishment discipline** — route establishment is disciplined (`production_routeOf_disciplined`),
  and callee-cell allocation is inert AFTER route establishment (`calleeCell_inert`), while
  establishing the route may legitimately demand a runtime-projection receiver
  (`calleeCell_route_first`): NOT every route is resolvable without evaluation.
* **Distinct plans, shared cells** — two written invocations are two plans
  (`written_invocations_distinct`); a rebuilt `op.Algorithm(op.Arguments*)` prepares the ORIGINAL
  argument cells of `op` (`ArgumentViewLaws.view_spread_slot`, restated as `rebuilt_supply_slot`).
* **Dispatch names** (META-S3-4-DIAG, October 20 2026) — every route but `.Algorithm` keeps its
  effective written callee (`dispatchName_ordinary`); the `.Algorithm` route names the CAPTURED
  plan's callee (`dispatchName_algorithm`), which is exactly the ordinary intrinsic's `calleeName`
  (`planned_name_is_ordinary_name`); the name is a pure heap read (`dispatchName_inert`), and the
  correction changes nothing but the string dispatch receives (`executeAlong_changes_only_the_name`).

NOT claimed: kernel refinement of whole runs (the executable `InvocationRouteGuards` pin whole
programs); the error-context strings of the extension route against `callLexicalWithReceiverCounted`
beyond the shared `CtxMsg.dotCall` frame; C# async route resolution, the C# CAS, cancellation, J7
retention and expression-checkpoint accounting (C#-only, `InvocationRouteTests`).
-/

namespace KatLang.InvocationRouteLaws

/-! ## The domain -/

/-- Capture of an argument-bearing dot edge is the same pure read as every capture: the plan's own
    reference, the state unchanged (CR-2: nothing resolved, executed, prepared or demanded). -/
theorem dot_capture_inert (a : Nat) (s : EvalState) (cell : NeedCell)
    (r : Expr) (n : Ident) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (hc : s.needs[a]? = some cell) (hsus : cell.suspension = .expression (.dotMember r n fb (some args)) c v) :
    (NeedPlan.reify a).runState s = (.ok ⟨a⟩, s) :=
  reify_identity a s ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩
    (by simp [NeedPlan.shapeAt?, hc, hsus, NeedPlan.ofSuspension?, dot_edge_shape])

/-- The intrinsic-shaped `5.string()` is a plan by its written form (D-1A: capture never asks
    whether the route is callable). -/
theorem intrinsic_shape_is_plan (c : EvalCtx) (v : ValEnv) :
    (NeedPlan.callShape? (.dotMember (.num 5) "string" (.resolve "string") (some [])) c v).isSome = true := rfl

/-! ## Route stickiness -/

/-- **A successful first classification records its result.** Whatever the classifier did, after a
    successful `routeOf` the plan cell's route record is exactly the returned route (given a
    disciplined classifier, which keeps the cell). -/
theorem routeOf_records (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, Disciplined (classify shape)) (a : Nat) (shape : NeedPlan.CallShape)
    (s t : EvalState) (r : PlanRoute) (cell : NeedCell) (hc : s.needs[a]? = some cell)
    (h : (NeedPlan.routeOf classify a shape).runState s = (.ok r, t)) :
    ∃ d, t.needs[a]? = some d ∧ d.route = some r := by
  cases hr : cell.route with
  | some r0 =>
    rw [routeOf_recorded classify a shape s cell r0 hc hr] at h
    cases h
    exact ⟨cell, hc, hr⟩
  | none =>
    rw [routeOf_fresh classify a shape s cell hc hr] at h
    have k := hclassify shape s
    rcases hcl : (classify shape).runState s with ⟨_ | r1, t1⟩ <;> rw [hcl] at h k
    · cases h
    · obtain ⟨c1, hc1, _⟩ := k a cell hc
      dsimp only at hc1 h
      simp only [recordRoute] at h
      cases hb : (t1.needs[a]?).bind NeedCell.route with
      | some recorded =>
        rw [hb] at h
        cases h
        rw [hc1] at hb
        exact ⟨c1, hc1, hb⟩
      | none =>
        rw [hb] at h
        cases h
        exact ⟨{ c1 with route := some r1 }, by simp [withRoute, modify_get, hc1], rfl⟩

/-- **Route stickiness across computations.** No disciplined computation — VALUE, `Invoke()`, the
    argument view, a loop, a nested classification — ever rewrites a recorded route. -/
theorem route_survives {α : Type} (m : EvalM α) (hm : Disciplined m) (a : Nat) (s : EvalState)
    (cell : NeedCell) (r : PlanRoute) (hc : s.needs[a]? = some cell) (hr : cell.route = some r) :
    ∃ d, (m.runState s).2.needs[a]? = some d ∧ d.route = some r := by
  obtain ⟨d, hd, k⟩ := hm s a cell hc
  exact ⟨d, hd, k.routed r hr⟩

/-- **Route determinism.** After a first successful classification, every later `routeOf` (after any
    disciplined computation) returns the SAME route, classifies nothing and changes nothing. -/
theorem routeOf_deterministic (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, Disciplined (classify shape)) (a : Nat) (shape : NeedPlan.CallShape)
    (s t : EvalState) (r : PlanRoute) (cell : NeedCell) (hc : s.needs[a]? = some cell)
    (h : (NeedPlan.routeOf classify a shape).runState s = (.ok r, t))
    {α : Type} (m : EvalM α) (hm : Disciplined m) (shape' : NeedPlan.CallShape) :
    (NeedPlan.routeOf classify a shape').runState (m.runState t).2 = (.ok r, (m.runState t).2) := by
  obtain ⟨d, hd, hdr⟩ := routeOf_records classify hclassify a shape s t r cell hc h
  obtain ⟨e, he, her⟩ := route_survives m hm a t d r hd hdr
  exact routeOf_recorded classify a shape' _ e r he her

/-! ## Route agreement with ordinary dot dispatch -/

/-- The plan route of a dot-edge selection: a declared member is an ordinary call of its path, a
    miss its `DotMiss.planRoute`, a selection failure the route's failure. -/
def routeOfSelection : Except Error DotSelection → Except Error PlanRoute
  | .error e => .error e
  | .ok (.member _ _) => .ok .call
  | .ok (.miss kind) => .ok kind.planRoute

/-- **The dot-form route IS the ordinary selection's image.** Classifying an argument-bearing dot
    edge resolves its receiver's typed identity once, then decides through `selectDotEdge` — the
    same decision ordinary dot evaluation branches on (`evalDotCallCounted_selects`). -/
theorem classify_dot (resolve : Expr → EvalCtx → EvalM (Option Algorithm))
    (algorithmRoute : Expr → EvalCtx → EvalM Bool) (callee : Expr) (args : OutputBundle)
    (caller : EvalCtx) (values : ValEnv) (r : Expr) (n : Ident) (fb : Expr) (s : EvalState) :
    (classifyPlanRouteWith resolve algorithmRoute ⟨callee, args, caller, values, .dot r n fb⟩).runState s =
      (match (resolve r caller).runState s with
       | (.ok target, t) => (routeOfSelection (selectDotEdge caller r n target), t)
       | (.error e, t) => (.error e, t)) := by
  simp only [classifyPlanRouteWith, bind_run]
  rcases (resolve r caller).runState s with ⟨_ | target, t⟩
  · rfl
  · dsimp only
    cases selectDotEdge caller r n target with
    | error e => rfl
    | ok sel => cases sel <;> rfl


/-- **Agreement on a selection failure** (failure is not absence, NEED-06). When the receiver's
    identity resolves to `target` and the ordinary selection fails — an inaccessible member, a
    branch-only member — ordinary dot evaluation and the plan route fail with the SAME error from
    the SAME state: the plan never falls back to a lexical extension. -/
theorem selection_failure_agrees (rec : EvalRec) (r : Expr) (n : Ident) (fb : Expr)
    (argsOpt : Option OutputBundle) (callee : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (target : Option Algorithm) (e : Error)
    (hres : (rec.resolveDotReceiver? r ctx).runState s = (.ok target, t))
    (hsel : selectDotEdge ctx r n target = .error e) :
    (EvalBody.evalDotCallCounted rec r n fb argsOpt ctx env).runState s = (.error e, t) ∧
    (classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute
      ⟨callee, args, ctx, env, .dot r n fb⟩).runState s = (.error e, t) := by
  refine ⟨?_, ?_⟩
  · simp only [EvalBody.evalDotCallCounted, bind_run, hres, hsel]; rfl
  · rw [classify_dot, hres]; simp only [routeOfSelection, hsel]

/-- **Agreement on a declared member** (structural first): the plan route is an ordinary call of
    the member path, and ordinary evaluation of `t.N(args)` calls the selected member's CALLABLE
    target over the written arguments. -/
theorem member_agrees (rec : EvalRec) (r : Expr) (n : Ident) (fb : Expr)
    (args : OutputBundle) (callee : Expr) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (target : Option Algorithm) (targetAlg : Algorithm) (p : PropDef)
    (hres : (rec.resolveDotReceiver? r ctx).runState s = (.ok target, t))
    (hsel : selectDotEdge ctx r n target = .ok (.member targetAlg p)) :
    (EvalBody.evalDotCallCounted rec r n fb (some args) ctx env).runState s =
      ((do
        let wired ← rec.resolveAliasTarget (childOfInContext targetAlg p.alg ctx) ctx
        rec.evalResolvedCallCounted wired args ctx env n) : EvalM CountedResult).runState t ∧
    (classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute
      ⟨callee, args, ctx, env, .dot r n fb⟩).runState s = (.ok .call, t) := by
  refine ⟨?_, ?_⟩
  · simp only [EvalBody.evalDotCallCounted, bind_run, hres, hsel]
  · rw [classify_dot, hres]; simp only [routeOfSelection, hsel]

/-- **Agreement on the extension route** (DOT-03): on any other structural miss, ordinary
    evaluation is the lexical call with the receiver first, and the plan route is `extension`. -/
theorem extension_agrees (rec : EvalRec) (r : Expr) (n : Ident) (fb : Expr)
    (args : OutputBundle) (callee : Expr) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (target : Option Algorithm)
    (hres : (rec.resolveDotReceiver? r ctx).runState s = (.ok target, t))
    (hsel : selectDotEdge ctx r n target = .ok (.miss .extension)) :
    (EvalBody.evalDotCallCounted rec r n fb (some args) ctx env).runState s =
      (rec.callLexicalWithReceiverCounted n r fb (some args) ctx env).runState t ∧
    (classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute
      ⟨callee, args, ctx, env, .dot r n fb⟩).runState s = (.ok .extension, t) := by
  refine ⟨?_, ?_⟩
  · simp only [EvalBody.evalDotCallCounted, bind_run, hres, hsel]
  · rw [classify_dot, hres]; simp only [routeOfSelection, hsel, DotMiss.planRoute]

/-- **Agreement on the `.Algorithm` intrinsic** (CR-14 c): on a structural miss of `Algorithm`,
    ordinary evaluation applies the intrinsic, and the plan route is `algorithm`. -/
theorem algorithm_agrees (rec : EvalRec) (r : Expr) (fb : Expr)
    (args : OutputBundle) (callee : Expr) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (target : Option Algorithm)
    (hres : (rec.resolveDotReceiver? r ctx).runState s = (.ok target, t))
    (hsel : selectDotEdge ctx r "Algorithm" target = .ok (.miss .algorithm)) :
    (classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute
      ⟨callee, args, ctx, env, .dot r "Algorithm" fb⟩).runState s = (.ok .algorithm, t) := by
  rw [classify_dot, hres]; simp only [routeOfSelection, hsel, DotMiss.planRoute]

/-- **A declared member wins, whatever its spelling** (Q-17 S-C): an accessible declared member —
    one named `Algorithm`, `Invoke`, `string` or `Arguments` included — is selected before any
    intrinsic or lexical fallback is considered. -/
theorem declared_member_wins (ctx : EvalCtx) (r : Expr) (n : Ident) (targetAlg : Algorithm) (p : PropDef)
    (hp : Algorithm.lookupPropDefAny? targetAlg n = some p) (ha : memberAccessible? ctx targetAlg p = true) :
    selectDotEdge ctx r n (some targetAlg) = .ok (.member targetAlg p) := by
  simp [selectDotEdge, hp, ha]

/-- A branch-only member is the local-only error, never a miss (no lexical fallback). -/
theorem branch_only_member_fails (ctx : EvalCtx) (r : Expr) (n : Ident) (targetAlg : Algorithm)
    (hp : Algorithm.lookupPropDefAny? targetAlg n = none)
    (hb : Algorithm.conditionalBranchesDefineProperty targetAlg n = true) :
    selectDotEdge ctx r n (some targetAlg) =
      .error (Error.localOnlyProperty (openExprName r) n .localConditional) := by
  simp [selectDotEdge, hp, hb]

/-- A value receiver declares no member: the miss route by spelling. -/
theorem value_receiver_misses (ctx : EvalCtx) (r : Expr) (n : Ident) :
    selectDotEdge ctx r n none = .ok (.miss (DotMiss.ofName n)) := rfl

/-- The `.Algorithm` route fact is the same selection (`algorithmIntrinsicRoute`): the intrinsic
    exactly when the selection of `Algorithm` is its miss. -/
theorem algorithmIntrinsicRoute_selects (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx) :
    EvalBody.algorithmIntrinsicRoute rec receiver ctx = (do
      match selectDotEdge ctx receiver "Algorithm" (← rec.resolveDotReceiver? receiver ctx) with
      | .ok (.miss .algorithm) => pure true
      | _ => pure false) := rfl

/-- **The call form consults the `.Algorithm` route fact exactly for an `X.Algorithm` callee**
    (`(t.Algorithm)(args)`, as `evalCallCountedExpr` does). -/
theorem classify_call_link (resolve : Expr → EvalCtx → EvalM (Option Algorithm))
    (algorithmRoute : Expr → EvalCtx → EvalM Bool) (receiver fb : Expr) (args : OutputBundle)
    (caller : EvalCtx) (values : ValEnv) (s : EvalState) :
    (classifyPlanRouteWith resolve algorithmRoute
      ⟨.dotMember receiver "Algorithm" fb none, args, caller, values, .call⟩).runState s =
      (match (algorithmRoute receiver caller).runState s with
       | (.ok true, t) => (.ok .algorithm, t)
       | (.ok false, t) => (.ok .call, t)
       | (.error e, t) => (.error e, t)) := by
  simp only [classifyPlanRouteWith, linkEdge?, if_true, bind_run]
  rcases (algorithmRoute receiver caller).runState s with ⟨_ | b, t⟩
  · rfl
  · cases b <;> rfl

/-- **A plain written call classifies without evaluating anything**: its route is `call` and the
    state is unchanged (a name or parameter callee needs no route decision at all). -/
theorem classify_call_plain (resolve : Expr → EvalCtx → EvalM (Option Algorithm))
    (algorithmRoute : Expr → EvalCtx → EvalM Bool) (callee : Expr) (args : OutputBundle)
    (caller : EvalCtx) (values : ValEnv) (s : EvalState) (h : linkEdge? callee = none) :
    (classifyPlanRouteWith resolve algorithmRoute ⟨callee, args, caller, values, .call⟩).runState s =
      (.ok .call, s) := by
  simp only [classifyPlanRouteWith, h]
  rfl

/-! ## Callee identity and effective supply per route -/

/-- A member route calls the argumentless member path over the written bundle (DOT-09). -/
theorem member_effective (r : Expr) (n : Ident) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv) :
    NeedPlan.effective ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ .call =
      ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ := rfl

/-- The `.Algorithm` route's callee is the link edge `t.Algorithm` itself, over the written bundle:
    its callee cell is the link whose ONE receiver cell the plan's VALUE, `Invoke()`, `.Algorithm`
    and loops share (CR-15, D-3). -/
theorem algorithm_effective (r : Expr) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (form : NeedPlan.CallForm) :
    (NeedPlan.effective ⟨.dotMember r "Algorithm" fb none, args, c, v, form⟩ .algorithm).callee =
      .dotMember r "Algorithm" fb none ∧
    (NeedPlan.effective ⟨.dotMember r "Algorithm" fb none, args, c, v, form⟩ .algorithm).args = args :=
  ⟨rfl, rfl⟩

/-- **D-5: the extension receiver belongs to the supply.** An extension route calls the edge's
    lexical fallback with the receiver as the ordinary FIRST supplied argument. -/
theorem extension_effective (r : Expr) (n : Ident) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv) :
    (NeedPlan.effective ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ .extension).callee = fb ∧
    (NeedPlan.effective ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ .extension).args = r :: args :=
  ⟨rfl, rfl⟩

/-- **Plain/dot correspondence of the extension route** (DOT-03): its effective callee and bundle
    are exactly those of the written call `F(t, args)` — the plan the written `Add(5, 1)` is — in the
    same captured context. -/
theorem extension_is_written_call (r : Expr) (n : Ident) (f : Ident) (args : OutputBundle)
    (c : EvalCtx) (v : ValEnv) :
    match NeedPlan.callShape? (.call (.resolve f) (r :: args)) c v with
    | some written =>
      written.callee = (NeedPlan.effective ⟨.dotMember r n (.resolve f) none, args, c, v, .dot r n (.resolve f)⟩ .extension).callee ∧
      written.args = (NeedPlan.effective ⟨.dotMember r n (.resolve f) none, args, c, v, .dot r n (.resolve f)⟩ .extension).args
    | none => False :=
  ⟨rfl, rfl⟩

/-- The view of a member plan is the written bundle (the receiver selects the member and is NOT
    supplied), of an extension plan the receiver-first bundle — whose `count` is one more. -/
theorem view_bundle_lengths (r : Expr) (n : Ident) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv) :
    (NeedPlan.effective ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ .call).args.length = args.length ∧
    (NeedPlan.effective ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ .extension).args.length = args.length + 1 := by
  simp [NeedPlan.effective, prepareLexicalDotCallArgs]

/-! ## D-1A: an intrinsic route is no callable invocation -/

/-- With an intrinsic route recorded, an explicit invocation is the refusal, with no effect. -/
theorem execute_intrinsic (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape)
    (s : EvalState) (cell : NeedCell) (hc : s.needs[a]? = some cell) (hr : cell.route = some .intrinsic) :
    (NeedPlan.execute route a shape).runState s = (.error NeedPlan.invocationRefusal, s) := by
  simp only [NeedPlan.execute, bind_run, withCtx_run, routeOf_recorded route.classify a shape s cell .intrinsic hc hr]
  rfl

/-- D-1A, the callee projection and the argument supply refuse likewise
    (`AlgorithmProjectionLaws.calleeCell_intrinsic`, `ArgumentViewLaws.viewCells_intrinsic`), while
    the ORIGINAL VALUE is the ordinary evaluation (`suspended_intrinsic_is_ordinary`). -/
theorem intrinsic_reference_operations_refuse (route : NeedPlan.Route) (a : Nat) (s : EvalState)
    (cell : NeedCell) (shape : NeedPlan.CallShape)
    (hc : s.needs[a]? = some cell) (hcallee : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) (hr : cell.route = some .intrinsic) :
    (NeedPlan.calleeCell route.classify a).runState s = (.error NeedPlan.invocationRefusal, s) ∧
    (NeedPlan.viewCells route.spread route.classify a).runState s = (.error NeedPlan.invocationRefusal, s) ∧
    (NeedPlan.invoke route ⟨a⟩).runState s = (.error NeedPlan.invocationRefusal, s) := by
  have hsa : NeedPlan.shapeAt? s.needs a = some shape := by simp [NeedPlan.shapeAt?, hc, hshape]
  refine ⟨AlgorithmProjectionLaws.calleeCell_intrinsic route.classify a s cell shape hc hcallee hshape hr,
    ArgumentViewLaws.viewCells_intrinsic route.spread route.classify a s shape cell hsa hc hr, ?_⟩
  rw [invoke_run route a s shape hsa]
  exact execute_intrinsic route a shape s cell hc hr

/-! ## Failure preservation -/

/-- **A route failure is the execution's failure**, under the written form's context, with nothing
    executed after it. -/
theorem execute_route_failure (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape)
    (s t : EvalState) (e : Error)
    (h : (NeedPlan.routeOf route.classify a shape).runState s = (.error e, t)) :
    (NeedPlan.execute route a shape).runState s =
      (.error (if (Except.error e : Except Error Unit).isIncomplete then e else Error.withContext shape.ctxMsg e), t) := by
  simp only [NeedPlan.execute, bind_run, withCtx_run, h]

/-! ## Establishment discipline (production) -/

/-- The production route classifier keeps every existing cell (it may demand a runtime-projection
    receiver, which `ProductionDiscipline` already covers). -/
theorem production_routeOf_disciplined (a : Nat) (shape : NeedPlan.CallShape) :
    Disciplined (NeedPlan.routeOf productionPlanRoute.classify a shape) :=
  disciplined_routeOf _ KatLang.EvaluatorDiscipline.classify_disciplined a shape

/-- The production callee cell is canonical: one cell per plan, whatever route established it. -/
theorem production_calleeCell_canonical (a c : Nat) (s t : EvalState)
    (h : (NeedPlan.calleeCell productionPlanRoute.classify a).runState s = (.ok c, t)) :
    (NeedPlan.calleeCell productionPlanRoute.classify a).runState t = (.ok c, t) :=
  AlgorithmProjectionLaws.calleeCell_canonical _ KatLang.EvaluatorDiscipline.classify_disciplined a c s t h

/-! ## Distinct plans, shared cells -/

/-- **Two written invocations are two plans** (CR-3): supplying two written dot edges — even spelled
    alike — allocates two cells, so META reifies two different references. -/
theorem written_invocations_distinct (e : Expr) (c : EvalCtx) (v : ValEnv) (s : EvalState)
    (hn : ∀ name, e ≠ .param name) :
    ∃ x y, (do let x ← supplyNeed e c v; let y ← supplyNeed e c v; pure (x, y) : EvalM (Nat × Nat)).runState s =
      (.ok (x, y), ((do let x ← supplyNeed e c v; let y ← supplyNeed e c v; pure (x, y) : EvalM (Nat × Nat)).runState s).2) ∧
      x ≠ y := by
  have h1 := KatLang.NeedControl.Allocation.supply_nonparameter e c v s hn
  have h2 := KatLang.NeedControl.Allocation.supply_nonparameter e c v
    { s with needs := s.needs.push { suspension := .expression e c v } } hn
  refine ⟨s.needs.size, s.needs.size + 1, ?_, by omega⟩
  simp only [bind_run, h1, h2, pure_run, Array.size_push]

/-- **The rebuilt invocation's supply holds the ORIGINAL cells.** A plan whose written argument is
    `op.Arguments*` forms its slot from the view's supply: exactly the captured plan's recorded
    addresses — the same cells, not copies (`ArgumentViewLaws.view_spread_slot`). -/
theorem rebuilt_supply_slot (ev sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (ctx : EvalCtx) (env : ValEnv) (operand : Expr) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute) (cells : List NeedSupply.Sourced)
    (hk : (spreadCollectorSlice? operand ctx).runState s = (.ok none, s))
    (hv : (ev (.sequenceSpread operand) ctx env).runState s = (NeedPlan.viewSupply sp classify a).runState s)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) (hp : cell.plan = .prepared (.ok cells)) :
    ∃ sourced, (NeedSupply.slot ev ctx env (.sequenceSpread operand)).runState s = (.ok sourced, s) ∧
      sourced.map Prod.fst = cells.map Prod.fst :=
  ArgumentViewLaws.view_spread_slot ev sp classify ctx env operand a s shape cell r cells hk hv hs hc hr hi hp


/-! ## Dispatch diagnostic names (META-S3-4-DIAG, October 20 2026)

A plan's execution names its dispatch by `NeedPlan.dispatchName`, a pure read of the heap
(`dispatchNameIn`). Until this date `executeAlong` passed the effective written callee
(`openExprName eff.callee`) on every route, so a planned `.Algorithm` invocation `Id(R.Algorithm(1))`
with `R = Capture(F(0))` reported `noMatchingBranch "R.Algorithm"` while the ordinary intrinsic
(`algorithmOfValue` / `algorithmCalleeOf`) and C# report `"F"`. -/

/-- **Ordinary routes keep their names.** Every route but `.Algorithm` names its dispatch exactly as
    before: its effective written callee — the call's callee, the argumentless member path, an
    extension's fallback. -/
theorem dispatchName_ordinary (needs : Array NeedCell) (a : Nat) (eff : NeedPlan.CallShape)
    (r : PlanRoute) (h : r ≠ .algorithm) :
    NeedPlan.dispatchNameIn needs a eff r = openExprName eff.callee := by
  cases r <;> first | rfl | exact absurd rfl h

/-- **The `.Algorithm` route names the captured plan's callee.** When plan `a`'s callee cell is a
    link whose recorded receiver completed with the call reference of plan `p` — the state
    `NeedLink.callable` leaves behind once the callee phase obtained the link's CALLABLE — the
    dispatch is named by `p`'s own callee name (`calleeNameIn?`: its route's effective callee). -/
theorem dispatchName_algorithm (needs : Array NeedCell) (a l rc p k : Nat) (eff : NeedPlan.CallShape)
    (c cl cr : NeedCell) (n : String)
    (hc : needs[a]? = some c) (hl : c.callee = some l) (hcl : needs[l]? = some cl)
    (hrc : cl.receiver = some rc) (hcr : needs[rc]? = some cr)
    (hst : cr.state = .completed (.ok (.callRef p, k)))
    (hn : NeedPlan.calleeNameIn? needs p = some n) :
    NeedPlan.dispatchNameIn needs a eff .algorithm = n := by
  have hlink : NeedPlan.linkedPlanIn? needs l = some p := by
    unfold NeedPlan.linkedPlanIn?
    rcases cl with ⟨_, _, _, _, _, _, receiver, _, _⟩
    rcases cr with ⟨_, state, _, _, _, _, _, _, _⟩
    simp only at hrc hst
    subst hrc hst
    simp [hcl, hcr]
  simp [NeedPlan.dispatchNameIn, hc, hl, hlink, hn]

/-- An unreadable link (no recorded callee cell, receiver or call-reference VALUE) falls back to the
    written link, so the name is total. -/
theorem dispatchName_algorithm_fallback (needs : Array NeedCell) (a : Nat) (eff : NeedPlan.CallShape)
    (h : ((needs[a]?).bind NeedCell.callee).bind (NeedPlan.linkedPlanIn? needs) = none) :
    NeedPlan.dispatchNameIn needs a eff .algorithm = openExprName eff.callee := by
  simp [NeedPlan.dispatchNameIn, h]

/-- **One naming rule.** `NeedPlan.calleeName` — the name the ORDINARY `.Algorithm` intrinsic gives a
    fresh call of a decoded plan (`algorithmOfValue`, `algorithmCalleeOf`) — is `calleeNameIn?` over
    the current heap, read without any state change. -/
theorem calleeName_reads (p : Nat) (s : EvalState) (n : String)
    (h : NeedPlan.calleeNameIn? s.needs p = some n) :
    (NeedPlan.calleeName p).runState s = (.ok n, s) := by
  simp only [NeedPlan.calleeName, bind_run, get_run, h]
  rfl

/-- **The planned and the ordinary `.Algorithm` invocation are named alike**: over the heap where the
    captured plan `p` is decoded, the planned dispatch name IS the ordinary intrinsic's
    `calleeName p`. -/
theorem planned_name_is_ordinary_name (s : EvalState) (a l rc p k : Nat) (eff : NeedPlan.CallShape)
    (c cl cr : NeedCell) (n : String)
    (hc : s.needs[a]? = some c) (hl : c.callee = some l) (hcl : s.needs[l]? = some cl)
    (hrc : cl.receiver = some rc) (hcr : s.needs[rc]? = some cr)
    (hst : cr.state = .completed (.ok (.callRef p, k)))
    (hn : NeedPlan.calleeNameIn? s.needs p = some n) :
    (NeedPlan.calleeName p).runState s = (.ok (NeedPlan.dispatchNameIn s.needs a eff .algorithm), s) := by
  rw [dispatchName_algorithm s.needs a l rc p k eff c cl cr n hc hl hcl hrc hcr hst hn]
  exact calleeName_reads p s n hn

/-- **Naming demands nothing.** Reading the dispatch name leaves the state EXACTLY as it was: no
    cell is allocated, demanded, projected or prepared, so every supplied cell, VALUE, CALLABLE,
    plan record, route record, callee cell and receiver cell is preserved, and no receiver or
    argument is evaluated again. -/
theorem dispatchName_inert (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) :
    (NeedPlan.dispatchName a eff r).runState s = (.ok (NeedPlan.dispatchNameIn s.needs a eff r), s) :=
  dispatchName_run a eff r s

/-- `executeAlong` as it was before META-S3-4-DIAG: the dispatch named by the effective written
    callee on every route. -/
def executeAlongWritten (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    EvalM CountedResult := do
  let eff := NeedPlan.effective shape r
  let callee ← withCtx shape.ctxMsg (NeedPlan.calleeAlong route a eff r)
  let result ← withCtx shape.ctxMsg (do
    let normal ← route.normalize callee eff.caller
    let cells ← NeedPlan.prepare route.spread a eff
    route.dispatch normal cells eff.caller eff.values (openExprName eff.callee))
  pure (reCountValueBoundary result)

/-- **The correction changes only the name.** For a dispatch whose behaviour does not depend on the
    name it is given (`d` is name-free), the corrected `executeAlong` and the former one have the
    same outcome and the same final state from every state — the same callee phase, supply, effects
    and records; only the diagnostic string passed to dispatch changed. -/
theorem executeAlong_changes_only_the_name (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape)
    (r : PlanRoute)
    (d : Algorithm → List NeedSupply.Sourced → EvalCtx → ValEnv → EvalM CountedResult)
    (hname : ∀ g cells c v n, route.dispatch g cells c v n = d g cells c v) (s : EvalState) :
    (NeedPlan.executeAlong route a shape r).runState s = (executeAlongWritten route a shape r).runState s := by
  simp only [NeedPlan.executeAlong, executeAlongWritten, bind_run, dispatchName_run, hname]

end KatLang.InvocationRouteLaws
