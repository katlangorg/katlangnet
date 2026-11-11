import KatLangArityLaws.PlanConservativity
import KatLangArityLaws.DotFunnel
import KatLangArityLaws.InvocationRoute

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# Plan conservativity, step 1: the route bridges to ordinary evaluation (ledger E-18)

`PlanConservativity.lean` proved that the plan's `ordinaryCall` IS the production written call on
the call and extension routes (`ordinaryCall_is_written_call_named`, `ordinaryCall_is_written_call`)
and, for a written call whose callee is no `X.Algorithm` link, the production `evalCallCountedExpr`
(`written_call_is_evalCallCountedExpr`). This module relates the plan's dot-form routes to ORDINARY
DOT EVALUATION (`evalCounted (.dotMember …)`, `EvalBody.evalDotCallCounted`). Production unfolding is
about COMPLETED runs and every theorem carries its route premises explicitly.

* **The resolved phase, every route** (`ordinaryCall_is_resolved`): on a completed run, the
  plan route's normalization, supply formation and dispatch are the production
  `evalResolvedCallCounted` (`resolved_call_is_production`) after the route's own callee phase and
  heap-read name and origin.
* **The extension route IS ordinary dot evaluation** (`ordinaryCall_extension_is_dot_call`, through
  the E-17 dot funnel `dot_run` / `written_eq_lexical_production`): from the receiver probe's exit
  state, the extension ordinary call is EXACTLY the re-counted production
  `evalCounted (.dotMember target F fallback (some args))` run from the probe's entry state —
  outcome, error context and final state. `classify_dot` shows that the probe is the plan route's
  own classification step.
* **The member route IS ordinary dot evaluation** (`member_bridge` and its instances): after a probe
  selecting a declared member, the member-route ordinary call and the re-counted production
  `evalCounted (.dotMember target N fallback (some args))` are ONE run from ONE entry state —
  outcome (a failing dispatch's `noMatchingBranch N` included), error context `CtxMsg.dotCall` and
  final state. This became true with the E-18 MEMBER-ROUTE CORRECTION (November 11 2026): the
  planned member dispatch is named by the member `N` (`NeedPlan.writtenDispatchName` in
  `KatLang.lean`), as ordinary dot evaluation and C# name it; until then it reported the
  argumentless path `t.N`, and `Box5.Algorithm(1)` failed with `noMatchingBranch "Box5.Algorithm"`
  on the plan route against `"Algorithm"` in production. Two things still differ between the two
  sides and are PROVED not to matter on the stated domains:
  - the RECEIVER: the plan navigates it by the structural projection of the argumentless path
    (`projectNeedStructuralMember`), production by the receiver probe (`resolveDotReceiver?`).
    `probe_is_projected_structure` identifies them by recursion on the receiver for every receiver
    that can select a member — a name, an inline block and every argumentless member path over them
    (`member_bridge_static`), and a parameter-rooted receiver whose supplied CALLABLE is
    structure-normal (`member_bridge_param`); a value head never selects a member
    (`resolveAlg_memberless`);
  - the callee ORIGIN (CACHE-PUB-1): written path on the plan side, bound member in production. It
    is read only for an EMPTY formed supply, so a bundle with a plain first slot never reads it
    (`member_bridge`, E-17 `resolved_origin_independent`); for every other bundle (`t.N()`,
    `t.N(xs*)`) the two origins name the same binding whenever the receiver's navigation is
    state-inert (`member_bridge_inert`, `NavInert`, `written_origin_is_bound`).
  `member_bridge_of_origin` is the general statement, relative to that origin agreement.
* **The `.Algorithm` route: ONE receiver read, and a plan-side decomposition — NOT a bridge.** Since
  the E-18 RECEIVER-READ CORRECTION (November 11 2026; `KatLang.lean`: `NeedInvocationRole`,
  `EvalBody.invocationReceiverValue`, `EvalBody.plannedLinkCallable`) the plan reads its receiver as
  the ordinary intrinsic does:
  - `invocationReceiverValue_eq` (an `EvalM` equation) — the production invocation receiver read is
    the receiver's identity probe followed by exactly the dot intrinsic's read after ITS probe
    (`algorithmReceiverValue`, `dot_algorithm_run`); the ordinary link callee `(X.Algorithm)(args)`
    runs the same definition (`algorithmCalleeOf`);
  - `receiver_cell_reads_invocation_receiver` — on a completed run the evaluator of the plan's
    retained receiver cell (a cell marked `NeedInvocationRole.receiver` over a link edge) IS that
    read, counted at its value boundary; `link_cell_keeps_its_evaluator` — every other cell over a
    link edge keeps the pre-correction evaluator, so nothing else changed;
  - `plannedReceiverValue_cell` / `plannedReceiverValue_param` — the plan's receiver VALUE is the
    retained cell's or, for a parameter receiver, the invocation receiver read of the written
    parameter (the transported cell keeps the VALUE);
  - `algorithm_callee_is_planned_callee` (an `EvalM` equation) — the callee phase is the canonical
    cell (`NeedPlan.calleeCell`, which marks the link and records it in the plan cell, CR-13/D-3)
    followed by `plannedCallee`: the receiver VALUE, then the SAME tail as the direct intrinsic's
    (`decodeCallRef`, the decoded plan's callee cell, the production `capturedCallee`). It replaces
    `algorithm_callee_is_captured_callee`, whose statement (the generic CALLABLE projection of the
    link) the correction made false.
  Hence `ordinaryCall_algorithm_is_production` equates the `.Algorithm` ordinary call with the
  proof-local `algorithmPlanCall`, retaining that SAME plan-side callee phase. It does not equate it
  with `evalCounted` or `evalCallCountedExpr`. The direct production intrinsic has the SAME tail — a fresh
  `evalResolvedCallCounted` of the captured plan's projected callee, named by that plan's
  `calleeName`, with origin `.cell` of its callee cell — after its OWN callee phase:
  `dot_algorithm_run` (`R.Algorithm(args)`, the dot form: the `.miss .algorithm` arm and
  `algorithm_of_value_run`) and `link_call_run` (`(R.Algorithm)(args)`, the link arm of
  `evalCallCountedExpr`). `algorithm_tail_name_origin` identifies the plan's heap-read name and origin
  with the captured plan's `calleeName` and callee cell once the link's receiver is decoded.

## Boundary

**The `.Algorithm` route is not bridged — no longer because the outcomes differ, but because the
heaps do.** The language-visible difference the E-18 correction task found — the plan read its
receiver as an ordinary supplied VALUE (`supplyNeed`, `evalCounted receiver`), so a receiver without
output (`Empty = { }`, `Empty.Algorithm(0)`) failed with its OWN missing output under `while
evaluating property Empty` where the ordinary intrinsic and C# report the NESTED, unframed one — is
CORRECTED in `KatLang.lean` (the receiver-read correction above; C#'s
`InvocationReceiverSuspension`, rule D-3). `PlanRouteBridgeGuards.algorithmReceiverFailureAgrees` is
the regression of the former witness `algorithmReceiverFailureDiffers`, and the guards find the two
routes' outcomes equal on every receiver tried: without output, member paths, nested `.Algorithm`
links, written calls, values, transparent references and parameters. That is finite evidence. What
an outcome THEOREM still needs:
* `algorithmHeapDiffers` (a permanent witness) — exact final-state equality is FALSE: from the SAME
  reached flight state for `R.Algorithm(0)` both return `(0, 1)`, while only the plan side records
  the outer callee and it has two more need cells (the link and its receiver cell). The bridge must
  be stated up to a heap relation, and because the plan allocates those cells BEFORE the receiver
  read and the tail run, every address they allocate is shifted while results can carry addresses
  (`callRef`, `argView`): an address-RENAMING simulation of the whole evaluator, not a relation that
  ignores extra cells.
* The retained cell's read resolves the receiver's identity once more (`invocationReceiverValue_eq`:
  probe, then read), where the dot-form intrinsic reads after the ONE probe that also selected the
  edge. The bridge needs that second resolution to answer alike from the plan's state — the memo
  stability of CALLABLE projection and of the alias chase that the member route's remaining class
  needs too.
* The receiver cell's completion shell around the read (`evaluating`, then the memoized outcome),
  and the heap-read dispatch name and origin (`algorithm_tail_name_origin`) from the state the callee
  phase leaves.

**The member route's remaining class**: an empty or spread-first bundle over a receiver whose
navigation is not state-inert — a transparent reference or a runtime-target alias (its structure is
a chase), a name resolved through `open`, a parameter (its first projection writes the cell's
CALLABLE memo). There the plan's written origin navigates the receiver a second time when the origin
is read, and no theorem shows that the second navigation finds the bound member; the guards find
agreement. That every supplied CALLABLE is structure-normal on reachable heaps (the parameter
receiver's premise) is likewise not proved as a heap invariant.

Only completed runs; C# evidence stays finite.
-/

namespace KatLang.PlanRouteBridge

open KatLang.PlanConservativity (writtenCall writtenCallNamed resolved_call_is_production
  ordinaryCall_is_written_call ordinaryCall_is_written_call_named withCtx_incomplete)

/-! ## The resolved phase, every route -/

/-- The ordinary call with its resolved phase written as the production `evalResolvedCallCounted`:
    the route's callee phase, the heap-read dispatch name and origin, then the production resolved
    call under the written form's context. -/
def plannedResolvedCall (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) : EvalM CountedResult := do
  let eff := NeedPlan.effective shape r
  let callee ← withCtx shape.ctxMsg (NeedPlan.calleeAlong productionPlanRoute a eff r)
  let name ← NeedPlan.dispatchName a eff r
  let origin ← NeedPlan.dispatchOrigin a eff r
  let result ← withCtx shape.ctxMsg (evalResolvedCallCounted callee eff.args eff.caller eff.values name origin)
  pure (reCountValueBoundary result)

/-- **The resolved phase of every route IS production.** On a completed run, `ordinaryCall` along
    any route is `plannedResolvedCall`: its normalization, formation and dispatch are the production
    `evalResolvedCallCounted` (`resolved_call_is_production`). -/
theorem ordinaryCall_is_resolved (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState)
    (hcomp : ((plannedResolvedCall a shape r).runState s).1 ≠ .error .fuelExhausted) :
    (ordinaryCall productionPlanRoute a shape r).runState s = (plannedResolvedCall a shape r).runState s := by
  unfold ordinaryCall plannedResolvedCall at *
  dsimp only at hcomp ⊢
  simp only [bind_run, dispatchName_run, dispatchOrigin_run] at hcomp ⊢
  generalize NeedPlan.effective shape r = eff at hcomp ⊢
  rcases h1 : (withCtx shape.ctxMsg (NeedPlan.calleeAlong productionPlanRoute a eff r)).runState s with ⟨o1, t1⟩
  rw [h1] at hcomp
  cases o1 with
  | error e => rfl
  | ok callee =>
    dsimp only at hcomp ⊢
    generalize NeedPlan.dispatchNameIn t1.needs a eff r = name at hcomp ⊢
    generalize NeedPlan.dispatchOriginIn t1.needs a eff r = origin at hcomp ⊢
    have hin : ProductionCompletes (evalResolvedCallCounted callee eff.args eff.caller eff.values name origin) t1 := by
      intro hinc
      apply hcomp
      have := withCtx_incomplete shape.ctxMsg _ t1 hinc
      revert this
      rcases (withCtx shape.ctxMsg (evalResolvedCallCounted callee eff.args eff.caller eff.values name origin)).runState t1
        with ⟨o, t2⟩
      intro h; simp only at h; subst h; rfl
    have he := resolved_call_is_production callee eff.args eff.caller eff.values name origin t1 hin
    have hw : (withCtx shape.ctxMsg (do
        let normal ← productionPlanRoute.normalize callee eff.caller
        let cells ← NeedSupply.form productionPlanRoute.spread eff.caller eff.values eff.args
        productionPlanRoute.dispatch origin normal cells eff.caller eff.values name)).runState t1 =
        (withCtx shape.ctxMsg (evalResolvedCallCounted callee eff.args eff.caller eff.values name origin)).runState t1 := by
      have he' : (do
          let normal ← productionPlanRoute.normalize callee eff.caller
          let cells ← NeedSupply.form productionPlanRoute.spread eff.caller eff.values eff.args
          productionPlanRoute.dispatch origin normal cells eff.caller eff.values name).runState t1 =
          (evalResolvedCallCounted callee eff.args eff.caller eff.values name origin).runState t1 := he
      rw [withCtx_run, withCtx_run, he']
    rw [hw]

/-! ## The `.Algorithm` route -/

/-- The production `capturedCallee` is its delegation: the cell's production CALLABLE projection,
    with the captured callee's absence report. -/
def capturedOf : Option Algorithm → EvalM Algorithm
  | some algorithm => pure algorithm
  | none => .error (Error.notAnAlgorithm capturedCalleeDescription)

theorem capturedCallee_eq (c : Nat) :
    capturedCallee c = (projectNeedCallable c >>= capturedOf) := by
  have hstep : ∀ rec : EvalRec, evalStep rec (.capturedCallee c) = rec (.projectNeedCallable c) >>= capturedOf := by
    intro rec
    show EvalBody.capturedCallee rec c = _
    unfold EvalBody.capturedCallee
    congr 1
  exact delegation_equation (.capturedCallee c) (.projectNeedCallable c) capturedOf hstep
    (fun o _ => by cases o <;> exact nofun)

/-! ### The receiver read of the two routes (D-3; E-18 receiver-read correction, November 11 2026)

Until the correction the plan read its receiver as an ordinary supplied VALUE (`evalCounted
receiver` inside the receiver cell's completion shell), the direct intrinsic through
`referenceReceiverValue`; the two reported a receiver's own failure differently
(`PlanRouteBridgeGuards.algorithmReceiverFailureAgrees` is the regression of that witness). Now the
plan's retained receiver cell, the plan's read of a parameter receiver and the ordinary link callee
`(X.Algorithm)(args)` run ONE definition, `invocationReceiverValue`, and that definition is the
dot-form intrinsic's own read after its probe. -/

/-- The receiver VALUE read of the direct `.Algorithm` intrinsic on the dot route (`.miss .algorithm`),
    after the receiver's identity probe answered `alg?`. -/
def algorithmReceiverValue (target : Expr) (alg? : Option Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  match alg? with
  | some targetAlg => referenceReceiverValue target targetAlg ctx env
  | none => withNestedMissingOutput (eval target ctx env)

/-- **The invocation receiver read IS the intrinsic's receiver read.** The production invocation
    receiver read — the VALUE of a planned `.Algorithm` invocation's retained receiver cell
    (`receiver_cell_reads_invocation_receiver`), the plan's read of a parameter receiver
    (`plannedReceiverValue_param`) and the ordinary link callee's read (`algorithmCalleeOf`) — is the
    receiver's identity probe followed by exactly the read the dot-form intrinsic performs after
    ITS probe (`dot_algorithm_run`). An `EvalM` equation: no completion premise. -/
theorem invocationReceiverValue_eq (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    invocationReceiverValue receiver ctx env =
      (resolveDotReceiver? receiver ctx >>= fun alg? => algorithmReceiverValue receiver alg? ctx env) := by
  show (resolveDotReceiver? receiver ctx >>= fun alg? =>
    match alg? with
    | none => withNestedMissingOutput (eval receiver ctx env)
    | some targetAlg => referenceReceiverValue receiver targetAlg ctx env) = _
  congr 1
  funext alg?
  cases alg? <;> rfl

/-- The role test of the VALUE evaluator is a pure heap read. -/
theorem isInvocationReceiver_run (r : Nat) (s : EvalState) :
    (NeedLink.isInvocationReceiver r).runState s =
      (.ok ((s.needs[r]?).map NeedCell.invocation == some .receiver), s) := rfl

/-- **The retained receiver cell reads its receiver as the intrinsic does (D-3).** On a completed
    run, the written-expression evaluator of a cell marked `NeedInvocationRole.receiver` over a link
    edge `receiver.Algorithm` — the `ev` the VALUE shell `NeedDemand.step` runs for that cell — is
    the production invocation receiver read of `receiver`, counted at its value boundary: not
    `evalCounted` of the edge, not the link's VALUE, not a supplied VALUE of `receiver` and not an
    invocation plan of a receiver that is itself a written call. -/
theorem receiver_cell_reads_invocation_receiver (r : Nat) (source receiver fallback : Expr) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState) (cell : NeedCell)
    (hl : linkEdge? source = some (receiver, fallback))
    (hcell : s.needs[r]? = some cell) (hrole : cell.invocation = .receiver)
    (hc : ProductionCompletes (evalSuppliedAt r source ctx env) s) :
    (evalSuppliedAt r source ctx env).runState s =
      (invocationReceiverValue receiver ctx env >>= fun value =>
        (pure (value, Result.valueCount value) : EvalM CountedResult)).runState s := by
  have hu := production_unfolds (.evalSuppliedAt r source ctx env) s hc
  change (evalUnbounded (.evalSuppliedAt r source ctx env)).runState s = _
  rw [← hu]
  change (EvalBody.evalSuppliedAt evalUnbounded r source ctx env).runState s = _
  unfold EvalBody.evalSuppliedAt
  rw [hl]
  have hb : ((s.needs[r]?).map NeedCell.invocation == some NeedInvocationRole.receiver) = true := by
    rw [hcell, Option.map_some, hrole]; rfl
  dsimp only
  rw [EvalM.bind_runState, isInvocationReceiver_run, hb]
  rfl

/-- **Every other cell over a link edge keeps the pre-correction evaluator.** For a cell that is NOT
    a retained invocation receiver — a supplied `X.Algorithm` link, the plan's callee link itself —
    the evaluator decides the link route as before: the link's VALUE on the intrinsic route, the
    ordinary evaluation of the edge on a declared member. -/
theorem link_cell_keeps_its_evaluator (r : Nat) (source receiver fallback : Expr) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState)
    (hl : linkEdge? source = some (receiver, fallback))
    (hrole : (s.needs[r]?).map NeedCell.invocation ≠ some .receiver)
    (hc : ProductionCompletes (evalSuppliedAt r source ctx env) s) :
    (evalSuppliedAt r source ctx env).runState s =
      (algorithmIntrinsicRoute receiver ctx >>= fun intrinsic =>
        if intrinsic then linkValue r else evalCounted source ctx env).runState s := by
  have hu := production_unfolds (.evalSuppliedAt r source ctx env) s hc
  change (evalUnbounded (.evalSuppliedAt r source ctx env)).runState s = _
  rw [← hu]
  change (EvalBody.evalSuppliedAt evalUnbounded r source ctx env).runState s = _
  unfold EvalBody.evalSuppliedAt
  rw [hl]
  have hb : ((s.needs[r]?).map NeedCell.invocation == some NeedInvocationRole.receiver) = false := by
    cases h : (s.needs[r]?).map NeedCell.invocation with
    | none => rfl
    | some role =>
      cases role with
      | receiver => exact absurd h hrole
      | supplied => rfl
      | link => rfl
  dsimp only
  rw [EvalM.bind_runState, isInvocationReceiver_run, hb]
  rfl

/-! ### The planned callee read -/

/-- **The plan's receiver VALUE over a PARAMETER receiver** is the production invocation receiver
    read of the written parameter in the link's caller context (D-3: the transported parameter cell
    keeps the VALUE; the read keeps the intrinsic's failure shape — the nested missing output and
    its frames). -/
theorem plannedReceiverValue_param (link : NeedCell) (cell : Nat) (source fallback : Expr) (x : Ident)
    (caller : EvalCtx) (values : ValEnv) (hs : link.suspension = .expression source caller values)
    (hl : linkEdge? source = some (.param x, fallback)) :
    plannedReceiverValue link cell = invocationReceiverValue (.param x) caller values := by
  show EvalBody.plannedReceiverValue evalUnbounded link cell = _
  unfold EvalBody.plannedReceiverValue
  rw [hs]
  dsimp only
  rw [hl]
  rfl

/-- **The plan's receiver VALUE over every other receiver** is the VALUE of the link's retained
    receiver cell (`receiver_cell_reads_invocation_receiver`: the invocation receiver read, inside
    the cell's ONE completion shell — demanded at most once for the plan). -/
theorem plannedReceiverValue_cell (link : NeedCell) (cell : Nat) (source receiver fallback : Expr)
    (caller : EvalCtx) (values : ValEnv) (hs : link.suspension = .expression source caller values)
    (hl : linkEdge? source = some (receiver, fallback)) (hp : ∀ x, receiver ≠ .param x) :
    plannedReceiverValue link cell = Prod.fst <$> demandNeedRecursive cell := by
  show EvalBody.plannedReceiverValue evalUnbounded link cell = _
  unfold EvalBody.plannedReceiverValue
  rw [hs]
  dsimp only
  rw [hl]
  cases receiver with
  | param x => exact absurd rfl (hp x)
  | _ => rfl

/-- **The production callee read of a planned `.Algorithm` invocation** over production operations
    only: the link's receiver cell, the receiver VALUE, the decoded plan's canonical callee cell and
    that cell's production CALLABLE. An `EvalM` equation (`plannedLinkCallable` is a body over the
    production answer, not a recursive evaluator call: no completion premise). -/
theorem plannedLinkCallable_eq (link : Nat) :
    plannedLinkCallable link = (do
      let cell ← NeedLink.receiverCell link
      let some linkCell := (← get).needs[link]? | throw (Error.illegalInEval "invalid need address")
      let value ← plannedReceiverValue linkCell cell
      let plan ← decodeCallRef value
      let callee ← NeedPlan.calleeCell productionPlanRoute.classify plan
      projectNeedCallable callee) := rfl

/-- The captured callee a planned `.Algorithm` invocation reads from its callee link: after the
    receiver VALUE, the SAME tail as the direct intrinsic's — `decodeCallRef`, the decoded plan's
    `NeedPlan.calleeCell` and the production `capturedCallee` of that cell
    (`algorithm_of_value_run`, `algorithmCalleeOf`). -/
def plannedCallee (link : Nat) : EvalM Algorithm := do
  let cell ← NeedLink.receiverCell link
  let some linkCell := (← get).needs[link]? | throw (Error.illegalInEval "invalid need address")
  let value ← plannedReceiverValue linkCell cell
  let plan ← decodeCallRef value
  let callee ← NeedPlan.calleeCell productionPlanRoute.classify plan
  capturedCallee callee

theorem plannedCallee_eq (link : Nat) :
    (plannedLinkCallable link >>= capturedOf) = plannedCallee link := by
  rw [plannedLinkCallable_eq]
  unfold plannedCallee
  simp only [EvalM.bind_assoc, capturedCallee_eq]
  congr 1
  funext cell
  congr 1
  funext st
  cases st.needs[link]? with
  | none => rfl
  | some linkCell =>
    dsimp only
    simp only [EvalM.bind_assoc]

/-- **The `.Algorithm` callee phase IS production.** The plan's callee along the `.Algorithm` route
    is `plannedCallee` of the plan's canonical callee cell — the link `NeedPlan.calleeCell`
    establishes, marks as an invocation link and RECORDS in the plan cell (CR-13, D-3). An `EvalM`
    equation: no completion premise. (Before the receiver-read correction this was the generic
    CALLABLE projection of the link, `capturedCallee`; it is now the planned callee read, whose
    receiver read is the intrinsic's.) -/
theorem algorithm_callee_is_planned_callee (a : Nat) (eff : NeedPlan.CallShape) :
    NeedPlan.calleeAlong productionPlanRoute a eff .algorithm =
      (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee) := by
  simp only [NeedPlan.calleeAlong]
  congr 1
  funext link
  rw [← plannedCallee_eq]
  show (plannedLinkCallable link >>= _) = _
  congr 1

/-- The `.Algorithm` route's ordinary call over production operations only: the plan's callee cell,
    the planned callee read (`plannedCallee`), the heap-read name and origin, and the production
    resolved call under the written form's context. -/
def algorithmPlanCall (a : Nat) (shape : NeedPlan.CallShape) : EvalM CountedResult := do
  let callee ← withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee)
  let name ← NeedPlan.dispatchName a shape .algorithm
  let origin ← NeedPlan.dispatchOrigin a shape .algorithm
  let result ← withCtx shape.ctxMsg
    (evalResolvedCallCounted callee shape.args shape.caller shape.values name origin)
  pure (reCountValueBoundary result)

/-- **Plan-side decomposition, `.Algorithm` route.** On a completed run, the plan's ordinary call along the
    `.Algorithm` route is `algorithmPlanCall`: the production establishment of the plan's callee cell,
    the planned callee read of that link (`plannedCallee`), and the production `evalResolvedCallCounted` —
    with the dispatch named and originated from the heap the callee phase leaves
    (`algorithm_tail_name_origin`). The RHS is proof-local, NOT the ordinary evaluator entry point;
    no equality with `evalCounted` or `evalCallCountedExpr` is proved here. -/
theorem ordinaryCall_algorithm_is_production (a : Nat) (shape : NeedPlan.CallShape) (s : EvalState)
    (hcomp : ((algorithmPlanCall a shape).runState s).1 ≠ .error .fuelExhausted) :
    (ordinaryCall productionPlanRoute a shape .algorithm).runState s = (algorithmPlanCall a shape).runState s := by
  have he : plannedResolvedCall a shape .algorithm = algorithmPlanCall a shape := by
    unfold plannedResolvedCall algorithmPlanCall
    simp only [NeedPlan.effective]
    rw [algorithm_callee_is_planned_callee]
  rw [ordinaryCall_is_resolved a shape .algorithm s (by rw [he]; exact hcomp), he]

/-- A recorded callee cell is read back: establishing it again changes nothing. -/
theorem calleeCell_recorded (classify : NeedPlan.CallShape → EvalM PlanRoute) (p c : Nat) (s : EvalState)
    (cp : NeedCell) (hp : s.needs[p]? = some cp) (hc : cp.callee = some c) :
    (NeedPlan.calleeCell classify p).runState s = (.ok c, s) := by
  simp only [NeedPlan.calleeCell, bind_run, get_run, hp, hc]
  rfl

/-- **The `.Algorithm` tail's name and origin.** Once the link the plan cell records as its callee
    has its receiver decoded into the captured plan `p` (a completed `callRef p`), the plan's
    heap-read dispatch name is `p`'s `calleeName` (META-S3-4-DIAG) and its origin is `.cell` of
    `p`'s recorded callee cell — exactly the name and origin the direct intrinsic passes
    (`algorithm_of_value_run`, `algorithmCalleeOf`). -/
theorem algorithm_tail_name_origin (s : EvalState) (a l rc p k c : Nat) (eff : NeedPlan.CallShape)
    (ca cl cr cp : NeedCell) (n : String)
    (ha : s.needs[a]? = some ca) (hl : ca.callee = some l) (hcl : s.needs[l]? = some cl)
    (hrc : cl.receiver = some rc) (hcr : s.needs[rc]? = some cr)
    (hst : cr.state = .completed (.ok (.callRef p, k)))
    (hn : NeedPlan.calleeNameIn? s.needs p = some n)
    (hp : s.needs[p]? = some cp) (hc : cp.callee = some c) :
    NeedPlan.dispatchNameIn s.needs a eff .algorithm = n ∧
    (NeedPlan.calleeName p).runState s = (.ok n, s) ∧
    NeedPlan.dispatchOriginIn s.needs a eff .algorithm = .cell c ∧
    (NeedPlan.calleeCell productionPlanRoute.classify p).runState s = (.ok c, s) := by
  have hname := KatLang.InvocationRouteLaws.dispatchName_algorithm s.needs a l rc p k eff ca cl cr n
    ha hl hcl hrc hcr hst hn
  have hlink : NeedPlan.linkedPlanIn? s.needs l = some p := by
    unfold NeedPlan.linkedPlanIn?
    rcases cl with ⟨_, _, _, _, _, _, receiver, _⟩
    rcases cr with ⟨_, state, _, _, _, _, _, _⟩
    simp only at hrc hst
    subst hrc hst
    simp [hcl, hcr]
  refine ⟨hname, KatLang.InvocationRouteLaws.calleeName_reads p s n hn, ?_,
    calleeCell_recorded _ p c s cp hp hc⟩
  simp [NeedPlan.dispatchOriginIn, ha, hl, hlink, hp, hc]

theorem complete_of_ctx {α : Type} (msg : String) (m : EvalM α) (s : EvalState)
    (h : ((withCtx msg m).runState s).1 ≠ .error .fuelExhausted) : ProductionCompletes m s := by
  intro hm; exact h (withCtx_incomplete msg m s hm)

/-- **The direct dot-form intrinsic `target.Algorithm(args)`.** After a receiver probe completing at
    `(.ok alg?, s')` that selects the `.Algorithm` miss, the production dot evaluation is the
    receiver's VALUE read and `algorithmOfValue` from the probe's exit state, under
    `CtxMsg.dotCall target Algorithm`. -/
theorem dot_algorithm_run (target fallback : Expr) (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s s' : EvalState) (alg? : Option Algorithm)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hc : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback args?) ctx env) s) :
    (evalCounted (.dotMember target "Algorithm" fallback args?) ctx env).runState s =
      KatLang.FiniteLoop.ctxOutcome (CtxMsg.dotCall target "Algorithm")
        ((algorithmReceiverValue target alg? ctx env >>= fun val => algorithmOfValue val args? ctx env).runState s') := by
  have hu := production_unfolds (.evalCounted (.dotMember target "Algorithm" fallback args?) ctx env) s hc
  have hc' : ((withCtx (CtxMsg.dotCall target "Algorithm")
      (evalDotCallCounted target "Algorithm" fallback args? ctx env)).runState s).1 ≠ .error .fuelExhausted := by
    change ((evalStep evalUnbounded (.evalCounted (.dotMember target "Algorithm" fallback args?) ctx env)).runState s).1 ≠ _
    rw [hu]; exact hc
  change (evalUnbounded (.evalCounted (.dotMember target "Algorithm" fallback args?) ctx env)).runState s = _
  rw [← hu]
  change (withCtx (CtxMsg.dotCall target "Algorithm")
    (evalDotCallCounted target "Algorithm" fallback args? ctx env)).runState s = _
  have hd := complete_of_ctx _ _ s hc'
  have hu2 := production_unfolds (.evalDotCallCounted target "Algorithm" fallback args? ctx env) s hd
  rw [KatLang.FiniteLoop.ctx_run]
  change KatLang.FiniteLoop.ctxOutcome _
    ((evalUnbounded (.evalDotCallCounted target "Algorithm" fallback args? ctx env)).runState s) = _
  rw [← hu2]
  congr 1
  change (EvalBody.evalDotCallCounted evalUnbounded target "Algorithm" fallback args? ctx env).runState s = _
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState]
  have hp : (EvalRec.resolveDotReceiver? evalUnbounded target ctx).runState s = (.ok alg?, s') := hprobe
  rw [hp]
  simp only [hmiss]
  cases alg? <;> rfl

/-- **The direct intrinsic's fresh call.** On a completed run, `algorithmOfValue` with an argument
    list decodes the plan, establishes its callee cell, projects that cell's CALLABLE and makes the
    production resolved call named by the plan's `calleeName`, with origin `.cell` of the callee cell. -/
theorem algorithm_of_value_run (val : Result) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (algorithmOfValue val (some args) ctx env) s) :
    (algorithmOfValue val (some args) ctx env).runState s =
      (do let plan ← decodeCallRef val
          let callee ← NeedPlan.calleeCell productionPlanRoute.classify plan
          let algorithm ← capturedCallee callee
          let name ← NeedPlan.calleeName plan
          evalResolvedCallCounted algorithm args ctx env name (.cell callee)).runState s := by
  have hu := production_unfolds (.algorithmOfValue val (some args) ctx env) s hc
  change (evalUnbounded (.algorithmOfValue val (some args) ctx env)).runState s = _
  rw [← hu]
  rfl

/-- **The direct link-callee call `(target.Algorithm)(args)`** (the link arm of
    `evalCallCountedExpr`): once the intrinsic route is decided `true` at `s₁`, the production call is
    `algorithmCalleeOf` (the receiver's VALUE, decoded, its callee cell and CALLABLE, the plan's
    `calleeName`) and the production resolved call with origin `.cell`, under `CtxMsg.call f`. -/
theorem link_call_run (f receiver fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s s₁ : EvalState) (hl : linkEdge? f = some (receiver, fallback))
    (hroute : (withCtx (CtxMsg.call f) (algorithmIntrinsicRoute receiver ctx)).runState s = (.ok true, s₁))
    (hc : ProductionCompletes (evalCallCountedExpr f args ctx env) s) :
    (evalCallCountedExpr f args ctx env).runState s =
      (withCtx (CtxMsg.call f) (algorithmCalleeOf receiver ctx env) >>= fun found =>
        withCtx (CtxMsg.call f)
          (evalResolvedCallCounted found.1 args ctx env found.2.1 (.cell found.2.2))).runState s₁ := by
  have hu := production_unfolds (.evalCallCountedExpr f args ctx env) s hc
  change (evalUnbounded (.evalCallCountedExpr f args ctx env)).runState s = _
  rw [← hu]
  change (EvalBody.evalCallCountedExpr evalUnbounded f args ctx env).runState s = _
  unfold EvalBody.evalCallCountedExpr
  rw [hl]
  simp only [bind_run]
  have hr : (withCtx (CtxMsg.call f) (EvalRec.algorithmIntrinsicRoute evalUnbounded receiver ctx)).runState s =
      (.ok true, s₁) := hroute
  rw [hr]
  simp only [ite_true, bind_run]
  rfl

/-! ## The extension route against the production dot evaluation (E-17) -/

/-- The production written call named `name`, framed once (the two `withCtx` frames of one message
    merge). -/
theorem writtenCallNamed_framed (msg : String) (eff : NeedPlan.CallShape) (name : String) :
    writtenCallNamed msg eff name = reCountValueBoundary <$> withCtx msg
      (resolveCalleeAlg eff.callee eff.caller >>= fun callee =>
        evalResolvedCallCounted callee eff.args eff.caller eff.values name
          (.written eff.callee eff.caller)) := by
  unfold writtenCallNamed
  rw [← KatLang.DotFunnel.withCtx_bind]
  apply EvalM.ext; intro s
  simp only [bind_run, map_run]
  rcases (withCtx msg (resolveCalleeAlg eff.callee eff.caller)).runState s with ⟨_ | c, t⟩
  · rfl
  · dsimp only
    rcases (withCtx msg (evalResolvedCallCounted c eff.args eff.caller eff.values name
      (.written eff.callee eff.caller))).runState t with ⟨_ | r, t'⟩ <;> rfl

/-- The production written call, framed once (the two `withCtx` frames of one message merge). -/
theorem writtenCall_framed (msg : String) (eff : NeedPlan.CallShape) :
    writtenCall msg eff = reCountValueBoundary <$> withCtx msg
      (resolveCalleeAlg eff.callee eff.caller >>= fun callee =>
        evalResolvedCallCounted callee eff.args eff.caller eff.values (openExprName eff.callee)
          (.written eff.callee eff.caller)) :=
  writtenCallNamed_framed msg eff (openExprName eff.callee)

/-- The plan route a dot selection gives (`classifyPlanRouteWith`'s dot arm). -/
def selectionRoute : DotSelection → PlanRoute
  | .member _ _ => .call
  | .miss kind => kind.planRoute

/-- **The probe IS the plan route's classification of a dot shape.** For an argument-bearing dot
    edge, the production classifier runs exactly the receiver probe and the dot decision
    `selectDotEdge`. -/
theorem classify_dot (target : Expr) (F : Ident) (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (sel : DotSelection)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target F alg? = .ok sel) :
    (productionPlanRoute.classify ⟨.dotMember target F fallback none, args, ctx, env, .dot target F fallback⟩).runState s =
      (.ok (selectionRoute sel), s') := by
  unfold productionPlanRoute
  dsimp only
  unfold classifyPlanRouteWith
  simp only [bind_run]
  rw [hprobe]
  dsimp only
  rw [hsel]
  cases sel <;> rfl

/-- **STEP 1, extension route against the production dot evaluation.** After a receiver probe
    completing at `(.ok alg?, s')` with an extension miss — the plan route's own classification step
    (`classify_dot`) — for a non-spread receiver and a name fallback, the extension ordinary call run
    from `s'` IS the re-counted production dot evaluation `target.F(args)` run from `s`: outcome,
    error context (`CtxMsg.dotCall target F`) and final state. Reuses the E-17 dot funnel
    (`dot_run`, `written_eq_lexical_production`). -/
theorem ordinaryCall_extension_is_dot_call (a : Nat) (target : Expr) (F : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (hsp : ¬ ∃ x, target = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension))
    (hc : ProductionCompletes (evalCounted (.dotMember target F fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target F fallback none, args, ctx, env, .dot target F fallback⟩
        .extension).runState s' =
      (reCountValueBoundary <$> evalCounted (.dotMember target F fallback (some args)) ctx env).runState s := by
  have hD := KatLang.DotFunnel.dot_run target F fallback (some args) ctx env s s' alg? hfb hprobe hmiss
  have hx : ((KatLang.DotFunnel.lexicalRun F target fallback (some args) ctx env evalUnbounded).runState s').1 ≠
      .error .fuelExhausted := fun h => hD.2 h hc
  have hwr := KatLang.DotFunnel.written_eq_lexical_production F target fallback hfb hsp (some args) ctx env
  have hframe : (writtenCall (CtxMsg.dotCall target F) ⟨fallback, target :: args, ctx, env, .dot target F fallback⟩).runState s' =
      (reCountValueBoundary <$> withCtx (CtxMsg.dotCall target F)
        (KatLang.DotFunnel.lexicalRun F target fallback (some args) ctx env evalUnbounded)).runState s' := by
    rw [writtenCall_framed]
    dsimp only
    rw [KatLang.DotFunnel.openExprName_name F fallback hfb, ← hwr]
    rfl
  have hrhs : (reCountValueBoundary <$> evalCounted (.dotMember target F fallback (some args)) ctx env).runState s =
      (reCountValueBoundary <$> withCtx (CtxMsg.dotCall target F)
        (KatLang.DotFunnel.lexicalRun F target fallback (some args) ctx env evalUnbounded)).runState s' := by
    rw [map_run, map_run, hD.1 hx, KatLang.FiniteLoop.ctx_run]
  have hne : ((writtenCall (CtxMsg.dotCall target F)
      ⟨fallback, target :: args, ctx, env, .dot target F fallback⟩).runState s').1 ≠ .error .fuelExhausted := by
    rw [hframe, map_run, KatLang.FiniteLoop.ctx_run]
    revert hx
    rcases (KatLang.DotFunnel.lexicalRun F target fallback (some args) ctx env evalUnbounded).runState s' with ⟨o, t⟩
    intro hx
    cases o with
    | ok v => nofun
    | error e => cases e <;> first | exact absurd rfl hx | nofun
  have heff : NeedPlan.effective ⟨.dotMember target F fallback none, args, ctx, env, .dot target F fallback⟩
      .extension = ⟨fallback, target :: args, ctx, env, .dot target F fallback⟩ := rfl
  have hmsg : NeedPlan.CallShape.ctxMsg ⟨.dotMember target F fallback none, args, ctx, env, .dot target F fallback⟩ =
      CtxMsg.dotCall target F := rfl
  have hw := ordinaryCall_is_written_call a ⟨.dotMember target F fallback none, args, ctx, env, .dot target F fallback⟩
    .extension (by decide) (by decide) (fun h => nomatch h) s' (by rw [heff, hmsg]; exact hne)
  rw [heff, hmsg] at hw
  rw [hw, hrhs]
  exact hframe

/-! ## The member route against the production dot evaluation

After the receiver probe selects a declared member, production runs `memberRun` named by the member
with the bound origin (`dot_member_run`); the plan runs the same `memberRun`, named by the member too
(`NeedPlan.writtenDispatchName`), with the written origin, once its structural projection of the
argumentless path reaches that member (`ordinaryCall_member_run`). `member_bridge_of_origin` joins
them into one run equality relative to the origin; `member_bridge` discharges the origin for a plain
first slot. The receiver premise and the remaining bundles are the next two sections. -/

/-- The member route's ONE run after the receiver: the alias-resolved selected member's production
    resolved call over the written bundle, named `name`, with callee origin `origin`. -/
def memberRun (owner : Algorithm) (p : PropDef) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (origin : CalleeOrigin) : EvalM CountedResult :=
  resolveAliasTarget (childOfInContext owner p.alg ctx) ctx >>= fun callee =>
    evalResolvedCallCounted callee args ctx env name origin

/-- **Production member dot call.** After a receiver probe completing at `(.ok alg?, s')` whose dot
    decision selects the declared member `p` of `owner`, the production dot evaluation
    `target.N(args)` from `s` is `memberRun` named by the member `N`, with origin `.bound owner p`,
    from `s'`, under `CtxMsg.dotCall target N`. -/
theorem dot_member_run (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hc : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (evalCounted (.dotMember target N fallback (some args)) ctx env).runState s =
      KatLang.FiniteLoop.ctxOutcome (CtxMsg.dotCall target N)
        ((memberRun owner p args ctx env N (.bound owner p)).runState s') := by
  have hu := production_unfolds (.evalCounted (.dotMember target N fallback (some args)) ctx env) s hc
  have hc' : ((withCtx (CtxMsg.dotCall target N)
      (evalDotCallCounted target N fallback (some args) ctx env)).runState s).1 ≠ .error .fuelExhausted := by
    change ((evalStep evalUnbounded (.evalCounted (.dotMember target N fallback (some args)) ctx env)).runState s).1 ≠ _
    rw [hu]; exact hc
  change (evalUnbounded (.evalCounted (.dotMember target N fallback (some args)) ctx env)).runState s = _
  rw [← hu]
  change (withCtx (CtxMsg.dotCall target N) (evalDotCallCounted target N fallback (some args) ctx env)).runState s = _
  have hd := complete_of_ctx _ _ s hc'
  have hu2 := production_unfolds (.evalDotCallCounted target N fallback (some args) ctx env) s hd
  rw [KatLang.FiniteLoop.ctx_run]
  change KatLang.FiniteLoop.ctxOutcome _
    ((evalUnbounded (.evalDotCallCounted target N fallback (some args) ctx env)).runState s) = _
  rw [← hu2]
  congr 1
  change (EvalBody.evalDotCallCounted evalUnbounded target N fallback (some args) ctx env).runState s = _
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState]
  have hp : (EvalRec.resolveDotReceiver? evalUnbounded target ctx).runState s = (.ok alg?, s') := hprobe
  rw [hp]
  simp only [hsel]
  rfl

/-- The production callee law of an argumentless member path, as a finite body. -/
def calleeBody (f : Expr) (ctx : EvalCtx) (rec : EvalRec) : EvalM Algorithm :=
  rec.projectNeedStructuralMember f ctx >>= fun o => match o with
    | some algorithm => rec.resolveAliasTarget algorithm ctx
    | none => .error (Error.notAnAlgorithm computedDotCalleeDescription)

theorem calleeBody_step (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx) (rec : EvalRec) :
    evalStep rec (.resolveCalleeAlg (.dotMember target N fallback none) ctx) =
      calleeBody (.dotMember target N fallback none) ctx rec := by
  show EvalBody.resolveCalleeAlg rec _ ctx = _
  unfold EvalBody.resolveCalleeAlg resolveCalleeAlgWith calleeBody
  rfl

theorem finite_calleeBody (f : Expr) (ctx : EvalCtx) :
    KatLang.WhileRoundProduction.Finite (calleeBody f ctx) := by
  unfold calleeBody
  refine KatLang.WhileRoundProduction.finite_bind (KatLang.WhileRoundProduction.finite_call _) (fun o => ?_)
  cases o with
  | some algorithm => exact KatLang.WhileRoundProduction.finite_call _
  | none => exact KatLang.WhileRoundProduction.finite_const _

/-- **The plan's member callee phase.** When the structural projection of the argumentless member
    path reaches the selected member at `s'`, and the alias resolution of that member completes there,
    the production callee law of the path from `s` is that alias resolution from `s'`. -/
theorem member_callee_run (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx) (s s' : EvalState)
    (owner : Algorithm) (p : PropDef)
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hres : ProductionCompletes (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx) s') :
    (resolveCalleeAlg (.dotMember target N fallback none) ctx).runState s =
      (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' := by
  have hrun : (calleeBody (.dotMember target N fallback none) ctx evalUnbounded).runState s =
      (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' := by
    unfold calleeBody
    rw [bind_run]
    have hp : (EvalRec.projectNeedStructuralMember evalUnbounded (.dotMember target N fallback none) ctx).runState s =
        (.ok (some (childOfInContext owner p.alg ctx)), s') := hproj
    rw [hp]
    rfl
  have hcb : ProductionCompletes (calleeBody (.dotMember target N fallback none) ctx evalUnbounded) s := by
    unfold ProductionCompletes; rw [hrun]; exact hres
  exact (KatLang.WhileRoundProduction.production_eq_of_finite _ _
    (calleeBody_step target N fallback ctx) (finite_calleeBody _ ctx) s hcb).trans hrun

theorem finite_memberProjection (receiver : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx) :
    KatLang.WhileRoundProduction.Finite
      (fun rec => EvalBody.projectNeedStructuralMember rec (.dotMember receiver N fallback none) ctx) := by
  unfold EvalBody.projectNeedStructuralMember
  dsimp only
  refine KatLang.WhileRoundProduction.finite_bind (KatLang.WhileRoundProduction.finite_call _) (fun container => ?_)
  cases container with
  | none => exact KatLang.WhileRoundProduction.finite_const _
  | some selected =>
    dsimp only
    refine KatLang.WhileRoundProduction.finite_bind (KatLang.WhileRoundProduction.finite_call _) (fun alg? => ?_)
    cases alg? with
    | none => exact KatLang.WhileRoundProduction.finite_const _
    | some algorithm => exact KatLang.WhileRoundProduction.finite_const _

/-- A member selection is a declared, accessible member. -/
theorem select_member (ctx : EvalCtx) (target : Expr) (N : Ident) (owner owner' : Algorithm) (p : PropDef)
    (hsel : selectDotEdge ctx target N (some owner) = .ok (.member owner' p)) :
    owner' = owner ∧ Algorithm.lookupPropDefAny? owner N = some p ∧ memberAccessible? ctx owner p = true := by
  unfold selectDotEdge at hsel
  dsimp only at hsel
  cases hq : Algorithm.lookupPropDefAny? owner N with
  | none =>
    rw [hq] at hsel
    dsimp only at hsel
    split at hsel <;> cases hsel
  | some q =>
    rw [hq] at hsel
    dsimp only at hsel
    split at hsel
    · cases hsel
    · rename_i hacc
      cases hsel
      exact ⟨rfl, rfl, by simpa using hacc⟩

/-- **The receiver premise, discharged for a named receiver.** For `n.N` with `n` a name, the
    plan's structural projection of the argumentless path and the production receiver probe make
    the SAME lookup and structure read: when the probe completes at `(.ok (some owner), s')` and
    selects the member `p`, the projection reaches `p`'s member at `s'`. -/
theorem member_projection_of_probe (n N : Ident) (fallback : Expr) (ctx : EvalCtx) (s s' : EvalState)
    (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hsel : selectDotEdge ctx (.resolve n) N (some owner) = .ok (.member owner p)) :
    (projectNeedStructuralMember (.dotMember (.resolve n) N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s') := by
  obtain ⟨-, hlook, hacc⟩ := select_member ctx (.resolve n) N owner owner p hsel
  have hpc : ProductionCompletes (resolveDotReceiver? (.resolve n) ctx) s := by
    unfold ProductionCompletes; rw [hprobe]; nofun
  have hpu := production_unfolds (.resolveDotReceiver? (.resolve n) ctx) s hpc
  have hprobe' : (EvalBody.resolveDotReceiver? evalUnbounded (.resolve n) ctx).runState s = (.ok (some owner), s') :=
    hpu.trans hprobe
  unfold EvalBody.resolveDotReceiver? at hprobe'
  cases hcs : ctx.callStack with
  | nil =>
    rw [hcs] at hprobe'
    cases hprobe'
  | cons top rest =>
    rw [hcs] at hprobe'
    dsimp only at hprobe'
    rw [bind_run] at hprobe'
    rcases hl : (lookupLexicalPropertyRaw top n ctx).runState s with ⟨lo, t⟩
    rw [hl] at hprobe'
    cases lo with
    | error e => cases hprobe'
    | ok resolved =>
      dsimp only at hprobe'
      -- the head projection is answer-free
      have hhead : (projectNeedStructuralMember (.resolve n) ctx).runState s = (.ok (some resolved.alg), t) := by
        apply KatLang.WhileRoundProduction.production_of_answer_free _ s
        · intro rec
          show (EvalBody.projectNeedStructuralMember rec (.resolve n) ctx).runState s = _
          unfold EvalBody.projectNeedStructuralMember
          rw [hcs]
          dsimp only
          rw [bind_run, hl]
          rfl
        · nofun
      have hstr : (resolveAliasStructure resolved.alg ctx).runState t = (.ok (some owner), s') := hprobe'
      have hbody : (EvalBody.projectNeedStructuralMember evalUnbounded (.dotMember (.resolve n) N fallback none) ctx).runState s =
          (.ok (some (childOfInContext owner p.alg ctx)), s') := by
        unfold EvalBody.projectNeedStructuralMember
        dsimp only
        rw [bind_run]
        have hh : (EvalRec.projectNeedStructuralMember evalUnbounded (.resolve n) ctx).runState s =
            (.ok (some resolved.alg), t) := hhead
        rw [hh]
        dsimp only
        rw [bind_run]
        have hs : (EvalRec.resolveAliasStructure evalUnbounded resolved.alg ctx).runState t = (.ok (some owner), s') := hstr
        rw [hs]
        dsimp only
        rw [hlook]
        dsimp only
        rw [hacc]
        rfl
      have hcb : ProductionCompletes
          (EvalBody.projectNeedStructuralMember evalUnbounded (.dotMember (.resolve n) N fallback none) ctx) s := by
        unfold ProductionCompletes; rw [hbody]; nofun
      exact (KatLang.WhileRoundProduction.production_eq_of_finite
        (.projectNeedStructuralMember (.dotMember (.resolve n) N fallback none) ctx)
        (fun rec => EvalBody.projectNeedStructuralMember rec (.dotMember (.resolve n) N fallback none) ctx)
        (fun _ => rfl)
        (finite_memberProjection (.resolve n) N fallback ctx) s hcb).trans hbody

/-- **STEP 1, member route (plan side).** When the plan's structural projection of the argumentless
    member path `target.N` reaches the selected member at `s'` and the member run completes there,
    the member-route ordinary call from `s` is `memberRun` named by the MEMBER `N`
    (`NeedPlan.writtenDispatchName`, E-18 member-route correction), with the written origin, from
    `s'`, under `CtxMsg.dotCall target N`. -/
theorem ordinaryCall_member_run (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hcomp : ProductionCompletes (memberRun owner p args ctx env N
      (.written (.dotMember target N fallback none) ctx)) s') :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> withCtx (CtxMsg.dotCall target N)
        (memberRun owner p args ctx env N (.written (.dotMember target N fallback none) ctx))).runState s' := by
  have hres : ProductionCompletes (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx) s' := by
    intro h; apply hcomp; unfold memberRun; rw [bind_run]
    revert h
    rcases (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' with ⟨o, t⟩
    intro h; simp only at h; subst h; rfl
  have hcal := member_callee_run target N fallback ctx s s' owner p hproj hres
  have hframe : (writtenCallNamed (CtxMsg.dotCall target N)
      ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩ N).runState s =
      (reCountValueBoundary <$> withCtx (CtxMsg.dotCall target N)
        (memberRun owner p args ctx env N (.written (.dotMember target N fallback none) ctx))).runState s' := by
    rw [writtenCallNamed_framed, map_run, map_run, KatLang.FiniteLoop.ctx_run, KatLang.FiniteLoop.ctx_run]
    dsimp only
    unfold memberRun
    rw [bind_run, bind_run, hcal]
  have hne : ((writtenCallNamed (CtxMsg.dotCall target N)
      ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩ N).runState s).1 ≠
      .error .fuelExhausted := by
    rw [hframe, map_run, KatLang.FiniteLoop.ctx_run]
    revert hcomp
    unfold ProductionCompletes
    rcases (memberRun owner p args ctx env N (.written (.dotMember target N fallback none) ctx)).runState s' with ⟨o, t⟩
    intro hx
    cases o with
    | ok v => nofun
    | error e => cases e <;> first | exact absurd rfl hx | nofun
  have hw := ordinaryCall_is_written_call_named a
    ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩ .call (by decide) (by decide) s hne
  exact hw.trans hframe

/-- The callee origin of a member run is not read for a nonempty bundle whose first slot is no
    spread (E-17, `resolved_origin_independent`). -/
theorem memberRun_origin_independent (owner : Algorithm) (p : PropDef) (e : Expr) (rest : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (o₁ o₂ : CalleeOrigin) (hsp : ¬ ∃ x, e = .sequenceSpread x) :
    memberRun owner p (e :: rest) ctx env name o₁ = memberRun owner p (e :: rest) ctx env name o₂ := by
  unfold memberRun
  congr 1
  funext callee
  exact KatLang.DotFunnel.resolved_origin_independent o₁ o₂ callee e rest ctx env name hsp

/-- A completed production member dot call has a completed member run after its probe. -/
theorem memberRun_completes_of_dot (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    ProductionCompletes (memberRun owner p args ctx env N (.bound owner p)) s' := by
  have hD := dot_member_run target N fallback args ctx env s s' alg? owner p hprobe hsel hprod
  unfold ProductionCompletes at hprod ⊢
  rw [hD] at hprod
  exact (KatLang.FiniteLoop.ctxOutcome_fuel _ _).1 hprod

/-- **THE MEMBER BRIDGE, relative to the member run's origin.** After a receiver probe completing at
    `(.ok alg?, s')` that selects the declared member `p` of `owner`, with the plan's structural
    projection of the argumentless path reaching that member at `s'`: whenever the member run does
    not distinguish the plan's WRITTEN origin from production's BOUND origin at `s'` (`horigin`), the
    member-route ordinary call IS the re-counted production dot evaluation `target.N(args)`, both
    run from the SAME state `s` — outcome, error context and final state. `member_bridge` discharges
    `horigin` for a bundle with a plain first slot, `member_bridge_inert` for every bundle over a
    receiver whose navigation is state-inert. -/
theorem member_bridge_of_origin (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (horigin : (memberRun owner p args ctx env N (.written (.dotMember target N fallback none) ctx)).runState s' =
      (memberRun owner p args ctx env N (.bound owner p)).runState s')
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s := by
  have hbound := memberRun_completes_of_dot target N fallback args ctx env s s' alg? owner p hprobe hsel hprod
  have hplan : ProductionCompletes (memberRun owner p args ctx env N
      (.written (.dotMember target N fallback none) ctx)) s' := by
    unfold ProductionCompletes at hbound ⊢; rw [horigin]; exact hbound
  rw [ordinaryCall_member_run a target N fallback args ctx env s s' owner p hproj hplan, map_run, map_run,
    dot_member_run target N fallback args ctx env s s' alg? owner p hprobe hsel hprod,
    KatLang.FiniteLoop.ctx_run, horigin]

/-- **STEP 1, member route against the production dot evaluation.** After a receiver probe
    completing at `(.ok alg?, s')` — the plan route's own classification step (`classify_dot`) —
    that selects the declared member `p` of `owner`, and with the plan's structural projection of
    the argumentless path reaching that member at `s'`: for a bundle `e :: rest` whose first slot is
    no spread, the member-route ordinary call IS the re-counted production dot evaluation
    `target.N(e, …)`, both run from the SAME state `s` — outcome (the failing dispatch's
    `noMatchingBranch N` included), error context `CtxMsg.dotCall target N` and final state.
    Completion is assumed of the production dot evaluation only. -/
theorem member_bridge (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (e : Expr) (rest : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hproj : (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s'))
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, e :: rest, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env).runState s :=
  member_bridge_of_origin a target N fallback (e :: rest) ctx env s s' alg? owner p hprobe hsel hproj
    (by rw [memberRun_origin_independent owner p e rest ctx env N
      (.written (.dotMember target N fallback none) ctx) (.bound owner p) hsp]) hprod

/-- **`member_bridge` for a named receiver `n.N(e, …)`**, its receiver premise discharged by
    `member_projection_of_probe`: only the probe, the member selection and the production
    completion remain. -/
theorem member_bridge_named (a : Nat) (n N : Ident) (fallback : Expr) (e : Expr) (rest : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? (.resolve n) ctx).runState s = (.ok (some owner), s'))
    (hsel : selectDotEdge ctx (.resolve n) N (some owner) = .ok (.member owner p))
    (hprod : ProductionCompletes (evalCounted (.dotMember (.resolve n) N fallback (some (e :: rest))) ctx env) s) :
    (ordinaryCall productionPlanRoute a
        ⟨.dotMember (.resolve n) N fallback none, e :: rest, ctx, env, .dot (.resolve n) N fallback⟩ .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember (.resolve n) N fallback (some (e :: rest))) ctx env).runState s :=
  member_bridge a (.resolve n) N fallback e rest ctx env s s' (some owner) owner p hsp hprobe hsel
    (member_projection_of_probe n N fallback ctx s s' owner p hprobe hsel) hprod

/-! ## The receiver premise, for every receiver path

`member_bridge` assumes that the plan's structural projection of the argumentless path `target.N`
reaches the member the production probe selected, at the probe's exit state (`hproj`). This section
discharges it from the probe and the selection alone for every receiver that CAN select a member:
a name, an inline block, and any argumentless member path over them (`Lib.Sub.N`), and — under one
decidable condition on the supplied cell's CALLABLE — a parameter and any path over a parameter.
Every other receiver head (a literal, a capture, a call or dot RESULT) has no member: the probe
gives it no identity or a memberless carrier (`resolveAlg_memberless`), so it never takes the member
route. -/

/-- An algorithm whose STRUCTURE is itself (M4★): no alias, or a structural carrier. Every
    STRUCTURE chase ends at one (`EvalBody.resolveAliasChase`, `followCarriers = false`). -/
def structureNormal : Algorithm → Bool
  | .alias _ _ _ _ _ reference => !reference
  | _ => true

/-- The STRUCTURE of a structure-normal algorithm is itself, read without any state change. -/
theorem resolveAliasStructure_normal (g : Algorithm) (c : EvalCtx) (hg : structureNormal g = true) :
    resolveAliasStructure g c = pure (some g) := by
  apply EvalM.ext; intro s
  have h2 : (evalFuel 2 (.resolveAliasStructure g c)).runState s = (.ok (some g), s) := by
    cases g with
    | «alias» p op pr t id reference =>
      cases reference with
      | true => simp [structureNormal] at hg
      | false => rfl
    | mk p pp op pr out id => rfl
    | builtin b => rfl
    | conditional p op bs id => rfl
  exact ((production_completes_iff _ s _).2
    ⟨2, h2, (evalFuel_completes_iff 2 _ s).2 (by rw [h2]; nofun)⟩).1

/-- The receiver's STRUCTURE as the plan's callee law reads it (`EvalBody.projectNeedStructuralMember`'s
    dot arm): the structural projection of the receiver, then its structure. -/
def projectedStructure (target : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  projectNeedStructuralMember target ctx >>= fun container =>
    match container with
    | some selected => resolveAliasStructure selected ctx
    | none => pure none

/-- The parameter an argumentless receiver path is rooted at, if any (`Expr.isParamHeaded`). -/
def headParam? : Expr → Option Ident
  | .param x => some x
  | .dotMember receiver _ _ none => headParam? receiver
  | _ => none

/-- **One member step of the plan's projection.** When the receiver's projected structure is `owner`
    at `s'` and `owner` declares the accessible member `p` named `N`, the structural projection of
    the argumentless path `target.N` is `p`'s member, wired to `owner`, at `s'`. -/
theorem member_projection_run (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx) (s s' : EvalState)
    (owner : Algorithm) (p : PropDef)
    (hstruct : (projectedStructure target ctx).runState s = (.ok (some owner), s'))
    (hlook : Algorithm.lookupPropDefAny? owner N = some p) (hacc : memberAccessible? ctx owner p = true) :
    (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s') := by
  unfold projectedStructure at hstruct
  rw [bind_run] at hstruct
  rcases hh : (projectNeedStructuralMember target ctx).runState s with ⟨o, t⟩
  rw [hh] at hstruct
  cases o with
  | error e => cases hstruct
  | ok container =>
    cases container with
    | none => cases hstruct
    | some selected =>
      have hs : (resolveAliasStructure selected ctx).runState t = (.ok (some owner), s') := hstruct
      have hbody : (EvalBody.projectNeedStructuralMember evalUnbounded (.dotMember target N fallback none) ctx).runState s =
          (.ok (some (childOfInContext owner p.alg ctx)), s') := by
        unfold EvalBody.projectNeedStructuralMember
        dsimp only
        rw [bind_run]
        have hh' : (EvalRec.projectNeedStructuralMember evalUnbounded target ctx).runState s =
            (.ok (some selected), t) := hh
        rw [hh']
        dsimp only
        rw [bind_run]
        have hs' : (EvalRec.resolveAliasStructure evalUnbounded selected ctx).runState t = (.ok (some owner), s') := hs
        rw [hs']
        dsimp only
        rw [hlook]
        dsimp only
        rw [hacc]
        rfl
      have hcb : ProductionCompletes
          (EvalBody.projectNeedStructuralMember evalUnbounded (.dotMember target N fallback none) ctx) s := by
        unfold ProductionCompletes; rw [hbody]; nofun
      exact (KatLang.WhileRoundProduction.production_eq_of_finite
        (.projectNeedStructuralMember (.dotMember target N fallback none) ctx)
        (fun rec => EvalBody.projectNeedStructuralMember rec (.dotMember target N fallback none) ctx)
        (fun _ => rfl)
        (finite_memberProjection target N fallback ctx) s hcb).trans hbody

theorem lookup_of_props_nil (w : Algorithm) (N : Ident) (h : w.props = []) :
    Algorithm.lookupPropDefAny? w N = none := by
  simp [Algorithm.lookupPropDefAny?, KatLang.lookupPropDefAny?, h]

/-- A runtime wrapper over written rows declares no member. -/
theorem wrapper_props (ctx : EvalCtx) (rows : OutputBundle) (id : Option PropertyIdentity) :
    ((wireToCaller ctx (Algorithm.mk none [] [] [] rows)).withDeclarationId id).props = [] := by
  unfold wireToCaller
  cases ctx.callStack.head? <;> rfl

/-- **A value head has no member.** The canonical resolution of any written expression other than a
    name, an inline block or a parameter is a failure or a MEMBERLESS runtime wrapper (a capture's
    value thunk, the carrier of a dot result). -/
theorem resolveAlg_memberless (e : Expr) (ctx : EvalCtx) (s s' : EvalState) (w : Algorithm)
    (hr : ∀ n, e ≠ .resolve n) (hb : ∀ a, e ≠ .algorithmExpr a) (hp : ∀ x, e ≠ .param x)
    (h : (resolveAlg e ctx).runState s = (.ok w, s')) : w.props = [] := by
  have hc : ProductionCompletes (resolveAlg e ctx) s := by unfold ProductionCompletes; rw [h]; nofun
  have hu := production_unfolds (.resolveAlg e ctx) s hc
  have h' : (EvalBody.resolveAlg evalUnbounded e ctx).runState s = (.ok w, s') := hu.trans h
  cases e with
  | resolve n => exact absurd rfl (hr n)
  | algorithmExpr a => exact absurd rfl (hb a)
  | param x => exact absurd rfl (hp x)
  | capture rows =>
    have h'' : ((Except.ok ((wireToCaller ctx (Algorithm.mk none [] [] [] rows)).withDeclarationId
        (some (.runtime s.nextRuntimeDeclaration))) : Except Error Algorithm),
        ({ s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 } : EvalState)) = (.ok w, s') := h'
    injection h'' with h1 _
    injection h1 with h1
    subst h1
    exact wrapper_props ctx rows _
  | dotMember o n fb args =>
    have h'' : ((Except.ok ((wireToCaller ctx (Algorithm.mk none [] [] [] [.dotMember o n fb args])).withDeclarationId
        (some (.runtime s.nextRuntimeDeclaration))) : Except Error Algorithm),
        ({ s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 } : EvalState)) = (.ok w, s') := h'
    injection h'' with h1 _
    injection h1 with h1
    subst h1
    exact wrapper_props ctx _ _
  | _ => cases h'

/-- The probe of a value head (anything but a name, a block, a parameter or an argumentless member
    edge): an attempt of its canonical resolution, absence reported as `none`. -/
def valueHeadProbe (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
  match ← evalAttempt (rec.resolveAlg e ctx) with
  | .ok a => pure (some a)
  | .error (.notAnAlgorithm _) => pure none
  | .error err => .error err

/-- A value head's probe result declares no member. -/
theorem valueHeadProbe_memberless (e : Expr) (ctx : EvalCtx) (s s' : EvalState) (owner : Algorithm)
    (hr : ∀ n, e ≠ .resolve n) (hb : ∀ a, e ≠ .algorithmExpr a) (hp : ∀ x, e ≠ .param x)
    (h : (valueHeadProbe evalUnbounded e ctx).runState s = (.ok (some owner), s')) : owner.props = [] := by
  unfold valueHeadProbe at h
  rw [bind_run, evalAttempt_run] at h
  have hra : (EvalRec.resolveAlg evalUnbounded e ctx).runState s = (resolveAlg e ctx).runState s := rfl
  rw [hra] at h
  rcases hrun : (resolveAlg e ctx).runState s with ⟨o, t⟩
  rw [hrun] at h
  cases o with
  | ok w =>
    have h1 : ((Except.ok (some w) : Except Error (Option Algorithm)), t) = (.ok (some owner), s') := h
    injection h1 with h2 h3
    injection h2 with h2
    injection h2 with h2
    subst h2 h3
    exact resolveAlg_memberless e ctx s t w hr hb hp hrun
  | error err => cases err <;> cases h

/-- **THE PROBE IS THE PLAN'S PROJECTED STRUCTURE.** Whenever the production receiver probe of
    `target` completes at `(.ok (some owner), s')` with an `owner` that declares a member, the
    receiver's structure as the plan's callee law reads it (`projectedStructure`) is `owner` at the
    same state `s'`: a name and an inline block make the same lookup and structure read; an
    argumentless member edge navigates the same declared member (by recursion on the path); a value
    head never yields a member-declaring identity. A PARAMETER head is its supplied cell's CALLABLE
    on both sides, which the plan's projection reads through its structure once more: the two agree
    when that CALLABLE is structure-normal (`hnorm`) — what every STRUCTURE chase returns. -/
theorem probe_is_projected_structure : ∀ (target : Expr) (ctx : EvalCtx) (s s' : EvalState)
    (owner : Algorithm) (N : Ident) (p : PropDef),
    (resolveDotReceiver? target ctx).runState s = (.ok (some owner), s') →
    Algorithm.lookupPropDefAny? owner N = some p →
    (∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true) →
    (projectedStructure target ctx).runState s = (.ok (some owner), s')
  | target, ctx, s, s', owner, N, p, hprobe, hlook, hnorm => by
    have hpc : ProductionCompletes (resolveDotReceiver? target ctx) s := by
      unfold ProductionCompletes; rw [hprobe]; nofun
    have hpu := production_unfolds (.resolveDotReceiver? target ctx) s hpc
    have hprobe' : (EvalBody.resolveDotReceiver? evalUnbounded target ctx).runState s = (.ok (some owner), s') :=
      hpu.trans hprobe
    have hvalue : ∀ e : Expr, (∀ n, e ≠ .resolve n) → (∀ a, e ≠ .algorithmExpr a) → (∀ x, e ≠ .param x) →
        (valueHeadProbe evalUnbounded e ctx).runState s = (.ok (some owner), s') → False := by
      intro e hr hb hp h
      have := lookup_of_props_nil owner N (valueHeadProbe_memberless e ctx s s' owner hr hb hp h)
      rw [this] at hlook; cases hlook
    match target with
    | .resolve n =>
      unfold EvalBody.resolveDotReceiver? at hprobe'
      cases hcs : ctx.callStack with
      | nil => rw [hcs] at hprobe'; cases hprobe'
      | cons top rest =>
        rw [hcs] at hprobe'
        dsimp only at hprobe'
        rw [bind_run] at hprobe'
        rcases hl : (lookupLexicalPropertyRaw top n ctx).runState s with ⟨lo, t⟩
        rw [hl] at hprobe'
        cases lo with
        | error e => cases hprobe'
        | ok resolved =>
          have hhead : (projectNeedStructuralMember (.resolve n) ctx).runState s = (.ok (some resolved.alg), t) := by
            apply KatLang.WhileRoundProduction.production_of_answer_free _ s
            · intro rec
              show (EvalBody.projectNeedStructuralMember rec (.resolve n) ctx).runState s = _
              unfold EvalBody.projectNeedStructuralMember
              rw [hcs]
              dsimp only
              rw [bind_run, hl]
              rfl
            · nofun
          have hstr : (resolveAliasStructure resolved.alg ctx).runState t = (.ok (some owner), s') := hprobe'
          unfold projectedStructure
          rw [bind_run, hhead]
          exact hstr
    | .algorithmExpr a =>
      have hhead : (projectNeedStructuralMember (.algorithmExpr a) ctx).runState s =
          (.ok (some (wireToCaller ctx a)), s) := by
        apply KatLang.WhileRoundProduction.production_of_answer_free _ s
        · intro rec; rfl
        · nofun
      have hstr : (resolveAliasStructure (wireToCaller ctx a) ctx).runState s = (.ok (some owner), s') := hprobe'
      unfold projectedStructure
      rw [bind_run, hhead]
      exact hstr
    | .param x =>
      have hcall : (projectParameterCallable x ctx).runState s = (.ok (some owner), s') := hprobe'
      have hhead : (projectNeedStructuralMember (.param x) ctx).runState s = (.ok (some owner), s') := by
        have hcb : ProductionCompletes ((fun rec : EvalRec => rec (.projectParameterCallable x ctx)) evalUnbounded) s := by
          unfold ProductionCompletes
          show ((projectParameterCallable x ctx).runState s).1 ≠ _
          rw [hcall]; nofun
        exact (KatLang.WhileRoundProduction.production_eq_of_finite (.projectNeedStructuralMember (.param x) ctx)
          (fun rec => rec (.projectParameterCallable x ctx)) (fun _ => rfl)
          (KatLang.WhileRoundProduction.finite_call _) s hcb).trans hcall
      unfold projectedStructure
      rw [bind_run, hhead]
      dsimp only
      rw [resolveAliasStructure_normal owner ctx (hnorm x owner s' rfl hcall)]
      rfl
    | .dotMember o n fb none =>
      unfold EvalBody.resolveDotReceiver? at hprobe'
      dsimp only at hprobe'
      rw [bind_run] at hprobe'
      rcases hpo : (resolveDotReceiver? o ctx).runState s with ⟨ro, s1⟩
      have hpo' : (EvalRec.resolveDotReceiver? evalUnbounded o ctx).runState s = (ro, s1) := hpo
      rw [hpo'] at hprobe'
      -- every non-navigating arm ends in the memberless carrier of the dot result
      have hcarrier : ∀ t : EvalState,
          ((some <$> EvalRec.resolveAlg evalUnbounded (.dotMember o n fb none) ctx : EvalM (Option Algorithm)).runState t =
            (.ok (some owner), s')) → False := by
        intro t h
        rw [map_run] at h
        have hra : (EvalRec.resolveAlg evalUnbounded (.dotMember o n fb none) ctx).runState t =
            (resolveAlg (.dotMember o n fb none) ctx).runState t := rfl
        rw [hra] at h
        rcases hrun : (resolveAlg (.dotMember o n fb none) ctx).runState t with ⟨r, u⟩
        rw [hrun] at h
        cases r with
        | error e => cases h
        | ok w =>
          have h1 : ((Except.ok (some w) : Except Error (Option Algorithm)), u) = (.ok (some owner), s') := h
          injection h1 with h2 h3
          injection h2 with h2
          injection h2 with h2
          subst h2 h3
          have := lookup_of_props_nil w N (resolveAlg_memberless _ ctx t u w (by nofun) (by nofun) (by nofun) hrun)
          rw [this] at hlook; cases hlook
      cases ro with
      | error e => cases hprobe'
      | ok r? =>
        dsimp only at hprobe'
        cases r? with
        | none => exact (hcarrier s1 hprobe').elim
        | some a =>
          dsimp only at hprobe'
          cases hl : Algorithm.lookupPropDefAny? a n with
          | none =>
            rw [hl] at hprobe'
            dsimp only at hprobe'
            split at hprobe'
            · cases hprobe'
            · exact (hcarrier s1 hprobe').elim
          | some q =>
            rw [hl] at hprobe'
            dsimp only at hprobe'
            split at hprobe'
            · cases hprobe'
            · rename_i hacc
              rw [bind_run] at hprobe'
              rcases hst : (resolveAliasStructure (childOfInContext a q.alg ctx) ctx).runState s1 with ⟨so, s2⟩
              have hst' : (EvalRec.resolveAliasStructure evalUnbounded (childOfInContext a q.alg ctx) ctx).runState s1 =
                  (so, s2) := hst
              rw [hst'] at hprobe'
              cases so with
              | error e => cases hprobe'
              | ok m? =>
                dsimp only at hprobe'
                cases m? with
                | none => exact (hcarrier s2 hprobe').elim
                | some member =>
                  have h1 : ((Except.ok (some member) : Except Error (Option Algorithm)), s2) =
                      (.ok (some owner), s') := hprobe'
                  injection h1 with h2 h3
                  injection h2 with h2
                  injection h2 with h2
                  subst h2 h3
                  have hacc' : memberAccessible? ctx a q = true := by simpa using hacc
                  have ih := probe_is_projected_structure o ctx s s1 a n q hpo hl
                    (fun x o' t hx => hnorm x o' t (by simpa [headParam?] using hx))
                  have hstep := member_projection_run o n fb ctx s s1 a q ih hl hacc'
                  unfold projectedStructure
                  rw [bind_run, hstep]
                  exact hst
    | .dotMember o n fb (some args) =>
      exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .num v => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .stringLiteral v => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .interpolatedString h l => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .boolLiteral b => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .unary op e => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .binary op e₁ e₂ => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .comparison e l => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .index e l => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .sequenceConstruct e₁ e₂ => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .emptySequence d => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .sequenceSpread e => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .listLiteral l => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .capture rows => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim
    | .call f args => exact (hvalue _ (by nofun) (by nofun) (by nofun) hprobe').elim

/-- **The receiver premise of `member_bridge`, discharged for every receiver.** After a probe
    completing at `(.ok alg?, s')` that selects the declared member `p` of `owner`, the plan's
    structural projection of the argumentless path `target.N` reaches that member at `s'` — for a
    name, an inline block or any member path over them outright, and for a parameter-rooted receiver
    when the head parameter's CALLABLE is structure-normal (`hnorm`; vacuous otherwise). -/
theorem member_projection_of_selection (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx)
    (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hnorm : ∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true) :
    (projectNeedStructuralMember (.dotMember target N fallback none) ctx).runState s =
      (.ok (some (childOfInContext owner p.alg ctx)), s') := by
  cases alg? with
  | none => simp [selectDotEdge] at hsel
  | some owner' =>
    obtain ⟨rfl, hlook, hacc⟩ := select_member ctx target N owner' owner p hsel
    exact member_projection_run target N fallback ctx s s' owner p
      (probe_is_projected_structure target ctx s s' owner N p hprobe hlook hnorm) hlook hacc

/-- A receiver that is not rooted at a parameter has no parameter head. -/
theorem headParam_none_of_not_paramHeaded : ∀ (target : Expr), target.isParamHeaded = false → headParam? target = none
  | .param _, h => by simp [Expr.isParamHeaded] at h
  | .dotMember receiver _ _ none, h =>
    headParam_none_of_not_paramHeaded receiver (by simpa [Expr.isParamHeaded] using h)
  | .dotMember _ _ _ (some _), _ => rfl
  | .num _, _ => rfl
  | .stringLiteral _, _ => rfl
  | .interpolatedString _ _, _ => rfl
  | .boolLiteral _, _ => rfl
  | .unary _ _, _ => rfl
  | .binary _ _ _, _ => rfl
  | .comparison _ _, _ => rfl
  | .index _ _, _ => rfl
  | .sequenceConstruct _ _, _ => rfl
  | .emptySequence _, _ => rfl
  | .sequenceSpread _, _ => rfl
  | .listLiteral _, _ => rfl
  | .resolve _, _ => rfl
  | .algorithmExpr _, _ => rfl
  | .capture _, _ => rfl
  | .call _ _, _ => rfl

/-- **THE MEMBER BRIDGE for a receiver not rooted at a parameter** — a name, an inline block, any
    argumentless member path over them (`Lib.Sub.N(e, …)`) — with a plain first argument: only the
    probe, the member selection and the production completion remain. -/
theorem member_bridge_static (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (e : Expr) (rest : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hhead : target.isParamHeaded = false)
    (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, e :: rest, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env).runState s :=
  member_bridge a target N fallback e rest ctx env s s' alg? owner p hsp hprobe hsel
    (member_projection_of_selection target N fallback ctx s s' alg? owner p hprobe hsel
      (fun x _ _ hx => by rw [headParam_none_of_not_paramHeaded target hhead] at hx; cases hx)) hprod

/-- **THE MEMBER BRIDGE for a parameter-rooted receiver** (`b.N(e, …)`, `b.Sub.N(e, …)`), with a
    plain first argument, when the head parameter's supplied CALLABLE is structure-normal at the
    entry state: the probe reads that CALLABLE as the receiver, the plan's projection reads its
    structure once more, and the two coincide exactly then. -/
theorem member_bridge_param (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (e : Expr) (rest : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hnorm : ∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true)
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, e :: rest, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some (e :: rest))) ctx env).runState s :=
  member_bridge a target N fallback e rest ctx env s s' alg? owner p hsp hprobe hsel
    (member_projection_of_selection target N fallback ctx s s' alg? owner p hprobe hsel hnorm) hprod

/-! ## The callee origin: empty and spread-first bundles

The plan's member call carries the WRITTEN origin of its argumentless path, production's the BOUND
origin of the selected member (CACHE-PUB-1; C# has the same two origins). The origin is read only
when the formed supply is EMPTY (`evalSuppliedCallCounted`), through `EvalBody.originBinding?`, and
then the written origin NAVIGATES the receiver again. `member_bridge` covers every bundle that
cannot form an empty supply before its first plain slot. This section covers the rest — `t.N()`,
`t.N(xs*)` — for a receiver whose navigation is STATE-INERT (`NavInert`): a name bound in an
enclosing scope to a structure-normal algorithm, an inline block, and member paths over them. -/

open KatLang.WhileRoundProduction (Finite finite_const finite_call finite_bind production_eq_of_finite)
open KatLang.FiniteLoop (finite_evalAttempt)
open KatLang.PlanConservativity (isAliasAlg resolveAliasTarget_not_alias resolved_body_not_alias)

theorem finite_publicationBinding (owner : Algorithm) (binding : PropDef) (wired : Algorithm) (ctx : EvalCtx) :
    Finite (fun rec => EvalBody.publicationBinding? rec owner binding wired ctx) := by
  unfold EvalBody.publicationBinding?
  cases wired with
  | «alias» p op pr t id r => exact finite_call _
  | mk p pp op pr out id => exact finite_const _
  | builtin b => exact finite_const _
  | conditional p op bs id => exact finite_const _

theorem finite_writtenCalleeBinding (callee : Expr) (caller : EvalCtx) :
    Finite (fun rec => EvalBody.writtenCalleeBinding? rec callee caller) := by
  unfold EvalBody.writtenCalleeBinding?
  split
  · split
    · refine finite_bind (finite_const _) (fun r => ?_)
      cases r with
      | ok resolved => exact finite_publicationBinding _ _ _ _
      | error e => exact finite_const _
    · exact finite_const _
  · refine finite_bind (finite_evalAttempt (finite_call _)) (fun r => ?_)
    split
    · refine finite_bind (finite_evalAttempt (finite_call _)) (fun r' => ?_)
      split
      · split
        · exact finite_publicationBinding _ _ _ _
        · exact finite_const _
      · exact finite_const _
    · exact finite_const _
  · exact finite_const _

theorem finite_cellCalleeBinding (address : Nat) :
    Finite (fun rec => EvalBody.cellCalleeBinding? rec address) := by
  unfold EvalBody.cellCalleeBinding?
  refine finite_bind (finite_const _) (fun st => ?_)
  dsimp only
  split
  · exact finite_writtenCalleeBinding _ _
  · exact finite_const _

/-- Reading a callee origin's property binding is a finite body of the evaluator answer. -/
theorem finite_originBinding (o : CalleeOrigin) (ctx : EvalCtx) :
    Finite (fun rec => EvalBody.originBinding? rec o ctx) := by
  unfold EvalBody.originBinding?
  split
  · exact finite_const _
  · refine finite_bind (finite_const _) (fun activation => ?_)
    split
    · exact finite_cellCalleeBinding _
    · exact finite_const _
  · exact finite_writtenCalleeBinding _ _
  · exact finite_cellCalleeBinding _
  · exact finite_publicationBinding _ _ _ _

/-- The dispatch of a supplied call is a finite body of the evaluator answer, whatever its origin. -/
theorem finite_suppliedBody (o : CalleeOrigin) (g : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx)
    (env : ValEnv) (name : String) :
    Finite (fun rec => EvalBody.evalSuppliedCallCounted rec o g cells ctx env name) := by
  cases g with
  | builtin b => exact finite_call _
  | «alias» p op pr t id r =>
    exact finite_bind (B := fun rec : EvalRec => rec (.resolveAliasTarget (.alias p op pr t id r) ctx))
      (finite_call _) (fun _ => finite_call _)
  | mk p pp op pr out id =>
    unfold EvalBody.evalSuppliedCallCounted
    dsimp only
    split
    · refine finite_bind (finite_originBinding o ctx) (fun ob => ?_)
      split
      · exact finite_bind (B := fun rec : EvalRec => rec (.evalZeroArgPropertyAccessCounted .lexical _ _
          (.mk p pp op pr out id) ctx env (.invoke name))) (finite_call _) (fun _ => finite_const _)
      · exact finite_call _
    · exact finite_call _
  | conditional p op bs id =>
    unfold EvalBody.evalSuppliedCallCounted
    dsimp only
    have hrest : Finite (fun rec : EvalRec =>
        match flatBinderUserEquivalent? (.conditional p op bs id) with
        | some simple => rec.evalNeedUserSupply simple (cells.map Prod.fst) ctx env
        | none => rec.evalNeedFamilySupply (.conditional p op bs id) (cells.map Prod.fst) ctx env name) := by
      cases flatBinderUserEquivalent? (.conditional p op bs id) <;> exact finite_call _
    split
    · refine finite_bind (finite_originBinding o ctx) (fun ob => ?_)
      split
      · exact finite_bind (B := fun rec : EvalRec => rec (.evalZeroArgPropertyAccessCounted .lexical _ _
          (.conditional p op bs id) ctx env (.invoke name))) (finite_call _) (fun _ => finite_const _)
      · exact hrest
    · exact hrest

/-- Two origins whose property bindings read alike at `t` dispatch a normalized callee alike from
    `t`: the origin is consulted through `EvalBody.originBinding?` alone. -/
theorem supplied_origin_agrees (o₁ o₂ : CalleeOrigin) (g : Algorithm) (cells : List NeedSupply.Sourced)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (t : EvalState) (hg : isAliasAlg g = false)
    (hagree : (EvalBody.originBinding? evalUnbounded o₁ ctx).runState t =
      (EvalBody.originBinding? evalUnbounded o₂ ctx).runState t)
    (hc : ProductionCompletes (evalSuppliedCallCounted o₂ g cells ctx env name) t) :
    (evalSuppliedCallCounted o₁ g cells ctx env name).runState t =
      (evalSuppliedCallCounted o₂ g cells ctx env name).runState t := by
  have hu₂ := production_unfolds (.evalSuppliedCallCounted o₂ g cells ctx env name) t hc
  have hbody : (EvalBody.evalSuppliedCallCounted evalUnbounded o₁ g cells ctx env name).runState t =
      (EvalBody.evalSuppliedCallCounted evalUnbounded o₂ g cells ctx env name).runState t := by
    cases g with
    | builtin b => rfl
    | «alias» p op pr tg id r => simp [isAliasAlg] at hg
    | mk p pp op pr out id =>
      unfold EvalBody.evalSuppliedCallCounted
      dsimp only
      split
      · rw [bind_run, bind_run, hagree]
      · rfl
    | conditional p op bs id =>
      unfold EvalBody.evalSuppliedCallCounted
      dsimp only
      split
      · rw [bind_run, bind_run, hagree]
      · rfl
  have hc₁ : ProductionCompletes
      ((fun rec => EvalBody.evalSuppliedCallCounted rec o₁ g cells ctx env name) evalUnbounded) t := by
    unfold ProductionCompletes
    show ((EvalBody.evalSuppliedCallCounted evalUnbounded o₁ g cells ctx env name).runState t).1 ≠ _
    rw [hbody]
    have : (EvalBody.evalSuppliedCallCounted evalUnbounded o₂ g cells ctx env name).runState t =
        (evalSuppliedCallCounted o₂ g cells ctx env name).runState t := hu₂
    rw [this]; exact hc
  have h₁ := production_eq_of_finite (.evalSuppliedCallCounted o₁ g cells ctx env name)
    (fun rec => EvalBody.evalSuppliedCallCounted rec o₁ g cells ctx env name) (fun _ => rfl)
    (finite_suppliedBody o₁ g cells ctx env name) t hc₁
  exact h₁.trans (hbody.trans hu₂)

theorem finite_slot (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Finite (fun rec : EvalRec => NeedSupply.slot rec.evalSupplySpread ctx env e) := by
  unfold NeedSupply.slot
  split
  · refine finite_bind (finite_const _) (fun o => ?_)
    cases o with
    | some slice => exact finite_const _
    | none =>
      exact finite_bind (B := fun rec : EvalRec => rec (.evalSupplySpread _ ctx env)) (finite_call _)
        (fun sp => by cases sp <;> exact finite_const _)
  · exact finite_const _

/-- Supply formation is a finite body of the evaluator answer (only a computed spread re-enters it). -/
theorem finite_form (ctx : EvalCtx) (env : ValEnv) :
    ∀ args : OutputBundle, Finite (fun rec : EvalRec => NeedSupply.form rec.evalSupplySpread ctx env args)
  | [] => finite_const _
  | e :: rest =>
    finite_bind (finite_slot ctx env e) (fun _ => finite_bind (finite_form ctx env rest) (fun _ => finite_const _))

/-- Two origins whose property bindings read alike at every state make the resolved call of a
    normalized callee alike, over ANY bundle (an empty or spread-first one included). -/
theorem resolved_origin_agrees (o₁ o₂ : CalleeOrigin) (g : Algorithm) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (t : EvalState) (hg : isAliasAlg g = false)
    (hagree : ∀ u, (EvalBody.originBinding? evalUnbounded o₁ ctx).runState u =
      (EvalBody.originBinding? evalUnbounded o₂ ctx).runState u)
    (hc : ProductionCompletes (evalResolvedCallCounted g args ctx env name o₂) t) :
    (evalResolvedCallCounted g args ctx env name o₁).runState t =
      (evalResolvedCallCounted g args ctx env name o₂).runState t := by
  have hu₂ := production_unfolds (.evalResolvedCallCounted g args ctx env name o₂) t hc
  have hb₂ : (evalResolvedCallCounted g args ctx env name o₂).runState t =
      (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t := by
    show (evalUnbounded (.evalResolvedCallCounted g args ctx env name o₂)).runState t = _
    rw [← hu₂]
    show (EvalBody.evalResolvedCallCounted evalUnbounded g args ctx env name o₂).runState t = _
    rw [resolved_body_not_alias _ _ _ _ _ _ _ hg]
    rfl
  have hbody : (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₁ g cells ctx env name).runState t =
      (NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t := by
    have hc' : ((NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₂ g cells ctx env name).runState t).1 ≠ .error .fuelExhausted := by
      rw [← hb₂]; exact hc
    rw [bind_run] at hc' ⊢
    rw [bind_run]
    rcases hf : (NeedSupply.form evalSupplySpread ctx env args).runState t with ⟨fo, t2⟩
    rw [hf] at hc'
    cases fo with
    | error e => rfl
    | ok cells => exact supplied_origin_agrees o₁ o₂ g cells ctx env name t2 hg (hagree t2) hc'
  have hstep : ∀ rec, evalStep rec (.evalResolvedCallCounted g args ctx env name o₁) =
      (NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
        rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) := by
    intro rec
    show EvalBody.evalResolvedCallCounted rec g args ctx env name o₁ = _
    rw [resolved_body_not_alias _ _ _ _ _ _ _ hg]
    rfl
  have hfin : Finite (fun rec : EvalRec => NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
      rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) :=
    finite_bind (finite_form ctx env args) (fun _ => finite_call _)
  have hc₁ : ProductionCompletes ((fun rec : EvalRec => NeedSupply.form rec.evalSupplySpread ctx env args >>= fun cells =>
      rec (.evalSuppliedCallCounted o₁ g cells ctx env name)) evalUnbounded) t := by
    unfold ProductionCompletes
    show ((NeedSupply.form evalSupplySpread ctx env args >>= fun cells =>
        evalSuppliedCallCounted o₁ g cells ctx env name).runState t).1 ≠ _
    rw [hbody, ← hb₂]; exact hc
  have h₁ := production_eq_of_finite (.evalResolvedCallCounted g args ctx env name o₁) _ hstep hfin t hc₁
  exact h₁.trans (hbody.trans hb₂.symm)

/-- Two origins whose property bindings read alike at every state make the member run alike, over
    any bundle. -/
theorem memberRun_origin_agrees (owner : Algorithm) (p : PropDef) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (o₁ o₂ : CalleeOrigin) (s' : EvalState)
    (hagree : ∀ u, (EvalBody.originBinding? evalUnbounded o₁ ctx).runState u =
      (EvalBody.originBinding? evalUnbounded o₂ ctx).runState u)
    (hc : ProductionCompletes (memberRun owner p args ctx env name o₂) s') :
    (memberRun owner p args ctx env name o₁).runState s' = (memberRun owner p args ctx env name o₂).runState s' := by
  unfold memberRun at hc ⊢
  unfold ProductionCompletes at hc
  rw [bind_run] at hc ⊢
  rw [bind_run]
  rcases hr : (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState s' with ⟨ro, t1⟩
  rw [hr] at hc
  cases ro with
  | error e => rfl
  | ok g =>
    exact resolved_origin_agrees o₁ o₂ g args ctx env name t1
      (resolveAliasTarget_not_alias _ ctx s' t1 g hr) hagree hc

/-- **State-inert receiver navigation.** From EVERY state, the receiver's structure as the plan's
    callee law reads it is `owner`, and reading it changes nothing: the navigation neither demands,
    projects nor allocates, so reading it again when the origin is consulted finds the same member. -/
def NavInert (target : Expr) (ctx : EvalCtx) (owner : Algorithm) : Prop :=
  ∀ t, (projectedStructure target ctx).runState t = (.ok (some owner), t)

/-- **Over a state-inert receiver, the written origin IS the bound origin**: at every state, the
    property binding the argumentless path `target.N` names is the selected member's. -/
theorem written_origin_is_bound (target : Expr) (N : Ident) (fallback : Expr) (ctx : EvalCtx)
    (owner : Algorithm) (p : PropDef) (hnav : NavInert target ctx owner)
    (hlook : Algorithm.lookupPropDefAny? owner N = some p) (t : EvalState) :
    (EvalBody.originBinding? evalUnbounded (.written (.dotMember target N fallback none) ctx) ctx).runState t =
      (EvalBody.originBinding? evalUnbounded (.bound owner p) ctx).runState t := by
  have hn := hnav t
  unfold projectedStructure at hn
  rw [bind_run] at hn
  rcases hh : (projectNeedStructuralMember target ctx).runState t with ⟨o, t1⟩
  rw [hh] at hn
  cases o with
  | error e => cases hn
  | ok container =>
    cases container with
    | none => cases hn
    | some selected =>
      have hs : (resolveAliasStructure selected ctx).runState t1 = (.ok (some owner), t) := hn
      have hh' : (EvalRec.projectNeedStructuralMember evalUnbounded target ctx).runState t =
          (.ok (some selected), t1) := hh
      have hs' : (EvalRec.resolveAliasStructure evalUnbounded selected ctx).runState t1 = (.ok (some owner), t) := hs
      unfold EvalBody.originBinding?
      dsimp only
      unfold EvalBody.writtenCalleeBinding?
      dsimp only
      rw [bind_run, evalAttempt_runState_of_complete _ t t1 _ hh' rfl]
      dsimp only
      rw [bind_run, evalAttempt_runState_of_complete _ t1 t _ hs' rfl]
      dsimp only
      rw [hlook]

/-- **THE MEMBER BRIDGE over a state-inert receiver, for EVERY bundle** — `t.N()`, `t.N(xs*)` and
    every other written list. After a probe completing at `(.ok alg?, s')` that selects the declared
    member `p` of `owner`, when the receiver's navigation is state-inert (`NavInert`; a
    parameter-rooted receiver additionally needs `hnorm`), the member-route ordinary call IS the
    re-counted production dot evaluation `target.N(args)`, both run from the SAME state `s` —
    outcome, error context, final state and the CACHE-PUB-1 publication an empty supply makes. -/
theorem member_bridge_inert (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm) (owner : Algorithm) (p : PropDef)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hsel : selectDotEdge ctx target N alg? = .ok (.member owner p))
    (hnorm : ∀ x o t, headParam? target = some x → (projectParameterCallable x ctx).runState s = (.ok (some o), t) →
      structureNormal o = true)
    (hnav : NavInert target ctx owner)
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s := by
  have hlook : Algorithm.lookupPropDefAny? owner N = some p := by
    cases alg? with
    | none => simp [selectDotEdge] at hsel
    | some owner' =>
      obtain ⟨rfl, hlook, -⟩ := select_member ctx target N owner' owner p hsel
      exact hlook
  exact member_bridge_of_origin a target N fallback args ctx env s s' alg? owner p hprobe hsel
    (member_projection_of_selection target N fallback ctx s s' alg? owner p hprobe hsel hnorm)
    (memberRun_origin_agrees owner p args ctx env N _ _ s'
      (written_origin_is_bound target N fallback ctx owner p hnav hlook)
      (memberRun_completes_of_dot target N fallback args ctx env s s' alg? owner p hprobe hsel hprod)) hprod

/-- An inline block that is no transparent reference navigates inertly. -/
theorem navInert_block (block : Algorithm) (ctx : EvalCtx) (h : structureNormal (wireToCaller ctx block) = true) :
    NavInert (.algorithmExpr block) ctx (wireToCaller ctx block) := by
  intro t
  have hhead : (projectNeedStructuralMember (.algorithmExpr block) ctx).runState t =
      (.ok (some (wireToCaller ctx block)), t) := by
    apply KatLang.WhileRoundProduction.production_of_answer_free _ t
    · intro rec; rfl
    · nofun
  unfold projectedStructure
  rw [bind_run, hhead]
  dsimp only
  rw [resolveAliasStructure_normal _ ctx h]
  rfl

/-- A name whose lexical lookup is state-inert and structure-normal navigates inertly. -/
theorem navInert_name (n : Ident) (ctx : EvalCtx) (top : Algorithm) (rest : List Algorithm) (r : ResolvedProperty)
    (hcs : ctx.callStack = top :: rest)
    (hl : ∀ t, (lookupLexicalPropertyRaw top n ctx).runState t = (.ok r, t))
    (h : structureNormal r.alg = true) : NavInert (.resolve n) ctx r.alg := by
  intro t
  have hhead : (projectNeedStructuralMember (.resolve n) ctx).runState t = (.ok (some r.alg), t) := by
    apply KatLang.WhileRoundProduction.production_of_answer_free _ t
    · intro rec
      show (EvalBody.projectNeedStructuralMember rec (.resolve n) ctx).runState t = _
      unfold EvalBody.projectNeedStructuralMember
      rw [hcs]
      dsimp only
      rw [bind_run, hl t]
      rfl
    · nofun
  unfold projectedStructure
  rw [bind_run, hhead]
  dsimp only
  rw [resolveAliasStructure_normal _ ctx h]
  rfl

/-- A name the current scope DECLARES is looked up without reading or changing the state. -/
theorem lookup_local_inert (top : Algorithm) (n : Ident) (ctx : EvalCtx) (prop : PropDef)
    (h : Algorithm.lookupPropDefAny? top n = some prop) (t : EvalState) :
    (lookupLexicalPropertyRaw top n ctx).runState t =
      (.ok { owner := top, binding := prop, alg := childOfInContext top prop.alg ctx }, t) := by
  unfold lookupLexicalPropertyRaw
  rw [h]
  rfl

/-- A name an ENCLOSING scope declares is looked up without reading or changing the state. -/
theorem lookup_parent_inert (top : Algorithm) (n : Ident) (ctx : EvalCtx) (sc : ScopeCtx) (r : ResolvedProperty)
    (h : Algorithm.lookupPropDefAny? top n = none) (hp : Algorithm.parent top = some sc)
    (hr : lookupInParentsStructuralProperty sc n = some r) (t : EvalState) :
    (lookupLexicalPropertyRaw top n ctx).runState t = (.ok r, t) := by
  unfold lookupLexicalPropertyRaw
  rw [h]
  dsimp only
  rw [hp]
  dsimp only
  rw [hr]
  rfl

/-- One declared, accessible, structure-normal member step keeps the navigation inert. -/
theorem navInert_member (o : Expr) (n : Ident) (fb : Expr) (ctx : EvalCtx) (a : Algorithm) (q : PropDef)
    (h : NavInert o ctx a) (hl : Algorithm.lookupPropDefAny? a n = some q)
    (hacc : memberAccessible? ctx a q = true)
    (hn : structureNormal (childOfInContext a q.alg ctx) = true) :
    NavInert (.dotMember o n fb none) ctx (childOfInContext a q.alg ctx) := by
  intro t
  have hstep := member_projection_run o n fb ctx t t a q (h t) hl hacc
  unfold projectedStructure
  rw [bind_run, hstep]
  dsimp only
  rw [resolveAliasStructure_normal _ ctx hn]
  rfl

end KatLang.PlanRouteBridge
