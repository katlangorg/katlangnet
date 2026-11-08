import KatLangArityLaws.FiniteLoopCorrespondence

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction KatLang.FiniteLoop
open Lean.Order

/-!
# Q-66 dot funnel: an extension dot call IS the written call

DOT-CALL PASSES A VALUE: on an extension miss, `R.F(args)` is the written call `F(R, args)`
(`prepareLexicalDotCallArgs`, `EvalBody.callLexicalWithReceiverCounted`). Before this module only the
argument PREPARATION was proved (`dot_receiver_is_ordinary_leading_argument`). Since R7 the whole
route is a total, kernel-visible definition, and this module proves the end-to-end statement over
production Lean, in its QUALIFIED form.

## What is proved

1. **Route** (`dot_route_ok`, `dot_route_error`; every evaluator answer `rec`): the dot-call body
   first runs the receiver probe `resolveDotReceiver?`; a failed or incomplete probe is the body's
   outcome, and after a probe completing at `(.ok alg?, s')` whose `selectDotEdge` is an extension
   miss the body IS `callLexicalWithReceiverCounted` run from `s'`.
2. **Funnel** (`lexical_call_body`, `written_call_body`, `callee_body`; every `rec`): for the two
   elaborated fallbacks `.resolve F` / `.param F`, the lexical call resolves `fallback` with
   `resolveAlg` and dispatches the bundle `target :: args` with origin `.none`; the written call
   `fallback(target :: args)` is the SAME resolution and dispatch, framed once by `CtxMsg.call`
   (`withCtx_bind` merges its two frames), with `resolveCalleeAlg` (which is `resolveAlg` for a
   name, `callee_production`) and origin `.written fallback ctx`. `linkEdge? fallback = none` and
   `openExprName fallback = F` are the definitional facts the proof uses.
3. **Origin independence** (`supplied_origin_independent`, `resolved_origin_independent`;
   production, every fuel by `fuel_origin_independent`): the callee origin is read only for an
   EMPTY supply (CACHE-PUB-1), so `evalSuppliedCallCounted` over a nonempty cell list and
   `evalResolvedCallCounted` over a bundle whose first slot is not a `.sequenceSpread` do not
   depend on it.
4. **The dot funnel** (`dot_funnel`; production): with the probe completing at `(.ok alg?, s')`,
   an extension miss, a non-spread receiver and a name fallback, the dot call run from `s` and the
   written call `evalCounted (.call fallback (target :: args))` run from `s'` are either both
   incomplete, or both complete with the same final state and the same value, or the errors
   `withContext (CtxMsg.dotCall target F) e` and `withContext (CtxMsg.call fallback) e` for one
   inner `e`. `dot_run` / `written_run` state each side against their ONE shared inner run
   (`lexicalRun`).
5. **Loops** (`dot_builtin_funnel`, `dot_repeat_funnel`, `dot_while_funnel`): when the fallback
   resolves to a builtin and every supplied slot is non-spread (`Plain`, including `repeat`'s count),
   the dot spelling reaches that builtin's `applyBuiltinCounted` arm over
   the ordinary supply cells of `target :: args`; for `Step(x).repeat(n)` / `Step(x).while` that is
   `applyBuiltinCounted .repeatBuiltin [a, c]` / `.whileBuiltin [a]`, exactly the shapes of
   `repeat_arm` / `while_arm` and `repeat_completes_iff` / `while_completes_iff` (E-13).

## Why the qualification

The unrestricted `R.F(args) = F(R, args)` is FALSE, so it is not stated:
* a receiver that DECLARES `F` takes the member route (DOT-01, member first): `Box.F(1)` is not
  `F(Box, 1)` (`DotFunnelGuards`, negative control);
* the intrinsics `string` / `Invoke` / `Arguments` / `Algorithm` are their own miss routes
  (`DotMiss.ofName`), not the extension route;
* the probe may change the state, so the two spellings are related from the probe's exit state
  `s'`, not from one entry state; incomplete runs keep their own entry states and are related by
  outcome only (`ProductionCompletes`);
* a spread receiver is outside: the parser lowers `R*.F` to the call `F(R*)`.

Incompletion is read through `ProductionCompletes` (Q-82 stays open). Lean only: nothing here is
about C#.
-/

namespace KatLang.DotFunnel

/-! ## 1. The route (every evaluator answer) -/

/-- **Route.** After a probe completing at `(.ok alg?, s')` with an extension miss, the dot-call
    body is the lexical extension call run from the probe's exit state. -/
theorem dot_route_ok (rec : EvalRec) (target : Expr) (F : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension)) :
    (EvalBody.evalDotCallCounted rec target F fallback args? ctx env).runState s =
      (rec.callLexicalWithReceiverCounted F target fallback args? ctx env).runState s' := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]
  simp only [hmiss]

/-- A probe that fails (or is incomplete) is the dot-call body's outcome. -/
theorem dot_route_error (rec : EvalRec) (target : Expr) (F : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState) (e : Error)
    (hprobe : (rec.resolveDotReceiver? target ctx).runState s = (.error e, t)) :
    (EvalBody.evalDotCallCounted rec target F fallback args? ctx env).runState s = (.error e, t) := by
  unfold EvalBody.evalDotCallCounted
  rw [EvalM.bind_runState, hprobe]

/-! ## 2. The funnel (every evaluator answer) -/

/-- Two `withCtx` frames of one message around a bind are one frame around the bind. -/
theorem withCtx_bind {α β : Type} (c : String) (m : EvalM α) (k : α → EvalM β) :
    (withCtx c m >>= fun a => withCtx c (k a)) = withCtx c (m >>= k) := by
  apply EvalM.ext; intro s
  rw [EvalM.bind_runState, ctx_run, ctx_run, EvalM.bind_runState]
  rcases m.runState s with ⟨_ | a, t⟩
  · rename_i e; cases e <;> rfl
  · exact ctx_run c (k a) t

theorem linkEdge_name (F : Ident) (fallback : Expr) (hfb : fallback = .resolve F ∨ fallback = .param F) :
    linkEdge? fallback = none := by
  rcases hfb with rfl | rfl <;> rfl

theorem openExprName_name (F : Ident) (fallback : Expr) (hfb : fallback = .resolve F ∨ fallback = .param F) :
    openExprName fallback = F := by
  rcases hfb with rfl | rfl <;> simp only [openExprName]

/-- **The lexical extension call** resolves its name fallback with `resolveAlg` and dispatches the
    bundle `target :: args` (the receiver FIRST) with the default origin `.none`. -/
theorem lexical_call_body (rec : EvalRec) (F : Ident) (target fallback : Expr)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.callLexicalWithReceiverCounted rec F target fallback args? ctx env =
      (rec.resolveAlg fallback ctx >>= fun callee =>
        rec.evalResolvedCallCounted callee (target :: args?.getD []) ctx env F .none) := by
  rcases hfb with rfl | rfl <;> rfl

/-- **The written call** of a name callee is the same resolution and dispatch under ONE
    `CtxMsg.call` frame, with `resolveCalleeAlg` and the written origin. -/
theorem written_call_body (rec : EvalRec) (F : Ident) (fallback : Expr)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalCallCountedExpr rec fallback args ctx env =
      withCtx (CtxMsg.call fallback) (rec.resolveCalleeAlg fallback ctx >>= fun callee =>
        rec.evalResolvedCallCounted callee args ctx env F (.written fallback ctx)) := by
  rw [← withCtx_bind]
  rcases hfb with rfl | rfl <;> (unfold EvalBody.evalCallCountedExpr; simp only [linkEdge?, openExprName])

/-- For a name callee, callee resolution is `resolveAlg` (DOT-09: only a dot callee differs). -/
theorem callee_body (rec : EvalRec) (F : Ident) (fallback : Expr)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (ctx : EvalCtx) :
    EvalBody.resolveCalleeAlg rec fallback ctx = rec.resolveAlg fallback ctx := by
  rcases hfb with rfl | rfl <;> rfl

theorem callee_production (F : Ident) (fallback : Expr)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (ctx : EvalCtx) :
    resolveCalleeAlg fallback ctx = resolveAlg fallback ctx :=
  (delegation_equation (.resolveCalleeAlg fallback ctx) (.resolveAlg fallback ctx) pure
    (fun rec => (callee_body rec F fallback hfb ctx).trans (bind_pure_eq _).symm)
    (fun _ _ => nofun)).trans (bind_pure_eq _)

/-! ## 3. Origin independence -/

/-- A supply formed over a plain (non-spread) first slot: one need for that slot, then the rest. -/
theorem form_cons_plain (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv) (e : Expr)
    (rest : OutputBundle) (hsp : ¬ ∃ x, e = .sequenceSpread x) :
    NeedSupply.form spread ctx env (e :: rest) =
      (supplyNeed e ctx env >>= fun a => NeedSupply.form spread ctx env rest >>= fun tail =>
        pure ((a, some e) :: tail)) := by
  apply EvalM.ext; intro s
  cases e
  all_goals first
    | (exfalso; exact hsp ⟨_, rfl⟩)
    | (simp only [NeedSupply.form, NeedSupply.slot, EvalM.bind_runState]
       rcases supplyNeed _ ctx env |>.runState s with ⟨_ | a, t⟩ <;> rfl)

/-- The supplied-call body over a nonempty supply does not read its origin, given that its
    recursive alias arm does not. -/
theorem supplied_body_origin (rec : EvalRec) (o₁ o₂ : CalleeOrigin)
    (hrec : ∀ callee cells ctx env name, cells ≠ [] →
      rec.evalSuppliedCallCounted o₁ callee cells ctx env name = rec.evalSuppliedCallCounted o₂ callee cells ctx env name)
    (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (hne : cells ≠ []) :
    EvalBody.evalSuppliedCallCounted rec o₁ callee cells ctx env name =
      EvalBody.evalSuppliedCallCounted rec o₂ callee cells ctx env name := by
  have he : cells.isEmpty = false := by cases cells with | nil => exact absurd rfl hne | cons _ _ => rfl
  unfold EvalBody.evalSuppliedCallCounted
  split
  · rfl
  · congr 1; funext target; exact hrec _ _ _ _ _ hne
  · simp only [he]
    rfl

/-- The resolved-call body over a bundle with a plain first slot does not read its origin, given
    that its recursive calls do not. -/
theorem resolved_body_origin (rec : EvalRec) (o₁ o₂ : CalleeOrigin)
    (hsup : ∀ callee cells ctx env name, cells ≠ [] →
      rec.evalSuppliedCallCounted o₁ callee cells ctx env name = rec.evalSuppliedCallCounted o₂ callee cells ctx env name)
    (hres : ∀ callee e rest ctx env name, (¬ ∃ x, e = .sequenceSpread x) →
      rec.evalResolvedCallCounted callee (e :: rest) ctx env name o₁ =
        rec.evalResolvedCallCounted callee (e :: rest) ctx env name o₂)
    (callee : Algorithm) (e : Expr) (rest : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (hsp : ¬ ∃ x, e = .sequenceSpread x) :
    EvalBody.evalResolvedCallCounted rec callee (e :: rest) ctx env name o₁ =
      EvalBody.evalResolvedCallCounted rec callee (e :: rest) ctx env name o₂ := by
  unfold EvalBody.evalResolvedCallCounted
  split
  · congr 1; funext target; exact hres _ _ _ _ _ _ hsp
  · rw [form_cons_plain _ _ _ _ _ hsp, EvalM.bind_assoc, EvalM.bind_assoc]
    congr 1; funext a
    rw [EvalM.bind_assoc, EvalM.bind_assoc]
    congr 1; funext tail
    simp only [EvalM.pure_bind]
    exact hsup _ _ _ _ _ (List.cons_ne_nil _ _)

/-- **Origin independence at every fuel**, by induction (the alias arms recurse with the same
    origin). -/
theorem fuel_origin_independent (o₁ o₂ : CalleeOrigin) : ∀ n,
    (∀ callee cells ctx env name, cells ≠ [] →
      evalFuel n (.evalSuppliedCallCounted o₁ callee cells ctx env name) =
        evalFuel n (.evalSuppliedCallCounted o₂ callee cells ctx env name)) ∧
    (∀ callee e rest ctx env name, (¬ ∃ x, e = .sequenceSpread x) →
      evalFuel n (.evalResolvedCallCounted callee (e :: rest) ctx env name o₁) =
        evalFuel n (.evalResolvedCallCounted callee (e :: rest) ctx env name o₂))
  | 0 => ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | Nat.succ n => by
    obtain ⟨ihs, ihr⟩ := fuel_origin_independent o₁ o₂ n
    refine ⟨fun callee cells ctx env name hne => ?_, fun callee e rest ctx env name hsp => ?_⟩
    · rw [evalFuel_succ, evalFuel_succ]
      exact congrArg EvalM.normalizeIncomplete
        (supplied_body_origin (evalFuel n) o₁ o₂ ihs callee cells ctx env name hne)
    · rw [evalFuel_succ, evalFuel_succ]
      exact congrArg EvalM.normalizeIncomplete
        (resolved_body_origin (evalFuel n) o₁ o₂ ihs ihr callee e rest ctx env name hsp)

/-- **Origin independence at production**: a nonempty supply never reads its callee origin. -/
theorem supplied_origin_independent (o₁ o₂ : CalleeOrigin) (callee : Algorithm)
    (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (name : String) (hne : cells ≠ []) :
    evalSuppliedCallCounted o₁ callee cells ctx env name = evalSuppliedCallCounted o₂ callee cells ctx env name := by
  have hf := fun n => (fuel_origin_independent o₁ o₂ n).1 callee cells ctx env name hne
  apply EvalM.ext; intro s
  by_cases hc : ProductionCompletes (evalSuppliedCallCounted o₁ callee cells ctx env name) s
  · obtain ⟨m, hm, hmc⟩ := (production_completes_iff _ s _).1 ⟨rfl, hc⟩
    rw [hf m] at hm hmc
    exact ((production_completes_iff _ s _).2 ⟨m, hm, hmc⟩).1.symm
  · have hc₂ : ¬ ProductionCompletes (evalSuppliedCallCounted o₂ callee cells ctx env name) s := by
      intro hc₂
      obtain ⟨m, hm, hmc⟩ := (production_completes_iff _ s _).1 ⟨rfl, hc₂⟩
      rw [← hf m] at hm hmc
      exact hc ((production_completes_iff _ s _).2 ⟨m, hm, hmc⟩).2
    exact (production_incomplete_state _ s hc).trans (production_incomplete_state _ s hc₂).symm

/-- **Origin independence at production**: a bundle whose first slot is not a spread never reads
    its callee origin. -/
theorem resolved_origin_independent (o₁ o₂ : CalleeOrigin) (callee : Algorithm) (e : Expr)
    (rest : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (name : String) (hsp : ¬ ∃ x, e = .sequenceSpread x) :
    evalResolvedCallCounted callee (e :: rest) ctx env name o₁ =
      evalResolvedCallCounted callee (e :: rest) ctx env name o₂ := by
  have hf := fun n => (fuel_origin_independent o₁ o₂ n).2 callee e rest ctx env name hsp
  apply EvalM.ext; intro s
  by_cases hc : ProductionCompletes (evalResolvedCallCounted callee (e :: rest) ctx env name o₁) s
  · obtain ⟨m, hm, hmc⟩ := (production_completes_iff _ s _).1 ⟨rfl, hc⟩
    rw [hf m] at hm hmc
    exact ((production_completes_iff _ s _).2 ⟨m, hm, hmc⟩).1.symm
  · have hc₂ : ¬ ProductionCompletes (evalResolvedCallCounted callee (e :: rest) ctx env name o₂) s := by
      intro hc₂
      obtain ⟨m, hm, hmc⟩ := (production_completes_iff _ s _).1 ⟨rfl, hc₂⟩
      rw [← hf m] at hm hmc
      exact hc ((production_completes_iff _ s _).2 ⟨m, hm, hmc⟩).2
    exact (production_incomplete_state _ s hc).trans (production_incomplete_state _ s hc₂).symm

/-! ## 4. The dot funnel (production) -/

theorem call_step_iff {c : EvalCall} {B : EvalRec → EvalM c.Ret} (hstep : ∀ rec, evalStep rec c = B rec)
    (s : EvalState) (r : Except Error c.Ret × EvalState) :
    CompletedAt (fun rec => rec c) s r ↔ CompletedAt B s r := by
  have hB : (fun rec => evalStep rec c) = B := funext hstep
  rw [← hB]
  exact (completedAt_call c s r).trans (completedAt_step c s r).symm

theorem completedAt_finite_iff {α : Type} {B : EvalRec → EvalM α} (hB : Finite B) (s : EvalState)
    (r : Except Error α × EvalState) :
    CompletedAt B s r ↔ ((B evalUnbounded).runState s = r ∧ r.1 ≠ .error .fuelExhausted) := by
  constructor
  · intro h; exact ⟨h.production hB.1, h.1⟩
  · rintro ⟨h, hr⟩
    obtain ⟨m, hm⟩ := hB.2 s (by unfold ProductionCompletes; rw [h]; exact hr)
    exact ⟨hr, m, hm.trans h⟩

/-- From a characterization of a call's completed body runs to its production run. -/
theorem production_of_characterization (c : EvalCall) (s : EvalState) (Y : Except Error c.Ret × EvalState)
    (hY : ∀ r, CompletedAt (fun rec => evalStep rec c) s r ↔ (Y = r ∧ Y.1 ≠ .error .fuelExhausted)) :
    (Y.1 ≠ .error .fuelExhausted → (evalUnbounded c).runState s = Y) ∧
      (Y.1 = .error .fuelExhausted → ¬ ProductionCompletes (evalUnbounded c) s) := by
  refine ⟨fun hne => ((completedAt_step c s Y).1 ((hY Y).2 ⟨rfl, hne⟩)).1, fun hfe hc => ?_⟩
  obtain ⟨_, hne⟩ := (hY _).1 ((completedAt_step c s _).2 ⟨rfl, hc⟩)
  exact hne hfe

/-- The completed runs of the dot-call body from `s` are those of the lexical call from `s'`. -/
theorem dot_inner_iff (target : Expr) (F : Ident) (fallback : Expr) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension)) (y : Except Error CountedResult × EvalState) :
    CompletedAt (fun rec => EvalBody.evalDotCallCounted rec target F fallback args? ctx env) s y ↔
      CompletedAt (fun rec => rec.callLexicalWithReceiverCounted F target fallback args? ctx env) s' y := by
  constructor
  · rintro ⟨hy, k, hk⟩
    rcases evalFuel_approx_production k (.resolveDotReceiver? target ctx) s with hi | he
    · exfalso
      unfold EvalM.IsIncompleteAt at hi
      rw [dot_route_error (evalFuel k) target F fallback args? ctx env s _ _ hi] at hk
      rw [← hk] at hy; exact hy rfl
    · have hp : ((evalFuel k).resolveDotReceiver? target ctx).runState s = (.ok alg?, s') := he.trans hprobe
      rw [dot_route_ok (evalFuel k) target F fallback args? ctx env s s' alg? hp hmiss] at hk
      exact ⟨hy, k, hk⟩
  · intro h
    have hpc : CompletedAt (fun rec : EvalRec => rec (.resolveDotReceiver? target ctx)) s (.ok alg?, s') :=
      (completedAt_call _ s _).2 ⟨hprobe, nofun⟩
    obtain ⟨k₁, hk₁⟩ := hpc.eventually (fun _ _ h => h _)
    obtain ⟨k₂, hk₂⟩ := h.eventually (fun _ _ h => h _)
    refine ⟨h.1, max k₁ k₂, ?_⟩
    rw [dot_route_ok (evalFuel (max k₁ k₂)) target F fallback args? ctx env s s' alg?
      (hk₁ _ (Nat.le_max_left _ _)) hmiss]
    exact hk₂ _ (Nat.le_max_right _ _)

/-- THE inner run both spellings share: the lexical extension call over the evaluator answer. -/
abbrev lexicalRun (F : Ident) (target fallback : Expr) (args? : Option OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (rec : EvalRec) : EvalM CountedResult :=
  rec.resolveAlg fallback ctx >>= fun callee =>
    rec.evalResolvedCallCounted callee (target :: args?.getD []) ctx env F .none

/-- The written call's run inside its frame. -/
abbrev writtenRun (F : Ident) (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (rec : EvalRec) : EvalM CountedResult :=
  rec.resolveCalleeAlg fallback ctx >>= fun callee =>
    rec.evalResolvedCallCounted callee args ctx env F (.written fallback ctx)

theorem finite_lexicalRun (F : Ident) (target fallback : Expr) (args? : Option OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) : Finite (lexicalRun F target fallback args? ctx env) :=
  finite_bind (B := fun rec : EvalRec => rec (.resolveAlg fallback ctx)) (finite_call _) (fun _ => finite_call _)

theorem finite_writtenRun (F : Ident) (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) : Finite (writtenRun F fallback args ctx env) :=
  finite_bind (B := fun rec : EvalRec => rec (.resolveCalleeAlg fallback ctx)) (finite_call _) (fun _ => finite_call _)

/-- At production the written call's inner run IS the lexical run: `resolveCalleeAlg` is
    `resolveAlg` for a name, and the origin is not read (non-spread receiver). -/
theorem written_eq_lexical_production (F : Ident) (target fallback : Expr)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (hsp : ¬ ∃ x, target = .sequenceSpread x)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    writtenRun F fallback (target :: args?.getD []) ctx env evalUnbounded =
      lexicalRun F target fallback args? ctx env evalUnbounded := by
  show (resolveCalleeAlg fallback ctx >>= fun callee =>
      evalResolvedCallCounted callee (target :: args?.getD []) ctx env F (.written fallback ctx)) =
    (resolveAlg fallback ctx >>= fun callee =>
      evalResolvedCallCounted callee (target :: args?.getD []) ctx env F .none)
  rw [callee_production F fallback hfb ctx]
  congr 1; funext callee
  exact resolved_origin_independent _ _ callee target _ ctx env F hsp

theorem dot_completed_iff (target : Expr) (F : Ident) (fallback : Expr) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hfb : fallback = .resolve F ∨ fallback = .param F)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension)) (r : Except Error CountedResult × EvalState) :
    CompletedAt (fun rec => evalStep rec (.evalCounted (.dotMember target F fallback args?) ctx env)) s r ↔
      ∃ y, CompletedAt (lexicalRun F target fallback args? ctx env) s' y ∧ ctxOutcome (CtxMsg.dotCall target F) y = r := by
  refine (ctx_transform (CtxMsg.dotCall target F)
    (fun rec => rec.evalDotCallCounted target F fallback args? ctx env) s r).trans ?_
  apply exists_congr; intro y
  apply and_congr_left'
  refine (call_step_iff (c := .evalDotCallCounted target F fallback args? ctx env)
    (B := fun rec => EvalBody.evalDotCallCounted rec target F fallback args? ctx env) (fun _ => rfl) s y).trans ?_
  refine (dot_inner_iff target F fallback args? ctx env s s' alg? hprobe hmiss y).trans ?_
  refine (call_step_iff (c := .callLexicalWithReceiverCounted F target fallback args? ctx env)
    (B := fun rec => EvalBody.callLexicalWithReceiverCounted rec F target fallback args? ctx env)
    (fun _ => rfl) s' y).trans ?_
  rw [show (fun rec => EvalBody.callLexicalWithReceiverCounted rec F target fallback args? ctx env) =
    lexicalRun F target fallback args? ctx env from
      funext fun rec => lexical_call_body rec F target fallback hfb args? ctx env]

theorem written_completed_iff (F : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s' : EvalState)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (r : Except Error CountedResult × EvalState) :
    CompletedAt (fun rec => evalStep rec (.evalCounted (.call fallback args) ctx env)) s' r ↔
      ∃ y, CompletedAt (writtenRun F fallback args ctx env) s' y ∧ ctxOutcome (CtxMsg.call fallback) y = r := by
  have h1 : (fun rec => evalStep rec (.evalCounted (.call fallback args) ctx env)) =
      fun rec => rec (.evalCallCountedExpr fallback args ctx env) := rfl
  rw [h1]
  refine (call_step_iff (c := .evalCallCountedExpr fallback args ctx env)
    (B := fun rec => withCtx (CtxMsg.call fallback) (writtenRun F fallback args ctx env rec))
    (fun rec => written_call_body rec F fallback hfb args ctx env) s' r).trans ?_
  exact ctx_transform _ _ s' r

/-- **The dot side against the shared inner run**: complete exactly when the lexical run from `s'`
    is, and then its outcome under the `CtxMsg.dotCall` frame. -/
theorem dot_run (target : Expr) (F : Ident) (fallback : Expr) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hfb : fallback = .resolve F ∨ fallback = .param F)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension)) :
    (((lexicalRun F target fallback args? ctx env evalUnbounded).runState s').1 ≠ .error .fuelExhausted →
      (evalCounted (.dotMember target F fallback args?) ctx env).runState s =
        ctxOutcome (CtxMsg.dotCall target F) ((lexicalRun F target fallback args? ctx env evalUnbounded).runState s')) ∧
    (((lexicalRun F target fallback args? ctx env evalUnbounded).runState s').1 = .error .fuelExhausted →
      ¬ ProductionCompletes (evalCounted (.dotMember target F fallback args?) ctx env) s) := by
  let x := (lexicalRun F target fallback args? ctx env evalUnbounded).runState s'
  have hX : ∀ y, CompletedAt (lexicalRun F target fallback args? ctx env) s' y ↔
      (x = y ∧ x.1 ≠ .error .fuelExhausted) := by
    intro y
    rw [completedAt_finite_iff (finite_lexicalRun F target fallback args? ctx env)]
    constructor
    · rintro ⟨h, hne⟩; subst h; exact ⟨rfl, hne⟩
    · rintro ⟨h, hne⟩; subst h; exact ⟨rfl, hne⟩
  have hD := production_of_characterization (.evalCounted (.dotMember target F fallback args?) ctx env) s
    (ctxOutcome (CtxMsg.dotCall target F) x) (fun r => by
      rw [dot_completed_iff target F fallback args? ctx env s s' alg? hfb hprobe hmiss r]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨rfl, hne⟩ := (hX y).1 hy
        exact ⟨rfl, (ctxOutcome_fuel _ _).2 hne⟩
      · rintro ⟨rfl, hne⟩
        exact ⟨x, (hX x).2 ⟨rfl, (ctxOutcome_fuel _ _).1 hne⟩, rfl⟩)
  refine ⟨fun hx => hD.1 ((ctxOutcome_fuel _ _).2 hx), fun hx => hD.2 ?_⟩
  have hx' : x.1 = .error .fuelExhausted := hx
  show (ctxOutcome _ x).1 = _
  clear_value x
  rcases x with ⟨o, t⟩
  simp only at hx'
  subst hx'
  rfl

/-- **The written side against the same inner run** (non-spread receiver, name callee): complete
    exactly when the lexical run from `s'` is, and then its outcome under the `CtxMsg.call` frame. -/
theorem written_run (target : Expr) (F : Ident) (fallback : Expr) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s' : EvalState)
    (hfb : fallback = .resolve F ∨ fallback = .param F) (hsp : ¬ ∃ x, target = .sequenceSpread x) :
    (((lexicalRun F target fallback args? ctx env evalUnbounded).runState s').1 ≠ .error .fuelExhausted →
      (evalCounted (.call fallback (target :: args?.getD [])) ctx env).runState s' =
        ctxOutcome (CtxMsg.call fallback) ((lexicalRun F target fallback args? ctx env evalUnbounded).runState s')) ∧
    (((lexicalRun F target fallback args? ctx env evalUnbounded).runState s').1 = .error .fuelExhausted →
      ¬ ProductionCompletes (evalCounted (.call fallback (target :: args?.getD [])) ctx env) s') := by
  let x := (lexicalRun F target fallback args? ctx env evalUnbounded).runState s'
  have hX : ∀ y, CompletedAt (writtenRun F fallback (target :: args?.getD []) ctx env) s' y ↔
      (x = y ∧ x.1 ≠ .error .fuelExhausted) := by
    intro y
    rw [completedAt_finite_iff (finite_writtenRun F fallback _ ctx env),
      written_eq_lexical_production F target fallback hfb hsp args? ctx env]
    constructor
    · rintro ⟨h, hne⟩; subst h; exact ⟨rfl, hne⟩
    · rintro ⟨h, hne⟩; subst h; exact ⟨rfl, hne⟩
  have hC := production_of_characterization (.evalCounted (.call fallback (target :: args?.getD [])) ctx env) s'
    (ctxOutcome (CtxMsg.call fallback) x) (fun r => by
      rw [written_completed_iff F fallback _ ctx env s' hfb r]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨rfl, hne⟩ := (hX y).1 hy
        exact ⟨rfl, (ctxOutcome_fuel _ _).2 hne⟩
      · rintro ⟨rfl, hne⟩
        exact ⟨x, (hX x).2 ⟨rfl, (ctxOutcome_fuel _ _).1 hne⟩, rfl⟩)
  refine ⟨fun hx => hC.1 ((ctxOutcome_fuel _ _).2 hx), fun hx => hC.2 ?_⟩
  have hx' : x.1 = .error .fuelExhausted := hx
  show (ctxOutcome _ x).1 = _
  clear_value x
  rcases x with ⟨o, t⟩
  simp only at hx'
  subst hx'
  rfl

/-- **THE DOT FUNNEL (Q-66).** After a receiver probe completing at `(.ok alg?, s')` with an
    extension miss, for a non-spread receiver and a name fallback, the dot call `target.F(args)`
    run from `s` and the written call `fallback(target, args)` run from `s'` are both incomplete,
    or both complete with the same final state and either the same value or the same inner error
    `e` under their own frames (`CtxMsg.dotCall target F` and `CtxMsg.call fallback`). -/
theorem dot_funnel (target : Expr) (F : Ident) (fallback : Expr) (args? : Option OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (alg? : Option Algorithm)
    (hfb : fallback = .resolve F ∨ fallback = .param F)
    (hsp : ¬ ∃ x, target = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension)) :
    (¬ ProductionCompletes (evalCounted (.dotMember target F fallback args?) ctx env) s ∧
      ¬ ProductionCompletes (evalCounted (.call fallback (target :: args?.getD [])) ctx env) s') ∨
    (((evalCounted (.dotMember target F fallback args?) ctx env).runState s).2 =
        ((evalCounted (.call fallback (target :: args?.getD [])) ctx env).runState s').2 ∧
      ((∃ v, ((evalCounted (.dotMember target F fallback args?) ctx env).runState s).1 = .ok v ∧
          ((evalCounted (.call fallback (target :: args?.getD [])) ctx env).runState s').1 = .ok v) ∨
       (∃ e, e ≠ .fuelExhausted ∧
          ((evalCounted (.dotMember target F fallback args?) ctx env).runState s).1 =
            .error (Error.withContext (CtxMsg.dotCall target F) e) ∧
          ((evalCounted (.call fallback (target :: args?.getD [])) ctx env).runState s').1 =
            .error (Error.withContext (CtxMsg.call fallback) e)))) := by
  have hD := dot_run target F fallback args? ctx env s s' alg? hfb hprobe hmiss
  have hC := written_run target F fallback args? ctx env s' hfb hsp
  by_cases hx : ((lexicalRun F target fallback args? ctx env evalUnbounded).runState s').1 = .error .fuelExhausted
  · exact .inl ⟨hD.2 hx, hC.2 hx⟩
  · right
    rw [hD.1 hx, hC.1 hx]
    rcases hxv : (lexicalRun F target fallback args? ctx env evalUnbounded).runState s' with ⟨_ | v, t⟩
    · rename_i e
      have he : e ≠ .fuelExhausted := by intro h; subst h; rw [hxv] at hx; exact hx rfl
      refine ⟨by cases e <;> first | exact absurd rfl he | rfl, .inr ⟨e, he, ?_, ?_⟩⟩
      · cases e <;> first | exact absurd rfl he | rfl
      · cases e <;> first | exact absurd rfl he | rfl
    · exact ⟨rfl, .inl ⟨v, rfl, rfl⟩⟩

/-! ## 5. Loops: the dot spellings reach the builtin arms (E-13) -/

/-- The supply cells of a bundle of plain (non-spread) slots: one need per slot, in order. -/
def plainCells (ctx : EvalCtx) (env : ValEnv) : OutputBundle → EvalM (List NeedSupply.Sourced)
  | [] => pure []
  | e :: rest => supplyNeed e ctx env >>= fun a => plainCells ctx env rest >>= fun tail => pure ((a, some e) :: tail)

/-- Every slot is plain (not a `.sequenceSpread`). -/
def Plain (slots : OutputBundle) : Prop := ∀ e ∈ slots, ¬ ∃ x, e = .sequenceSpread x

theorem form_plain (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv) :
    ∀ slots, Plain slots → NeedSupply.form spread ctx env slots = plainCells ctx env slots
  | [], _ => rfl
  | e :: rest, h => by
    rw [form_cons_plain spread ctx env e rest (h e (List.mem_cons_self ..)),
      form_plain spread ctx env rest (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

/-- The argument a builtin receives for one sourced supply cell (`evalSuppliedCallCounted`). -/
def sourcedArgument (c : NeedSupply.Sourced) : ResolvedArgumentAlgorithm :=
  { algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some c.1, source? := c.2 }

/-- The builtin arm of the supplied call IS `applyBuiltinCounted` over its sourced arguments
    (through `applyBuiltinCountedResolved`), for every origin. -/
theorem supplied_builtin_production (o : CalleeOrigin) (b : Builtin) (cells : List NeedSupply.Sourced)
    (ctx : EvalCtx) (env : ValEnv) (name : String) :
    evalSuppliedCallCounted o (.builtin b) cells ctx env name =
      applyBuiltinCounted b (cells.map sourcedArgument) ctx env := by
  have h1 : evalSuppliedCallCounted o (.builtin b) cells ctx env name =
      applyBuiltinCountedResolved b (cells.map sourcedArgument) ctx env :=
    (delegation_equation (.evalSuppliedCallCounted o (.builtin b) cells ctx env name)
      (.applyBuiltinCountedResolved b (cells.map sourcedArgument) ctx env) pure
      (fun rec => Eq.trans rfl (bind_pure_eq _).symm) (fun _ _ => nofun)).trans (bind_pure_eq _)
  have h2 : applyBuiltinCountedResolved b (cells.map sourcedArgument) ctx env =
      applyBuiltinCounted b (cells.map sourcedArgument) ctx env :=
    (delegation_equation (.applyBuiltinCountedResolved b (cells.map sourcedArgument) ctx env)
      (.applyBuiltinCounted b (cells.map sourcedArgument) ctx env) pure
      (fun rec => Eq.trans rfl (bind_pure_eq _).symm) (fun _ _ => nofun)).trans (bind_pure_eq _)
  exact h1.trans h2

/-- **A resolved builtin over plain slots** is the ordinary supply and then the builtin's
    `applyBuiltinCounted` arm: both incomplete, or the same run. -/
theorem resolved_builtin_production (b : Builtin) (slots : OutputBundle) (hp : Plain slots)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (o : CalleeOrigin) (s : EvalState) :
    (¬ ProductionCompletes (evalResolvedCallCounted (.builtin b) slots ctx env name o) s ∧
      ¬ ProductionCompletes (plainCells ctx env slots >>= fun cells =>
        applyBuiltinCounted b (cells.map sourcedArgument) ctx env) s) ∨
    ((evalResolvedCallCounted (.builtin b) slots ctx env name o).runState s =
      (plainCells ctx env slots >>= fun cells => applyBuiltinCounted b (cells.map sourcedArgument) ctx env).runState s) := by
  let B : EvalRec → EvalM CountedResult := fun rec =>
    plainCells ctx env slots >>= fun cells => rec (.evalSuppliedCallCounted o (.builtin b) cells ctx env name)
  have hstep : ∀ rec, evalStep rec (.evalResolvedCallCounted (.builtin b) slots ctx env name o) = B rec := by
    intro rec
    show EvalBody.evalResolvedCallCounted rec (.builtin b) slots ctx env name o = B rec
    unfold EvalBody.evalResolvedCallCounted
    simp only
    rw [form_plain _ ctx env slots hp]
    rfl
  have hB : Finite B := finite_bind (finite_const _) (fun _ => finite_call _)
  have hBp : B evalUnbounded = (plainCells ctx env slots >>= fun cells =>
      applyBuiltinCounted b (cells.map sourcedArgument) ctx env) := by
    show (plainCells ctx env slots >>= fun cells => evalSuppliedCallCounted o (.builtin b) cells ctx env name) = _
    congr 1; funext cells; exact supplied_builtin_production o b cells ctx env name
  rw [← hBp]
  by_cases hc : ProductionCompletes (B evalUnbounded) s
  · exact .inr (production_eq_of_finite (.evalResolvedCallCounted (.builtin b) slots ctx env name o) B hstep hB s hc)
  · exact .inl ⟨fun h => hc ((production_completes_iff_body
      (.evalResolvedCallCounted (.builtin b) slots ctx env name o) B hstep hB s).1 h), hc⟩

/-- **A dot spelling whose fallback resolves to a builtin** reaches that builtin's
    `applyBuiltinCounted` arm over the ordinary supply cells of `target :: args`, under the dot
    frame: both incomplete, or the dot call's run is the framed run of the builtin arm. -/
theorem dot_builtin_funnel (b : Builtin) (target : Expr) (F : Ident) (fallback : Expr)
    (args? : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s s' s₁ : EvalState) (alg? : Option Algorithm)
    (hfb : fallback = .resolve F ∨ fallback = .param F)
    (hp : Plain (target :: args?.getD []))
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target F alg? = .ok (.miss .extension))
    (hres : (resolveAlg fallback ctx).runState s' = (.ok (.builtin b), s₁)) :
    (¬ ProductionCompletes (evalCounted (.dotMember target F fallback args?) ctx env) s ∧
      ¬ ProductionCompletes (plainCells ctx env (target :: args?.getD []) >>= fun cells =>
        applyBuiltinCounted b (cells.map sourcedArgument) ctx env) s₁) ∨
    ((evalCounted (.dotMember target F fallback args?) ctx env).runState s =
        ctxOutcome (CtxMsg.dotCall target F) ((plainCells ctx env (target :: args?.getD []) >>= fun cells =>
          applyBuiltinCounted b (cells.map sourcedArgument) ctx env).runState s₁) ∧
      ProductionCompletes (plainCells ctx env (target :: args?.getD []) >>= fun cells =>
        applyBuiltinCounted b (cells.map sourcedArgument) ctx env) s₁) := by
  have hrun := dot_run target F fallback args? ctx env s s' alg? hfb hprobe hmiss
  have hx : (lexicalRun F target fallback args? ctx env evalUnbounded).runState s' =
      (evalResolvedCallCounted (.builtin b) (target :: args?.getD []) ctx env F .none).runState s₁ := by
    show (resolveAlg fallback ctx >>= fun callee =>
      evalResolvedCallCounted callee (target :: args?.getD []) ctx env F .none).runState s' = _
    rw [EvalM.bind_runState, hres]
  rw [hx] at hrun
  rcases resolved_builtin_production b _ hp ctx env F .none s₁ with ⟨hr, hP⟩ | heq
  · exact .inl ⟨hrun.2 (Classical.not_not.mp hr), hP⟩
  · rw [heq] at hrun
    by_cases hc : ProductionCompletes (plainCells ctx env (target :: args?.getD []) >>= fun cells =>
        applyBuiltinCounted b (cells.map sourcedArgument) ctx env) s₁
    · exact .inr ⟨hrun.1 hc, hc⟩
    · exact .inl ⟨hrun.2 (Classical.not_not.mp hc), hc⟩

theorem plainCells_two {β : Type} (ctx : EvalCtx) (env : ValEnv) (t n : Expr) (k : List NeedSupply.Sourced → EvalM β) :
    (plainCells ctx env [t, n] >>= k) =
      (supplyNeed t ctx env >>= fun a => supplyNeed n ctx env >>= fun c => k [(a, some t), (c, some n)]) := by
  apply EvalM.ext; intro s
  simp only [plainCells, EvalM.bind_runState]
  rcases (supplyNeed t ctx env).runState s with ⟨_ | a, u⟩
  · rfl
  · dsimp only
    rcases (supplyNeed n ctx env).runState u with ⟨_ | c, w⟩ <;> rfl

theorem plainCells_one {β : Type} (ctx : EvalCtx) (env : ValEnv) (t : Expr) (k : List NeedSupply.Sourced → EvalM β) :
    (plainCells ctx env [t] >>= k) = (supplyNeed t ctx env >>= fun a => k [(a, some t)]) := by
  apply EvalM.ext; intro s
  simp only [plainCells, EvalM.bind_runState]
  rcases (supplyNeed t ctx env).runState s with ⟨_ | a, u⟩ <;> rfl

/-- The `repeat` dot spelling's builtin run: the supply cells of `[target, n]`, then the `repeat`
    arm over exactly two arguments (the shape of `repeat_arm` / `repeat_completes_iff`). -/
abbrev repeatRun (target n : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  supplyNeed target ctx env >>= fun a => supplyNeed n ctx env >>= fun c =>
    applyBuiltinCounted .repeatBuiltin [sourcedArgument (a, some target), sourcedArgument (c, some n)] ctx env

/-- The `while` dot spelling's builtin run: the supply cell of `[target]`, then the `while` arm over
    exactly one argument (the shape of `while_arm` / `while_completes_iff`). -/
abbrev whileRun (target : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  supplyNeed target ctx env >>= fun a => applyBuiltinCounted .whileBuiltin [sourcedArgument (a, some target)] ctx env

/-- **`Step(x).repeat(n)` IS the `repeat` arm** over the ordinary supply cells of `[Step(x), n]`,
    under the dot frame, once `repeat` resolves to the prelude builtin. -/
theorem dot_repeat_funnel (target n : Expr) (ctx : EvalCtx) (env : ValEnv) (s s' s₁ : EvalState)
    (alg? : Option Algorithm)
    (htsp : ¬ ∃ x, target = .sequenceSpread x) (hnsp : ¬ ∃ x, n = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target "repeat" alg? = .ok (.miss .extension))
    (hres : (resolveAlg (.resolve "repeat") ctx).runState s' = (.ok (.builtin .repeatBuiltin), s₁)) :
    (¬ ProductionCompletes (evalCounted (Expr.dotCall target "repeat" (some [n])) ctx env) s ∧
      ¬ ProductionCompletes (repeatRun target n ctx env) s₁) ∨
    ((evalCounted (Expr.dotCall target "repeat" (some [n])) ctx env).runState s =
        ctxOutcome (CtxMsg.dotCall target "repeat") ((repeatRun target n ctx env).runState s₁) ∧
      ProductionCompletes (repeatRun target n ctx env) s₁) := by
  have hp : Plain [target, n] := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact htsp
    · rcases List.mem_singleton.1 he with rfl; exact hnsp
  have h := dot_builtin_funnel .repeatBuiltin target "repeat" (.resolve "repeat") (some [n]) ctx env s s' s₁ alg?
    (.inl rfl) hp hprobe hmiss hres
  rw [show (plainCells ctx env (target :: (some [n]).getD []) >>= fun cells =>
      applyBuiltinCounted .repeatBuiltin (cells.map sourcedArgument) ctx env) = repeatRun target n ctx env
    from plainCells_two ctx env target n _] at h
  exact h

/-- **`Step(x).while` IS the `while` arm** over the ordinary supply cell of `[Step(x)]`, under the
    dot frame, once `while` resolves to the prelude builtin (`Step(x).while` and `Step(x).while()`). -/
theorem dot_while_funnel (target : Expr) (ctx : EvalCtx) (env : ValEnv) (s s' s₁ : EvalState)
    (alg? : Option Algorithm) (args? : Option OutputBundle) (hargs : args?.getD [] = [])
    (htsp : ¬ ∃ x, target = .sequenceSpread x)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target "while" alg? = .ok (.miss .extension))
    (hres : (resolveAlg (.resolve "while") ctx).runState s' = (.ok (.builtin .whileBuiltin), s₁)) :
    (¬ ProductionCompletes (evalCounted (Expr.dotCall target "while" args?) ctx env) s ∧
      ¬ ProductionCompletes (whileRun target ctx env) s₁) ∨
    ((evalCounted (Expr.dotCall target "while" args?) ctx env).runState s =
        ctxOutcome (CtxMsg.dotCall target "while") ((whileRun target ctx env).runState s₁) ∧
      ProductionCompletes (whileRun target ctx env) s₁) := by
  have hp : Plain (target :: args?.getD []) := by
    rw [hargs]; intro e he
    rcases List.mem_singleton.1 he with rfl; exact htsp
  have h := dot_builtin_funnel .whileBuiltin target "while" (.resolve "while") args? ctx env s s' s₁ alg?
    (.inl rfl) hp hprobe hmiss hres
  rw [hargs, show (plainCells ctx env [target] >>= fun cells =>
      applyBuiltinCounted .whileBuiltin (cells.map sourcedArgument) ctx env) = whileRun target ctx env
    from plainCells_one ctx env target _] at h
  exact h

/-- The `repeat` arm the dot spelling reaches IS the installed stages, at every evaluator answer
    (`repeat_arm`, E-13), over the two sourced arguments `dot_repeat_funnel` names. -/
theorem dot_repeat_arm (rec : EvalRec) (a c : Nat) (target n : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .repeatBuiltin
        [sourcedArgument (a, some target), sourcedArgument (c, some n)] ctx env =
      withNestedMissingOutput (repeatBody rec (sourcedArgument (a, some target))
        (sourcedArgument (c, some n)) ctx env) :=
  repeat_arm rec _ _ ctx env

/-- The `while` arm the dot spelling reaches IS the installed stages (`while_arm`, E-13). -/
theorem dot_while_arm (rec : EvalRec) (a : Nat) (target : Expr) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .whileBuiltin [sourcedArgument (a, some target)] ctx env =
      withNestedMissingOutput (whileBody rec (sourcedArgument (a, some target)) ctx env) :=
  while_arm rec _ ctx env

end KatLang.DotFunnel
