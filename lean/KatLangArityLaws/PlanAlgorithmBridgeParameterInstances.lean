import KatLangArityLaws.PlanAlgorithmBridgeInstances

/-!
# Successful parameter-receiver bridge instances (E-18, review repair)

The parameter's OWN declaring head binds `r`; it need not walk a captured ancestor. This path is
kernel-evaluable even though more general parameter paths use well-founded helpers. No evaluator
definition is changed.

The finite supply harness starts at `EvalState.empty`, supplies `Seven()`, captures it by the
production `NeedPlan.reference` (`captured`), and installs its Ready adapter as `r` in an explicit
own-parameter context. It supplies the reconstructed invocation and proves its first route classification
(`flight_dot`, `flight_grouped`), including the first CALLABLE memo write. `Inv` follows from the
allocation laws and the production probe's invariant. The receiver demand completes the adapter
once; `repeated_read` reads its memo without another write.

`bridge_dot` and `bridge_grouped` APPLY the final parameter bridge theorems with every premise
proved, including the singleton-domain insertion and preservation obligations. Both production
entries return 7; both conclusions include final `HeapInsertion.Inserted`, hence `Frame`.
`shifted_callee` proves the later captured-callee allocation moves past the one inserted cell.

This is a concrete supply/parameter-context instance, not a source-program reachability theorem
or a proof of the full `R.Algorithm(0)` control. Those — with alias receivers, a captured-ancestor
parameter in the context a source binder built, effectful memo sharing and an address-bearing
whole-bridge result — are `PlanAlgorithmBridgeSourceInstances` and its companion modules.
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.HeapInsertion
open KatLang.PlanAlgorithmBridge KatLang.PlanAlgorithmBridgeInstances
open KatLang.AddressInvariant (Inv inv_push empty_inv)
namespace KatLang.PlanAlgorithmBridgeInstances.Parameter
set_option maxRecDepth 100000
def seven0 : Expr := .call (.resolve "Seven") []
def s₀ : EvalState := ((supplyNeed seven0 ctx []).runState EvalState.empty).2
def s₁ : EvalState := ((readyNeed (.callRef 0, 1)).runState s₀).2
/-- The Ready reference came from production capture of the supplied call. -/
theorem captured : (NeedPlan.reference 0).runState s₀ = (.ok 1, s₁) := by kernel_rfl
def caller : EvalCtx := { ctx with callStack := alg ["r"] [] [] [.param "r"] :: ctx.callStack, needEnv := [("r", 1)] }
def receiver : Expr := .param "r"
def edge : Expr := .dotMember receiver "Algorithm" fb none
def source (grouped : Bool) : Expr :=
  if grouped then .call edge [] else .dotMember receiver "Algorithm" fb (some [])
def supplied (grouped : Bool) : EvalState := ((supplyNeed (source grouped) caller []).runState s₁).2
def entry (grouped : Bool) : EvalState := withState 2 .evaluating (supplied grouped)
def probed (grouped : Bool) : EvalState := ((evalFuel 40 (.resolveDotReceiver? receiver caller)).runState (entry grouped)).2
def x (grouped : Bool) : EvalState := withRoute 2 .algorithm (probed grouped)
def x₄ (grouped : Bool) : EvalState := ((evalFuel 40 (.eval receiver caller [])).runState (x grouped)).2
def ca (grouped : Bool) : NeedCell :=
  { suspension := .expression (source grouped) caller [], state := .evaluating, route := some .algorithm }
def ι (grouped : Bool) : Insertion := paramInsertion (x grouped).needs.size 2 edge caller [] 1
def x₅ (grouped : Bool) : EvalState :=
  ((evalFuel 50 (.algorithmOfValue (.callRef 0) (some []) caller [])).runState (x₄ grouped)).2
theorem x_cell (g : Bool) : (x g).needs[2]? = some (ca g) := by cases g <;> kernel_rfl
theorem entry_cell (g : Bool) : (entry g).needs[2]? =
    some { suspension := .expression (source g) caller [], state := .evaluating } := by cases g <;> kernel_rfl
theorem probe_entry (g : Bool) : (resolveDotReceiver? receiver caller).runState (entry g) = (.ok none, probed g) :=
  prod_of_fuel 40 (.resolveDotReceiver? receiver caller) (entry g) _ (by cases g <;> kernel_rfl) (ok_complete _)
theorem miss : selectDotEdge caller receiver "Algorithm" none = .ok (.miss .algorithm) := by kernel_rfl
theorem flight_dot :
    (withCtx (dotShape receiver fb [] caller []).ctxMsg
      (NeedPlan.routeOf productionPlanRoute.classify 2 (dotShape receiver fb [] caller []))).runState (entry false) =
      (.ok .algorithm, x false) :=
  PlanAlgorithmBridgeInstances.flight_dot 2 receiver fb [] caller [] (entry false) (probed false)
    _ none (entry_cell false) rfl (probe_entry false) miss (by kernel_rfl)
theorem decided_entry :
    (algorithmIntrinsicRoute receiver caller).runState (entry true) = (.ok true, probed true) :=
  prod_of_fuel 40 (.algorithmIntrinsicRoute receiver caller) (entry true) _ (by kernel_rfl) (ok_complete _)
theorem flight_grouped :
    (withCtx (groupedShape receiver fb [] caller []).ctxMsg
      (NeedPlan.routeOf productionPlanRoute.classify 2 (groupedShape receiver fb [] caller []))).runState (entry true) =
      (.ok .algorithm, x true) :=
  PlanAlgorithmBridgeInstances.flight_grouped 2 receiver fb [] caller [] (entry true) (probed true)
    _ (entry_cell true) rfl decided_entry (by kernel_rfl)
theorem s₀_eq : s₀ =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression seven0 ctx [] } } := by kernel_rfl
theorem s₁_eq : s₁ = { s₀ with needs := s₀.needs.push { suspension := .ready (.callRef 0, 1) } } := by kernel_rfl
theorem supplied_eq (g : Bool) : supplied g =
    { s₁ with needs := s₁.needs.push { suspension := .expression (source g) caller [] } } := by cases g <;> kernel_rfl
theorem caller_valid_s₁ : KatLang.HeapAddressValidity.ValidCtx s₁.needs caller := by
  intro p hp
  have h : p = ("r", 1) := List.mem_singleton.mp hp
  subst h
  decide +kernel
theorem inv_entry (g : Bool) : Inv (entry g) := by
  have h0 := inv_push empty_inv (.expression seven0 ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← s₀_eq] at h0
  have hr : KatLang.AddressInvariant.CRV s₀.needs (.callRef 0, 1) := by
    intro a hm
    cases hm
    decide +kernel
  have h1 := inv_push h0 (.ready (.callRef 0, 1)) hr
  rw [← s₁_eq] at h1
  have h2 := inv_push h1 (.expression (source g) caller []) ⟨caller_valid_s₁, fun _ m => by cases m⟩
  rw [← supplied_eq g] at h2
  exact KatLang.AddressInvariant.inv_modify h2 2 _ (fun cell hc =>
    ⟨rfl, ⟨(h2.cells 2 cell hc).susp, trivial, (h2.cells 2 cell hc).plan,
      (h2.cells 2 cell hc).callee, (h2.cells 2 cell hc).receiver⟩⟩)
theorem caller_valid_entry (g : Bool) : KatLang.HeapAddressValidity.ValidCtx (entry g).needs caller := by
  intro p hp
  have h : p = ("r", 1) := List.mem_singleton.mp hp
  subst h
  cases g <;> decide +kernel
theorem inv_x (g : Bool) : Inv (x g) := by
  have h := (KatLang.AddressInvariant.production_sound_all (.resolveDotReceiver? receiver caller)
    (entry g) (inv_entry g) (caller_valid_entry g)).1
  rw [show (evalUnbounded (.resolveDotReceiver? receiver caller)).runState (entry g) =
      (.ok none, probed g) from probe_entry g] at h
  have hf := inv_flight h 2
  have heq : withState 2 .evaluating (probed g) = probed g := by cases g <;> kernel_rfl
  rw [heq] at hf
  exact hf
theorem probe_x (g : Bool) : (resolveDotReceiver? receiver caller).runState (x g) = (.ok none, x g) :=
  prod_of_fuel 40 (.resolveDotReceiver? receiver caller) (x g) _ (by cases g <;> kernel_rfl) (ok_complete _)
theorem value_x (g : Bool) : (eval receiver caller []).runState (x g) = (.ok (.callRef 0), x₄ g) :=
  prod_of_fuel 40 (.eval receiver caller []) (x g) _ (by cases g <;> kernel_rfl) (ok_complete _)
theorem read_x (g : Bool) : (invocationReceiverValue receiver caller []).runState (x g) = (.ok (.callRef 0), x₄ g) :=
  irv_value receiver caller [] (x g) (x g) (x₄ g) (.ok (.callRef 0)) (probe_x g) (value_x g)
theorem probe_plan (g : Bool) :
    (resolveDotReceiver? receiver caller).runState (embed (ι g) (x g)) = (.ok none, embed (ι g) (x g)) :=
  prod_of_fuel 40 (.resolveDotReceiver? receiver caller) (embed (ι g) (x g)) _ (by cases g <;> kernel_rfl) (ok_complete _)
theorem value_plan (g : Bool) : (eval receiver caller []).runState (embed (ι g) (x g)) =
    (.ok (.callRef 0), embed (ι g) (x₄ g)) :=
  prod_of_fuel 40 (.eval receiver caller []) (embed (ι g) (x g)) _ (by cases g <;> kernel_rfl) (ok_complete _)
theorem read_plan (g : Bool) : (invocationReceiverValue receiver caller []).runState (embed (ι g) (x g)) =
    (.ok (.callRef 0), embed (ι g) (x₄ g)) :=
  irv_value receiver caller [] _ _ _ (.ok (.callRef 0)) (probe_plan g) (value_plan g)
theorem tail (g : Bool) : (algorithmOfValue (.callRef 0) (some []) caller []).runState (x₄ g) =
    (.ok (.atom 7, 1), x₅ g) :=
  prod_of_fuel 50 (.algorithmOfValue (.callRef 0) (some []) caller []) (x₄ g) _
    (by cases g <;> kernel_rfl) (ok_complete _)
theorem tail_plan (g : Bool) : (algorithmOfValue (.callRef 0) (some []) caller []).runState (embed (ι g) (x₄ g)) =
    (.ok (.atom 7, 1), embed (ι g) (x₅ g)) :=
  prod_of_fuel 50 (.algorithmOfValue (.callRef 0) (some []) caller []) (embed (ι g) (x₄ g)) _
    (by cases g <;> kernel_rfl) (ok_complete _)
theorem repeated_read (g : Bool) :
    (invocationReceiverValue receiver caller []).runState (x₄ g) = (.ok (.callRef 0), x₄ g) := by
  apply irv_value receiver caller [] (x₄ g) (x₄ g) (x₄ g) (.ok (.callRef 0))
  · exact prod_of_fuel 40 (.resolveDotReceiver? receiver caller) (x₄ g) _
      (by cases g <;> kernel_rfl) (ok_complete _)
  · exact prod_of_fuel 40 (.eval receiver caller []) (x₄ g) _
      (by cases g <;> kernel_rfl) (ok_complete _)
theorem shifted_callee (g : Bool) :
    ((x₅ g).needs[0]?).bind NeedCell.callee = some (x g).needs.size ∧
    ((embed (ι g) (x₅ g)).needs[0]?).bind NeedCell.callee = some ((x g).needs.size + 1) := by
  cases g <;> constructor <;> decide +kernel
theorem production_value :
    (evalCounted (source false) caller []).runState (x false) = (.ok (.atom 7, 1), x₅ false) :=
  prod_of_fuel 60 (.evalCounted (source false) caller []) (x false) _ (by kernel_rfl) (ok_complete _)
theorem production_completeB : completeB ((evalFuel 60 (.evalCounted (source false) caller [])).runState (x false)).1 =
    true := by decide +kernel
theorem production_completes : ProductionCompletes (evalCounted (source false) caller []) (x false) := by
  have h := prod_of_fuel 60 (.evalCounted (source false) caller []) (x false) _ rfl
    (complete_of_B production_completeB)
  unfold ProductionCompletes
  rw [show (evalCounted (source false) caller []).runState (x false) = _ from h]
  exact complete_of_B production_completeB
theorem bridge_dot :
    Bridged (ι false)
      ((ordinaryCall productionPlanRoute 2 (dotShape receiver fb [] caller []) .algorithm).runState (x false))
      ((reCountValueBoundary <$> evalCounted (source false) caller []).runState (x false)) := by
  apply algorithm_bridge_dot_param_at 2 "r" fb [] caller [] (x false) (x false) none (ca false) 1
    (x_cell false) rfl rfl rfl (probe_x false) miss (by kernel_rfl) (by decide +kernel)
    (inv_x false) (.ok (.callRef 0)) (x₄ false) (read_x false)
  · exact read_plan false
  · decide +kernel
  · intro v hv
    cases hv
    exact ⟨planCallees_of_B (by decide +kernel),
      ⟨{ suspension := .ready (.callRef 0, 1), state := .completed (.ok (.callRef 0, 1)),
          callable := .projected (.ok none) }, 1, by kernel_rfl, rfl⟩,
      .ok (.atom 7, 1), x₅ false, tail false, tail_plan false, by decide +kernel⟩
  · exact production_completes
theorem settled : (withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute receiver caller)).runState (x true) =
    (.ok true, x true) := by
  rw [KatLang.FiniteLoop.ctx_run, show (algorithmIntrinsicRoute receiver caller).runState (x true) =
      (.ok true, x true) from prod_of_fuel 40 (.algorithmIntrinsicRoute receiver caller) (x true) _
        (by kernel_rfl) (ok_complete _)]
  rfl
theorem productionG_completeB : completeB ((evalFuel 60 (.evalCallCountedExpr edge [] caller [])).runState (x true)).1 =
    true := by decide +kernel
theorem productionG_value :
    (evalCallCountedExpr edge [] caller []).runState (x true) = (.ok (.atom 7, 1), x₅ true) :=
  prod_of_fuel 60 (.evalCallCountedExpr edge [] caller []) (x true) _ (by kernel_rfl) (ok_complete _)
theorem productionG_completes : ProductionCompletes (evalCallCountedExpr edge [] caller []) (x true) := by
  have h := prod_of_fuel 60 (.evalCallCountedExpr edge [] caller []) (x true) _ rfl
    (complete_of_B productionG_completeB)
  unfold ProductionCompletes
  rw [show (evalCallCountedExpr edge [] caller []).runState (x true) = _ from h]
  exact complete_of_B productionG_completeB
theorem bridge_grouped :
    Bridged (ι true)
      ((ordinaryCall productionPlanRoute 2 (groupedShape receiver fb [] caller []) .algorithm).runState (x true))
      ((reCountValueBoundary <$> evalCallCountedExpr edge [] caller []).runState (x true)) := by
  apply algorithm_bridge_grouped_param_at 2 "r" fb [] caller [] (x true) (ca true) 1 settled
    (x_cell true) rfl rfl rfl (by kernel_rfl) (by decide +kernel)
    (inv_x true) (.ok (.callRef 0)) (x₄ true) (read_x true)
  · exact read_plan true
  · decide +kernel
  · intro v hv
    cases hv
    exact ⟨planCallees_of_B (by decide +kernel),
      ⟨{ suspension := .ready (.callRef 0, 1), state := .completed (.ok (.callRef 0, 1)),
          callable := .projected (.ok none) }, 1, by kernel_rfl, rfl⟩,
      .ok (.atom 7, 1), x₅ true, tail true, tail_plan true, by decide +kernel⟩
  · exact productionG_completes
end KatLang.PlanAlgorithmBridgeInstances.Parameter

