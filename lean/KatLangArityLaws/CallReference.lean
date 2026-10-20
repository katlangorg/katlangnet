import KatLangArityLaws.InvocationPlan
import KatLangArityLaws.BinderTrace

open KatLang KatLang.CallPlan KatLang.BinderTrace

/-!
# CallReference S1: META capture, the reference value and `Invoke()` (October 2026)

S1 makes the M1.5 invocation plan reachable from source:

* a `meta` parameter (`ParameterKind.metaRef`, binder pattern `NeedPattern.metaRef`) binds its name
  to a fresh Ready ADAPTER cell holding the supplied call's reference `Result.callRef a`, where `a`
  is the supplied cell's need address (the plan identity). The binder reaches a META capture in
  written order and invokes the generic core's `reference` capability; production installs
  `NeedPlan.reference` (`reify`, then one `readyNeed`);
* `Result.callRef a` is an ordinary transportable value with no callable identity, members,
  number, Boolean or text view;
* `R.Invoke()` (the dot intrinsic on a structural miss, `evalDotCallCounted`) reads R's VALUE and,
  for `callRef a`, runs `NeedPlan.invoke productionPlanRoute ⟨a⟩` — exactly
  `invokeNeedCall ⟨a⟩`, whose execution laws are `KatLangArityLaws/InvocationPlan.lean`.

Every theorem below is about the authoritative definitions. Proved here:

* capture is INERT: it reads only the supplied cell's suspension; every existing cell — its
  suspension, VALUE state, CALLABLE memo and plan supply — is unchanged; success appends exactly
  one Ready adapter, a refusal changes nothing (`capture_*`);
* the adapter's VALUE is the reference, and its CALLABLE projection is nothing (`adapter_*`);
* reference IDENTITY is the plan address: one cell gives equal references, distinct cells
  unequal ones, through any chain of forwarding hops and after any disciplined computation —
  in particular after the original VALUE completed (`reference_identity`, `forwarded_capture`,
  `capture_after`);
* the binder's META arm is that capability followed by the ordinary name transport; a META
  occurrence never demands or projects its supplied cell (`meta_occurrence_events`), and a head
  WITHOUT a META capture binds identically under every `reference` capability
  (`meta_free_binding_ignores_reference`, production form
  `production_meta_free_binding_ignores_reference`) — the conservative extension of ordinary
  binding;
* the run boundary refuses a value containing a reference and passes every other value
  unchanged (`export_*`).

Explicit invocation reuses the M1.5 laws unchanged: `invoke_run` (fresh `execute` over the plan),
`invoke_and_value_share_cells` (VALUE and every invocation bind THE same prepared cells),
`prepared_survives` (the supply is formed at most once) and `production_invocations_keep_value`
(an invocation never rewrites a completed VALUE, under `ProductionDiscipline`).

NOT claimed (source facts, executable guards in `CallReferenceGuards.lean`): that the `partial`
evaluator's `Invoke` arm, the user-call driver and the dot route call these definitions; the
reachable-state refinement (still open, M1.5 §8) and `ProductionDiscipline` (open until R7; now
the theorem `productionDiscipline_holds`, `EvaluatorDiscipline.lean`); run identity — Lean
has one run per `EvalState` and no channel that brings a value into another run, so foreign-run
and terminal-run rejection are C#-only obligations; C# concurrency, cancellation and resources.
-/

namespace KatLang.CallReferenceLaws

/-! ## The META capability (actual `NeedPlan.reference`) -/

/-- The Ready adapter cell a successful capture of plan `a` allocates. -/
def adapterCell (a : Nat) : NeedCell := { suspension := .ready (.callRef a, 1) }

theorem reference_run (a : Nat) (s : EvalState) :
    (NeedPlan.reference a).runState s =
      match NeedPlan.reifyResult s.needs a with
      | .ok r => (.ok s.needs.size, { s with needs := s.needs.push (adapterCell r.plan) })
      | .error e => (.error e, s) := by
  simp only [NeedPlan.reference, bind_run, reify_run]
  cases NeedPlan.reifyResult s.needs a <;> rfl

/-- **Capture of a supplied call**: the adapter is the next heap cell and holds the reference
    whose plan is the supplied cell itself. -/
theorem capture_on_plan (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs a = some shape) :
    (NeedPlan.reference a).runState s =
      (.ok s.needs.size, { s with needs := s.needs.push (adapterCell a) }) := by
  rw [reference_run]
  simp [NeedPlan.reifyResult, h]

/-- **Refusal**: a cell that is no supplied call (Ready data, a collector, a non-call expression,
    an unsupported callee, an invalid address) is the structured `metaRefusal`, with the state
    unchanged — nothing is evaluated to discover a call. -/
theorem capture_refuses (a : Nat) (s : EvalState) (h : NeedPlan.shapeAt? s.needs a = none) :
    (NeedPlan.reference a).runState s = (.error NeedPlan.metaRefusal, s) := by
  rw [reference_run]
  simp [NeedPlan.reifyResult, h]

/-- **Capture inertia**: every cell that existed before the capture — the supplied cell
    included — is exactly as it was afterwards: no target execution, no argument VALUE demand, no
    supply preparation, no spread, no CALLABLE projection. -/
theorem capture_inert (a : Nat) (s : EvalState) (b : Nat) (hb : b < s.needs.size) :
    ((NeedPlan.reference a).runState s).2.needs[b]? = s.needs[b]? := by
  rw [reference_run]
  cases NeedPlan.reifyResult s.needs a with
  | error e => rfl
  | ok r =>
    simp only [Array.getElem?_push]
    split
    · omega
    · rfl

/-- Capture grows the heap by at most the one adapter and changes no other run state. -/
theorem capture_state (a : Nat) (s : EvalState) :
    let t := ((NeedPlan.reference a).runState s).2
    t.zeroArgPropertyCache = s.zeroArgPropertyCache
      ∧ t.activeZeroArgProperties = s.activeZeroArgProperties
      ∧ t.nextBindingContext = s.nextBindingContext
      ∧ t.lexicalActivations = s.lexicalActivations
      ∧ t.nextRuntimeDeclaration = s.nextRuntimeDeclaration
      ∧ t.needs.size ≤ s.needs.size + 1 := by
  rw [reference_run]
  cases NeedPlan.reifyResult s.needs a <;> simp

/-- Capture keeps the heap discipline of M1.5 (`Disciplined`). -/
theorem disciplined_reference (a : Nat) : Disciplined (NeedPlan.reference a) := by
  intro s b c hc
  have hb : b < s.needs.size := by
    rcases Nat.lt_or_ge b s.needs.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hc
  refine ⟨c, ?_, CellKept.refl c⟩
  rw [capture_inert a s b hb, hc]

/-! ## The adapter: VALUE is the reference, CALLABLE is nothing -/

/-- The adapter's VALUE, through THE completion shell every production demand uses, is the
    reference with one emitted value; nothing else is evaluated. -/
theorem adapter_value (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (b a : Nat) (s : EvalState)
    (h : s.needs[b]? = some (adapterCell a)) :
    ((NeedDemand.step ev route demand b).runState s).1 = .ok (.callRef a, 1) := by
  have := KatLang.NeedControl.Memo.suspended_retains_state ev route demand b s
    { s with needs := s.needs.modify b (fun c => { c with state := .evaluating }) }
    (adapterCell a) (.ok (.callRef a, 1)) h rfl rfl rfl
  rw [this]

/-- References are equal values iff they denote the same need address (the plan identity); the
    language's `==` on them is the derived structural comparison of that address (guards). -/
theorem reference_identity (a b : Nat) : Result.callRef a = Result.callRef b ↔ a = b :=
  ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-- A reference is no number, Boolean, text or structure. -/
theorem reference_is_opaque (a : Nat) :
    (Result.callRef a).asInt? = none ∧ (Result.callRef a).asBool? = none
      ∧ (Result.callRef a).singleAtomicNumber? = none
      ∧ (Result.callRef a).structureItems? = none
      ∧ (Result.callRef a).sequencePatternItems? = none
      ∧ (Result.callRef a).listPatternItems? = none := by
  simp [Result.asInt?, Result.asBool?, Result.singleAtomicNumber?, Result.structureItems?,
    Result.sequencePatternItems?, Result.listPatternItems?]

/-! ## Identity through forwarding and after VALUE -/

/-- **Capture after any disciplined computation** — after the original VALUE completed
    successfully or with an ordinary failure, after explicit invocations, after other captures:
    the capture of the same cell still yields the reference to the SAME plan (M1.5 `meta_after`). -/
theorem capture_after {α : Type} (m : EvalM α) (hm : Disciplined m) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (hs : NeedPlan.shapeAt? s.needs a = some shape) :
    ((NeedPlan.reference a).runState (m.runState s).2).1 = .ok (m.runState s).2.needs.size
      ∧ ((NeedPlan.reference a).runState (m.runState s).2).2.needs
          = (m.runState s).2.needs.push (adapterCell a) := by
  rw [capture_on_plan a _ shape (shapeAt_kept (hm s) a shape hs)]
  exact ⟨rfl, rfl⟩

/-- **Capture through forwarding**: a cell forwarded through any chain of plain parameter hops
    is captured exactly as the original cell — the same plan, never a re-resolution in a
    forwarding scope (M1.5 `forward_chain_identity`). -/
theorem forwarded_capture (hops : List (Ident × EvalCtx × ValEnv)) (a : Nat) (s : EvalState)
    (hbound : ∀ hop ∈ hops, ∃ activation,
      (capturedParameterActivation? hop.1 hop.2.1).runState s = (.ok activation, s) ∧
      lookupAssoc hop.1 (activation.map ParameterActivation.needs |>.getD hop.2.1.needEnv) = some a) :
    (forwardChain hops a >>= NeedPlan.reference).runState s = (NeedPlan.reference a).runState s := by
  simp only [bind_run, forward_chain_identity hops a s hbound]

/-- Two captures of one cell denote ONE plan; the plan record is untouched by both. -/
theorem repeated_capture_same_plan (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs a = some shape) :
    let first := (NeedPlan.reference a).runState s
    let second := (NeedPlan.reference a).runState first.2
    first.2.needs[s.needs.size]? = some (adapterCell a)
      ∧ second.2.needs[s.needs.size + 1]? = some (adapterCell a) := by
  simp only
  rw [capture_on_plan a s shape h]
  have h' : NeedPlan.shapeAt? (s.needs.push (adapterCell a)) a = some shape :=
    shapeAt_kept (HeapKept.push s.needs (adapterCell a)) a shape h
  rw [capture_on_plan a _ shape h']
  simp [Array.getElem_push]

/-! ## The binder's META arm -/

/-- The META arm of the generic core: the `reference` capability, then the ordinary name
    transport of the adapter. -/
theorem bindOne_metaRef_shape {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    (k : NeedCapabilities m) (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv)
    (family : Bool) :
    NeedBinder.bindOne k (.metaRef name) address repeated bound family = (do
      let adapter ← k.reference address
      NeedBinder.bindName k name adapter repeated bound family) := rfl

/-- **A META occurrence demands nothing**: its boundary events are exactly the one reification
    (none if it refused) — never a VALUE or CALLABLE invocation of the supplied cell — for a
    name the head does not repeat (every valid META head, `ParameterPattern.metaViolation?`). -/
theorem meta_occurrence_events (k : NeedCapabilities EvalM) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (hr : repeated.contains name = false) :
    oneEvents k (.metaRef name) address repeated bound family s =
      match runEval (k.reference address) s with
      | (.ok adapter, _) => [.reference address adapter]
      | (.error _, _) => [] := by
  have hr' : name ∉ repeated := by simpa using hr
  rcases h1 : runEval (k.reference address) s with ⟨_ | adapter, s1⟩ <;>
    simp [oneEvents, h1, nameEvents, hr']

/-- The production META occurrence binds the name to the fresh adapter (no repeated name). -/
theorem production_meta_binding (channels : NeedChannels) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (shape : NeedPlan.CallShape) (h : NeedPlan.shapeAt? s.needs address = some shape)
    (hr : repeated.contains name = false) :
    (bindNeedOne channels (.metaRef name) address repeated bound family).runState s =
      (.ok (some (bound.filter (fun entry => entry.fst != name) ++ [(name, s.needs.size)])),
        { s with needs := s.needs.push (adapterCell address) }) := by
  have hr' : name ∉ repeated := by simpa using hr
  simp only [bindNeedOne, NeedChannels.capabilities, NeedBinder.bindOne, bind_run,
    capture_on_plan address s shape h]
  simp [NeedBinder.bindName, hr']

/-! ## Conservative extension: META-free heads ignore the reference capability -/

mutual
  /-- No META capture anywhere in the pattern. -/
  def _root_.KatLang.NeedPattern.metaFree : NeedPattern → Bool
    | .metaRef _ => false
    | .bind _ _ => true
    | .literal _ => true
    | .sequence ps => metaFreeList ps
    | .list ps => metaFreeList ps
    | .unpack ps => metaFreeList ps

  /-- No META capture anywhere in the list. -/
  def metaFreeList : List NeedPattern → Bool
    | [] => true
    | p :: ps => p.metaFree && metaFreeList ps
end

mutual
  theorem one_ignores_reference (k : NeedCapabilities EvalM) (r : Nat → EvalM Nat) (p : NeedPattern)
      (hp : p.metaFree = true) (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
      NeedBinder.bindOne { k with reference := r } p address repeated bound family
        = NeedBinder.bindOne k p address repeated bound family := by
    cases p with
    | bind name collecting => rfl
    | literal literal => rfl
    | metaRef name => simp [NeedPattern.metaFree] at hp
    | sequence ps =>
      simp only [NeedPattern.metaFree] at hp
      simp only [NeedBinder.bindOne]
      simp only [sources_ignore_reference k r ps hp]
    | list ps =>
      simp only [NeedPattern.metaFree] at hp
      simp only [NeedBinder.bindOne]
      simp only [sources_ignore_reference k r ps hp]
    | unpack ps =>
      simp only [NeedPattern.metaFree] at hp
      simp only [NeedBinder.bindOne]
      simp only [sources_ignore_reference k r ps hp]

  theorem sources_ignore_reference (k : NeedCapabilities EvalM) (r : Nat → EvalM Nat)
      (ps : List NeedPattern) (hps : metaFreeList ps = true) :
      ∀ (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool),
      NeedBinder.bindSources { k with reference := r } ps sources repeated bound family
        = NeedBinder.bindSources k ps sources repeated bound family := by
    intro sources repeated bound family
    cases ps with
    | nil => rfl
    | cons p rest =>
      simp only [metaFreeList, Bool.and_eq_true] at hps
      simp only [NeedBinder.bindSources]
      simp only [one_ignores_reference k r p hps.1, sources_ignore_reference k r rest hps.2]
end

mutual
  /-- One parameter pattern without a META capture translates to a META-free binder pattern. -/
  theorem ofParameter_one_metaFree : (p : ParameterPattern) → ParameterPattern.hasNestedMeta p = false →
      (∀ q, p = .capture q → q.kind ≠ .metaRef) → (NeedPattern.ofParameter p).metaFree = true
    | .capture q, _, hk => by
      have hq := hk q rfl
      simp only [NeedPattern.ofParameter]
      split
      · rename_i h
        exact absurd (by simpa using h) hq
      · simp [NeedPattern.metaFree]
    | .sequenceValue ps, h, _ => by
      simp only [ParameterPattern.hasNestedMeta] at h
      simp only [NeedPattern.ofParameter, NeedPattern.metaFree]
      exact ofParameter_metaFree ps h
    | .listValue ps, h, _ => by
      simp only [ParameterPattern.hasNestedMeta] at h
      simp only [NeedPattern.ofParameter, NeedPattern.metaFree]
      exact ofParameter_metaFree ps h
    | .unpacking ps, h, _ => by
      simp only [ParameterPattern.hasNestedMeta] at h
      simp only [NeedPattern.ofParameter, NeedPattern.metaFree]
      exact ofParameter_metaFree ps h

  /-- Every ORDINARY signature without a META capture is META-free after translation. -/
  theorem ofParameter_metaFree : (ps : List ParameterPattern) →
      ParameterPattern.anyHasMetaCapture ps = false → metaFreeList (ps.map NeedPattern.ofParameter) = true
    | [], _ => rfl
    | p :: rest, h => by
      cases p with
      | capture q =>
        simp only [ParameterPattern.anyHasMetaCapture, Bool.or_eq_false_iff] at h
        simp only [List.map_cons, metaFreeList, Bool.and_eq_true]
        refine ⟨ofParameter_one_metaFree (.capture q) rfl (fun r hr => ?_), ofParameter_metaFree rest h.2⟩
        cases hr
        simpa using h.1
      | sequenceValue items =>
        simp only [ParameterPattern.anyHasMetaCapture, Bool.or_eq_false_iff] at h
        simp only [List.map_cons, metaFreeList, Bool.and_eq_true]
        exact ⟨ofParameter_one_metaFree _ h.1 (fun _ hq => by cases hq), ofParameter_metaFree rest h.2⟩
      | listValue items =>
        simp only [ParameterPattern.anyHasMetaCapture, Bool.or_eq_false_iff] at h
        simp only [List.map_cons, metaFreeList, Bool.and_eq_true]
        exact ⟨ofParameter_one_metaFree _ h.1 (fun _ hq => by cases hq), ofParameter_metaFree rest h.2⟩
      | unpacking items =>
        simp only [ParameterPattern.anyHasMetaCapture, Bool.or_eq_false_iff] at h
        simp only [List.map_cons, metaFreeList, Bool.and_eq_true]
        exact ⟨ofParameter_one_metaFree _ h.1 (fun _ hq => by cases hq), ofParameter_metaFree rest h.2⟩
end

/-- **CONSERVATIVE EXTENSION OF BINDING (S1)**: a head with no META capture binds identically
    whatever the `reference` capability is — in particular exactly as the pre-S1 binder, whose
    core had no such capability. -/
theorem meta_free_binding_ignores_reference (k : NeedCapabilities EvalM) (r : Nat → EvalM Nat)
    (ps : List NeedPattern) (hps : metaFreeList ps = true) (cells : List Nat) (family : Bool) :
    NeedBinder.bindPatterns { k with reference := r } ps cells family
      = NeedBinder.bindPatterns k ps cells family := by
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel]
  rw [sources_ignore_reference k r ps hps]

/-- The production form over every ordinary signature without a META capture. -/
theorem production_meta_free_binding_ignores_reference (channels : NeedChannels) (r : Nat → EvalM Nat)
    (ps : List ParameterPattern) (h : ParameterPattern.anyHasMetaCapture ps = false)
    (cells : List Nat) (family : Bool) :
    NeedBinder.bindPatterns { channels.capabilities with reference := r } (ps.map NeedPattern.ofParameter)
        cells family
      = bindNeedPatterns channels (ps.map NeedPattern.ofParameter) cells family :=
  meta_free_binding_ignores_reference channels.capabilities r _ (ofParameter_metaFree ps h) cells family

/-! ## The run boundary -/

theorem export_refuses (value : Result) (s : EvalState) (h : value.containsCallRef = true) :
    (exportRunValue value).runState s = (.error (.typeMismatch callReferenceLeavesRunMessage), s) := by
  simp only [exportRunValue, requireCallRefFree, h, bind_run, ↓reduceIte]
  rfl

theorem export_passes (value : Result) (s : EvalState) (h : value.containsCallRef = false) :
    (exportRunValue value).runState s = (.ok value, s) := by
  simp only [exportRunValue, requireCallRefFree, h, bind_run, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem any_contains_of_mem (a : Nat) (before after : List Result) :
    Result.anyContainsCallRef (before ++ Result.callRef a :: after) = true := by
  induction before with
  | nil => simp [Result.anyContainsCallRef, Result.containsCallRef]
  | cons r rest ih => simp [Result.anyContainsCallRef, ih]

/-- A reference nested anywhere in a list or sequence is contained, so the boundary refuses it. -/
theorem nested_reference_is_contained (a : Nat) (before after : List Result) :
    (Result.listValue (before ++ Result.callRef a :: after)).containsCallRef = true
      ∧ (Result.sequenceValue (before ++ Result.callRef a :: after)).containsCallRef = true := by
  simp [Result.containsCallRef, any_contains_of_mem]

/-- Scalars contain no reference: ordinary results pass the S1 boundary unchanged. -/
theorem reference_free_scalars (n : Int) (t : String) (b : Bool) :
    (Result.atom n).containsCallRef = false ∧ (Result.str t).containsCallRef = false
      ∧ (Result.bool b).containsCallRef = false := by
  simp [Result.containsCallRef]

end KatLang.CallReferenceLaws
