import Lean
import KatLangArityLaws.EvaluatorCacheLaws
import KatLangArityLaws.FamilyDispatch
import KatLangArityLaws.PropertyOwnerContext
import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.EvaluatorCore KatLang.EvaluatorCacheLaws KatLang.WhileRoundProduction
open KatLang.PropertyOwnerContext KatLang.WhileRoundLaws KatLang.BinderTrace

/-!
# FG-K2: a retained declaring-owner context is stable across evaluation

A LOCAL-only property's cache key carries the binding context `propertyOwnerBindingContext` finds on
the property's declaring chain. `WhileRoundProduction.local_publication_reused` took "that context
is still `n` at the later read" as its premise `hstable`. This module derives it, for one fixed
resolved binding and its fixed chain, from the operations between publication and read.

* **Whole-evaluator preservation** (`ActivationPrefix`, `activations_kept_core`, `activations_kept`):
  the array only grows, keeping every earlier record whole at its index. The one writer is
  `recordParameterActivation`, reached by `enterAlgorithmBody` (hence `enterPropertyOwnerBody`) and
  `wireSelectedBranchBody`; no body restores a snapshot. The proof is per body, for all `EvalCall`
  constructors: `EvalBody.*_pres` of `EvaluatorCacheLaws` are generic over a `WriteFrame`, which
  `ActivationPrefix` is and `FieldFrame` is not, and `activation_property_step` handles the property
  access. `activations_kept` covers every production outcome: a run with no completing fuel returns
  its entry state. `activations_kept_core` needs `Completes`: an incomplete core run forgets its
  state (`normalizeIncomplete`). Neither says anything of termination.
* **The owner condition** (`OwnerSearchValid`, `owner_context_stable`, `RetainedAt`): lookup skips a
  level whose record is missing, so an append CAN change the answer on an arbitrary chain
  (`dangling_reference_breaks_stability`, a synthetic state, not a reachable-program claim). The
  chain must have no dangling level where the search stops. `AddressInvariant` does not give this:
  it excludes `ScopeCtx.activation` indices.
* **Production establishes it** (§3): a recording body entry's head scope, an inherited (read-owned)
  entry's site and a selected family level are retained in the exit state with the context their
  record stores. A record's INDEX is not its binding context, and a fresh record may store an
  existing context; only the stored context matters here.
* **Local reuse** (`local_publication_reused_after_production`, §4): the production theorem. Rows:
  `transitions_read_discovery_entry`, `entered_body_shares_local_entry`,
  `round_exit_reads_discovery_entry`, `false_continuation_keeps_local_entry`,
  `dispatched_body_shares_local_entry`. Lexical against structural spellings:
  `structural_read_reuses_lexical_entry`. The host fallback keeps its input conditions:
  `fallback_publication_reused_after_production`.

The premises that remain are initial facts about a chain (`RetainedAt` at the earlier state),
discharged by §3 for entered and dispatched bodies; `RetainedAt` mentions no later state.

NOT claimed: that `scopeInContext` selected the semantically intended declaration
(`activeDeclaration?` is `partial`, hence `childOfInContext_chain`'s selection premise), so which
chain a given production read resolves stays a source fact pinned by guards; that every expression's
property reads route through `evalZeroArgPropertyAccessCounted`; `WiresDirectly` for a module or
builtin, which rebuild a different chain or have none; reuse across a fresh owner activation or a
rebuilt unrelated chain (their keys differ); explicit invocations, which never read an entry; that a
miss publishes under the key a later read uses (the cache entry is a premise); key injectivity,
reentrancy (FG-K1), `FuelReached` for the binder channels; anything about C#.
-/

namespace KatLang.OwnerContextStability

/-! ## 1. The activation array only grows -/

/-- The activation array of `s` is an unchanged prefix of the one of `t`: every earlier record is
    kept whole, at its index. -/
def ActivationPrefix (s t : EvalState) : Prop :=
  ∃ suffix, t.lexicalActivations.toList = s.lexicalActivations.toList ++ suffix

theorem ActivationPrefix.refl (s : EvalState) : ActivationPrefix s s := ⟨[], by simp⟩

theorem ActivationPrefix.trans {s t u : EvalState} (h₁ : ActivationPrefix s t)
    (h₂ : ActivationPrefix t u) : ActivationPrefix s u := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

theorem ActivationPrefix.of_eq {s t : EvalState} (h : t.lexicalActivations = s.lexicalActivations) :
    ActivationPrefix s t := ⟨[], by simp [h]⟩

/-- A write whose activation array is one append extends, whatever else it changes. -/
theorem ActivationPrefix.of_push {s t : EvalState} {a : ParameterActivation}
    (h : t.lexicalActivations = s.lexicalActivations.push a) : ActivationPrefix s t :=
  ⟨[a], by simp [h]⟩

theorem ActivationPrefix.push (s : EvalState) (a : ParameterActivation) :
    ActivationPrefix s { s with lexicalActivations := s.lexicalActivations.push a } :=
  ActivationPrefix.of_push rfl

theorem ActivationPrefix.size_le {s t : EvalState} (h : ActivationPrefix s t) :
    s.lexicalActivations.size ≤ t.lexicalActivations.size := by
  obtain ⟨a, ha⟩ := h
  have := congrArg List.length ha
  simp only [Array.length_toList, List.length_append] at this
  omega

/-- Every record the earlier array holds is the record the later array holds at that index. -/
theorem ActivationPrefix.lookup {s t : EvalState} (h : ActivationPrefix s t) {id : Nat}
    (hid : id < s.lexicalActivations.size) :
    t.lexicalActivations[id]? = s.lexicalActivations[id]? := by
  obtain ⟨a, ha⟩ := h
  rw [← Array.getElem?_toList, ← Array.getElem?_toList, ha]
  exact List.getElem?_append_left (by simpa using hid)

instance : StateRel ActivationPrefix := ⟨ActivationPrefix.refl, ActivationPrefix.trans⟩
instance : WriteFrame ActivationPrefix := ⟨fun _ _ _ _ h => ActivationPrefix.of_eq h, ActivationPrefix.push⟩

/-- The property access writes only the cache and the owner set: its own writes keep the array,
    its calculation extends it. -/
theorem activation_property_step (rec : EvalRec) (hrec : ∀ c, Preserves ActivationPrefix (rec c))
    (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Preserves ActivationPrefix
      (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc := EvalBody.zeroArgPropertyCalculation_pres (R := ActivationPrefix) rec hrec request resolvedAlgorithm ctx env
  intro s
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · simp only [EvalM.bind_runState, get_runState]
    split
    · cases request with
      | read => exact ActivationPrefix.refl s
      | invoke _ => exact hcalc s
    · split
      · exact hcalc s
      · simp only [EvalM.bind_runState, set_runState]
        obtain ⟨o, t2, hm, hc⟩ := evalAttempt_cases (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)
          { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        have hk := hcalc { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        rw [hm] at hk
        have hstart : ActivationPrefix s
            { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties } :=
          ActivationPrefix.of_eq rfl
        have hk' := hstart.trans hk
        rcases hc with ⟨hrun, _⟩ | ⟨hrun, _⟩
        · rw [hrun]; exact hk'
        · rw [hrun]
          simp only [get_runState]
          cases o with
          | ok counted =>
            simp only [EvalM.bind_runState, set_runState, pure_runState]
            exact hk'.trans (ActivationPrefix.of_eq rfl)
          | error err =>
            simp only [EvalM.bind_runState, set_runState, throw_runState]
            exact hk'.trans (ActivationPrefix.of_eq rfl)
  · exact hcalc s

/-- **Whole run (core):** every completed run of the total core, at every fuel, from every state —
    success and ordinary failure alike — keeps the activation array as a prefix. An INCOMPLETE core
    run is excluded: `normalizeIncomplete` forgets its state (`{}`), so nothing holds of it. -/
theorem activations_kept_core (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) : ActivationPrefix s ((evalFuel n c).runState s).2 :=
  invariant_transfer ActivationPrefix ActivationPrefix.refl
    (fun rec hrec => evalStep_preserves activation_property_step rec hrec) n c s hc

/-- **Whole run (production):** every production operation, from every state, whatever its outcome.
    A run with no completing fuel returns the entry state itself (`production_preserves`), so the
    statement carries no completion premise and says nothing of termination. -/
theorem activations_kept (c : EvalCall) : Preserves ActivationPrefix (evalUnbounded c) :=
  production_preserves ActivationPrefix ActivationPrefix.refl
    (fun rec hrec => evalStep_preserves activation_property_step rec hrec) c

/-! ## 2. Which chains keep their owner -/

/-- The owner search of `propertyOwnerBindingContext` over a chain stays inside the array: the
    nearest ACTIVATED level names an existing record. That is exactly the searched prefix: the
    search stops at that record, unactivated levels below it are skipped, and a chain with no
    activated level is valid vacuously. It rules out a DANGLING level, the one thing a later append
    can turn from "skipped" into "selected" (`dangling_reference_breaks_stability`). -/
def OwnerSearchValid : Option ScopeCtx → EvalState → Prop
  | none, _ => True
  | some (.mk parent _ _ _ _ _ activation _), s =>
      match activation with
      | some id => id < s.lexicalActivations.size
      | none => OwnerSearchValid parent s

theorem OwnerSearchValid.mono {s t : EvalState} (h : ActivationPrefix s t) :
    ∀ {chain : Option ScopeCtx}, OwnerSearchValid chain s → OwnerSearchValid chain t
  | none, _ => by simp only [OwnerSearchValid]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      cases activation with
      | some id =>
        simp only [OwnerSearchValid] at hv ⊢
        exact Nat.lt_of_lt_of_le hv h.size_le
      | none =>
        simp only [OwnerSearchValid] at hv ⊢
        exact OwnerSearchValid.mono h (chain := parent) hv

/-- **Owner lookup is stable on a valid chain**: an activation-prefix extension leaves the answer
    unchanged, whether that answer is an owner context or `none`. -/
theorem owner_context_stable {s t : EvalState} (h : ActivationPrefix s t) :
    ∀ {chain : Option ScopeCtx}, OwnerSearchValid chain s →
      propertyOwnerBindingContext chain t = propertyOwnerBindingContext chain s
  | none, _ => by simp only [propertyOwnerBindingContext]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      cases activation with
      | some id =>
        simp only [OwnerSearchValid] at hv
        obtain ⟨r, hr⟩ : ∃ r, s.lexicalActivations[id]? = some r := ⟨_, Array.getElem?_eq_getElem hv⟩
        simp only [propertyOwnerBindingContext, Option.bind_some, h.lookup hv, hr]
      | none =>
        simp only [OwnerSearchValid] at hv
        simp only [propertyOwnerBindingContext, Option.bind_none]
        exact owner_context_stable h (chain := parent) hv

/-- A nearer level at index `1`, its ancestor at index `0`. -/
def danglingChain : Option ScopeCtx :=
  some (.mk (some (.mk none [] [] [] [] [] (some 0) none)) [] [] [] [] [] (some 1) none)

/-- Only index `0` exists: the search skips the nearer level and answers the ancestor's `10`. -/
def danglingBefore : EvalState := { lexicalActivations := #[{ values := [], bindingContext := 10 }] }

/-- The same record, and one appended at index `1` with another context. -/
def danglingAfter : EvalState :=
  { lexicalActivations := #[{ values := [], bindingContext := 10 }, { values := [], bindingContext := 20 }] }

/-- **NEGATIVE CONTROL.** Append-only records alone do NOT make owner lookup stable: a dangling
    nearer level is skipped until a record lands at its index. Synthetic: it bounds the theorem and
    shows no reachable language bug. `OwnerSearchValid` excludes exactly this shape. -/
theorem dangling_reference_breaks_stability :
    ActivationPrefix danglingBefore danglingAfter ∧
    propertyOwnerBindingContext danglingChain danglingBefore = some 10 ∧
    propertyOwnerBindingContext danglingChain danglingAfter = some 20 ∧
    ¬ OwnerSearchValid danglingChain danglingBefore := by
  refine ⟨⟨[{ values := [], bindingContext := 20 }], rfl⟩, ?_, ?_, ?_⟩
  · simp [danglingChain, danglingBefore, propertyOwnerBindingContext]
  · simp [danglingChain, danglingAfter, propertyOwnerBindingContext]
  · simp [danglingChain, danglingBefore, OwnerSearchValid]

/-- So the unqualified statement is false. -/
theorem unqualified_stability_is_false :
    ¬ ∀ (chain : Option ScopeCtx) (s t : EvalState), ActivationPrefix s t →
      propertyOwnerBindingContext chain t = propertyOwnerBindingContext chain s := by
  intro h
  obtain ⟨hp, hb, ha, _⟩ := dangling_reference_breaks_stability
  have := h danglingChain danglingBefore danglingAfter hp
  rw [hb, ha] at this
  exact absurd this (by decide)

/-- `chain` keeps owner context `n` from `s` on: its search is valid and answers `n`. An initial
    `RetainedAt` is the only fact a later read needs about the chain; it mentions no later state
    (`RetainedAt.mono` derives that). -/
structure RetainedAt (chain : Option ScopeCtx) (s : EvalState) (n : Nat) : Prop where
  valid : OwnerSearchValid chain s
  context : propertyOwnerBindingContext chain s = some n

theorem RetainedAt.mono {chain : Option ScopeCtx} {s t : EvalState} {n : Nat}
    (hr : RetainedAt chain s n) (h : ActivationPrefix s t) : RetainedAt chain t n :=
  ⟨OwnerSearchValid.mono h hr.valid, (owner_context_stable h hr.valid).trans hr.context⟩

/-- An unactivated level over a retained chain — a structural `B.V`'s rebuilt receiver, an opened
    provider, a body entered without a record — retains the same context. -/
theorem RetainedAt.unactivated_level {parent : Option ScopeCtx} {s : EvalState} {n : Nat}
    (hr : RetainedAt parent s n) (params : List Ident) (opens : List Expr) (props : List PropDef)
    (output : List Expr) (branches : List CondBranch) (decl : Option PropertyIdentity) :
    RetainedAt (some (.mk parent params opens props output branches none decl)) s n :=
  ⟨by simpa only [OwnerSearchValid] using hr.valid,
   (owner_context_unactivated parent params opens props output branches decl s).trans hr.context⟩

/-- A level activated at an existing record retains that record's context, whatever its parents. -/
theorem RetainedAt.activated_level (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (id : Nat)
    (decl : Option PropertyIdentity) (s : EvalState) (act : ParameterActivation)
    (h : s.lexicalActivations[id]? = some act) :
    RetainedAt (some (.mk parent params opens props output branches (some id) decl)) s act.bindingContext := by
  refine ⟨?_, owner_context_activated parent params opens props output branches id decl s act h⟩
  simp only [OwnerSearchValid]
  exact (Array.getElem?_eq_some_iff.1 h).1

/-! ## 3. The production writers establish retained chains -/

/-- The one writer: it appends the advertised record and returns that record's index, which is the
    old size — an index in the array, NOT the record's binding context. -/
theorem recordParameterActivation_run (names : List Ident) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (recordParameterActivation names ctx env).runState s =
      (.ok s.lexicalActivations.size,
       { s with
         lexicalActivations := s.lexicalActivations.push
           { values := env.filter (fun b => names.contains b.fst)
             needs := ctx.needEnv.filter (fun b => names.contains b.fst)
             bindingContext := ctx.bindingContext } }) := rfl

/-- The returned index exists in the resulting array and holds the appended record. -/
theorem pushed_record {s t : EvalState} {a : ParameterActivation}
    (h : t.lexicalActivations = s.lexicalActivations.push a) :
    t.lexicalActivations[s.lexicalActivations.size]? = some a := by
  simp [h]

/-- The activated scope ONE recording body entry installs as its head scope. -/
def enteredScope (a : Algorithm) (s : EvalState) : ScopeCtx :=
  a.asScopeCtx.withActivation s.lexicalActivations.size

/-- The scope a body's rows are formed in: the activated head when the entry records an activation,
    the body's own unactivated level otherwise. -/
def enteredSite (a : Algorithm) (s : EvalState) : ScopeCtx :=
  if recordsActivation a then enteredScope a s else a.asScopeCtx

theorem entered_siteScope (a : Algorithm) (ctx : EvalCtx) (s : EvalState) :
    siteScope? (enteredCtx a ctx s) = some (enteredSite a s) := by
  unfold enteredCtx enteredSite siteScope? EvalCtx.head? EvalCtx.push
  split <;> rfl

theorem entered_prefix (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ActivationPrefix s (enteredState a ctx env s) := by
  unfold enteredState
  split
  · exact ActivationPrefix.push s _
  · exact ActivationPrefix.refl s

theorem entered_record (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hrec : recordsActivation a = true) :
    (enteredState a ctx env s).lexicalActivations[s.lexicalActivations.size]? =
      some (enteredActivation a ctx env) := by
  unfold enteredState
  rw [if_pos hrec]
  exact pushed_record rfl

/-- **Ordinary body entry establishes the retained chain**: a recording entry's head scope is valid
    in the entered state, with NO premise on the incoming chain, and retains the entry context —
    `enteredActivation` stores `ctx.bindingContext`, whatever index it landed at. -/
theorem entered_scope_retained (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hrec : recordsActivation a = true) :
    RetainedAt (some (enteredScope a s)) (enteredState a ctx env s) ctx.bindingContext :=
  RetainedAt.activated_level _ _ _ _ _ _ _ _ _ _ (entered_record a ctx env s hrec)

/-- Entry keeps every incoming chain it found retained, recording or not. -/
theorem entered_keeps_chain (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    {chain : Option ScopeCtx} {n : Nat} (hr : RetainedAt chain s n) :
    RetainedAt chain (enteredState a ctx env s) n :=
  hr.mono (entered_prefix a ctx env s)

/-- A body entered without a record has no level of its own in the search: its site retains what
    its declaring chain retains. -/
theorem entered_site_of_parent (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) {n : Nat}
    (hrec : recordsActivation a = false) (hr : RetainedAt a.parent s n) :
    RetainedAt (some (enteredSite a s)) (enteredState a ctx env s) n := by
  have hs : enteredState a ctx env s = s := by simp [enteredState, hrec]
  rw [hs]
  simp only [enteredSite, hrec, Bool.false_eq_true, if_false]
  exact hr.unactivated_level _ _ _ _ _ _

/-- **Any entry whose context carries the retained `n`** — an inherited entry, a selected family
    body — has a retained site, recording or not. -/
theorem entered_site_retained (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) {n : Nat}
    (hn : ctx.bindingContext = n) (hr : RetainedAt a.parent s n) :
    RetainedAt (some (enteredSite a s)) (enteredState a ctx env s) n := by
  cases hrec : recordsActivation a with
  | false => exact entered_site_of_parent a ctx env s hrec hr
  | true =>
    simp only [enteredSite, hrec, if_true]
    exact hn ▸ entered_scope_retained a ctx env s hrec

/-- **A read-owned entry retains the declaring context.** The entry of `enterPropertyOwnerBody`
    with the inherited context (`inheritedContext`, for a parameterless owner directly and for a
    collecting-only owner over the binder's context `boundCtx`: only the record's context is
    replaced, `collecting_read_record_keeps_the_binding`) has a site retaining the declaring `m`,
    whatever the reader's and the binder's fresh contexts. The premise is on the incoming chain. -/
theorem property_entry_retains_declaring_context (a : Algorithm) (boundCtx ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) {m : Nat} (hr : RetainedAt a.parent s m) :
    RetainedAt (some (enteredSite a s))
      (enteredState a { boundCtx with bindingContext := inheritedContext a ctx s } env s) m :=
  entered_site_retained a _ env s (by simp only [inheritedContext, hr.context, Option.getD_some]) hr

/-- **Lexical and structural levels agree after a read-owned entry**: the recording entry's level
    and the unactivated level a structural `B.V` or an opened `V` rebuilds over the SAME declaring
    chain answer the same context in the entered state — `lexical_and_structural_levels_agree`,
    with its record and parent premises discharged from the entry. -/
theorem read_entry_levels_agree (a : Algorithm) (boundCtx ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    {m : Nat} (hrec : recordsActivation a = true) (hr : RetainedAt a.parent s m)
    (params : List Ident) (opens : List Expr) (props : List PropDef) (output : List Expr)
    (branches : List CondBranch) (decl : Option PropertyIdentity) :
    propertyOwnerBindingContext (some (enteredScope a s))
        (enteredState a { boundCtx with bindingContext := inheritedContext a ctx s } env s) =
      propertyOwnerBindingContext (some (.mk a.parent params opens props output branches none decl))
        (enteredState a { boundCtx with bindingContext := inheritedContext a ctx s } env s) := by
  have hin : inheritedContext a ctx s = m := by simp only [inheritedContext, hr.context, Option.getD_some]
  exact lexical_and_structural_levels_agree a.parent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m
    (entered_record a _ env s hrec) (entered_keeps_chain a _ env s hr).context hin

/-! The writers themselves, each over its production equation: every one extends the array, so every
chain retained before it stays retained (`RetainedAt.mono`). -/

theorem enterAlgorithmBody_extends (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves ActivationPrefix (enterAlgorithmBody a ctx env) := fun s => by
  rw [enter_run]
  exact entered_prefix a ctx env s

theorem enterPropertyOwnerBody_extends (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (n : Nat) :
    Preserves ActivationPrefix (enterPropertyOwnerBody a ctx env n) := fun s => by
  rw [enterPropertyOwnerBody_run]
  exact entered_prefix a _ env s

theorem wireSelectedBranchBody_extends (callee body : Algorithm) (names : List Ident) (ctx : EvalCtx)
    (env : ValEnv) : Preserves ActivationPrefix (wireSelectedBranchBody callee body names ctx env) :=
  fun _ => ActivationPrefix.of_push rfl

/-- `withParent` installs its chain as written: not a builtin (no chain) and not a module (which
    roots its chain, `ScopeCtx.chainRoot`). Those two routes rebuild a different chain and are not
    covered. -/
def WiresDirectly (a : Algorithm) : Prop := ∀ p, (a.withParent p).parent = p

theorem wiresDirectly_mk (p : Option ScopeCtx) (pp : List ParameterPattern) (o : List Expr)
    (pr : List PropDef) (out : List Expr) (d : Option PropertyIdentity)
    (hm : ∀ n, d ≠ some (.module n)) (hv : ∀ n view, d ≠ some (.moduleView n view)) :
    WiresDirectly (.mk p pp o pr out d) := by
  intro q
  cases d with
  | none => rfl
  | some i =>
    cases i <;> first | rfl | exact absurd rfl (hm _) | exact absurd rfl (hv _ _)

theorem wiresDirectly_conditional (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity) : WiresDirectly (.conditional p o br d) := fun _ => rfl

/-- Wiring onto a retained chain keeps it. -/
theorem RetainedAt.wired {chain : Option ScopeCtx} {s : EvalState} {n : Nat} {child : Algorithm}
    (hr : RetainedAt chain s n) (hw : WiresDirectly child) :
    RetainedAt (child.withParent chain).parent s n := by
  rw [hw]; exact hr

/-- What `childOfInContext` wires, GIVEN the scope `scopeInContext` selected. That selection is the
    lookup-fidelity question (`activeDeclaration?` is `partial`), kept as a premise here. -/
theorem childOfInContext_chain {parent child : Algorithm} {ctx : EvalCtx} {scope : ScopeCtx}
    (hw : WiresDirectly child) (hsel : scopeInContext parent ctx = scope) :
    (childOfInContext parent child ctx).parent = some scope := by
  unfold childOfInContext
  rw [hsel]
  exact hw _

/-- The level a selected clause is wired under (`wireSelectedBranchBody`). -/
def familyScope (callee : Algorithm) (names : List Ident) (id : Nat) : ScopeCtx :=
  .mk callee.parent names callee.opens callee.props callee.output callee.branches (some id) callee.declarationId

/-- **Selected-family activation establishes the retained chain**: `needActivateBranch` extends the
    array and, in its exit state, the family level holds the FRESH binding context the bound context
    received — with no premise on the incoming chain. -/
theorem family_activation_retained (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) (s : EvalState) :
    ActivationPrefix s (runEval (needActivateBranch callee ctx env branch bindings) s).2 ∧
    RetainedAt (some (familyScope callee (bindings.map Prod.fst) s.lexicalActivations.size))
      (runEval (needActivateBranch callee ctx env branch bindings) s).2 s.nextBindingContext := by
  rw [KatLang.FamilyDispatch.activation_run]
  refine ⟨ActivationPrefix.of_push rfl, ?_⟩
  unfold familyScope
  exact RetainedAt.activated_level _ _ _ _ _ _ _ _ _
    { values := _, needs := _, bindingContext := s.nextBindingContext } (pushed_record (s := s) rfl)

/-- The wired body's own entry, in the activated context, has a site retaining that fresh context:
    recording, its head stores it; not recording, the family level answers it. -/
theorem family_body_retained (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) (s : EvalState) (hwired : WiresDirectly branch.body) :
    RetainedAt
      (some (enteredSite (KatLang.FamilyDispatch.activatedBody callee branch bindings s.lexicalActivations.size)
        (runEval (needActivateBranch callee ctx env branch bindings) s).2))
      (enteredState (KatLang.FamilyDispatch.activatedBody callee branch bindings s.lexicalActivations.size)
        (KatLang.FamilyDispatch.activatedContext callee ctx bindings s.nextBindingContext)
        (ValEnv.shadow env (bindings.map Prod.fst))
        (runEval (needActivateBranch callee ctx env branch bindings) s).2)
      s.nextBindingContext := by
  refine entered_site_retained _ _ _ _ rfl ?_
  have h := (family_activation_retained callee ctx env branch bindings s).2
  unfold KatLang.FamilyDispatch.activatedBody
  rw [hwired]
  exact h

/-- **The dispatched body.** Under the premises of `production_dispatch_activates_the_first_match`,
    whatever `selectNeedFamilyBranch` returned is that clause's body, and its site retains the fresh
    context of this activation in its entered state. -/
theorem dispatched_body_retained (c : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (before after : List CondBranch) (branch : CondBranch)
    (s s' s'' : EvalState) (bindings : NeedEnv)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hbranches : Algorithm.branches callee = before ++ branch :: after)
    (hrej : KatLang.FamilyDispatch.RejectedInOrder c.capabilities cells before s s')
    (hmatch : runEval (bindNeedPatterns c (needClauseHead branch.pattern) cells true) s' = (.ok (some bindings), s''))
    (hwired : WiresDirectly branch.body)
    (body : Algorithm) (next : EvalCtx) (values : ValEnv) (t : EvalState)
    (hrun : runEval (selectNeedFamilyBranch c callee cells ctx env name) s = (.ok (body, next, values), t)) :
    RetainedAt (some (enteredSite body t)) (enteredState body next values t) s''.nextBindingContext := by
  have h := (KatLang.FamilyDispatch.production_dispatch_activates_the_first_match c callee cells ctx env name
    before after branch s s' s'' bindings hdup hbranches hrej hmatch).symm.trans hrun
  simp only [Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  exact family_body_retained callee ctx env branch bindings s'' hwired

/-! ## 4. Retained reads: one relation, the whole evaluator -/

/-- What a later read needs of the computation between a publication and itself: the activation
    array extended (so the owner context stays) and every published entry kept (so the key still
    hits). Neither implies the other. -/
def Retained (s t : EvalState) : Prop := ActivationPrefix s t ∧ CacheKept s t

instance : StateRel Retained :=
  ⟨fun s => ⟨ActivationPrefix.refl s, StateRel.refl s⟩,
   fun h k => ⟨h.1.trans k.1, StateRel.trans h.2 k.2⟩⟩

instance : WriteFrame Retained :=
  ⟨fun s t hc ha hl => ⟨ActivationPrefix.of_eq hl, WriteFrame.keep s t hc ha hl⟩,
   fun s a => ⟨ActivationPrefix.push s a, WriteFrame.push s a⟩⟩

/-- Every production operation, from every state, whatever its outcome, retains. -/
theorem production_retained (c : EvalCall) : Preserves Retained (evalUnbounded c) :=
  fun s => ⟨activations_kept c s, cache_entries_survive c s⟩

/-- Every completed core run retains. -/
theorem core_retained (n : Nat) (c : EvalCall) (s : EvalState) (hc : Completes (evalFuel n c) s) :
    Retained s ((evalFuel n c).runState s).2 :=
  ⟨activations_kept_core n c s hc, cache_entries_survive_core n c s hc⟩

/-- The step shared by every reuse theorem below: `local_publication_reused` with its `hstable`
    premise DERIVED from the chain retained at the earlier state. -/
theorem local_entry_read (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolved : Algorithm) (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) {n : Nat} {s t : EvalState} {v : CountedResult}
    (hret : RetainedAt resolved.parent s n)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (hkept : Retained s t) (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState t = (.ok v, t) :=
  local_publication_reused k k' owner binding resolved hcache ctx₀ env₀ n s t v hentry hkept.2 ctx env
    (hret.mono hkept.1).context

/-- **THE PRODUCTION THEOREM (FG-K2).** Let the fixed declaring chain of `resolved` have a valid
    owner search at `s`, answering `n`, and let the cache hold `v` for this owner and binding under
    retained context `n`. After ANY production operation from `s` — its actual exit state, whatever
    its outcome, whatever nested calls, activations and publications it made — a cacheable READ of
    that binding, in ANY consumer context and environment, returns `v` and leaves the state
    unchanged. Cache survival and the former `hstable` premise are both derived from the operation.
    Reads only: an explicit invocation stays fresh. -/
theorem local_publication_reused_after_production (c : EvalCall) (k k' : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (s : EvalState) (v : CountedResult)
    (hvalid : OwnerSearchValid resolved.parent s)
    (howner : propertyOwnerBindingContext resolved.parent s = some n)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState
        ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) :=
  local_entry_read k k' owner binding resolved hcache ctx₀ env₀ ⟨hvalid, howner⟩ hentry
    (production_retained c s) ctx env

/-- The same over a completed run of the total core (an incomplete core run forgets its state). -/
theorem local_publication_reused_after_core (m : Nat) (c : EvalCall) (k k' : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (s : EvalState) (v : CountedResult)
    (hc : Completes (evalFuel m c) s) (hret : RetainedAt resolved.parent s n)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState
        ((evalFuel m c).runState s).2 =
      (.ok v, ((evalFuel m c).runState s).2) :=
  local_entry_read k k' owner binding resolved hcache ctx₀ env₀ hret hentry
    (core_retained m c s hc) ctx env

/-- An operation that FAILS ordinarily still kept the records and the entries: a post-state query.
    It does not say the containing language run continues past the failure. -/
theorem failed_operation_keeps_local_entry (c : EvalCall) (e : Error) (t : EvalState)
    (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (s : EvalState) (v : CountedResult)
    (hrun : (evalUnbounded c).runState s = (.error e, t))
    (hret : RetainedAt resolved.parent s n)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState t = (.ok v, t) := by
  have h := production_retained c s
  rw [hrun] at h
  exact local_entry_read k k' owner binding resolved hcache ctx₀ env₀ hret hentry h ctx env

/-- **The host fallback keeps its input conditions.** With no retained context (`none` on a valid
    chain, which stays `none`), a surviving entry is reused only by a read with the SAME environment
    and an equal binding context: nothing here makes such a key consumer-independent. -/
theorem fallback_publication_reused_after_production (c : EvalCall) (k k' : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ ctx : EvalCtx) (env : ValEnv) (s : EvalState) (v : CountedResult)
    (hvalid : OwnerSearchValid resolved.parent s)
    (hnone : propertyOwnerBindingContext resolved.parent s = none)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env none) = some v)
    (hctx : ctx.bindingContext = ctx₀.bindingContext) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState
        ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) := by
  have hr := production_retained c s
  apply property_cache_hit_production k' owner binding resolved ctx env _ v hcache
  rw [owner_context_stable hr.1 hvalid, hnone, cacheKey_same_inputs k' k owner binding ctx ctx₀ env hctx]
  exact hr.2 _ v hentry

/-! ## 5. Lexical and structural reads -/

/-- The key fields besides the access context: equal for two reads of one binding through two
    spellings. Equality of the retained context ALONE does not equate keys; this does. -/
structure SameKeyFields (owner : Algorithm) (binding : PropDef) (owner' : Algorithm) (binding' : PropDef) : Prop where
  ownerShape : reprStr owner.declarationId ++ reprStr (cacheScopeShape owner.asScopeCtx) =
    reprStr owner'.declarationId ++ reprStr (cacheScopeShape owner'.asScopeCtx)
  hostOwners : hostMarks 0 owner.asScopeCtx.hostChain = hostMarks 0 owner'.asScopeCtx.hostChain
  componentOwners : hostMarks 0 owner.asScopeCtx.componentChain = hostMarks 0 owner'.asScopeCtx.componentChain
  propertyName : binding.name = binding'.name
  propertyAlgorithm : reprStr (cacheAlgorithmShape binding.alg) = reprStr (cacheAlgorithmShape binding'.alg)
  exported : binding.exposure.isExported = binding'.exposure.isExported

theorem cacheKey_of_same_fields {owner owner' : Algorithm} {binding binding' : PropDef}
    (h : SameKeyFields owner binding owner' binding') (k k' : ZeroArgPropertyAccessKind)
    (ctx ctx' : EvalCtx) (env env' : ValEnv) (n : Nat) :
    zeroArgPropertyCacheKey k' owner' binding' ctx' env' (some n) =
      zeroArgPropertyCacheKey k owner binding ctx env (some n) := by
  simp [zeroArgPropertyCacheKey, h.ownerShape, h.hostOwners, h.componentOwners, h.propertyName, h.propertyAlgorithm, h.exported]

/-- **A structural or opened read reuses the lexical read's entry.** `resolved` hangs under a level
    activated at record `id`, `resolved'` under the unactivated level rebuilt over the SAME parent
    chain, and the record holds the context the parent chain retains
    (`lexical_and_structural_levels_agree`). When the two spellings also have the same key fields,
    an entry published lexically is read through BOTH spellings, after any production operation.
    Other routes to a property are not claimed. -/
theorem structural_read_reuses_lexical_entry (c : EvalCall) (k k' : ZeroArgPropertyAccessKind)
    (owner owner' : Algorithm) (binding binding' : PropDef) (resolved resolved' : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (hcache' : isCacheableZeroArgPropertyAlgorithm resolved' = true)
    (hfields : SameKeyFields owner binding owner' binding')
    (parent : Option ScopeCtx) (params params' : List Ident) (opens opens' : List Expr)
    (props props' : List PropDef) (output output' : List Expr) (branches branches' : List CondBranch)
    (id : Nat) (decl decl' : Option PropertyIdentity) (act : ParameterActivation)
    (hlex : resolved.parent = some (.mk parent params opens props output branches (some id) decl))
    (hstr : resolved'.parent = some (.mk parent params' opens' props' output' branches' none decl'))
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (s : EvalState) (v : CountedResult)
    (hrecord : s.lexicalActivations[id]? = some act) (hparent : RetainedAt parent s n)
    (hrecorded : act.bindingContext = n)
    (hentry : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState
        ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) ∧
    (evalZeroArgPropertyAccessCounted k' owner' binding' resolved' ctx env).runState
        ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) := by
  have hagree := lexical_and_structural_levels_agree parent params params' opens opens' props props'
    output output' branches branches' id decl decl' s act n hrecord hparent.context hrecorded
  have hret : RetainedAt resolved'.parent s n := by
    refine ⟨?_, ?_⟩
    · rw [hstr]; exact (hparent.unactivated_level params' opens' props' output' branches' decl').valid
    · rw [hstr, ← hagree, owner_context_activated parent params opens props output branches id decl s act hrecord,
        hrecorded]
  have hret₀ : RetainedAt resolved.parent s n := by
    rw [hlex, ← hrecorded]
    exact RetainedAt.activated_level parent params opens props output branches id decl s act hrecord
  refine ⟨local_entry_read k k' owner binding resolved hcache ctx₀ env₀ hret₀ hentry (production_retained c s) ctx env,
    local_entry_read k k' owner' binding' resolved' hcache' ctx₀ env₀ hret ?_ (production_retained c s) ctx env⟩
  rw [cacheKey_of_same_fields hfields k k ctx₀ ctx₀ env₀ env₀ n]
  exact hentry

/-! ## 6. The rows of one entered body -/

section Rows
variable (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)

/-- The ONE row former of an entered body (`readRows_entered`). -/
abbrev bodyRows : Expr → EvalM (List Result) := formOutputRow (enteredCtx a ctx s) env

/-- The state after a round's discovery, over the entered state. -/
abbrev discovered : EvalState :=
  ((WhileRound.discover (bodyRows a ctx env s) a.output.reverse).runState (enteredState a ctx env s)).2

omit a ctx env s in
theorem rows_retained (rowCtx : EvalCtx) (rowEnv : ValEnv) (rows : List Expr) :
    Preserves Retained (OutputRows.formLeftToRight (formOutputRow rowCtx rowEnv) rows) :=
  pres_formLeftToRight _ (fun e => production_retained (.formOutputRow rowCtx rowEnv e)) rows

theorem discover_retained (rowCtx : EvalCtx) (rowEnv : ValEnv) (rows : List Expr) :
    Preserves Retained (WhileRound.discover (formOutputRow rowCtx rowEnv) rows) :=
  pres_discover _ (fun e => production_retained (.formOutputRow rowCtx rowEnv e)) rows

/-- What a round does after discovery retains: the flag check, then — only on `true` — the earlier
    rows. On every other path no row is formed. -/
theorem after_discovery_retained (form : Expr → EvalM (List Result)) (h : ∀ e, Preserves Retained (form e))
    (rows : List Expr) (t : EvalState) :
    Retained ((WhileRound.discover form rows.reverse).runState t).2
      ((WhileRound.conditionFirst form rows).runState t).2 := by
  have hrows := pres_formLeftToRight (R := Retained) form h
  unfold WhileRound.conditionFirst
  rw [EvalM.bind_runState]
  rcases hd : (WhileRound.discover form rows.reverse).runState t with ⟨o, t'⟩
  cases o with
  | error e => exact StateRel.refl t'
  | ok r =>
    dsimp only
    revert t'
    have hk : Preserves Retained
        (match r with
         | none => WhileRound.noFlag
         | some (earlier, flagItems) =>
           match flagItems.getLast? with
           | none => WhileRound.noFlag
           | some f => do
             if ← WhileRound.flag f then
               let formed ← OutputRows.formLeftToRight form earlier
               pure (some (WhileRound.nextSlots (formed ++ flagItems)))
             else pure none : EvalM (Option (List Result))) := by
      pres_tac_mid
    intro t' _
    exact hk t'

/-- The whole round's row reading retains. -/
theorem conditionFirst_retained (rowCtx : EvalCtx) (rowEnv : ValEnv) (rows : List Expr) :
    Preserves Retained (WhileRound.conditionFirst (formOutputRow rowCtx rowEnv) rows) := fun t =>
  StateRel.trans (discover_retained rowCtx rowEnv rows.reverse t)
    (after_discovery_retained _ (fun e => production_retained (.formOutputRow rowCtx rowEnv e)) rows t)

/-- **Later rows read discovery's entry.** The chain retained at the entered state — by a recording
    entry, a read-owned entry or a family activation (§3) — and an entry present when discovery
    ends: every read during or after any left-to-right formation of the earlier rows, whatever
    those rows evaluate, returns the entry, in any consumer context. -/
theorem transitions_read_discovery_entry (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (resolved : Algorithm) (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (v : CountedResult)
    (hret : RetainedAt resolved.parent (enteredState a ctx env s) n)
    (hpub : ZeroArgPropertyCache.lookup (discovered a ctx env s).zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (earlier : List Expr) (readCtx : EvalCtx) (readEnv : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved readCtx readEnv).runState
        ((OutputRows.formLeftToRight (bodyRows a ctx env s) earlier).runState (discovered a ctx env s)).2 =
      (.ok v, ((OutputRows.formLeftToRight (bodyRows a ctx env s) earlier).runState (discovered a ctx env s)).2) :=
  local_entry_read k k' owner binding resolved hcache ctx₀ env₀
    (hret.mono (discover_retained _ env a.output.reverse _).1) hpub (rows_retained _ env earlier _)
    readCtx readEnv

/-- The ordinary instance, with NO validity premise: a property wired under the head scope ONE
    recording entry installs keeps the entry context, so `RetainedAt` comes from the entry. -/
theorem entered_body_shares_local_entry (hrec : recordsActivation a = true)
    (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (hparent : resolved.parent = some (enteredScope a s))
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (v : CountedResult)
    (hpub : ZeroArgPropertyCache.lookup (discovered a ctx env s).zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some ctx.bindingContext)) = some v)
    (earlier : List Expr) (readCtx : EvalCtx) (readEnv : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved readCtx readEnv).runState
        ((OutputRows.formLeftToRight (bodyRows a ctx env s) earlier).runState (discovered a ctx env s)).2 =
      (.ok v, ((OutputRows.formLeftToRight (bodyRows a ctx env s) earlier).runState (discovered a ctx env s)).2) :=
  transitions_read_discovery_entry a ctx env s k k' owner binding resolved hcache ctx₀ env₀ _ v
    (hparent ▸ entered_scope_retained a ctx env s hrec) hpub earlier readCtx readEnv

/-- **The production round's exit reads discovery's entry**: for a checked, non-builtin step whose
    round completes, the actual exit state of `whileVerdictSlots` — `true`, `false` or a failure —
    still answers the entry. -/
theorem round_exit_reads_discovery_entry (ha : NotBuiltin a) (hp : Passes a)
    (hc : ((WhileRound.conditionFirst (bodyRows a ctx env s) a.output).runState
      (enteredState a ctx env s)).1 ≠ .error .fuelExhausted)
    (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (v : CountedResult)
    (hret : RetainedAt resolved.parent (enteredState a ctx env s) n)
    (hpub : ZeroArgPropertyCache.lookup (discovered a ctx env s).zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (readCtx : EvalCtx) (readEnv : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved readCtx readEnv).runState
        ((whileVerdictSlots a ctx env).runState s).2 =
      (.ok v, ((whileVerdictSlots a ctx env).runState s).2) := by
  rw [whileVerdictSlots_entered a ha hp ctx env s hc]
  exact local_entry_read k k' owner binding resolved hcache ctx₀ env₀
    (hret.mono (discover_retained _ env a.output.reverse _).1) hpub
    (after_discovery_retained _ (fun e => production_retained (.formOutputRow _ env e)) a.output _)
    readCtx readEnv

/-- **A false continuation forms no transition and still keeps the entry**: under the CF-1 premises
    the round stops in the state discovery reached (`production_cf1_false_skips_earlier_rows`); no
    earlier row is formed to obtain this, and that state answers an entry it holds. -/
theorem false_continuation_keeps_local_entry (ha : NotBuiltin a) (hp : Passes a)
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ : EvalState) (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix (bodyRows a ctx env s) trail (enteredState a ctx env s) s₁)
    (hr : (bodyRows a ctx env s r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some false)
    (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (v : CountedResult)
    (hret : RetainedAt resolved.parent (enteredState a ctx env s) n)
    (hpub : ZeroArgPropertyCache.lookup s₂.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (readCtx : EvalCtx) (readEnv : ValEnv) :
    (whileVerdictSlots a ctx env).runState s = (.ok none, s₂) ∧
    (evalZeroArgPropertyAccessCounted k' owner binding resolved readCtx readEnv).runState s₂ = (.ok v, s₂) := by
  refine ⟨production_cf1_false_skips_earlier_rows a ha hp ctx env s pre r trail hrows s₁ s₂ x xs f htrail hr hlast hf, ?_⟩
  have h := cf1_false_skips_earlier_rows _ pre r trail _ s₁ s₂ x xs f htrail hr hlast hf
  rw [← hrows] at h
  have hk := conditionFirst_retained (enteredCtx a ctx s) env a.output (enteredState a ctx env s)
  rw [show (WhileRound.conditionFirst (formOutputRow (enteredCtx a ctx s) env) a.output).runState
    (enteredState a ctx env s) = (.ok none, s₂) from h] at hk
  exact property_cache_hit_production k' owner binding resolved readCtx readEnv s₂ v hcache (by
    rw [(hret.mono hk.1).context, cacheKey_retained_owner_context k' k owner binding readCtx ctx₀ readEnv env₀ n]
    exact hpub)

end Rows

/-! ## 7. A dispatched family body -/

/-- **A dispatched family round's rows share a local entry**: `dispatched_body_retained` feeds
    `transitions_read_discovery_entry`. No premise on the incoming chain. -/
theorem dispatched_body_shares_local_entry (c : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (before after : List CondBranch) (branch : CondBranch)
    (s s' s'' : EvalState) (bindings : NeedEnv)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hbranches : Algorithm.branches callee = before ++ branch :: after)
    (hrej : KatLang.FamilyDispatch.RejectedInOrder c.capabilities cells before s s')
    (hmatch : runEval (bindNeedPatterns c (needClauseHead branch.pattern) cells true) s' = (.ok (some bindings), s''))
    (hwired : WiresDirectly branch.body)
    (body : Algorithm) (next : EvalCtx) (values : ValEnv) (t : EvalState)
    (hrun : runEval (selectNeedFamilyBranch c callee cells ctx env name) s = (.ok (body, next, values), t))
    (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (hparent : resolved.parent = some (enteredSite body t))
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (v : CountedResult)
    (hpub : ZeroArgPropertyCache.lookup (discovered body next values t).zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some s''.nextBindingContext)) = some v)
    (earlier : List Expr) (readCtx : EvalCtx) (readEnv : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved readCtx readEnv).runState
        ((OutputRows.formLeftToRight (bodyRows body next values t) earlier).runState (discovered body next values t)).2 =
      (.ok v, ((OutputRows.formLeftToRight (bodyRows body next values t) earlier).runState (discovered body next values t)).2) :=
  transitions_read_discovery_entry body next values t k k' owner binding resolved hcache ctx₀ env₀ _ v
    (hparent ▸ dispatched_body_retained c callee cells ctx env name before after branch s s' s'' bindings
      hdup hbranches hrej hmatch hwired body next values t hrun) hpub earlier readCtx readEnv

end KatLang.OwnerContextStability
