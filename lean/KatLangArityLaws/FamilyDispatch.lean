import KatLangArityLaws.BinderTrace

open KatLang KatLang.BinderTrace

/-!
# Clause-family dispatch: search, activation and trace (R3, October 2026)

The production dispatcher `selectNeedFamilyBranch c callee cells ctx env name` is, by definition,
the generic dispatcher `NeedBinder.selectFamily c.capabilities callee cells name
(needActivateBranch callee ctx env)` (`production_dispatcher_is_the_core`): a duplicate-clause
check, the family's cardinality check, then the clause search `NeedBinder.chooseBranch`, whose
first match is handed to the one activation `needActivateBranch`.

The laws are stated at the layer they belong to:

* § Search — for EVERY capability record `k : NeedCapabilities EvalM` (the production one is
  `c.capabilities`) and EVERY activation callback:
  the precedence of the two checks, written-order attempts over the SAME supplied cells, a
  non-match continuing from the state the attempt left (no rollback), a raised failure aborting
  the search, the first match being the only activation, and exhaustion;
* § Activation — the production `needActivateBranch` for an ARBITRARY incoming context, value
  environment and evaluator state: the fresh binding context, the shadowing of inherited names,
  the recorded lexical activation and the wired body, all exactly;
* § Composition — the production dispatcher end to end, for arbitrary contexts: the first
  match activated, an attempt's raised failure, and exhaustion (with
  `choose_outcomes_are_exhaustive`, these are all the outcomes past the two checks);
* § Trace — the dispatcher in the trace interpretation: its events are its attempts' binder
  events, in order, and activation adds none.

Not claimed: anything about `Algorithm.hasDuplicateBranchPatterns` beyond its Boolean (it calls
`partial` definitions), the partial callers that pass the channels (`evalNeedFamilySupply`,
`runNeedStepSlots`), or C#. A raw family-mode `none` is a clause NON-MATCH; it is not the
ordinary call's arity error — the ordinary driver `evalNeedUserSupply` (`partial`) turns an
unexpected `none` into `badArity` itself, a source fact — and the raw binder returns `none` for
a literal mismatch in BOTH modes (`literal_mismatch_is_none_in_both_modes`).
-/

namespace KatLang.FamilyDispatch

/-! ## Search -/

section Search

variable {β : Type} (k : NeedCapabilities EvalM) (cells : List Nat) (name : String)
  (activate : CondBranch → NeedEnv → EvalM β)

/-- THE SEARCH STEP: the next clause is attempted on the SAME supplied cells (the dispatcher's
    `cells`, never a re-formed supply) through the binder in family mode; a non-match continues
    with the next clause FROM THE STATE THE ATTEMPT LEFT, a raised error aborts the search with
    that error and state, and a match is activated — after its binding, and only it. -/
theorem choose_step (branch : CondBranch) (rest : List CondBranch) (s : EvalState) :
    runEval (NeedBinder.chooseBranch k cells name activate (branch :: rest)) s
      = match runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s with
        | (.ok none, s1) => runEval (NeedBinder.chooseBranch k cells name activate rest) s1
        | (.ok (some bindings), s1) => runEval (activate branch bindings) s1
        | (.error e, s1) => (.error e, s1) := by
  simp only [NeedBinder.chooseBranch, runEval_bind]
  rcases runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s
    with ⟨_ | (_ | bindings), s1⟩ <;> rfl

/-- EXHAUSTION: no clause left is `noMatchingBranch`, in the state the attempts left. -/
theorem choose_exhausted (s : EvalState) :
    runEval (NeedBinder.chooseBranch k cells name activate []) s
      = (.error (Error.noMatchingBranch name), s) := rfl

/-- `RejectedInOrder k cells branches s s'`: every clause of `branches`, attempted in written
    order on the same cells, was a NON-MATCH, the first from `s`, each next one from the state
    the previous attempt left, ending in `s'`. -/
inductive RejectedInOrder : List CondBranch → EvalState → EvalState → Prop
  | nil (s : EvalState) : RejectedInOrder [] s s
  | cons (branch : CondBranch) (rest : List CondBranch) (s s1 s' : EvalState)
      (h : runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s = (.ok none, s1))
      (hrest : RejectedInOrder rest s1 s') : RejectedInOrder (branch :: rest) s s'

/-- THE FIRST MATCH IN WRITTEN ORDER IS THE ONE ACTIVATED: after the clauses `before` were all
    non-matches (each from the state the previous one left — their completed effects retained),
    a matching clause is activated with ITS bindings in the state its own attempt left; the
    clauses after it are never attempted. -/
theorem choose_selects_the_first_match (before after : List CondBranch) (branch : CondBranch)
    (s s' s'' : EvalState) (bindings : NeedEnv) (hrej : RejectedInOrder k cells before s s')
    (hmatch : runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s'
      = (.ok (some bindings), s'')) :
    runEval (NeedBinder.chooseBranch k cells name activate (before ++ branch :: after)) s
      = runEval (activate branch bindings) s'' := by
  induction hrej with
  | nil s => rw [List.nil_append, choose_step, hmatch]
  | cons b rest s s1 s' h _ ih => rw [List.cons_append, choose_step, h]; exact ih hmatch

/-- A RAISED FAILURE ABORTS THE SEARCH: an attempt that raises (a VALUE or CALLABLE failure, a
    failed allocation, an ordinary binder error) ends the dispatch with that error and the state
    it left; no later clause is attempted and nothing is activated. -/
theorem choose_aborts_on_a_raised_failure (before after : List CondBranch) (branch : CondBranch)
    (s s' t : EvalState) (e : Error) (hrej : RejectedInOrder k cells before s s')
    (hfail : runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s'
      = (.error e, t)) :
    runEval (NeedBinder.chooseBranch k cells name activate (before ++ branch :: after)) s
      = (.error e, t) := by
  induction hrej with
  | nil s => rw [List.nil_append, choose_step, hfail]
  | cons b rest s s1 s' h _ ih => rw [List.cons_append, choose_step, h]; exact ih hfail

/-- NO CLAUSE MATCHES: `noMatchingBranch`, in the state the last attempt left. -/
theorem choose_reports_no_matching_branch (branches : List CondBranch) (s s' : EvalState)
    (hrej : RejectedInOrder k cells branches s s') :
    runEval (NeedBinder.chooseBranch k cells name activate branches) s
      = (.error (Error.noMatchingBranch name), s') := by
  induction hrej with
  | nil s => rfl
  | cons b rest s s1 s' h _ ih => rw [choose_step, h]; exact ih

/-- THE SEARCH OUTCOMES ARE EXHAUSTIVE: either every clause was a non-match in written order
    (then `choose_reports_no_matching_branch`), or some clause, after the non-matches before it,
    was the first attempt to bind or to raise (then `choose_selects_the_first_match` or
    `choose_aborts_on_a_raised_failure`). -/
theorem choose_outcomes_are_exhaustive (branches : List CondBranch) (s : EvalState) :
    (∃ s', RejectedInOrder k cells branches s s')
    ∨ ∃ before branch after s' result t, branches = before ++ branch :: after
        ∧ RejectedInOrder k cells before s s'
        ∧ runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s' = (result, t)
        ∧ result ≠ .ok none := by
  induction branches generalizing s with
  | nil => exact Or.inl ⟨s, .nil s⟩
  | cons branch rest ih =>
    rcases h : runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s
      with ⟨result, s1⟩
    by_cases hnone : result = .ok none
    · subst hnone
      rcases ih s1 with ⟨s', hrej⟩ | ⟨before, b, after, s', result', t, hb, hrej, hrun, hne⟩
      · exact Or.inl ⟨s', .cons branch rest s s1 s' h hrej⟩
      · exact Or.inr ⟨branch :: before, b, after, s', result', t, by simp [hb],
          .cons branch before s s1 s' h hrej, hrun, hne⟩
    · exact Or.inr ⟨[], branch, rest, s, result, s1, rfl, .nil s, h, hnone⟩

/-- A family-mode attempt that binds or raises got past its own cardinality gate (an unaccepted
    count is a silent non-match). -/
theorem attempt_past_its_gate (ps : List NeedPattern) (s t : EvalState) (result : Except Error (Option NeedEnv))
    (hrun : runEval (NeedBinder.bindPatterns k ps cells true) s = (result, t)) (hne : result ≠ .ok none) :
    needAcceptsCardinality ps cells.length = true := by
  cases hacc : needAcceptsCardinality ps cells.length
  · rw [show NeedBinder.bindPatterns k ps cells true = pure none by
      simp [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, hacc]] at hrun
    simp at hrun
    exact absurd hrun.1.symm hne
  · rfl

/-- THE DUPLICATE-CLAUSE CHECK PRECEDES EVERYTHING: a family with duplicate heads fails before
    the count check, before any attempt and with the state unchanged. -/
theorem select_duplicate_first (callee : Algorithm) (s : EvalState)
    (hdup : callee.hasDuplicateBranchPatterns = true) :
    runEval (NeedBinder.selectFamily k callee cells name activate) s
      = (.error Error.duplicateBranchPattern, s) := by
  simp [NeedBinder.selectFamily, hdup]

/-- THE FAMILY'S COUNT CHECK PRECEDES EVERY ATTEMPT: when no clause head accepts the supply
    count, dispatch fails with the first clause's minimum and the complete count, before any
    attempt and with the state unchanged — never `noMatchingBranch`. -/
theorem select_count_before_attempts (callee : Algorithm) (s : EvalState)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hnone : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = false) :
    runEval (NeedBinder.selectFamily k callee cells name activate) s
      = (.error (Error.arityMismatch
          (((Algorithm.branches callee).head?.map
            (fun branch => needMinimumSuppliedSlots (needClauseHead branch.pattern))).getD 0)
          cells.length), s) := by
  simp [NeedBinder.selectFamily, hdup, hnone]

/-- Past both checks, dispatch IS the clause search over the family's clauses in written order,
    from the unchanged state. -/
theorem select_is_the_search (callee : Algorithm) (s : EvalState)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hsome : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = true) :
    runEval (NeedBinder.selectFamily k callee cells name activate) s
      = runEval (NeedBinder.chooseBranch k cells name activate (Algorithm.branches callee)) s := by
  simp [NeedBinder.selectFamily, hdup, hsome]

end Search

/-! ### Association-list lookups -/

theorem lookupAssoc_append {A : Type} (x : Ident) (l1 l2 : Assoc Ident A) :
    lookupAssoc x (l1 ++ l2) = match lookupAssoc x l1 with
      | some v => some v
      | none => lookupAssoc x l2 := by
  induction l1 with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    by_cases hx : x = key <;> simp [lookupAssoc, hx, ih]

theorem lookupAssoc_filter_unbound {A : Type} (x : Ident) (names : List Ident) (l : Assoc Ident A) :
    lookupAssoc x (l.filter (fun entry => !names.contains entry.fst))
      = if x ∈ names then none else lookupAssoc x l := by
  induction l with
  | nil => simp [lookupAssoc]
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    simp only [List.contains_eq_mem] at ih ⊢
    by_cases hk : key ∈ names
    · by_cases hx : x = key
      · subst hx; simp_all
      · simp_all [lookupAssoc]
    · by_cases hx : x = key
      · subst hx; simp_all [lookupAssoc]
      · simp_all [lookupAssoc]

theorem lookupAssoc_of_not_key {A : Type} (x : Ident) (l : Assoc Ident A)
    (h : (l.map Prod.fst).contains x = false) : lookupAssoc x l = none := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    have hx : x ≠ key := by intro hxk; subst hxk; simp at h
    have ht : (tail.map Prod.fst).contains x = false := by simp_all
    simp [lookupAssoc, hx, ih ht]

theorem lookupAssoc_of_key {A : Type} (x : Ident) (l : Assoc Ident A)
    (h : (l.map Prod.fst).contains x = true) : ∃ v, lookupAssoc x l = some v := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    by_cases hx : x = key
    · exact ⟨value, by simp [lookupAssoc, hx]⟩
    · have ht : (tail.map Prod.fst).contains x = true := by
        simp only [List.map_cons, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · exact absurd h hx
        · exact h
      obtain ⟨v, hv⟩ := ih ht
      exact ⟨v, by simp [lookupAssoc, hx, hv]⟩

/-! ## Activation, for arbitrary incoming context, values and state -/

/-- The context a selected clause runs in: the family pushed on the incoming context, a FRESH
    binding context, and the clause's bindings in front of the inherited cells, from which every
    bound name was removed. -/
def activatedContext (callee : Algorithm) (ctx : EvalCtx) (bindings : NeedEnv) (fresh : Nat) : EvalCtx :=
  { ctx.push callee with
    bindingContext := fresh,
    needEnv := bindings ++ (ctx.push callee).needEnv.filter
      (fun entry => !(bindings.map Prod.fst).contains entry.fst) }

/-- The selected body wired under the family, publishing the binder names and the activation
    record `activation`. -/
def activatedBody (callee : Algorithm) (branch : CondBranch) (bindings : NeedEnv) (activation : Nat) :
    Algorithm :=
  branch.body.withParent (some (.mk callee.parent (bindings.map Prod.fst) callee.opens callee.props
    callee.output callee.branches (some activation) callee.declarationId))

/-- THE ACTIVATION OF A SELECTED CLAUSE, exactly, for EVERY incoming context `ctx`, value
    environment `env`, callee, clause, bindings and evaluator state `s`: the body wired with
    activation id `s.lexicalActivations.size`, the context `activatedContext` with the fresh
    binding context `s.nextBindingContext`, the values `env` with every bound name shadowed;
    and the state with the binding-context counter advanced by one and ONE lexical activation
    recorded (the new context's id, the shadowed values' and the new context's entries for the
    bound names) — nothing else changes: no cell is demanded, projected or allocated. -/
theorem activation_run (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) (s : EvalState) :
    runEval (needActivateBranch callee ctx env branch bindings) s
      = (.ok (activatedBody callee branch bindings s.lexicalActivations.size,
              activatedContext callee ctx bindings s.nextBindingContext,
              ValEnv.shadow env (bindings.map Prod.fst)),
          { s with
            nextBindingContext := s.nextBindingContext + 1,
            lexicalActivations := s.lexicalActivations.push
              { values := (ValEnv.shadow env (bindings.map Prod.fst)).filter
                  (fun entry => (bindings.map Prod.fst).contains entry.fst)
                needs := (activatedContext callee ctx bindings s.nextBindingContext).needEnv.filter
                  (fun entry => (bindings.map Prod.fst).contains entry.fst)
                bindingContext := s.nextBindingContext } }) := rfl

/-- The activated context keeps the incoming call stack under the family and starts with no head
    scope, whatever the incoming context was. -/
theorem activated_context_identity (callee : Algorithm) (ctx : EvalCtx) (bindings : NeedEnv) (fresh : Nat) :
    (activatedContext callee ctx bindings fresh).callStack = callee :: ctx.callStack
    ∧ (activatedContext callee ctx bindings fresh).headScope = none
    ∧ (activatedContext callee ctx bindings fresh).bindingContext = fresh := ⟨rfl, rfl, rfl⟩

/-- INHERITED-NAME SHADOWING, cells: a bound name reads the clause's own binding, never an
    inherited cell of the same name; every other name reads exactly the incoming context. -/
theorem activated_context_lookup (callee : Algorithm) (ctx : EvalCtx) (bindings : NeedEnv) (fresh : Nat)
    (x : Ident) :
    lookupAssoc x (activatedContext callee ctx bindings fresh).needEnv
      = if x ∈ bindings.map Prod.fst then lookupAssoc x bindings else lookupAssoc x ctx.needEnv := by
  have hpush : (ctx.push callee).needEnv = ctx.needEnv := rfl
  simp only [activatedContext, hpush, lookupAssoc_append, lookupAssoc_filter_unbound]
  by_cases hc : x ∈ bindings.map Prod.fst
  · obtain ⟨v, hv⟩ := lookupAssoc_of_key x bindings (by simpa using hc)
    simp [hv, hc]
  · rw [lookupAssoc_of_not_key x bindings (by simpa using hc)]

/-- INHERITED-NAME SHADOWING, values: a bound name has no inherited value; every other name keeps
    its incoming value. -/
theorem activated_values_lookup (env : ValEnv) (names : List Ident) (x : Ident) :
    lookupAssoc x (ValEnv.shadow env names) = if x ∈ names then none else lookupAssoc x env :=
  lookupAssoc_filter_unbound x names env

/-- THE RECORDED ACTIVATION holds exactly the clause's bindings — every bound cell, none of the
    inherited ones — and no value entries (Model-C parameters live in the cell tier), whatever
    the incoming context and values were. -/
theorem activation_record (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (bindings : NeedEnv)
    (fresh : Nat) :
    (activatedContext callee ctx bindings fresh).needEnv.filter
        (fun entry => (bindings.map Prod.fst).contains entry.fst) = bindings
    ∧ (ValEnv.shadow env (bindings.map Prod.fst)).filter
        (fun entry => (bindings.map Prod.fst).contains entry.fst) = [] := by
  constructor
  · simp only [activatedContext, List.filter_append]
    have hkeep : bindings.filter (fun entry => (bindings.map Prod.fst).contains entry.fst) = bindings := by
      rw [List.filter_eq_self]
      intro entry hentry
      simpa using ⟨entry.snd, by simpa using hentry⟩
    have hdrop : ((ctx.push callee).needEnv.filter
          (fun entry => !(bindings.map Prod.fst).contains entry.fst)).filter
          (fun entry => (bindings.map Prod.fst).contains entry.fst) = [] := by
      rw [List.filter_filter, List.filter_eq_nil_iff]
      intro entry _
      simp
    rw [hkeep, hdrop, List.append_nil]
  · simp only [ValEnv.shadow, List.filter_filter, List.filter_eq_nil_iff]
    intro entry _
    simp

/-! ## Composition: the production dispatcher, end to end, for arbitrary contexts -/

/-- THE PRODUCTION DISPATCHER (FORMAL-07's `selectNeedFamilyBranch`, NEED-04, PAT-10/11), for
    EVERY channel pair, family, supply, incoming context, value environment and state: past the
    duplicate check (the count check is then passed, `attempt_past_its_gate`), when the clauses
    `before` the clause `branch` were non-matches in
    written order on the same cells (their effects retained in `s'`) and `branch` matches with
    `bindings` leaving `s''`, dispatch returns exactly the activation of `branch` — its wired
    body, its context and its values — over that state. -/
theorem production_dispatch_activates_the_first_match (c : NeedChannels) (callee : Algorithm)
    (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (before after : List CondBranch) (branch : CondBranch) (s s' s'' : EvalState) (bindings : NeedEnv)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hbranches : Algorithm.branches callee = before ++ branch :: after)
    (hrej : RejectedInOrder c.capabilities cells before s s')
    (hmatch : runEval (bindNeedPatterns c (needClauseHead branch.pattern) cells true) s'
      = (.ok (some bindings), s'')) :
    runEval (selectNeedFamilyBranch c callee cells ctx env name) s
      = (.ok (activatedBody callee branch bindings s''.lexicalActivations.size,
              activatedContext callee ctx bindings s''.nextBindingContext,
              ValEnv.shadow env (bindings.map Prod.fst)),
          { s'' with
            nextBindingContext := s''.nextBindingContext + 1,
            lexicalActivations := s''.lexicalActivations.push
              { values := (ValEnv.shadow env (bindings.map Prod.fst)).filter
                  (fun entry => (bindings.map Prod.fst).contains entry.fst)
                needs := (activatedContext callee ctx bindings s''.nextBindingContext).needEnv.filter
                  (fun entry => (bindings.map Prod.fst).contains entry.fst)
                bindingContext := s''.nextBindingContext } }) := by
  have hsome : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = true := by
    rw [List.any_eq_true]
    exact ⟨branch, by simp [hbranches],
      attempt_past_its_gate c.capabilities cells _ s' s'' _ hmatch (by simp)⟩
  rw [BinderCore.production_dispatcher_is_the_core, select_is_the_search _ _ _ _ _ _ hdup hsome,
    hbranches, choose_selects_the_first_match _ _ _ _ before after branch s s' s'' bindings hrej hmatch,
    activation_run]

/-- THE PRODUCTION DISPATCHER, abort: past the duplicate check (the count check is then passed),
    when an attempt after non-matches RAISES, dispatch fails with
    that error in the state it left — no later clause, no activation. -/
theorem production_dispatch_aborts_on_a_raised_failure (c : NeedChannels) (callee : Algorithm)
    (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (before after : List CondBranch) (branch : CondBranch) (s s' t : EvalState) (e : Error)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hbranches : Algorithm.branches callee = before ++ branch :: after)
    (hrej : RejectedInOrder c.capabilities cells before s s')
    (hfail : runEval (bindNeedPatterns c (needClauseHead branch.pattern) cells true) s' = (.error e, t)) :
    runEval (selectNeedFamilyBranch c callee cells ctx env name) s = (.error e, t) := by
  have hsome : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = true := by
    rw [List.any_eq_true]
    exact ⟨branch, by simp [hbranches],
      attempt_past_its_gate c.capabilities cells _ s' t _ hfail (by simp)⟩
  rw [BinderCore.production_dispatcher_is_the_core, select_is_the_search _ _ _ _ _ _ hdup hsome,
    hbranches, choose_aborts_on_a_raised_failure _ _ _ _ before after branch s s' t e hrej hfail]

/-- THE PRODUCTION DISPATCHER, exhaustion: past the checks, when every clause was a non-match,
    dispatch is `noMatchingBranch` in the state the last attempt left. -/
theorem production_dispatch_reports_no_matching_branch (c : NeedChannels) (callee : Algorithm)
    (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (name : String) (s s' : EvalState)
    (hdup : callee.hasDuplicateBranchPatterns = false)
    (hsome : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = true)
    (hrej : RejectedInOrder c.capabilities cells (Algorithm.branches callee) s s') :
    runEval (selectNeedFamilyBranch c callee cells ctx env name) s
      = (.error (Error.noMatchingBranch name), s') := by
  rw [BinderCore.production_dispatcher_is_the_core, select_is_the_search _ _ _ _ _ _ hdup hsome,
    choose_reports_no_matching_branch _ _ _ _ _ s s' hrej]

/-! ## Trace -/

/-- An activation run in the trace interpretation: lifted, so it records no event. -/
def tracedActivation {β : Type} (activate : CondBranch → NeedEnv → EvalM β) :
    CondBranch → NeedEnv → TraceM β :=
  fun branch bindings => liftEval (activate branch bindings)

/-- THE EVENT SCHEDULE OF A CLAUSE SEARCH: each attempted clause's binder events over the SAME
    cells, in written order, the next attempt only after a non-match; the activation adds none. -/
def chooseEvents (k : NeedCapabilities EvalM) (cells : List Nat) :
    List CondBranch → EvalState → List NeedEvent
  | [], _ => []
  | branch :: rest, s =>
    patternsEvents k (needClauseHead branch.pattern) cells true s ++
      match runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s with
      | (.ok none, s1) => chooseEvents k cells rest s1
      | _ => []

/-- The schedule of a whole dispatch: nothing before a failed duplicate or count check. -/
def familyEvents (k : NeedCapabilities EvalM) (callee : Algorithm) (cells : List Nat)
    (s : EvalState) : List NeedEvent :=
  if callee.hasDuplicateBranchPatterns = true then []
  else if (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = true then
    chooseEvents k cells (Algorithm.branches callee) s
  else []

theorem traced_choose {β : Type} (k : NeedCapabilities EvalM) (cells : List Nat) (name : String)
    (activate : CondBranch → NeedEnv → EvalM β) (branches : List CondBranch) :
    TracesAs (NeedBinder.chooseBranch (traced k) cells name (tracedActivation activate) branches)
      (NeedBinder.chooseBranch k cells name activate branches) (chooseEvents k cells branches) := by
  induction branches with
  | nil => intro s tr; simp [NeedBinder.chooseBranch, chooseEvents]
  | cons branch rest ih =>
    intro s tr
    simp only [NeedBinder.chooseBranch, runTrace_bind, runEval_bind, chooseEvents]
    rw [traced_patterns k (needClauseHead branch.pattern) cells true s tr]
    rcases runEval (NeedBinder.bindPatterns k (needClauseHead branch.pattern) cells true) s
      with ⟨_ | (_ | bindings), s1⟩
    · simp
    · simp only [thenRun_ok]
      rw [ih s1]
      simp
    · simp [tracedActivation]

/-- THE TRACE THEOREM FOR DISPATCH: for every production capability record, family, supply,
    name, activation, semantic state and event prefix, the traced dispatcher returns exactly the
    production dispatcher's outcome and final state, keeps the prefix, and appends exactly
    `familyEvents` — every attempt's binder events, in written order, and nothing else. -/
theorem traced_family {β : Type} (k : NeedCapabilities EvalM) (callee : Algorithm) (cells : List Nat)
    (name : String) (activate : CondBranch → NeedEnv → EvalM β) :
    TracesAs (NeedBinder.selectFamily (traced k) callee cells name (tracedActivation activate))
      (NeedBinder.selectFamily k callee cells name activate) (familyEvents k callee cells) := by
  intro s tr
  cases hdup : callee.hasDuplicateBranchPatterns
  · cases hsome : (Algorithm.branches callee).any
        (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length)
    · simp [NeedBinder.selectFamily, familyEvents, hdup, hsome]
    · simp only [NeedBinder.selectFamily, familyEvents, hdup, hsome, Bool.false_eq_true, ↓reduceIte,
        Bool.not_true]
      exact traced_choose k cells name activate (Algorithm.branches callee) s tr
  · simp [NeedBinder.selectFamily, familyEvents, hdup]

/-- TRACE ERASURE FOR THE PRODUCTION DISPATCHER, arbitrary incoming context and values. -/
theorem trace_erasure_dispatch (c : NeedChannels) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (s : EvalState) (tr : List NeedEvent) :
    eraseTrace (NeedBinder.selectFamily (traced c.capabilities) callee cells name
        (tracedActivation (needActivateBranch callee ctx env))) s tr
      = runEval (selectNeedFamilyBranch c callee cells ctx env name) s := by
  simp [eraseTrace, traced_family c.capabilities callee cells name (needActivateBranch callee ctx env) s tr,
    BinderCore.production_dispatcher_is_the_core]

end KatLang.FamilyDispatch
