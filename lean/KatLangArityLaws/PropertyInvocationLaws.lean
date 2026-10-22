import Lean
import KatLangArityLaws.EvaluatorCacheLaws

open KatLang KatLang.EvaluatorCore KatLang.EvaluatorCacheLaws

/-!
# CACHE-PUB-1: explicit zero-supply invocations share the property-cache publication law

Owner decision (October 22 2026): *when a property's cache is empty, its outermost qualifying
evaluation owns publication, whether initiated through a property-style read or an explicit
zero-argument invocation. Successful completion establishes the cached value. Bare reads reuse
that value. Explicit invocations remain fresh and never replace an established cached value.*

The production mechanism is ONE body, `EvalBody.evalZeroArgPropertyAccessCounted`, over a
request (`ZeroArgPropertyRequest.read` / `.invoke calleeName`): reads and invocations share the
key, the active owner set and the publication statement, and differ only in their calculation
(`EvalBody.zeroArgPropertyCalculation`) and in what an ESTABLISHED entry means. The dispatch
reaches it for a zero-supply invocation whose origin names a property binding
(`EvalBody.evalSuppliedCallCounted`, `EvalBody.originBinding?`).

The theorems below are PRODUCTION laws over those bodies at ANY evaluator answer `rec` (so at the
total core's every fuel and at the production answer), each a statement about one execution step:

* `read_with_entry_is_hit` — a read of an established entry returns it and changes nothing;
* `invocation_with_entry_is_fresh` — an invocation of an established entry is its own fresh
  calculation (never a cache hit), so it can neither return nor replace the entry;
* `reentrant_request_is_its_calculation` — a request on an ACTIVE key publishes nothing of its own;
* `owner_success_publishes` — an owning request's success is published, with exactly the counted
  result its calculation produced, and the owner set is restored;
* `owner_failure_publishes_nothing` — an owning request's completed failure adds no entry of its
  own and restores the owner set;
* `invocation_calculation_is_the_call_before_its_boundary` / `user_call_is_its_output_recounted` —
  the counted result an owning user invocation publishes is the call's own output BEFORE the call's
  value boundary, which the ordinary call then re-counts;
* `nonzero_supply_never_requests_the_cache` — a supply with at least one cell is the ordinary
  dispatch, untouched;
* `zero_supply_bound_invocation_requests_the_cache` — a zero-supply invocation whose origin names a
  binding is the cache's `invoke` request under that binding, at the call's value boundary.

Whole-run consequences come from `EvaluatorCacheLaws` unchanged in statement: every established
entry survives every completed computation (`cache_entries_survive`, now covering invocations),
and the owner set is restored on every completed run (`owner_set_restored`). NOT claimed: a
whole-evaluator equivalence theorem, key injectivity, that a re-entrant run can never publish its
own key (needs `LawfulBEq` of the key, as in `EvaluatorCacheLaws`), or any C# behaviour.
-/

namespace KatLang.PropertyInvocationLaws

/-- The key a request computes in state `s`. -/
abbrev keyAt (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) : ZeroArgPropertyCacheKey :=
  zeroArgPropertyCacheKey k owner binding ctx env (propertyOwnerBindingContext a.parent s)

/-- The state an owning request runs its calculation in: its key marked active. -/
abbrev markedAt (key : ZeroArgPropertyCacheKey) (s : EvalState) : EvalState :=
  { s with activeZeroArgProperties := key :: s.activeZeroArgProperties }

section Steps
variable (rec : EvalRec) (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
  (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)

/-- **Bare reads reuse the established value**: a cacheable read whose key holds `v` returns `v`
    and leaves the state unchanged — no calculation, no owner mark, no publication. -/
theorem read_with_entry_is_hit (v : CountedResult)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hhit : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = some v) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env .read).runState s = (.ok v, s) := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, if_true, EvalM.bind_runState, get_runState]
  rw [hhit]; rfl

/-- **Explicit invocations remain fresh**: an invocation whose key holds an established entry is
    exactly its own calculation from the same state — it never obtains its result from the entry,
    marks no owner and publishes nothing (the entry it found survives by `cache_entries_survive`). -/
theorem invocation_with_entry_is_fresh (calleeName : String) (v : CountedResult)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hhit : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = some v) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env (.invoke calleeName)).runState s =
      (EvalBody.zeroArgPropertyCalculation rec (.invoke calleeName) a ctx env).runState s := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, if_true, EvalM.bind_runState, get_runState]
  rw [hhit]

/-- **Re-entrant requests publish nothing of their own**: a request — read or invocation — on an
    empty key whose owner is still active is exactly its calculation from the same state. -/
theorem reentrant_request_is_its_calculation (request : ZeroArgPropertyRequest)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hact : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = true) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env request).runState s =
      (EvalBody.zeroArgPropertyCalculation rec request a ctx env).runState s := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, if_true, EvalM.bind_runState, get_runState]
  rw [hmiss]
  simp only [hact, if_true]

/-- **The successful outermost owner publishes once, with its calculation's counted result**: a
    request — read or invocation — on an empty, inactive key runs its calculation with the key
    marked active; when that calculation succeeds with `counted` (exit state `t`), the request
    returns `counted`, restores the owner set it found, and inserts `counted` under the key (which
    never replaces an existing entry, `lookup_insert_keep`). -/
theorem owner_success_publishes (request : ZeroArgPropertyRequest) (counted : CountedResult) (t : EvalState)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (hrun : (EvalBody.zeroArgPropertyCalculation rec request a ctx env).runState
      (markedAt (keyAt k owner binding a ctx env s) s) = (.ok counted, t)) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env request).runState s =
      (.ok counted, { t with
        activeZeroArgProperties := s.activeZeroArgProperties,
        zeroArgPropertyCache :=
          ZeroArgPropertyCache.insert t.zeroArgPropertyCache (keyAt k owner binding a ctx env s) counted }) := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, if_true, EvalM.bind_runState, get_runState]
  rw [hmiss]
  simp only [hnot, Bool.false_eq_true, if_false, EvalM.bind_runState, set_runState]
  rw [evalAttempt_runState_of_complete _ _ t (.ok counted) hrun rfl]
  rfl

/-- **A failed owner publishes nothing for its key**: when an owning request's calculation
    completes with an ordinary failure `e` (exit state `t`), the request fails with `e`, restores
    the owner set, and adds no entry: the cache is exactly the one the calculation left — entries
    OTHER keys' owners published meanwhile stay (there is no rollback). -/
theorem owner_failure_publishes_nothing (request : ZeroArgPropertyRequest) (e : Error) (t : EvalState)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (hcomplete : (Except.error e : Except Error CountedResult).isIncomplete = false)
    (hrun : (EvalBody.zeroArgPropertyCalculation rec request a ctx env).runState
      (markedAt (keyAt k owner binding a ctx env s) s) = (.error e, t)) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env request).runState s =
      (.error e, { t with activeZeroArgProperties := s.activeZeroArgProperties }) := by
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, if_true, EvalM.bind_runState, get_runState]
  rw [hmiss]
  simp only [hnot, Bool.false_eq_true, if_false, EvalM.bind_runState, set_runState]
  rw [evalAttempt_runState_of_complete _ _ t (.error e) hrun hcomplete]
  rfl

end Steps

/-! ## The counted result an invocation publishes, and where the dispatch requests it -/

/-- An invocation's calculation for a user callee (neither a clause family nor a builtin or an
    alias, which never reach it) is the ordinary user invocation BEFORE its value boundary. -/
theorem invocation_calculation_is_the_call_before_its_boundary (rec : EvalRec) (calleeName : String)
    (parent : Option ScopeCtx) (patterns : List ParameterPattern) (opens : List Expr)
    (properties : List PropDef) (output : List Expr) (declarationId : Option PropertyIdentity)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.zeroArgPropertyCalculation rec (.invoke calleeName)
        (Algorithm.mk parent patterns opens properties output declarationId) ctx env =
      EvalBody.evalNeedUserSupplyOutput rec
        (Algorithm.mk parent patterns opens properties output declarationId) [] ctx env := rfl

/-- …and the ordinary user call is that output re-counted at the call's value boundary: what the
    caller receives (`reCountValueBoundary`) and what the property's entry holds (the output's own
    emitted count) are different projections of ONE execution. -/
theorem user_call_is_its_output_recounted (rec : EvalRec) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalNeedUserSupply rec callee cells ctx env =
      (do let result ← EvalBody.evalNeedUserSupplyOutput rec callee cells ctx env
          pure (reCountValueBoundary result)) := rfl

/-- **A non-zero supply never requests the property cache**: with at least one supplied cell the
    dispatch of a user or family callee is the ordinary one, whatever the origin. -/
theorem nonzero_supply_never_requests_the_cache (rec : EvalRec) (origin : CalleeOrigin)
    (callee : Algorithm) (cell : NeedSupply.Sourced) (rest : List NeedSupply.Sourced)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
    (hb : ∀ b, callee ≠ .builtin b) (ha : ∀ p o ps t d, callee ≠ .alias p o ps t d) :
    EvalBody.evalSuppliedCallCounted rec origin callee (cell :: rest) ctx env calleeName =
      (match callee with
       | .conditional _ _ _ _ =>
         match flatBinderUserEquivalent? callee with
         | some simple => rec.evalNeedUserSupply simple ((cell :: rest).map Prod.fst) ctx env
         | none => rec.evalNeedFamilySupply callee ((cell :: rest).map Prod.fst) ctx env calleeName
       | _ => rec.evalNeedUserSupply callee ((cell :: rest).map Prod.fst) ctx env) := by
  cases callee with
  | builtin b => exact absurd rfl (hb b)
  | alias p o ps t d => exact absurd rfl (ha p o ps t d)
  | mk => simp [EvalBody.evalSuppliedCallCounted]
  | conditional => simp only [EvalBody.evalSuppliedCallCounted, List.isEmpty_cons, Bool.false_eq_true, if_false]; rfl

/-- **A zero-supply invocation whose origin names a binding is that binding's `invoke` request**:
    once the origin's binding is read (`originBinding?`, which evaluates nothing), the dispatch of a
    user or family callee over the EMPTY supply is the property cache's `invoke` request under that
    binding, at the call's value boundary. -/
theorem zero_supply_bound_invocation_requests_the_cache (rec : EvalRec) (origin : CalleeOrigin)
    (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
    (owner : Algorithm) (binding : PropDef) (s s' : EvalState)
    (hb : ∀ b, callee ≠ .builtin b) (ha : ∀ p o ps t d, callee ≠ .alias p o ps t d)
    (horigin : (EvalBody.originBinding? rec origin ctx callee).runState s = (.ok (some (owner, binding)), s')) :
    (EvalBody.evalSuppliedCallCounted rec origin callee [] ctx env calleeName).runState s =
      ((do
        let counted ← rec.evalZeroArgPropertyAccessCounted .lexical owner binding callee ctx env (.invoke calleeName)
        pure (reCountValueBoundary counted)) : EvalM CountedResult).runState s' := by
  cases callee with
  | builtin b => exact absurd rfl (hb b)
  | alias p o ps t d => exact absurd rfl (ha p o ps t d)
  | mk =>
    simp only [EvalBody.evalSuppliedCallCounted, List.isEmpty_nil, if_true, EvalM.bind_runState, horigin]
  | conditional =>
    simp only [EvalBody.evalSuppliedCallCounted, List.isEmpty_nil, if_true, EvalM.bind_runState, horigin]

end KatLang.PropertyInvocationLaws
