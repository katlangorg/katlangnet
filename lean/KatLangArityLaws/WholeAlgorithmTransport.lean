import Lean
import KatLangArityLaws.PropertyInvocationLaws
import KatLangArityLaws.RuntimeAlias

open KatLang KatLang.EvaluatorCore

/-!
# M4★ whole-algorithm transport (ALIAS-UNIFY-1, October 2026)

The laws of the two alias kinds the surface pass forms (`Algorithm.alias … reference`): a
TRANSPARENT REFERENCE `A = R` (`reference = true`) and a STRUCTURAL FORWARDING CARRIER `A = { R }`
(`reference = false`). Every statement is about the evaluator's OWN definitions: the bodies
(`EvalBody.*`) quantified over the recursive answer `rec` — the production installs
`evalUnbounded` there (`evalStep`; a completed production outcome IS its body over production,
`production_unfolds`) — or the production operations themselves (`evalUnbounded`, through the R7
bridge `production_completes_iff`).

* **§1 Normalization and identity** (statement 1). Three chases over ONE definition
  (`EvalBody.resolveAliasChase`): STRUCTURE stops at a carrier (`chase_stops_at_carrier`), a
  non-alias ends every chase as itself (`chase_of_non_alias`), and a chase that follows carriers
  never ends at an alias (`evalFuel_follow_chase_ends`, by fuel induction over the production core).
  Production: the STRUCTURE of a carrier is the carrier from every state, nothing evaluated
  (`production_structure_of_carrier`), while every INVOCATION target is a non-alias
  (`production_invocation_target_is_no_alias`) — invocation normalization cannot erase the
  structural surface, since the two are different operations. A static name step is the raw
  ownership-first lookup in the alias's OWN scope (`static_name_step_is_the_raw_lookup`): the target
  keeps its own declaration and declaring context.
* **§2 Structure-first inertness** (statement 2). A carrier's members are its own `properties`,
  decided without its target (`carrier_members_ignore_the_target`); an own-member hit on a navigated
  carrier ends with exactly the navigation's state (`own_member_hit_never_resolves_the_target`).
  Runtime-reference establishment is distinguished: a chase that projects nothing stops AT a runtime
  alias before its binding cell is projected (`nonprojecting_chase_stops_at_runtime`), and a
  non-runtime row is classified with nothing evaluated (`static_row_is_no_runtime_step`).
* **§3 Forwarding** (statement 3). A call through either kind dispatches its INVOCATION target over
  the very same written arguments or formed supply cells, origin and callee name
  (`forwarding_passes_the_written_arguments`, `forwarding_passes_the_supplied_cells`); callbacks and
  loop steps through an alias are the target's own callback and step routes. ELABORATION PREMISE:
  that an open body whose one row is a resolved reference becomes an alias at ANY target arity is
  the C# front end's classification (`ImplicitArgumentResolver.TryCompleteLoneCalleeRow`), which Lean
  does not model; outside it a raw host-built `User` keeps its ordinary meaning
  (`raw_user_is_no_alias`, guard-checked in `WholeAlgorithmTransportGuards.lean`).
* **§4 VALUE and publication** (statement 4). The production VALUE terminal of every read is a
  NON-alias binding (`production_value_terminal_is_no_alias`), so no alias ever keys a zero-argument
  entry (OD-E); an alias's publication origin is its static chain's terminal binding
  (`alias_origin_is_the_value_terminal`), a non-alias binding is its own
  (`publication_binding_of_non_alias`); a callback or loop step through an alias never reaches the
  origin-bearing dispatch. Success-only outermost publication and non-replacement are the ONE
  publication law's (`PropertyInvocationLaws.owner_success_publishes`,
  `owner_failure_publishes_nothing`, `invocation_with_entry_is_fresh`), applied to the target's key.
* **§12 META and static open.** A captured call's structural callee is read through STRUCTURE, its
  invocation through INVOCATION (`capturedCallee` projects; `algorithmOfValue` calls the ordinary
  dispatch); static open is stratified — a carrier and a runtime reference are their own namespaces
  (`carrier_is_its_own_open_namespace`, `runtime_reference_opens_itself`) and a reference opens its
  target found by direct lookup only (`resolveOpen_opens_the_target_structure`, in
  `KatLangArityLaws.lean`), deduplicated by provider identity.
* **§13 Production bridge.** The `production_*` theorems are about `evalUnbounded` itself.

Not claimed: elaboration (Lean models none), C# concurrency, async routing, cancellation and
terminality, and whole-run refinement beyond the Q-37 step laws.
-/

namespace KatLang.WholeAlgorithmTransport

/-- Whether an algorithm is an alias, of either kind. -/
def isAlias : Algorithm → Bool
  | .alias _ _ _ _ _ _ => true
  | _ => false

/-- Wiring keeps the constructor: a wired alias is an alias, a wired non-alias is not. -/
theorem isAlias_withParent (p : Option ScopeCtx) (a : Algorithm) : isAlias (a.withParent p) = isAlias a := by
  cases a with
  | mk _ _ _ _ _ id => cases id with
    | none => rfl
    | some i => cases i <;> rfl
  | builtin => rfl
  | conditional => rfl
  | alias _ _ _ _ id _ => cases id with
    | none => rfl
    | some i => cases i <;> rfl

/-- The value view of any algorithm is no alias. -/
theorem isAlias_aliasPropertyView (a : Algorithm) : isAlias a.aliasPropertyView = false := by
  cases a <;> rfl

/-- A completed normalized run is the underlying run. -/
theorem normalize_ok {α : Type} {m : EvalM α} {s t : EvalState} {r : α}
    (h : m.normalizeIncomplete.runState s = (.ok r, t)) : m.runState s = (.ok r, t) := by
  by_cases hc : (m.runState s).1 = .error .fuelExhausted
  · rw [normalize_of_incomplete m s hc] at h; cases h
  · rw [normalize_of_complete m s hc] at h; exact h

/-- A successful production run is the run of the core at some fuel. -/
theorem fuel_of_production {c : EvalCall} {s t : EvalState} {r : c.Ret}
    (h : (evalUnbounded c).runState s = (.ok r, t)) : ∃ m, (evalFuel m c).runState s = (.ok r, t) := by
  obtain ⟨m, hm, _⟩ := (production_completes_iff c s (.ok r, t)).1
    ⟨h, by unfold ProductionCompletes; rw [h]; intro h'; cases h'⟩
  exact ⟨m, hm⟩

/-- A run of the core at some fuel with a completed outcome is the production run. -/
theorem production_of_fuel {c : EvalCall} {s : EvalState} (m : Nat) {r : Except Error c.Ret × EvalState}
    (h : (evalFuel m c).runState s = r) (hr : r.1 ≠ .error .fuelExhausted) :
    (evalUnbounded c).runState s = r := by
  have hc : Completes (evalFuel m c) s := (evalFuel_completes_iff m c s).2 (by rw [h]; exact hr)
  exact ((production_completes_iff c s r).2 ⟨m, h, hc⟩).1

/-! ## §1 — reference normalization and identity -/

/-- **The STRUCTURE chase stops at a carrier.** With `followCarriers = false` a structural carrier is
the chase's end — its own identity, with the binding of the chase's last static hop — whatever its
target and whatever the recursive answer, and nothing is evaluated: the state is untouched. -/
theorem chase_stops_at_carrier (rec : EvalRec) (projectRuntime : Bool) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (ctx : EvalCtx)
    (visited : List String) (last : Option (Algorithm × PropDef)) (s : EvalState) :
    (EvalBody.resolveAliasChase rec false projectRuntime (.alias p op pr target id false) ctx visited last).runState s
      = (.ok (.identity (.alias p op pr target id false) last), s) := rfl

/-- **A non-alias ends every chase as itself**, with the state untouched. -/
theorem chase_of_non_alias (rec : EvalRec) (followCarriers projectRuntime : Bool) (a : Algorithm)
    (h : isAlias a = false) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef))
    (s : EvalState) :
    (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last).runState s
      = (.ok (.identity a last), s) := by
  cases a with
  | alias => cases h
  | mk => rfl
  | builtin => rfl
  | conditional => rfl

/-- The end of a chase that follows carriers: never an alias identity. -/
def EndsBeyondAliases : AliasChaseEnd → Prop
  | .identity a _ => isAlias a = false
  | _ => True

/-- **A chase that follows carriers never ends at an alias** — at every fuel of the production core,
whether or not it projects runtime steps: a reference and a carrier alike are followed to a
non-alias, a value-only runtime reference ends as `valueView`, and a non-projecting chase ends AT the
first runtime alias (`runtime`). -/
theorem evalFuel_follow_chase_ends :
    ∀ (n : Nat) (projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String)
      (last : Option (Algorithm × PropDef)) (s t : EvalState) (r : AliasChaseEnd),
      (evalFuel n (.resolveAliasChase true projectRuntime a ctx visited last)).runState s = (.ok r, t) →
      EndsBeyondAliases r := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; cases h
  | succ k ih =>
    intro projectRuntime a ctx visited last s t r h
    have h' := normalize_ok h
    change (EvalBody.resolveAliasChase (evalFuel k) true projectRuntime a ctx visited last).runState s
      = (.ok r, t) at h'
    cases a with
    | mk => cases h'; rfl
    | builtin => cases h'; rfl
    | conditional => cases h'; rfl
    | alias p op pr target id reference =>
      simp only [EvalBody.resolveAliasChase, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        if_false] at h'
      split at h'
      · cases h'
      · rw [EvalM.bind_runState] at h'
        split at h'
        · rename_i b s1 _
          cases b with
          | true =>
            simp only [if_true] at h'
            cases projectRuntime with
            | false => cases h'; trivial
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, if_false] at h'
              rw [EvalM.bind_runState] at h'
              split at h'
              · rename_i step s2 _
                cases step with
                | terminal => cases h'; trivial
                | «continue» identity => exact ih true identity ctx _ none s2 t r h'
              · cases h'
          | false =>
            simp only [Bool.false_eq_true, if_false] at h'
            rw [EvalM.bind_runState] at h'
            split at h'
            · rename_i next s2 _
              exact ih projectRuntime next.alg ctx _ _ s2 t r h'
            · cases h'
        · cases h'

/-- **Production: a chase that follows carriers never ends at an alias.** -/
theorem production_follow_chase_ends (projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx)
    (visited : List String) (last : Option (Algorithm × PropDef)) (s t : EvalState) (r : AliasChaseEnd)
    (h : (resolveAliasChase true projectRuntime a ctx visited last).runState s = (.ok r, t)) :
    EndsBeyondAliases r := by
  obtain ⟨m, hm⟩ := fuel_of_production (c := .resolveAliasChase true projectRuntime a ctx visited last) h
  exact evalFuel_follow_chase_ends m projectRuntime a ctx visited last s t r hm

/-- The core's STRUCTURE chase of a carrier, at fuel one. -/
theorem fuel_chase_stops_at_carrier (projectRuntime : Bool) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (ctx : EvalCtx)
    (visited : List String) (last : Option (Algorithm × PropDef)) (s : EvalState) :
    (evalFuel 1 (.resolveAliasChase false projectRuntime (.alias p op pr target id false) ctx visited last)).runState s
      = (.ok (.identity (.alias p op pr target id false) last), s) := rfl

/-- **Production: the STRUCTURE chase of a carrier is the carrier**, from every state, untouched. -/
theorem production_chase_stops_at_carrier (projectRuntime : Bool) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (ctx : EvalCtx)
    (visited : List String) (last : Option (Algorithm × PropDef)) (s : EvalState) :
    (resolveAliasChase false projectRuntime (.alias p op pr target id false) ctx visited last).runState s
      = (.ok (.identity (.alias p op pr target id false) last), s) :=
  production_of_fuel 1 (fuel_chase_stops_at_carrier projectRuntime p op pr target id ctx visited last s)
    (by intro h; cases h)

/-- The core's STRUCTURE of a carrier, at fuel two. -/
theorem fuel_structure_of_carrier (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (ctx : EvalCtx) (s : EvalState) :
    (evalFuel 2 (.resolveAliasStructure (.alias p op pr target id false) ctx)).runState s
      = (.ok (some (.alias p op pr target id false)), s) := rfl

/-- **Production: the STRUCTURE of a carrier is the carrier itself** — its own declaration, members and
namespace, never its forwarding target — from every state, with the state untouched: nothing is
projected, demanded, allocated or evaluated, and its target row is never resolved. -/
theorem production_structure_of_carrier (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (ctx : EvalCtx) (s : EvalState) :
    (resolveAliasStructure (.alias p op pr target id false) ctx).runState s
      = (.ok (some (.alias p op pr target id false)), s) :=
  production_of_fuel 2 (fuel_structure_of_carrier p op pr target id ctx s) (by intro h; cases h)

/-- **Production: every INVOCATION target is a non-alias** — a reference and a carrier alike are
followed to the algorithm an explicit call invokes, and a value-only runtime reference is its value
view (`Algorithm.aliasPropertyView`, an ordinary zero-parameter body). With
`production_structure_of_carrier`: invocation normalization never substitutes for the structure. -/
theorem production_invocation_target_is_no_alias (a : Algorithm) (ctx : EvalCtx) (s t : EvalState)
    (target : Algorithm) (h : (resolveAliasTarget a ctx).runState s = (.ok target, t)) :
    isAlias target = false := by
  obtain ⟨m, hm⟩ := fuel_of_production (c := .resolveAliasTarget a ctx) h
  cases m with
  | zero => cases hm
  | succ k =>
    have h' := normalize_ok hm
    change (EvalBody.resolveAliasTarget (evalFuel k) a ctx).runState s = (.ok target, t) at h'
    simp only [EvalBody.resolveAliasTarget, EvalM.bind_runState] at h'
    split at h'
    · rename_i r s1 hr
      have hends := evalFuel_follow_chase_ends k true a ctx [] none s s1 r hr
      cases r with
      | identity x last => cases h'; exact hends
      | valueView alias => cases h'; exact isAlias_aliasPropertyView alias
      | runtime alias => cases h'; exact isAlias_aliasPropertyView alias
    · cases h'

/-- **A static name step is the raw ownership-first lookup in the alias's OWN scope** — the alias
pushed as the head, exactly where its body would be evaluated, so the selected target keeps its own
declaration, owner and declaring context (the lookup wires it to its owner), and a target that is
itself an alias is returned RAW for the chase to continue. Nothing here reads the target's arity. -/
theorem static_name_step_is_the_raw_lookup (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (step : Algorithm) (n : Ident) (ctx : EvalCtx) :
    resolveAliasStepWith structureOf step (.resolve n) ctx = lookupLexicalPropertyRaw step n (ctx.push step) := by
  simp only [resolveAliasStepWith, Expr.staticAliasPath?, aliasStepNavigateWith, EvalM.pure_bind]
  exact EvalM.bind_pure' _

/-! ## §2 — structure-first inertness -/

/-- **A carrier's members are its own declarations**, decided without its target: every member
lookup on an alias reads its own `properties` only (a carrier inherits nothing from its forwarding
target; a reference's own declarations never form a surface, since every structural reader takes
its STRUCTURE first). -/
theorem alias_member_lookup_is_its_own_declarations (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (name : Ident) :
    (Algorithm.alias p op pr target id reference).lookupPropDefAny? name = KatLang.lookupPropDefAny? pr name :=
  rfl

theorem carrier_members_ignore_the_target (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (target target' : Expr) (id : Option PropertyIdentity) (name : Ident) :
    (Algorithm.alias p op pr target id false).lookupPropDefAny? name
      = (Algorithm.alias p op pr target' id false).lookupPropDefAny? name := rfl

/-- **An own-member hit never resolves the forwarding target** (the production body of the dot-path
projection, over any recursive answer): once the receiver navigates to an algorithm `c` whose
STRUCTURE is `c` itself — production: every carrier (`production_structure_of_carrier`) — and `c`
declares an accessible member, the selected member is `c`'s own, and the run ends with EXACTLY the
navigation's state: the carrier's target row is never resolved, projected or evaluated. -/
theorem own_member_hit_never_resolves_the_target (rec : EvalRec) (receiver : Expr) (name : Ident)
    (fb : Expr) (ctx : EvalCtx) (c : Algorithm) (prop : PropDef) (s s' : EvalState)
    (hrecv : (rec.projectNeedStructuralMember receiver ctx).runState s = (.ok (some c), s'))
    (hstruct : (rec.resolveAliasStructure c ctx).runState s' = (.ok (some c), s'))
    (hprop : c.lookupPropDefAny? name = some prop) (hacc : memberAccessible? ctx c prop = true) :
    (EvalBody.projectNeedStructuralMember rec (.dotMember receiver name fb none) ctx).runState s
      = (.ok (some (childOfInContext c prop.alg ctx)), s') := by
  simp only [EvalBody.projectNeedStructuralMember, EvalM.bind_runState, hrecv, hstruct, hprop, hacc,
    Bool.not_true, Bool.false_eq_true, if_false]
  rfl

/-- **Production: an own-member hit on a navigated carrier.** Where the production projection of
`receiver.name` completes (the standard completion premise) and its receiver navigates to a carrier
declaring an accessible `name`, the projection is that own member with exactly the navigation's state. -/
theorem production_own_member_hit (receiver : Expr) (name : Ident) (fb : Expr) (ctx : EvalCtx)
    (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity)
    (prop : PropDef) (s s' : EvalState)
    (hcomp : ProductionCompletes (projectNeedStructuralMember (.dotMember receiver name fb none) ctx) s)
    (hrecv : (projectNeedStructuralMember receiver ctx).runState s
      = (.ok (some (.alias p op pr target id false)), s'))
    (hprop : KatLang.lookupPropDefAny? pr name = some prop)
    (hacc : memberAccessible? ctx (.alias p op pr target id false) prop = true) :
    (projectNeedStructuralMember (.dotMember receiver name fb none) ctx).runState s
      = (.ok (some (childOfInContext (.alias p op pr target id false) prop.alg ctx)), s') := by
  show (evalUnbounded (.projectNeedStructuralMember (.dotMember receiver name fb none) ctx)).runState s = _
  rw [← production_unfolds _ s hcomp]
  exact own_member_hit_never_resolves_the_target evalUnbounded receiver name fb ctx _ prop s s' hrecv
    (production_structure_of_carrier p op pr target id ctx s') hprop hacc

/-- **A non-runtime row is classified with nothing evaluated**: a static path is no runtime step. -/
theorem static_row_is_no_runtime_step (rec : EvalRec) (step : Algorithm) (target : Expr) (ctx : EvalCtx)
    (visited : List String) (s : EvalState) (h : target.isRuntimeAliasRow = false) :
    (EvalBody.aliasStepIsRuntime rec step target ctx visited).runState s = (.ok false, s) := by
  simp only [EvalBody.aliasStepIsRuntime, h, Bool.not_false, if_true]
  rfl

/-- **Runtime-reference establishment is distinguished**: a chase that projects nothing (the VALUE
chase and the static-only structure chase) stops AT the first runtime alias — after its runtime
test, before its binding cell is established or projected — so only the projecting chases
(STRUCTURE and INVOCATION) reach `runtimeAliasStepWith`, whose receiver/route demands are the runtime
reference's legitimate establishment dependencies. -/
theorem nonprojecting_chase_stops_at_runtime (rec : EvalRec) (followCarriers : Bool) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool)
    (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) (s s1 : EvalState)
    (hfollow : (!followCarriers && !reference) = false)
    (hfresh : visited.contains (aliasChaseKey (.alias p op pr target id reference)) = false)
    (hrt : (rec.aliasStepIsRuntime (.alias p op pr target id reference) target ctx
      (aliasStructureContext followCarriers (aliasChaseKey (.alias p op pr target id reference)) visited)).runState s
        = (.ok true, s1)) :
    (EvalBody.resolveAliasChase rec followCarriers false (.alias p op pr target id reference) ctx visited last).runState s
      = (.ok (.runtime (.alias p op pr target id reference)), s1) := by
  simp only [EvalBody.resolveAliasChase, hfollow, Bool.false_eq_true, if_false, hfresh, EvalM.bind_runState,
    hrt, if_true, Bool.not_false]
  rfl

/-! ## §3 — forwarding -/

/-- **Forwarding passes the written arguments**: a call through an alias — either kind, at any target
arity — dispatches its INVOCATION target over the very same written argument bundle, callee name and
origin; the supply is formed ONCE, by the target's ordinary dispatch (no wrapper, no second formation). -/
theorem forwarding_passes_the_written_arguments (rec : EvalRec) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    EvalBody.evalResolvedCallCounted rec (.alias p op pr target id reference) args ctx env calleeName origin
      = (rec.resolveAliasTarget (.alias p op pr target id reference) ctx >>= fun t =>
          rec.evalResolvedCallCounted t args ctx env calleeName origin) := rfl

/-- **Forwarding passes the exact supplied computations**: over an already formed supply (an
invocation plan's sticky supply, a callback's cells) the alias arm passes the very same cells — the
same addresses, hence the same memoized computations — with the same origin and name. -/
theorem forwarding_passes_the_supplied_cells (rec : EvalRec) (origin : CalleeOrigin) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool)
    (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    EvalBody.evalSuppliedCallCounted rec origin (.alias p op pr target id reference) cells ctx env calleeName
      = (rec.resolveAliasTarget (.alias p op pr target id reference) ctx >>= fun t =>
          rec.evalSuppliedCallCounted origin t cells ctx env calleeName) := rfl

/-- A CALLBACK through an alias is the target's own callback invocation (no origin is attached: the
callback route never reaches the origin-bearing dispatch). -/
theorem callback_through_alias_is_the_target_callback (rec : EvalRec) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool)
    (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    EvalBody.evalResolvedCallbackCallCounted rec (.alias p op pr target id reference) args ctx env calleeName
      = (rec.resolveAliasTarget (.alias p op pr target id reference) ctx >>= fun t =>
          rec.evalResolvedCallbackCallCounted t args ctx env calleeName) := rfl

/-- A LOOP STEP through an alias is the target's own step over the same state cells (`again`), with
the loop's own receiver. -/
theorem loop_step_through_alias_is_the_target_step (rec : EvalRec) {α : Type}
    (read : Algorithm → EvalCtx → ValEnv → EvalM α) (atomic : CountedResult → EvalM α) (again : Algorithm → EvalM α)
    (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity)
    (reference : Bool) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    EvalBody.runNeedStepWith rec read atomic again (.alias p op pr target id reference) ctx env cells stepName
      = (rec.resolveAliasTarget (.alias p op pr target id reference) ctx >>= again) := rfl

/-- **The elaboration boundary**: a raw host-built `User` whose one row is a reference is NOT an alias
— every chase ends at it, so it keeps its own signature (its parameter patterns, `[]` for a
parameterless one, whose nonempty supply is the binder's cardinality failure) and its own members. -/
theorem raw_user_is_no_alias (rec : EvalRec) (followCarriers projectRuntime : Bool) (p : Option ScopeCtx)
    (ps : List ParameterPattern) (op : List Expr) (pr : List PropDef) (out : List Expr)
    (id : Option PropertyIdentity) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef))
    (s : EvalState) :
    (EvalBody.resolveAliasChase rec followCarriers projectRuntime (.mk p ps op pr out id) ctx visited last).runState s
      = (.ok (.identity (.mk p ps op pr out id) last), s)
      ∧ (Algorithm.mk p ps op pr out id).parameterPatterns = ps :=
  ⟨rfl, rfl⟩

/-! ## §4 — VALUE and publication -/

/-- Where a VALUE terminal reads: never an alias binding. -/
def TerminalBeyondAliases : AliasTerminal → Prop
  | .plain a _ => isAlias a = false
  | .binding _ _ a _ => isAlias a = false
  | .runtime _ _ => True

/-- The core's VALUE chase never ends at an alias binding, at every fuel. -/
theorem evalFuel_value_terminal_is_no_alias (n : Nat) (a : Algorithm) (ctx : EvalCtx) (s t : EvalState)
    (term : AliasTerminal) (h : (evalFuel n (.resolveAliasValueTarget a ctx)).runState s = (.ok term, t)) :
    TerminalBeyondAliases term := by
  cases n with
  | zero => cases h
  | succ k =>
    have h' := normalize_ok h
    change (EvalBody.resolveAliasValueTarget (evalFuel k) a ctx).runState s = (.ok term, t) at h'
    simp only [EvalBody.resolveAliasValueTarget, EvalM.bind_runState] at h'
    split at h'
    · rename_i r s1 hr
      have hends := evalFuel_follow_chase_ends k false a ctx [] none s s1 r hr
      -- The reference-only static chase only decides the `nested` flag.
      split at h'
      · cases r with
        | identity x last =>
          cases last with
          | none => cases h'; exact hends
          | some ob =>
            obtain ⟨owner, binding⟩ := ob
            cases h'; exact hends
        | valueView alias => cases h'; trivial
        | runtime alias => cases h'; trivial
      · cases h'
    · cases h'

/-- **Production: a VALUE terminal is never an alias** — the bare read of any algorithm reads a
non-alias binding (the terminal binding of a static chain, under ITS key, owner and activation) or a
runtime reference's binding cell, so no alias ever keys a zero-argument entry (OD-E). -/
theorem production_value_terminal_is_no_alias (a : Algorithm) (ctx : EvalCtx) (s t : EvalState)
    (term : AliasTerminal) (h : (resolveAliasValueTarget a ctx).runState s = (.ok term, t)) :
    TerminalBeyondAliases term := by
  obtain ⟨m, hm⟩ := fuel_of_production (c := .resolveAliasValueTarget a ctx) h
  exact evalFuel_value_terminal_is_no_alias m a ctx s t term hm

/-- **Production: a lexical VALUE read never keys an alias**: the binding a property read `A` reads
(its cache key's binding, `terminalAccess`) is never an alias — an alias binding is replaced by its
VALUE terminal. -/
theorem production_value_read_is_no_alias (a : Algorithm) (name : Ident) (ctx : EvalCtx) (s t : EvalState)
    (term : AliasTerminal) (h : (lookupLexicalValueProperty a name ctx).runState s = (.ok term, t)) :
    TerminalBeyondAliases term := by
  obtain ⟨m, hm⟩ := fuel_of_production (c := .lookupLexicalValueProperty a name ctx) h
  cases m with
  | zero => cases hm
  | succ k =>
    have h' := normalize_ok hm
    change (EvalBody.lookupLexicalValueProperty (evalFuel k) a name ctx).runState s = (.ok term, t) at h'
    simp only [EvalBody.lookupLexicalValueProperty, EvalM.bind_runState] at h'
    split at h'
    · rename_i resolved s1 _
      split at h'
      · exact evalFuel_value_terminal_is_no_alias k _ ctx s1 t term h'
      · rename_i hnot
        cases h'
        show isAlias resolved.alg = false
        cases hres : resolved.alg with
        | alias p op pr tg id r => exact absurd hres (hnot p op pr tg id r)
        | mk => rfl
        | builtin => rfl
        | conditional => rfl
    · cases h'

/-- **The publication origin of an alias is its VALUE terminal's binding** (R-6, over any recursive
answer): when the VALUE chase ends at a static chain's terminal binding, an explicit zero-supply call
through the alias publishes under THAT binding — never the alias's own — and the origin is read with
exactly the chase's state (nothing more is evaluated). -/
theorem alias_origin_is_the_value_terminal (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (s s' : EvalState)
    (owner : Algorithm) (binding : PropDef) (x : Algorithm) (nested : Bool)
    (h : (rec.resolveAliasValueTarget a ctx).runState s = (.ok (.binding owner binding x nested), s')) :
    (EvalBody.aliasOriginBinding? rec a ctx).runState s = (.ok (some (owner, binding)), s') := by
  simp only [EvalBody.aliasOriginBinding?, EvalM.bind_runState]
  rw [evalAttempt_runState_of_complete _ s s' _ h rfl]
  rfl

/-- A selected binding that is an alias publishes under its TARGET's origin… -/
theorem publication_binding_of_alias (rec : EvalRec) (owner : Algorithm) (binding : PropDef)
    (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity)
    (reference : Bool) (ctx : EvalCtx) :
    EvalBody.publicationBinding? rec owner binding (.alias p op pr target id reference) ctx
      = rec.aliasOriginBinding? (.alias p op pr target id reference) ctx := rfl

/-- …and a non-alias binding under its own. -/
theorem publication_binding_of_non_alias (rec : EvalRec) (owner : Algorithm) (binding : PropDef)
    (wired : Algorithm) (ctx : EvalCtx) (h : isAlias wired = false) :
    EvalBody.publicationBinding? rec owner binding wired ctx = pure (some (owner, binding)) := by
  cases wired with
  | alias => cases h
  | mk => rfl
  | builtin => rfl
  | conditional => rfl

/-- A callee with no origin names no publication binding (callbacks and loop steps carry none). -/
theorem no_origin_names_no_binding (rec : EvalRec) (ctx : EvalCtx) :
    EvalBody.originBinding? rec .none ctx = pure none := rfl

/-! ## §12 — META's structural callee and static open -/

/-- **A written carrier projects the carrier** (the CALLABLE of a supplied cell written as a name —
production: the callee cell of a captured `A(3)`, which `R.Algorithm` exposes): when the name's raw
lookup selects a carrier, the projection is the carrier itself — its own structure, never its
forwarding target — given the two production chase facts `production_chase_stops_at_carrier` and
`production_structure_of_carrier` for the recursive answers, with exactly the lookup's state. -/
theorem written_carrier_projects_the_carrier (rec : EvalRec) (n : Ident) (caller : EvalCtx)
    (owner : Algorithm) (rest : List Algorithm) (hstack : caller.callStack = owner :: rest)
    (resolved : ResolvedProperty) (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef) (target : Expr)
    (id : Option PropertyIdentity) (s s1 : EvalState)
    (hlook : (lookupLexicalPropertyRaw owner n caller).runState s = (.ok resolved, s1))
    (halg : resolved.alg = .alias p op pr target id false)
    (hchase : (rec.resolveAliasChase false false (.alias p op pr target id false) caller [] none).runState s1
      = (.ok (.identity (.alias p op pr target id false) none), s1))
    (hstruct : (rec.resolveAliasStructure (.alias p op pr target id false) caller).runState s1
      = (.ok (some (.alias p op pr target id false)), s1)) :
    (EvalBody.projectNeedWritten rec (.resolve n) caller).runState s
      = (.ok (some (.alias p op pr target id false)), s1) := by
  simp only [EvalBody.projectNeedWritten, hstack, EvalM.bind_runState]
  rw [evalAttempt_runState_of_complete _ s s1 _ hlook rfl]
  simp only [halg, EvalM.bind_runState]
  rw [evalAttempt_runState_of_complete _ s1 s1 _ hchase rfl]
  simp only [EvalM.bind_runState]
  rw [evalAttempt_runState_of_complete _ s1 s1 _ hstruct rfl]
  rfl

/-- **Static open is stratified** (OD-C): a transparent reference whose target is a static NAME opens
what DIRECT lookup finds in its own declarations and declaring chain — `lookupLexicalDirect`, never an
open — read through the same stratified structure. -/
theorem open_structure_reads_direct_lookup (fuel : Nat) (ctx : EvalCtx) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (n : Ident) (id : Option PropertyIdentity) (found : Algorithm)
    (h : lookupLexicalDirect (.alias p op pr (.resolve n) id true) n = some found) :
    openStructure (fuel + 1) ctx (.alias p op pr (.resolve n) id true) = openStructure fuel ctx found := by
  simp only [openStructure, Expr.staticAliasPath?, h, EvalM.pure_bind, openNavigateWith]

/-- …and a static name that direct lookup does not find is unresolved — an open never resolves an
open target's reference head. -/
theorem open_structure_never_consults_an_open (fuel : Nat) (ctx : EvalCtx) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (n : Ident) (id : Option PropertyIdentity) (s : EvalState)
    (h : lookupLexicalDirect (.alias p op pr (.resolve n) id true) n = none) :
    (openStructure (fuel + 1) ctx (.alias p op pr (.resolve n) id true)).runState s
      = (.error (Error.unknownName n), s) := by
  simp only [openStructure, Expr.staticAliasPath?, h, EvalM.bind_runState]
  rfl

end KatLang.WholeAlgorithmTransport
