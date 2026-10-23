import Lean
import KatLangArityLaws.EvaluatorCacheLaws
import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.EvaluatorCore KatLang.EvaluatorCacheLaws KatLang.WhileRoundProduction

/-!
# CACHE-OWNER-D1: a property-style read inherits the declaring context

Owner decision (October 23 2026): *a parameterless algorithm entered through a qualifying
property-style read inherits the binding-context identity of its declaring activation, as resolved
in the current lexical context. An explicit call establishes a fresh binding context.*

The production mechanism is ONE definition on the read route, `EvalBody.evalPropertyDemandCounted`
(the `.read` calculation of the property cache, `EvalBody.zeroArgPropertyCalculation`): a
parameterless user owner is checked and entered exactly as an ordinary body, through
`enterPropertyOwnerBody`, which is `enterAlgorithmBody` except that the activation it records
carries the binding context `propertyOwnerBindingContext a.parent` finds — the context the owner's
OWN cache key carries — and the reader's only when there is none. Every other callable, and the
`.invoke` calculation of an explicit call, are untouched.

What is proved here, over the production definitions:

* **Equations of the owner context** (`owner_context_*`): the total `propertyOwnerBindingContext`
  returns the nearest activated level's recorded context and skips an unactivated level.
* **Lexical and structural spellings agree** (`lexical_and_structural_levels_agree`): a level
  activated by a property-demand entry and the unactivated level a structural `B.V` or an opened
  `V` rebuilds over the same parent chain select the same context.
* **Body entry** (`enterPropertyOwnerBody_run`, `enterPropertyOwnerBody_self`): the entry returns
  exactly `enterAlgorithmBody`'s context — the reader's need tier, binding context, call stack
  and head scope — and appends exactly `enterAlgorithmBody`'s activation record but for its binding
  context; inheriting the reader's own context IS `enterAlgorithmBody`.
* **The read route** (`read_calculation_is_the_property_demand`, `property_demand_run`,
  `property_demand_*_is_the_ordinary_demand`): a read's calculation is the property demand; for a
  parameterless user owner it is the checks, ONE entry recording the declaring context, and the
  rows over the entered context; every other callable is the ordinary zero-argument demand.
* **Consumer independence** (`property_demand_records_the_declaring_context`): whenever the
  declaring chain has an activated level, the recorded context is that level's, whatever the
  reader's binding context.
* **Explicit calls stay fresh**: the `.invoke` calculation is unchanged — still the ordinary user
  invocation (`PropertyInvocationLaws.invocation_calculation_is_the_call_before_its_boundary`,
  which binds a fresh context through `EvalCtx.bindParameters`).

Whole-run cache laws need no restatement: `cache_entries_survive` and `owner_set_restored`
(`EvaluatorCacheLaws`) are proved over every body, the new one included, so published entries
are never replaced and the owner set is restored. NOT claimed: a whole-evaluator equivalence
theorem, that the declaring activation found in context is the semantically intended one (a
source fact of `scopeInContext`, pinned by the CoreTests D1 guards), or any C# behaviour.
-/

namespace KatLang.PropertyOwnerContext

/-! ## 1. The owner context of a declaring chain -/

theorem owner_context_none (s : EvalState) : propertyOwnerBindingContext none s = none := by
  simp only [propertyOwnerBindingContext]

/-- An activated level whose record exists answers with that record's binding context. -/
theorem owner_context_activated (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (id : Nat)
    (decl : Option PropertyIdentity) (s : EvalState) (act : ParameterActivation)
    (h : s.lexicalActivations[id]? = some act) :
    propertyOwnerBindingContext (some (.mk parent params opens props output branches (some id) decl)) s =
      some act.bindingContext := by
  simp only [propertyOwnerBindingContext, Option.bind_some, h]

/-- An unactivated level — the rebuilt receiver of a structural `B.V`, an opened provider — is
    skipped: the answer is its parent chain's. -/
theorem owner_context_unactivated (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch)
    (decl : Option PropertyIdentity) (s : EvalState) :
    propertyOwnerBindingContext (some (.mk parent params opens props output branches none decl)) s =
      propertyOwnerBindingContext parent s := by
  simp only [propertyOwnerBindingContext, Option.bind_none]

/-- **Lexical and structural spellings agree**: a level activated with a record whose binding
    context is the one its parent chain answers (what a property-demand entry records, §3), and an
    unactivated level over the SAME parent chain, answer alike. So `V`'s key read lexically inside
    `B`'s body and its key read through a rebuilt `B` (`B.V`, an opened `V`) carry one context. -/
theorem lexical_and_structural_levels_agree (parent : Option ScopeCtx) (params params' : List Ident)
    (opens opens' : List Expr) (props props' : List PropDef) (output output' : List Expr)
    (branches branches' : List CondBranch) (id : Nat) (decl decl' : Option PropertyIdentity)
    (s : EvalState) (act : ParameterActivation) (n : Nat)
    (h : s.lexicalActivations[id]? = some act) (hparent : propertyOwnerBindingContext parent s = some n)
    (hrecorded : act.bindingContext = n) :
    propertyOwnerBindingContext (some (.mk parent params opens props output branches (some id) decl)) s =
      propertyOwnerBindingContext (some (.mk parent params' opens' props' output' branches' none decl')) s := by
  rw [owner_context_activated parent params opens props output branches id decl s act h,
    owner_context_unactivated, hparent, hrecorded]

/-! ## 2. The property-demand body entry -/

/-- **Body entry of a property-style read**: it never fails; it returns exactly the context the
    ordinary entry returns (`enteredCtx`: the reader's need tier, binding context and call stack,
    the activated head scope at the same index) and leaves the ordinary entered state for the
    context carrying the INHERITED binding context — the only difference is the record's
    `bindingContext`. -/
theorem enterPropertyOwnerBody_run (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (n : Nat) (s : EvalState) :
    (enterPropertyOwnerBody a ctx env n).runState s =
      (.ok (enteredCtx a ctx s), enteredState a { ctx with bindingContext := n } env s) := by
  unfold enterPropertyOwnerBody
  rw [EvalM.bind_runState, enter_run]
  simp only [pure_runState]
  unfold enteredCtx EvalCtx.push
  split <;> rfl

/-- The record a property-demand entry appends is the ordinary one but for its binding context. -/
theorem enteredActivation_inherited (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (n : Nat) :
    enteredActivation a { ctx with bindingContext := n } env =
      { enteredActivation a ctx env with bindingContext := n } := rfl

/-- **Inheriting the reader's own context IS the ordinary entry**: nothing else differs. -/
theorem enterPropertyOwnerBody_self (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (enterPropertyOwnerBody a ctx env ctx.bindingContext).runState s = (enterAlgorithmBody a ctx env).runState s := by
  rw [enterPropertyOwnerBody_run, enter_run]

/-! ## 3. The read route -/

/-- A read's calculation is the property demand. -/
theorem read_calculation_is_the_property_demand (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.zeroArgPropertyCalculation rec .read a ctx env = EvalBody.evalPropertyDemandCounted rec a ctx env := rfl

/-- The binding context a property-style read of `a` enters it in, in state `s`. -/
abbrev inheritedContext (a : Algorithm) (ctx : EvalCtx) (s : EvalState) : Nat :=
  (propertyOwnerBindingContext a.parent s).getD ctx.bindingContext

/-- **The property demand of a parameterless user owner**: after its checks pass (state-free), it
    is ONE entry recording the inherited context, then the rows over the entered context — the
    reader's own context shape (`enteredCtx a ctx s`) — and the prepared output's counted result. -/
theorem property_demand_run (rec : EvalRec) (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef)
    (out : List Expr) (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hp : Passes (Algorithm.mk p [] o pr out d)) :
    (EvalBody.evalPropertyDemandCounted rec (Algorithm.mk p [] o pr out d) ctx env).runState s =
      (do let prepared ← rec.evalOutputRowsPreparedCore out (enteredCtx (Algorithm.mk p [] o pr out d) ctx s) env
          pure prepared.counted).runState
        (enteredState (Algorithm.mk p [] o pr out d)
          { ctx with bindingContext := inheritedContext (Algorithm.mk p [] o pr out d) ctx s } env s) := by
  simp only [EvalBody.evalPropertyDemandCounted]
  rw [EvalM.bind_runState, hp s]
  simp only
  rw [EvalM.bind_runState, get_runState]
  simp only
  rw [EvalM.bind_runState, enterPropertyOwnerBody_run]
  rfl

/-- **Consumer independence**: when the declaring chain has an activated level with context `m`,
    the activation a property-style read records carries `m` — whatever the reader's binding
    context. Two consumers (a callback and the owner's own body, say) can therefore never split
    the owner's local-only entries. -/
theorem property_demand_records_the_declaring_context (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (m : Nat) (h : propertyOwnerBindingContext a.parent s = some m) :
    (enteredActivation a { ctx with bindingContext := inheritedContext a ctx s } env).bindingContext = m := by
  simp only [enteredActivation, inheritedContext, h, Option.getD_some]

/-- …and with no activated level (the root, an unactivated host scope) it is the reader's own:
    the existing fallback, unchanged. -/
theorem property_demand_falls_back_to_the_reader (a : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (h : propertyOwnerBindingContext a.parent s = none) :
    inheritedContext a ctx s = ctx.bindingContext := by
  simp only [inheritedContext, h, Option.getD_none]

/-- Every other callable keeps the ordinary zero-argument demand: a pattern list (whose binder
    mints a fresh context), … -/
theorem property_demand_patterned_is_the_ordinary_demand (rec : EvalRec) (p : Option ScopeCtx)
    (pattern : ParameterPattern) (patterns : List ParameterPattern) (o : List Expr) (pr : List PropDef)
    (out : List Expr) (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalPropertyDemandCounted rec (Algorithm.mk p (pattern :: patterns) o pr out d) ctx env =
      rec.evalZeroArgumentDemandOutputCounted (Algorithm.mk p (pattern :: patterns) o pr out d) ctx env := rfl

/-- … a clause family, … -/
theorem property_demand_family_is_the_ordinary_demand (rec : EvalRec) (p : Option ScopeCtx)
    (os : List Expr) (branches : List CondBranch) (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalPropertyDemandCounted rec (Algorithm.conditional p os branches d) ctx env =
      rec.evalZeroArgumentDemandOutputCounted (Algorithm.conditional p os branches d) ctx env := rfl

/-- … an alias, … -/
theorem property_demand_alias_is_the_ordinary_demand (rec : EvalRec) (p : Option ScopeCtx)
    (o : List Expr) (ps : List PropDef) (t : Expr) (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalPropertyDemandCounted rec (Algorithm.alias p o ps t d) ctx env =
      rec.evalZeroArgumentDemandOutputCounted (Algorithm.alias p o ps t d) ctx env := rfl

/-- … and a builtin. -/
theorem property_demand_builtin_is_the_ordinary_demand (rec : EvalRec) (b : Builtin) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalPropertyDemandCounted rec (Algorithm.builtin b) ctx env =
      rec.evalZeroArgumentDemandOutputCounted (Algorithm.builtin b) ctx env := rfl

end KatLang.PropertyOwnerContext
