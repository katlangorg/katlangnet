import KatLangArityLaws.NavigationRelational

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.MemberSettled
open KatLang.NavigationReread KatLang.NavigationContract KatLang.NavigationRelational

/-!
# The B2 pilot, pass 2: ONE syntax-directed procedure over the bodies (ledger E-18, step 1, B2 preparation)

`NavigationRelational.Agree K s m m' Q` is the combined judgment whose family is
`Contract.BodySound` (`bodySound_of_agree`): from the invariant state `s`, a completed run of `m`
(a body over the answer) is the run of `m'` (the same body over the answer GUARDED by the
contract), its exit state is invariant and an extension, and a success satisfies `Q`. The B2
preparation applied it BY HAND to four bodies. This module adds the PROCEDURE: `agree_tac`
symbolically executes a body over both answers at once — a bind whose head is a recursive call is
its leaf (`Agree.rec_call`, the call-site precondition left as a verification condition), any other
head is executed on its own (pure, throw, error, `<$>`, `evalAttempt`, a state-free helper), and
`match` / `if` are split — so a body's proof is `unfold` and `agree_tac`, and what remains are its
VERIFICATION CONDITIONS: the precondition at each recursive call site and a relational contract for
each state-writing or higher-order helper the body runs.

## What the pilot measures (threshold: `artifacts/.../pass2-20261113/pilot-threshold.md`)

Each theorem below is stated for EVERY contract `K` (`Ordered`), over every answer that keeps it.
Its proof is the procedure; its hypotheses beyond the call's own precondition are its verification
conditions, which a concrete contract must discharge. For the navigation contract they are NOT all
discharged here, so the pilot is PARTIAL by the threshold's items 4–5 (see the ledger row E-18).
The result contract of each body is not part of the pilot: every judgment below is stated with the
trivial result predicate, as the B2 preparation's were.
-/

namespace KatLang.NavigationPilot

/-! ## The procedure -/

/-- A pure step: the result predicate is the trivial one. -/
theorem agree_pure {K : Contract} (ho : Ordered K) {α : Type} {s : EvalState} (a : α) :
    Agree K s (Pure.pure a : EvalM α) (Pure.pure a) (fun _ _ => True) :=
  Agree.pure ho a (fun _ => trivial)

/-- A recursive call in tail position, under the trivial result predicate. -/
theorem agree_rec_tail {K : Contract} {rec : EvalRec} (hk : K.Keeps rec) {c : EvalCall} {s : EvalState}
    (hp : K.pre c s) : Agree K s (rec c) (K.guard rec c) (fun _ _ => True) :=
  Agree.conseq (Agree.rec_call hk hp) (fun _ _ _ => trivial)

/-- A state-free helper, under the trivial result predicate. -/
theorem agree_stateFree {K : Contract} (ho : Ordered K) {α : Type} {s : EvalState} {m : EvalM α}
    (hsf : StateFree m) : Agree K s m m (fun _ _ => True) :=
  Agree.conseq (Agree.stateFree ho hsf) (fun _ _ _ => trivial)

/-- A pure step as `<$>` leaves it after a bind (`pure ∘ g`), under the trivial result predicate. -/
theorem agree_comp_pure {K : Contract} (ho : Ordered K) {β γ : Type} {s : EvalState} (g : β → γ) (x : β) :
    Agree K s (Function.comp (fun a => (EvalM.mk (pure a) : EvalM γ)) g x)
      (Function.comp (fun a => (EvalM.mk (pure a) : EvalM γ)) g x) (fun _ _ => True) :=
  Agree.pure ho (g x) (fun _ => trivial)

/-- A caught computation, under the trivial result predicate. -/
theorem agree_attempt {K : Contract} {α : Type} {s : EvalState} {m m' : EvalM α}
    (hm : Agree K s m m' (fun _ _ => True)) : Agree K s (evalAttempt m) (evalAttempt m') (fun _ _ => True) :=
  Agree.conseq (Agree.attempt hm) (fun _ _ _ => trivial)

open Lean Elab Tactic Meta in
/-- Succeeds when the computation the goal `Agree K s m m' Q` judges — or the head of its bind or
    `<$>` — is a RECURSIVE CALL: an `EvalRec` accessor or the answer itself. Purely syntactic, so the
    procedure never unfolds a helper to find out. -/
elab "guard_rec_head" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``Agree do throwError "not an Agree goal"
  let m := tgt.getAppArgs[3]!
  let head :=
    if m.isAppOfArity ``Bind.bind 6 then m.getAppArgs[4]!
    else if m.isAppOfArity ``Functor.map 6 then m.getAppArgs[5]!
    else m
  match head.getAppFn with
  | .const n _ => unless (`KatLang.EvalRec).isPrefixOf n do throwError "not a recursive call"
  | .fvar _ => pure ()
  | _ => throwError "not a recursive call"

set_option hygiene false in
/-- **THE PROCEDURE.** In a context with `ho : Ordered K` and `hk : K.Keeps rec`, reduces a goal
    `Agree K s (body over rec) (body over K.guard rec) Q` to its verification conditions: the
    precondition at each recursive call, and the judgment of each helper that is neither pure,
    failing, caught, nor state-free. Every rule but the recursive-call leaf matches syntactically
    (reducible transparency), so a helper is never unfolded. -/
macro "agree_tac" : tactic => `(tactic| repeat' (first
  | with_reducible exact agree_pure ho _
  | with_reducible exact agree_comp_pure ho _ _
  | with_reducible exact Agree.throw ho _
  | with_reducible exact Agree.error ho _
  | with_reducible exact agree_stateFree ho (sf_lookupLexicalPropertyRaw _ _ _)
  | with_reducible exact agree_stateFree ho (by assumption)
  | (with_reducible refine Agree.bind ho (Agree.stateFree ho (sf_lookupLexicalPropertyRaw _ _ _)) (fun _ _ _ _ _ hsf => ?_)
     obtain ⟨rfl, _⟩ := hsf)
  | (guard_rec_head; refine Agree.bind ho (Agree.rec_call hk ?_) (fun _ _ _ _ _ _ => ?_))
  | (guard_rec_head; refine Agree.map ho _ (Agree.rec_call hk ?_) (fun _ _ _ => trivial))
  | (guard_rec_head; refine agree_rec_tail hk ?_)
  | (with_reducible refine Agree.bind ho (P := fun _ _ => True) ?_ (fun _ _ _ _ _ _ => ?_))
  | (with_reducible refine agree_attempt ?_)
  | (dsimp (config := { proj := false }) only)
  | split))

/-! ## The pilot bodies -/

section Bodies
variable {K : Contract} (ho : Ordered K) {rec : EvalRec} (hk : K.Keeps rec)
include ho hk

/-- STRUCTURAL: the structure chase. VC: the chase's precondition at the entry state. -/
theorem pilot_resolveAliasStructure (a : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (vc : K.pre (.resolveAliasChase false true a ctx [] none) s) :
    Agree K s (evalStep rec (.resolveAliasStructure a ctx)) (evalStep (K.guard rec) (.resolveAliasStructure a ctx))
      (fun _ _ => True) := by
  show Agree K s (EvalBody.resolveAliasStructure rec a ctx) (EvalBody.resolveAliasStructure (K.guard rec) a ctx) _
  unfold EvalBody.resolveAliasStructure
  agree_tac
  all_goals assumption

/-- STRUCTURAL + MEMBER NAVIGATION + LEXICAL NAME HEAD: the receiver probe, every arm. VCs: the
    precondition of each recursive call it makes, at each state it can make it from. -/
theorem pilot_resolveDotReceiver (e : Expr) (ctx : EvalCtx) (s : EvalState)
    (vcProbe : ∀ o, K.pre (.resolveDotReceiver? o ctx) s)
    (vcMember : ∀ (a : Algorithm) (p : PropDef) t, K.inv t →
      K.pre (.resolveAliasStructure (childOfInContext a p.alg ctx) ctx) t)
    (vcMiss : ∀ t, K.inv t → K.pre (.resolveAlg e ctx) t)
    (vcHead : ∀ (a : Algorithm), K.pre (.resolveAliasStructure a ctx) s)
    (vcParam : ∀ x, K.pre (.projectParameterCallable x ctx) s)
    (vcValue : K.pre (.resolveAlg e ctx) s) :
    Agree K s (evalStep rec (.resolveDotReceiver? e ctx)) (evalStep (K.guard rec) (.resolveDotReceiver? e ctx))
      (fun _ _ => True) := by
  show Agree K s (EvalBody.resolveDotReceiver? rec e ctx) (EvalBody.resolveDotReceiver? (K.guard rec) e ctx) _
  unfold EvalBody.resolveDotReceiver?
  agree_tac
  all_goals first | assumption | solve_by_elim

/-- STRUCTURAL: the structural projection of a written source, every arm. -/
theorem pilot_projectNeedStructuralMember (source : Expr) (ctx : EvalCtx) (s : EvalState)
    (vcReceiver : ∀ r, K.pre (.projectNeedStructuralMember r ctx) s)
    (vcChase : ∀ (a : Algorithm) t, K.inv t → K.pre (.resolveAliasStructure a ctx) t)
    (vcParam : ∀ x, K.pre (.projectParameterCallable x ctx) s) :
    Agree K s (evalStep rec (.projectNeedStructuralMember source ctx))
      (evalStep (K.guard rec) (.projectNeedStructuralMember source ctx)) (fun _ _ => True) := by
  show Agree K s (EvalBody.projectNeedStructuralMember rec source ctx)
    (EvalBody.projectNeedStructuralMember (K.guard rec) source ctx) _
  unfold EvalBody.projectNeedStructuralMember
  agree_tac
  all_goals first | assumption | solve_by_elim

/-- LEXICAL LOOKUP (with `open` resolution, inside the state-free `lookupLexicalPropertyRaw`). -/
theorem pilot_lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx) (s : EvalState)
    (vcTarget : ∀ (b : Algorithm), K.pre (.resolveAliasTarget b ctx) s) :
    Agree K s (evalStep rec (.lookupLexicalProperty a name ctx))
      (evalStep (K.guard rec) (.lookupLexicalProperty a name ctx)) (fun _ _ => True) := by
  show Agree K s (EvalBody.lookupLexicalProperty rec a name ctx) (EvalBody.lookupLexicalProperty (K.guard rec) a name ctx) _
  unfold EvalBody.lookupLexicalProperty
  agree_tac
  all_goals first | assumption | solve_by_elim

/-- The static-step structure callback of `resolveAliasChase`, over an answer. -/
def chaseStructure (r : EvalRec) (fc : Bool) (key : String) (visited : List String) :
    Algorithm → EvalCtx → EvalM (Option Algorithm) := fun receiver stepCtx => do
  match <- r.resolveAliasChase false false receiver stepCtx (aliasStructureContext fc key visited) none with
  | .identity found _ => pure (some found)
  | _ => pure none

set_option maxHeartbeats 2000000 in
/-- STRUCTURAL: the alias chase, at an alias (the other arm is `pure`). VCs: the preconditions of its
    recursive calls, and two relational HELPER contracts — the binding cell's allocation
    (`aliasBindingCell`, a state writer) and the static step over the two answers' structure
    callbacks (`resolveAliasStepWith`, a higher-order helper). -/
theorem pilot_resolveAliasChase (fc pr : Bool) (parent : Option ScopeCtx) (opens : List Expr)
    (props : List PropDef) (target : Expr) (id : Option PropertyIdentity) (reference : Bool)
    (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) (s : EvalState)
    (vcRuntime : ∀ step vis, K.pre (.aliasStepIsRuntime step target ctx vis) s)
    (vcCell : ∀ (w : Algorithm) t, Agree K t (aliasBindingCell w target ctx) (aliasBindingCell w target ctx)
      (fun _ _ => True))
    (vcProject : ∀ addr t, K.inv t → K.pre (.projectNeedCallable addr) t)
    (vcNext : ∀ (b : Algorithm) vis' last' t, K.inv t → K.pre (.resolveAliasChase fc pr b ctx vis' last') t)
    (vcStep : ∀ (w : Algorithm) key t, Agree K t (resolveAliasStepWith (chaseStructure rec fc key visited) w target ctx)
      (resolveAliasStepWith (chaseStructure (K.guard rec) fc key visited) w target ctx) (fun _ _ => True)) :
    Agree K s (evalStep rec (.resolveAliasChase fc pr (.alias parent opens props target id reference) ctx visited last))
      (evalStep (K.guard rec) (.resolveAliasChase fc pr (.alias parent opens props target id reference) ctx visited last))
      (fun _ _ => True) := by
  show Agree K s (EvalBody.resolveAliasChase rec fc pr (.alias parent opens props target id reference) ctx visited last)
    (EvalBody.resolveAliasChase (K.guard rec) fc pr (.alias parent opens props target id reference) ctx visited last) _
  unfold EvalBody.resolveAliasChase runtimeAliasStepWith
  agree_tac
  all_goals first | assumption | solve_by_elim | exact vcStep _ _ _

/-- BINDER ENTRY: a user algorithm over a formed cell supply. VCs: the relational contract of the
    binder over the two answers' binding channels (`bindNeedPatterns`, higher-order), one-run
    contracts of the context former and the value-view probe, and the preconditions of its calls. -/
theorem pilot_evalNeedUserSupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState)
    (vcBind : ∀ t, Agree K t
      (withNestedMissingOutput (bindNeedPatterns rec.bindingChannels
        ((Algorithm.parameterPatterns callee).map NeedPattern.ofParameter) cells))
      (withNestedMissingOutput (bindNeedPatterns (K.guard rec).bindingChannels
        ((Algorithm.parameterPatterns callee).map NeedPattern.ofParameter) cells)) (fun _ _ => True))
    (vcContext : ∀ bindings t, Agree K t (needBindingContext ctx bindings) (needBindingContext ctx bindings)
      (fun _ _ => True))
    (vcView : ∀ t, Agree K t (valueViewCell? callee) (valueViewCell? callee) (fun _ _ => True))
    (vcDemand : ∀ address t, K.inv t → K.pre (.demandNeedRecursive address) t)
    (vcOutput : ∀ next values t, K.inv t → K.pre (.evalAlgOutputCounted callee next values) t) :
    Agree K s (EvalBody.evalNeedUserSupply rec callee cells ctx env)
      (EvalBody.evalNeedUserSupply (K.guard rec) callee cells ctx env) (fun _ _ => True) := by
  unfold EvalBody.evalNeedUserSupply EvalBody.evalNeedUserSupplyOutput
  agree_tac
  all_goals first | assumption | solve_by_elim

/-- FAMILY DISPATCH: a clause family over a formed cell supply. VCs: the relational contract of the
    dispatcher over the two answers' binding channels (`selectNeedFamilyBranch`, higher-order; it
    records the selected branch's activation), and the precondition of the body's evaluation. -/
theorem pilot_evalNeedFamilySupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv)
    (calleeName : String) (s : EvalState)
    (vcSelect : Agree K s
      (withNestedMissingOutput (selectNeedFamilyBranch rec.bindingChannels callee cells ctx env calleeName))
      (withNestedMissingOutput (selectNeedFamilyBranch (K.guard rec).bindingChannels callee cells ctx env calleeName))
      (fun _ _ => True))
    (vcOutput : ∀ body next values t, K.inv t → K.pre (.evalAlgOutputCounted body next values) t) :
    Agree K s (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName)
      (EvalBody.evalNeedFamilySupply (K.guard rec) callee cells ctx env calleeName) (fun _ _ => True) := by
  unfold EvalBody.evalNeedFamilySupply
  agree_tac
  all_goals first | assumption | solve_by_elim

/-- BODY ENTRY: an algorithm's output, entered once. VCs: the one-run contract of the body entry
    (`enterAlgorithmBody`, which records an activation), of the builtin's value, and the
    precondition of the rows' evaluation in the entered context. -/
theorem pilot_evalAlgOutputPreparedCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (vcBuiltin : ∀ b, Agree K s (evalBuiltinValueCounted b) (evalBuiltinValueCounted b) (fun _ _ => True))
    (vcEnter : ∀ t, Agree K t (enterAlgorithmBody a ctx env) (enterAlgorithmBody a ctx env) (fun _ _ => True))
    (vcRows : ∀ entered t, K.inv t → K.pre (.evalOutputRowsPreparedCore (Algorithm.output a) entered env) t) :
    Agree K s (evalStep rec (.evalAlgOutputPreparedCore a ctx env))
      (evalStep (K.guard rec) (.evalAlgOutputPreparedCore a ctx env)) (fun _ _ => True) := by
  show Agree K s (EvalBody.evalAlgOutputPreparedCore rec a ctx env)
    (EvalBody.evalAlgOutputPreparedCore (K.guard rec) a ctx env) _
  unfold EvalBody.evalAlgOutputPreparedCore
  agree_tac
  all_goals first | assumption | solve_by_elim

end Bodies

end KatLang.NavigationPilot
