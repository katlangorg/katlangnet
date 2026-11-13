import KatLangArityLaws.NavigationContract

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.MemberSettled
open KatLang.NavigationReread KatLang.NavigationContract

/-!
# One judgment for both halves of the per-body obligation (ledger E-18, step 1, B2 preparation — PILOT)

`Contract.BodySound` has two halves: every body KEEPS the contract, and each navigation body runs
alike over the answer GUARDED by the contract. This module shows they are ONE obligation, for every
contract (the calculus is generic in the contract's value predicates — nothing here mentions
navigation's own):

* `Agree K s m m' Q` — if the run of `m` (the body over the answer) from the invariant state `s`
  completes, then `m'` (the body over the guarded answer) is the SAME run, the exit state is
  invariant and an extension, and a success satisfies `Q`.
* It composes syntax-directedly: `pure`, `throw`, `bind` (the continuation at the state actually
  reached, with the first computation's result contract), `evalAttempt`, `<$>`, a recursive call
  (`Agree.rec_call`: THE leaf at which a call-site precondition is established) and a computation
  that asks no question (`Agree.same`, from a one-run fact).
* `bodySound_of_agree` — a family of `Agree` judgments, one per body, IS `K.BodySound`.

## The pilot, and its verdict

The judgment is applied by hand (no tactic was built) to the structure chase
(`agree_resolveAliasStructure`), the `.Algorithm` route fact (`agree_algorithmIntrinsicRoute`) and
the receiver probe's NAME head and MEMBER edge (`agree_resolveDotReceiver_name`,
`agree_resolveDotReceiver_member`), each relative to its explicit call-site conditions. For the
member edge the one condition that is not structural is

    the member production wires, once accessible, satisfies the chase's precondition

which the B2 preparation (2026-11-12) found false on a source program. Since the anchoring of a
container's chain (owner decision 2026-11-13) that program's member is owned
(`NavigationSourceDomainGuards.OutsideContainer.reached_member_is_owned`), but the condition is not
proved for every member production wires. So the pilot is PARTIAL: the mechanism gives both halves
from one judgment, and member navigation is not closed. No whole-run claim follows from this module.
-/

namespace KatLang.NavigationRelational

/-- A contract whose extension order is a preorder (every contract of interest: heap growth, the
    activation prefix order). -/
structure Ordered (K : Contract) : Prop where
  refl : ∀ s, K.ext s s
  trans : ∀ s t u, K.ext s t → K.ext t u → K.ext s u

/-- **THE COMBINED JUDGMENT.** From the invariant state `s`: if the run of `m` completes, the run of
    `m'` is the same run, the exit state is invariant and extends `s`, and a success satisfies `Q`. -/
def Agree (K : Contract) {α : Type} (s : EvalState) (m m' : EvalM α) (Q : α → EvalState → Prop) : Prop :=
  K.inv s → (m.runState s).1 ≠ .error .fuelExhausted →
    m'.runState s = m.runState s ∧ K.inv (m.runState s).2 ∧ K.ext s (m.runState s).2 ∧
      ∀ x, (m.runState s).1 = .ok x → Q x (m.runState s).2

section Calculus
variable {K : Contract} (ho : Ordered K)
include ho

theorem Agree.pure {α : Type} {s : EvalState} {Q : α → EvalState → Prop} (a : α) (h : K.inv s → Q a s) :
    Agree K s (Pure.pure a : EvalM α) (Pure.pure a) Q :=
  fun hi _ => ⟨rfl, hi, ho.refl s, fun x hx => by cases hx; exact h hi⟩

theorem Agree.throw {α : Type} {s : EvalState} {Q : α → EvalState → Prop} (e : Error) :
    Agree K s (throw e : EvalM α) (throw e) Q :=
  fun hi _ => ⟨rfl, hi, ho.refl s, fun _ hx => by cases hx⟩

theorem Agree.error {α : Type} {s : EvalState} {Q : α → EvalState → Prop} (e : Error) :
    Agree K s (EvalM.error e : EvalM α) (EvalM.error e) Q :=
  fun hi _ => ⟨rfl, hi, ho.refl s, fun _ hx => by cases hx⟩

omit ho in
/-- A computation that asks the answer nothing, from a one-run fact about it. -/
theorem Agree.same {α : Type} {s : EvalState} {m : EvalM α} {Q : α → EvalState → Prop}
    (h : K.inv s → (m.runState s).1 ≠ .error .fuelExhausted →
      K.inv (m.runState s).2 ∧ K.ext s (m.runState s).2 ∧ ∀ x, (m.runState s).1 = .ok x → Q x (m.runState s).2) :
    Agree K s m m Q := fun hi hne => ⟨rfl, h hi hne⟩

/-- A state-free computation asks nothing and changes nothing. -/
theorem Agree.stateFree {α : Type} {s : EvalState} {m : EvalM α} (hsf : StateFree m) :
    Agree K s m m (fun x t => t = s ∧ m.runState s = (.ok x, s)) := by
  obtain ⟨o, hrun⟩ := hsf
  refine Agree.same (fun hi _ => ?_)
  rw [hrun s]
  exact ⟨hi, ho.refl s, fun x hx => ⟨rfl, by cases hx; rfl⟩⟩

/-- Sequencing: the continuation is judged at the state the first computation actually reached,
    with its result contract. -/
theorem Agree.bind {α β : Type} {s : EvalState} {m m' : EvalM α} {f f' : α → EvalM β}
    {P : α → EvalState → Prop} {Q : β → EvalState → Prop} (hm : Agree K s m m' P)
    (hf : ∀ a t, m.runState s = (.ok a, t) → K.inv t → K.ext s t → P a t → Agree K t (f a) (f' a) Q) :
    Agree K s (m >>= f) (m' >>= f') Q := by
  intro hi hdone
  rcases hrun : m.runState s with ⟨o, t⟩
  cases o with
  | error e =>
    have hb : (m >>= f).runState s = (.error e, t) := by rw [bind_run, hrun]
    rw [hb] at hdone
    have hne : e ≠ .fuelExhausted := fun he => hdone (by rw [he])
    have hm' := hm hi (by rw [hrun]; exact fun h => hne (Except.error.inj h))
    rw [hrun] at hm'
    rw [hb]
    refine ⟨?_, hm'.2.1, hm'.2.2.1, fun _ hx => by cases hx⟩
    rw [bind_run, hm'.1]
  | ok a =>
    have hb : (m >>= f).runState s = (f a).runState t := by rw [bind_run, hrun]
    rw [hb] at hdone
    have hm' := hm hi (by rw [hrun]; nofun)
    rw [hrun] at hm'
    have hf' := hf a t hrun hm'.2.1 hm'.2.2.1 (hm'.2.2.2 a rfl) hm'.2.1 hdone
    rw [hb]
    refine ⟨?_, hf'.2.1, ho.trans _ _ _ hm'.2.2.1 hf'.2.2.1, hf'.2.2.2⟩
    rw [bind_run, hm'.1]
    exact hf'.1

theorem Agree.map {α β : Type} {s : EvalState} {m m' : EvalM α} {P : α → EvalState → Prop}
    {Q : β → EvalState → Prop} (g : α → β) (hm : Agree K s m m' P) (h : ∀ a t, P a t → Q (g a) t) :
    Agree K s (g <$> m) (g <$> m') Q :=
  Agree.bind ho (f := fun a => Pure.pure (g a)) (f' := fun a => Pure.pure (g a)) hm
    (fun a _ _ _ _ hp => Agree.pure ho _ (fun _ => h a _ hp))

omit ho in
/-- A caught failure: the attempt of the guarded computation is the attempt of the computation. -/
theorem Agree.attempt {α : Type} {s : EvalState} {m m' : EvalM α} {Q : α → EvalState → Prop}
    (hm : Agree K s m m' Q) :
    Agree K s (evalAttempt m) (evalAttempt m') (fun r t => ∀ x, r = .ok x → Q x t) := by
  intro hi hdone
  rcases hrun : m.runState s with ⟨o, t⟩
  cases hinc : o.isIncomplete with
  | true =>
    have hoe := Except.isIncomplete_eq_true hinc
    subst hoe
    rw [evalAttempt_runState_of_incomplete m s t hrun] at hdone
    exact absurd rfl hdone
  | false =>
    have hne : o ≠ .error .fuelExhausted := by
      intro h; subst h; cases hinc
    have hm' := hm hi (by rw [hrun]; exact hne)
    rw [hrun] at hm'
    rw [evalAttempt_runState_of_complete m s t o hrun hinc,
      evalAttempt_runState_of_complete m' s t o hm'.1 hinc]
    exact ⟨rfl, hm'.2.1, hm'.2.2.1, fun r hr => by cases hr; exact hm'.2.2.2⟩

omit ho in
/-- **THE LEAF: a recursive call.** Over an answer that keeps the contract, a call whose precondition
    holds at the state it is asked from is answered alike by the guarded answer, and its result
    contract holds. This is where every call site's precondition is established. -/
theorem Agree.rec_call {rec : EvalRec} (hk : K.Keeps rec) {c : EvalCall} {s : EvalState} (hp : K.pre c s) :
    Agree K s (rec c) (K.guard rec c) (K.post c) :=
  fun hi hne => ⟨K.guard_run_of rec c s hi hp, hk c s hi hp hne⟩

omit ho in
theorem Agree.conseq {α : Type} {s : EvalState} {m m' : EvalM α} {P Q : α → EvalState → Prop}
    (hm : Agree K s m m' P) (h : ∀ a t, P a t → Q a t) : Agree K s m m' Q :=
  fun hi hne => ⟨(hm hi hne).1, (hm hi hne).2.1, (hm hi hne).2.2.1, fun x hx => h _ _ ((hm hi hne).2.2.2 x hx)⟩

end Calculus

/-- **ONE OBLIGATION, BOTH HALVES.** A family of combined judgments — every body, over every normal
    answer that keeps the contract, from every state satisfying the call's precondition — IS the
    per-body obligation of the contract. -/
theorem bodySound_of_agree (K : Contract)
    (h : ∀ rec : EvalRec, NormalRec rec → K.Keeps rec → ∀ (c : EvalCall) (s : EvalState), K.pre c s →
      Agree K s (evalStep rec c) (evalStep (K.guard rec) c) (K.post c)) : K.BodySound := by
  intro rec hn hk
  refine ⟨fun c s hi hp hne => (h rec hn hk c s hp hi hne).2, fun c s _ hi hp hne => (h rec hn hk c s hp hi hne).1⟩

/-! ## The pilot: navigation bodies, relative to their call-site conditions -/

section Bodies
variable {K : Contract} (ho : Ordered K) {rec : EvalRec} (hk : K.Keeps rec)
include ho hk

/-- THE STRUCTURE CHASE: one question, the chase of its own algorithm, at the entry state. -/
theorem agree_resolveAliasStructure (a : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (hchase : K.pre (.resolveAliasChase false true a ctx [] none) s) :
    Agree K s (EvalBody.resolveAliasStructure rec a ctx) (EvalBody.resolveAliasStructure (K.guard rec) a ctx)
      (fun _ _ => True) := by
  unfold EvalBody.resolveAliasStructure
  refine Agree.bind ho (Agree.rec_call hk hchase) (fun r t _ _ _ _ => ?_)
  cases r <;> exact Agree.pure ho _ (fun _ => trivial)

/-- THE `.Algorithm` ROUTE FACT: one question, the receiver probe, at the entry state. -/
theorem agree_algorithmIntrinsicRoute (receiver : Expr) (ctx : EvalCtx) (s : EvalState)
    (hprobe : K.pre (.resolveDotReceiver? receiver ctx) s) :
    Agree K s (EvalBody.algorithmIntrinsicRoute rec receiver ctx)
      (EvalBody.algorithmIntrinsicRoute (K.guard rec) receiver ctx) (fun _ _ => True) := by
  unfold EvalBody.algorithmIntrinsicRoute
  refine Agree.bind ho (Agree.rec_call hk hprobe) (fun r t _ _ _ _ => ?_)
  split <;> exact Agree.pure ho _ (fun _ => trivial)

/-- THE RECEIVER PROBE of a NAME head: the lexical lookup asks nothing; the one question is the
    structure chase of the binding it selects — LEXICAL LOOKUP's call-site condition. -/
theorem agree_resolveDotReceiver_name (n : Ident) (owner : Algorithm) (rest : List Algorithm) (ctx : EvalCtx)
    (s : EvalState) (hstack : ctx.callStack = owner :: rest)
    (hselected : ∀ resolved, (lookupLexicalPropertyRaw owner n ctx).runState s = (.ok resolved, s) →
      K.pre (.resolveAliasStructure resolved.alg ctx) s) :
    Agree K s (EvalBody.resolveDotReceiver? rec (.resolve n) ctx)
      (EvalBody.resolveDotReceiver? (K.guard rec) (.resolve n) ctx)
      (K.post (.resolveAliasStructure (match (lookupLexicalPropertyRaw owner n ctx).runState s with
        | (.ok resolved, _) => resolved.alg
        | _ => owner) ctx)) := by
  unfold EvalBody.resolveDotReceiver?
  simp only [hstack]
  refine Agree.bind ho (Agree.stateFree ho (sf_lookupLexicalPropertyRaw owner n ctx)) (fun resolved t _ _ _ hp => ?_)
  obtain ⟨rfl, hrun⟩ := hp
  rw [hrun]
  exact Agree.rec_call hk (hselected resolved hrun)

/-- **THE RECEIVER PROBE of a MEMBER edge `o.n`** — member navigation. Three kinds of question: the
    probe of the receiver, at the entry state; the structure chase of the member production wires
    (`childOfInContext`) once `memberAccessible?` accepts it; and `resolveAlg` of the edge on a miss.
    `hmember` is MEMBER NAVIGATION's call-site condition: for the navigation contract it asks the
    wired member to be `AlgOK`. The B2 preparation refuted it on a source program; since the
    anchoring of a container's chain (2026-11-13) that program's member is owned
    (`NavigationSourceDomainGuards.OutsideContainer.reached_member_is_owned`), and the condition is
    not proved in general. -/
theorem agree_resolveDotReceiver_member (o : Expr) (n : Ident) (fallback : Expr) (ctx : EvalCtx) (s : EvalState)
    (hprobe : K.pre (.resolveDotReceiver? o ctx) s)
    (hmember : ∀ a t, K.inv t → K.ext s t → K.post (.resolveDotReceiver? o ctx) (some a) t →
      ∀ p, Algorithm.lookupPropDefAny? a n = some p → memberAccessible? ctx a p = true →
        K.pre (.resolveAliasStructure (childOfInContext a p.alg ctx) ctx) t)
    (hmiss : ∀ t, K.inv t → K.ext s t → K.pre (.resolveAlg (.dotMember o n fallback none) ctx) t) :
    Agree K s (EvalBody.resolveDotReceiver? rec (.dotMember o n fallback none) ctx)
      (EvalBody.resolveDotReceiver? (K.guard rec) (.dotMember o n fallback none) ctx) (fun _ _ => True) := by
  have hmissAgree : ∀ t, K.inv t → K.ext s t →
      Agree K t (some <$> rec.resolveAlg (.dotMember o n fallback none) ctx)
        (some <$> (K.guard rec).resolveAlg (.dotMember o n fallback none) ctx) (fun _ _ => True) :=
    fun t hi he => Agree.map ho some (Agree.rec_call hk (hmiss t hi he)) (fun _ _ _ => trivial)
  unfold EvalBody.resolveDotReceiver?
  refine Agree.bind ho (Agree.rec_call hk hprobe) (fun r t _ hit het hpost => ?_)
  cases r with
  | none => exact hmissAgree t hit het
  | some a =>
    dsimp only
    cases hp : Algorithm.lookupPropDefAny? a n with
    | none =>
      dsimp only
      split
      · exact Agree.error ho _
      · exact hmissAgree t hit het
    | some p =>
      dsimp only
      by_cases hacc : memberAccessible? ctx a p = true
      · rw [hacc]
        refine Agree.bind ho (Agree.rec_call hk (hmember a t hit het hpost p hp hacc)) (fun member u _ hiu heu _ => ?_)
        cases member with
        | none => exact hmissAgree u hiu (ho.trans _ _ _ het heu)
        | some found => exact Agree.pure ho _ (fun _ => trivial)
      · have hfalse : memberAccessible? ctx a p = false := by
          cases h : memberAccessible? ctx a p with
          | true => exact absurd h hacc
          | false => rfl
        rw [hfalse]
        exact Agree.error ho _

end Bodies

end KatLang.NavigationRelational
