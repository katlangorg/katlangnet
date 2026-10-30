import KatLangArityLaws.AddressInvariantWrites

open KatLang KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.CallPlan (bind_run map_run get_run pure_run modify_run throw_run lift_run evalAttempt_run)

/-!
# FG-H1-FU-01: the syntax-directed `SoundI` procedure

`ht_tac` proves a goal `SoundI P m Q` by symbolic execution of `m`: a bind whose head is an
ATOMIC operation — a recursive call `rec c` (contract `CallPre c` / `CallPost c` from the
hypothesis `RecSound rec`), or a helper with a registered contract (`ht_bind_spec`, extended by
`macro_rules` next to each contract) — adds the operation's postcondition to the precondition of
the continuation (`SoundI.bind`); `pure`, binds of binds, `<$>`, local definitions, `match` and
`if` are normalized or split; an unregistered non-recursive helper is proved separately with the
trivial postcondition, or unfolded in tail position. The side goals are the operations' input
requirements and the final postcondition, `∀ h, P h → R h` over the accumulated facts, closed by
`ht_leaf` (`split_ands` + `solve_by_elim` over the validity lemmas, extended by `ht_lemma`).
Macro hygiene is off so the tactic reaches lemmas declared after it.
-/

namespace KatLang.AddressInvariant

/-! ## Structural lemmas the procedure applies -/

theorem SoundI.of_run {α : Type} {P : Array NeedCell → Prop} {m m' : EvalM α}
    {Q : α → Array NeedCell → Prop} (heq : ∀ s, m.runState s = m'.runState s) (h : SoundI P m' Q) :
    SoundI P m Q := by
  intro hp s vs ps
  rw [heq s]
  exact h hp s vs ps

theorem SoundI.pure_bind {α β : Type} {P : Array NeedCell → Prop} {x : α} {f : α → EvalM β}
    {Q : β → Array NeedCell → Prop} (h : SoundI P (f x) Q) : SoundI P (Pure.pure x >>= f) Q :=
  SoundI.of_run (fun s => by rw [EvalM.bind_runState]; rfl) h

theorem SoundI.bind_assoc {α β γ : Type} {P : Array NeedCell → Prop} {m : EvalM α} {g : α → EvalM β}
    {f : β → EvalM γ} {Q : γ → Array NeedCell → Prop}
    (h : SoundI P (m >>= fun x => g x >>= f) Q) : SoundI P ((m >>= g) >>= f) Q := by
  refine SoundI.of_run (fun s => ?_) h
  rw [EvalM.bind_runState, EvalM.bind_runState, EvalM.bind_runState]
  rcases m.runState s with ⟨o, t⟩
  cases o with
  | error e => rfl
  | ok x => dsimp only; rw [EvalM.bind_runState]

theorem SoundI.map_bind {α β γ : Type} {P : Array NeedCell → Prop} {m : EvalM α} {g : α → β}
    {f : β → EvalM γ} {Q : γ → Array NeedCell → Prop}
    (h : SoundI P (m >>= fun x => f (g x)) Q) : SoundI P ((g <$> m) >>= f) Q := by
  refine SoundI.of_run (fun s => ?_) h
  rw [EvalM.bind_runState, map_run, EvalM.bind_runState]
  rcases m.runState s with ⟨o, t⟩
  cases o <;> rfl

theorem SoundI.map_tail {α β : Type} {P : Array NeedCell → Prop} {m : EvalM α} {g : α → β}
    {Q : β → Array NeedCell → Prop}
    (h : SoundI P (m >>= fun x => Pure.pure (g x)) Q) : SoundI P (g <$> m) Q := by
  refine SoundI.of_run (fun s => ?_) h
  rw [map_run, EvalM.bind_runState]
  rcases m.runState s with ⟨o, t⟩
  cases o <;> rfl

theorem SoundI.throw_bind {α β : Type} {P : Array NeedCell → Prop} {Q : β → Array NeedCell → Prop}
    (e : Error) (f : α → EvalM β) : SoundI P ((MonadExcept.throw e : EvalM α) >>= f) Q := by
  intro _ s vs _
  rw [EvalM.bind_runState]
  exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

theorem SoundI.error_bind {α β : Type} {P : Array NeedCell → Prop} {Q : β → Array NeedCell → Prop}
    (e : Error) (f : α → EvalM β) : SoundI P ((EvalM.error e : EvalM α) >>= f) Q := by
  intro _ s vs _
  rw [EvalM.bind_runState]
  exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- Consequence: an atomic operation's contract at the call site. -/
theorem SoundI.conseq {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q R : α → Array NeedCell → Prop} (hm : SoundI P m Q) (hq : ∀ x h, P h → Q x h → R x h) :
    SoundI P m R := by
  intro hp s vs ps
  obtain ⟨v, g, r⟩ := hm hp s vs ps
  exact ⟨v, g, fun x hx => hq _ _ (hp _ _ g ps) (r x hx)⟩

/-- A recursive call under its contract. -/
theorem SoundI.rec_call {rec : EvalRec} (hrec : RecSound rec) {c : EvalCall}
    {P : Array NeedCell → Prop} (hreq : ∀ h, P h → CallPre c h) :
    SoundI P (rec c) (CallPost c) :=
  SoundI.weaken (hrec c) hreq (callPre_mono c) (fun _ _ h => h)

theorem SoundI.true_post {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} (hm : SoundI P m Q) : SoundI P m (fun _ _ => True) :=
  SoundI.conseq hm (fun _ _ _ _ => trivial)

theorem PMono.true {α : Type} : PMono (fun (_ : α) (_ : Array NeedCell) => True) := fun _ _ _ _ _ => trivial

theorem PMono.lift {α : Type} (e : Except Error α) :
    PMono (fun (x : α) (_ : Array NeedCell) => e = .ok x) := fun _ _ _ _ v => v

theorem SoundI.modify_cell {P : Array NeedCell → Prop} {a : Nat} {f : NeedCell → NeedCell}
    (hf : ∀ h, P h → ∀ c, CellV h c → (f c).suspension = c.suspension ∧ CellV h (f c)) :
    SoundI P (modify fun s => { s with needs := s.needs.modify a f } : EvalM Unit) (fun _ _ => True) := by
  intro _ s vs ps
  rw [modify_run]
  have hsz : (s.needs.modify a f).size = s.needs.size := Array.size_modify ..
  refine ⟨inv_modify vs a f (fun c hc => hf _ ps c (vs.cells a c hc)), ?_, fun _ _ => trivial⟩
  show s.needs.size ≤ (s.needs.modify a f).size
  rw [hsz]; exact Nat.le_refl _

/-! ## Cell updates that keep the cell valid -/

section CellUpd
variable {h : Array NeedCell} {c : NeedCell} (v : CellV h c)
include v
theorem CellV.with_state {st : NeedState} (hs : StateV h st) : CellV h { c with state := st } :=
  ⟨v.susp, hs, v.plan, v.callee, v.receiver⟩
theorem CellV.with_callable (x : NeedCallableState) : CellV h { c with callable := x } :=
  ⟨v.susp, v.state, v.plan, v.callee, v.receiver⟩
theorem CellV.with_plan {p : NeedPlanSupply} (hp : PlanV h p) : CellV h { c with plan := p } :=
  ⟨v.susp, v.state, hp, v.callee, v.receiver⟩
theorem CellV.with_route (r : Option PlanRoute) : CellV h { c with route := r } :=
  ⟨v.susp, v.state, v.plan, v.callee, v.receiver⟩
theorem CellV.with_callee {o : Option Nat} (ho : OptAddr h o) : CellV h { c with callee := o } :=
  ⟨v.susp, v.state, v.plan, ho, v.receiver⟩
theorem CellV.with_receiver {o : Option Nat} (ho : OptAddr h o) : CellV h { c with receiver := o } :=
  ⟨v.susp, v.state, v.plan, v.callee, ho⟩
end CellUpd

theorem ExcV.of_eq {α : Type} {Q : α → Array NeedCell → Prop} {r : Except Error α} {x : α}
    {h : Array NeedCell} (v : ExcV Q r h) (e : r = .ok x) : Q x h := v x e
theorem PlanV.of_excv {h : Array NeedCell} {o : Except Error (List NeedSupply.Sourced)}
    (v : ExcV (fun xs h => ValidSourced h xs) o h) : PlanV h (.prepared o) := by
  cases o with
  | ok r => exact v r rfl
  | error _ => trivial
theorem StateV.of_excv {h : Array NeedCell} {o : Except Error CountedResult}
    (v : ExcV (fun r h => CRV h r) o h) : StateV h (.completed o) := by
  cases o with
  | ok r => exact v r rfl
  | error _ => trivial

theorem StateV.completed_ok {h : Array NeedCell} {r : CountedResult} (v : CRV h r) :
    StateV h (.completed (.ok r)) := v
theorem StateV.of_outcome {h : Array NeedCell} {o : Except Error CountedResult}
    (v : ∀ x, o = .ok x → CRV h x) : StateV h (.completed o) := by
  cases o with
  | ok r => exact v r rfl
  | error _ => trivial
theorem PlanV.of_outcome {h : Array NeedCell} {o : Except Error (List NeedSupply.Sourced)}
    (v : ∀ x, o = .ok x → ValidSourced h x) : PlanV h (.prepared o) := by
  cases o with
  | ok r => exact v r rfl
  | error _ => trivial

theorem SoundI.liftM {α : Type} {P : Array NeedCell → Prop} (e : Except Error α) :
    SoundI P (liftM e : EvalM α) (fun x _ => e = .ok x) := SoundI.lift e

/-! ## Typed `mapM` rules -/

theorem SoundI.mapM_nat {α : Type} {P : Array NeedCell → Prop} {f : α → EvalM Nat} {xs : List α}
    (hf : ∀ x ∈ xs, SoundI P (f x) (fun a h => a < h.size)) :
    SoundI P (xs.mapM f) (fun ys h => ValidAddresses h ys) :=
  SoundI.mapM (q := fun (a : Nat) h => a < h.size) (fun _ _ _ g v => Nat.lt_of_lt_of_le v g) xs hf

theorem SoundI.mapM_sourced {α : Type} {P : Array NeedCell → Prop} {f : α → EvalM NeedSupply.Sourced}
    {xs : List α} (hf : ∀ x ∈ xs, SoundI P (f x) (fun p h => p.1 < h.size)) :
    SoundI P (xs.mapM f) (fun ys h => ValidSourced h ys) :=
  SoundI.mapM (q := fun (p : NeedSupply.Sourced) h => p.1 < h.size) (fun _ _ _ g v => Nat.lt_of_lt_of_le v g) xs hf

theorem SoundI.mapM_result {α : Type} {P : Array NeedCell → Prop} {f : α → EvalM Result} {xs : List α}
    (hf : ∀ x ∈ xs, SoundI P (f x) (fun r h => RV h r)) :
    SoundI P (xs.mapM f) (fun ys h => RLV h ys) :=
  SoundI.mapM (q := fun r h => RV h r) (fun _ _ _ g v => RV.mono g v) xs hf

theorem ValidSourced.cons {h : Array NeedCell} {p : NeedSupply.Sourced} {xs : List NeedSupply.Sourced}
    (v : p.1 < h.size) (vs : ValidSourced h xs) : ValidSourced h (p :: xs) := by
  intro q m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs q m
theorem ValidSourced.pair {h : Array NeedCell} {a : Nat} {src : Option Expr} {xs : List NeedSupply.Sourced}
    (v : a < h.size) (vs : ValidSourced h xs) : ValidSourced h ((a, src) :: xs) := ValidSourced.cons v vs
attribute [ht_lemmas] ValidSourced.cons ValidSourced.pair

theorem RLV.mem {h : Array NeedCell} {xs : List Result} {x : Result} (m : x ∈ xs) (v : RLV h xs) : RV h x := v x m
theorem CRLV.mem {h : Array NeedCell} {xs : List CountedResult} {x : CountedResult} (m : x ∈ xs) (v : CRLV h xs) :
    CRV h x := v x m
theorem ValidAddresses.mem {h : Array NeedCell} {xs : List Nat} {x : Nat} (m : x ∈ xs) (v : ValidAddresses h xs) :
    x < h.size := v x m
theorem ValidSourced.mem {h : Array NeedCell} {xs : List NeedSupply.Sourced} {x : NeedSupply.Sourced}
    (m : x ∈ xs) (v : ValidSourced h xs) : x.1 < h.size := v x m
theorem ValidSourced.mem_pair {h : Array NeedCell} {xs : List NeedSupply.Sourced} {b : Nat} {src : Option Expr}
    (m : (b, src) ∈ xs) (v : ValidSourced h xs) : b < h.size := v _ m
theorem RALV.mem {h : Array NeedCell} {xs : List ResolvedArgumentAlgorithm} {x : ResolvedArgumentAlgorithm}
    (m : x ∈ xs) (v : RALV h xs) : RAV h x := v x m
theorem ValidAddresses.head {h : Array NeedCell} {a : Nat} {xs : List Nat} (v : ValidAddresses h (a :: xs)) :
    a < h.size := v a List.mem_cons_self
theorem ValidAddresses.tail {h : Array NeedCell} {a : Nat} {xs : List Nat} (v : ValidAddresses h (a :: xs)) :
    ValidAddresses h xs := fun b m => v b (List.mem_cons_of_mem _ m)
attribute [ht_lemmas] RLV.mem CRLV.mem ValidAddresses.mem ValidSourced.mem ValidSourced.mem_pair RALV.mem
  ValidAddresses.head ValidAddresses.tail
attribute [ht_fwd] ValidAddresses.head ValidAddresses.tail

theorem ValidSourced.getElem? {h : Array NeedCell} {xs : List NeedSupply.Sourced} {i : Nat} {b : Nat}
    {src : Option Expr} (v : ValidSourced h xs) (e : xs[i]? = some (b, src)) : b < h.size :=
  v _ (List.mem_of_getElem? e)
theorem ValidSourced.head? {h : Array NeedCell} {xs : List NeedSupply.Sourced} {b : Nat}
    {src : Option Expr} (v : ValidSourced h xs) (e : xs.head? = some (b, src)) : b < h.size :=
  v _ (List.mem_of_mem_head? e)
theorem ValidSourced.getLast? {h : Array NeedCell} {xs : List NeedSupply.Sourced} {b : Nat}
    {src : Option Expr} (v : ValidSourced h xs) (e : xs.getLast? = some (b, src)) : b < h.size :=
  v _ (List.mem_of_getLast? e)
attribute [ht_lemmas] ValidSourced.getElem? ValidSourced.head? ValidSourced.getLast?
attribute [ht_fwd] ValidSourced.getElem? ValidSourced.head? ValidSourced.getLast?


/-- A local contract hypothesis at a call site. -/
theorem SoundI.of_hyp {α : Type} {P R : Array NeedCell → Prop} {m : EvalM α} {Q : α → Array NeedCell → Prop}
    (H : SoundI R m Q) (hR : HMono P → HMono R) (hreq : ∀ h, P h → R h) : SoundI P m Q :=
  fun hp s vs ps => H (hR hp) s vs (hreq _ ps)

theorem SoundI.captureMeta {P : Array NeedCell → Prop} {name : Ident} {m : EvalM Nat}
    {Q : Nat → Array NeedCell → Prop} (hm : SoundI P m Q) : SoundI P (NeedBinder.captureMeta name m) Q :=
  SoundI.tryCatch hm (fun _ => SoundI.throw _)

attribute [ht_spec] SoundI.captureMeta

theorem SoundI.attempt_true {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    (hm : SoundI P m (fun _ _ => True)) : SoundI P (evalAttempt m) (fun _ _ => True) :=
  SoundI.true_post (SoundI.attempt hm)
theorem SoundI.withCtx_true {α : Type} {P : Array NeedCell → Prop} {m : EvalM α} (c : String)
    (hm : SoundI P m (fun _ _ => True)) : SoundI P (KatLang.withCtx c m) (fun _ _ => True) :=
  SoundI.withCtx c hm PMono.true
theorem SoundI.withMissingOutputCtx_true {α : Type} {P : Array NeedCell → Prop} {m : EvalM α} (c : String)
    (hm : SoundI P m (fun _ _ => True)) : SoundI P (KatLang.withMissingOutputCtx c m) (fun _ _ => True) :=
  SoundI.withMissingOutputCtx c hm PMono.true
theorem SoundI.withNestedMissingOutput_true {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    (hm : SoundI P m (fun _ _ => True)) : SoundI P (KatLang.withNestedMissingOutput m) (fun _ _ => True) :=
  SoundI.withNestedMissingOutput hm PMono.true
theorem SoundI.withMissingOutputNesting_true {α : Type} {P : Array NeedCell → Prop} {m : EvalM α} (nested : Bool)
    (hm : SoundI P m (fun _ _ => True)) : SoundI P (KatLang.withMissingOutputNesting nested m) (fun _ _ => True) :=
  SoundI.withMissingOutputNesting nested hm PMono.true

attribute [ht_spec] SoundI.rec_call get_spec SoundI.lift SoundI.liftM SoundI.attempt SoundI.withCtx
  SoundI.withMissingOutputCtx SoundI.withNestedMissingOutput SoundI.withMissingOutputNesting SoundI.modify_cell SoundI.mapM_nat SoundI.mapM_sourced
  SoundI.mapM_result
attribute [ht_spec] SoundI.attempt_true SoundI.withCtx_true SoundI.withMissingOutputCtx_true
  SoundI.withNestedMissingOutput_true SoundI.withMissingOutputNesting_true

/-! ## The procedure -/

/-- Bind through a REGISTERED atomic operation (extended next to each contract). -/
syntax "ht_bind_spec" : tactic
/-- A registered atomic operation in tail position. -/
syntax "ht_tail_spec" : tactic
/-- Extra leaf-solving steps (extended by later modules). -/
syntax "ht_leaf_ext" : tactic
/-- Callback-contract discharge (extended by later modules). -/
syntax "ht_cb" : tactic

macro_rules | `(tactic| ht_leaf_ext) => `(tactic| fail "no leaf extension")
macro_rules | `(tactic| ht_cb) => `(tactic| fail "no callback contract")
macro_rules | `(tactic| ht_bind_spec) => `(tactic| fail "no registered contract")
macro_rules | `(tactic| ht_tail_spec) => `(tactic| fail "no registered contract")

/-! ### Reading a valid cell -/

section CellRead
variable {h : Array NeedCell} {c : NeedCell} (v : CellV h c)
include v
theorem CellV.expr_ctx {e : Expr} {caller : EvalCtx} {vals : ValEnv}
    (hs : c.suspension = .expression e caller vals) : ValidCtx h caller := by
  have := v.susp; rw [hs] at this; exact this.1
theorem CellV.expr_values {e : Expr} {caller : EvalCtx} {vals : ValEnv}
    (hs : c.suspension = .expression e caller vals) : VEV h vals := by
  have := v.susp; rw [hs] at this; exact this.2
theorem CellV.ready {r : CountedResult} (hs : c.suspension = .ready r) : CRV h r := by
  have := v.susp; rw [hs] at this; exact this
theorem CellV.collector {slice : List Nat} (hs : c.suspension = .collector slice) : ValidAddresses h slice := by
  have := v.susp; rw [hs] at this; exact this
theorem CellV.completed {o : Except Error CountedResult} {r : CountedResult}
    (hs : c.state = .completed o) (ho : o = .ok r) : CRV h r := by
  have := v.state; rw [hs, ho] at this; exact this
theorem CellV.prepared {o : Except Error (List NeedSupply.Sourced)} {xs : List NeedSupply.Sourced}
    (hs : c.plan = .prepared o) (ho : o = .ok xs) : ValidSourced h xs := by
  have := v.plan; rw [hs, ho] at this; exact this
theorem CellV.callee_lt {x : Nat} (hs : c.callee = some x) : x < h.size := v.callee x hs
theorem CellV.receiver_lt {x : Nat} (hs : c.receiver = some x) : x < h.size := v.receiver x hs
end CellRead

theorem GotV.cell' {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat} {c : NeedCell}
    (hc : st.needs[a]? = some c) : CellV h c := v.cell hc

attribute [ht_lemmas] RV.atom RV.str RV.bool RV.seq RV.list RV.callRef RV.argView RLV.nil RLV.cons
  RLV.append RLV.reverse RLV.take RLV.drop RLV.singleton RLV.map_atom RLV.getElem?
  RLV.head? RLV.getLast? RLV.head RLV.tail CRV.mk CRLV.nil CRLV.cons CRLV.head CRLV.tail
  CRLV.fst CRLV.ones VEV.nil VEV.filter VEV.shadow VEV.lookup OptAddr.nil OptAddr.mk
  OptAddr.get ValidAddresses.nil ValidAddresses.cons ValidSourced.nil
  ValidNeedEnv.filter ValidNeedEnv.append ValidNeedEnv.lookup ValidSourced.addresses
  ValidSourced.append ValidAddresses.append ValidAddresses.take ValidAddresses.drop
  GotV.cell GotV.lt GotV.activation tier_valid StateV.of_outcome PlanV.of_outcome
  CellV.expr_ctx CellV.expr_values
  CellV.ready CellV.collector CellV.completed CellV.prepared CellV.callee_lt CellV.receiver_lt
  ExcV.ok OptSliceV.get OptSliceV.some OptActV.some

attribute [ht_fwd] GotV.cell ExcV.ok OptSliceV.some OptActV.some CellV.expr_ctx CellV.expr_values
  GotV.lt CellV.susp
attribute [ht_lemmas] CellV.susp
  CellV.ready CellV.collector CellV.completed CellV.prepared CellV.callee_lt CellV.receiver_lt

theorem RV.callRef_lt {h : Array NeedCell} {a : Nat} (v : RV h (.callRef a)) : a < h.size := RV.callRef_iff.1 v
theorem RV.argView_lt {h : Array NeedCell} {a : Nat} (v : RV h (.argView a)) : a < h.size := RV.argView_iff.1 v
theorem RV.seq_items {h : Array NeedCell} {xs : List Result} (v : RV h (.sequenceValue xs)) : RLV h xs := RV.seq_iff.1 v
theorem RV.list_items {h : Array NeedCell} {xs : List Result} (v : RV h (.listValue xs)) : RLV h xs := RV.list_iff.1 v
theorem CRV.rv {h : Array NeedCell} {p : CountedResult} (v : CRV h p) : RV h p.1 := v
theorem CRV.of_fst {h : Array NeedCell} {p : CountedResult} (v : RV h p.1) : CRV h p := v
attribute [ht_lemmas] RV.callRef_lt RV.argView_lt RV.seq_items RV.list_items PlanV.of_excv StateV.of_excv
  CRV.of_fst
attribute [ht_fwd] CRV.rv
attribute [ht_fwd] RV.callRef_lt RV.argView_lt RV.seq_items RV.list_items ExcV.of_eq

open Lean Meta Elab Tactic in
/-- Forward saturation of a leaf (two rounds): every `ht_fwd` lemma whose explicit premises are
    all matched (with backtracking) by hypotheses adds its conclusion, unless already present. -/
elab "ht_fwd" : tactic => do
  let lemmas ← Lean.labelled `ht_fwd
  for _ in [0:2] do
    let goal ← getMainGoal
    let g ← goal.withContext do
      let mut g := goal
      let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d
      let mut known : Array Lean.Expr := hyps.map (·.type)
      for L in lemmas do
        let c ← mkConstWithFreshMVarLevels L
        let (args, binfos, _) ← forallMetaTelescope (← inferType c)
        let explicit := (List.range args.size).filter (fun i => binfos[i]! == .default)
        -- backtracking assignment of the explicit premises
        let rec search (todo : List Nat) : MetaM (List (Array Lean.Expr)) := do
          match todo with
          | [] =>
            let pf ← instantiateMVars (mkAppN c args)
            if pf.hasExprMVar then return [] else return [#[pf]]
          | i :: rest =>
            let mut out := []
            for d in hyps do
              let saved ← saveState
              if ← withReducible (isDefEq (← inferType args[i]!) d.type) then
                if ← isDefEq args[i]! d.toExpr then
                  out := out ++ (← search rest)
              restoreState saved
              if out.length > 4 then break
            return out
        let found ← search explicit
        for pfs in found do
          let pf := pfs[0]!
          let ty := (← instantiateMVars (← inferType pf)).headBeta
          let dup ← known.anyM (fun k => withReducible (isDefEq k ty))
          unless dup do
            let (_, g') ← (← g.assert `fwd ty pf).intro1P
            g := g'
            known := known.push ty
      return g
    replaceMainGoal [g]

set_option hygiene false in
/-- A cell record update whose untouched fields stay valid. -/
macro "ht_cell_upd" : tactic => `(tactic| first
  | (apply CellV.with_state)
  | (apply CellV.with_plan)
  | (apply CellV.with_callee)
  | (apply CellV.with_receiver)
  | (apply CellV.with_callable)
  | (apply CellV.with_route))

/-- The conclusion of a goal after all its binders. -/
def htConclusion (ty : Lean.Expr) : Lean.Expr :=
  match ty with
  | .forallE _ _ b _ => htConclusion b
  | e => e

open Lean Meta Elab Tactic in
/-- The head constant of a proposition (after instantiating, without unfolding). -/
def htPropHead (t : Lean.Expr) : Option Name :=
  let t := t.headBeta
  match t.getAppFn with
  | .const c _ => some c
  | _ => none

open Lean Meta Elab Tactic in
/-- Head-indexed backward search: a goal is closed by a hypothesis, or by a `ht_lemmas` lemma
    whose conclusion has the goal's head constant (applied at reducible transparency), its
    premises solved recursively, with backtracking, to depth `d`. -/
partial def htBwd (lemmas : Array (Name × Option Name)) (d : Nat) (g : MVarId) : MetaM Bool := do
  if ← g.isAssigned then return true
  let ty ← instantiateMVars (← g.getType)
  -- assumption first
  let ok ← g.withContext do
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        let saved ← saveState
        if ← withReducible (isDefEq decl.type ty) then
          g.assign decl.toExpr
          return true
        restoreState saved
    return false
  if ok then return true
  if ty.isConstOf ``True then g.assign (mkConst ``True.intro); return true
  if d == 0 then return false
  if ty.isForall then
    let (_, g') ← g.intros
    return ← htBwd lemmas (d - 1) g'
  let head := htPropHead ty
  for (L, lh) in lemmas do
    if lh != head then continue
    let saved ← saveState
    try
      let gs ← g.withContext <| withReducible (g.apply (← mkConstWithFreshMVarLevels L))
      let mut allOk := true
      for sg in gs do
        unless ← htBwd lemmas (d - 1) sg do
          allOk := false
          break
      if allOk then return true
      restoreState saved
    catch _ => restoreState saved
  return false

open Lean Meta Elab Tactic in
/-- The conclusion heads of the `ht_lemmas` lemmas. -/
def htLemmaHeads : MetaM (Array (Name × Option Name)) := do
  let env ← getEnv
  let ls ← Lean.labelled `ht_lemmas
  return ls.map fun L =>
    match env.find? L with
    | some info => (L, htPropHead (htConclusion info.type))
    | none => (L, none)

open Lean Meta Elab Tactic in
/-- The validity lemmas every leaf may use (`htBwd`, depth 5). -/
elab "ht_sbe" : tactic => do
  let g ← getMainGoal
  let lemmas ← htLemmaHeads
  if ← htBwd lemmas 5 g then replaceMainGoal []
  else throwError "ht_sbe: no proof"

open Lean Meta Elab Tactic in
/-- Forward step of a leaf: every hypothesis `∀ h, A h → B h` (a requirement handed down by a
    contract) is instantiated at every heap `h` of the context for which `A h` is a hypothesis. -/
elab "specialize_reqs" : tactic => do
  let goal ← getMainGoal
  let g ← goal.withContext do
    let mut g := goal
    let lctx ← getLCtx
    let heaps := lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.type.isAppOfArity ``Array 1 &&
          (d.type.getArg! 0).isConstOf ``KatLang.NeedCell then acc.push d.toExpr else acc
    for d in lctx do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall && t.bindingDomain!.isAppOfArity ``Array 1 then
          for heap in heaps do
            let t1 ← instantiateForall t #[heap]
            if t1.isForall && !t1.bindingBody!.hasLooseBVars then
              let a := t1.bindingDomain!
              for e in lctx do
                unless e.isImplementationDetail do
                  if ← withReducible (isDefEq e.type a) then
                    let pf := mkApp2 d.toExpr heap e.toExpr
                    let pty ← inferType pf
                    let (_, g') ← (← g.assert `hreq_inst pty pf).intro1P
                    g := g'
    return g
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Beta-reduces every hypothesis and the target. -/
elab "beta_all" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let mut g := goal
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        let t' := t.headBeta
        if t' != t then
          g ← g.replaceLocalDeclDefEq d.fvarId t'
    let ty ← instantiateMVars (← g.getType)
    g ← g.replaceTargetDefEq (← Core.betaReduce ty)
    replaceMainGoal [g]

set_option hygiene false in
/-- A leaf obligation: the accumulated facts imply a requirement or the final postcondition. -/
macro "ht_leaf" : tactic => `(tactic| (
    intros
    try split_ands
    try specialize_reqs
    try simp only [CallPre, CallPost, SuspV, SupplyV, OriginV, SuffixV, StateV, PlanV] at *
    try split_ands
    all_goals (try ht_fwd)
    all_goals (try simp only [CallPre, CallPost, SuspV, SupplyV, OriginV, SuffixV, StateV, PlanV] at *)
    all_goals (try split_ands)
    all_goals (try ht_fwd)
    all_goals (try split_ands)
    all_goals repeat' (first
      | exact True.intro
      | assumption
      | rfl
      | ht_leaf_ext
      | (with_reducible apply And.intro)
      | ht_cell_upd
      | ht_sbe
      | split)
    done))

/-- A precondition-monotonicity side goal. -/
syntax "ht_hmono" : tactic
set_option hygiene false in
macro_rules | `(tactic| ht_hmono) => `(tactic| first | assumption | (intro _ _ g v; split_ands; repeat' (first | (exact ‹HMono _› _ _ g ‹_›) | mono_atom g | (apply And.intro) | (intro _ _; mono_atom g) | exact ‹_›)))

set_option hygiene false in
/-- A postcondition-monotonicity side goal. -/
syntax "ht_pmono" : tactic
set_option hygiene false in
macro_rules | `(tactic| ht_pmono) => `(tactic| first
  | exact callPost_mono _
  | exact GotV.mono
  | exact PMono.true
  | (apply ExcV.mono; ht_pmono)
  | (intro _ _ _ g v; (try simp only [CallPost] at v ⊢); split_ands
     repeat' (first | mono_atom g | (apply And.intro) | (intro _ _; mono_atom g) | exact ‹_›)))


/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "ht_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false, zeta := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval] at *)

open Lean Meta Elab Tactic

/-- The `SoundI` components of a goal: `(m, P)`. -/
def htGoal? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if ty.isAppOfArity ``SoundI 4 then some (ty.getArg! 2, ty.getArg! 1) else none

/-- What a computation is, for the procedure. -/
inductive HtKind where
  | bind (x : Lean.Expr)
  | pure
  | branch
  | letE
  | map
  | throw
  | fvarApp
  | const (c : Name)
  | other

def htThrowConsts : List Name :=
  [``MonadExcept.throw, ``MonadExceptOf.throw, ``throwThe, ``EvalM.error]

def htClassify (m : Lean.Expr) : MetaM HtKind := do
  let m := m.headBeta
  if m.isLet then return .letE
  let fn := m.getAppFn
  match fn with
  | .const c _ =>
    if c == ``Bind.bind && m.getAppNumArgs == 6 then return .bind (m.getArg! 4)
    if c == ``Pure.pure then return .pure
    if c == ``Functor.map then return .map
    if c ∈ htThrowConsts then return .throw
    if c == ``ite || c == ``dite then return .branch
    if (← Lean.Meta.isMatcher c) then return .branch
    return .const c
  | .fvar _ => return .fvarApp
  | _ => return .other

/-- Zeta-reduces the top-level local definitions of the computation (and of a bind head). -/
def htZeta (m : Lean.Expr) : Lean.Expr := Id.run do
  let mut e := m
  for _ in [0:10000] do
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .mdata _ e' => e := e'
    | _ => break
  return e

def htReplaceComputation (goal : MVarId) (ty m' : Lean.Expr) : MetaM MVarId :=
  goal.replaceTargetDefEq (mkAppN ty.getAppFn #[ty.getArg! 0, ty.getArg! 1, m', ty.getArg! 3])

/-- Unfolds the head constant `c` of `x` (non-recursive definitions only). -/
def htUnfoldConst (goal : MVarId) (c : Name) : MetaM MVarId := do
  let g' ← Lean.Meta.unfoldTarget goal c
  let ty' ← instantiateMVars (← g'.getType)
  if (ty'.find? (fun e => e.isConstOf c)).isSome then
    throwError "ht: {c} is recursive (register a contract)"
  return g'

/-- A `match` whose discriminants are constructor applications, reduced. -/
def htReduceMatch (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  match ← Lean.Meta.reduceMatcher? e with
  | .reduced e' => return some e'.headBeta
  | _ => return none


/-- The head key of a contract's computation (`none` for a callback, i.e. a bound variable). -/
def htSpecKey? (t : Lean.Expr) : Option (Option Name) :=
  let concl := htConclusion t
  if concl.isAppOfArity ``SoundI 4 then
    let m := (concl.getArg! 2).headBeta
    match m.getAppFn with
    | .const c _ => some (some c)
    | .bvar _ => some none
    | _ => none
  else none

/-- The registered contracts whose computation head is `key`. -/
def htSpecsFor (key : Option Name) : MetaM (List Name) := do
  let all ← Lean.labelled `ht_spec
  let env ← getEnv
  return all.toList.filter fun L =>
    match env.find? L with
    | some info => htSpecKey? info.type == some key
    | none => false

/-- Applies `L : … → SoundI P (op …) Post` to a goal `SoundI P x ?Q`; returns its premises,
    those that are hypotheses (callback contracts, the recursive answer's contract) closed. -/
def htApplySpec (goal : MVarId) (L : Name) : MetaM (List MVarId) := do
  let c ← mkConstWithFreshMVarLevels L
  let gs ← withReducible (goal.apply c)
  let mut rest := []
  for g in gs do
    if ← g.isAssigned then continue
    let closed ← try (withReducible g.assumption); pure true catch _ => pure false
    unless closed do rest := rest ++ [g]
  return rest

/-- Bind (`bind := true`) or tail use of the first registered contract matching the head of the
    computation. -/
def htTrySpecs (bind : Bool) (key : Option Name) : TacticM Bool := do
  let goal ← getMainGoal
  -- local contract hypotheses first
  let hypOk ← goal.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      unless (htConclusion t).isAppOfArity ``SoundI 4 do continue
      let saved ← saveState
      try
        let (xs, _, _) ← forallMetaTelescope t
        let happ := mkAppN d.toExpr xs
        -- a hypothesis generalized over its precondition is used at the current one
        let hty ← instantiateMVars (← inferType happ)
        let gty0 ← instantiateMVars (← goal.getType)
        if (hty.getArg! 1).getAppFn.isMVar then
          discard <| isDefEq (hty.getArg! 1) (gty0.getArg! 1)
        let ofh ← mkConstWithFreshMVarLevels ``SoundI.of_hyp
        let (oargs, _, _) ← forallMetaTelescopeReducing (← inferType ofh) (some 6)
        unless ← isDefEq (← inferType oargs[5]!) (← inferType happ) do throwError "ht: hyp type"
        unless ← isDefEq oargs[5]! happ do throwError "ht: hyp"
        let pf := mkAppN ofh oargs
        let gty ← instantiateMVars (← goal.getType)
        let tailMVar := (gty.getArg! 3).getAppFn.isMVar
        let target ← if bind then do
            let gs ← goal.apply (← mkConstWithFreshMVarLevels ``SoundI.bind)
            pure (gs.head!, gs.tail)
          else if tailMVar then pure (goal, [])
          else do
            let gs ← goal.apply (← mkConstWithFreshMVarLevels ``SoundI.conseq)
            pure (gs.head!, gs.tail)
        let prem ← withReducible (target.1.apply pf)
        -- the hypothesis's own premises become goals
        let mut extra := []
        for x in xs do
          if !(← x.mvarId!.isAssigned) && (← isProp (← inferType x)) then extra := extra ++ [x.mvarId!]
        replaceMainGoal (prem ++ extra ++ target.2)
        return true
      catch _ => restoreState saved
    return false
  if hypOk then return true
  let specs ← htSpecsFor key
  -- tail use with a concrete postcondition: first every contract whose postcondition matches
  unless bind do
    let ty ← instantiateMVars (← goal.getType)
    unless (ty.getArg! 3).getAppFn.isMVar do
      for L in specs do
        let saved ← saveState
        try
          let prem ← htApplySpec goal L
          replaceMainGoal prem
          return true
        catch _ => restoreState saved
  for L in specs do
    let saved ← saveState
    try
      if bind then
        let gs ← goal.apply (← mkConstWithFreshMVarLevels ``SoundI.bind)
        -- goals: hm, hq, hf (implicit mvars are assigned or remain natural)
        match gs with
        | hm :: rest =>
          let prem ← htApplySpec hm L
          replaceMainGoal (prem ++ rest)
          return true
        | [] => throwError "ht: bind"
      else
        -- an unknown (metavariable) or matching postcondition is the contract's own; otherwise weaken
        let ty ← instantiateMVars (← goal.getType)
        if (ty.getArg! 3).getAppFn.isMVar then
          let prem ← htApplySpec goal L
          replaceMainGoal prem
          return true
        let gs ← goal.apply (← mkConstWithFreshMVarLevels ``SoundI.conseq)
        match gs with
        | hm :: rest =>
          let prem ← htApplySpec hm L
          replaceMainGoal (prem ++ rest)
          return true
        | [] => throwError "ht: tail"
    catch _ => restoreState saved
  return false

/-- Result types that carry no need address (`Algorithm`, `ResolvedProperty`, text, flags, …). -/
partial def htAddressFree (t : Lean.Expr) : Bool :=
  match t.getAppFn with
  | .const c _ =>
    if c ∈ [``KatLang.Algorithm, ``KatLang.ResolvedProperty, ``Bool, ``String, ``Unit, ``PUnit, ``Int,
        ``KatLang.PlanRoute, ``KatLang.RuntimeAliasStep, ``KatLang.Expr, ``KatLang.PropDef,
        ``KatLang.DotSelection] then true
    else if c == ``Option || c == ``List then
      if t.getAppNumArgs == 1 then htAddressFree (t.getArg! 0) else false
    else if c == ``Prod then
      t.getAppNumArgs == 2 && htAddressFree (t.getArg! 0) && htAddressFree (t.getArg! 1)
    else if c == ``Except then
      t.getAppNumArgs == 2 && htAddressFree (t.getArg! 1)
    else false
  | _ => false

/-- One step of the procedure on the main goal. -/
elab "ht_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let ty := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  match htGoal? ty with
  | none =>
    if ty.isAppOf ``PMono then evalTactic (← `(tactic| ht_pmono))
    else if ty.isAppOf ``HMono then evalTactic (← `(tactic| ht_hmono))
    else if ty.isForall && (htConclusion ty).isAppOf ``HMono then
      evalTactic (← `(tactic| (intro; ht_hmono)))
    else if ty.isForall then
      -- a continuation `∀ a, SoundI …` or a leaf
      if (htGoal? (htConclusion ty)).isSome then
        evalTactic (← `(tactic| intro_syntactic))
      else evalTactic (← `(tactic| ht_leaf))
    else evalTactic (← `(tactic| ht_leaf))
  | some (m, _) =>
    let m ← instantiateMVars m
    match ← htClassify m with
    | .letE => replaceMainGoal [← htReplaceComputation goal ty (htZeta m)]
    | .pure => evalTactic (← `(tactic| refine SoundI.pure _ ?_))
    | .throw => evalTactic (← `(tactic| first | exact SoundI.throw _ | exact SoundI.error _))
    | .branch =>
      match ← htReduceMatch m with
      | some m' => replaceMainGoal [← htReplaceComputation goal ty m']
      | none => evalTactic (← `(tactic| split))
    | .map => evalTactic (← `(tactic| apply SoundI.map_tail))
    | .fvarApp =>
      try evalTactic (← `(tactic| ht_tail_spec))
      catch _ =>
        unless ← htTrySpecs false none do throwError "ht: no contract for the callback {m}"
    | .other =>
      let m' ← whnfCore m
      if m' == m then throwError "ht: stuck on {m}"
      replaceMainGoal [← htReplaceComputation goal ty m']
    | .const c =>
      if ← htTrySpecs false (some c) then return
      try evalTactic (← `(tactic| ht_tail_spec))
      catch _ =>
        let m' ← whnfCore m
        if m' != m then replaceMainGoal [← htReplaceComputation goal ty m']
        else replaceMainGoal [← htUnfoldConst goal c]
    | .bind x =>
      let x ← instantiateMVars x
      match ← htClassify x with
      | .pure => evalTactic (← `(tactic| apply SoundI.pure_bind))
      | .bind _ => evalTactic (← `(tactic| apply SoundI.bind_assoc))
      | .map => evalTactic (← `(tactic| apply SoundI.map_bind))
      | .throw => evalTactic (← `(tactic| first | exact SoundI.throw_bind _ _ | exact SoundI.error_bind _ _))
      | .branch =>
        match ← htReduceMatch x with
        | some x' =>
          let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 x')
          replaceMainGoal [← htReplaceComputation goal ty m']
        | none => evalTactic (← `(tactic| split))
      | .letE =>
        let f := m.getArg! 5
        let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 (htZeta x) |>.set! 5 f)
        replaceMainGoal [← htReplaceComputation goal ty m']
      | .fvarApp =>
        try evalTactic (← `(tactic| ht_bind_spec))
        catch _ =>
          unless ← htTrySpecs true none do throwError "ht: no contract for the callback {x}"
      | .other =>
        let x' ← whnfCore x
        if x' == x then throwError "ht: stuck on bind head {x}"
        let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 x')
        replaceMainGoal [← htReplaceComputation goal ty m']
      | .const c =>
        -- a wrapper binding an address-free value: atomize it with the trivial postcondition
        let α ← whnfR (← instantiateMVars (m.getArg! 2))
        if (c == ``KatLang.withCtx || c == ``KatLang.withMissingOutputCtx ||
            c == ``KatLang.withNestedMissingOutput || c == ``KatLang.withMissingOutputNesting ||
            c == ``KatLang.evalAttempt) &&
            htAddressFree α then
          evalTactic (← `(tactic| refine SoundI.bind (Q := fun _ _ => True) ?_ PMono.true ?_))
          return
        if ← htTrySpecs true (some c) then return
        try evalTactic (← `(tactic| ht_bind_spec))
        catch _ =>
          let x' ← whnfCore x
          if x' != x then
            let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 x')
            replaceMainGoal [← htReplaceComputation goal ty m']
          else
            -- an unregistered helper: when its result type carries no need address, prove it
            -- separately with the trivial postcondition; otherwise inline it in place
            let α ← whnfR (← instantiateMVars (m.getArg! 2))
            if htAddressFree α then
              evalTactic (← `(tactic| refine SoundI.bind (Q := fun _ _ => True) ?_ PMono.true ?_))
            else
              match x.getAppFn with
              | .const c _ => replaceMainGoal [← htUnfoldConst goal c]
              | _ => throwError "ht: stuck on bind head {x}"

/-- The whole procedure. -/
macro "ht_tac" : tactic => `(tactic| ((try ht_unfold_rec) <;> repeat' (first | disc_absurd | (beta_all; ht_step) | ht_step)))


end KatLang.AddressInvariant
