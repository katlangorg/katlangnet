import KatLangArityLaws.BinderCorrespondence
import KatLangArityLaws.NeedControl
import KatLangArityLaws.CallReference

open KatLang KatLang.BinderTrace KatLang.BinderCorrespondence

/-!
# Callback / direct-call binder correspondence over formed supplies (R6, S5, October 2026)

A callback invocation (`evalUserCallbackCallCounted`, `evalConditionalCallbackCallCounted`,
`evalResolvedCallbackCallCounted`) allocates one READY cell per counted argument
(`args.mapM readyNeed`) and then runs THE SAME supplied-call arm as an ordinary call
(`evalNeedUserSupply` / `evalNeedFamilySupply`, whose binding is `bindNeedPatterns` /
`selectNeedFamilyBranch`, i.e. the generic core `NeedBinder`). An ordinary written call forms its
cells with `formNeedSupply` (`NeedSupply.form`), generally SUSPENDED expression cells. That both
routes call the same arm is a fact of the `partial` source; that both reach the same BINDER is
definitional (`bind_need_patterns_is_core`); that equal VALUES alone make the two supplies
equivalent is false (a Ready cell has no CALLABLE identity and no META plan).

THE OBSERVATION BOUNDARY. This module compares two BINDING RUNS — the binder's outcome (error,
non-match, or bound environment) and the two final states up to a stated correspondence — never
the callee body's evaluation, builtin role dispatch, alias resolution, a whole sequence operation,
host effects, budgets, diagnostics' presentation or whole-run caches. The body is an explicit
continuation where the clause search activates it (`choose_branch_sim`).

THREE LEVELS, kept apart:

1. SAME CELLS, SAME CAPABILITIES, SAME STATE: both routes run one definition on one input, so
   they agree by reflexivity. This is a source fact about the routes, not a theorem here, and
   it is NOT the R6 obligation.
2. AFTER READY SUPPLY FORMATION (`ready_supplies_bind_correspondingly`): two Ready supplies of
   the SAME counted values in the SAME order — formed at any two states, so at DIFFERENT
   addresses with different heaps — bind to the same outcome, the bound environments corresponding
   name for name and cell for cell, and the final states corresponding. Counts are part of the
   values: `(v, 1)` and `(v, 2)` are different supplies.
3. ANY TWO CORRESPONDING SUPPLIES (`patterns_sim`, `select_family_sim`): the general SIMULATION.
   A state relation `R` indexed by an address TABLE (a growing list of corresponding address
   pairs) and two capability records that correspond under it (`CapCorr`: corresponding cells
   give EQUAL VALUE outcomes, EQUAL CALLABLE outcomes and corresponding META outcomes, and
   corresponding allocations return a new corresponding pair, each re-establishing `R`) bind every
   head — fixed, collecting, nested structural, literal, META and repeated-name patterns, in
   either mode — correspondingly. This is a heap-RENAMING theorem: no heap, address or memo
   history is equated, only related. `HeapCorr` is the production instance: a partial
   bijection of addresses between Ready/collector cells with corresponding contents, for which
   the production allocator `allocateNeed`, the production META capability `NeedPlan.reference`
   and the production VALUE shell `NeedDemand.step` on Ready cells meet `CapCorr` as KERNEL
   theorems (`heap_corr_capabilities`). Two premises stay explicit there: the CALLABLE channel
   (`projectNeedCallable` is `partial`) and the recursive collector edge (`demandNeedRecursive`
   is `partial`; the binder never demands a collector it allocates on a validated signature,
   because collecting names are never repeated).

BOUNDARIES THE PREMISES MAKE EXPLICIT (and the guards in `SupplyCorrespondenceGuards.lean`
witness):

* a Ready cell projects NO callable identity, while a written algorithm reference does even when
  their VALUES are equal — `CapCorr.callable` fails between them, and a repeated name can then
  retain a different representative (lost CALLABLE channel);
* a META capture distinguishes a supplied written call (it reifies) from its already evaluated
  result (a Ready cell refuses with `metaRefusal`) — `CapCorr.reference` fails between them; the
  capability `NeedCapabilities.reference` is never erased;
* argument-view and collector forwarding transport ORIGINAL cells (`NeedSupply.slot`), which this
  simulation relates only if the transported cells themselves correspond — a value copy is a
  different, Ready, cell;
* suspended expression cells are NOT in `HeapCorr`: relating a suspended written argument to a
  Ready one needs their VALUE demands to agree, i.e. the evaluator's refinement (R7). The general
  simulation accepts any such relation as a premise; none is proved here.
-/

namespace KatLang.SupplyCorrespondence

/-! ## Tables, relations and the simulation judgement -/

/-- An address table: corresponding address pairs (left run, right run). -/
abbrev Table := List (Nat × Nat)

/-- A table extension: every old pair stays. -/
def Extends (t t' : Table) : Prop := ∀ p ∈ t, p ∈ t'

theorem extends_refl (t : Table) : Extends t t := fun _ h => h

theorem extends_trans {t t' t'' : Table} (h1 : Extends t t') (h2 : Extends t' t'') : Extends t t'' :=
  fun p hp => h2 p (h1 p hp)

theorem extends_cons (t : Table) (p : Nat × Nat) : Extends t (p :: t) := fun _ h => List.mem_cons_of_mem _ h

/-- Corresponding outcomes: two successes related by `P`, or the SAME error. -/
def ResCorr {α β : Type} (P : α → β → Prop) : Except Error α → Except Error β → Prop
  | .ok a, .ok b => P a b
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

/-- A state relation indexed by an address table. -/
abbrev StateRel := Table → EvalState → EvalState → Prop

/-- Two completed runs correspond from table `t`: some extension of `t` relates the final states
    and the outcomes. -/
def RunCorr {α β : Type} (R : StateRel) (P : Table → α → β → Prop) (t : Table)
    (r1 : Except Error α × EvalState) (r2 : Except Error β × EvalState) : Prop :=
  ∃ t', Extends t t' ∧ R t' r1.2 r2.2 ∧ ResCorr (P t') r1.1 r2.1

/-- THE SIMULATION JUDGEMENT: from any two states related at `t`, the two computations' runs
    correspond. -/
def Sim {α β : Type} (R : StateRel) (P : Table → α → β → Prop) (t : Table)
    (x : EvalM α) (y : EvalM β) : Prop :=
  ∀ s1 s2, R t s1 s2 → RunCorr R P t (runEval x s1) (runEval y s2)

theorem sim_pure {α β : Type} (R : StateRel) (P : Table → α → β → Prop) (t : Table) (a : α) (b : β)
    (h : P t a b) : Sim R P t (pure a) (pure b) := by
  intro s1 s2 hR
  exact ⟨t, extends_refl t, by simpa using hR, by simpa [ResCorr] using h⟩

theorem sim_throw {α β : Type} (R : StateRel) (P : Table → α → β → Prop) (t : Table) (e : Error) :
    Sim R P t (throw e : EvalM α) (throw e : EvalM β) := by
  intro s1 s2 hR
  exact ⟨t, extends_refl t, by simpa using hR, by simp [ResCorr]⟩

theorem sim_bind {α β γ δ : Type} (R : StateRel) (P : Table → α → β → Prop)
    (Q : Table → γ → δ → Prop) (t : Table) (x : EvalM α) (y : EvalM β)
    (f : α → EvalM γ) (g : β → EvalM δ) (hxy : Sim R P t x y)
    (hfg : ∀ t' a b, Extends t t' → P t' a b → Sim R Q t' (f a) (g b)) :
    Sim R Q t (x >>= f) (y >>= g) := by
  intro s1 s2 hR
  obtain ⟨t1, e1, r1, c1⟩ := hxy s1 s2 hR
  simp only [runEval_bind]
  rcases h1 : runEval x s1 with ⟨e | a, u1⟩ <;> rcases h2 : runEval y s2 with ⟨e' | b, u2⟩ <;>
    rw [h1, h2] at c1 r1 <;> simp only [ResCorr] at c1 <;> simp only [thenRun_ok, thenRun_error]
  · subst c1; exact ⟨t1, e1, r1, by simp [ResCorr]⟩
  · obtain ⟨t2, e2, r2, c2⟩ := hfg t1 a b e1 c1 u1 u2 r1
    exact ⟨t2, extends_trans e1 e2, r2, c2⟩

theorem sim_mono {α β : Type} (R : StateRel) (P Q : Table → α → β → Prop) (t : Table)
    (x : EvalM α) (y : EvalM β) (h : Sim R P t x y) (hPQ : ∀ t a b, P t a b → Q t a b) :
    Sim R Q t x y := by
  intro s1 s2 hR
  obtain ⟨t', e, r, c⟩ := h s1 s2 hR
  refine ⟨t', e, r, ?_⟩
  revert c
  cases (runEval x s1).1 <;> cases (runEval y s2).1 <;> simp only [ResCorr] <;> first | exact id | exact hPQ _ _ _

/-- The two runs of an EQUAL-outcome simulation, split into their two cases. -/
theorem sim_eq_cases {α : Type} {R : StateRel} {t : Table} {x y : EvalM α}
    (h : Sim R (fun _ v w => v = w) t x y) {s1 s2 : EvalState} (hR : R t s1 s2) :
    (∃ t' e u1 u2, Extends t t' ∧ R t' u1 u2 ∧ runEval x s1 = (.error e, u1) ∧ runEval y s2 = (.error e, u2)) ∨
    (∃ t' v u1 u2, Extends t t' ∧ R t' u1 u2 ∧ runEval x s1 = (.ok v, u1) ∧ runEval y s2 = (.ok v, u2)) := by
  obtain ⟨t', e, r, c⟩ := h s1 s2 hR
  rcases h1 : runEval x s1 with ⟨e1 | v1, u1⟩ <;> rcases h2 : runEval y s2 with ⟨e2 | v2, u2⟩ <;>
    rw [h1, h2] at c r <;> simp only [ResCorr] at c
  · subst c; exact Or.inl ⟨t', e1, u1, u2, e, r, rfl, rfl⟩
  · subst c; exact Or.inr ⟨t', v1, u1, u2, e, r, rfl, rfl⟩

/-! ## A pointwise relation of two lists -/

/-- Two lists related position by position (core Lean has no `List.Forall₂`). -/
inductive Rel2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Rel2 r [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : r a b → Rel2 r as bs → Rel2 r (a :: as) (b :: bs)

theorem Rel2.imp {α β : Type} {r s : α → β → Prop} (h : ∀ a b, r a b → s a b) :
    ∀ {x : List α} {y : List β}, Rel2 r x y → Rel2 s x y
  | _, _, .nil => .nil
  | _, _, .cons hab hr => .cons (h _ _ hab) (Rel2.imp h hr)

theorem Rel2.length_eq {α β : Type} {r : α → β → Prop} :
    ∀ {x : List α} {y : List β}, Rel2 r x y → x.length = y.length
  | _, _, .nil => rfl
  | _, _, .cons _ hr => by simp [Rel2.length_eq hr]

theorem Rel2.append {α β : Type} {r : α → β → Prop} :
    ∀ {x : List α} {y : List β} {x' : List α} {y' : List β}, Rel2 r x y → Rel2 r x' y' →
      Rel2 r (x ++ x') (y ++ y')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hab hr, h => .cons hab (Rel2.append hr h)

theorem Rel2.reverse_aux {α β : Type} {r : α → β → Prop} :
    ∀ {x : List α} {y : List β}, Rel2 r x y → Rel2 r x.reverse y.reverse
  | _, _, .nil => .nil
  | _, _, .cons hab hr => by
      simp only [List.reverse_cons]
      exact Rel2.append (Rel2.reverse_aux hr) (.cons hab .nil)

theorem Rel2.of_map {α β γ : Type} {r : α → β → Prop} (f : γ → α) (g : γ → β) :
    ∀ (l : List γ), (∀ x ∈ l, r (f x) (g x)) → Rel2 r (l.map f) (l.map g)
  | [], _ => .nil
  | x :: xs, h => .cons (h x List.mem_cons_self) (Rel2.of_map f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-! ## Corresponding cells, sources, suspensions and environments -/

/-- Two addresses correspond under the table. -/
def Addr (t : Table) (a b : Nat) : Prop := (a, b) ∈ t

/-- Two cell lists correspond position by position. -/
def Cells (t : Table) (c1 c2 : List Nat) : Prop := Rel2 (Addr t) c1 c2

theorem cells_mono {t t' : Table} (h : Extends t t') {c1 c2 : List Nat} (hc : Cells t c1 c2) :
    Cells t' c1 c2 :=
  Rel2.imp (fun _ _ hab => h _ hab) hc

theorem cells_length {t : Table} {c1 c2 : List Nat} (h : Cells t c1 c2) : c1.length = c2.length :=
  Rel2.length_eq h

/-- Corresponding suspensions of the two cells the binder may allocate: Ready cells of the SAME
    counted value, or collectors over corresponding slices. Expression suspensions never
    correspond here. -/
def SuspCorr (t : Table) : NeedSuspension → NeedSuspension → Prop
  | .ready v, .ready w => v = w
  | .collector s1, .collector s2 => Cells t s1 s2
  | _, _ => False

theorem susp_mono {t t' : Table} (h : Extends t t') : ∀ {s1 s2 : NeedSuspension},
    SuspCorr t s1 s2 → SuspCorr t' s1 s2
  | .ready _, .ready _, hs => hs
  | .collector _, .collector _, hs => cells_mono h hs
  | .expression _ _ _, .expression _ _ _, hs => hs.elim
  | .expression _ _ _, .ready _, hs => hs.elim
  | .expression _ _ _, .collector _, hs => hs.elim
  | .ready _, .expression _ _ _, hs => hs.elim
  | .ready _, .collector _, hs => hs.elim
  | .collector _, .expression _ _ _, hs => hs.elim
  | .collector _, .ready _, hs => hs.elim

/-- Corresponding sources of one pattern. -/
def SrcCorr (t : Table) : NeedSource Nat → NeedSource Nat → Prop
  | .cell a, .cell b => Addr t a b
  | .collector s1, .collector s2 => Cells t s1 s2
  | .missing, .missing => True
  | _, _ => False

theorem src_mono {t t' : Table} (h : Extends t t') : ∀ {x y : NeedSource Nat},
    SrcCorr t x y → SrcCorr t' x y
  | .cell _, .cell _, hs => h _ hs
  | .collector _, .collector _, hs => cells_mono h hs
  | .missing, .missing, _ => trivial
  | .cell _, .collector _, hs => hs.elim
  | .cell _, .missing, hs => hs.elim
  | .collector _, .cell _, hs => hs.elim
  | .collector _, .missing, hs => hs.elim
  | .missing, .cell _, hs => hs.elim
  | .missing, .collector _, hs => hs.elim

theorem srcs_mono {t t' : Table} (h : Extends t t') {x y : List (NeedSource Nat)}
    (hs : Rel2 (SrcCorr t) x y) : Rel2 (SrcCorr t') x y :=
  Rel2.imp (fun _ _ hab => src_mono h hab) hs

/-- Corresponding binding environments: the same names in the same order, at corresponding cells. -/
def EnvCorr (t : Table) (e1 e2 : NeedEnv) : Prop :=
  Rel2 (fun x y => x.1 = y.1 ∧ Addr t x.2 y.2) e1 e2

theorem env_mono {t t' : Table} (h : Extends t t') {e1 e2 : NeedEnv} (he : EnvCorr t e1 e2) :
    EnvCorr t' e1 e2 :=
  Rel2.imp (fun _ _ hab => ⟨hab.1, h _ hab.2⟩) he

/-- Corresponding binder outcomes: both non-matches, or corresponding environments. -/
def OptEnvCorr (t : Table) : Option NeedEnv → Option NeedEnv → Prop
  | none, none => True
  | some e1, some e2 => EnvCorr t e1 e2
  | _, _ => False

theorem env_lookup (n : Ident) {t : Table} : ∀ {e1 e2 : NeedEnv}, EnvCorr t e1 e2 →
    (lookupAssoc n e1 = none ∧ lookupAssoc n e2 = none) ∨
      ∃ a b, lookupAssoc n e1 = some a ∧ lookupAssoc n e2 = some b ∧ Addr t a b
  | [], [], Rel2.nil => Or.inl ⟨rfl, rfl⟩
  | (k1, a1) :: r1, (k2, a2) :: r2, Rel2.cons ⟨hk, ha⟩ hr => by
      simp only at hk ha
      subst hk
      simp only [lookupAssoc]
      by_cases hn : n = k1
      · simp only [hn, ↓reduceIte]; exact Or.inr ⟨a1, a2, rfl, rfl, ha⟩
      · simp only [hn, ↓reduceIte]; exact env_lookup n hr

theorem env_filter (n : Ident) {t : Table} : ∀ {e1 e2 : NeedEnv}, EnvCorr t e1 e2 →
    EnvCorr t (e1.filter (fun entry => entry.fst != n)) (e2.filter (fun entry => entry.fst != n))
  | [], [], Rel2.nil => Rel2.nil
  | (k1, a1) :: r1, (k2, a2) :: r2, Rel2.cons ⟨hk, ha⟩ hr => by
      simp only at hk ha
      subst hk
      by_cases hn : k1 = n
      · simp only [List.filter_cons, hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact env_filter n hr
      · have hb : (k1 != n) = true := by simpa using hn
        simp only [List.filter_cons, hb, ↓reduceIte]
        exact Rel2.cons ⟨rfl, ha⟩ (env_filter n hr)

theorem env_rebind (n : Ident) {t : Table} {e1 e2 : NeedEnv} {a1 a2 : Nat} (he : EnvCorr t e1 e2)
    (ha : Addr t a1 a2) :
    EnvCorr t (e1.filter (fun entry => entry.fst != n) ++ [(n, a1)])
      (e2.filter (fun entry => entry.fst != n) ++ [(n, a2)]) :=
  Rel2.append (env_filter n he) (Rel2.cons ⟨rfl, ha⟩ Rel2.nil)

/-! ## Corresponding capability records -/

/-- TWO CAPABILITY RECORDS CORRESPOND under the state relation `R`: on corresponding cells their
    VALUE demands and CALLABLE projections have EQUAL outcomes, their META reifications and their
    allocations of corresponding suspensions return corresponding cells, and each re-establishes
    `R` at some extension of the table. -/
structure CapCorr (R : StateRel) (k1 k2 : NeedCapabilities EvalM) : Prop where
  value : ∀ t a1 a2, Addr t a1 a2 → Sim R (fun _ v w => v = w) t (k1.value a1) (k2.value a2)
  callable : ∀ t a1 a2, Addr t a1 a2 → Sim R (fun _ v w => v = w) t (k1.callable a1) (k2.callable a2)
  allocate : ∀ t s1 s2, SuspCorr t s1 s2 → Sim R Addr t (k1.allocate s1) (k2.allocate s2)
  reference : ∀ t a1 a2, Addr t a1 a2 → Sim R Addr t (k1.reference a1) (k2.reference a2)

/-! ## The simulation of the binder core -/

theorem verdict_corr (n : Ident) {t : Table} {b1 b2 : NeedEnv} {a1 a2 : Nat} (hb : EnvCorr t b1 b2)
    (ha : Addr t a1 a2) (family : Bool) (first second : Option Algorithm) :
    ResCorr (OptEnvCorr t) (repeatedVerdict n a1 b1 family first second)
      (repeatedVerdict n a2 b2 family first second) := by
  have hr := env_rebind n hb ha
  unfold repeatedVerdict
  rcases first with _ | x <;> rcases second with _ | y <;> simp [ResCorr, OptEnvCorr, hb, hr]
  · by_cases hs : sameRepeatedCallableIdentity x y = true
    · simp [hs, hb]
    · cases family <;> simp [hs]

/-- ONE NAME OCCURRENCE, simulated: corresponding cells and environments give corresponding runs,
    repeated or not, in either mode. -/
theorem name_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
    (name : Ident) (a1 a2 : Nat) (repeated : List Ident) (b1 b2 : NeedEnv) (family : Bool) (t : Table)
    (ha : Addr t a1 a2) (hb : EnvCorr t b1 b2) :
    Sim R OptEnvCorr t (NeedBinder.bindName k1 name a1 repeated b1 family)
      (NeedBinder.bindName k2 name a2 repeated b2 family) := by
  by_cases hr : repeated.contains name = true
  · intro s1 s2 hR
    rw [repeated_name_binding k1 name a1 repeated b1 family s1 hr,
      repeated_name_binding k2 name a2 repeated b2 family s2 hr]
    rcases sim_eq_cases (hk.value t a1 a2 ha) hR with
      ⟨t1, e, u1, u2, x1, r1, h1, h2⟩ | ⟨t1, v, u1, u2, x1, r1, h1, h2⟩
    · simp only [h1, h2]; exact ⟨t1, x1, r1, by simp [ResCorr]⟩
    · simp only [h1, h2]
      have hb1 := env_mono x1 hb
      rcases env_lookup name hb1 with ⟨l1, l2⟩ | ⟨p1, p2, l1, l2, hp⟩
      · simp only [l1, l2]
        exact ⟨t1, x1, r1, by simpa [ResCorr, OptEnvCorr] using env_rebind name hb1 (x1 _ ha)⟩
      · simp only [l1, l2]
        rcases sim_eq_cases (hk.value t1 p1 p2 hp) r1 with
          ⟨t2, e, w1, w2, x2, r2, h3, h4⟩ | ⟨t2, before, w1, w2, x2, r2, h3, h4⟩
        · simp only [h3, h4]; exact ⟨t2, extends_trans x1 x2, r2, by simp [ResCorr]⟩
        · simp only [h3, h4]
          by_cases hbv : (!(before == v)) = true
          · simp only [hbv, ↓reduceIte]
            cases family <;> exact ⟨t2, extends_trans x1 x2, r2, by simp [ResCorr, OptEnvCorr]⟩
          · simp only [hbv, ↓reduceIte, Bool.false_eq_true]
            rcases sim_eq_cases (hk.callable t2 p1 p2 (x2 _ hp)) r2 with
              ⟨t3, e, z1, z2, x3, r3, h5, h6⟩ | ⟨t3, first, z1, z2, x3, r3, h5, h6⟩
            · simp only [h5, h6]
              exact ⟨t3, extends_trans x1 (extends_trans x2 x3), r3, by simp [ResCorr]⟩
            · simp only [h5, h6]
              have ha3 : Addr t3 a1 a2 := x3 _ (x2 _ (x1 _ ha))
              rcases sim_eq_cases (hk.callable t3 a1 a2 ha3) r3 with
                ⟨t4, e, q1, q2, x4, r4, h7, h8⟩ | ⟨t4, second, q1, q2, x4, r4, h7, h8⟩
              · simp only [h7, h8]
                exact ⟨t4, extends_trans x1 (extends_trans x2 (extends_trans x3 x4)), r4, by simp [ResCorr]⟩
              · simp only [h7, h8]
                refine ⟨t4, extends_trans x1 (extends_trans x2 (extends_trans x3 x4)), r4, ?_⟩
                exact verdict_corr name (env_mono (extends_trans x2 (extends_trans x3 x4)) hb1)
                  (x4 _ ha3) family first second
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k1 name a1 repeated b1 family hr',
      BinderCore.core_plain_name_is_pure k2 name a2 repeated b2 family hr']
    exact sim_pure R OptEnvCorr t _ _ (env_rebind name hb ha)

theorem ready_loop_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2) :
    ∀ (items : List Result) (acc1 acc2 : List Nat) (t : Table), Cells t acc1 acc2 →
      Sim R Cells t (List.mapM.loop (fun item => k1.allocate (.ready (item, Result.valueCount item))) items acc1)
        (List.mapM.loop (fun item => k2.allocate (.ready (item, Result.valueCount item))) items acc2)
  | [], acc1, acc2, t, h => by
      simp only [List.mapM.loop]
      exact sim_pure R Cells t _ _ (Rel2.reverse_aux h)
  | item :: rest, acc1, acc2, t, h => by
      simp only [List.mapM.loop]
      refine sim_bind R Addr Cells t _ _ _ _ (hk.allocate t _ _ (by simp [SuspCorr])) ?_
      intro t1 b1 b2 x1 hb
      exact ready_loop_sim R k1 k2 hk rest (b1 :: acc1) (b2 :: acc2) t1 (Rel2.cons hb (cells_mono x1 h))

/-- READY ALLOCATION, simulated: the same items allocate corresponding cells, in order. -/
theorem ready_cells_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
    (items : List Result) (t : Table) : Sim R Cells t (readyCells k1 items) (readyCells k2 items) := by
  unfold readyCells List.mapM
  exact ready_loop_sim R k1 k2 hk items [] [] t Rel2.nil

theorem gate_sim (R : StateRel) (ps : List NeedPattern) (n : Nat) (family : Bool) (t : Table)
    (x y : EvalM (Option NeedEnv)) (h : Sim R OptEnvCorr t x y) :
    Sim R OptEnvCorr t (NeedBinder.cardinalityGate ps n family x)
      (NeedBinder.cardinalityGate ps n family y) := by
  unfold NeedBinder.cardinalityGate
  split
  · cases family
    · exact sim_throw R OptEnvCorr t _
    · exact sim_pure R OptEnvCorr t none none trivial
  · exact h

theorem source_items_mem {α : Type} (ps : List NeedPattern) (cells : List α) (src : NeedSource α)
    (h : src ∈ needLevelSources ps cells) : ∀ x ∈ src.items, x ∈ cells := by
  simp only [needLevelSources, List.mem_map, List.mem_range] at h
  obtain ⟨i, -, rfl⟩ := h
  intro x hx
  unfold needSourceAt at hx
  split at hx
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  · split at hx
    · rename_i c hc
      simp only [NeedSource.items, List.mem_singleton] at hx
      subst hx
      exact List.mem_of_getElem? hc
    · simp [NeedSource.items] at hx

theorem zip_addr {t : Table} : ∀ {c1 c2 : List Nat}, Cells t c1 c2 → ∀ p ∈ c1.zip c2, Addr t p.1 p.2
  | [], [], Rel2.nil => by simp
  | a :: as, b :: bs, Rel2.cons hab hr => by
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hab
      · exact zip_addr hr p hp

/-- ALLOCATION, simulated: corresponding supplies give each pattern corresponding sources. -/
theorem level_sources_corr (ps : List NeedPattern) {t : Table} {c1 c2 : List Nat} (hc : Cells t c1 c2) :
    Rel2 (SrcCorr t) (needLevelSources ps c1) (needLevelSources ps c2) := by
  have hlen := cells_length hc
  have e1 : needLevelSources ps c1 = (needLevelSources ps (c1.zip c2)).map (NeedSource.map Prod.fst) := by
    rw [← need_level_sources_are_parametric, List.map_fst_zip (Nat.le_of_eq hlen)]
  have e2 : needLevelSources ps c2 = (needLevelSources ps (c1.zip c2)).map (NeedSource.map Prod.snd) := by
    rw [← need_level_sources_are_parametric, List.map_snd_zip (Nat.le_of_eq hlen.symm)]
  have hz := zip_addr hc
  rw [e1, e2]
  apply Rel2.of_map
  intro src hsrc
  have hmem := source_items_mem ps (c1.zip c2) src hsrc
  cases src with
  | cell p => exact hz p (hmem p (by simp [NeedSource.items]))
  | collector slice =>
    simp only [NeedSource.map, SrcCorr, Cells]
    exact Rel2.of_map _ _ slice (fun p hp => hz p (hmem p (by simpa [NeedSource.items] using hp)))
  | missing => trivial

theorem source_address_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
    (t : Table) : ∀ (x y : NeedSource Nat), SrcCorr t x y →
      Sim R Addr t (NeedBinder.sourceAddress k1.allocate x) (NeedBinder.sourceAddress k2.allocate y)
  | .cell a, .cell b, h => sim_pure R Addr t a b h
  | .collector s1, .collector s2, h => hk.allocate t (.collector s1) (.collector s2) h
  | .missing, .missing, _ => sim_throw R Addr t _
  | .cell _, .collector _, h => h.elim
  | .cell _, .missing, h => h.elim
  | .collector _, .cell _, h => h.elim
  | .collector _, .missing, h => h.elim
  | .missing, .cell _, h => h.elim
  | .missing, .collector _, h => h.elim

theorem head_src_corr {t : Table} {x y : List (NeedSource Nat)} (h : Rel2 (SrcCorr t) x y) :
    SrcCorr t (x.headD .missing) (y.headD .missing) ∧ Rel2 (SrcCorr t) x.tail y.tail := by
  cases h with
  | nil => exact ⟨trivial, Rel2.nil⟩
  | cons hab hr => exact ⟨hab, hr⟩

theorem structural_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
    (p : NeedPattern) (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps)
    (a1 a2 : Nat) (repeated : List Ident) (b1 b2 : NeedEnv) (family : Bool) (t : Table)
    (ha : Addr t a1 a2) (hb : EnvCorr t b1 b2)
    (ih : ∀ (t' : Table) (c1 c2 : List Nat) (e1 e2 : NeedEnv), Extends t t' → Cells t' c1 c2 → EnvCorr t' e1 e2 →
      Sim R OptEnvCorr t' (NeedBinder.bindSources k1 ps (needLevelSources ps c1) repeated e1 family)
        (NeedBinder.bindSources k2 ps (needLevelSources ps c2) repeated e2 family)) :
    Sim R OptEnvCorr t (NeedBinder.bindOne k1 p a1 repeated b1 family)
      (NeedBinder.bindOne k2 p a2 repeated b2 family) := by
  rw [bindOne_structural_shape k1 p ps hp, bindOne_structural_shape k2 p ps hp]
  refine sim_bind R (fun _ v w => v = w) OptEnvCorr t _ _ _ _ (hk.value t a1 a2 ha) ?_
  intro t1 v w x1 hvw
  subst hvw
  obtain ⟨value, count⟩ := v
  simp only
  cases structuralItems p value with
  | none =>
    cases family
    · exact sim_throw R OptEnvCorr t1 _
    · exact sim_pure R OptEnvCorr t1 none none trivial
  | some items =>
    simp only
    refine sim_bind R Cells OptEnvCorr t1 _ _ _ _ (ready_cells_sim R k1 k2 hk items t1) ?_
    intro t2 c1 c2 x2 hc
    rw [cells_length hc]
    exact gate_sim R ps c2.length family t2 _ _
      (ih t2 c1 c2 b1 b2 (extends_trans x1 x2) hc (env_mono (extends_trans x1 x2) hb))

mutual
  /-- ONE PATTERN, simulated. -/
  theorem one_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
      (p : NeedPattern) (a1 a2 : Nat) (repeated : List Ident) (b1 b2 : NeedEnv) (family : Bool)
      (t : Table) (ha : Addr t a1 a2) (hb : EnvCorr t b1 b2) :
      Sim R OptEnvCorr t (NeedBinder.bindOne k1 p a1 repeated b1 family)
        (NeedBinder.bindOne k2 p a2 repeated b2 family) := by
    cases p with
    | bind name collecting => exact name_sim R k1 k2 hk name a1 a2 repeated b1 b2 family t ha hb
    | metaRef name =>
      simp only [NeedBinder.bindOne]
      refine sim_bind R Addr OptEnvCorr t _ _ _ _ (hk.reference t a1 a2 ha) ?_
      intro t1 d1 d2 x1 hd
      exact name_sim R k1 k2 hk name d1 d2 repeated b1 b2 family t1 hd (env_mono x1 hb)
    | literal literal =>
      simp only [NeedBinder.bindOne]
      refine sim_bind R (fun _ v w => v = w) OptEnvCorr t _ _ _ _ (hk.value t a1 a2 ha) ?_
      intro t1 v w x1 hvw
      subst hvw
      obtain ⟨value, count⟩ := v
      simp only
      split
      · exact sim_pure R OptEnvCorr t1 _ _ (env_mono x1 hb)
      · exact sim_pure R OptEnvCorr t1 none none trivial
    | sequence ps =>
      exact structural_sim R k1 k2 hk _ ps (Or.inl rfl) a1 a2 repeated b1 b2 family t ha hb
        (fun t' c1 c2 e1 e2 _ hc he => sources_sim R k1 k2 hk ps _ _ repeated e1 e2 family t'
          (level_sources_corr ps hc) he)
    | list ps =>
      exact structural_sim R k1 k2 hk _ ps (Or.inr (Or.inl rfl)) a1 a2 repeated b1 b2 family t ha hb
        (fun t' c1 c2 e1 e2 _ hc he => sources_sim R k1 k2 hk ps _ _ repeated e1 e2 family t'
          (level_sources_corr ps hc) he)
    | unpack ps =>
      exact structural_sim R k1 k2 hk _ ps (Or.inr (Or.inr rfl)) a1 a2 repeated b1 b2 family t ha hb
        (fun t' c1 c2 e1 e2 _ hc he => sources_sim R k1 k2 hk ps _ _ repeated e1 e2 family t'
          (level_sources_corr ps hc) he)

  /-- ONE LEVEL'S PATTERNS, simulated. -/
  theorem sources_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
      (ps : List NeedPattern) (x y : List (NeedSource Nat)) (repeated : List Ident)
      (b1 b2 : NeedEnv) (family : Bool) (t : Table) (hs : Rel2 (SrcCorr t) x y)
      (hb : EnvCorr t b1 b2) :
      Sim R OptEnvCorr t (NeedBinder.bindSources k1 ps x repeated b1 family)
        (NeedBinder.bindSources k2 ps y repeated b2 family) := by
    cases ps with
    | nil => exact sim_pure R OptEnvCorr t (some b1) (some b2) hb
    | cons p rest =>
      simp only [NeedBinder.bindSources]
      obtain ⟨hhead, htail⟩ := head_src_corr hs
      refine sim_bind R Addr OptEnvCorr t _ _ _ _ (source_address_sim R k1 k2 hk t _ _ hhead) ?_
      intro t1 d1 d2 x1 hd
      refine sim_bind R OptEnvCorr OptEnvCorr t1 _ _ _ _
        (one_sim R k1 k2 hk p d1 d2 repeated b1 b2 family t1 hd (env_mono x1 hb)) ?_
      intro t2 o1 o2 x2 ho
      cases o1 with
      | none => cases o2 with
        | none => exact sim_pure R OptEnvCorr t2 none none trivial
        | some _ => exact ho.elim
      | some n1 => cases o2 with
        | none => exact ho.elim
        | some n2 =>
          exact sources_sim R k1 k2 hk rest x.tail y.tail repeated n1 n2 family t2
            (srcs_mono (extends_trans x1 x2) htail) ho
end

/-- A WHOLE HEAD, simulated: corresponding supplies bind to corresponding outcomes — the same
    error, both non-matches, or corresponding environments — in either mode. -/
theorem patterns_sim (R : StateRel) (k1 k2 : NeedCapabilities EvalM) (hk : CapCorr R k1 k2)
    (ps : List NeedPattern) (c1 c2 : List Nat) (family : Bool) (t : Table) (hc : Cells t c1 c2) :
    Sim R OptEnvCorr t (NeedBinder.bindPatterns k1 ps c1 family) (NeedBinder.bindPatterns k2 ps c2 family) := by
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel]
  rw [cells_length hc]
  exact gate_sim R ps c2.length family t _ _
    (sources_sim R k1 k2 hk ps _ _ (needRepeatedNames ps) [] [] family t (level_sources_corr ps hc) Rel2.nil)

/-! ## The clause search, with the activated body as an explicit continuation -/

/-- THE CLAUSE SEARCH, simulated: the same clauses over corresponding supplies try the same
    clauses in the same order; a match in one run is a match in the other with corresponding
    bindings, handed to the two `activate` continuations, which are a PREMISE (the selected
    body's evaluation is outside this module). -/
theorem choose_branch_sim {γ δ : Type} (R : StateRel) (k1 k2 : NeedCapabilities EvalM)
    (hk : CapCorr R k1 k2) (Q : Table → γ → δ → Prop) (calleeName : String)
    (act1 : CondBranch → NeedEnv → EvalM γ) (act2 : CondBranch → NeedEnv → EvalM δ)
    (hact : ∀ t b e1 e2, EnvCorr t e1 e2 → Sim R Q t (act1 b e1) (act2 b e2)) :
    ∀ (bs : List CondBranch) (t : Table) (c1 c2 : List Nat), Cells t c1 c2 →
      Sim R Q t (NeedBinder.chooseBranch k1 c1 calleeName act1 bs)
        (NeedBinder.chooseBranch k2 c2 calleeName act2 bs)
  | [], t, _, _, _ => by
      simp only [NeedBinder.chooseBranch]
      exact sim_throw R Q t _
  | b :: rest, t, c1, c2, hc => by
      simp only [NeedBinder.chooseBranch]
      refine sim_bind R OptEnvCorr Q t _ _ _ _ (patterns_sim R k1 k2 hk _ c1 c2 true t hc) ?_
      intro t1 o1 o2 x1 ho
      cases o1 with
      | none => cases o2 with
        | none => exact choose_branch_sim R k1 k2 hk Q calleeName act1 act2 hact rest t1 c1 c2 (cells_mono x1 hc)
        | some _ => exact ho.elim
      | some e1 => cases o2 with
        | none => exact ho.elim
        | some e2 => exact hact t1 b e1 e2 ho

/-- THE CLAUSE-FAMILY DISPATCHER, simulated (duplicate check, family cardinality, search). -/
theorem select_family_sim {γ δ : Type} (R : StateRel) (k1 k2 : NeedCapabilities EvalM)
    (hk : CapCorr R k1 k2) (Q : Table → γ → δ → Prop) (callee : Algorithm) (calleeName : String)
    (act1 : CondBranch → NeedEnv → EvalM γ) (act2 : CondBranch → NeedEnv → EvalM δ)
    (hact : ∀ t b e1 e2, EnvCorr t e1 e2 → Sim R Q t (act1 b e1) (act2 b e2))
    (t : Table) (c1 c2 : List Nat) (hc : Cells t c1 c2) :
    Sim R Q t (NeedBinder.selectFamily k1 callee c1 calleeName act1)
      (NeedBinder.selectFamily k2 callee c2 calleeName act2) := by
  have hl := cells_length hc
  unfold NeedBinder.selectFamily
  rw [hl]
  by_cases hdup : callee.hasDuplicateBranchPatterns = true
  · simp only [hdup, ↓reduceIte]
    refine sim_bind R (fun _ _ _ => True) Q t _ _ _ _ (sim_throw R _ t _) ?_
    intro t1 _ _ x1 _
    split
    · refine sim_bind R (fun _ _ _ => True) Q t1 _ _ _ _ (sim_throw R _ t1 _) ?_
      intro t2 _ _ x2 _
      exact choose_branch_sim R k1 k2 hk Q calleeName act1 act2 hact _ t2 c1 c2
        (cells_mono (extends_trans x1 x2) hc)
    · exact choose_branch_sim R k1 k2 hk Q calleeName act1 act2 hact _ t1 c1 c2 (cells_mono x1 hc)
  · simp only [hdup, Bool.false_eq_true, ↓reduceIte]
    split
    · refine sim_bind R (fun _ _ _ => True) Q t _ _ _ _ (sim_throw R _ t _) ?_
      intro t2 _ _ x2 _
      exact choose_branch_sim R k1 k2 hk Q calleeName act1 act2 hact _ t2 c1 c2 (cells_mono x2 hc)
    · exact choose_branch_sim R k1 k2 hk Q calleeName act1 act2 hact _ t c1 c2 hc

/-! ## The production heap correspondence -/

/-- Two cells correspond: corresponding suspensions (equal Ready values, corresponding collector
    slices), the same VALUE state, the same CALLABLE memo and the same plan supply. -/
def CellCorr (t : Table) (c1 c2 : NeedCell) : Prop :=
  SuspCorr t c1.suspension c2.suspension ∧ c1.state = c2.state ∧ c1.callable = c2.callable ∧
    c1.plan = c2.plan

theorem cell_mono {t t' : Table} (h : Extends t t') {c1 c2 : NeedCell} (hc : CellCorr t c1 c2) :
    CellCorr t' c1 c2 :=
  ⟨susp_mono h hc.1, hc.2⟩

/-- THE PRODUCTION HEAP CORRESPONDENCE: every table pair addresses two PRESENT corresponding
    cells, and the table is a partial BIJECTION of addresses (so a cell update on one side is
    mirrored by exactly one update on the other). Expression cells never correspond. -/
def HeapCorr : StateRel := fun t s1 s2 =>
  (∀ p ∈ t, ∃ c1 c2, s1.needs[p.1]? = some c1 ∧ s2.needs[p.2]? = some c2 ∧ CellCorr t c1 c2) ∧
  (∀ p ∈ t, ∀ q ∈ t, p.1 = q.1 ↔ p.2 = q.2)

/-- Any two states correspond under the empty table. -/
theorem heap_corr_empty (s1 s2 : EvalState) : HeapCorr [] s1 s2 :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem valid_of_some {xs : Array NeedCell} {i : Nat} {c : NeedCell} (h : xs[i]? = some c) :
    i < xs.size := by
  by_cases hi : i < xs.size
  · exact hi
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi)] at h; cases h

/-- THE PRODUCTION ALLOCATOR meets the allocation premise: corresponding suspensions are
    allocated at the two heaps' next addresses, which join the table as a new pair. -/
theorem allocate_need_sim (t : Table) (sp1 sp2 : NeedSuspension) (h : SuspCorr t sp1 sp2) :
    Sim HeapCorr Addr t (allocateNeed sp1) (allocateNeed sp2) := by
  intro s1 s2 hR
  obtain ⟨hcells, hbij⟩ := hR
  have run1 : runEval (allocateNeed sp1) s1 =
      (.ok s1.needs.size, { s1 with needs := s1.needs.push { suspension := sp1 } }) := rfl
  have run2 : runEval (allocateNeed sp2) s2 =
      (.ok s2.needs.size, { s2 with needs := s2.needs.push { suspension := sp2 } }) := rfl
  rw [run1, run2]
  have hold : ∀ p ∈ t, p.1 < s1.needs.size ∧ p.2 < s2.needs.size := by
    intro p hp
    obtain ⟨c1, c2, h1, h2, -⟩ := hcells p hp
    exact ⟨valid_of_some h1, valid_of_some h2⟩
  refine ⟨(s1.needs.size, s2.needs.size) :: t, extends_cons _ _, ⟨?_, ?_⟩, List.mem_cons_self⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, Array.getElem?_push_size, Array.getElem?_push_size,
        ⟨susp_mono (extends_cons _ _) h, rfl, rfl, rfl⟩⟩
    · obtain ⟨c1, c2, h1, h2, hc⟩ := hcells p hp
      obtain ⟨l1, l2⟩ := hold p hp
      exact ⟨c1, c2, by simp only [Array.getElem?_push, Nat.ne_of_lt l1, ↓reduceIte, h1],
        by simp only [Array.getElem?_push, Nat.ne_of_lt l2, ↓reduceIte, h2], cell_mono (extends_cons _ _) hc⟩
  · intro p hp q hq
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨l1, l2⟩ := hold q hq
      exact ⟨fun e => absurd e (Nat.ne_of_gt l1), fun e => absurd e (Nat.ne_of_gt l2)⟩
    · obtain ⟨l1, l2⟩ := hold p hp
      exact ⟨fun e => absurd e (Nat.ne_of_lt l1), fun e => absurd e (Nat.ne_of_lt l2)⟩
    · exact hbij p hp q hq

theorem no_plan_of_corr {t : Table} : ∀ {sp1 sp2 : NeedSuspension}, SuspCorr t sp1 sp2 →
    NeedPlan.ofSuspension? sp1 = none ∧ NeedPlan.ofSuspension? sp2 = none
  | .ready _, .ready _, _ => ⟨rfl, rfl⟩
  | .collector _, .collector _, _ => ⟨rfl, rfl⟩
  | .expression _ _ _, _, h => by cases h
  | .ready _, .expression _ _ _, h => by cases h
  | .ready _, .collector _, h => by cases h
  | .collector _, .expression _ _ _, h => by cases h
  | .collector _, .ready _, h => by cases h

/-- THE PRODUCTION META CAPABILITY meets the reference premise: corresponding (Ready or
    collector) cells are not supplied call computations, so both captures refuse with the same
    `metaRefusal` and leave both states unchanged. -/
theorem reference_sim (t : Table) (a1 a2 : Nat) (ha : Addr t a1 a2) :
    Sim HeapCorr Addr t (NeedPlan.reference a1) (NeedPlan.reference a2) := by
  intro s1 s2 hR
  obtain ⟨c1, c2, h1, h2, hc⟩ := hR.1 _ ha
  obtain ⟨n1, n2⟩ := no_plan_of_corr hc.1
  have r1 : NeedPlan.reifyResult s1.needs a1 = .error NeedPlan.metaRefusal := by
    simp [NeedPlan.reifyResult, NeedPlan.shapeAt?, h1, n1]
  have r2 : NeedPlan.reifyResult s2.needs a2 = .error NeedPlan.metaRefusal := by
    simp [NeedPlan.reifyResult, NeedPlan.shapeAt?, h2, n2]
  have e1 : runEval (NeedPlan.reference a1) s1 = (.error NeedPlan.metaRefusal, s1) := by
    show (NeedPlan.reference a1).runState s1 = _
    rw [KatLang.CallReferenceLaws.reference_run, r1]
  have e2 : runEval (NeedPlan.reference a2) s2 = (.error NeedPlan.metaRefusal, s2) := by
    show (NeedPlan.reference a2).runState s2 = _
    rw [KatLang.CallReferenceLaws.reference_run, r2]
  rw [e1, e2]
  exact ⟨t, extends_refl t, hR, rfl⟩

/-- Updating two corresponding cells by the same correspondence-preserving function preserves
    the heap correspondence (the table is a bijection). -/
theorem heap_modify (t : Table) (s1 s2 : EvalState) (a1 a2 : Nat) (f : NeedCell → NeedCell)
    (hR : HeapCorr t s1 s2) (ha : Addr t a1 a2) (hf : ∀ c1 c2, CellCorr t c1 c2 → CellCorr t (f c1) (f c2)) :
    HeapCorr t { s1 with needs := s1.needs.modify a1 f } { s2 with needs := s2.needs.modify a2 f } := by
  refine ⟨?_, hR.2⟩
  intro p hp
  obtain ⟨c1, c2, h1, h2, hc⟩ := hR.1 p hp
  have hiff := hR.2 (a1, a2) ha p hp
  simp only at hiff
  by_cases e : a1 = p.1
  · have e' : a2 = p.2 := hiff.mp e
    exact ⟨f c1, f c2, by simp [Array.getElem?_modify, e, h1], by simp [Array.getElem?_modify, e', h2], hf _ _ hc⟩
  · have e' : ¬ a2 = p.2 := fun h => e (hiff.mpr h)
    exact ⟨c1, c2, by simp [Array.getElem?_modify, e, h1], by simp [Array.getElem?_modify, e', h2], hc⟩

theorem state_update_corr (t : Table) (st : NeedState) :
    ∀ c1 c2, CellCorr t c1 c2 → CellCorr t { c1 with state := st } { c2 with state := st } :=
  fun _ _ hc => ⟨hc.1, rfl, hc.2.2.1, hc.2.2.2⟩

theorem map_eq_bind {α β : Type} (f : α → β) (x : EvalM α) : (f <$> x) = (x >>= fun a => pure (f a)) := rfl

theorem loop_eq_sim {γ : Type} (R : StateRel) (f : Nat → EvalM γ)
    (hf : ∀ t b1 b2, Addr t b1 b2 → Sim R (fun _ v w => v = w) t (f b1) (f b2)) :
    ∀ (xs1 xs2 : List Nat) (acc : List γ) (t : Table), Cells t xs1 xs2 →
      Sim R (fun _ v w => v = w) t (List.mapM.loop f xs1 acc) (List.mapM.loop f xs2 acc)
  | [], [], acc, t, _ => by simp only [List.mapM.loop]; exact sim_pure R _ t _ _ rfl
  | x :: xs, y :: ys, acc, t, Rel2.cons hxy hr => by
      simp only [List.mapM.loop]
      refine sim_bind R (fun _ v w => v = w) _ t _ _ _ _ (hf t x y hxy) ?_
      intro t1 b1 b2 x1 hb
      subst hb
      exact loop_eq_sim R f hf xs ys (b1 :: acc) t1 (cells_mono x1 hr)

theorem materialize_sim (recur : Nat → EvalM CountedResult)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (t : Table) (sl1 sl2 : List Nat) (h : Cells t sl1 sl2) :
    Sim HeapCorr (fun _ v w => v = w) t (NeedDemand.materialize recur sl1) (NeedDemand.materialize recur sl2) := by
  unfold NeedDemand.materialize List.mapM
  refine sim_bind HeapCorr (fun _ v w => v = w) _ t _ _ _ _ ?_ ?_
  · refine loop_eq_sim HeapCorr (fun a => Prod.fst <$> recur a) ?_ sl1 sl2 [] t h
    intro t' b1 b2 hb
    rw [map_eq_bind, map_eq_bind]
    refine sim_bind HeapCorr (fun _ v w => v = w) _ t' _ _ _ _ (hrec t' b1 b2 hb) ?_
    intro t'' v w _ hvw
    subst hvw
    exact sim_pure HeapCorr _ t'' _ _ rfl
  · intro t1 v w _ hvw
    subst hvw
    exact sim_pure HeapCorr _ t1 _ _ rfl

theorem suspended_value_sim (ev1 ev2 : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur : Nat → EvalM CountedResult)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (t : Table) (a1 a2 : Nat) :
    ∀ (sp1 sp2 : NeedSuspension), SuspCorr t sp1 sp2 →
      Sim HeapCorr (fun _ v w => v = w) t (NeedDemand.suspendedValue ev1 route recur a1 sp1)
        (NeedDemand.suspendedValue ev2 route recur a2 sp2)
  | .ready v, .ready w, h => by
      simp only [SuspCorr] at h; subst h
      exact sim_pure HeapCorr _ t _ _ rfl
  | .collector sl1, .collector sl2, h => materialize_sim recur hrec t sl1 sl2 h
  | .expression _ _ _, _, h => by cases h
  | .ready _, .expression _ _ _, h => by cases h
  | .ready _, .collector _, h => by cases h
  | .collector _, .expression _ _ _, h => by cases h
  | .collector _, .ready _, h => by cases h

theorem res_corr_eq {α : Type} {o1 o2 : Except Error α} (h : ResCorr (fun v w => v = w) o1 o2) : o1 = o2 := by
  cases o1 <;> cases o2 <;> simp_all [ResCorr]

/-- THE PRODUCTION VALUE SHELL meets the VALUE premise on corresponding cells: `NeedDemand.step`
    (the one shell of the public `demandNeed` and of the recursive driver) returns a completed
    outcome unchanged, reports a cycle on an evaluating cell, and on a suspended Ready cell
    publishes its value — in both runs alike. A collector cell's materialization goes through
    the recursive edge `recur`, whose correspondence is the premise `hrec`. -/
theorem step_sim (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur : Nat → EvalM CountedResult)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (t : Table) (a1 a2 : Nat) (ha : Addr t a1 a2) :
    Sim HeapCorr (fun _ v w => v = w) t (NeedDemand.step (ev a1) route recur a1) (NeedDemand.step (ev a2) route recur a2) := by
  intro s1 s2 hR
  obtain ⟨c1, c2, h1, h2, hc⟩ := hR.1 _ ha
  obtain ⟨hsusp, hst, -, -⟩ := hc
  cases hs : c1.state with
  | completed o =>
    have hs2 : c2.state = .completed o := hst ▸ hs
    have e1 : runEval (NeedDemand.step (ev a1) route recur a1) s1 = (o, s1) :=
      KatLang.NeedControl.Memo.completed_sticky (ev a1) route recur a1 s1 c1 o h1 hs
    have e2 : runEval (NeedDemand.step (ev a2) route recur a2) s2 = (o, s2) :=
      KatLang.NeedControl.Memo.completed_sticky (ev a2) route recur a2 s2 c2 o h2 hs2
    rw [e1, e2]
    exact ⟨t, extends_refl t, hR, by cases o <;> simp [ResCorr]⟩
  | evaluating =>
    have hs2 : c2.state = .evaluating := hst ▸ hs
    have e1 : runEval (NeedDemand.step (ev a1) route recur a1) s1 = (.error .demandCycle, s1) :=
      KatLang.NeedControl.Production.evaluating_cycle (ev a1) route recur a1 s1 c1 h1 hs
    have e2 : runEval (NeedDemand.step (ev a2) route recur a2) s2 = (.error .demandCycle, s2) :=
      KatLang.NeedControl.Production.evaluating_cycle (ev a2) route recur a2 s2 c2 h2 hs2
    rw [e1, e2]
    exact ⟨t, extends_refl t, hR, rfl⟩
  | suspended =>
    have hs2 : c2.state = .suspended := hst ▸ hs
    have hR' := heap_modify t s1 s2 a1 a2 (fun c => { c with state := .evaluating }) hR ha
      (state_update_corr t .evaluating)
    obtain ⟨t1, x1, r1, c⟩ := suspended_value_sim (ev a1) (ev a2) route recur hrec t a1 a2 _ _ hsusp _ _ hR'
    have ho := res_corr_eq c
    rcases hv1 : runEval (NeedDemand.suspendedValue (ev a1) route recur a1 c1.suspension)
        { s1 with needs := s1.needs.modify a1 (fun c => { c with state := .evaluating }) } with ⟨o1, u1⟩
    rcases hv2 : runEval (NeedDemand.suspendedValue (ev a2) route recur a2 c2.suspension)
        { s2 with needs := s2.needs.modify a2 (fun c => { c with state := .evaluating }) } with ⟨o2, u2⟩
    rw [hv1, hv2] at ho r1
    simp only at ho r1
    subst ho
    have e1 := KatLang.NeedControl.Memo.suspended_retains_state (ev a1) route recur a1 s1 u1 c1 o1 h1 hs hv1
    have e2 := KatLang.NeedControl.Memo.suspended_retains_state (ev a2) route recur a2 s2 u2 c2 o1 h2 hs2 hv2
    show RunCorr HeapCorr _ t ((NeedDemand.step (ev a1) route recur a1).runState s1)
      ((NeedDemand.step (ev a2) route recur a2).runState s2)
    rw [e1, e2]
    refine ⟨t1, x1, heap_modify t1 u1 u2 a1 a2 _ r1 (x1 _ ha) (state_update_corr t1 _), ?_⟩
    cases o1 <;> simp [ResCorr]

/-- THE PRODUCTION CAPABILITIES CORRESPOND under `HeapCorr`: the binder's allocator
    `allocateNeed` and META capability `NeedPlan.reference` unconditionally, its VALUE shell
    `NeedDemand.step` given the recursive collector edge's correspondence, and its CALLABLE
    channel given as a premise (`projectNeedCallable` is `partial`; that it answers a Ready or
    collector cell from that cell's memo and suspension alone is a fact of its source). -/
theorem heap_corr_capabilities (channels : NeedChannels)
    (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur : Nat → EvalM CountedResult) (hv : channels.value = fun a => NeedDemand.step (ev a) route recur a)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (hcal : ∀ t b1 b2, Addr t b1 b2 →
      Sim HeapCorr (fun _ v w => v = w) t (channels.callable b1) (channels.callable b2)) :
    CapCorr HeapCorr channels.capabilities channels.capabilities where
  value t a1 a2 ha := by
    show Sim HeapCorr _ t (channels.value a1) (channels.value a2)
    rw [hv]; exact step_sim ev route recur hrec t a1 a2 ha
  callable t a1 a2 ha := hcal t a1 a2 ha
  allocate t sp1 sp2 h := allocate_need_sim t sp1 sp2 h
  reference t a1 a2 ha := reference_sim t a1 a2 ha

/-! ## Ready supply formation, and the callback route -/

theorem ready_need_loop_sim : ∀ (args : List CountedResult) (acc1 acc2 : List Nat) (t : Table),
    Cells t acc1 acc2 → Sim HeapCorr Cells t (List.mapM.loop readyNeed args acc1) (List.mapM.loop readyNeed args acc2)
  | [], acc1, acc2, t, h => by
      simp only [List.mapM.loop]
      exact sim_pure HeapCorr Cells t _ _ (Rel2.reverse_aux h)
  | v :: rest, acc1, acc2, t, h => by
      simp only [List.mapM.loop]
      refine sim_bind HeapCorr Addr Cells t _ _ _ _ (allocate_need_sim t (.ready v) (.ready v) rfl) ?_
      intro t1 b1 b2 x1 hb
      exact ready_need_loop_sim rest (b1 :: acc1) (b2 :: acc2) t1 (Rel2.cons hb (cells_mono x1 h))

/-- READY SUPPLY FORMATION, simulated: the callback route's `args.mapM readyNeed`, run from two
    corresponding states (any two states, from the empty table), allocates corresponding cells
    position by position — the same counted values in the same order. -/
theorem ready_formation_sim (args : List CountedResult) (t : Table) :
    Sim HeapCorr Cells t (args.mapM readyNeed) (args.mapM readyNeed) := by
  unfold List.mapM
  exact ready_need_loop_sim args [] [] t Rel2.nil

/-- LEVEL 2 — AGREEMENT AFTER READY SUPPLY FORMATION (R6). Two bindings that each form a Ready
    supply of the SAME counted arguments — the callback route's prefix — and bind it with the ONE
    production binder `bindNeedPatterns`, started from ANY two states, correspond: the same error,
    both non-matches, or environments that bind the same names in the same order to corresponding
    cells, with corresponding final heaps. Every pattern kind is covered (fixed, collecting,
    nested structural, literal, META, repeated names) in either mode. The premises are the two
    `partial` channels' correspondence (`hrec`, `hcal`). -/
theorem ready_supplies_bind_correspondingly (channels : NeedChannels)
    (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur : Nat → EvalM CountedResult) (hv : channels.value = fun a => NeedDemand.step (ev a) route recur a)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (hcal : ∀ t b1 b2, Addr t b1 b2 →
      Sim HeapCorr (fun _ v w => v = w) t (channels.callable b1) (channels.callable b2))
    (args : List CountedResult) (ps : List NeedPattern) (family : Bool) (s1 s2 : EvalState) :
    RunCorr HeapCorr OptEnvCorr []
      (runEval (do let cells ← args.mapM readyNeed; bindNeedPatterns channels ps cells family) s1)
      (runEval (do let cells ← args.mapM readyNeed; bindNeedPatterns channels ps cells family) s2) :=
  sim_bind HeapCorr Cells OptEnvCorr [] _ _ _ _ (ready_formation_sim args [])
    (fun t' c1 c2 _ hc => patterns_sim HeapCorr _ _
      (heap_corr_capabilities channels ev route recur hv hrec hcal) ps c1 c2 family t' hc)
    s1 s2 (heap_corr_empty s1 s2)

/-- The same for the clause-family route (`evalConditionalCallbackCallCounted`'s dispatcher),
    with the activated body as an explicit continuation premise. -/
theorem ready_supplies_select_correspondingly {γ : Type} (channels : NeedChannels)
    (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur : Nat → EvalM CountedResult) (hv : channels.value = fun a => NeedDemand.step (ev a) route recur a)
    (hrec : ∀ t b1 b2, Addr t b1 b2 → Sim HeapCorr (fun _ v w => v = w) t (recur b1) (recur b2))
    (hcal : ∀ t b1 b2, Addr t b1 b2 →
      Sim HeapCorr (fun _ v w => v = w) t (channels.callable b1) (channels.callable b2))
    (Q : Table → γ → γ → Prop) (activate : CondBranch → NeedEnv → EvalM γ)
    (hact : ∀ t b e1 e2, EnvCorr t e1 e2 → Sim HeapCorr Q t (activate b e1) (activate b e2))
    (callee : Algorithm) (calleeName : String) (args : List CountedResult) (s1 s2 : EvalState) :
    RunCorr HeapCorr Q []
      (runEval (do let cells ← args.mapM readyNeed
                   NeedBinder.selectFamily channels.capabilities callee cells calleeName activate) s1)
      (runEval (do let cells ← args.mapM readyNeed
                   NeedBinder.selectFamily channels.capabilities callee cells calleeName activate) s2) :=
  sim_bind HeapCorr Cells Q [] _ _ _ _ (ready_formation_sim args [])
    (fun t' c1 c2 _ hc => select_family_sim HeapCorr _ _
      (heap_corr_capabilities channels ev route recur hv hrec hcal) Q callee calleeName activate activate
      hact t' c1 c2 hc)
    s1 s2 (heap_corr_empty s1 s2)

/-- The public channels: `demandNeed` IS `NeedDemand.step` at the production route, the
    address-indexed expression evaluation `evalSuppliedAt` (META-S3-1: a supplied `.Algorithm` link's
    VALUE reads its own receiver cell) and the recursive edge
    (`NeedControl.Production.demand_specialization`), so the two premises left are exactly the
    `partial` recursive edge `demandNeedRecursive` (reached only by collector cells) and the `partial`
    projection `projectNeedCallable`. -/
theorem public_channels_value :
    (⟨demandNeed, projectNeedCallable⟩ : NeedChannels).value =
      fun a => NeedDemand.step (evalSuppliedAt a) productionPlanRoute demandNeedRecursive a := by
  funext a
  exact KatLang.NeedControl.Production.demand_specialization a

end KatLang.SupplyCorrespondence
