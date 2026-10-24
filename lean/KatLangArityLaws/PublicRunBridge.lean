import KatLangArityLaws.EvaluatorCore

open KatLang KatLang.EvaluatorCore

/-!
# R7-FU-01: the public-entry bridge for `runResultM`

`runResultM` (`lean/KatLang.lean`) is the public entry: identification, validation, root wiring,
ONE root production call (`evalProgramOutput` or `eval`), then `exportRunValue`. Its projections
`runResultWithState`/`runResult`/`runFlat` drop the state on an error, so every state claim here
is made over `(runResultM e).runState s`.

`runResultWith rec e` is `runResultM`'s body with the evaluator answer `rec` at its two root calls;
`runResultM_is_production` pins `runResultM e = runResultWith evalUnbounded e` by `rfl`, so any
drift of `runResultM` breaks this module. Over it, with standard axioms only:

* **The public bridge** `public_bridge`: from EVERY entry state, the public run completes with
  `r` exactly when the SAME public composition over the total core (`evalFuel n`) completes with
  `r` at some fuel; `public_incomplete_iff`: the public outcome is the incomplete outcome exactly
  when it is incomplete at every fuel.
* **Public fuel laws**: `public_fuel_stable` (a completed public result — outcome AND final
  state — is identical at every larger fuel), `public_deterministic` (two completed fuels agree),
  `public_of_fuel` (a completed fuel result IS the public result).
* **The four-way case statement** `public_fuel_cases` over the fuel family (completed value,
  completed ordinary failure, incomplete at `n` but completing later, incomplete at every fuel),
  phrased through ONE predicate `Incomplete`, the interface its statements use for the incomplete
  representation (Constitution Q-82, open). The bridge proofs also use the core's normal-form laws.

THE OPAQUE PREFIX. Identification (`identifyPropertyExpr`), validation
(`validateExplicitParamOutputInvariantExpr` → the partial `validate*Tree`/`aliasCount`/
`staticChain`) and root wiring (`wireToCaller` → the partial `activeDeclaration?`/
`ScopeCtx.declaration`) are `partial def`s, i.e. kernel-opaque constants. Every theorem below is
PARAMETRIC in them: the proofs never unfold them, they case-split on whatever outcome and state the
validator yields and whatever tree identification yields (`runResultWith_oneCall`). They assume no
reachable-state, address or admission premise.

NOT claimed (it needs the prefix made total — Tier 2 of the R7-FU-01 plan,
`artifacts/validation/r7-fu-01/REPORT.md`): anything about what identification, validation or
wiring DO (the validator leaves the state unchanged or never yields the incomplete outcome,
identification keeps the root constructor, the admitted set); any entry-state invariant at the
public root call (e.g. FG-H1's `StateValid`, "no stored incomplete outcome"); that a public
incomplete outcome means divergence (in the kernel it means: the validator yields it, OR the root
call is incomplete at every fuel from the post-validation state — and a crafted entry state can
re-raise a stored one); transitive opacity-freedom. Not a Lean/C# claim and not a relation to the
retired `partial` evaluator. The incomplete STATES are unrelated (production keeps its entry
state, the core forgets it), so incomplete runs are related by outcome only.
-/

namespace KatLang.PublicRunBridge

/-- THE ONE PREDICATE through which the public laws read the incomplete representation (R7:
    `Error.fuelExhausted`; Constitution Q-82, open). It isolates their statements from that choice;
    `incomplete_iff` exposes the current representation to the proofs. -/
def Incomplete {α : Type} (o : Except Error α) : Prop := o = .error .fuelExhausted

theorem incomplete_iff {α : Type} (o : Except Error α) : Incomplete o ↔ o = .error .fuelExhausted :=
  Iff.rfl

/-- `runResultM`'s body with the evaluator answer `rec` at its two root calls. -/
def runResultWith (rec : EvalRec) (e : Expr) : EvalM Result := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx : EvalCtx := { callStack := [preludeAlg] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      if Algorithm.acceptsZeroSuppliedArguments wired then
        exportRunValue (<- rec.evalProgramOutput wired ctx [])
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => exportRunValue (<- rec.eval e ctx [])

/-- **Drift pin.** The public entry IS the composition over production. -/
theorem runResultM_is_production (e : Expr) : runResultM e = runResultWith evalUnbounded e := rfl

/-! ## One root call

A composition `f : EvalRec → EvalM α` is ONE-CALL at an entry state when its run there either does
not depend on the evaluator answer at all, or is exactly one call `c` from some state `t` followed
by a fixed continuation `k`. The witnesses (`c`, `k`, `t`) are whatever the opaque prefix
produced; nothing about them is known or needed. -/

def OneCallAt {α : Type} (f : EvalRec → EvalM α) (s : EvalState) : Prop :=
  (∀ rec rec' : EvalRec, (f rec).runState s = (f rec').runState s) ∨
  ∃ (c : EvalCall) (k : c.Ret → EvalM α) (t : EvalState),
    ∀ rec : EvalRec, (f rec).runState s = (rec c >>= k).runState t

/-- The bind lemma: one production call followed by a fixed continuation completes with `r`
    exactly when the same composition over the core completes with `r` at some fuel. -/
theorem bind_bridge {α : Type} (c : EvalCall) (k : c.Ret → EvalM α) (t : EvalState)
    (r : Except Error α × EvalState) :
    ((evalUnbounded c >>= k).runState t = r ∧ ¬ Incomplete r.1) ↔
    ∃ n, (evalFuel n c >>= k).runState t = r ∧ ¬ Incomplete r.1 := by
  constructor
  · rintro ⟨hr, hc⟩
    by_cases hp : ProductionCompletes (evalUnbounded c) t
    · obtain ⟨n, hn, -⟩ := (production_completes_iff c t _).1 ⟨rfl, hp⟩
      refine ⟨n, ?_, hc⟩
      rw [EvalM.bind_runState, hn, ← EvalM.bind_runState]; exact hr
    · rw [EvalM.bind_runState, production_incomplete_state c t hp] at hr
      exact absurd (by rw [← hr]; rfl) hc
  · rintro ⟨n, hr, hc⟩
    by_cases hn : Completes (evalFuel n c) t
    · have hp := (production_completes_iff c t _).2 ⟨n, rfl, hn⟩
      refine ⟨?_, hc⟩
      rw [EvalM.bind_runState, hp.1, ← EvalM.bind_runState]; exact hr
    · have hi : (evalFuel n c).runState t = (.error .fuelExhausted, {}) := Classical.not_not.mp hn
      rw [EvalM.bind_runState, hi] at hr
      exact absurd (by rw [← hr]; rfl) hc

/-- A one-call composition bridges production and the core. -/
theorem oneCall_bridge {α : Type} (f : EvalRec → EvalM α) (s : EvalState) (h : OneCallAt f s)
    (r : Except Error α × EvalState) :
    ((f evalUnbounded).runState s = r ∧ ¬ Incomplete r.1) ↔
    ∃ n, (f (evalFuel n)).runState s = r ∧ ¬ Incomplete r.1 := by
  rcases h with hind | ⟨c, k, t, hcall⟩
  · constructor
    · rintro ⟨hr, hc⟩; exact ⟨0, (hind _ _).trans hr, hc⟩
    · rintro ⟨n, hr, hc⟩; exact ⟨(hind _ _).trans hr, hc⟩
  · simp only [hcall]
    exact bind_bridge c k t r

/-- A completed one-call result at fuel `n` is the same at every larger fuel. -/
theorem oneCall_fuel_stable {α : Type} (f : EvalRec → EvalM α) (s : EvalState) (h : OneCallAt f s)
    {n m : Nat} (hnm : n ≤ m) (hc : ¬ Incomplete ((f (evalFuel n)).runState s).1) :
    (f (evalFuel m)).runState s = (f (evalFuel n)).runState s := by
  rcases h with hind | ⟨c, k, t, hcall⟩
  · exact hind _ _
  · rw [hcall, hcall] at *
    by_cases hn : Completes (evalFuel n c) t
    · rw [EvalM.bind_runState, EvalM.bind_runState, completed_stable hnm c t hn]
    · have hi : (evalFuel n c).runState t = (.error .fuelExhausted, {}) := Classical.not_not.mp hn
      rw [EvalM.bind_runState, hi] at hc
      exact absurd rfl hc

/-- The root step of `runResultWith`: wiring, the zero-supply gate and the root call. -/
def rootRun (rec : EvalRec) (e : Expr) : EvalM Result :=
  let ctx : EvalCtx := { callStack := [preludeAlg] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      if Algorithm.acceptsZeroSuppliedArguments wired then
        rec.evalProgramOutput wired ctx [] >>= exportRunValue
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => rec.eval e ctx [] >>= exportRunValue

theorem runResultWith_split (rec : EvalRec) (e : Expr) :
    runResultWith rec e =
      validateExplicitParamOutputInvariantExpr ((identifyPropertyExpr e).run' 0) >>= fun _ =>
        rootRun rec ((identifyPropertyExpr e).run' 0) := by
  unfold runResultWith rootRun
  generalize (identifyPropertyExpr e).run' 0 = e'
  cases e' <;> rfl

/-- The root step is one call, or does not depend on the evaluator answer (the gate refused). -/
theorem rootRun_shape (e : Expr) :
    (∀ rec rec' : EvalRec, rootRun rec e = rootRun rec' e) ∨
    ∃ (c : EvalCall) (k : c.Ret → EvalM Result), ∀ rec : EvalRec, rootRun rec e = rec c >>= k := by
  by_cases ha : ∃ a, e = .algorithmExpr a
  · obtain ⟨a, rfl⟩ := ha
    by_cases hz : Algorithm.acceptsZeroSuppliedArguments (wireToCaller { callStack := [preludeAlg] } a) = true
    · exact .inr ⟨.evalProgramOutput (wireToCaller { callStack := [preludeAlg] } a) { callStack := [preludeAlg] } [],
        exportRunValue, fun _ => by simp only [rootRun, hz, if_true]; rfl⟩
    · exact .inl (fun _ _ => by simp only [rootRun, hz]; rfl)
  · refine .inr ⟨.eval e { callStack := [preludeAlg] } [], exportRunValue, fun _ => ?_⟩
    cases e <;> first | rfl | exact absurd ⟨_, rfl⟩ ha

/-- `runResultWith` is one-call at every entry state, for every expression: the opaque prefix's
    outcome and state are case-split, never computed. -/
theorem runResultWith_oneCall (e : Expr) (s : EvalState) :
    OneCallAt (fun rec => runResultWith rec e) s := by
  have hsplit : ∀ rec : EvalRec, (runResultWith rec e).runState s =
      match (validateExplicitParamOutputInvariantExpr ((identifyPropertyExpr e).run' 0)).runState s with
      | (.ok _, t) => (rootRun rec ((identifyPropertyExpr e).run' 0)).runState t
      | (.error err, t) => (.error err, t) := fun rec => by
    rw [runResultWith_split, EvalM.bind_runState]
    rcases (validateExplicitParamOutputInvariantExpr ((identifyPropertyExpr e).run' 0)).runState s with ⟨o, t⟩
    cases o <;> rfl
  unfold OneCallAt
  simp only [hsplit]
  generalize (identifyPropertyExpr e).run' 0 = e'
  generalize (validateExplicitParamOutputInvariantExpr e').runState s = v
  rcases v with ⟨o, t⟩
  cases o with
  | error err => exact .inl (fun _ _ => rfl)
  | ok u =>
    rcases rootRun_shape e' with hind | ⟨c, k, hcall⟩
    · exact .inl (fun rec rec' => by simp only [hind rec rec'])
    · exact .inr ⟨c, k, t, fun rec => by simp only [hcall rec]⟩

/-! ## The public bridge -/

/-- **THE PUBLIC BRIDGE.** From every entry state, the public run completes with `r` (outcome AND
    final state) exactly when the same public composition over the total core completes with `r`
    at some fuel. Parametric in the opaque prefix. -/
theorem public_bridge (e : Expr) (s : EvalState) (r : Except Error Result × EvalState) :
    ((runResultM e).runState s = r ∧ ¬ Incomplete r.1) ↔
    ∃ n, (runResultWith (evalFuel n) e).runState s = r ∧ ¬ Incomplete r.1 :=
  oneCall_bridge (fun rec => runResultWith rec e) s (runResultWith_oneCall e s) r

/-- The public outcome is incomplete exactly when the core composition is incomplete at every
    fuel. In the kernel this is NOT divergence: see the module header. -/
theorem public_incomplete_iff (e : Expr) (s : EvalState) :
    Incomplete ((runResultM e).runState s).1 ↔
    ∀ n, Incomplete ((runResultWith (evalFuel n) e).runState s).1 := by
  constructor
  · intro hp n
    apply Classical.byContradiction
    intro hn
    have h := (public_bridge e s _).2 ⟨n, rfl, hn⟩
    exact h.2 (by rw [← h.1]; exact hp)
  · intro hall
    apply Classical.byContradiction
    intro hp
    obtain ⟨n, hn, hc⟩ := (public_bridge e s _).1 ⟨rfl, hp⟩
    exact hc (by rw [← hn]; exact hall n)

/-- A completed result at fuel `n` IS the public result. -/
theorem public_of_fuel (e : Expr) (s : EvalState) (n : Nat)
    (hc : ¬ Incomplete ((runResultWith (evalFuel n) e).runState s).1) :
    (runResultM e).runState s = (runResultWith (evalFuel n) e).runState s :=
  ((public_bridge e s _).2 ⟨n, rfl, hc⟩).1

/-- **Public fuel stability.** A completed public composition at fuel `n` has the same outcome
    AND final state at every larger fuel. -/
theorem public_fuel_stable (e : Expr) (s : EvalState) {n m : Nat} (hnm : n ≤ m)
    (hc : ¬ Incomplete ((runResultWith (evalFuel n) e).runState s).1) :
    (runResultWith (evalFuel m) e).runState s = (runResultWith (evalFuel n) e).runState s :=
  oneCall_fuel_stable (fun rec => runResultWith rec e) s (runResultWith_oneCall e s) hnm hc

/-- **Public determinism.** Two completed fuels give the same outcome and final state. -/
theorem public_deterministic (e : Expr) (s : EvalState) (n m : Nat)
    (hn : ¬ Incomplete ((runResultWith (evalFuel n) e).runState s).1)
    (hm : ¬ Incomplete ((runResultWith (evalFuel m) e).runState s).1) :
    (runResultWith (evalFuel n) e).runState s = (runResultWith (evalFuel m) e).runState s :=
  (public_of_fuel e s n hn).symm.trans (public_of_fuel e s m hm)

/-! ## The four-way case statement over the fuel family -/

/-- The public composition over the core at fuel `n`, from `s`. -/
abbrev atFuel (e : Expr) (s : EvalState) (n : Nat) : Except Error Result × EvalState :=
  (runResultWith (evalFuel n) e).runState s

/-- The four cases of the fuel family at fuel `n`. Only `Incomplete` reads the incomplete
    representation. -/
inductive FuelCase (e : Expr) (s : EvalState) (n : Nat) : Prop where
  /-- completed with a value -/
  | value (v : Result) (t : EvalState) (h : atFuel e s n = (.ok v, t))
  /-- completed with an ordinary failure -/
  | failure (err : Error) (t : EvalState) (hne : ¬ Incomplete (.error err : Except Error Result))
      (h : atFuel e s n = (.error err, t))
  /-- incomplete at `n`, completed at some larger fuel -/
  | incompleteAt (h : Incomplete (atFuel e s n).1) (m : Nat) (hnm : n < m)
      (hm : ¬ Incomplete (atFuel e s m).1)
  /-- incomplete at every fuel -/
  | incompleteEverywhere (h : ∀ m, Incomplete (atFuel e s m).1)

/-- Every fuel falls in one of the four cases. -/
theorem public_fuel_cases (e : Expr) (s : EvalState) (n : Nat) : FuelCase e s n := by
  by_cases hn : Incomplete (atFuel e s n).1
  · by_cases hall : ∀ m, Incomplete (atFuel e s m).1
    · exact .incompleteEverywhere hall
    · obtain ⟨m, hm⟩ := Classical.not_forall.mp hall
      have hnm : n < m := by
        rcases Nat.lt_or_ge n m with h | h
        · exact h
        · exact absurd hn (by
            show ¬ Incomplete ((runResultWith (evalFuel n) e).runState s).1
            rw [public_fuel_stable e s h hm]; exact hm)
      exact .incompleteAt hn m hnm hm
  · generalize hr : atFuel e s n = r at hn
    rcases r with ⟨o, t⟩
    cases o with
    | ok v => exact .value v t hr
    | error err => exact .failure err t hn hr

/-- The cases are exclusive: a completed fuel is never incomplete everywhere. -/
theorem fuelCase_completed_not_everywhere (e : Expr) (s : EvalState) (n : Nat)
    (hn : ¬ Incomplete (atFuel e s n).1) : ¬ ∀ m, Incomplete (atFuel e s m).1 :=
  fun hall => hn (hall n)

/-- What each case says about the public run. -/
theorem public_of_value (e : Expr) (s : EvalState) (n : Nat) (v : Result) (t : EvalState)
    (h : atFuel e s n = (.ok v, t)) : (runResultM e).runState s = (.ok v, t) := by
  have h' : (runResultWith (evalFuel n) e).runState s = (.ok v, t) := h
  rw [public_of_fuel e s n (by rw [h']; intro hi; cases hi), h']

theorem public_of_failure (e : Expr) (s : EvalState) (n : Nat) (err : Error) (t : EvalState)
    (hne : ¬ Incomplete (.error err : Except Error Result)) (h : atFuel e s n = (.error err, t)) :
    (runResultM e).runState s = (.error err, t) := by
  have h' : (runResultWith (evalFuel n) e).runState s = (.error err, t) := h
  rw [public_of_fuel e s n (by rw [h']; exact hne), h']

theorem public_of_incompleteAt (e : Expr) (s : EvalState) (m : Nat)
    (hm : ¬ Incomplete (atFuel e s m).1) : (runResultM e).runState s = atFuel e s m :=
  public_of_fuel e s m hm

theorem public_of_incompleteEverywhere (e : Expr) (s : EvalState)
    (h : ∀ m, Incomplete (atFuel e s m).1) : Incomplete ((runResultM e).runState s).1 :=
  (public_incomplete_iff e s).2 h

end KatLang.PublicRunBridge
