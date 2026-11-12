import KatLangArityLaws.NavigationSettled
import KatLangArityLaws.MemberBridgeSourceInstances

/-!
# Re-read guards: a mark IN FLIGHT, a failed route decision, a reference chain (E-18 step 1, M1)

Three things `NavigationReread` claims are exercised here on reached states.

## 1. `SelfLink` — `SA = SA.Algorithm`: the in-flight mark, a failed route decision, a re-read failure

A runtime-target alias whose receiver is itself. Its chase's ROUTE DECISION fails — the receiver
path leads back into the structure chase in progress, a cycle — and the chase reads that failure as
the runtime route (`decision_recovers`). The runtime step records the binding cell and projects it;
the projection, IN FLIGHT, navigates `SA` again, whose runtime step re-enters the flight:
`demandCycle`.

* `flight_state` — `inFlight` is the state the projection shell runs the cell's projection from:
  the cell is marked `projecting` (`mark_in_flight`).
* `inner_fails` — from that in-flight state the receiver probe FAILS with `demandCycle`: a
  navigation run (`inner_nav`) that minted nothing.
* `mark_kept` — **`MemoLinks.LinkKept.projecting` APPLIED at a state with a mark in flight**: after
  that production operation the cell is still `projecting`. Not vacuous: the entry mark IS
  `projecting`.
* `failure_reread` — **`navigation_reread` APPLIED to a FAILURE**: from every navigation extension
  of the inner probe's exit state the probe fails with `demandCycle` again and writes nothing. The
  re-read goes through the mark kept in flight.
* `whole_fails`, `published`, `whole_reread` — the whole probe from the empty state fails with
  `demandCycle`, the cell holds that failure as its completed CALLABLE, and from every navigation
  extension of the exit state the probe fails again: the PUBLISHED failure is read back.

## 2. `Chain` — `AB2 = AB`, `AB = Box`: a two-step reference chain, by EXECUTION

`navigation_reread` covers a chain of any length with no alias-key premise. Its run facts for a
concrete chain are not Lean-provable: the chase compares the second step's key with the first's,
both built with `reprStr`, and `Std.Format.pretty` is an opaque constant of Lean core. Compiled
code runs it: the `#guard`s below EXECUTE the navigation core on the chain — it completes, mints
nothing, and re-running the probe from the exit state, and from that state extended by an
allocation, gives the same answer and writes nothing. These are executable checks, NOT theorems.

## 3. The stuck comparison, exactly

`keysDiffer` is the proposition a chain instance would need. Its two sides are closed terms; the
kernel cannot reduce `Std.Format.pretty` (its layout loop `Std.Format.be` is `partial`, hence an
`opaque` constant), and no proof term can distinguish two applications of an opaque constant: the
model in which the constant is its `Inhabited` default makes every printed key the empty string,
so the INEQUALITY is not provable; the EQUALITY is not provable either (compiled code refutes it).
`keysDiffer_executed` is the executable check.
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.NavigationReread KatLang.NavigationSettled
open KatLang.MemoLinks (LinkHeapKept LinkKept evalUnbounded_linkDisc)

namespace KatLang.NavigationRereadGuards

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-- A source program with the given declarations and no row, wired as `runResultM` wires it. -/
def rootOf (decls : List (Ident × Algorithm)) : Algorithm :=
  match (identifyPropertyExpr (.algorithmExpr (algPrivate [] [] decls []))).run' 0 with
  | .algorithmExpr a => a
  | _ => alg [] [] [] []

def base : EvalCtx := { callStack := [preludeAlg] }

def ctxOf (decls : List (Ident × Algorithm)) : EvalCtx := base.push (wireToCaller base (rootOf decls))

/-- The binding a name selects in a context (the evaluator's own lookup). -/
def selected (ctx : EvalCtx) (name : Ident) : Algorithm :=
  match ctx.callStack with
  | top :: _ =>
      (match ((lookupLexicalPropertyRaw top name ctx).runState EvalState.empty).1 with
       | .ok r => r.alg
       | .error _ => alg [] [] [] [])
  | [] => alg [] [] [] []

/-- The context the cell at `a` was supplied in. -/
def cellCtx (s : EvalState) (a : Nat) (dflt : EvalCtx) : EvalCtx :=
  match s.needs[a]? with
  | some cell =>
      (match cell.suspension with
       | .expression _ c _ => c
       | _ => dflt)
  | none => dflt

/-! ## 1. `SA = SA.Algorithm` -/

namespace SelfLink

def row : Expr := .dotMember (.resolve "SA") "Algorithm" (.resolve "Algorithm") none

/-- `SA = SA.Algorithm`. -/
def ctx : EvalCtx := ctxOf [("SA", .alias none [] [] row)]

/-- The alias, as the lookup wires it. -/
def sa : Algorithm := selected ctx "SA"

/-- After the runtime step established the binding cell: cell 0, recorded. -/
def established : EvalState := ((aliasBindingCell sa row ctx).runState EvalState.empty).2

/-- The context the binding cell's row is supplied in. -/
def declCtx : EvalCtx := cellCtx established 0 ctx

/-- THE IN-FLIGHT STATE: the projection shell's `projecting` mark on the binding cell. -/
def inFlight : EvalState := KatLang.NeedControl.Projection.setCallable 0 .projecting established

/-- The exit state of the receiver probe run from the in-flight state. -/
def innerExit : EvalState := ((resolveDotReceiver? (.resolve "SA") declCtx).runState inFlight).2

/-- The exit state of the whole probe from the empty state. -/
def wholeExit : EvalState := ((resolveDotReceiver? (.resolve "SA") ctx).runState EvalState.empty).2

theorem facts :
    ((aliasBindingCell sa row ctx).runState EvalState.empty = (.ok 0, established)) ∧
    ((established.needs[0]?).map NeedCell.callable = some .unprojected) ∧
    ((inFlight.needs[0]?).map NeedCell.callable = some .projecting) ∧
    ((aliasStepIsRuntime sa row ctx (aliasStructureContext false (aliasChaseKey sa) [])).runState EvalState.empty =
      (.ok true, EvalState.empty)) ∧
    ((navFuel 64 (.resolveDotReceiver? (.resolve "SA") declCtx)).runState inFlight = (.error .demandCycle, innerExit)) ∧
    (innerExit.nextRuntimeDeclaration = inFlight.nextRuntimeDeclaration) ∧
    ((navFuel 64 (.resolveDotReceiver? (.resolve "SA") ctx)).runState EvalState.empty = (.error .demandCycle, wholeExit)) ∧
    (wholeExit.nextRuntimeDeclaration = EvalState.empty.nextRuntimeDeclaration) ∧
    ((wholeExit.needs[0]?).map NeedCell.callable = some (.projected (.error .demandCycle))) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

end SelfLink

namespace SelfLink

theorem established_cell : (aliasBindingCell sa row ctx).runState EvalState.empty = (.ok 0, established) := facts.1

theorem unprojected_before : (established.needs[0]?).map NeedCell.callable = some .unprojected := facts.2.1

/-- The binding cell's CALLABLE mark is IN FLIGHT at `inFlight`. -/
theorem mark_in_flight : (inFlight.needs[0]?).map NeedCell.callable = some .projecting := facts.2.2.1

/-- **`inFlight` is the state the projection shell runs the cell's projection from**: the shell's
    run from `established` is its callback's run from `inFlight`, then the publication
    (`NeedControl.Projection.unprojected_publishes`). -/
theorem flight_state (project : NeedSuspension → EvalM (Option Algorithm)) (cell : NeedCell)
    (hc : established.needs[0]? = some cell) (outcome : Except Error (Option Algorithm)) (t : EvalState)
    (hrun : (project cell.suspension).runState inFlight = (outcome, t)) (hcomplete : outcome.isIncomplete = false) :
    (NeedProjection.step project 0).runState established =
      (outcome, KatLang.NeedControl.Projection.setCallable 0 (.projected outcome) t) := by
  have hcal : cell.callable = .unprojected := by
    have h := unprojected_before
    rw [hc] at h
    exact Option.some.inj h
  exact KatLang.NeedControl.Projection.unprojected_publishes project 0 established t cell outcome hc hcal hrun hcomplete

/-- **The route decision FAILS and the chase recovers**: the receiver path of `SA = SA.Algorithm`
    leads back into the structure chase in progress — a cycle inside the decision — and the caught
    failure is read as the runtime route. -/
theorem decision_recovers :
    (aliasStepIsRuntime sa row ctx (aliasStructureContext false (aliasChaseKey sa) [])).runState EvalState.empty =
      (.ok true, EvalState.empty) := facts.2.2.2.1

/-- From the in-flight state the receiver probe is a navigation run that FAILS with `demandCycle`. -/
theorem inner_nav :
    NavRuns (.resolveDotReceiver? (.resolve "SA") declCtx) inFlight (.error .demandCycle, innerExit) :=
  ⟨64, facts.2.2.2.2.1, by intro h; cases h⟩

theorem inner_fails : (resolveDotReceiver? (.resolve "SA") declCtx).runState inFlight = (.error .demandCycle, innerExit) :=
  inner_nav.production

theorem inner_no_mint : innerExit.nextRuntimeDeclaration = inFlight.nextRuntimeDeclaration := facts.2.2.2.2.2.1

/-- **`LinkKept.projecting` APPLIED at a state with a mark in flight.** The receiver probe is a
    production operation started while the cell is `projecting`; whatever it does — here it records
    nothing new, re-enters the flight and fails — the cell is still `projecting` afterwards. -/
theorem mark_kept : (innerExit.needs[0]?).map NeedCell.callable = some .projecting := by
  have hk := evalUnbounded_linkDisc (.resolveDotReceiver? (.resolve "SA") declCtx) inFlight
  cases hc : inFlight.needs[0]? with
  | none =>
    have h := mark_in_flight
    rw [hc] at h
    cases h
  | some cell =>
    have hm : cell.callable = .projecting := by
      have h := mark_in_flight
      rw [hc] at h
      exact Option.some.inj h
    obtain ⟨cell', hc', hkept⟩ := hk 0 cell hc
    have hc'' : innerExit.needs[0]? = some cell' := hc'
    rw [hc'']
    exact congrArg some (hkept.projecting hm)

/-- **`navigation_reread` APPLIED to a FAILURE.** From every navigation extension of the inner
    probe's exit state the probe fails with `demandCycle` again and writes nothing — the mark kept
    in flight is what the re-entry reads. -/
theorem failure_reread (u : EvalState) (hu : NavExt innerExit u) :
    (resolveDotReceiver? (.resolve "SA") declCtx).runState u = (.error .demandCycle, u) :=
  ((navigation_reread _ inFlight innerExit _ inner_nav inner_no_mint).2 u hu).1

/-- The whole probe from the empty state: a navigation run that fails with `demandCycle`. -/
theorem whole_nav :
    NavRuns (.resolveDotReceiver? (.resolve "SA") ctx) EvalState.empty (.error .demandCycle, wholeExit) :=
  ⟨64, facts.2.2.2.2.2.2.1, by intro h; cases h⟩

theorem whole_fails : (resolveDotReceiver? (.resolve "SA") ctx).runState EvalState.empty = (.error .demandCycle, wholeExit) :=
  whole_nav.production

/-- The failure is PUBLISHED: the binding cell holds it as its completed CALLABLE. -/
theorem published : (wholeExit.needs[0]?).map NeedCell.callable = some (.projected (.error .demandCycle)) :=
  facts.2.2.2.2.2.2.2.2

/-- **The published failure is read back**: from every navigation extension of the exit state the
    whole probe fails with `demandCycle` again and writes nothing. -/
theorem whole_reread (u : EvalState) (hu : NavExt wholeExit u) :
    (resolveDotReceiver? (.resolve "SA") ctx).runState u = (.error .demandCycle, u) :=
  ((navigation_reread _ EvalState.empty wholeExit _ whole_nav facts.2.2.2.2.2.2.2.1).2 u hu).1

end SelfLink

/-! ## 2. A two-step reference chain, by execution -/

namespace Chain

/-- `Box = { V = 7 }`, `AB = Box`, `AB2 = AB`. -/
def ctx : EvalCtx :=
  ctxOf [("Box", algPrivate [] [] [("V", alg [] [] [] [.num 7])] []),
         ("AB", .alias none [] [] (.resolve "Box")),
         ("AB2", .alias none [] [] (.resolve "AB"))]

def probe : EvalCall := .resolveDotReceiver? (.resolve "AB2") ctx

/-- What a run of the navigation core answers, printed, and the sizes of the state it leaves. -/
def observe (s : EvalState) : Option String × Nat × Nat × Nat × Nat :=
  let r := (navFuel 64 probe).runState s
  ((match r.1 with
    | .ok (some owner) => some (reprStr owner)
    | _ => none),
   r.2.needs.size, r.2.aliasCells.length, r.2.nextRuntimeDeclaration, r.2.lexicalActivations.size)

def exit : EvalState := ((navFuel 64 probe).runState EvalState.empty).2

/-- A navigation extension of the exit state: one more allocated cell. -/
def extended : EvalState := { exit with needs := exit.needs.push { suspension := .ready (.atom 0, 1) } }

-- EXECUTED, not proved: the navigation core completes the chain's probe and mints nothing …
#guard (observe EvalState.empty).1.isSome
#guard (observe EvalState.empty).2.2.2.1 == 0
-- … the probe answers the chain's END (`Box`, a plain declaration) …
#guard (observe EvalState.empty).1 == some (reprStr (selected ctx "Box"))
-- … and re-running it from the exit state, and from an extension of it, answers the same and
-- leaves the state as it found it.
#guard observe exit == ((observe EvalState.empty).1, exit.needs.size, exit.aliasCells.length,
  exit.nextRuntimeDeclaration, exit.lexicalActivations.size)
#guard observe extended == ((observe EvalState.empty).1, extended.needs.size, extended.aliasCells.length,
  extended.nextRuntimeDeclaration, extended.lexicalActivations.size)

/-! ## 3. The comparison no Lean proof decides -/

/-- The fact a theorem-level chain instance would need: the two steps have different chase keys.
    Stated, NOT proved — and not provable (see the module header). -/
def keysDiffer : Prop := aliasChaseKey (selected ctx "AB") ≠ aliasChaseKey (selected ctx "AB2")

-- EXECUTED: compiled code prints the two keys and they differ.
#guard aliasChaseKey (selected ctx "AB") != aliasChaseKey (selected ctx "AB2")

end Chain

end KatLang.NavigationRereadGuards
