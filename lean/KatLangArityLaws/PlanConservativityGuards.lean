import KatLangArityLaws.PlanConservativity
import KatLangArityLaws.InvocationPlanGuards
import KatLangArityLaws.CallReferenceGuards

open KatLang KatLang.CallPlan KatLang.PlanConservativity

/-!
# Plan conservativity guards: candidate invariants on the authoritative evaluator (ledger E-18)

Every guard runs the authoritative evaluator of `KatLang.lean` from `EvalState.empty`. A
REACHABLE state is the final state of a whole program (`runResultWithState`) or of a setup built
from the production operations; the plan's FLIGHT state is what the production VALUE demand
itself reaches before the plan executes: the cell marked `evaluating` by the completion shell, then
its route established by `NeedPlan.routeOf` (`flight`). At that state the guards compare the two
sides of `CallPlan.fresh_plan_is_ordinary_call`: one `NeedPlan.execute productionPlanRoute` against
`ordinaryCall productionPlanRoute` along the recorded route (`conservativeAt`: the same outcome, and
the planned final state is the ordinary one with only the plan's own record changed).

Candidate invariants `P` for `PlanConservativity.BodyObliviousOn`, decided on a state:
* `activeAt` — the plan's cell is `evaluating` (the completion shell's mark);
* `noStoredRef` — additionally no stored value (completed or Ready cell, captured value
  environment, property cache, lexical activation) is `callRef a` or `argView a`;
* `unreachableFromRefs` — `a` is not reachable from any stored reference through recorded plan
  supplies, collector slices and recorded callee/receiver cells;
* `refFree` — no stored reference at all (the state half of a META-free run).

Results: `activeAt` and `noStoredRef` are REFUTED as sufficient simulation hypotheses by
`selfInvokeOutcomeDiffers` (outcome) and `viewReadHeapDiffers` (heap). `unreachableFromRefs` holds on
the `conservativeFresh` controls and fails on both counterexamples, but is not necessary
(`closureMemberStillConservative`). `refFree` holds at those controls' entry flights except the
VALUE-then-META case, which deliberately retains an older reference. These are entry-state checks,
not preservation proofs. `referenceExclusionsFailPush` refutes `PushClosed` for all three
reference-exclusion candidates. `unrestrictedDispatchCreatesRef` refutes reference exclusion's
preservation under the unrestricted dispatch family required by `PlanCalls`. None of the
candidates has discharged the production theorem's invariant contracts.
-/

namespace KatLang.PlanConservativityGuards


def program (extra : List (Ident × Algorithm)) (rows : List Expr) : Expr :=
  KatLang.CallReferenceGuards.program extra rows
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def addE (a b : Expr) : Expr := .binary .add a b
def invokeE (receiver : Expr) : Expr := .dotCall receiver "Invoke" (some [])
def argsOf (r : Expr) : Expr := .dotCall r "Arguments" none
def countOf (e : Expr) : Expr := .call (.resolve "count") [e]
def firstOf (e : Expr) : Expr := .call (.resolve "first") [e]
def R : Expr := .resolve "R"

/-! ## Candidate invariants, decided on a state -/

partial def refsOf : Result → List Nat
  | .callRef p => [p]
  | .argView p => [p]
  | .sequenceValue items => items.flatMap refsOf
  | .listValue items => items.flatMap refsOf
  | _ => []

def envRefs (env : ValEnv) : List Nat := env.flatMap fun (_, v) => refsOf v

/-- Every reference a state stores. -/
def storedRefs (x : EvalState) : List Nat :=
  (x.needs.toList.flatMap fun cell =>
    (match cell.state with
     | .completed (.ok (v, _)) => refsOf v
     | _ => []) ++
    (match cell.suspension with
     | .ready (v, _) => refsOf v
     | .expression _ _ values => envRefs values
     | .collector _ => [])) ++
  (x.zeroArgPropertyCache.flatMap fun (_, (v, _)) => refsOf v) ++
  (x.lexicalActivations.toList.flatMap fun act => envRefs act.values)

/-- The cells one step from cell `b`: its recorded supply, its collector slice, its recorded
    callee and receiver cells. -/
def edges (x : EvalState) (b : Nat) : List Nat :=
  match x.needs[b]? with
  | some cell =>
    (match cell.plan with
     | .prepared (.ok cells) => cells.map Prod.fst
     | _ => []) ++
    (match cell.suspension with
     | .collector slice => slice
     | _ => []) ++
    cell.callee.toList ++ cell.receiver.toList
  | none => []

def closureFrom (x : EvalState) : Nat → List Nat → List Nat
  | 0, seen => seen
  | Nat.succ fuel, seen =>
    let next := (seen.flatMap (edges x)).filter (fun b => !seen.contains b)
    if next.isEmpty then seen else closureFrom x fuel (seen ++ next.eraseDups)

/-- Every cell reachable from a stored reference (the plans themselves included). -/
def refClosure (x : EvalState) : List Nat := closureFrom x (x.needs.size + 1) (storedRefs x).eraseDups

def activeAt (x : EvalState) (a : Nat) : Bool :=
  match x.needs[a]? with
  | some { state := .evaluating, .. } => true
  | _ => false

def noStoredRef (x : EvalState) (a : Nat) : Bool := activeAt x a && !(storedRefs x).contains a
def unreachableFromRefs (x : EvalState) (a : Nat) : Bool := activeAt x a && !(refClosure x).contains a
def refFree (x : EvalState) (a : Nat) : Bool := activeAt x a && (storedRefs x).isEmpty

/-! ## The flight state and the two sides of the simulation -/

/-- The production VALUE demand's own first steps on a fresh plan cell: the shell's `evaluating`
    mark, then the route, established exactly as `NeedDemand.suspendedValue` establishes it. -/
def flight (s : EvalState) (a : Nat) : Option (NeedPlan.CallShape × PlanRoute × EvalState) :=
  match NeedPlan.shapeAt? s.needs a with
  | none => none
  | some shape =>
    match (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify a shape)).runState
        (withState a .evaluating s) with
    | (.ok r, x) => some (shape, r, x)
    | _ => none

def plannedAt (shape : NeedPlan.CallShape) (a : Nat) (x : EvalState) : Except Error CountedResult × EvalState :=
  (NeedPlan.execute productionPlanRoute a shape).runState x

def ordinaryAt (shape : NeedPlan.CallShape) (a : Nat) (r : PlanRoute) (x : EvalState) :
    Except Error CountedResult × EvalState :=
  (ordinaryCall productionPlanRoute a shape r).runState x

def sameOutcome (shape : NeedPlan.CallShape) (a : Nat) (r : PlanRoute) (x : EvalState) : Bool :=
  reprStr (plannedAt shape a x).1 == reprStr (ordinaryAt shape a r x).1

/-- The conclusion of `fresh_plan_is_ordinary_call`, decided: the same outcome, and the planned
    final state is the ordinary one with only the plan's own record changed. -/
def conservativeAt (shape : NeedPlan.CallShape) (a : Nat) (r : PlanRoute) (x : EvalState) : Bool :=
  let p := plannedAt shape a x
  let o := ordinaryAt shape a r x
  sameOutcome shape a r x &&
    (match p.2.needs[a]? with
     | some cell => reprStr p.2 == reprStr (withPlan a cell.plan o.2)
     | none => false)

def cellOf (s : EvalState) (src : Expr) : Option Nat :=
  (List.range s.needs.size).find? fun a =>
    match s.needs[a]? with
    | some { suspension := .expression e _ _, .. } => reprStr e == reprStr src
    | _ => false

/-- The final state of `program decls [count(R.Arguments)]`: `R`'s captured call is prepared, so its
    one argument cell — the plan under test — exists, suspended and fresh. -/
def reached (decls : List (Ident × Algorithm)) : Option EvalState :=
  match runResultWithState (program decls [countOf (argsOf R)]) with
  | .ok (_, s) => some s
  | .error _ => none

/-- Runs `check` on the flight of the cell holding `src` in the reached state. -/
def atFlight (decls : List (Ident × Algorithm)) (src : Expr)
    (check : EvalState → Nat → NeedPlan.CallShape → PlanRoute → EvalState → Bool) : Bool :=
  match reached decls with
  | none => false
  | some s =>
    match cellOf s src with
    | none => false
    | some a =>
      match s.needs[a]? with
      | some { state := .suspended, plan := .unprepared, route := none, .. } =>
        match flight s a with
        | some (shape, r, x) => check s a shape r x
        | none => false
      | _ => false

/-! ## Counterexample 1: the captured call re-invokes itself while forming its own supply

`R = Capture(Wrap(Inner((Capture(R.Arguments*).Invoke())*)))`. `first(R.Arguments)` prepares the
`Wrap` plan, whose one argument cell `a = Inner(…)` is then demanded. Forming `a`'s supply evaluates
the spread: `R.Arguments*` transports `a` itself into `Capture`, whose META binder reifies it, and
`.Invoke()` executes `a` again. On the plan route `a`'s record is `preparing`, so the inner
preparation is a cycle at once; the ordinary call forms without a record, so the inner invocation
prepares `a` once more and the cycle is met one level deeper — two more context frames. -/

def selfInvoke : Expr := invokeE (callN "Capture" [.sequenceSpread (argsOf R)])
def innerA : Expr := callN "Inner" [.sequenceSpread selfInvoke]
def selfInvokeDecls : List (Ident × Algorithm) :=
  [("Wrap", alg ["x"] [] [] [.param "x"]),
   ("Inner", alg ["x"] [] [] [.param "x"]),
   ("R", alg [] [] [] [callN "Capture" [callN "Wrap" [innerA]]])]

def frames : Error → Nat
  | .withContext _ inner => frames inner + 1
  | _ => 0

def cycleFrames (r : Except Error CountedResult) : Option Nat :=
  match r with
  | .error e =>
    match KatLang.CallReferenceGuards.innermost e with
    | .demandCycle => some (frames e)
    | _ => none
  | .ok _ => none

def selfInvokeOutcomeDiffers : Bool :=
  atFlight selfInvokeDecls innerA fun _ a shape r x =>
    r == .call &&
    -- the refuted candidates hold at the flight state
    activeAt x a && noStoredRef x a &&
    -- the surviving candidates do not
    !unreachableFromRefs x a && !refFree x a &&
    -- both sides fail with a cycle, at different depths: the OUTCOMES differ
    cycleFrames (plannedAt shape a x).1 == some 3 &&
    cycleFrames (ordinaryAt shape a r x).1 == some 5 &&
    !sameOutcome shape a r x
#guard selfInvokeOutcomeDiffers

/-- The same difference at the VALUE boundary: production `demandNeed` against the pre-M1.5
    ordinary completion (`CallPlanGuards.ordinaryCompletion`) of the same reached cell. -/
def selfInvokeValueDiffers : Bool :=
  match reached selfInvokeDecls with
  | none => false
  | some s =>
    match cellOf s innerA with
    | none => false
    | some a =>
      cycleFrames ((demandNeed a).runState s).1 == some 3 &&
      cycleFrames ((KatLang.CallPlanGuards.ordinaryCompletion a).runState s).1 == some 5
#guard selfInvokeValueDiffers

/- A whole program reaches that VALUE demand: `first(R.Arguments)` fails with the PLAN route's
    outcome (three frames under `first`'s), not the ordinary one. -/
#guard match runResult (program selfInvokeDecls [firstOf (argsOf R)]) with
  | .error e =>
    (match KatLang.CallReferenceGuards.innermost e with | .demandCycle => true | _ => false) && frames e == 4
  | .ok _ => false

/-! ## Counterexample 2: the captured call's body reads its own argument view

`R = Capture(Wrap(Inner2(5)))`, `Inner2(x) = x + count(Capture(R.Arguments*).Arguments)`. During
dispatch the plan route's record of `a = Inner2(5)` is `prepared` and `count` reuses its cells; the
ordinary call left it `unprepared`, so `count` prepares `a` afresh and allocates a second argument
cell. The value is the same (6); the heaps differ by more than the plan record. -/

def inner2 : Expr := callN "Inner2" [.num 5]
def viewReadDecls : List (Ident × Algorithm) :=
  [("Wrap", alg ["x"] [] [] [.param "x"]),
   ("Inner2", alg ["x"] [] [] [addE (.param "x")
      (countOf (argsOf (callN "Capture" [.sequenceSpread (argsOf R)])))]),
   ("R", alg [] [] [] [callN "Capture" [callN "Wrap" [inner2]]])]

def viewReadHeapDiffers : Bool :=
  atFlight viewReadDecls inner2 fun _ a shape r x =>
    r == .call && activeAt x a && noStoredRef x a && !unreachableFromRefs x a &&
    sameOutcome shape a r x &&
    KatLang.CallPlanGuards.valueIs (plannedAt shape a x).1 6 &&
    (ordinaryAt shape a r x).2.needs.size == (plannedAt shape a x).2.needs.size + 1 &&
    !conservativeAt shape a r x
#guard viewReadHeapDiffers

/-! ## Positive controls -/

/-- A captured call that never observes itself: `a` IS reachable from a stored reference (the
    `Wrap` plan's supply), so `unreachableFromRefs` fails, yet the simulation's conclusion holds —
    that candidate is not necessary. -/
def inner3 : Expr := callN "Inner3" [.num 5]
def plainDecls : List (Ident × Algorithm) :=
  [("Wrap", alg ["x"] [] [] [.param "x"]),
   ("Inner3", alg ["x"] [] [] [addE (.param "x") (.num 1)]),
   ("R", alg [] [] [] [callN "Capture" [callN "Wrap" [inner3]]])]

def closureMemberStillConservative : Bool :=
  atFlight plainDecls inner3 fun _ a shape r x =>
    activeAt x a && !unreachableFromRefs x a && conservativeAt shape a r x &&
    KatLang.CallPlanGuards.valueIs (plannedAt shape a x).1 6
#guard closureMemberStillConservative

/-- The flight of a fresh cell supplied by `setup`: check every entry-state candidate explicitly,
    with the expected reference-free verdict, and the simulation's conclusion. -/
def conservativeFresh {α : Type} (setup : EvalM (α × Nat)) (expected? : Option Int := none)
    (expectRefFree : Bool := true) : Bool :=
  match setup.run EvalState.empty with
  | .error _ => false
  | .ok ((_, a), s) =>
    match flight s a with
    | none => false
    | some (shape, r, x) =>
      activeAt x a && noStoredRef x a && unreachableFromRefs x a &&
      refFree x a == expectRefFree && conservativeAt shape a r x &&
      (match expected? with
       | some v => KatLang.CallPlanGuards.valueIs (plannedAt shape a x).1 v
       | none => true)

/-- A root context with the prelude (so `repeat`, `count` resolve), wired as `runResultM` wires a
    program root. -/
def preludeCtx (root : Algorithm) : EvalCtx :=
  let base : EvalCtx := { callStack := [preludeAlg] }
  base.push (wireToCaller base root)

def fresh (src : Expr) : EvalM (Unit × Nat) := do
  let a ← supplyNeed src (preludeCtx KatLang.CallPlanGuards.root) []
  pure ((), a)

-- META-free runs (`refFree` holds): the `agrees` corpus at the theorem's own comparison point.
open KatLang.CallPlanGuards (callF bad) in
def metaFreeSources : List Expr :=
  [callF (.num 41),
   .call (.resolve "Keep") [.num 7, bad],
   .call (.resolve "Add2") [.sequenceSpread (.call (.resolve "Pair") [])],
   .call (.resolve "Add2") [.sequenceSpread (.call (.resolve "BadPair") [])],
   .call (.resolve "F") [bad, .num 2],
   .call (.resolve "Bad") [.num 1],
   callF (callF (.num 1)),
   .call (.resolve "G") [.num 41],
   .call (.resolve "count") [.listLiteral [.num 1, .num 2]],
   .call (.resolve "Sign") [.num 0],
   .call (.resolve "Sign") [bad]]

#guard metaFreeSources.all fun src => conservativeFresh (fresh src)
#guard conservativeFresh (fresh (KatLang.CallPlanGuards.callF (.num 41))) (some 42)
#guard conservativeFresh (fresh (.call (.resolve "count") [.listLiteral [.num 1, .num 2]])) (some 2)
#guard conservativeFresh (fresh (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "Pair") [])])) (some 3)
#guard metaFreeSources.all fun src =>
  match (fresh src).run EvalState.empty with
  | .ok ((_, a), s) => match flight s a with
    | some (_, _, x) => refFree x a
    | none => false
  | .error _ => false

/-- A root with META and loops INSIDE the flight: `Loop(n) = repeat(Inc(n), 3)`,
    `UseRef(x) = Capture(Sq(x)).Invoke() + x`, `Views(x) = count(Capture(Add(x, 1)).Arguments)`. -/
def metaRoot : Algorithm := algPrivate [] []
  (KatLang.CallReferenceGuards.decls ++
   [("Loop", alg ["n"] [] [] [callN "repeat" [callN "Inc" [.param "n"], .num 3]]),
    ("UseRef", alg ["x"] [] [] [addE (invokeE (callN "Capture" [callN "Sq" [.param "x"]])) (.param "x")]),
    ("Views", alg ["x"] [] [] [countOf (argsOf (callN "Capture" [callN "Add" [.param "x", .num 1]]))])]) []
def metaCtx : EvalCtx := preludeCtx metaRoot

def freshMeta (src : Expr) : EvalM (Unit × Nat) := do
  let a ← supplyNeed src metaCtx []
  pure ((), a)

#guard conservativeFresh (freshMeta (callN "Loop" [.num 5])) (some 8)        -- a loop in the flight
#guard conservativeFresh (freshMeta (callN "UseRef" [.num 3])) (some 12)     -- a nested plan, invoked
#guard conservativeFresh (freshMeta (callN "Views" [.num 3])) (some 2)       -- a nested argument view
#guard conservativeFresh (freshMeta (callN "Sign" [.num 0])) (some 100)      -- a family

/-- VALUE then META of another plan, retaining the reference in a Ready adapter, then a fresh
    plan: the new cell is not reachable from the earlier reference, and conservativity holds. -/
def valueThenMetaThenFresh : EvalM (NeedPlan.CallReference × Nat) := do
  let b ← supplyNeed (KatLang.CallPlanGuards.callF (.num 41)) (preludeCtx KatLang.CallPlanGuards.root) []
  let _ ← demandNeed b
  let r ← reifyNeedCall b
  let _ ← readyNeed (.callRef r.plan, 1)
  let a ← supplyNeed (.call (.resolve "G") [.num 41]) (preludeCtx KatLang.CallPlanGuards.root) []
  pure (r, a)
#guard conservativeFresh valueThenMetaThenFresh (some 42) false

/-! ## Obstacles in the current sufficient contracts

These checks concern the contracts of the generic production theorem, rather than additional
counterexamples to a META-free execution. `PushClosed` permits an arbitrary cell; `PlanCalls`
includes a META dispatch, even when the intended future domain is META-free.
-/

def referenceExclusionsFailPush : Bool :=
  match (fresh (KatLang.CallPlanGuards.callF (.num 41))).run EvalState.empty with
  | .ok ((_, a), s) =>
    match flight s a with
    | some (_, _, x) =>
      let y := { x with needs := x.needs.push { suspension := .ready (.callRef a, 1) } }
      noStoredRef x a && unreachableFromRefs x a && refFree x a && activeAt y a &&
      !noStoredRef y a && !unreachableFromRefs y a && !refFree y a
    | none => false
  | .error _ => false
#guard referenceExclusionsFailPush

/-- `PlanCalls` includes this production META dispatch for every `Q` satisfying it. The Ready
    adapter it allocates stores `callRef a` without demanding or completing the active cell. -/
def unrestrictedDispatchCreatesRef : Bool :=
  match (fresh (KatLang.CallPlanGuards.callF (.num 41))).run EvalState.empty with
  | .ok ((_, a), s) =>
    match flight s a with
    | some (_, _, x) =>
      let capture := algWithParameters [KatLang.CallReferenceGuards.metaParam "op"] [] [] [.param "op"]
      match (evalSuppliedCallCounted .none capture [(a, none)]
          (preludeCtx KatLang.CallPlanGuards.root) [] "Capture").runState x with
      | (.ok (.callRef b, _), y) =>
        refFree x a && noStoredRef x a && unreachableFromRefs x a && b == a && activeAt y a &&
        !noStoredRef y a && !unreachableFromRefs y a && !refFree y a
      | _ => false
    | none => false
  | .error _ => false
#guard unrestrictedDispatchCreatesRef

end KatLang.PlanConservativityGuards
