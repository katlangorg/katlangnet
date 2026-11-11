import KatLangArityLaws.PlanConservativityAdmissible
import KatLangArityLaws.PlanConservativityGuards

open KatLang KatLang.CallPlan KatLang.PlanConservativity KatLang.PlanConservativityGuards
  KatLang.PlanConservativityAdmissible

/-!
# Admissible plan-conservativity guards (ledger E-18)

Executable checks, on the authoritative evaluator, of the admissible domain of
`PlanConservativityAdmissible.production_fresh_plan_refFree` at the plan's FLIGHT state
(`PlanConservativityGuards.flight`):

* `admissibleAt` decides the domain's entry part: the cell is `evaluating` (`Active`), no reference
  is stored (`storedRefFreeB`, which agrees with the older guards' `refFree` on every state checked
  here), the plan's captured value environment is reference-free (`formAdmissible_activeRefFree`'s
  premise), the route is a written call or extension route, and the written callee, once resolved
  and normalized, declares no `meta` parameter (the `RT`/`RN` contract instantiated by
  `admissibleCallee`). These checks do not decide the universal body or output contracts, or
  syntactic META-freedom of the callee's body (`UseRef` below passes the entry checks too).
* On the META-free corpus and on a LOOP-ONLY plan (`Loop(n) = repeat(Inc(n), 3)`) the domain holds
  and the simulation's conclusion holds (`conservativeAt`).
* Both META counterexamples and the unrestricted-contract obstacles fall OUTSIDE the domain — they
  are excluded, not contradicted: their guards in `PlanConservativityGuards` still pass.
* `loopRunStoresReference`: `StoredRefFree` is NOT kept by a loop-only run. Lean's `repeat` binds
  its step through the builtin `meta step` parameter (`builtinSignature`), which stores a Ready
  `callRef` adapter of the still-suspended STEP cell; that reference does not reach the plan's cell, and the
  simulation still holds. So `Keeps (ActiveRefFree a)` fails for this loop-only operation;
  any domain containing it cannot discharge all the reference-free body obligations.
* `activeKeptAtEnd`: the active mark survives both runs, the decided instance of
  `keeps_active_production`.
-/

namespace KatLang.PlanConservativityAdmissibleGuards

/-- No `meta` parameter in a callee's signature (a user algorithm's parameter patterns or a
    builtin's authoritative signature). -/
def admissibleCallee : Algorithm → Bool
  | .mk _ patterns _ _ _ _ => !ParameterPattern.anyHasMetaCapture patterns
  | .builtin b => !builtinDeclaresMeta b
  | _ => true

/-- The written callee of the plan, resolved and normalized from state `x`. -/
def normalizedCallee? (eff : NeedPlan.CallShape) (x : EvalState) : Option Algorithm :=
  match (resolveCalleeAlg eff.callee eff.caller).runState x with
  | (.ok g, y) =>
    match (NeedPlan.normalizeCallee g eff.caller).runState y with
    | (.ok n, _) => some n
    | _ => none
  | _ => none

/-- The entry part of the admissible reference-free domain, decided at a flight state. -/
def admissibleAt (shape : NeedPlan.CallShape) (a : Nat) (r : PlanRoute) (x : EvalState) : Bool :=
  let eff := NeedPlan.effective shape r
  activeAt x a && storedRefFreeB x && envRefFreeB eff.values &&
    r != .intrinsic && r != .algorithm &&
    (match normalizedCallee? eff x with
     | some g => admissibleCallee g
     | none => true)

/-- `storedRefFreeB` is the older guards' `refFree` state half. -/
def agreesWithRefFree (x : EvalState) (a : Nat) : Bool :=
  refFree x a == (activeAt x a && storedRefFreeB x)

/-- The flight of `setup`'s fresh cell, checked by `check`. -/
def atFresh {α : Type} (setup : EvalM (α × Nat))
    (check : Nat → NeedPlan.CallShape → PlanRoute → EvalState → Bool) : Bool :=
  match setup.run EvalState.empty with
  | .error _ => false
  | .ok ((_, a), s) =>
    match flight s a with
    | some (shape, r, x) => check a shape r x
    | none => false

/-! ## The domain holds, and the simulation with it, on META-free and loop-only plans -/

def admissibleAndConservative {α : Type} (setup : EvalM (α × Nat)) : Bool :=
  atFresh setup fun a shape r x =>
    admissibleAt shape a r x && agreesWithRefFree x a && conservativeAt shape a r x

#guard metaFreeSources.all fun src => admissibleAndConservative (fresh src)

/-- Only these two ordinary declarations belong to the loop fixture. In particular it does not
    inherit `CallReferenceGuards.decls`, whose uncalled explicit META binders would make a C# run
    fully retaining rather than loop-only. -/
def loopOnlyDecls : List (Ident × Algorithm) :=
  [("Inc", alg ["x"] [] [] [addE (.param "x") (.num 1)]),
   ("Loop", alg ["n"] [] [] [callN "repeat" [callN "Inc" [.param "n"], .num 3]])]

def loopOnlyRoot : Algorithm := algPrivate [] [] loopOnlyDecls [callN "Loop" [.num 5]]

/-- A loop-only plan: `Loop(5)` with `Loop(n) = repeat(Inc(n), 3)`, value 8. -/
def loopOnly : EvalM (Unit × Nat) := do
  let a ← supplyNeed (callN "Loop" [.num 5]) (preludeCtx loopOnlyRoot) []
  pure ((), a)

/-- A stored reference targets a written invocation whose VALUE has not been demanded. This is
    the obstruction to excluding references to every planned-but-unevaluated cell at once. -/
def hasRefToSuspendedPlan (s : EvalState) : Bool :=
  (storedRefs s).any fun b =>
    match s.needs[b]? with
    | some { state := .suspended, .. } => (NeedPlan.shapeAt? s.needs b).isSome
    | _ => false

#guard admissibleAndConservative loopOnly
#guard atFresh loopOnly fun a shape _ x => KatLang.CallPlanGuards.valueIs (plannedAt shape a x).1 8

/- The same two-declaration program reaches 8 through the production evaluator and stores a
   reference despite containing no explicit META declaration. -/
#guard match runResultWithState (.algorithmExpr loopOnlyRoot) with
  | .ok (v, s) => v == .atom 8 && !storedRefFreeB s && hasRefToSuspendedPlan s
  | .error _ => false

/- Entry checks alone do not exclude a user body that captures a call internally. -/
#guard admissibleAndConservative (freshMeta (callN "UseRef" [.num 3]))

/-! ## `StoredRefFree` is not kept by a loop-only run -/

/-- From an admissible, reference-free flight state, the planned AND the ordinary run of the
    loop-only plan both end with stored references — every one of them to the loop's step plan,
    none reaching the plan's own cell — and the simulation's conclusion holds. -/
def loopRunStoresReference : Bool :=
  atFresh loopOnly fun a shape r x =>
    let p := (plannedAt shape a x).2
    let o := (ordinaryAt shape a r x).2
    admissibleAt shape a r x &&
    !storedRefFreeB p && !storedRefFreeB o &&
    hasRefToSuspendedPlan p && hasRefToSuspendedPlan o &&
    !(storedRefs p).isEmpty && !(storedRefs p).contains a && !(refClosure p).contains a &&
    !(storedRefs o).contains a && !(refClosure o).contains a &&
    conservativeAt shape a r x
#guard loopRunStoresReference

/-! ## The active mark survives both runs (decided instance of `keeps_active_production`) -/

def activeKeptAtEnd {α : Type} (setup : EvalM (α × Nat)) : Bool :=
  atFresh setup fun a shape r x =>
    activeAt x a && activeAt (plannedAt shape a x).2 a && activeAt (ordinaryAt shape a r x).2 a

#guard metaFreeSources.all fun src => activeKeptAtEnd (fresh src)
#guard activeKeptAtEnd loopOnly
#guard [callN "UseRef" [.num 3], callN "Views" [.num 3], callN "Sign" [.num 0]].all
  fun src => activeKeptAtEnd (freshMeta src)

/-! ## The META counterexamples and the old obstacles are outside the domain -/

/- Counterexample 1 (`selfInvokeOutcomeDiffers`): the flight state stores a reference. -/
#guard atFlight selfInvokeDecls innerA fun _ a shape r x =>
  !admissibleAt shape a r x && !storedRefFreeB x && agreesWithRefFree x a
/- Counterexample 2 (`viewReadHeapDiffers`): the same. -/
#guard atFlight viewReadDecls inner2 fun _ a shape r x =>
  !admissibleAt shape a r x && !storedRefFreeB x && agreesWithRefFree x a

/- `referenceExclusionsFailPush`'s pushed Ready reference is no admissible allocation: it is
    neither an expression cell nor a reference-free Ready value. -/
#guard !cellRefFreeB { suspension := .ready (.callRef 0, 1) }
#guard (Result.callRef 0).containsCallRef

/- `unrestrictedDispatchCreatesRef`'s callee declares a `meta` parameter: its dispatch is outside
    `PlanCallsOn` at the `admissibleCallee` contract. The loop builtins are META-binding too, so a
    PLAN whose own callee is `repeat`/`while` is outside it as well (a loop INSIDE a plan's body is
    not: `loopOnly` is admissible). -/
#guard !admissibleCallee (algWithParameters [KatLang.CallReferenceGuards.metaParam "op"] [] [] [.param "op"])
#guard !admissibleCallee (.builtin .repeatBuiltin) && !admissibleCallee (.builtin .whileBuiltin)
#guard admissibleCallee (.builtin .ifBuiltin)

/- `valueThenMetaThenFresh` retains an older reference: it is outside `StoredRefFree` although
    its simulation holds (the reference does not reach the new cell). -/
#guard atFresh valueThenMetaThenFresh fun a shape r x =>
  !admissibleAt shape a r x && agreesWithRefFree x a && conservativeAt shape a r x

end KatLang.PlanConservativityAdmissibleGuards
