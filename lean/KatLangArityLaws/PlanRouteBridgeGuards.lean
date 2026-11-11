import KatLangArityLaws.PlanRouteBridge
import KatLangArityLaws.PlanConservativityGuards
import KatLangArityLaws.InvocationRouteGuards

open KatLang KatLang.CallPlan KatLang.PlanRouteBridge
open KatLang.InvocationRouteGuards (dot algoCall grouped inId failsWith valueIs)
open KatLang.PlanConservativityGuards (preludeCtx flight)

/-!
# Plan-route bridge guards: the `.Algorithm`, extension and member routes (ledger E-18, step 1)

Every guard runs the authoritative evaluator from `EvalState.empty`, in a prelude root holding the
`InvocationRouteGuards` declarations (`Box = { Step, G(x) = x * 10, V = 7 }`,
`Box5 = { Algorithm(0) = 0 }`, `Pack = { F(0) = 0 }`, `R = Capture(F(0))`, `Q = Capture(Pack.F(0))`,
`S = Capture(Sq(2))`, `X = Mk2(5)`, `F(0) = 0`, `G(x, 0) = x`, …) and this module's own
(`Empty = { }`, `Lib = { Sub = { H(x) = x + 1, K = 3, Fam(0) = 0 } }`, `AB = Box` a transparent
reference, `Nil = ()`, `L = [1, 2]`). The written source is supplied as a fresh cell — the plan —
and the checks instantiate the theorems of `PlanRouteBridge.lean` at concrete states. `same`
compares outcomes AND final states.

* **Member route** (`memberIn`): the hypotheses of `member_bridge` — the probe, the member selection
  and the receiver premise `member_projection_of_selection` discharges — and its CONCLUSION: the
  member-route ordinary call and the re-counted production dot evaluation are ONE run from ONE
  state. Successful and failing calls; named receivers, member paths, an inline block, a transparent
  reference and a parameter (`member_bridge_static` / `member_bridge_param`); plain, empty and
  spread-first bundles (`member_bridge_inert`, with `NavInert` checked by `navInertAt`).
  `memberNameAgrees` is the REGRESSION of the former correspondence witness: `Box5.Algorithm(1)`
  reported `noMatchingBranch "Box5.Algorithm"` on the plan route and `"Algorithm"` in production
  until the E-18 member-route correction (`NeedPlan.writtenDispatchName`); both now report the member.
* **Extension route**, from the probe's exit state: `classify_dot` and
  `ordinaryCall_extension_is_dot_call` (`extensionAt`: outcome, error context and final state equal).
* **`.Algorithm` route**, at the plan's own flight (cell `evaluating`, route recorded by `routeOf`):
  the plan-side decomposition `ordinaryCall_algorithm_is_production` (`algorithmAt`) and the heap
  facts of `algorithm_tail_name_origin` (`tailAt`). Its correspondence with the ordinary intrinsic is
  NOT a theorem: `algorithmHeapDiffers`, a permanent witness, shows full-state equality false even
  when both runs start at the SAME flight state and return `(0, 1)` — only the plan side allocates
  the link and receiver cells and records its callee.
* **The receiver read (D-3; E-18 receiver-read correction, November 11 2026).** The plan's retained
  receiver cell keeps the ordinary invocation receiver evaluator, so the two routes report ONE
  outcome — finite evidence, on every receiver tried:
  - `algorithmReceiverFailureAgrees` is the REGRESSION of the former witness
    `algorithmReceiverFailureDiffers`: for a receiver without output (`Empty.Algorithm(0)`,
    `(Empty.Algorithm)(0)`), the plan route reported the receiver's OWN missing output under a
    property frame while its receiver cell was an ordinary supplied VALUE; both routes now report
    the NESTED, unframed one, as C# always did (`AlgorithmRouteDiagnosticNameTests`);
  - `algorithmOutcomeAgrees` over receivers that fail or are no call reference (`failingReceivers`,
    both written forms) and over receivers that yield one;
  - `receiverCellAt` — the heap facts of the correction (`receiverCell_establishes_invocation`) and
    the hypotheses and conclusions of `receiver_cell_reads_invocation_receiver` and
    `invocationReceiverValue_eq`; `receiverMemoAt` — the memoized read, the link's CALLABLE memo
    untouched; `paramReceiverAt` — a parameter receiver (`plannedReceiverValue_param`);
  - whole programs: the ordinary row, the plan read through a parameter and the plan invoked afresh
    report one failure (`threeConsumers`), also under a spread; the plan's callee link over a
    parameter receiver; and the receiver is read lazily and once per plan (`tick()`-counted).
-/

namespace KatLang.PlanRouteBridgeGuards

def add (a b : Expr) : Expr := .binary .add a b
def invoked (e : Expr) : Expr := dot (.call (.resolve "Capture") [e]) "Invoke" (some [])
def spr (e : Expr) : Expr := .listLiteral [.sequenceSpread e]
def tick : Expr := .call (.resolve "tick") []
/-- `Forced(tick(), R)`: a receiver whose every evaluation advances the run's `tick()` counter. -/
def counted : Expr := .call (.resolve "Forced") [tick, .resolve "R"]

def boxBlock : Algorithm :=
  algPrivate [] [] [("G", alg ["x"] [] [] [.binary .mul (.param "x") (.num 10)]), ("V", alg [] [] [] [.num 7])] []

def extra : List (Ident × Algorithm) :=
  [("Empty", alg [] [] [] []),
   ("Lib", algPrivate [] [] [
      ("Sub", algPrivate [] [] [
        ("H", alg ["x"] [] [] [add (.param "x") (.num 1)]),
        ("K", alg [] [] [] [.num 3]),
        ("Fam", KatLang.InvocationRouteGuards.zeroFamily)] [])] []),
   ("AB", .alias none [] [] (.resolve "Box")),
   ("Nil", alg [] [] [] [.emptySequence 0]),
   ("L", alg [] [] [] [.listLiteral [.num 1, .num 2]]),
   -- `UseP(b) = Id(b.G(2))`, `UseO(b) = b.G(2)`; `FamP(b) = Id(b.F(1))`, `FamO(b) = b.F(1)`;
   -- `ReadP(b) = Id(b.V())`, `ReadO(b) = b.V()`: a member call over a PARAMETER receiver, as a plan
   -- and as the ordinary row.
   ("UseP", alg ["b"] [] [] [inId (dot (.param "b") "G" (some [.num 2]))]),
   ("UseO", alg ["b"] [] [] [dot (.param "b") "G" (some [.num 2])]),
   ("FamP", alg ["b"] [] [] [inId (dot (.param "b") "F" (some [.num 1]))]),
   ("FamO", alg ["b"] [] [] [dot (.param "b") "F" (some [.num 1])]),
   ("ReadP", alg ["b"] [] [] [inId (dot (.param "b") "V" (some []))]),
   ("ReadO", alg ["b"] [] [] [dot (.param "b") "V" (some [])]),
   -- The `.Algorithm` receiver-read declarations (D-3): `Inner = Empty + 1` (a missing output nested in
   -- the receiver's own evaluation), `AE = Empty` and `RA = R` (transparent references), `Seven = 7`,
   -- `NeedsArg(x) = x`, `Fail(x) = x / 0`; the parameter-receiver wrappers `PO(r) = r.Algorithm(0)`,
   -- `PP(r) = Id(r.Algorithm(0))`, `PI(r) = Capture(r.Algorithm(0)).Invoke()` and the same three under
   -- a spread (`SO`, `SJ`, `SI`); `Forced(a, b) = if(a > 0, b, b)` (forces `a`, returns `b`),
   -- `Twice(meta op) = op.Invoke() + op.Invoke()`, `Both(meta op) = op.Algorithm(0) + op.Invoke()`,
   -- `Dup(x) = x + x`.
   ("Inner", alg [] [] [] [add (.resolve "Empty") (.num 1)]),
   ("AE", .alias none [] [] (.resolve "Empty")),
   ("RA", .alias none [] [] (.resolve "R")),
   ("Seven", alg [] [] [] [.num 7]),
   ("NeedsArg", alg ["x"] [] [] [.param "x"]),
   ("Fail", alg ["x"] [] [] [.binary .div (.param "x") (.num 0)]),
   ("PO", alg ["r"] [] [] [algoCall (.param "r") [.num 0]]),
   ("PP", alg ["r"] [] [] [inId (algoCall (.param "r") [.num 0])]),
   ("PI", alg ["r"] [] [] [invoked (algoCall (.param "r") [.num 0])]),
   ("SO", alg ["r"] [] [] [spr (algoCall (.param "r") [.num 0])]),
   ("SJ", alg ["r"] [] [] [spr (inId (algoCall (.param "r") [.num 0]))]),
   ("SI", alg ["r"] [] [] [spr (invoked (algoCall (.param "r") [.num 0]))]),
   ("Forced", alg ["a", "b"] [] [] [.call (.resolve "if") [.compare .gt (.param "a") (.num 0), .param "b", .param "b"]]),
   ("Twice", algWithParameters [KatLang.InvocationRouteGuards.metaParam "op"] [] []
      [add (dot (.param "op") "Invoke" (some [])) (dot (.param "op") "Invoke" (some []))]),
   ("Both", algWithParameters [KatLang.InvocationRouteGuards.metaParam "op"] [] []
      [add (algoCall (.param "op") [.num 0]) (dot (.param "op") "Invoke" (some []))]),
   ("Dup", alg ["x"] [] [] [add (.param "x") (.param "x")]),
   -- `LinkOf(r) = Capture(r.Algorithm(0)).Algorithm(0)`: the plan's callee link observed through
   -- `.Algorithm`, not an execution of the plan.
   ("LinkOf", alg ["r"] [] [] [algoCall (.call (.resolve "Capture") [algoCall (.param "r") [.num 0]]) [.num 0]]),
   -- `PT(r) = Twice(r.Algorithm(0))`: a plan over a PARAMETER receiver, executed twice.
   ("PT", alg ["r"] [] [] [.call (.resolve "Twice") [algoCall (.param "r") [.num 0]]])]

def decls : List (Ident × Algorithm) :=
  KatLang.InvocationRouteGuards.decls ++ KatLang.InvocationRouteGuards.diagDecls ++ extra

def root : Algorithm := algPrivate [] [] decls []
def ctx : EvalCtx := preludeCtx root

def same {α : Type} [Repr α] (x y : Except Error α × EvalState) : Bool :=
  reprStr x.1 == reprStr y.1 && reprStr x.2 == reprStr y.2

/-- The reached state after supplying `src` as a fresh cell, and its address. -/
def supplied (src : Expr) : Option (Nat × EvalState) :=
  match (supplyNeed src ctx []).runState EvalState.empty with
  | (.ok a, s) => some (a, s)
  | _ => none

/-- A whole program over the same declarations, through the public run. -/
def run (rows : List Expr) : Except Error Result := runResult (.algorithmExpr (algPrivate [] [] decls rows))

/-! ## The member route: `member_bridge` and its receiver and origin premises -/

/-- The hypotheses and the conclusion of `member_bridge` for `target.N(args)` written in context `c`,
    supplied as a fresh plan cell from state `s₀`: the probe selects a declared member, the plan's
    structural projection reaches it at the probe's exit state (`member_projection_of_selection`),
    the plan route classifies the edge as a call through that same probe (`classify_dot`), and the
    member-route ordinary call IS the re-counted production dot evaluation — one run, one state. -/
def memberIn (c : EvalCtx) (s₀ : EvalState) (target : Expr) (N : Ident) (args : List Expr) : Bool :=
  let path : Expr := .dotMember target N (.resolve N) none
  let src := dot target N (some args)
  match (supplyNeed src c []).runState s₀, NeedPlan.callShape? src c [] with
  | (.ok a, s), some shape =>
    match (resolveDotReceiver? target c).runState s with
    | (.ok alg?, s') =>
      match selectDotEdge c target N alg? with
      | .ok (.member owner p) =>
        same ((projectNeedStructuralMember path c).runState s) (.ok (some (childOfInContext owner p.alg c)), s') &&
        same ((productionPlanRoute.classify shape).runState s) (.ok .call, s') &&
        same ((ordinaryCall productionPlanRoute a shape .call).runState s)
          ((reCountValueBoundary <$> evalCounted src c []).runState s)
      | _ => false
    | _ => false
  | _, _ => false

def memberAt (target : Expr) (N : Ident) (args : List Expr) : Bool := memberIn ctx EvalState.empty target N args

def Box : Expr := .resolve "Box"
def sub : Expr := dot (.resolve "Lib") "Sub" none
def spread (e : Expr) : Expr := .sequenceSpread e

-- Named receivers, a plain first argument (`member_bridge_named`): successes and failures.
#guard memberAt Box "G" [.num 2]                         -- `Box.G(2)` = 20
#guard memberAt Box "Step" [.num 0]                      -- a two-row member
#guard memberAt Box "G" [.num 1, .num 2]                 -- an arity failure, same context
#guard memberAt (.resolve "Box5") "Algorithm" [.num 0]   -- a declared member `Algorithm`, matching branch
#guard memberAt (.resolve "Box5") "Algorithm" [.num 1]   -- THE FORMER COUNTEREXAMPLE: now one run
#guard memberAt (.resolve "Pack") "F" [.num 1]           -- a failing family, named by its member
-- Member paths, an inline block, a transparent reference (`member_bridge_static`).
#guard memberAt sub "H" [.num 2]                         -- `Lib.Sub.H(2)` = 3
#guard memberAt sub "Fam" [.num 1]                       -- `Lib.Sub.Fam(1)`: `noMatchingBranch "Fam"`
#guard memberAt (.algorithmExpr boxBlock) "G" [.num 2]   -- `{ … }.G(2)` = 20
#guard memberAt (.resolve "AB") "G" [.num 2]             -- `AB = Box`: the reference navigates its target
-- Empty and spread-first bundles (`member_bridge_inert`): the origin is read, the publication made.
#guard memberAt Box "V" []                               -- `Box.V()` = 7, publishing V's entry
#guard memberAt Box "G" []                               -- `Box.G()`: the arity failure
#guard memberAt sub "K" []                               -- `Lib.Sub.K()` = 3
#guard memberAt sub "Fam" []                             -- an empty family supply
#guard memberAt Box "V" [spread (.resolve "Nil")]        -- `Box.V(Nil*)`: a spread forming no slot
#guard memberAt Box "G" [spread (.resolve "L")]          -- `Box.G(L*)`: a spread forming two slots
#guard memberAt (.algorithmExpr boxBlock) "V" []         -- `{ … }.V()`
-- A transparent reference with an empty bundle is outside `NavInert` (its structure is a chase);
-- the run equality still holds here — finite evidence, not a theorem.
#guard memberAt (.resolve "AB") "V" []
-- Negative controls: a structural miss selects no member (the extension route), and a value head
-- has no member to select — `memberIn` is not vacuously true.
#guard !memberAt Box "Inc" []
#guard !memberAt (.num 5) "G" [.num 0]

/-- `NavInert target ctx owner`, at two different states: the receiver's projected structure is the
    probe's `owner`, and reading it changes neither state. -/
def navInertAt (target : Expr) : Bool :=
  match supplied (dot target "V" (some [])) with
  | some (_, s) =>
    match (resolveDotReceiver? target ctx).runState s with
    | (.ok (some owner), _) =>
      same ((projectedStructure target ctx).runState s) (.ok (some owner), s) &&
      same ((projectedStructure target ctx).runState EvalState.empty) (.ok (some owner), EvalState.empty) &&
      structureNormal owner
    | _ => false
  | none => false

#guard navInertAt Box
#guard navInertAt sub
#guard navInertAt (.algorithmExpr boxBlock)

/-- **Regression of the former correspondence witness.** `Box5.Algorithm(1)`: the plan route's member
    dispatch and production's are named alike — the MEMBER — under the same dot context. -/
def memberNameAgrees : Bool :=
  let src := dot (.resolve "Box5") "Algorithm" (some [.num 1])
  match supplied src, NeedPlan.callShape? src ctx [] with
  | some (a, s), some shape =>
    (match ((ordinaryCall productionPlanRoute a shape .call).runState s).1, ((evalCounted src ctx []).runState s).1 with
     | .error (.withContext c₁ (.noMatchingBranch n₁)), .error (.withContext c₂ (.noMatchingBranch n₂)) =>
       c₁ == c₂ && n₁ == "Algorithm" && n₂ == "Algorithm"
     | _, _ => false)
  | _, _ => false
#guard memberNameAgrees

/-- **The premise `hm` of `PlanConservativity.ordinaryCall_is_written_call` is necessary, and
    `ordinaryCall_is_written_call_named` is what holds without it.** For the member call
    `Box5.Algorithm(1)` — the `.call` route of a dot edge — the plan's ordinary call, the production
    written call named by the written callee PATH (`writtenCall`, the conclusion the premise now
    excludes) and the production written call named by the route's dispatch name
    (`writtenCallNamed … writtenDispatchName`) all fail with `noMatchingBranch`: the first and the
    third name the member `Algorithm`, the second the path `Box5.Algorithm`. So the path-named
    statement is false exactly on the excluded case, and the member-named one replaces it there. -/
def memberCallIsNotPathNamed : Bool :=
  let src := dot (.resolve "Box5") "Algorithm" (some [.num 1])
  match supplied src, NeedPlan.callShape? src ctx [] with
  | some (a, s), some shape =>
    let eff := NeedPlan.effective shape .call
    (match ((ordinaryCall productionPlanRoute a shape .call).runState s).1,
        ((KatLang.PlanConservativity.writtenCall shape.ctxMsg eff).runState s).1,
        ((KatLang.PlanConservativity.writtenCallNamed shape.ctxMsg eff
          (NeedPlan.writtenDispatchName eff .call)).runState s).1 with
     | .error (.withContext _ (.noMatchingBranch n₁)), .error (.withContext _ (.noMatchingBranch n₂)),
       .error (.withContext _ (.noMatchingBranch n₃)) =>
       n₁ == "Algorithm" && n₂ == "Box5.Algorithm" && n₃ == "Algorithm"
     | _, _, _ => false) &&
    same ((ordinaryCall productionPlanRoute a shape .call).runState s)
      ((KatLang.PlanConservativity.writtenCallNamed shape.ctxMsg eff
        (NeedPlan.writtenDispatchName eff .call)).runState s)
  | _, _ => false
#guard memberCallIsNotPathNamed

/-! ### A parameter receiver (`member_bridge_param`) -/

/-- A context binding the parameter `b` to a supplied cell holding the written `Box`. -/
def paramSetup : Option (EvalCtx × EvalState) :=
  match (supplyNeed Box ctx []).runState EvalState.empty with
  | (.ok cell, s) => some ({ ctx with needEnv := [("b", cell)] }, s)
  | _ => none

/-- `member_bridge_param`: the head parameter's CALLABLE is structure-normal at the entry state, and
    the bridge holds. -/
def paramMemberAt (N : Ident) (args : List Expr) : Bool :=
  match paramSetup with
  | some (c, s₀) =>
    (match (supplyNeed (dot (.param "b") N (some args)) c []).runState s₀ with
     | (.ok _, s) =>
       (match (projectParameterCallable "b" c).runState s with
        | (.ok (some o), _) => structureNormal o
        | _ => false)
     | _ => false) &&
    headParam? (dot (.param "b") N none) == some "b" &&
    memberIn c s₀ (.param "b") N args
  | none => false

#guard paramMemberAt "G" [.num 2]                        -- `b.G(2)` with `b = Box`
#guard paramMemberAt "G" [.num 1, .num 2]                -- its arity failure
#guard paramMemberAt "Step" [.num 0]
-- An empty bundle over a parameter receiver is outside `NavInert` (the first projection writes the
-- cell's CALLABLE memo); the run equality still holds here — finite evidence, not a theorem.
#guard paramMemberAt "V" []

-- Whole programs: a member call over a parameter receiver, as a plan (`Id(b.N(…))`) and as the
-- ordinary row, successful and failing; the failing family is named by its member on both routes.
#guard valueIs (run [.call (.resolve "UseP") [Box], .call (.resolve "UseO") [Box]]) (.sequenceValue [.atom 20, .atom 20])
#guard valueIs (run [.call (.resolve "ReadP") [Box], .call (.resolve "ReadO") [Box]]) (.sequenceValue [.atom 7, .atom 7])
#guard failsWith (run [.call (.resolve "FamO") [.resolve "Pack"]])
  ["while evaluating call to FamO", "while evaluating dotCall .F of b", "noMatchingBranch F"]
#guard failsWith (run [.call (.resolve "FamP") [.resolve "Pack"]])
  ["while evaluating call to FamP", "while evaluating call to Id", "while evaluating dotCall .F of b",
   "noMatchingBranch F"]

/-! ## The extension route -/

/-- `classify_dot` and `ordinaryCall_extension_is_dot_call` for `target.F(args)` from the reached state. -/
def extensionAt (target : Expr) (F : Ident) (args : List Expr) : Bool :=
  let src := dot target F (some args)
  match supplied src, NeedPlan.callShape? src ctx [] with
  | some (a, s), some shape =>
    match (resolveDotReceiver? target ctx).runState s with
    | (.ok alg?, s') =>
      (match selectDotEdge ctx target F alg? with
       | .ok (.miss .extension) => true
       | _ => false) &&
      same ((productionPlanRoute.classify shape).runState s) (.ok .extension, s') &&
      same ((ordinaryCall productionPlanRoute a shape .extension).runState s')
        ((reCountValueBoundary <$> evalCounted src ctx []).runState s)
    | _ => false
  | _, _ => false

#guard extensionAt (.num 5) "G" [.num 0]                -- `5.G(0)` is `G(5, 0)` = 5
#guard extensionAt (.num 5) "G" [.num 1]                -- a failing dispatch, same context and payload
#guard extensionAt (.num 5) "Inc" []                    -- `5.Inc()` = 6
#guard extensionAt Box "Inc" []                         -- a structural miss on an algorithm receiver

/-! ## The `.Algorithm` route -/

/-- `ordinaryCall_algorithm_is_production` at the plan's flight: the same outcome and final state. -/
def algorithmAt (src : Expr) : Bool :=
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      same ((ordinaryCall productionPlanRoute a shape .algorithm).runState x) ((algorithmPlanCall a shape).runState x)
    | _ => false

/-- The heap facts of `algorithm_tail_name_origin` after the callee phase: the plan cell records the
    link, the link's receiver is a completed `callRef p`, and the heap-read name and origin are `p`'s
    `calleeName` and `.cell` of `p`'s callee cell. -/
def tailAt (src : Expr) (expected : String) : Bool :=
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      match (withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee)).runState x with
      | (.ok _, t) =>
        match (t.needs[a]?).bind NeedCell.callee with
        | some l =>
          match NeedPlan.linkedPlanIn? t.needs l, NeedPlan.calleeNameIn? t.needs (NeedPlan.linkedPlanIn? t.needs l |>.getD 0) with
          | some p, some n =>
            n == expected && NeedPlan.dispatchNameIn t.needs a shape .algorithm == n &&
              (match (t.needs[p]?).bind NeedCell.callee with
               | some c => reprStr (NeedPlan.dispatchOriginIn t.needs a shape .algorithm) == reprStr (CalleeOrigin.cell c)
               | none => false)
          | _, _ => false
        | none => false
      | _ => false
    | _ => false

/-- The plan's ordinary outcome at its flight is the direct production intrinsic's outcome from the
    same state: the counted result, or the whole structured error (context chain, payload,
    missing-output origin). Finite evidence — the outcome bridge is not a theorem. -/
def outcomeAgreesIn (c : EvalCtx) (s₀ : EvalState) (src : Expr) : Bool :=
  match (supplyNeed src c []).runState s₀ with
  | (.ok a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      reprStr ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).1 ==
        reprStr ((reCountValueBoundary <$> evalCounted src c []).runState s).1 &&
      reprStr ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).1 ==
        reprStr ((reCountValueBoundary <$> evalCounted src c []).runState x).1
    | _ => false
  | _ => false

def algorithmOutcomeAgrees (src : Expr) : Bool := outcomeAgreesIn ctx EvalState.empty src

def algorithmSources : List Expr :=
  [algoCall (.resolve "R") [.num 0], algoCall (.resolve "R") [.num 1],
   grouped (.resolve "R") [.num 0], grouped (.resolve "R") [.num 1],
   algoCall (.resolve "S") [.num 3], algoCall (.resolve "S") [.num 1, .num 2],
   algoCall (.resolve "Q") [.num 0], algoCall (.resolve "Q") [.num 1],
   algoCall (.resolve "X") [.num 1]]

#guard algorithmSources.all algorithmAt
#guard algorithmSources.all algorithmOutcomeAgrees

/-- **Correspondence witness: the `.Algorithm` callee phases have different heaps.**
    At the SAME reached flight state for `R.Algorithm(0)`, both calls complete with `(0, 1)`.
    The plan's ordinary call additionally records its link callee and allocates the link/receiver
    cells; direct production evaluation does neither for this outer call. Equality of the full
    runs is therefore false here, even though their outcomes agree. This does not refute an
    outcome theorem under a suitable heap relation, or META-free conservativity. The receiver-read
    correction changed WHAT the receiver cell computes, not that the plan allocates it: the witness
    stands unchanged. -/
def algorithmHeapDiffers : Bool :=
  let src := algoCall (.resolve "R") [.num 0]
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      let planned := (ordinaryCall productionPlanRoute a shape .algorithm).runState x
      let produced := (reCountValueBoundary <$> evalCounted src ctx []).runState x
      let expected : Except Error CountedResult := .ok (.atom 0, 1)
      reprStr planned.1 == reprStr expected && reprStr produced.1 == reprStr expected &&
        planned.2.needs.size == produced.2.needs.size + 2 &&
        ((planned.2.needs[a]?).bind NeedCell.callee).isSome &&
        ((produced.2.needs[a]?).bind NeedCell.callee).isNone
    | _ => false

#guard algorithmHeapDiffers

/-! ### The receiver read (D-3): the E-18 receiver-read correction -/

def emptyBlock : Expr := .algorithmExpr (alg [] [] [] [])
def libSub : Expr := dot (.resolve "Lib") "Sub" none
def idOf (e : Expr) : Expr := .call (.resolve "Id") [e]
def nestedR : Expr := dot (.resolve "R") "Algorithm" none

/-- The receivers whose read FAILS or is not a call reference: without output (a name, an inline
    block, a member path), a missing output nested in the receiver's own evaluation, a transparent
    reference, a receiver that is itself a written call, a nested `.Algorithm` receiver, values.
    Each was a potential difference while the plan read its receiver as an ordinary supplied VALUE;
    three of them (`Empty`, `Lib.Sub`, `R.Algorithm`) differed, in both written forms. (An unknown
    receiver name fails the plan's route CLASSIFICATION, so it never reaches this route; the whole
    programs below cover it.) -/
def failingReceivers : List Expr :=
  [.resolve "Empty", emptyBlock, libSub, .resolve "Inner", .resolve "AE", idOf (.resolve "Empty"),
   .call (.resolve "Fail") [.num 1], nestedR, .resolve "Seven", .resolve "NeedsArg", .num 5]

-- Dot form and grouped call form, at the plan's flight: outcome for outcome.
#guard failingReceivers.all fun receiver => algorithmOutcomeAgrees (algoCall receiver [.num 0])
#guard failingReceivers.all fun receiver => algorithmOutcomeAgrees (grouped receiver [.num 0])
-- Receivers that DO yield a call reference: a transparent reference to one, a call returning one.
#guard algorithmOutcomeAgrees (algoCall (.resolve "RA") [.num 0])
#guard algorithmOutcomeAgrees (algoCall (.resolve "RA") [.num 1])
#guard algorithmOutcomeAgrees (algoCall (.call (.resolve "Mk") [.num 1]) [.num 5])
#guard algorithmOutcomeAgrees (algoCall (.call (.resolve "Capture") [.call (.resolve "F") [.num 0]]) [.num 1])

/-- The receiver's failure at the plan's flight for `src`: the plan's ordinary call and the direct
    production evaluation fail ALIKE — under the one frame `outer`, the NESTED missing output, and no
    `while evaluating property …` frame of the receiver's own. -/
def receiverFailureAgreesAt (src : Expr) (outer : String) : Bool :=
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      (match ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).1,
          ((reCountValueBoundary <$> evalCounted src ctx []).runState x).1 with
       | .error (.withContext c₁ (.missingOutput .nested)),
         .error (.withContext c₂ (.missingOutput .nested)) => c₁ == outer && c₂ == outer
       | _, _ => false)
    | _ => false

/-- **Regression of the former correspondence witness `algorithmReceiverFailureDiffers`.**
    `Empty = { }` has no output. Until the E-18 receiver-read correction (November 11 2026) the plan
    route read the receiver as its link's receiver cell — an ordinary supplied VALUE, `evalCounted
    Empty`: the property's OWN missing output under `while evaluating property Empty` — while the
    ordinary intrinsic read it through `referenceReceiverValue`, a subordinate read whose missing
    output is NESTED and unframed. The plan's receiver cell now keeps the invocation receiver
    evaluator (`NeedInvocationRole.receiver`, `receiver_cell_reads_invocation_receiver`), so the two
    routes report ONE structured failure — on the dot form, on the grouped call form, and through the
    public run (`Id(Empty.Algorithm(0))` is the row's failure under `Id`'s call frame), as C# always
    did (`AlgorithmRouteDiagnosticNameTests`). -/
def algorithmReceiverFailureAgrees : Bool :=
  receiverFailureAgreesAt (algoCall (.resolve "Empty") [.num 0]) "while evaluating dotCall .Algorithm of Empty" &&
  receiverFailureAgreesAt (grouped (.resolve "Empty") [.num 0]) "while evaluating call to Empty.Algorithm" &&
  (match run [algoCall (.resolve "Empty") [.num 0]], run [inId (algoCall (.resolve "Empty") [.num 0])] with
   | .error (.withContext c₁ (.missingOutput .nested)),
     .error (.withContext cId (.withContext c₂ (.missingOutput .nested))) =>
     c₁ == "while evaluating dotCall .Algorithm of Empty" && c₂ == c₁ && cId == "while evaluating call to Id"
   | _, _ => false)

#guard algorithmReceiverFailureAgrees

/-- The retained receiver cell of the plan supplied for `src = receiver.Algorithm(args)`
    (`receiverCell_establishes_invocation`, `receiver_cell_reads_invocation_receiver`), at the plan's
    flight:
    * establishing the plan's callee cell marks the link (`NeedInvocationRole.link`) and establishes
      NO receiver — the receiver cell is lazy;
    * the link's first receiver observation allocates ONE cell over the link's own suspension, marked
      `NeedInvocationRole.receiver`, suspended and unprojected, and evaluates nothing;
    * that cell's written-expression evaluator IS the production invocation receiver read — outcome
      and final state — which is the identity probe followed by the dot intrinsic's read
      (`invocationReceiverValue_eq`);
    * a second observation returns the same cell and changes nothing. -/
def receiverCellAt (src receiver : Expr) : Bool :=
  let edge := dot receiver "Algorithm" none
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (_, .algorithm, x) =>
      match (NeedPlan.calleeCell productionPlanRoute.classify a).runState x with
      | (.ok l, x₁) =>
        (match x₁.needs[l]? with
         | some link => link.invocation == .link && link.receiver.isNone && x₁.needs.size == x.needs.size + 1
         | none => false) &&
        (match (NeedLink.receiverCell l).runState x₁ with
         | (.ok rc, x₂) =>
           x₂.needs.size == x₁.needs.size + 1 && rc == x₁.needs.size &&
           (match x₂.needs[rc]?, x₂.needs[l]? with
            | some cell, some link =>
              cell.invocation == .receiver && reprStr cell.suspension == reprStr link.suspension &&
                (cell.state matches .suspended) && (cell.callable matches .unprojected) &&
                link.receiver == some rc
            | _, _ => false) &&
           same ((evalSuppliedAt rc edge ctx []).runState x₂)
             ((invocationReceiverValue receiver ctx [] >>= fun value =>
               (pure (value, Result.valueCount value) : EvalM CountedResult)).runState x₂) &&
           same ((invocationReceiverValue receiver ctx []).runState x₂)
             ((resolveDotReceiver? receiver ctx >>= fun alg? => algorithmReceiverValue receiver alg? ctx []).runState x₂) &&
           same ((NeedLink.receiverCell l).runState x₂) (.ok rc, x₂)
         | _ => false)
      | _ => false
    | _ => false

#guard receiverCellAt (algoCall (.resolve "Empty") [.num 0]) (.resolve "Empty")
#guard receiverCellAt (grouped (.resolve "Empty") [.num 0]) (.resolve "Empty")
#guard receiverCellAt (algoCall (.resolve "R") [.num 0]) (.resolve "R")
#guard receiverCellAt (algoCall libSub [.num 0]) libSub
#guard receiverCellAt (algoCall nestedR [.num 0]) nestedR
#guard receiverCellAt (algoCall (.call (.resolve "Mk") [.num 1]) [.num 5]) (.call (.resolve "Mk") [.num 1])

/-- After the whole callee phase the retained receiver cell is COMPLETED with the invocation
    receiver read's outcome — the memo every later channel reads (`decoded_link_reuses_receiver`) —
    and the link's own CALLABLE memo is untouched: the planned callee read is not the link's
    projection shell. -/
def receiverMemoAt (src : Expr) (succeeds : Bool) : Bool :=
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      let run := (withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee)).runState x
      (match run.1 with | .ok _ => succeeds | .error _ => !succeeds) &&
      (match (run.2.needs[a]?).bind NeedCell.callee with
       | some l =>
         match run.2.needs[l]? with
         | some link =>
           (link.callable matches .unprojected) &&
           (match link.receiver.bind (run.2.needs[·]?) with
            | some cell =>
              cell.invocation == .receiver &&
                (match cell.state with
                 | .completed (.ok (.callRef _, _)) => succeeds
                 | .completed (.error _) => !succeeds
                 | _ => false)
            | none => false)
         | none => false
       | none => false)
    | _ => false

#guard receiverMemoAt (algoCall (.resolve "R") [.num 0]) true
#guard receiverMemoAt (algoCall (.resolve "R") [.num 1]) true     -- the DISPATCH fails later; the receiver read succeeded
#guard receiverMemoAt (algoCall (.resolve "Empty") [.num 0]) false
#guard receiverMemoAt (algoCall libSub [.num 0]) false

/-! #### A parameter receiver -/

/-- A context binding the parameter `r` to a supplied cell holding the written `arg`. -/
def receiverParam (arg : Expr) : Option (EvalCtx × EvalState) :=
  match (supplyNeed arg ctx []).runState EvalState.empty with
  | (.ok cell, s) => some ({ ctx with needEnv := [("r", cell)] }, s)
  | _ => none

/-- `r.Algorithm(0)` / `(r.Algorithm)(0)` over a PARAMETER receiver bound to the written `arg`: the
    plan's ordinary call at its flight and the direct production intrinsic have ONE outcome. The
    link's receiver is the parameter's own cell — no receiver cell is allocated — and the planned
    callee read reads the written parameter through the invocation receiver evaluator
    (`plannedReceiverValue_param`), so a failing argument is reported as the intrinsic reports it:
    the NESTED missing output, not the transported cell's own. -/
def paramReceiverAt (arg : Expr) : Bool :=
  match receiverParam arg with
  | none => false
  | some (c, s₀) =>
    outcomeAgreesIn c s₀ (algoCall (.param "r") [.num 0]) &&
    outcomeAgreesIn c s₀ (grouped (.param "r") [.num 0]) &&
    (match (supplyNeed (algoCall (.param "r") [.num 0]) c []).runState s₀ with
     | (.ok a, s) =>
       (match flight s a with
        | some (shape, .algorithm, x) =>
          let run := (withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee)).runState x
          (match (run.2.needs[a]?).bind NeedCell.callee with
           | some l =>
             (match run.2.needs[l]? with
              | some link => link.invocation == .link && link.receiver == lookupAssoc "r" c.needEnv
              | none => false) &&
             run.2.needs.toList.all (fun cell => cell.invocation != .receiver)
           | none => false)
        | _ => false)
     | _ => false)

#guard paramReceiverAt (.resolve "Empty")   -- the transported cell fails with its OWN missing output; the read nests it
#guard paramReceiverAt emptyBlock
#guard paramReceiverAt libSub
#guard paramReceiverAt (.resolve "Inner")
#guard paramReceiverAt (.resolve "R")       -- a forwarded call reference: `(0, 1)` on both routes
#guard paramReceiverAt (.resolve "RA")
#guard paramReceiverAt (.num 5)

/-! #### Whole programs: the three consumers of the plan, and the receiver's demand count -/

/-- The whole structured failure of a program, frames first, with the missing-output origin. -/
def failureShape : Except Error Result → List String
  | .ok _ => ["ok"]
  | .error e => go e
where
  go : Error → List String
    | .withContext c inner => c :: go inner
    | .missingOutput .nested => ["missingOutput nested"]
    | .missingOutput .own => ["missingOutput own"]
    | .spreadMissingOutput => ["spreadMissingOutput"]
    | .noMatchingBranch n => [s!"noMatchingBranch {n}"]
    | .unknownName n => [s!"unknownName {n}"]
    | _ => ["other"]

def ctxInvoke : String := "while evaluating dotCall .Invoke of (call)"
def ctxId : String := "while evaluating call to Id"

/-- The ordinary row, the plan read through a parameter (`Id(row)`) and the plan executed afresh
    (`Capture(row).Invoke()`) report ONE failure below their own consumer frame. -/
def threeConsumers (row : Expr) (expected : List String) : Bool :=
  failureShape (run [row]) == expected && failureShape (run [inId row]) == ctxId :: expected &&
    failureShape (run [invoked row]) == ctxInvoke :: expected

#guard threeConsumers (algoCall (.resolve "Empty") [.num 0])
  ["while evaluating dotCall .Algorithm of Empty", "missingOutput nested"]
#guard threeConsumers (grouped (.resolve "Empty") [.num 0])
  ["while evaluating call to Empty.Algorithm", "missingOutput nested"]
-- A member-path receiver: no frame of the path's own dot evaluation.
#guard threeConsumers (algoCall libSub [.num 0])
  ["while evaluating dotCall .Algorithm of Lib.Sub", "missingOutput nested"]
-- A nested reference failure: the receiver `R.Algorithm` is the intrinsic's bare VALUE read, under its
-- own dot-call frame.
#guard threeConsumers (algoCall nestedR [.num 0])
  ["while evaluating dotCall .Algorithm of R.Algorithm", "while evaluating dotCall .Algorithm of R", "noMatchingBranch F"]
-- A missing output nested in the receiver's own evaluation keeps its frames.
#guard threeConsumers (algoCall (.resolve "Inner") [.num 0])
  ["while evaluating dotCall .Algorithm of Inner", "while evaluating property Empty", "missingOutput nested"]
-- A receiver that is itself a written call is read as the ordinary call, never as a plan of its own.
#guard threeConsumers (algoCall (idOf (.resolve "Empty")) [.num 0])
  ["while evaluating dotCall .Algorithm of (call)", "while evaluating call to Id", "while evaluating property Empty",
   "missingOutput nested"]
-- An unknown receiver: the identity resolution's failure, on the row and as the plan's route failure.
#guard threeConsumers (algoCall (.resolve "Missing") [.num 0])
  ["while evaluating dotCall .Algorithm of Missing", "unknownName Missing"]
-- The captured callee's own failure is unchanged (META-S3-4-DIAG).
#guard threeConsumers (algoCall (.resolve "R") [.num 1])
  ["while evaluating dotCall .Algorithm of R", "noMatchingBranch F"]

-- Under a SPREAD an operand's OWN missing output would become `spreadMissingOutput`: the receiver's
-- stays nested on every route (before the correction the invoked plan reported `spreadMissingOutput`).
#guard [algoCall (.resolve "Empty") [.num 0], inId (algoCall (.resolve "Empty") [.num 0]),
    invoked (algoCall (.resolve "Empty") [.num 0]), invoked (grouped (.resolve "Empty") [.num 0])].all fun row =>
  (failureShape (run [spr row])).getLast? == some "missingOutput nested" &&
    !(failureShape (run [spr row])).contains "while evaluating property Empty"

-- A PARAMETER receiver, through the public run: `PO(r) = r.Algorithm(0)`, `PP(r) = Id(r.Algorithm(0))`,
-- `PI(r) = Capture(r.Algorithm(0)).Invoke()` and the same three under a spread (`SO`, `SJ`, `SI`).
#guard ["PO", "PP", "PI", "SO", "SJ", "SI"].all fun wrapper =>
  (failureShape (run [.call (.resolve wrapper) [.resolve "Empty"]])).drop
      ((failureShape (run [.call (.resolve wrapper) [.resolve "Empty"]])).length - 3) ==
    ["while evaluating dotCall .Algorithm of r", "while evaluating property Empty", "missingOutput nested"]
#guard ["PO", "PP", "PI", "SO", "SJ", "SI"].all fun wrapper =>
  (failureShape (run [.call (.resolve wrapper) [emptyBlock]])).drop
      ((failureShape (run [.call (.resolve wrapper) [emptyBlock]])).length - 2) ==
    ["while evaluating dotCall .Algorithm of r", "missingOutput nested"]
#guard valueIs (run [.call (.resolve "PO") [.resolve "R"], .call (.resolve "PP") [.resolve "R"],
    .call (.resolve "PI") [.resolve "R"]]) (.sequenceValue [.atom 0, .atom 0, .atom 0])

-- The plan's CALLEE LINK observed through `.Algorithm` — not an execution of the plan — demands a
-- parameter receiver's transported cell: the link's own channel (D-3), unchanged by the correction.
#guard failureShape (run [.call (.resolve "LinkOf") [.resolve "Empty"]]) ==
  ["while evaluating call to LinkOf", "while evaluating dotCall .Algorithm of (call)",
   "while evaluating property Empty", "missingOutput nested"]
#guard valueIs (run [.call (.resolve "LinkOf") [.resolve "R"]]) (.atom 0)

-- LAZY and ONCE per plan (D-3): the final `tick()` counts the receiver's evaluations.
-- Capture alone reads nothing.
#guard valueIs (run [.call (.resolve "Ignore") [algoCall counted [.num 0]], tick])
  (.sequenceValue [.atom 0, .atom 1])
-- Two `Invoke()`s of one plan read the receiver once.
#guard valueIs (run [.call (.resolve "Twice") [algoCall counted [.num 0]], tick])
  (.sequenceValue [.atom 0, .atom 2])
#guard valueIs (run [.call (.resolve "Twice") [grouped counted [.num 0]], tick])
  (.sequenceValue [.atom 0, .atom 2])
-- The plan's `.Algorithm` (its callee link's CALLABLE) and its `Invoke()` share the one receiver cell.
#guard valueIs (run [.call (.resolve "Both") [algoCall counted [.num 0]], tick])
  (.sequenceValue [.atom 0, .atom 2])
-- The plan's VALUE, read twice through a parameter.
#guard valueIs (run [.call (.resolve "Dup") [algoCall counted [.num 0]], tick])
  (.sequenceValue [.atom 0, .atom 2])
-- Two ordinary rows read it once each.
#guard valueIs (run [add (algoCall counted [.num 0]) (algoCall counted [.num 0]), tick])
  (.sequenceValue [.atom 0, .atom 3])
-- A PARAMETER receiver: each execution reads the written parameter through the invocation receiver
-- evaluator, and the parameter's own cell holds the VALUE — its argument is evaluated once.
#guard valueIs (run [.call (.resolve "PT") [counted], tick]) (.sequenceValue [.atom 0, .atom 2])
-- Alias forwarding: a transparent reference to a call reference, on the three routes.
#guard valueIs (run [algoCall (.resolve "RA") [.num 0], inId (algoCall (.resolve "RA") [.num 0]),
    invoked (algoCall (.resolve "RA") [.num 0])]) (.sequenceValue [.atom 0, .atom 0, .atom 0])

#guard tailAt (algoCall (.resolve "R") [.num 1]) "F"
#guard tailAt (grouped (.resolve "R") [.num 0]) "F"
#guard tailAt (algoCall (.resolve "Q") [.num 1]) "Pack.F"
#guard tailAt (algoCall (.resolve "S") [.num 3]) "Sq"
-- A failing callee projection (`X = Mk2(5)` captures `f(1)` with `f = 5`) ends the callee phase:
-- no tail runs, so `tailAt` has nothing to read.
#guard !tailAt (algoCall (.resolve "X") [.num 1]) "f"

end KatLang.PlanRouteBridgeGuards
