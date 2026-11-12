import KatLangArityLaws.MemberStability
import KatLangArityLaws.PlanRouteBridgeGuards

open KatLang KatLang.CallPlan KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.InvocationRouteGuards (dot algoCall inId valueIs failsWith)
open KatLang.PlanConservativityGuards (preludeCtx)
open KatLang.PlanRouteBridgeGuards (same memberIn boxBlock spread)

/-!
# Member-route stability guards (ledger E-18, step 1, M1)

Every guard runs the authoritative evaluator from `EvalState.empty`, in a prelude root holding the
`PlanRouteBridgeGuards` declarations and this module's own:

    FM(x) = { V = 7, G(y) = y ⏎ x }       -- a callable that declares members
    MkFM(x) = Capture(FM(x))              RC = Capture(FM(0))
    RTA = RC.Algorithm                    -- a runtime-target alias over a static receiver
    MTA = 5.MkFM.Algorithm                -- a runtime-target alias whose receiver is a DOT RESULT
    AB2 = AB                              -- a chain of transparent references (`AB = Box`)
    ALS = Lib.Sub                         -- a transparent reference to a member path
    OLib = { public OBox = { G(x) = x * 10, V = 7 } }, opened by the root (`open OLib`)
    Zero = 1 / 0                          -- a failing spread operand

`settledIn` checks the decidable equations of `MemberStability.member_bridge_settled`: its probe, selection and receiver
premises (`PlanRouteBridgeGuards.memberIn`), its settledness premise at the state the member run
reads its callee origin in, the same settledness at the probe's exit (the state `NavStable` is
established at), and its CONCLUSION — the member-route ordinary call and the re-counted production
dot evaluation are one run from one state. `paramStableAt` checks the decidable premises and
conclusion of `member_bridge_param_stable`, with no `NavInert` condition. These are executable
guards, not applications of the final theorems; no quantified `NavStable` instance is proved here.
THEOREM applications — every premise proved, on genuine source programs — are
`MemberBridgeSourceInstances` and its companions (`member_bridge_settled` over every receiver class
and bundle kind) and `MemberSettledInstances` (the quantified `NavSettled` DERIVED from the probe,
for references to a named target, opened names, nested paths and parameters); since the M1
completion pass `MemberRereadInstances` applies the general `member_bridge_of_probe` to every
receiver class, runtime-target aliases and path-row references included.

`memberOriginRemintsRuntimeIdentity` is the PERMANENT WITNESS that the settledness premise is
necessary: over `MTA`, an empty and a spread-first bundle make the plan's final state differ from
production's by exactly one minted runtime declaration identity, with equal outcomes.
-/

namespace KatLang.MemberStabilityGuards

def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args

/-- `FM(x) = { V = 7, G(y) = y ⏎ x }`: a callable that declares members. -/
def fm : Algorithm :=
  algPrivate ["x"] [] [("V", alg [] [] [] [.num 7]), ("G", alg ["y"] [] [] [.param "y"])] [.param "x"]

def extra : List (Ident × Algorithm) :=
  [("FM", fm),
   ("MkFM", alg ["x"] [] [] [callN "Capture" [callN "FM" [.param "x"]]]),
   ("RC", alg [] [] [] [callN "Capture" [callN "FM" [.num 0]]]),
   ("RTA", .alias none [] [] (dot (.resolve "RC") "Algorithm" none)),
   ("MTA", .alias none [] [] (dot (dot (.num 5) "MkFM" none) "Algorithm" none)),
   ("AB2", .alias none [] [] (.resolve "AB")),
   ("ALS", .alias none [] [] (dot (.resolve "Lib") "Sub" none)),
   ("Zero", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
   -- `CapP(b) = { W = Id(b.V()) ⏎ W }`, `CapO(b) = { W = b.V() ⏎ W }`: the member call over a parameter
   -- read from a CAPTURED activation, as a plan and as the ordinary row.
   ("CapP", algPrivate ["b"] [] [("W", alg [] [] [] [inId (dot (.param "b") "V" (some []))])] [.resolve "W"]),
   ("CapO", algPrivate ["b"] [] [("W", alg [] [] [] [dot (.param "b") "V" (some [])])] [.resolve "W"])]

def openedLib : Algorithm := alg [] [] [publicProp "OBox" boxBlock] []

def decls : List (Ident × Algorithm) :=
  KatLang.PlanRouteBridgeGuards.decls ++ extra ++ [("OLib", openedLib)]

/-- The root opens `OLib`, so `OBox` is a name selected through `open`. -/
def root : Algorithm := algPrivate [] [.resolve "OLib"] decls []
def ctx : EvalCtx := preludeCtx root

def run (rows : List Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [.resolve "OLib"] decls rows))

/-! ## `member_bridge_settled`: the settledness premise and the conclusion -/

/-- Whether the supply formation of `args` from the state the member's alias resolution leaves
    completes with a formed supply (`some true`), fails (`some false`), or is never reached. -/
def formationAt (c : EvalCtx) (s' : EvalState) (owner : Algorithm) (p : PropDef) (args : List Expr) :
    Option (Option EvalState) :=
  match (resolveAliasTarget (childOfInContext owner p.alg c) c).runState s' with
  | (.ok _, t) =>
    match (NeedSupply.form evalSupplySpread c [] args).runState t with
    | (.ok _, u) => some (some u)
    | (.error _, _) => some none
  | (.error _, _) => none

/-- The hypotheses and the conclusion of `member_bridge_settled` for `target.N(args)` written in
    context `c`, supplied as a fresh plan cell from `s₀`: the probe selects a declared member and the
    plan's projection reaches it (`memberIn`, which also checks the CONCLUSION); the receiver's
    navigation is settled at the probe's exit state and — the theorem's premise — at the state the
    member run reads its origin in, after the member's alias resolution and the supply formation. -/
def settledIn (c : EvalCtx) (s₀ : EvalState) (target : Expr) (N : Ident) (args : List Expr) : Bool :=
  let src := dot target N (some args)
  match (supplyNeed src c []).runState s₀ with
  | (.ok _, s) =>
    match (resolveDotReceiver? target c).runState s with
    | (.ok alg?, s') =>
      match selectDotEdge c target N alg? with
      | .ok (.member owner p) =>
        same ((projectedStructure target c).runState s') (.ok (some owner), s') &&
        (match formationAt c s' owner p args with
         | some (some u) => same ((projectedStructure target c).runState u) (.ok (some owner), u)
         | _ => true) &&
        memberIn c s₀ target N args
      | _ => false
    | _ => false
  | _ => false

def settledAt (target : Expr) (N : Ident) (args : List Expr) : Bool := settledIn ctx EvalState.empty target N args

/-- The formation of `args` after the probe of `target.N` FAILS: the origin is never read. -/
def formationFails (target : Expr) (N : Ident) (args : List Expr) : Bool :=
  match (supplyNeed (dot target N (some args)) ctx []).runState EvalState.empty with
  | (.ok _, s) =>
    match (resolveDotReceiver? target ctx).runState s with
    | (.ok alg?, s') =>
      match selectDotEdge ctx target N alg? with
      | .ok (.member owner p) =>
        (match formationAt ctx s' owner p args with
         | some none => true
         | _ => false)
      | _ => false
    | _ => false
  | _ => false

def AB : Expr := .resolve "AB"
def Nil : Expr := .resolve "Nil"
def L : Expr := .resolve "L"

-- Transparent references (a chase): empty, spread-first without and with cells, a failing spread.
#guard settledAt AB "V" []                              -- `AB.V()`, publishing V's entry
#guard settledAt AB "V" [spread Nil]                    -- `AB.V(Nil*)`: a spread forming no slot
#guard settledAt AB "G" [spread L]                      -- `AB.G(L*)`: a spread forming two slots
#guard settledAt AB "G" [spread (.resolve "Zero")]      -- a failing spread: the formation's failure
#guard formationFails AB "G" [spread (.resolve "Zero")]
#guard settledAt (.resolve "AB2") "V" []                -- a chain of references
#guard settledAt (.resolve "AB2") "V" [spread Nil]
#guard settledAt (.resolve "ALS") "K" []                -- a reference to a member path
#guard settledAt (.resolve "ALS") "Fam" []              -- an empty family supply
-- A runtime-target alias over a static receiver (its binding cell, its projection, its chase).
#guard settledAt (.resolve "RTA") "V" []
#guard settledAt (.resolve "RTA") "V" [spread Nil]
#guard settledAt (.resolve "RTA") "G" [spread L]
#guard settledAt (.resolve "RTA") "G" [.num 3]
#guard settledAt (.resolve "RTA") "G" [spread (.resolve "Zero")]
-- A name selected through `open`.
#guard settledAt (.resolve "OBox") "V" []
#guard settledAt (.resolve "OBox") "V" [spread Nil]
#guard settledAt (.resolve "OBox") "G" [spread L]
#guard settledAt (.resolve "OBox") "G" [.num 2]
-- The established classes stay instances of the general statement.
#guard settledAt (.resolve "Box") "V" []
#guard settledAt (dot (.resolve "Lib") "Sub" none) "K" []
#guard settledAt (.algorithmExpr boxBlock) "V" [spread Nil]
-- Declared-member / intrinsic shadowing: a DECLARED member `Algorithm` takes the member route, in
-- every bundle form; it is never the intrinsic.
#guard settledAt (.resolve "Box5") "Algorithm" [.num 0]
#guard settledAt (.resolve "Box5") "Algorithm" []
#guard settledAt (.resolve "Box5") "Algorithm" [spread Nil]
-- Negative controls: a structural miss selects no member; `settledIn` is not vacuously true.
#guard !settledAt (.resolve "Box") "Inc" []
#guard !settledAt (.num 5) "G" []

/-- CACHE-PUB-1: the empty-supply member call publishes the member's entry — on both sides, which
    the run equality of `settledIn` compares; here the publication itself is observed. -/
def publishes (target : Expr) (N : Ident) (args : List Expr) : Bool :=
  let src := dot target N (some args)
  match (supplyNeed src ctx []).runState EvalState.empty, NeedPlan.callShape? src ctx [] with
  | (.ok a, s), some shape =>
    let planned := ((ordinaryCall productionPlanRoute a shape .call).runState s).2.zeroArgPropertyCache
    let produced := ((reCountValueBoundary <$> evalCounted src ctx []).runState s).2.zeroArgPropertyCache
    let seven : CountedResult := (.atom 7, 1)
    s.zeroArgPropertyCache.isEmpty && reprStr planned == reprStr produced &&
      planned.any (fun entry => reprStr entry.2 == reprStr seven)
  | _, _ => false

#guard publishes AB "V" []
#guard publishes AB "V" [spread Nil]
#guard publishes (.resolve "RTA") "V" []
#guard publishes (.resolve "OBox") "V" []

/-! ## `member_bridge_param_stable`: a parameter receiver, every bundle -/

/-- A context binding the parameter `b` to a supplied cell holding the written `arg`. -/
def paramCtx (arg : Expr) : Option (EvalCtx × EvalState) :=
  match (supplyNeed arg ctx []).runState EvalState.empty with
  | (.ok cell, s) => some ({ ctx with needEnv := [("b", cell)] }, s)
  | _ => none

/-- The hypotheses and the conclusion of `member_bridge_param_stable` for `b.N(args)` with `b`
    bound to the written `arg`: the probe of the parameter is its CALLABLE projection and selects a
    declared member of the projected `owner`; `owner` is structure-normal; the parameter's captured
    activation, if any, is recorded; the cell's CALLABLE memo is published at the probe's exit
    (`projectNeedCallable_publishes`) — the fact `navStable_param` reads back; and the conclusion
    with the settledness premise of the general statement (`settledIn`). -/
def paramStableAt (arg : Expr) (N : Ident) (args : List Expr) : Bool :=
  match paramCtx arg with
  | none => false
  | some (c, s₀) =>
    (match (supplyNeed (dot (.param "b") N (some args)) c []).runState s₀ with
     | (.ok _, s) =>
       (match (resolveDotReceiver? (.param "b") c).runState s with
        | (.ok (some owner), s') =>
          (match selectDotEdge c (.param "b") N (some owner) with
           | .ok (.member o _) => reprStr o == reprStr owner
           | _ => false) &&
          structureNormal owner &&
          (match capturedId? "b" c with
           | none => true
           | some id => decide (id < s.lexicalActivations.size)) &&
          same ((projectParameterCallable "b" c).runState s) (.ok (some owner), s') &&
          (match parameterAddressIn s.lexicalActivations "b" c with
           | some address =>
             (match s'.needs[address]? with
              | some cell =>
                (match cell.callable with
                 | .projected (.ok (some g)) => reprStr g == reprStr owner
                 | _ => false)
              | none => false)
           | none => false)
        | _ => false)
     | _ => false) &&
    settledIn c s₀ (.param "b") N args

def Box : Expr := .resolve "Box"

-- `b = Box`: the first projection writes the cell's CALLABLE memo (outside `NavInert`).
#guard paramStableAt Box "V" []                         -- `b.V()`, publishing V's entry
#guard paramStableAt Box "V" [spread Nil]               -- `b.V(Nil*)`
#guard paramStableAt Box "G" [spread L]                 -- `b.G(L*)`: two formed slots, the arity failure
#guard paramStableAt Box "G" [spread (.resolve "Zero")] -- a failing spread
#guard paramStableAt Box "G" []                         -- `b.G()`: the arity failure
#guard paramStableAt Box "G" [.num 2]                   -- a plain first argument stays covered
-- The parameter bound to a transparent reference, a runtime-target alias, a supplied `.Algorithm`
-- link and the minting alias: the projected CALLABLE is the structure-normal target every time.
#guard paramStableAt AB "V" []
#guard paramStableAt (.resolve "RTA") "V" []
#guard paramStableAt (dot (.resolve "RC") "Algorithm" none) "V" [spread Nil]
#guard paramStableAt (.resolve "MTA") "V" []
#guard paramStableAt (.resolve "OBox") "V" []
-- Declared-member / intrinsic shadowing over a parameter: `b.Algorithm(…)` with `b = Box5`.
#guard paramStableAt (.resolve "Box5") "Algorithm" [.num 0]
#guard paramStableAt (.resolve "Box5") "Algorithm" []
-- Negative control: a parameter whose CALLABLE declares no such member.
#guard !paramStableAt Box "Inc" []

/-- A member path over a parameter (`b.Sub.K()` with `b = Lib`): `navStable_member` over
    `navStable_param` — the head's CALLABLE and the navigated member are structure-normal — and the
    general statement's premise and conclusion. -/
def paramPathStableAt (arg : Expr) (member N : Ident) (args : List Expr) : Bool :=
  match paramCtx arg with
  | none => false
  | some (c, s₀) =>
    let target := dot (.param "b") member none
    (match (supplyNeed (dot target N (some args)) c []).runState s₀ with
     | (.ok _, s) =>
       (match (projectParameterCallable "b" c).runState s with
        | (.ok (some head), _) =>
          structureNormal head &&
          (match Algorithm.lookupPropDefAny? head member with
           | some q => memberAccessible? c head q && structureNormal (childOfInContext head q.alg c)
           | none => false)
        | _ => false)
     | _ => false) &&
    settledIn c s₀ target N args

#guard paramPathStableAt (.resolve "Lib") "Sub" "K" []
#guard paramPathStableAt (.resolve "Lib") "Sub" "K" [spread Nil]
#guard paramPathStableAt (.resolve "Lib") "Sub" "H" [spread L]
#guard paramPathStableAt (.resolve "Lib") "Sub" "Fam" []

-- Whole programs: the member call over a parameter read from a CAPTURED activation, as a plan and
-- as the ordinary row; and every newly covered receiver through the public run, both routes.
#guard valueIs (run [callN "CapP" [Box], callN "CapO" [Box]]) (.sequenceValue [.atom 7, .atom 7])
#guard valueIs (run [dot AB "V" (some []), inId (dot AB "V" (some []))]) (.sequenceValue [.atom 7, .atom 7])
#guard valueIs (run [dot (.resolve "RTA") "V" (some []), inId (dot (.resolve "RTA") "V" (some []))])
  (.sequenceValue [.atom 7, .atom 7])
#guard valueIs (run [dot (.resolve "OBox") "V" (some []), inId (dot (.resolve "OBox") "V" (some []))])
  (.sequenceValue [.atom 7, .atom 7])
#guard valueIs (run [dot (.resolve "MTA") "V" (some []), inId (dot (.resolve "MTA") "V" (some []))])
  (.sequenceValue [.atom 7, .atom 7])

/-! ## The witness: the settledness premise is necessary -/

/-- **Correspondence witness: over a receiver whose navigation re-mints a runtime identity, the
    member bridge's exact run equality is FALSE for an empty or spread-first bundle.**
    `MTA = 5.MkFM.Algorithm` is a runtime-target alias whose `.Algorithm` receiver `5.MkFM` is a
    dot RESULT. Every structure chase through it re-decides the alias's route
    (`EvalBody.aliasStepIsRuntime`, `algorithmIntrinsicRoute`), and that decision resolves the
    receiver through the dot result's memberless carrier, which mints a fresh runtime declaration
    identity (`identifyRuntimeAlgorithm`). For `MTA.V(args)` with `args` forming an EMPTY supply:
    * the probe selects the declared member `V` and the plan's projection reaches it at the probe's
      exit (the receiver premise of `member_bridge_of_origin` holds);
    * navigating the receiver again answers the SAME owner, but changes the state — by exactly one
      minted identity: `member_bridge_settled`'s premise fails;
    * the plan's written origin navigates the receiver once more when it is read, production's
      bound origin does not: both runs complete with `(7, 1)`, and their final states differ by
      exactly that one minted identity (`EvalState.nextRuntimeDeclaration`), nothing else.
    So origin agreement — hence the member bridge as an exact run equality — fails on this reached
    state. The outcomes agree, and C# has no such counter (it mints object identities). With a plain
    first argument the origin is never read and `member_bridge` holds (`memberIn` below). -/
def memberOriginRemintsRuntimeIdentity (args : List Expr) : Bool :=
  let target : Expr := .resolve "MTA"
  let src := dot target "V" (some args)
  match (supplyNeed src ctx []).runState EvalState.empty, NeedPlan.callShape? src ctx [] with
  | (.ok a, s), some shape =>
    match (resolveDotReceiver? target ctx).runState s with
    | (.ok alg?, s') =>
      match selectDotEdge ctx target "V" alg? with
      | .ok (.member owner p) =>
        let nav := (projectedStructure target ctx).runState s'
        let planned := (ordinaryCall productionPlanRoute a shape .call).runState s
        let produced := (reCountValueBoundary <$> evalCounted src ctx []).runState s
        same ((projectNeedStructuralMember (.dotMember target "V" (.resolve "V") none) ctx).runState s)
          (.ok (some (childOfInContext owner p.alg ctx)), s') &&
        reprStr nav.1 == reprStr (Except.ok (some owner) : Except Error (Option Algorithm)) &&
        nav.2.nextRuntimeDeclaration == s'.nextRuntimeDeclaration + 1 &&
        reprStr { nav.2 with nextRuntimeDeclaration := s'.nextRuntimeDeclaration } == reprStr s' &&
        (match planned.1, produced.1 with
         | .ok (.atom 7, 1), .ok (.atom 7, 1) => true
         | _, _ => false) &&
        reprStr planned.2 != reprStr produced.2 &&
        planned.2.nextRuntimeDeclaration == produced.2.nextRuntimeDeclaration + 1 &&
        reprStr { planned.2 with nextRuntimeDeclaration := produced.2.nextRuntimeDeclaration } == reprStr produced.2
      | _ => false
    | _ => false
  | _, _ => false

#guard memberOriginRemintsRuntimeIdentity []
#guard memberOriginRemintsRuntimeIdentity [spread Nil]
-- Neither is an instance of the general statement: its premise fails there.
#guard !settledAt (.resolve "MTA") "V" []
#guard !settledAt (.resolve "MTA") "V" [spread Nil]
-- A plain first argument never reads the origin: `member_bridge` holds over the same receiver.
#guard memberIn ctx EvalState.empty (.resolve "MTA") "G" [.num 3]

/-- A counterexample to the proposed stability invariant, not to the member bridge.
    `MemoExt.withoutAliasCells` proves that this deletion is allowed by `MemoExt`. The first
    probe of `RTA` records its alias cell; after deleting the alias table while keeping the entire
    heap and activation array, navigation allocates again. Thus no `NavStable` instance at this
    probe exit can be derived using the current extension relation. -/
def aliasMemosNotProtected : Bool :=
  let target : Expr := .resolve "RTA"
  match (resolveDotReceiver? target ctx).runState EvalState.empty with
  | (.ok (some owner), t) =>
    let u := { t with aliasCells := [] }
    let nav := (projectedStructure target ctx).runState u
    !t.aliasCells.isEmpty && nav.2.needs.size > u.needs.size &&
      !same nav (.ok (some owner), u)
  | _ => false

#guard aliasMemosNotProtected

/-! ## The strengthened relation protects the record

`MemberStability.NavExt` is `MemoExt` with every recorded alias binding cell kept and the
runtime-declaration counter not moved back (`NavKept`, a whole-run relation:
`production_navKept`, `form_navKept`). The deletion above is NOT a navigation extension. -/

/-- At `RTA`'s probe exit the alias table holds a record under the alias's key, and the state
    without the table has lost it: the premise of `NavExt.not_withoutAliasCells` at that state. -/
def aliasRecordProtected : Bool :=
  let target : Expr := .resolve "RTA"
  match (resolveDotReceiver? target ctx).runState EvalState.empty with
  | (.ok (some _), t) =>
    match t.aliasCells with
    | (key, a) :: _ =>
      lookupAssoc key t.aliasCells == some a &&
        lookupAssoc key ({ t with aliasCells := [] } : EvalState).aliasCells == none
    | [] => false
  | _ => false

#guard aliasRecordProtected

/-- The theorem, at every state holding a record: the deletion is not a navigation extension. -/
example (s : EvalState) (key : String) (a : Nat) (h : lookupAssoc key s.aliasCells = some a) :
    ¬ KatLang.MemberStability.NavExt s { s with aliasCells := [] } :=
  KatLang.MemberStability.NavExt.not_withoutAliasCells h

/-- Over an ACTUAL later state — after the member's alias resolution and a supply formation that
    runs spread code — the record `RTA`'s probe wrote is still there and the runtime-declaration
    counter has not gone back: `production_navExt` / `form_navExt` on a concrete run. -/
def aliasRecordSurvivesRun : Bool :=
  let target : Expr := .resolve "RTA"
  match (resolveDotReceiver? target ctx).runState EvalState.empty with
  | (.ok (some _), t) =>
    let later := ((evalCounted (dot target "G" (some [spread L])) ctx []).runState t).2
    t.aliasCells.all (fun p => lookupAssoc p.1 later.aliasCells == some p.2) &&
      decide (t.nextRuntimeDeclaration ≤ later.nextRuntimeDeclaration) && !t.aliasCells.isEmpty
  | _ => false

#guard aliasRecordSurvivesRun

/-! ## Is the minted identity observable? (research evidence, not a theorem)

`memberOriginRemintsRuntimeIdentity`'s two runs end in states that differ by ONE minted runtime
identity (`EvalState.nextRuntimeDeclaration`). Whether a LATER production continuation can observe
that is decided here on a sample of continuations run from both final states: repeated member and
`.Algorithm` calls over the minting alias, another runtime-target alias, a captured reference, a
dot result that mints and RETAINS an identity, a failing member call, a failing bare read.

* **Every sampled continuation has the SAME outcome from both states** — values, counts and
  structured failures (`mintedIdentityOutcomesAgree`).
* **"Equal up to the counter" is NOT preserved by continuations** (`mintedIdentityIsRetained`): a
  continuation that mints and stores an identity (`5.MkFM.Algorithm(1)`) stores `.runtime n + 1`
  on one side and `.runtime n` on the other. A CANDIDATE relation for contextual preservation is
  equality up to an INJECTIVE RENAMING of runtime identities minted after the divergence (here:
  shifted by one), with the counter shifted alike. The samples do not prove that continuations
  preserve it.

Adopting that relation in place of exact equality for this class needs a proof obligation this
module does not discharge: a contextual two-run theorem — every evaluator body, run from two states
related by the renaming, ends in related states with related outcomes — and a boundary statement
for TEXT that renders an identity (cache and alias-cell keys are strings). The owner decision is
PENDING; exact run equality stays the only claim, and it stays false on this class. -/

/-- The two final states of the minting witness: the plan's and production's. -/
def mintedFinals (args : List Expr) : Option (EvalState × EvalState) :=
  let target : Expr := .resolve "MTA"
  let src := dot target "V" (some args)
  match (supplyNeed src ctx []).runState EvalState.empty, NeedPlan.callShape? src ctx [] with
  | (.ok a, s), some shape =>
    some (((ordinaryCall productionPlanRoute a shape .call).runState s).2,
      ((reCountValueBoundary <$> evalCounted src ctx []).runState s).2)
  | _, _ => none

def mintedContinuations : List Expr :=
  [dot (.resolve "MTA") "V" (some []),
   dot (.resolve "MTA") "G" (some [.num 3]),
   dot (.resolve "RTA") "V" (some []),
   inId (dot (.resolve "MTA") "V" (some [])),
   dot (.num 5) "MkFM" none,
   algoCall (dot (.num 5) "MkFM" none) [.num 1],
   callN "Capture" [dot (.resolve "MTA") "G" (some [.num 2])],
   dot (.resolve "MTA") "Nope" (some []),
   .resolve "MTA",
   .listLiteral [dot (.resolve "MTA") "V" (some []), algoCall (dot (.num 5) "MkFM" none) [.num 2]]]

/-- Every sampled continuation has one outcome from the two final states, and the counters stay
    exactly one apart. -/
def mintedIdentityOutcomesAgree (args : List Expr) : Bool :=
  match mintedFinals args with
  | some (planned, produced) =>
    planned.nextRuntimeDeclaration == produced.nextRuntimeDeclaration + 1 &&
    mintedContinuations.all fun c =>
      let rp := (evalCounted c ctx []).runState planned
      let ro := (evalCounted c ctx []).runState produced
      reprStr rp.1 == reprStr ro.1 && rp.2.nextRuntimeDeclaration == ro.2.nextRuntimeDeclaration + 1
  | none => false

#guard mintedIdentityOutcomesAgree []
#guard mintedIdentityOutcomesAgree [spread Nil]

/-- A continuation that mints and STORES an identity leaves states that differ by more than the
    counter: "equal up to the counter" is not a relation continuations preserve. -/
def mintedIdentityIsRetained : Bool :=
  match mintedFinals [] with
  | some (planned, produced) =>
    let c := algoCall (dot (.num 5) "MkFM" none) [.num 1]
    let rp := (evalCounted c ctx []).runState planned
    let ro := (evalCounted c ctx []).runState produced
    reprStr rp.1 == reprStr ro.1 &&
      reprStr { rp.2 with nextRuntimeDeclaration := ro.2.nextRuntimeDeclaration } != reprStr ro.2
  | none => false

#guard mintedIdentityIsRetained

end KatLang.MemberStabilityGuards
