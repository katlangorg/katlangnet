import KatLangArityLaws.RepeatedNameLaws

open KatLang KatLang.RepeatedNameLaws

/-!
# Executable guards for the repeated-name group laws (NEED-04 group-aware, ALIAS-UNIFY-1)

Concrete witnesses for `KatLangArityLaws/RepeatedNameLaws.lean`: structural value equality and
the emitted count, the optional-callable trap, the data anchor checking EVERY reference's own
VALUE, first-richest selection, the reference-only VALUE boundary of permutation, the
failure-category witness, and the production binder agreeing with the pure fold on real heaps —
reference cells included, whose VALUE the binder never demands. Three LOCAL negative controls
(`gfoldPairwise`, `gfoldLastRichest`, `gfoldKeepFirst`) are the mutations the laws exclude; each
guard below that names one shows the observable it would change. Executable checks, not theorems.
-/

namespace KatLang.RepeatedNameGuards

/-! ## Value equality is structural and counts the emitted count -/

#guard (Result.listValue [.atom 1] == Result.listValue [.atom 1])
#guard !(Result.listValue [.atom 1] == Result.sequenceValue [.atom 1])
#guard !(Result.listValue [] == Result.sequenceValue [])
#guard !(Result.callRef 3 == Result.argView 3)
#guard (Result.sequenceValue [.listValue [.str "a"], .bool true] ==
  Result.sequenceValue [.listValue [.str "a"], .bool true])
#guard !(Result.sequenceValue [.atom 1, .atom 2] == Result.sequenceValue [.atom 2, .atom 1])
-- Equal displayed value, different emitted count: unequal contributions.
#guard !(((Result.atom 1, 1) : CountedResult) == (Result.atom 1, 2))

/-! ## Contributions -/

def mapA : Algorithm := .builtin .mapBuiltin
def filterA : Algorithm := .builtin .filterBuiltin
def one : CountedResult := (.atom 1, 1)
def two : CountedResult := (.atom 2, 1)
def c (a : Nat) (cal : Option Algorithm) (v : CountedResult := one) : Contribution := ⟨a, v, cal⟩

def run (cs : List Contribution) : Except Conflict GState := gfold {} cs

def isCallableConflict : Except Conflict GState → Bool
  | .error .callable => true
  | _ => false

def isValueConflict : Except Conflict GState → Bool
  | .error .value => true
  | _ => false

def isOk : Except Conflict GState → Bool
  | .ok _ => true
  | .error _ => false

/-- The representative's address. -/
def repAt : Except Conflict GState → Option Nat
  | .ok g => g.rep.map Contribution.address
  | .error _ => none

/-- The representative's counted VALUE. -/
def repValue : Except Conflict GState → Option CountedResult
  | .ok g => g.rep.map Contribution.value
  | .error _ => none

/-! ## The optional-callable trap -/

-- A value-only contribution between two different identities cannot hide their conflict, in any
-- position: identities are compared with the group's FIRST identity, whatever the anchor.
#guard isCallableConflict (run [c 0 (some mapA), c 1 none, c 2 (some filterA)])
#guard isCallableConflict (run [c 1 none, c 0 (some mapA), c 2 (some filterA)])
#guard isCallableConflict (run [c 0 (some mapA), c 2 (some filterA), c 1 none])

/-- NEGATIVE CONTROL: a fold that keeps the FIRST contribution as the representative and never
    records an identity a value-only contribution did not bring. -/
def gfoldKeepFirst (g : GState) : List Contribution → Except Conflict GState
  | [] => .ok g
  | x :: xs =>
    match gstep g x with
    | .error e => .error e
    | .ok next => gfoldKeepFirst { next with rep := g.rep <|> some x } xs

-- …it drops the CALLABLE channel of a compatible mixed group: the representative is the
-- value-only cell instead of the reference.
#guard repAt (gfoldKeepFirst {} [c 1 none, c 0 (some mapA)]) == some 1
#guard repAt (run [c 1 none, c 0 (some mapA)]) == some 0

/-! ## A data anchor checks EVERY reference's own VALUE (§5 R6) -/

/-- NEGATIVE CONTROL: the PAIRWISE SHORTCUT — the first value-only contribution compares its
    VALUE with the representative only, not with every pending reference. -/
def gstepPairwise (g : GState) (x : Contribution) : Except Conflict GState :=
  match x.callable, g.anchor with
  | none, none =>
    if (g.rep.map (fun r => r.value == x.value)).getD true then .ok (g.withAnchor x) else .error .value
  | _, _ => gstep g x

def gfoldPairwise (g : GState) : List Contribution → Except Conflict GState
  | [] => .ok g
  | x :: xs =>
    match gstepPairwise g x with
    | .error e => .error e
    | .ok next => gfoldPairwise next xs

-- Two references of ONE identity with DIFFERENT completed VALUEs (1 and 2) and a value-only 1:
-- the group-aware fold refuses in either order of the references, the shortcut accepts one.
#guard isValueConflict (run [c 0 (some mapA) one, c 1 (some mapA) two, c 3 none one])
#guard isValueConflict (run [c 1 (some mapA) two, c 0 (some mapA) one, c 3 none one])
#guard isOk (gfoldPairwise {} [c 0 (some mapA) one, c 1 (some mapA) two, c 3 none one])
-- A reference AFTER the anchor is checked at once.
#guard isValueConflict (run [c 3 none one, c 1 (some mapA) two])

/-! ## First among the richest -/

/-- NEGATIVE CONTROL: a fold that keeps the LAST richest contribution. -/
def gfoldLastRichest (g : GState) : List Contribution → Except Conflict GState
  | [] => .ok g
  | x :: xs =>
    match gstep g x with
    | .error e => .error e
    | .ok next => gfoldLastRichest (if x.callable.isSome then { next with rep := some x } else next) xs

#guard repAt (run [c 0 none, c 1 (some mapA), c 2 (some mapA)]) == some 1
#guard repAt (gfoldLastRichest {} [c 0 none, c 1 (some mapA), c 2 (some mapA)]) == some 2
-- No callable anywhere: the first contribution.
#guard repAt (run [c 3 none, c 1 none, c 2 none]) == some 3

/-! ## Permutation of one name's contributions -/

-- The representative's ADDRESS follows the written order.
#guard repAt (run [c 0 none, c 1 none]) == some 0
#guard repAt (run [c 1 none, c 0 none]) == some 1
-- A MIXED group keeps the counted VALUE in every order (`gfold_perm_preserves_value_mixed`).
#guard match run [c 0 none, c 1 (some mapA), c 2 none], run [c 2 none, c 0 none, c 1 (some mapA)] with
  | .ok g, .ok g' => repAt (.ok g) == some 1 && repAt (.ok g') == some 1 &&
      repValue (.ok g) == repValue (.ok g')
  | _, _ => false
-- A REFERENCE-ONLY group need not: one identity, completed VALUEs 1 and 2 — both orders succeed,
-- binding representatives of different VALUEs (the `Coherent` premise is necessary).
#guard isOk (run [c 0 (some mapA) one, c 1 (some mapA) two])
#guard isOk (run [c 1 (some mapA) two, c 0 (some mapA) one])
#guard repValue (run [c 0 (some mapA) one, c 1 (some mapA) two]) == some one
#guard repValue (run [c 1 (some mapA) two, c 0 (some mapA) one]) == some two
-- Satisfiability is permutation invariant, incompatible combinations included.
#guard isValueConflict (run [c 0 none, c 1 none (.atom 1, 2)])
#guard isValueConflict (run [c 1 none (.atom 1, 2), c 0 none])

-- FAILURE CATEGORIES ARE NOT: the same contributions reach a different first refusal under
-- permutation (cf. `CoreTests.ModelC.mixedRepeatedConflicts`).
#guard isCallableConflict (run [c 0 (some mapA), c 1 (some filterA), c 2 none two])
#guard isValueConflict (run [c 2 none two, c 0 (some mapA), c 1 (some filterA)])

/-! ## The production binder computes the fold (real heaps) -/

def heap (vs : List CountedResult) : EvalState :=
  { needs := (vs.map fun v => ({ suspension := .ready v } : NeedCell)).toArray }

def channels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩

/-- The stable observation of a Ready heap: its counted values, no callable identity. -/
def obsOf (vs : List CountedResult) (a : Nat) : CountedResult × Option Algorithm :=
  ((vs[a]?).getD (.atom 0, 0), none)

def flat (names : List Ident) : List NeedPattern := names.map (fun n => NeedPattern.bind n)

def agrees (names : List Ident) (vs : List CountedResult) : Bool :=
  let cells := List.range vs.length
  let production := ((bindNeedPatterns channels (flat names) cells).runState (heap vs)).1
  let pure := (flatBind (obsOf vs) (needRepeatedNames (flat names)) false {} (names.zip cells)).map
    (Option.map NeedBindState.bound)
  match production, pure with
  | .ok (some e1), .ok (some e2) => e1 == e2
  | .ok none, .ok none => true
  | .error e1, .error e2 => reprStr e1 == reprStr e2
  | _, _ => false

#guard agrees ["x", "y", "x"] [one, two, one]
#guard agrees ["x", "y", "x"] [one, two, (.atom 1, 2)]
#guard agrees ["x", "x", "x"] [one, one, one]
#guard agrees ["x", "y", "y", "x"] [one, two, two, (.atom 3, 1)]
-- …and the production binding of a compatible repeated name keeps its FIRST cell.
#guard match ((bindNeedPatterns channels (flat ["x", "y", "x"]) [0, 1, 2]).runState
    (heap [one, two, one])).1 with
  | .ok (some env) => lookupAssoc "x" env == some 0 && lookupAssoc "y" env == some 1
  | _ => false

/-- A supplied written reference to a builtin (resolved under the prelude, as a run root is), and
    a failing computed expression. -/
def preludeCtx : EvalCtx := { callStack := [preludeAlg] }
def refCell (name : String) : NeedCell := { suspension := .expression (.resolve name) preludeCtx [] }
def failingCell : NeedCell := { suspension := .expression (.binary .div (.num 1) (.num 0)) EvalCtx.empty [] }
def cellHeap (cells : List NeedCell) : EvalState := { needs := cells.toArray }
def suspendedAt (s : EvalState) (address : Nat) : Bool :=
  match s.needs[address]?.map (·.state) with
  | some NeedState.suspended => true
  | _ => false

-- REFERENCE-GROUP INERTNESS on a real heap (§6 statement 5): two supplied references to the same
-- builtin bind by identity alone — neither cell's VALUE is demanded, both stay suspended.
#guard match (bindNeedPatterns channels (flat ["x", "x"]) [0, 1]).runState (cellHeap [refCell "map", refCell "map"]) with
  | (.ok (some env), s) => lookupAssoc "x" env == some 0 && suspendedAt s 0 && suspendedAt s 1
  | _ => false
-- Different builtin references conflict by identity, before any VALUE demand.
#guard match (bindNeedPatterns channels (flat ["x", "x"]) [0, 1]).runState (cellHeap [refCell "map", refCell "filter"]) with
  | (.error (.typeMismatch _), s) => suspendedAt s 0 && suspendedAt s 1
  | _ => false
-- A failing computed expression is value-only: its own VALUE is demanded and its failure is final.
#guard match (bindNeedPatterns channels (flat ["x", "x"]) [0, 1]).runState (cellHeap [failingCell, failingCell]) with
  | (.error .divByZero, _) => true
  | _ => false

end KatLang.RepeatedNameGuards
