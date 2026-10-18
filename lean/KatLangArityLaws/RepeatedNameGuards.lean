import KatLangArityLaws.RepeatedNameLaws

open KatLang KatLang.RepeatedNameLaws

/-!
# Executable guards for the repeated-name laws (R4 / Q-28, S5)

Concrete witnesses for `KatLangArityLaws/RepeatedNameLaws.lean`: structural value equality and
the emitted count, the optional-callable trap, first-richest selection, permutation of one
name's contributions, the failure-category witness, and the production binder agreeing with the
pure fold on real Ready heaps. Two LOCAL negative controls (`retainKeepFirst`,
`retainLastRichest`) are the mutations the laws exclude; each guard below that names one shows
the observable it would change. Executable checks, not theorems.
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
def c (a : Nat) (cal : Option Algorithm) (v : CountedResult := one) : Contribution := ⟨a, v, cal⟩

def isCallableConflict : Except Conflict Contribution → Bool
  | .error .callable => true
  | _ => false

def isValueConflict : Except Conflict Contribution → Bool
  | .error .value => true
  | _ => false

def retainedAt : Except Conflict Contribution → Option Nat
  | .ok r => some r.address
  | .error _ => none

/-! ## The optional-callable trap -/

-- A value-only contribution between two different identities cannot hide their conflict,
-- in either position.
#guard isCallableConflict (retain (c 0 (some mapA)) [c 1 none, c 2 (some filterA)])
#guard isCallableConflict (retain (c 1 none) [c 0 (some mapA), c 2 (some filterA)])
#guard isCallableConflict (retain (c 0 (some mapA)) [c 2 (some filterA), c 1 none])

/-- NEGATIVE CONTROL: a fold that forgets the richer contribution (always keeps the first). -/
def retainKeepFirst (rep : Contribution) : List Contribution → Except Conflict Contribution
  | [] => .ok rep
  | x :: xs =>
    match retainStep rep x with
    | .error e => .error e
    | .ok _ => retainKeepFirst rep xs

-- The mutant accepts the conflicting combination the binder refuses.
#guard !isCallableConflict (retainKeepFirst (c 1 none) [c 0 (some mapA), c 2 (some filterA)])
-- …and drops the CALLABLE channel of a compatible one.
#guard retainedAt (retainKeepFirst (c 1 none) [c 0 (some mapA)]) == some 1
#guard retainedAt (retain (c 1 none) [c 0 (some mapA)]) == some 0

/-! ## First among the richest -/

/-- NEGATIVE CONTROL: a fold that keeps the LAST richest contribution. -/
def retainLastRichest (rep : Contribution) : List Contribution → Except Conflict Contribution
  | [] => .ok rep
  | x :: xs =>
    match retainStep rep x with
    | .error e => .error e
    | .ok next => retainLastRichest (if x.callable.isSome then x else next) xs

#guard retainedAt (retain (c 0 none) [c 1 (some mapA), c 2 (some mapA)]) == some 1
#guard retainedAt (retainLastRichest (c 0 none) [c 1 (some mapA), c 2 (some mapA)]) == some 2
-- No callable anywhere: the first contribution.
#guard retainedAt (retain (c 3 none) [c 1 none, c 2 none]) == some 3

/-! ## Permutation of one name's contributions -/

-- The retained ADDRESS follows the written order; the observation does not.
#guard retainedAt (retain (c 0 none) [c 1 none]) == some 0
#guard retainedAt (retain (c 1 none) [c 0 none]) == some 1
#guard match retain (c 0 none) [c 1 (some mapA), c 2 none],
             retain (c 2 none) [c 0 none, c 1 (some mapA)] with
  | .ok r, .ok r' => r.address == 1 && r'.address == 1 && r.value == r'.value
  | _, _ => false
-- Satisfiability is permutation invariant, incompatible combinations included.
#guard isValueConflict (retain (c 0 none) [c 1 none (.atom 1, 2)])
#guard isValueConflict (retain (c 1 none (.atom 1, 2)) [c 0 none])

-- FAILURE CATEGORIES ARE NOT: the same contributions, every VALUE equal or not, reach a
-- different first refusal under permutation (cf. `CoreTests.ModelC.mixedRepeatedConflicts`).
#guard isCallableConflict (retain (c 0 (some mapA)) [c 1 (some filterA), c 2 none (.atom 2, 1)])
#guard isValueConflict (retain (c 2 none (.atom 2, 1)) [c 0 (some mapA), c 1 (some filterA)])

/-! ## The production binder computes the fold (real Ready heaps) -/

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
  let pure := flatBind (obsOf vs) (needRepeatedNames (flat names)) false [] (names.zip cells)
  match production, pure with
  | .ok (some e1), .ok (some e2) => e1 == e2
  | .ok none, .ok none => true
  | .error e1, .error e2 => reprStr e1 == reprStr e2
  | _, _ => false

#guard agrees ["x", "y", "x"] [one, (.atom 2, 1), one]
#guard agrees ["x", "y", "x"] [one, (.atom 2, 1), (.atom 1, 2)]
#guard agrees ["x", "x", "x"] [one, one, one]
#guard agrees ["x", "y", "y", "x"] [one, (.atom 2, 1), (.atom 2, 1), (.atom 3, 1)]
-- …and the production binding of a compatible repeated name keeps its FIRST cell.
#guard match ((bindNeedPatterns channels (flat ["x", "y", "x"]) [0, 1, 2]).runState
    (heap [one, (.atom 2, 1), one])).1 with
  | .ok (some env) => lookupAssoc "x" env == some 0 && lookupAssoc "y" env == some 1
  | _ => false

end KatLang.RepeatedNameGuards
