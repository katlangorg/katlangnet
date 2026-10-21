import KatLangArityLaws.NestedRepeatedNames

open KatLang KatLang.RepeatedNameLaws KatLang.NestedRepeatedNames KatLang.CallableIdentityDomain

/-!
# Executable guards for nested and mixed repeated names (R4 / Q-66, S6a)

Concrete witnesses for `KatLangArityLaws/NestedRepeatedNames.lean` and
`KatLangArityLaws/CallableIdentityDomain.lean`. Every binder run below is the PRODUCTION binder
`bindNeedPatterns` at the evaluator's own channels `bindingChannels` (the total shells over
`demandNeedRecursive` / `projectNeedWrittenAt`) on a hand-built heap — clearly labeled Lean
constructions: Ready cells, completed cells with a published CALLABLE outcome, and one completed
supplied CALL (an invocation plan, for META). Nothing here evaluates a written expression: every
demanded cell is in the stable domain, which is exactly what the theorems cover.

The matrix: a repeated name at the top level and nested, in sibling structures, through
sequence / list / unpack patterns; literals, fixed names, a collector and META beside it; equal
values with different counts; a value-only contribution between conflicting identities and its
permutations; fresh-child provenance and preserved cells; published `some`/`none`, a fresh Ready
projection and a repeated observation after publication; ordinary versus family outcomes and the
retained state at the stop; the walk agreeing with the production run; mixed identity profiles.
Executable checks, not theorems. End-to-end KatLang programs over nested repeated names stay in
`CoreTests/RepeatedNameConstraints.lean` (§§ 6–7) and the C# `RepeatedNameConstraintTests`;
Decimal128 representatives in `NumericRepresentativeSelectionTests`.
-/

namespace KatLang.NestedRepeatedNameGuards

/-! ## Heaps -/

def mapA : Algorithm := .builtin .mapBuiltin
def filterA : Algorithm := .builtin .filterBuiltin
def n (i : Int) : CountedResult := (.atom i, 1)
def sq (is : List Int) : CountedResult := (.sequenceValue (is.map .atom), 1)
def li (is : List Int) : CountedResult := (.listValue (is.map .atom), 1)

/-- A suspended Ready cell (opened data or a callback item). -/
def ready (v : CountedResult) : NeedCell := { suspension := .ready v }

/-- A completed supplied cell whose CALLABLE projection was already published. -/
def done (v : CountedResult) (callable : Option Algorithm) : NeedCell :=
  { suspension := .expression (.resolve "Supplied") EvalCtx.empty [], state := .completed (.ok v),
    callable := .projected (.ok callable) }

/-- A completed supplied CALL `F()` (an invocation plan) with its absence of identity published. -/
def plan (v : CountedResult) : NeedCell :=
  { suspension := .expression (.call (.resolve "F") []) EvalCtx.empty [], state := .completed (.ok v),
    callable := .projected (.ok none) }

def heap (cells : List NeedCell) : EvalState := { needs := cells.toArray }

def run (ps : List NeedPattern) (cells : List NeedCell) (family : Bool := false) :
    Except Error (Option NeedEnv) × EvalState :=
  (bindNeedPatterns bindingChannels ps (List.range cells.length) family).runState (heap cells)

def bound (r : Except Error (Option NeedEnv) × EvalState) (x : Ident) : Option Nat :=
  match r.1 with
  | .ok (some env) => lookupAssoc x env
  | _ => none

def nonMatch (r : Except Error (Option NeedEnv) × EvalState) : Bool :=
  match r.1 with
  | .ok none => true
  | _ => false

def valueConflict (r : Except Error (Option NeedEnv) × EvalState) (name : Ident := "x") : Bool :=
  match r.1 with
  | .error (.withContext context .badArity) => context == repeatedParameterContext name
  | _ => false

def callableConflict (r : Except Error (Option NeedEnv) × EvalState) : Bool :=
  match r.1 with
  | .error (.typeMismatch message) => message == "Repeated bind equality requires the same callable identity"
  | _ => false

/-- The binder-level META refusal of the parameter `m` (META-DIAG-1): the canonical refusal inside
    the frame naming the parameter. -/
def metaRefused (r : Except Error (Option NeedEnv) × EvalState) : Bool :=
  match r.1 with
  | .error (.withContext context (.notAnAlgorithm message)) =>
      context == "while binding meta parameter 'm'" && message == "meta: not a supplied call computation"
  | _ => false

def size (r : Except Error (Option NeedEnv) × EvalState) : Nat := r.2.needs.size

def completed (r : Except Error (Option NeedEnv) × EvalState) (a : Nat) : Bool :=
  match r.2.needs[a]? with
  | some { state := .completed _, .. } => true
  | _ => false

def projectedNone (r : Except Error (Option NeedEnv) × EvalState) (a : Nat) : Bool :=
  match r.2.needs[a]? with
  | some { callable := .projected (.ok none), .. } => true
  | _ => false

def unprojected (r : Except Error (Option NeedEnv) × EvalState) (a : Nat) : Bool :=
  match r.2.needs[a]? with
  | some { callable := .unprojected, .. } => true
  | _ => false

/-! ## The walk agrees with the production run -/

/-- The observation model of a heap: stable cells only (completed or Ready VALUE, published or
    Ready-unprojected CALLABLE). -/
def viewOf (s : EvalState) (a : Nat) : Option Obs :=
  match s.needs[a]? with
  | some c =>
    let v? : Option CountedResult := match c.state, c.suspension with
      | .completed (.ok v), _ => some v
      | .suspended, .ready v => some v
      | _, _ => none
    let o? : Option (Option Algorithm) := match c.callable, c.suspension with
      | .projected (.ok o), _ => some o
      | .unprojected, .ready _ => some none
      | _, _ => none
    match v?, o? with
    | some v, some o => some (v, o)
    | _, _ => none
  | none => none

def modelOf (s : EvalState) : Model :=
  ⟨viewOf s, fun a => (NeedPlan.shapeAt? s.needs a).isSome, s.needs.size⟩

/-- The production run and the walk return the same outcome and the same heap size. -/
def agrees (ps : List NeedPattern) (cells : List NeedCell) (family : Bool := false) : Bool :=
  let r := run ps cells family
  match walkHead (modelOf (heap cells)) ps (List.range cells.length) family with
  | none => false
  | some w =>
    w.2.1.size == r.2.needs.size &&
    match r.1, w.1 with
    | .ok (some e1), .ok (some e2) => e1 == e2
    | .ok none, .ok none => true
    | .error e1, .error e2 => reprStr e1 == reprStr e2
    | _, _ => false

/-- The occurrences the walk logged for `x`. -/
def logged (ps : List NeedPattern) (cells : List NeedCell) (x : Ident) : List Nat :=
  match walkHead (modelOf (heap cells)) ps (List.range cells.length) false with
  | some w => occ x w.2.2
  | none => []

def x := NeedPattern.bind "x"
def y := NeedPattern.bind "y"
def z := NeedPattern.bind "z"

/-! ### Top-level and nested occurrences of one name -/

-- `F(x, (x, y))`: the nested `x` is the FRESH child 2 of cell 1; x keeps its first (top-level) cell.
#guard agrees [x, .sequence [x, y]] [ready (n 1), ready (sq [1, 2])]
#guard bound (run [x, .sequence [x, y]] [ready (n 1), ready (sq [1, 2])]) "x" == some 0
#guard bound (run [x, .sequence [x, y]] [ready (n 1), ready (sq [1, 2])]) "y" == some 3
#guard logged [x, .sequence [x, y]] [ready (n 1), ready (sq [1, 2])] "x" == [0, 2]
-- Unequal nested value: the ordinary repeated-parameter `badArity`.
#guard valueConflict (run [x, .sequence [x, y]] [ready (n 1), ready (sq [2, 2])])
#guard agrees [x, .sequence [x, y]] [ready (n 1), ready (sq [2, 2])]

-- Separate nested siblings `((x, y), [x])`: both contributions are fresh children.
#guard agrees [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])]
#guard bound (run [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])]) "x" == some 2
#guard logged [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])] "x" == [2, 4]
-- An equal number inside a sequence versus inside a list: compared by counted value only.
#guard agrees [.sequence [x, y], .list [x]] [ready (sq [1, 7]), ready (li [1])]
#guard bound (run [.sequence [x, y], .list [x]] [ready (sq [1, 7]), ready (li [1])]) "x" == some 2

-- Internal Lean `.unpack [x, x]` (deconstruction), with equal/unequal items and a deeper occurrence.
#guard agrees [.unpack [x, x]] [ready (sq [4, 4])]
#guard bound (run [.unpack [x, x]] [ready (sq [4, 4])]) "x" == some 1
#guard valueConflict (run [.unpack [x, x]] [ready (sq [4, 5])])
-- A supply the head does not accept (three cells for two patterns): the same arity error.
#guard agrees [x, .unpack [y, .list [x]]] [ready (n 3), ready (sq [0]), ready (n 0)]
#guard agrees [x, .unpack [y, .list [x]]] [ready (n 3), ready (.sequenceValue [.atom 0, .listValue [.atom 3]], 1)]
#guard bound (run [x, .unpack [y, .list [x]]] [ready (n 3), ready (.sequenceValue [.atom 0, .listValue [.atom 3]], 1)]) "x"
  == some 0

/-! ### Literals, fixed names, collectors and META beside a repeated name -/

def seven := NeedPattern.literal (.litInt 7)

-- A literal mismatch BEFORE the repeated name: non-match, and x's cells are never demanded.
#guard nonMatch (run [seven, x, x] [ready (n 8), ready (n 1), ready (n 1)])
#guard !completed (run [seven, x, x] [ready (n 8), ready (n 1), ready (n 1)]) 1
#guard agrees [seven, x, x] [ready (n 8), ready (n 1), ready (n 1)]
-- …and AFTER a compatible repeated name: still a non-match, x's cells already completed.
#guard nonMatch (run [x, x, seven] [ready (n 1), ready (n 1), ready (n 8)])
#guard completed (run [x, x, seven] [ready (n 1), ready (n 1), ready (n 8)]) 1
#guard agrees [x, x, seven] [ready (n 1), ready (n 1), ready (n 8)]
-- Compatible names and a matching literal bind.
#guard bound (run [x, seven, x] [ready (n 1), ready (n 7), ready (n 1)]) "x" == some 0

-- A collector between the occurrences: its cell is allocated (address 4), never demanded.
#guard agrees [x, .bind "rest" true, x] [ready (n 1), ready (n 9), ready (n 9), ready (n 1)]
#guard bound (run [x, .bind "rest" true, x] [ready (n 1), ready (n 9), ready (n 9), ready (n 1)]) "rest" == some 4
#guard bound (run [x, .bind "rest" true, x] [ready (n 1), ready (n 9), ready (n 9), ready (n 1)]) "x" == some 0
#guard !completed (run [x, .bind "rest" true, x] [ready (n 1), ready (n 9), ready (n 9), ready (n 1)]) 1
-- A nested collector shifts later addresses without forcing its slice.
#guard agrees [.sequence [x, .bind "rest" true, x], x] [ready (sq [1, 9, 1]), ready (n 1)]
#guard bound (run [.sequence [x, .bind "rest" true, x], x] [ready (sq [1, 9, 1]), ready (n 1)]) "rest" == some 5
#guard bound (run [.sequence [x, .bind "rest" true, x], x] [ready (sq [1, 9, 1]), ready (n 1)]) "x" == some 2
#guard !completed (run [.sequence [x, .bind "rest" true, x], x] [ready (sq [1, 9, 1]), ready (n 1)]) 3

-- META before a repeated name: a supplied call is reified to a fresh adapter (address 3)…
#guard bound (run [.metaRef "m", x, x] [plan (n 5), ready (n 1), ready (n 1)]) "m" == some 3
#guard agrees [.metaRef "m", x, x] [plan (n 5), ready (n 1), ready (n 1)]
-- …while a non-call cell is refused before the repeated name is inspected.
#guard metaRefused (run [.metaRef "m", x, x] [ready (n 5), ready (n 1), ready (n 2)])
#guard !completed (run [.metaRef "m", x, x] [ready (n 5), ready (n 1), ready (n 2)]) 1
#guard agrees [.metaRef "m", x, x] [ready (n 5), ready (n 1), ready (n 2)]
-- A later refusal retains completed repeated observations; an earlier conflict wins over it.
#guard metaRefused (run [x, x, .metaRef "m"] [ready (n 1), ready (n 1), ready (n 5)])
#guard completed (run [x, x, .metaRef "m"] [ready (n 1), ready (n 1), ready (n 5)]) 1
#guard agrees [x, x, .metaRef "m"] [ready (n 1), ready (n 1), ready (n 5)]
#guard valueConflict (run [x, x, .metaRef "m"] [ready (n 1), ready (n 2), ready (n 5)])
-- The adapter is allocated before structural children, whose addresses reflect that prefix.
#guard agrees [.metaRef "m", .sequence [x, y], x] [plan (n 5), ready (sq [1, 2]), ready (n 1)]
#guard bound (run [.metaRef "m", .sequence [x, y], x] [plan (n 5), ready (sq [1, 2]), ready (n 1)]) "m" == some 3
#guard bound (run [.metaRef "m", .sequence [x, y], x] [plan (n 5), ready (sq [1, 2]), ready (n 1)]) "x" == some 4

/-! ### Counted values, callable identities, first richest -/

-- A nested child's count is its OWN `valueCount`, not its parent's: `[1]` with count 2 still opens to
-- a child `(1, 1)` equal to the top-level `x`...
#guard bound (run [x, .list [x]] [ready (n 1), ready (.listValue [.atom 1], 2)]) "x" == some 0
-- ...while equal result values with different emitted counts are unequal contributions.
#guard valueConflict (run [x, x] [ready (n 1), ready (.atom 1, 2)])
#guard agrees [x, x] [ready (n 1), ready (.atom 1, 2)]

-- A value-only nested contribution between two conflicting identities cannot hide the conflict.
#guard callableConflict (run [x, .list [x], x] [done (n 1) (some mapA), ready (li [1]), done (n 1) (some filterA)])
#guard agrees [x, .list [x], x] [done (n 1) (some mapA), ready (li [1]), done (n 1) (some filterA)]
-- Permutations: the FIRST richest contribution is retained, whatever comes first.
#guard bound (run [.list [x], x, x] [ready (li [1]), done (n 1) (some mapA), done (n 1) (some mapA)]) "x" == some 1
#guard bound (run [x, .list [x], x] [done (n 1) (some mapA), ready (li [1]), done (n 1) (some mapA)]) "x" == some 0
#guard bound (run [x, x, .list [x]] [done (n 1) none, done (n 1) (some mapA), ready (li [1])]) "x" == some 1
-- A name contributed only by fresh children retains no identity (they are Ready data).
#guard bound (run [.list [x], .list [x]] [ready (li [1]), ready (li [1])]) "x" == some 2

/-! ### Provenance, publication and repeated observation -/

-- Fresh children take the next addresses in item order; supplied cells keep their contents.
#guard size (run [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])]) == 5
#guard (run [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])]).2.needs[2]?.map
  (fun c => reprStr c.suspension) == some (reprStr (NeedSuspension.ready (n 1)))
-- The first demand of a Ready child completes it; a second occurrence projects both CALLABLEs:
-- the fresh Ready projections publish the absence of identity.
#guard completed (run [.list [x], .list [x]] [ready (li [1]), ready (li [1])]) 2
#guard projectedNone (run [.list [x], .list [x]] [ready (li [1]), ready (li [1])]) 2
#guard projectedNone (run [.list [x], .list [x]] [ready (li [1]), ready (li [1])]) 3
-- A first-only occurrence projects nothing (the plain child `y` stays unprojected).
#guard unprojected (run [.sequence [x, y], .list [x]] [ready (sq [1, 2]), ready (li [1])]) 3
-- Published `some` and `none` outcomes are reused unchanged.
#guard bound (run [x, x] [done (n 1) (some mapA), done (n 1) none]) "x" == some 0
#guard agrees [x, x] [done (n 1) (some mapA), done (n 1) none]
-- Repeated observation after publication: binding again over the published heap agrees.
#guard let r1 := run [x, x] [ready (n 1), ready (n 1)]
  let r2 := (bindNeedPatterns bindingChannels [x, x] [0, 1]).runState r1.2
  bound r1 "x" == some 0 && bound r2 "x" == some 0 && r2.2.needs.size == r1.2.needs.size

/-! ### Ordinary call versus family, and the retained state at the stop -/

-- The same conflict: an error for an ordinary call, a non-match for a family clause.
#guard valueConflict (run [x, .list [x], z] [ready (n 1), ready (li [2]), ready (n 0)])
#guard nonMatch (run [x, .list [x], z] [ready (n 1), ready (li [2]), ready (n 0)] true)
#guard agrees [x, .list [x], z] [ready (n 1), ready (li [2]), ready (n 0)] true
-- The stop keeps what it did: the opened child stays allocated and completed, later cells untouched.
#guard size (run [x, .list [x], .list [z]] [ready (n 1), ready (li [2]), ready (li [0])]) == 4
#guard completed (run [x, .list [x], .list [z]] [ready (n 1), ready (li [2]), ready (li [0])]) 3
#guard !completed (run [x, .list [x], .list [z]] [ready (n 1), ready (li [2]), ready (li [0])]) 2

/-! ### Whole-head success is not compatibility (cf. `compatible_is_not_success`) -/

#guard nonMatch (run [x, x, .sequence [y, z]] [ready (n 1), ready (n 1), ready (n 5)] true)
#guard logged [x, x, .sequence [y, z]] [ready (n 1), ready (n 1), ready (n 5)] "x" == [0, 1]
#guard agrees [x, x, .sequence [y, z]] [ready (n 1), ready (n 1), ready (n 5)] true

/-! ## Mixed identity profiles (`CallableIdentityDomain`) -/

/-- A nonempty initial identity domain: two published builtin identities. The identities
    conflict with each other; belonging to the transitivity domain does not imply compatibility. -/
def initialIdentityModel : Model :=
  ⟨fun a => if a = 0 then some (n 1, some mapA)
    else if a = 1 then some (n 1, some filterA) else none, fun _ => false, 2⟩

theorem initial_identity_domain : ModelNoCross initialIdentityModel := by
  apply model_no_cross_of_profiles initialIdentityModel none
  intro a ha
  obtain ⟨address, v, hv⟩ := ha
  simp only [initialIdentityModel] at hv
  split at hv
  · cases hv; rfl
  · split at hv
    · cases hv; rfl
    · cases hv

def lvl (parent : Option ScopeCtx) (id : Option PropertyIdentity) : ScopeCtx := level parent id

def identified : ScopeCtx := lvl none (some (.syntax 1))
def anonymous : ScopeCtx := lvl none none

/-- Two algorithms with the same declaration under the given parents. -/
def under (p : ScopeCtx) : Algorithm := .mk (some p) [] [] [] [] (some (.syntax 9))

-- Mixed presence at a compared level: the printed declarations differ, so the comparison fails
-- (executable evidence for the residual `ReprSeparatesPresence`; not a kernel fact).
#guard reprStr identified.declaration != reprStr anonymous.declaration
#guard reprStr (lvl (some identified) none).declaration != reprStr (lvl (some anonymous) none).declaration
#guard !sameRepeatedCallableIdentity (under identified) (under anonymous)
-- Anonymous at the top with differently identified parents: the S5 profiles differ, the new
-- domain admits them, and the fallback decides by the printed chain.
#guard idProfile (lvl (some identified) none) != idProfile (lvl (some anonymous) none)
#guard !sameRepeatedCallableIdentity (under (lvl (some identified) none)) (under (lvl (some anonymous) none))
#guard sameRepeatedCallableIdentity (under (lvl (some identified) none)) (under (lvl (some identified) none))

end KatLang.NestedRepeatedNameGuards
