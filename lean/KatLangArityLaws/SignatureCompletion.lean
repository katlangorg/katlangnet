import KatLang

open KatLang

/-!
# SC-1: the signature-completion reference kernel

THIS IS A FRONT-END REFERENCE MODEL, NOT THE LEAN EVALUATOR AND NOT THE C# COMPILER. `KatLang.lean` models no
signature construction (FORMAL-02: Lean sees elaborated programs). This module is a small total model of the finite
equation system the C# front end hands to `SignatureSelector` (`src/KatLang/SignatureSelection.cs`): a theorem here is
a theorem about THIS model. Its relation to C# is finite executable agreement on the bridge corpus
(`SignatureCompletionGuards.lean`, `tests/KatLang.Tests/SignatureCompletion/`), never a proof about the C# code.

What it reuses from the authoritative model, by name and not by copy: `ParameterPattern`, the zero-supply rule
`ParameterPattern.minimumSuppliedSlots` and the X-02 validator `ParameterPattern.signatureViolation?`.

## The boundary

| Native piece | Model | Note |
| --- | --- | --- |
| `SignatureAnalysis.Body` + `SignatureEquationReference` | `Equation`, `Reference` | INPUT: raw analysis output, not modeled |
| `Compose` closure of `SelectSignatures`, `LiftSignature`, `MergeOwnerSignature`, `MissingCapturePattern` | `composeFact`, `missing*` | The ONE composition law, concrete |
| `ParameterPattern.KeepFirstCollectingCapturePerLevel` | `recoverLevel` | X-02 recovery |
| `SignatureSelector.Lifted` | `liftedWith` | Guard, then zero-supply skip, then identity dedupe |
| `SignatureSelector.Evaluate` | `evalVector`, `evalComponent` | Layers of components instead of Tarjan's order |
| `SignatureSelector.Complete` | `completeLoop` | Brent's two snapshots, as native |
| `SignatureSelector.SameState` | `Fact` equality | Pattern tree and X-02 flag; origins are not in `Fact` |
| `Table`, `GroundednessOf`, `Rule` | `rowOf`, `groundednessOf`, `rule` | Over the WHOLE system (rule G6) |
| `Solve`'s local pass and joint regions | none | An optimization the bridge checks, not modeled |
| `SealCompletion` (origins), `CompletedStaticStructures`, the rewrite | none | Sealed AFTER stabilization; outside this model |
| `StaticQueryResourceBudget`, cancellation | `fuel`, `.exhausted` | A bound, not the C# ledger: see below |

`fuel` bounds the rounds of one component. It is not the C# ledger: the two run out at different points, and the
bridge compares no exhausted outcome. Origins (R1) are excluded on purpose: the state of a round holds no origin, and
sealing happens after a state settled (`SignatureFact`'s records are ignored by `SamePatterns`). `Fact` therefore has
no origin field, and `IsLifted` is recomputable from the composition.

Equation keys are `Nat`s standing for native equation indices; `Reference.identity` stands for the native
`SignatureEquationReference.Identity` object (one per endpoint).
-/

namespace KatLang.SignatureCompletion

deriving instance DecidableEq for CallableParameter

mutual
  /-- Structural equality of patterns: node kinds, capture names and kinds, grouping and order (`SamePatterns`). -/
  def decEqPattern : (a b : ParameterPattern) → Decidable (a = b)
    | .capture p, .capture q =>
        if h : p = q then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
    | .sequenceValue x, .sequenceValue y =>
        match decEqPatterns x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .listValue x, .listValue y =>
        match decEqPatterns x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .unpacking x, .unpacking y =>
        match decEqPatterns x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .capture _, .sequenceValue _ | .capture _, .listValue _ | .capture _, .unpacking _
    | .sequenceValue _, .capture _ | .sequenceValue _, .listValue _ | .sequenceValue _, .unpacking _
    | .listValue _, .capture _ | .listValue _, .sequenceValue _ | .listValue _, .unpacking _
    | .unpacking _, .capture _ | .unpacking _, .sequenceValue _ | .unpacking _, .listValue _ =>
        isFalse nofun

  def decEqPatterns : (a b : List ParameterPattern) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | x :: xs, y :: ys =>
        match decEqPattern x y, decEqPatterns xs ys with
        | isTrue h, isTrue t => isTrue (by rw [h, t])
        | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
        | _, isFalse t => isFalse (by intro e; cases e; exact t rfl)
end

instance : DecidableEq ParameterPattern := decEqPattern

abbrev Patterns := List ParameterPattern

/-- `CallableSignature.AcceptsZeroSuppliedArguments` (Q-03): the authoritative zero-supply rule. -/
def acceptsZero (patterns : Patterns) : Bool :=
  ParameterPattern.minimumSuppliedSlots patterns == 0

/-! ## The composition law -/

/-- C# `LiftedCapture`: lifting gives the caller an ORDINARY binding for a META capture. -/
def liftedCapture (parameter : CallableParameter) : CallableParameter :=
  if parameter.kind = .metaRef then { parameter with kind := .normal } else parameter

/-- The closing decision of C# `MissingGroupCapturePattern`: `original` is the group, `items` its items and `kept`
    their missing parts. Nothing new: no group. Nothing filtered: the group itself. A sequence left with one
    non-collecting item IS that item (the singleton rule); otherwise the group keeps its kind. -/
def closeGroup (original : ParameterPattern) (rebuild : Patterns → ParameterPattern) (isSequence : Bool)
    (items kept : Patterns) : Option ParameterPattern :=
  match kept with
  | [] => none
  | first :: rest =>
      if first :: rest = items then some original
      else if isSequence && ParameterPattern.isSingletonSequenceItems (first :: rest) then some first
      else some (rebuild (first :: rest))

mutual
  /-- C# `MissingCapturePattern`: the part of a pattern no earlier capture binds, threading the names kept so far
      (`existing`); a name an enclosing binding supplies (`forwardable`, Q-04) is never kept. -/
  def missingPattern (forwardable : List Ident) : ParameterPattern → List Ident → Option ParameterPattern × List Ident
    | .capture parameter, existing =>
        if forwardable.contains parameter.name || existing.contains parameter.name then (none, existing)
        else (some (.capture (liftedCapture parameter)), parameter.name :: existing)
    | .sequenceValue items, existing =>
        let (kept, existing') := missingItems forwardable items existing
        (closeGroup (.sequenceValue items) .sequenceValue true items kept, existing')
    | .listValue items, existing =>
        let (kept, existing') := missingItems forwardable items existing
        (closeGroup (.listValue items) .listValue false items kept, existing')
    | .unpacking items, existing =>
        let (kept, existing') := missingItems forwardable items existing
        (closeGroup (.unpacking items) .unpacking false items kept, existing')

  /-- C# `AppendMissingPatterns` over one list. -/
  def missingItems (forwardable : List Ident) : Patterns → List Ident → Patterns × List Ident
    | [], existing => ([], existing)
    | pattern :: rest, existing =>
        let (kept, existing') := missingPattern forwardable pattern existing
        let (others, existing'') := missingItems forwardable rest existing'
        (match kept with
          | some p => p :: others
          | none => others,
         existing'')
end

/-- C# `TryGetSingleCollectingForwarding`: an owner whose whole list is a lone top-level collector re-supplies a
    callee whose whole list is one group holding a lone collector. -/
def canForwardStream (own callee : Patterns) : Bool :=
  let isCollector : ParameterPattern → Bool
    | .capture parameter => parameter.kind == .collecting
    | _ => false
  match own, callee with
  | [caller], [.sequenceValue [inner]] => isCollector caller && isCollector inner
  | [caller], [.listValue [inner]] => isCollector caller && isCollector inner
  | [caller], [.unpacking [inner]] => isCollector caller && isCollector inner
  | _, _ => false

/-- The captures a dependency sequence adds to an owner, in order, first occurrence of each name winning. -/
def appended (forwardable : List Ident) : List Patterns → List Ident → Patterns
  | [], _ => []
  | dependency :: rest, existing =>
      let (kept, existing') := missingItems forwardable dependency existing
      kept ++ appended forwardable rest existing'

/-- The capture names of a list, left to right at every depth. -/
def namesOf (patterns : Patterns) : List Ident :=
  (ParameterPattern.capturesOfList patterns).map (·.name)

mutual
  /-- C# `KeepFirstCollectingCapturePerLevel`: the first collector of every level stays, a later one becomes fixed. -/
  def recoverLevel : Bool → Patterns → Patterns
    | _, [] => []
    | seen, .capture parameter :: rest =>
        if parameter.kind = .collecting then
          (if seen then .capture { parameter with kind := .normal } else .capture parameter) :: recoverLevel true rest
        else .capture parameter :: recoverLevel seen rest
    | seen, .sequenceValue items :: rest => .sequenceValue (recoverGroup items) :: recoverLevel seen rest
    | seen, .listValue items :: rest => .listValue (recoverGroup items) :: recoverLevel seen rest
    | seen, .unpacking items :: rest => .unpacking (recoverGroup items) :: recoverLevel seen rest

  def recoverGroup : Patterns → Patterns
    | [] => []
    | item :: rest => recoverLevel false (item :: rest)
end

/-- One equation's fact: exactly the state `SignatureSelector.SameState` compares. -/
structure Fact where
  patterns : Patterns
  violation : Option ParameterPattern.SignatureViolation
  deriving DecidableEq, Repr, Inhabited

/-- The fact a cycle member is read as under the closed gate: no parameter at all. -/
def closedFact : Fact := ⟨[], none⟩

/-- THE ONE COMPOSITION LAW (C#'s `Compose` over `LiftSignature`): own patterns, then what the lifted callees add;
    an X-02 violation of a LIFTED list is flagged and the recovered list is the fact (a list nothing was added to is
    the owner's own and is never judged here). -/
def composeFact (own : Patterns) (forwardable : List Ident) (lifted : List Patterns) : Fact :=
  let included := lifted.filter (fun callee => !canForwardStream own callee)
  match appended forwardable included (namesOf own) with
  | [] => ⟨own, none⟩
  | first :: rest =>
      let whole := own ++ first :: rest
      match ParameterPattern.signatureViolation? whole with
      | some violation => ⟨recoverLevel false whole, some violation⟩
      | none => ⟨whole, none⟩

/-! ## Equation systems -/

inductive Target where
  /-- An equation of this selection (`SignatureEquationReference.Target`). -/
  | member (key : Nat)
  /-- A signature that is FINAL here (`SignatureEquationReference.External`): a written list, a registry member, a
      clause family or an earlier operation's body. -/
  | external (patterns : Patterns)
  deriving DecidableEq, Repr, Inhabited

/-- One value-role read, in written order. `guard` is the `.Algorithm` link whose class decides that it is a read. -/
structure Reference where
  target : Target
  identity : Nat
  guard : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

structure Equation where
  own : Patterns := []
  forwardable : List Ident := []
  references : List Reference := []
  isLink : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A finite equation system: `keys` is declaration storage, `equation` the equations. No global universe of
    signatures is assumed anywhere. -/
structure System where
  keys : List Nat
  equation : Nat → Equation

/-- The system of a list of equations, keyed by position. -/
def System.ofList (equations : List Equation) : System where
  keys := List.range equations.length
  equation k := equations.getD k {}

/-- Every reference stays inside the system, and storage holds each key once. -/
structure System.WellFormed (sys : System) : Prop where
  nodup : sys.keys.Nodup
  targets : ∀ k ∈ sys.keys, ∀ r ∈ (sys.equation k).references,
    (∀ t, r.target = .member t → t ∈ sys.keys) ∧ (∀ g, r.guard = some g → g ∈ sys.keys)

/-- Whether a reference is a read under the classification `opened` (`Guard < 0 || isOpen(Guard)`). -/
def Reference.active (opened : Nat → Bool) (r : Reference) : Bool :=
  match r.guard with
  | none => true
  | some link => opened link

/-- The in-system reads of an equation under a classification (C#'s `Active`). -/
def activeTargets (eq : Equation) (opened : Nat → Bool) : List Nat :=
  eq.references.filterMap fun r =>
    match r.target with
    | .member k => if r.active opened then some k else none
    | .external _ => none

/-- The signature a reference target denotes. -/
def signatureOf (look : Nat → Patterns) : Target → Patterns
  | .member k => look k
  | .external patterns => patterns

/-- THE LIFTING RULE (`SignatureSelector.Lifted`): the callees the references lift, in written order, each identity
    once. The guard decides BEFORE deduplication, so an inactive first occurrence never hides an active later one. -/
def liftedFrom (opened : Nat → Bool) (look : Nat → Patterns) : List Reference → List Nat → List Patterns
  | [], _ => []
  | r :: rest, seen =>
      if r.active opened then
        let signature := signatureOf look r.target
        if acceptsZero signature then liftedFrom opened look rest seen
        else if seen.contains r.identity then liftedFrom opened look rest seen
        else signature :: liftedFrom opened look rest (r.identity :: seen)
      else liftedFrom opened look rest seen

/-- Composition of one equation over the signatures `look` gives its reads. -/
def composeWith (eq : Equation) (opened : Nat → Bool) (look : Nat → Patterns) : Fact :=
  composeFact eq.own eq.forwardable (liftedFrom opened look eq.references [])

/-! ## Reachability and components -/

/-- One round of reachability: the keys already reached and every key a reached one reads. -/
def grow (sys : System) (opened : Nat → Bool) (reached : List Nat) : List Nat :=
  sys.keys.filter fun j =>
    reached.contains j || reached.any fun i => (activeTargets (sys.equation i) opened).contains j

def growN (sys : System) (opened : Nat → Bool) : Nat → List Nat → List Nat
  | 0, reached => reached
  | .succ n, reached => growN sys opened n (grow sys opened reached)

/-- A tabulated function. It is DATA on purpose: the compiler eta-expands a definition whose result type is a function,
    so a table returned at type `Nat → α` would be rebuilt by every lookup. -/
structure Memo (α : Type) where
  get : Nat → α

instance {α} : CoeFun (Memo α) (fun _ => Nat → α) := ⟨Memo.get⟩

/-- A pure function of `keys` tabulated once, so an executable lookup never recomputes it. On `keys` it IS `f`
    (`tabulate_of_mem`); `default` elsewhere. -/
def tabulate {α} (keys : List Nat) (default : α) (f : Nat → α) : Memo α :=
  let table := keys.map fun k => (k, f k)
  ⟨fun k => (table.lookup k).getD default⟩

/-- The keys `a` reaches through zero or more reads. -/
def reachOf (sys : System) (opened : Nat → Bool) (a : Nat) : List Nat :=
  growN sys opened sys.keys.length (grow sys opened [a])

/-- Whether two keys lie in one strongly connected component of the active read graph, given the reach table. -/
def sameComponent (reach : Nat → List Nat) (a b : Nat) : Bool :=
  (reach a).contains b && (reach b).contains a

/-- The component of `a`, in storage order. -/
def componentOf (sys : System) (reach : Nat → List Nat) (a : Nat) : List Nat :=
  sys.keys.filter (sameComponent reach a)

/-! ## Simultaneous completion -/

/-- Outcome of the rounds of one component. -/
inductive RoundOutcome (σ : Type) where
  | settled (state : σ)
  | nonSettling
  | exhausted

/-- SIMULTANEOUS COMPLETION (`SignatureSelector.Complete`): each round recomposes every member from the PRECEDING
    round. Two equal successive states settle. A state equal to Brent's saved snapshot proves non-settling: there is no
    history table. `fuel` bounds the rounds; running out decides nothing. -/
def completeLoop {σ : Type} (step : σ → σ) (same : σ → σ → Bool) :
    Nat → σ → σ → Nat → Nat → RoundOutcome σ
  | 0, _, _, _, _ => .exhausted
  | .succ fuel, previous, saved, age, window =>
      let current := step previous
      if same previous current then .settled current
      else if same saved current then .nonSettling
      else if age + 1 == window then completeLoop step same fuel current current 0 (window * 2)
      else completeLoop step same fuel current saved (age + 1) window

/-- What evaluating a key gives: its fact, no meaning, or no verdict. -/
inductive Cell where
  | pending
  | fact (fact : Fact)
  | meaningless
  | exhausted
  deriving DecidableEq, Repr, Inhabited

def Cell.patterns : Cell → Patterns
  | .fact f => f.patterns
  | _ => []

section Component

variable (sys : System) (opened : Nat → Bool) (members : List Nat) (lower : Nat → Patterns)

/-- How a round reads: a member from the state, anything else from the lower facts, fixed during the component. -/
def readThrough (state : Nat → Fact) (target : Nat) : Patterns :=
  if members.contains target then (state target).patterns else lower target

def nextFact (state : Nat → Fact) (k : Nat) : Fact :=
  composeWith (sys.equation k) opened (readThrough members lower state)

/-- One simultaneous round: every member from the preceding state only. -/
def roundStep (state : Memo Fact) : Memo Fact :=
  tabulate members closedFact (nextFact sys opened members lower state.get)

/-- `SameState`: the members' facts agree. -/
def sameState (left right : Memo Fact) : Bool :=
  members.all fun k => left k == right k

/-- The closed gate: every member read as declaring nothing. -/
def gateState : Memo Fact :=
  roundStep sys opened members lower ⟨fun _ => closedFact⟩

/-- Whether a read inside the cycle lifts under the gate: a GENUINE LIFTING CYCLE. -/
def gateLifts : Bool :=
  let gate := gateState sys opened members lower
  members.any fun k =>
    (activeTargets (sys.equation k) opened).any fun t =>
      members.contains t && !acceptsZero (gate t).patterns

end Component

/-- The reads leaving a component. -/
def outsideReads (sys : System) (opened : Nat → Bool) (members : List Nat) : List Nat :=
  members.flatMap fun k => (activeTargets (sys.equation k) opened).filter fun t => !members.contains t

/-- The lower facts a component reads: exactly its reads leaving it, so nothing else about the cells can matter. -/
def lowerReads (sys : System) (opened : Nat → Bool) (members : List Nat) (cells : Nat → Cell) (t : Nat) : Patterns :=
  if (outsideReads sys opened members).contains t then (cells t).patterns else []

/-- One component given the settled cells below it (`SignatureSelector.Evaluate`). A read of an exhausted cell gives
    no verdict, a read of a meaningless cell no meaning; otherwise the closed gate, and its rounds when it lifts. -/
def evalComponent (sys : System) (opened : Nat → Bool) (fuel : Nat) (members : List Nat) (cells : Nat → Cell) :
    Nat → Cell :=
  let outside := outsideReads sys opened members
  if outside.any (fun t => cells t == .exhausted) then fun _ => .exhausted
  else if outside.any (fun t => cells t == .meaningless) then fun _ => .meaningless
  else
    let lower := lowerReads sys opened members cells
    let gate := gateState sys opened members lower
    if !gateLifts sys opened members lower then fun k => .fact (gate k)
    else
      match completeLoop (roundStep sys opened members lower) (sameState members) fuel gate gate 0 1 with
      | .settled state => fun k => .fact (state k)
      | .nonSettling => fun _ => .meaningless
      | .exhausted => fun _ => .exhausted

/-- Whether every read leaving `members` has a settled cell. -/
def layerReady (sys : System) (opened : Nat → Bool) (members : List Nat) (cells : Nat → Cell) : Bool :=
  (outsideReads sys opened members).all fun t => cells t != .pending

/-- One layer: every pending component whose reads are settled is evaluated, each from the same cells. A layer has no
    order among its components, so no enumeration of them can matter. -/
def layer (sys : System) (opened : Nat → Bool) (fuel : Nat) (reach : Nat → List Nat) (cells : Memo Cell) :
    Memo Cell :=
  tabulate sys.keys .pending fun k =>
    match cells k with
    | .pending =>
        let members := componentOf sys reach k
        if layerReady sys opened members cells.get then evalComponent sys opened fuel members cells.get k
        else .pending
    | settled => settled

def layers (sys : System) (opened : Nat → Bool) (fuel : Nat) (reach : Nat → List Nat) :
    Nat → Memo Cell → Memo Cell
  | 0, cells => cells
  | .succ n, cells => layers sys opened fuel reach n (layer sys opened fuel reach cells)

/-- The reading of the WHOLE system under the classification `opened`, dependency-first. -/
def evalVector (sys : System) (opened : Nat → Bool) (fuel : Nat) : Memo Cell :=
  layers sys opened fuel (tabulate sys.keys [] (reachOf sys opened)).get sys.keys.length ⟨fun _ => .pending⟩

/-! ## Rule G6 -/

def links (sys : System) : List Nat := sys.keys.filter fun k => (sys.equation k).isLink

/-- All subsets of a list; each is a classification or a support set. -/
def subsetsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: rest => let below := subsetsOf rest; below ++ below.map (x :: ·)

/-- The class function of a subset: a calculation exactly when it is in the subset. -/
def classOf (subset : List Nat) (k : Nat) : Bool := subset.contains k

inductive Groundedness where
  | grounded
  | undetermined
  | ungrounded
  | noVerdict
  deriving DecidableEq, Repr

/-- A link that stays a nonempty calculation in this reading. -/
def stillCalculation (cells : Nat → Cell) (link : Nat) : Bool :=
  match cells link with
  | .fact f => !f.patterns.isEmpty
  | _ => false

/-- A link with no fact in this reading. -/
def undecidedLink (cells : Nat → Cell) (link : Nat) : Bool :=
  match cells link with
  | .fact _ => false
  | _ => true

/-- One counterfactual: `some true` when the support is REFUTED (a member stays a nonempty calculation without it),
    `some false` when it is unfounded (every member evaluates, to empty), `none` when undetermined. `support` must be
    nonempty to mean anything. -/
def refutedWithout (cells : Nat → Cell) (support : List Nat) : Option Bool :=
  if support.any (stillCalculation cells) then some true
  else if support.any (undecidedLink cells) then none
  else some false

/-- Whether a reading has a cell with no verdict. No cell stays pending (`no_pending_cell`); the case is kept here
    so that the model never invents an answer for one. -/
def noVerdict (sys : System) (cells : Nat → Cell) : Bool :=
  sys.keys.any fun k => cells k == .exhausted || cells k == .pending

/-- `GroundednessOf`: every nonempty set of calculation links must be refuted. A counterfactual with no verdict decides
    nothing about groundedness: as in C#, where exhaustion ends the selection, it leaves the whole row without a verdict. -/
def groundednessOf (sys : System) (fuel : Nat) (linkSet : List Nat) (assigned : Nat → Bool) : Groundedness :=
  let calculations := linkSet.filter assigned
  let readings := ((subsetsOf calculations).filter (!·.isEmpty)).map fun support =>
    (support, evalVector sys (fun k => assigned k && !classOf support k) fuel)
  if readings.any (fun reading => noVerdict sys reading.2.get) then .noVerdict
  else
    let verdicts := readings.map fun reading => refutedWithout reading.2.get reading.1
    if verdicts.contains (some false) then .ungrounded
    else if verdicts.contains none then .undetermined
    else .grounded

inductive Row where
  | exhausted
  | refuted
  | meaningless
  | consistent (verdict : Groundedness) (facts : Nat → Fact)


def factOf : Cell → Fact
  | .fact f => f
  | _ => closedFact

/-- Whether a link evaluates against its assigned class. -/
def refutesClass (cells : Nat → Cell) (assigned : Nat → Bool) (l : Nat) : Bool :=
  match cells l with
  | .fact f => (!f.patterns.isEmpty) != assigned l
  | _ => false

/-- One classification's row (`Table`). -/
def rowOf (sys : System) (fuel : Nat) (linkSet : List Nat) (assigned : Nat → Bool) : Row :=
  let cells := evalVector sys assigned fuel
  if noVerdict sys cells.get then .exhausted
  else if linkSet.any (refutesClass cells.get assigned) then .refuted
  else if sys.keys.any (fun k => cells k == .meaningless) then .meaningless
  else
    match groundednessOf sys fuel linkSet assigned with
    | .noVerdict => .exhausted
    | verdict => .consistent verdict (fun k => factOf (cells k))

/-- The refusal categories of `SignatureSelectionOutcome`. -/
inductive Refusal where
  | ambiguous
  | contradiction
  | ungroundedOnly
  | undetermined
  | nonSettling
  deriving DecidableEq, Repr

inductive Outcome where
  | selected (facts : Nat → Fact)
  | refused (category : Refusal)
  | exhausted

def Row.isExhausted : Row → Bool
  | .exhausted => true
  | _ => false

def Row.isGrounded : Row → Bool
  | .consistent .grounded _ => true
  | _ => false

def Row.isUndetermined : Row → Bool
  | .consistent .undetermined _ => true
  | _ => false

def Row.isUngrounded : Row → Bool
  | .consistent .ungrounded _ => true
  | _ => false

def Row.isMeaningless : Row → Bool
  | .meaningless => true
  | _ => false

def Outcome.isExhausted : Outcome → Bool
  | .exhausted => true
  | _ => false

/-- RULE G6 (`SignatureSelector.Rule`): exactly one grounded reading and nothing undetermined selects; each other case
    refuses by its category. There is no search beyond the rows: each classification has one reading. -/
def rule (rows : List Row) : Outcome :=
  if rows.any Row.isExhausted then .exhausted
  else
    match rows.filter Row.isGrounded with
    | _ :: _ :: _ => .refused .ambiguous
    | [.consistent _ facts] =>
        if rows.any Row.isUndetermined then .refused .undetermined else .selected facts
    | [_] => .refused .undetermined
    | [] =>
        if rows.any Row.isUndetermined then .refused .undetermined
        else if rows.any Row.isUngrounded then .refused .ungroundedOnly
        else if rows.any Row.isMeaningless then .refused .nonSettling
        else .refused .contradiction

/-- THE REFERENCE KERNEL: rule G6 over every classification of the whole system. -/
def select (sys : System) (fuel : Nat) : Outcome :=
  let linkSet := links sys
  rule ((subsetsOf linkSet).map fun gamma => rowOf sys fuel linkSet (classOf gamma))

/-! ## Rendering, for the bridge -/

def renderParameter (parameter : CallableParameter) : String :=
  match parameter.kind with
  | .normal => parameter.name
  | .collecting => "*" ++ parameter.name
  | .metaRef => "meta " ++ parameter.name

mutual
  def renderPattern : ParameterPattern → String
    | .capture parameter => renderParameter parameter
    | .sequenceValue items => "(" ++ renderList items ++ ")"
    | .listValue items => "[" ++ renderList items ++ "]"
    | .unpacking items => "<" ++ renderList items ++ ">"

  def renderList : Patterns → String
    | [] => ""
    | [item] => renderPattern item
    | item :: rest => renderPattern item ++ "," ++ renderList rest
end

def renderViolation : Option ParameterPattern.SignatureViolation → String
  | none => ""
  | some .singletonSequencePattern => "!singleton"
  | some .multipleCollectingAtOneLevel => "!collectors"
  | some .repeatedNameIncludesCollecting => "!repeated"

def renderRefusal : Refusal → String
  | .ambiguous => "Ambiguous"
  | .contradiction => "Contradiction"
  | .ungroundedOnly => "UngroundedOnly"
  | .undetermined => "Undetermined"
  | .nonSettling => "NonSettling"

/-- One outcome as the bridge compares it: every key's fact in key order, or the refusal category. -/
def renderOutcome (sys : System) : Outcome → String
  | .selected facts =>
      "selected " ++ " ".intercalate (sys.keys.map fun k =>
        s!"{k}:({renderList (facts k).patterns}){renderViolation (facts k).violation}")
  | .refused category => "refused " ++ renderRefusal category
  | .exhausted => "exhausted"

end KatLang.SignatureCompletion
