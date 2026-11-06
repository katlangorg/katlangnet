import KatLangArityLaws.SignatureCompletionOrder
import KatLangArityLaws.SignatureCompletionStructure
import KatLangArityLaws.SignatureCompletionRelabel
import KatLangArityLaws.SignatureCompletionBridgeCases
import KatLangArityLaws.SignatureCompletionOutcomes

open KatLang KatLang.SignatureCompletion KatLang.SignatureCompletion.Bridge

/-!
# SC-1 guards: the kernel on concrete systems, the bridge corpus, and the negative controls

Everything here is about the REFERENCE KERNEL. `bridge_outcomes_are_the_models` recomputes the outcome of every bridge system
and compares it with the committed file the C# bridge reads, so the agreement chain is: the real selector equals that
file (`SignatureCompletionBridgeTests`, the .NET phase) and that file is what this kernel computes (this guard, the Lean
phase). Agreement is on this corpus only.
-/

namespace KatLang.SignatureCompletion.Guards

/-! ## The agreement guard -/

def committedOutcomes : String := include_str "../../tests/KatLang.Tests/SignatureCompletion/lean-model-outcomes.txt"

/- `bridge_outcomes_are_the_models`: the committed outcomes ARE this kernel's, line for line. -/
#guard renderCorpus bridgeCases == committedOutcomes

#guard bridgeCases.length == 299

def bridgeSystem (id : String) : System :=
  ((bridgeCases.find? (·.1 == id)).map (·.2)).getD { keys := [], equation := fun _ => {} }

def outcomeOf (id : String) : String := renderOutcome (bridgeSystem id) (select (bridgeSystem id) bridgeFuel)

/-! ## Hand-derived expectations, independent of any native run -/

private def p (name : String) : ParameterPattern := .capture { name := name }
private def c (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }
private def m (name : String) : ParameterPattern := .capture { name := name, kind := .metaRef }
private def own (names : List String) : Patterns := names.map p
private def read (k : Nat) : Reference := ⟨.member k, k, none⟩
private def ext (id : Nat) (patterns : Patterns) : Reference := ⟨.external patterns, 100 + id, none⟩

/-- `A = … x + y … B + 1`, `B = A + z`: `A(x, y, z)`, `B(z, x, y)`. Written order decides; both are round results. -/
def writtenOrder : System := System.ofList
  [{ own := own ["x", "y"], references := [read 1] }, { own := own ["z"], references := [read 0] }]

#guard renderOutcome writtenOrder (select writtenOrder 16) == "selected 0:(x,y,z) 1:(z,x,y)"

/-- `A = B + X`, `B = A + Y`: two successive states alternate. -/
def oscillating : System := System.ofList
  [{ references := [read 1, ext 0 [p "x"]] }, { references := [read 0, ext 1 [p "y"]] }]

#guard renderOutcome oscillating (select oscillating 16) == "refused NonSettling"

/-- `F = F + G + E`, `G = p + F`: the rounds reach `F(e, p)`; the equally consistent `F(p, e)` is not sought. -/
def severalAnswers : System := System.ofList
  [{ references := [read 0, read 1, ext 0 [p "e"]] }, { own := own ["p"], references := [read 0] }]

#guard renderOutcome severalAnswers (select severalAnswers 16) == "selected 0:(e,p) 1:(p,e)"

/-- `(p, e)` is ALSO a fixed point of the composition law: uniqueness is not what selects. -/
def otherFixedPoint : Nat → Fact
  | 0 => ⟨own ["p", "e"], none⟩
  | _ => ⟨own ["p", "e"], none⟩

#guard composeWith (severalAnswers.equation 0) (fun _ => false) (fun t => (otherFixedPoint t).patterns) == otherFixedPoint 0
#guard composeWith (severalAnswers.equation 1) (fun _ => false) (fun t => (otherFixedPoint t).patterns) == otherFixedPoint 1

/-- Grouped, list, META: `A = P + M + Q + B`, `B = A + 0`. A group stays a group, META lifts as ordinary, an already bound name
    is filtered out of a list group, which keeps its brackets. -/
def patternShapes : System := System.ofList
  [{ references := [ext 0 [.sequenceValue [p "a", p "b"]], ext 1 [m "r"], ext 2 [.listValue [p "a", p "d"]], read 1] },
   { references := [read 0] }]

#guard renderOutcome patternShapes (select patternShapes 16) == "selected 0:((a,b),r,[d]) 1:((a,b),r,[d])"

/-- A collector survives as a collector; a second one is the X-02 flag on the recovered list. -/
def twoCollectors : System := System.ofList
  [{ references := [ext 0 [p "a", c "p"], ext 1 [p "b", c "q"]] }]

#guard renderOutcome twoCollectors (select twoCollectors 16) == "selected 0:(a,*p,b,q)!collectors"

/-- A link read by a guard: the reader lifts `X` exactly when the link is a calculation. -/
def linked : System := System.ofList
  [{ references := [⟨.external [p "x"], 100, some 1⟩] }, { references := [ext 1 [p "k"]], isLink := true }]

#guard renderOutcome linked (select linked 16) == "selected 0:(x) 1:(k)"

/-! ## Non-vacuity: the theorems' premises hold of real systems, and the verdicts are kernel-checked -/

def twoEquationsWellFormed (equations : List Equation)
    (h : ∀ k < equations.length, ∀ r ∈ (equations.getD k {}).references,
      (∀ t, r.target = .member t → t < equations.length) ∧ (∀ g, r.guard = some g → g < equations.length)) :
    (System.ofList equations).WellFormed where
  nodup := List.nodup_range
  targets := by
    intro k hk r hr
    have hk' : k < equations.length := List.mem_range.1 hk
    have := h k hk' r hr
    exact ⟨fun t e => List.mem_range.2 (this.1 t e), fun g e => List.mem_range.2 (this.2 g e)⟩

theorem writtenOrder_wf : writtenOrder.WellFormed := by
  refine twoEquationsWellFormed _ ?_
  intro k hk r hr
  have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases hk2 with rfl | rfl <;> simp [read] at hr <;> subst hr <;> simp

/-- `select_obligations` and `publish` are not vacuous: a recursive system is selected and published. -/
theorem writtenOrder_selected : ∃ facts, select writtenOrder 16 = .selected facts := ⟨_, rfl⟩

theorem writtenOrder_published : (publish writtenOrder 16 writtenOrder_wf).isSome = true := by
  obtain ⟨facts, h⟩ := writtenOrder_selected
  unfold publish
  split
  · rfl
  · simp_all
  · simp_all

/-- `nonSettling_never_settles` is not vacuous: oscillation is refused at any bound above its period. -/
theorem oscillating_refused : select oscillating 16 = .refused .nonSettling := rfl

/-- EXHAUSTION DECIDES NOTHING, on the witnesses: the same systems have no verdict at bound zero and opposite verdicts above
    it, so an exhausted selection can mean neither "inconsistent" nor "divergent". -/
theorem exhausted_decides_nothing :
    (select writtenOrder 0).isExhausted = true ∧ (select oscillating 0).isExhausted = true
      ∧ (∃ facts, select writtenOrder 16 = .selected facts) ∧ select oscillating 16 = .refused .nonSettling :=
  ⟨rfl, rfl, writtenOrder_selected, oscillating_refused⟩

/-- `acyclic_agrees`' premise is satisfiable: a chain and its order. -/
def chain : System := System.ofList [{ references := [read 1, ext 0 [p "a"]] }, { references := [ext 1 [p "b"]] }]

theorem chain_wf : chain.WellFormed := by
  refine twoEquationsWellFormed _ ?_
  intro k hk r hr
  have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases hk2 with rfl | rfl
  · simp [read, ext] at hr
    rcases hr with rfl | rfl <;> simp
  · simp [ext] at hr
    subst hr
    simp

theorem chain_topological : Topological chain (fun _ => false) [1, 0] where
  nodup := by decide
  keys := by
    intro k
    have : chain.keys = [0, 1] := rfl
    rw [this]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  before := by
    intro k hk t ht
    have hk' : k = 0 ∨ k = 1 := by
      have : chain.keys = [0, 1] := rfl
      rw [this] at hk
      simpa using hk
    rcases hk' with rfl | rfl
    · have : activeTargets (chain.equation 0) (fun _ => false) = [1] := rfl
      rw [this] at ht
      simp only [List.mem_singleton] at ht
      subst ht
      decide
    · have : activeTargets (chain.equation 1) (fun _ => false) = [] := rfl
      rw [this] at ht
      cases ht

example : (evalVector chain (fun _ => false) 0).get 0
    = .fact (applyOrder chain (fun _ => false) [1, 0] (fun _ => closedFact) 0) :=
  acyclic_agrees chain _ 0 chain_wf chain_topological (by decide)

/-! ## Relabeling, concretely -/

def swapKeys (k : Nat) : Nat := if k = 0 then 1 else if k = 1 then 0 else k

theorem swapKeys_twice (k : Nat) : swapKeys (swapKeys k) = k := by
  unfold swapKeys
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k = 1
    · simp [h1]
    · simp [h0, h1]

def swapRelabeling : Relabeling where
  key := swapKeys
  inv := swapKeys
  left := swapKeys_twice
  right := swapKeys_twice
  identity := (· + 1000)
  identity_injective h := by simpa using h

/- Renamed keys and identities and reversed storage: the same answer, under the swapped keys. -/
#guard renderOutcome (writtenOrder.relabel swapRelabeling [1, 0]) (select (writtenOrder.relabel swapRelabeling [1, 0]) 16)
  == "selected 1:(x,y,z) 0:(z,x,y)"

/-! ## Negative controls: the comparison can fail -/

def twoCallees : System := System.ofList [{ references := [ext 0 [p "p"], ext 1 [p "q"]] }]

def reverseReferences (sys : System) : System :=
  { sys with equation := fun k => { sys.equation k with references := (sys.equation k).references.reverse } }

/- Written reference order is NOT internal: reversing it changes the answer. A selector with that defect fails the bridge. -/
#guard renderOutcome twoCallees (select twoCallees 16) == "selected 0:(p,q)"
#guard renderOutcome twoCallees (select (reverseReferences twoCallees) 16) == "selected 0:(q,p)"
#guard (bridgeCases.filter fun (id, sys) => id.startsWith "random" &&
    renderOutcome sys (select (reverseReferences sys) bridgeFuel) != renderOutcome sys (select sys bridgeFuel)).length > 10

mutual
  def plainPattern : ParameterPattern → ParameterPattern
    | .capture parameter => .capture { parameter with kind := .normal }
    | .sequenceValue items => .sequenceValue (plainList items)
    | .listValue items => .listValue (plainList items)
    | .unpacking items => .unpacking (plainList items)

  def plainList : Patterns → Patterns
    | [] => []
    | item :: rest => plainPattern item :: plainList rest
end

def eraseKinds (sys : System) : System :=
  { sys with equation := fun k => { sys.equation k with
      references := (sys.equation k).references.map fun r => { r with
        target := match r.target with
          | .external patterns => .external (plainList patterns)
          | target => target } } }

/- Pattern kinds are not decoration: erasing them changes the answer. -/
#guard renderOutcome twoCollectors (select (eraseKinds twoCollectors) 16) != "selected 0:(a,*p,b,q)!collectors"

/-- IN-PLACE ROUNDS, the wrong round order: each member reads its neighbours' NEW facts. -/
def inPlaceRound (sys : System) (opened : Nat → Bool) (members : List Nat) (lower : Nat → Patterns)
    (state : Memo Fact) : Memo Fact :=
  let final := members.foldl (fun (s : List (Nat × Fact)) k =>
    (k, nextFact sys opened members lower (fun t => (s.lookup t).getD closedFact) k) :: s)
    (members.map fun k => (k, state.get k))
  ⟨fun t => (final.lookup t).getD closedFact⟩

def inPlaceSettles (sys : System) (members : List Nat) : Bool :=
  let gate := gateState sys (fun _ => false) members (fun _ => [])
  match completeLoop (inPlaceRound sys (fun _ => false) members (fun _ => [])) (sameState members) 16 gate gate 0 1 with
  | .settled _ => true
  | _ => false

/- On the corpus's `oscillation`, the kernel refuses; in-place rounds would settle: a wrong round order is detected. -/
#guard outcomeOf "oscillation" == "refused NonSettling"
#guard inPlaceSettles oscillating [0, 1]

/-! ## Axioms: the standard three, pinned -/

/-- info: 'KatLang.SignatureCompletion.select_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms select_obligations

/-- info: 'KatLang.SignatureCompletion.publish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms publish

/-- info: 'KatLang.SignatureCompletion.rowOf_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rowOf_composed

/-- info: 'KatLang.SignatureCompletion.no_pending_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_pending_cell

/-- info: 'KatLang.SignatureCompletion.nonSettling_never_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonSettling_never_settles

/-- info: 'KatLang.SignatureCompletion.select_verdict_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms select_verdict_stable

/-- info: 'KatLang.SignatureCompletion.acyclic_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms acyclic_agrees

/-- info: 'KatLang.SignatureCompletion.select_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms select_relabel

/-- info: 'KatLang.SignatureCompletion.select_storage_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms select_storage_independent

/-- info: 'KatLang.SignatureCompletion.repetition_never_settles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms repetition_never_settles

/-- info: 'KatLang.SignatureCompletion.composeFact_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms composeFact_ordered

/-- info: 'KatLang.SignatureCompletion.missingPattern_whole' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms missingPattern_whole

end KatLang.SignatureCompletion.Guards
