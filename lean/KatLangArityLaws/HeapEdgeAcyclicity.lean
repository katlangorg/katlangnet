import KatLangArityLaws.AddressInvariantProduction

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.EvaluatorCore

/-!
# FC-AC: which need-heap edges are acyclic

"The heap is acyclic" is not one claim. This module proves the claim that is true for production and
`HeapEdgeAcyclicityGuards.lean` refutes the one that is false; the ledger `docs/design/formal-correspondence-ledger.md`
keeps the other graphs apart (host ASTs, demand/wait, callable dependencies).

* **Collector slice edges are acyclic for production.** `a → b` when the cell at `a` is a collector whose slice holds
  `b`. Every such edge descends strictly (`collector_path_descends`), so no path of them closes
  (`collector_no_cycle`), in every state satisfying `Inv`; every production evaluator operation keeps `Inv`
  (`production_sound_all`), so that holds after every production operation from an `Inv` entry
  (`production_collector_no_cycle`), in particular from `EvalState.empty`.

* **The graph of ALL stored addresses is NOT acyclic.** A plan's prepared supply is written after the plan cell exists and a
  completed VALUE can hold a `callRef`, so a stored edge can point to a younger cell and back: the guard
  `stored_addresses_have_a_cycle` runs a valid program whose final heap holds a two-cycle. Allocation order is a ranking of
  collector edges only. No result here, or in `Inv`, depends on stored-address acyclicity, and no evaluator or binder law
  needs it: a stored edge is not a demand.

Not claimed: anything about C# `NeedCell` graphs, the demand wait-for graph, or termination.
-/

namespace KatLang.HeapEdgeAcyclicity

/-- One collector slice edge. -/
def CollectorEdge (heap : Array NeedCell) (a b : Nat) : Prop :=
  ∃ cell slice, heap[a]? = some cell ∧ cell.suspension = .collector slice ∧ b ∈ slice

/-- A nonempty path of collector slice edges. -/
inductive CollectorPath (heap : Array NeedCell) : Nat → Nat → Prop where
  | edge {a b} : CollectorEdge heap a b → CollectorPath heap a b
  | step {a b c} : CollectorEdge heap a b → CollectorPath heap b c → CollectorPath heap a c

theorem collector_edge_descends {heap : Array NeedCell} (v : ValidCollectorHeap heap) {a b : Nat}
    (h : CollectorEdge heap a b) : b < a := by
  obtain ⟨cell, slice, hc, hs, hb⟩ := h
  exact v a cell hc slice hs b hb

/-- Every collector path descends strictly in allocation order. -/
theorem collector_path_descends {heap : Array NeedCell} (v : ValidCollectorHeap heap) {a b : Nat}
    (h : CollectorPath heap a b) : b < a := by
  induction h with
  | edge e => exact collector_edge_descends v e
  | step e _ ih =>
    have := collector_edge_descends v e
    omega

theorem collector_no_cycle {heap : Array NeedCell} (v : ValidCollectorHeap heap) (a : Nat) :
    ¬ CollectorPath heap a a := fun h => Nat.lt_irrefl _ (collector_path_descends v h)

/-- COLLECTOR EDGES ARE ACYCLIC FOR PRODUCTION: after every production evaluator operation from an `Inv` state that meets
    the operation's structural contract, whatever its outcome. -/
theorem production_collector_no_cycle (c : EvalCall) (s : EvalState) (vs : Inv s) (ps : CallPre c s.needs) (a : Nat) :
    ¬ CollectorPath ((evalUnbounded c).runState s).2.needs a a :=
  collector_no_cycle (production_sound_all c s vs ps).1.collectors a

/-- The empty entry state, which every public run starts from. -/
theorem production_collector_no_cycle_from_empty (c : EvalCall) (ps : CallPre c EvalState.empty.needs) (a : Nat) :
    ¬ CollectorPath ((evalUnbounded c).runState EvalState.empty).2.needs a a :=
  production_collector_no_cycle c _ empty_inv ps a

end KatLang.HeapEdgeAcyclicity
