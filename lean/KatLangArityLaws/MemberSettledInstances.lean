import KatLangArityLaws.MemberSettled
import KatLangArityLaws.MemberBridgeSourcePaths
import KatLangArityLaws.MemberBridgeSourceParameters

/-!
# Settled navigation DERIVED from the probe, applied (E-18 step 1, M1)

`MemberBridgeSourceInstances` and its companions apply `member_bridge_settled` with the settledness
premise established on the run's own states. This module applies the GENERAL theorems of
`MemberSettled` to the same source programs: `NavSettled` at the probe's exit is DERIVED — from the
production probe, the state-free lookup and the unfolded alias chase — and the member bridge is
concluded from the state BEFORE the plan's classification (`entry`, the state the VALUE shell runs
the plan from), with the production probe itself as the navigation premise:

| namespace | receiver | theorem applied | what is derived |
| --- | --- | --- | --- |
| `Ref…` (five bundles) | `AB = Box` | `member_bridge_reference_of_probe` | the reference's chase from every state |
| `Open…` (two bundles) | `OBox`, through `open OLib` | `member_bridge_name_of_probe` | the opened name's lookup from every state |
| `Nested…` (three bundles) | `Lib.Sub` | `navSettled_member` over `navSettled_plain_name_of_probe` | the path, member by member |
| `Param…` (three bundles) | `b` | `navSettled_param_of_probe` | the first projection's memo read back (the probe WRITES) |
| `ParamPath` | `b.Sub` | `navSettled_member` over `navSettled_param_of_probe` | a parameter-rooted path |

Each namespace re-uses the definitions and the reachability chain of the instance of the same name
(`KatLang.MemberStabilityInstances.…`: `captured`, `plan_cell`, `probe_entry`, `selected`); the new
facts are the lookups the general theorems ask for (each proved by `cbv` at `entry` — and, the
lookup being state-free, thereby at every state), and production's completion from `entry`.

`nav_settled` is the derived `NavSettled` — a statement over EVERY navigation extension of the
probe's exit state, not over the run's own states; `bridge_of_probe` is the member bridge.

Not here: the runtime-target alias (`RTC`, `RTA`) and the path-row reference (`ALS = Lib.Sub`) —
their structure chase is not unfolded by `MemberSettled`. They are in `MemberRereadInstances`,
where the general re-read theorem (`NavigationSettled.member_bridge_of_probe`) is applied to every
instance of this module too.
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.MemberStabilityInstances
open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
open KatLang.PlanConservativity (isAliasAlg)

namespace KatLang.MemberSettledInstances

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## Transparent references: `AB = Box` -/

namespace RefEmpty
open KatLang.MemberStabilityInstances.RefEmpty

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "AB" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
def aParent : Option ScopeCtx := match sel.alg with | .alias q _ _ _ _ _ => q | _ => none
def aOpens : List Expr := match sel.alg with | .alias _ o _ _ _ _ => o | _ => []
def aProps : List PropDef := match sel.alg with | .alias _ _ pr _ _ _ => pr | _ => []
def aId : Option PropertyIdentity := match sel.alg with | .alias _ _ _ _ i _ => i | _ => none
/-- The selected binding IS a transparent reference whose row is the name `Box`. -/
abbrev A : Algorithm := .alias aParent aOpens aProps (.resolve "Box") aId true
/-- The row's lookup, in the reference's OWN scope. -/
def tgt : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry)) ∧
    (sel.alg = A) ∧
    ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry)) ∧
    (isAliasAlg tgt.alg = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "AB") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "AB") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

theorem sel_reference : sel.alg = A :=
  facts.2.2.2.1

theorem target_entry : (lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry) :=
  facts.2.2.2.2.1

theorem target_plain : isAliasAlg tgt.alg = false :=
  facts.2.2.2.2.2

/-- **`navSettled_reference_of_probe` APPLIED**: the probe changed nothing, the identity is the
    reference's target, and the navigation is settled over EVERY navigation extension. -/
theorem nav_settled : probed = entry ∧ owner = tgt.alg ∧ NavSettled (.resolve "AB") ctx owner probed :=
  navSettled_reference_of_probe "AB" ctx top ctx.callStack.tail entry probed owner hcs probe aParent aOpens aProps
    "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt target_entry target_plain

/-- **`member_bridge_reference_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_reference_of_probe 0 "AB" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs
    probe select aParent aOpens aProps "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt
    target_entry target_plain production_entry

end RefEmpty

namespace RefSpreadNone
open KatLang.MemberStabilityInstances.RefSpreadNone

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "AB" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
def aParent : Option ScopeCtx := match sel.alg with | .alias q _ _ _ _ _ => q | _ => none
def aOpens : List Expr := match sel.alg with | .alias _ o _ _ _ _ => o | _ => []
def aProps : List PropDef := match sel.alg with | .alias _ _ pr _ _ _ => pr | _ => []
def aId : Option PropertyIdentity := match sel.alg with | .alias _ _ _ _ i _ => i | _ => none
/-- The selected binding IS a transparent reference whose row is the name `Box`. -/
abbrev A : Algorithm := .alias aParent aOpens aProps (.resolve "Box") aId true
/-- The row's lookup, in the reference's OWN scope. -/
def tgt : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry)) ∧
    (sel.alg = A) ∧
    ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry)) ∧
    (isAliasAlg tgt.alg = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "AB") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "AB") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

theorem sel_reference : sel.alg = A :=
  facts.2.2.2.1

theorem target_entry : (lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry) :=
  facts.2.2.2.2.1

theorem target_plain : isAliasAlg tgt.alg = false :=
  facts.2.2.2.2.2

/-- **`navSettled_reference_of_probe` APPLIED**: the probe changed nothing, the identity is the
    reference's target, and the navigation is settled over EVERY navigation extension. -/
theorem nav_settled : probed = entry ∧ owner = tgt.alg ∧ NavSettled (.resolve "AB") ctx owner probed :=
  navSettled_reference_of_probe "AB" ctx top ctx.callStack.tail entry probed owner hcs probe aParent aOpens aProps
    "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt target_entry target_plain

/-- **`member_bridge_reference_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_reference_of_probe 0 "AB" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs
    probe select aParent aOpens aProps "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt
    target_entry target_plain production_entry

end RefSpreadNone

namespace RefSpreadOne
open KatLang.MemberStabilityInstances.RefSpreadOne

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "AB" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
def aParent : Option ScopeCtx := match sel.alg with | .alias q _ _ _ _ _ => q | _ => none
def aOpens : List Expr := match sel.alg with | .alias _ o _ _ _ _ => o | _ => []
def aProps : List PropDef := match sel.alg with | .alias _ _ pr _ _ _ => pr | _ => []
def aId : Option PropertyIdentity := match sel.alg with | .alias _ _ _ _ i _ => i | _ => none
/-- The selected binding IS a transparent reference whose row is the name `Box`. -/
abbrev A : Algorithm := .alias aParent aOpens aProps (.resolve "Box") aId true
/-- The row's lookup, in the reference's OWN scope. -/
def tgt : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry)) ∧
    (sel.alg = A) ∧
    ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry)) ∧
    (isAliasAlg tgt.alg = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "AB") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "AB") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

theorem sel_reference : sel.alg = A :=
  facts.2.2.2.1

theorem target_entry : (lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry) :=
  facts.2.2.2.2.1

theorem target_plain : isAliasAlg tgt.alg = false :=
  facts.2.2.2.2.2

/-- **`navSettled_reference_of_probe` APPLIED**: the probe changed nothing, the identity is the
    reference's target, and the navigation is settled over EVERY navigation extension. -/
theorem nav_settled : probed = entry ∧ owner = tgt.alg ∧ NavSettled (.resolve "AB") ctx owner probed :=
  navSettled_reference_of_probe "AB" ctx top ctx.callStack.tail entry probed owner hcs probe aParent aOpens aProps
    "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt target_entry target_plain

/-- **`member_bridge_reference_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_reference_of_probe 0 "AB" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs
    probe select aParent aOpens aProps "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt
    target_entry target_plain production_entry

end RefSpreadOne

namespace RefSpreadFails
open KatLang.MemberStabilityInstances.RefSpreadFails

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "AB" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
def aParent : Option ScopeCtx := match sel.alg with | .alias q _ _ _ _ _ => q | _ => none
def aOpens : List Expr := match sel.alg with | .alias _ o _ _ _ _ => o | _ => []
def aProps : List PropDef := match sel.alg with | .alias _ _ pr _ _ _ => pr | _ => []
def aId : Option PropertyIdentity := match sel.alg with | .alias _ _ _ _ i _ => i | _ => none
/-- The selected binding IS a transparent reference whose row is the name `Box`. -/
abbrev A : Algorithm := .alias aParent aOpens aProps (.resolve "Box") aId true
/-- The row's lookup, in the reference's OWN scope. -/
def tgt : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry)) ∧
    (sel.alg = A) ∧
    ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry)) ∧
    (isAliasAlg tgt.alg = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "AB") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "AB") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

theorem sel_reference : sel.alg = A :=
  facts.2.2.2.1

theorem target_entry : (lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry) :=
  facts.2.2.2.2.1

theorem target_plain : isAliasAlg tgt.alg = false :=
  facts.2.2.2.2.2

/-- **`navSettled_reference_of_probe` APPLIED**: the probe changed nothing, the identity is the
    reference's target, and the navigation is settled over EVERY navigation extension. -/
theorem nav_settled : probed = entry ∧ owner = tgt.alg ∧ NavSettled (.resolve "AB") ctx owner probed :=
  navSettled_reference_of_probe "AB" ctx top ctx.callStack.tail entry probed owner hcs probe aParent aOpens aProps
    "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt target_entry target_plain

/-- **`member_bridge_reference_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_reference_of_probe 0 "AB" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs
    probe select aParent aOpens aProps "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt
    target_entry target_plain production_entry

end RefSpreadFails

namespace RefOrdinary
open KatLang.MemberStabilityInstances.RefOrdinary

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "AB" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
def aParent : Option ScopeCtx := match sel.alg with | .alias q _ _ _ _ _ => q | _ => none
def aOpens : List Expr := match sel.alg with | .alias _ o _ _ _ _ => o | _ => []
def aProps : List PropDef := match sel.alg with | .alias _ _ pr _ _ _ => pr | _ => []
def aId : Option PropertyIdentity := match sel.alg with | .alias _ _ _ _ i _ => i | _ => none
/-- The selected binding IS a transparent reference whose row is the name `Box`. -/
abbrev A : Algorithm := .alias aParent aOpens aProps (.resolve "Box") aId true
/-- The row's lookup, in the reference's OWN scope. -/
def tgt : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry)) ∧
    (sel.alg = A) ∧
    ((lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry)) ∧
    (isAliasAlg tgt.alg = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "AB") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "AB") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "AB" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

theorem sel_reference : sel.alg = A :=
  facts.2.2.2.1

theorem target_entry : (lookupLexicalPropertyRaw A "Box" (ctx.push A)).runState entry = (.ok tgt, entry) :=
  facts.2.2.2.2.1

theorem target_plain : isAliasAlg tgt.alg = false :=
  facts.2.2.2.2.2

/-- **`navSettled_reference_of_probe` APPLIED**: the probe changed nothing, the identity is the
    reference's target, and the navigation is settled over EVERY navigation extension. -/
theorem nav_settled : probed = entry ∧ owner = tgt.alg ∧ NavSettled (.resolve "AB") ctx owner probed :=
  navSettled_reference_of_probe "AB" ctx top ctx.callStack.tail entry probed owner hcs probe aParent aOpens aProps
    "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt target_entry target_plain

/-- **`member_bridge_reference_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_reference_of_probe 0 "AB" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs
    probe select aParent aOpens aProps "Box" aId (fun r h => by rw [lookup_unique r h]; exact sel_reference) tgt
    target_entry target_plain production_entry

end RefOrdinary

/-! ## Names selected through `open` -/

namespace OpenEmpty
open KatLang.MemberStabilityInstances.OpenEmpty

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "OBox" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok sel, entry)) ∧
    (Algorithm.lookupPropDefAny? top "OBox" = none ∧ (top.parent.bind fun sc => lookupInParentsStructuralProperty sc "OBox") = none) ∧
    (structureNormal sel.alg = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "OBox") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "OBox") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

/-- **Selected through `open`**: neither the site nor its enclosing scopes declare the name. -/
theorem opened : Algorithm.lookupPropDefAny? top "OBox" = none ∧
    (top.parent.bind fun sc => lookupInParentsStructuralProperty sc "OBox") = none :=
  facts.2.2.2.1

theorem sel_plain : structureNormal sel.alg = true :=
  facts.2.2.2.2

/-- **`navSettled_plain_name_of_probe` APPLIED** to a name an opened namespace provides. -/
theorem nav_settled : probed = entry ∧ NavSettled (.resolve "OBox") ctx owner probed :=
  navSettled_plain_name_of_probe "OBox" ctx top ctx.callStack.tail entry probed owner hcs probe
    (fun r h => by rw [lookup_unique r h]; exact sel_plain)

/-- **`member_bridge_name_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_name_of_probe 0 "OBox" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs probe
    select (fun r h => by rw [lookup_unique r h]; exact sel_plain) production_entry

end OpenEmpty

namespace OpenSpreadNone
open KatLang.MemberStabilityInstances.OpenSpreadNone

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The binding the name selects (computed by the evaluator's lookup). -/
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "OBox" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok sel, entry)) ∧
    (Algorithm.lookupPropDefAny? top "OBox" = none ∧ (top.parent.bind fun sc => lookupInParentsStructuralProperty sc "OBox") = none) ∧
    (structureNormal sel.alg = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.resolve "OBox") ctx).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
theorem select : selectDotEdge ctx (.resolve "OBox") N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h
theorem lookup_entry : (lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.1

theorem lookup_unique (r : ResolvedProperty)
    (h : (lookupLexicalPropertyRaw top "OBox" ctx).runState entry = (.ok r, entry)) : r = sel := by
  rw [lookup_entry] at h
  exact (Except.ok.inj (Prod.mk.inj h).1).symm

/-- **Selected through `open`**: neither the site nor its enclosing scopes declare the name. -/
theorem opened : Algorithm.lookupPropDefAny? top "OBox" = none ∧
    (top.parent.bind fun sc => lookupInParentsStructuralProperty sc "OBox") = none :=
  facts.2.2.2.1

theorem sel_plain : structureNormal sel.alg = true :=
  facts.2.2.2.2

/-- **`navSettled_plain_name_of_probe` APPLIED** to a name an opened namespace provides. -/
theorem nav_settled : probed = entry ∧ NavSettled (.resolve "OBox") ctx owner probed :=
  navSettled_plain_name_of_probe "OBox" ctx top ctx.callStack.tail entry probed owner hcs probe
    (fun r h => by rw [lookup_unique r h]; exact sel_plain)

/-- **`member_bridge_name_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_name_of_probe 0 "OBox" N (.resolve N) args ctx [] top ctx.callStack.tail entry probed owner p hcs probe
    select (fun r h => by rw [lookup_unique r h]; exact sel_plain) production_entry

end OpenSpreadNone

/-! ## Nested member paths: `Lib.Sub` -/

namespace NestedEmpty
open KatLang.MemberStabilityInstances.NestedEmpty

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The receiver path's HEAD `Lib`: its own production probe. -/
def headOwner : Algorithm :=
  match ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry).1 with
  | .ok (some a) => a
  | _ => top
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- The member step `Sub`: declared by the head's structure, accessible, structure-normal. -/
def q : PropDef := (Algorithm.lookupPropDefAny? headOwner "Sub").getD { name := "", alg := top, isPublic := false }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry)) ∧
    ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry)) ∧
    (structureNormal sel.alg = true) ∧
    (Algorithm.lookupPropDefAny? headOwner "Sub" = some q) ∧
    (memberAccessible? ctx headOwner q = true) ∧
    (childOfInContext headOwner q.alg ctx = owner) ∧
    (structureNormal owner = true) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem head_probe : (resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry) :=
  facts.2.2.1

theorem lookup_entry : (lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.2.1

theorem sel_plain : structureNormal sel.alg = true :=
  facts.2.2.2.2.1

theorem head_settled : NavSettled (.resolve "Lib") ctx headOwner entry :=
  (navSettled_plain_name_of_probe "Lib" ctx top ctx.callStack.tail entry entry headOwner hcs head_probe
    (fun r h => by
      rw [lookup_entry] at h
      rw [← Except.ok.inj (Prod.mk.inj h).1]
      exact sel_plain)).2
theorem member_declared : Algorithm.lookupPropDefAny? headOwner "Sub" = some q :=
  facts.2.2.2.2.2.1

theorem member_accessible : memberAccessible? ctx headOwner q = true :=
  facts.2.2.2.2.2.2.1

theorem member_owner : childOfInContext headOwner q.alg ctx = owner :=
  facts.2.2.2.2.2.2.2.1

theorem member_plain : structureNormal owner = true :=
  facts.2.2.2.2.2.2.2.2.1

theorem probe_inert : probed = entry :=
  facts.2.2.2.2.2.2.2.2.2

/-- **`navSettled_member` over `navSettled_plain_name_of_probe` APPLIED**: the nested member path is
    settled, member by member. -/
theorem nav_settled : NavSettled target ctx owner probed := by
  rw [probe_inert]
  have h := navSettled_member (.resolve "Lib") "Sub" (.resolve "Sub") ctx headOwner q
    (childOfInContext headOwner q.alg ctx) entry head_settled member_declared member_accessible
    (structSettled_normal _ ctx entry (by rw [member_owner]; exact member_plain))
  rw [member_owner] at h
  exact h

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_settled 0 target N (.resolve N) args ctx [] entry probed alg? owner p probe_entry selected
    (fun x _ _ hx => by simp [target, headParam?] at hx) nav_settled production_entry

end NestedEmpty

namespace NestedSpreadOne
open KatLang.MemberStabilityInstances.NestedSpreadOne

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The receiver path's HEAD `Lib`: its own production probe. -/
def headOwner : Algorithm :=
  match ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry).1 with
  | .ok (some a) => a
  | _ => top
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- The member step `Sub`: declared by the head's structure, accessible, structure-normal. -/
def q : PropDef := (Algorithm.lookupPropDefAny? headOwner "Sub").getD { name := "", alg := top, isPublic := false }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry)) ∧
    ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry)) ∧
    (structureNormal sel.alg = true) ∧
    (Algorithm.lookupPropDefAny? headOwner "Sub" = some q) ∧
    (memberAccessible? ctx headOwner q = true) ∧
    (childOfInContext headOwner q.alg ctx = owner) ∧
    (structureNormal owner = true) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem head_probe : (resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry) :=
  facts.2.2.1

theorem lookup_entry : (lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.2.1

theorem sel_plain : structureNormal sel.alg = true :=
  facts.2.2.2.2.1

theorem head_settled : NavSettled (.resolve "Lib") ctx headOwner entry :=
  (navSettled_plain_name_of_probe "Lib" ctx top ctx.callStack.tail entry entry headOwner hcs head_probe
    (fun r h => by
      rw [lookup_entry] at h
      rw [← Except.ok.inj (Prod.mk.inj h).1]
      exact sel_plain)).2
theorem member_declared : Algorithm.lookupPropDefAny? headOwner "Sub" = some q :=
  facts.2.2.2.2.2.1

theorem member_accessible : memberAccessible? ctx headOwner q = true :=
  facts.2.2.2.2.2.2.1

theorem member_owner : childOfInContext headOwner q.alg ctx = owner :=
  facts.2.2.2.2.2.2.2.1

theorem member_plain : structureNormal owner = true :=
  facts.2.2.2.2.2.2.2.2.1

theorem probe_inert : probed = entry :=
  facts.2.2.2.2.2.2.2.2.2

/-- **`navSettled_member` over `navSettled_plain_name_of_probe` APPLIED**: the nested member path is
    settled, member by member. -/
theorem nav_settled : NavSettled target ctx owner probed := by
  rw [probe_inert]
  have h := navSettled_member (.resolve "Lib") "Sub" (.resolve "Sub") ctx headOwner q
    (childOfInContext headOwner q.alg ctx) entry head_settled member_declared member_accessible
    (structSettled_normal _ ctx entry (by rw [member_owner]; exact member_plain))
  rw [member_owner] at h
  exact h

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_settled 0 target N (.resolve N) args ctx [] entry probed alg? owner p probe_entry selected
    (fun x _ _ hx => by simp [target, headParam?] at hx) nav_settled production_entry

end NestedSpreadOne

namespace NestedSpreadFails
open KatLang.MemberStabilityInstances.NestedSpreadFails

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctx.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The receiver path's HEAD `Lib`: its own production probe. -/
def headOwner : Algorithm :=
  match ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry).1 with
  | .ok (some a) => a
  | _ => top
def sel : ResolvedProperty :=
  match ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry).1 with
  | .ok r => r
  | .error _ => dflt
/-- The member step `Sub`: declared by the head's structure, accessible, structure-normal. -/
def q : PropDef := (Algorithm.lookupPropDefAny? headOwner "Sub").getD { name := "", alg := top, isPublic := false }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctx.callStack = top :: ctx.callStack.tail) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    ((resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry)) ∧
    ((lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry)) ∧
    (structureNormal sel.alg = true) ∧
    (Algorithm.lookupPropDefAny? headOwner "Sub" = some q) ∧
    (memberAccessible? ctx headOwner q = true) ∧
    (childOfInContext headOwner q.alg ctx = owner) ∧
    (structureNormal owner = true) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctx.callStack = top :: ctx.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctx []).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B production_entry_done

theorem head_probe : (resolveDotReceiver? (.resolve "Lib") ctx).runState entry = (.ok (some headOwner), entry) :=
  facts.2.2.1

theorem lookup_entry : (lookupLexicalPropertyRaw top "Lib" ctx).runState entry = (.ok sel, entry) :=
  facts.2.2.2.1

theorem sel_plain : structureNormal sel.alg = true :=
  facts.2.2.2.2.1

theorem head_settled : NavSettled (.resolve "Lib") ctx headOwner entry :=
  (navSettled_plain_name_of_probe "Lib" ctx top ctx.callStack.tail entry entry headOwner hcs head_probe
    (fun r h => by
      rw [lookup_entry] at h
      rw [← Except.ok.inj (Prod.mk.inj h).1]
      exact sel_plain)).2
theorem member_declared : Algorithm.lookupPropDefAny? headOwner "Sub" = some q :=
  facts.2.2.2.2.2.1

theorem member_accessible : memberAccessible? ctx headOwner q = true :=
  facts.2.2.2.2.2.2.1

theorem member_owner : childOfInContext headOwner q.alg ctx = owner :=
  facts.2.2.2.2.2.2.2.1

theorem member_plain : structureNormal owner = true :=
  facts.2.2.2.2.2.2.2.2.1

theorem probe_inert : probed = entry :=
  facts.2.2.2.2.2.2.2.2.2

/-- **`navSettled_member` over `navSettled_plain_name_of_probe` APPLIED**: the nested member path is
    settled, member by member. -/
theorem nav_settled : NavSettled target ctx owner probed := by
  rw [probe_inert]
  have h := navSettled_member (.resolve "Lib") "Sub" (.resolve "Sub") ctx headOwner q
    (childOfInContext headOwner q.alg ctx) entry head_settled member_declared member_accessible
    (structSettled_normal _ ctx entry (by rw [member_owner]; exact member_plain))
  rw [member_owner] at h
  exact h

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_settled 0 target N (.resolve N) args ctx [] entry probed alg? owner p probe_entry selected
    (fun x _ _ hx => by simp [target, headParam?] at hx) nav_settled production_entry

end NestedSpreadFails

/-! ## Parameter receivers -/

namespace ParamEmpty
open KatLang.MemberStabilityInstances.ParamEmpty

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctxIn.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctxIn.callStack = top :: ctxIn.callStack.tail) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (structureNormal owner = true) ∧
    (capturedId? "b" ctxIn = none) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctxIn.callStack = top :: ctxIn.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctxIn envIn).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.param "b") ctxIn).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
/-- The projected CALLABLE is structure-normal (decided on the probe's actual result). -/
theorem owner_plain : structureNormal owner = true :=
  facts.2.2.1

/-- `b` is a parameter of the site itself: no captured activation is read. -/
theorem own_parameter : capturedId? "b" ctxIn = none :=
  facts.2.2.2

theorem activation_recorded : ∀ id, capturedId? "b" ctxIn = some id → id < entry.lexicalActivations.size := by
  intro id h
  rw [own_parameter] at h
  cases h

/-- **`navSettled_param_of_probe` APPLIED**: after the probe — the parameter's FIRST CALLABLE
    projection, which WROTE its memo (`probe_wrote`) — the navigation is settled over every
    navigation extension. -/
theorem nav_settled : NavSettled (.param "b") ctxIn owner probed :=
  navSettled_param_of_probe "b" ctxIn entry probed owner owner probe activation_recorded
    (structSettled_normal owner ctxIn probed owner_plain)

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification: the probe is the
    writing one. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_settled k (.param "b") N (.resolve N) args ctxIn envIn entry probed alg? owner p probe_entry
    selected
    (fun x o t hx hrun => by
      have hxb : "b" = x := by simpa [target, headParam?] using hx
      subst hxb
      rw [probe_param "b" ctxIn entry probed (some owner) probe] at hrun
      rw [← Option.some.inj (Except.ok.inj (Prod.mk.inj hrun).1)]
      exact owner_plain)
    nav_settled production_entry

end ParamEmpty

namespace ParamRefSpreadNone
open KatLang.MemberStabilityInstances.ParamRefSpreadNone

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctxIn.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctxIn.callStack = top :: ctxIn.callStack.tail) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (structureNormal owner = true) ∧
    (capturedId? "b" ctxIn = none) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctxIn.callStack = top :: ctxIn.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctxIn envIn).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.param "b") ctxIn).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
/-- The projected CALLABLE is structure-normal (decided on the probe's actual result). -/
theorem owner_plain : structureNormal owner = true :=
  facts.2.2.1

/-- `b` is a parameter of the site itself: no captured activation is read. -/
theorem own_parameter : capturedId? "b" ctxIn = none :=
  facts.2.2.2

theorem activation_recorded : ∀ id, capturedId? "b" ctxIn = some id → id < entry.lexicalActivations.size := by
  intro id h
  rw [own_parameter] at h
  cases h

/-- **`navSettled_param_of_probe` APPLIED**: after the probe — the parameter's FIRST CALLABLE
    projection, which WROTE its memo (`probe_wrote`) — the navigation is settled over every
    navigation extension. -/
theorem nav_settled : NavSettled (.param "b") ctxIn owner probed :=
  navSettled_param_of_probe "b" ctxIn entry probed owner owner probe activation_recorded
    (structSettled_normal owner ctxIn probed owner_plain)

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification: the probe is the
    writing one. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_settled k (.param "b") N (.resolve N) args ctxIn envIn entry probed alg? owner p probe_entry
    selected
    (fun x o t hx hrun => by
      have hxb : "b" = x := by simpa [target, headParam?] using hx
      subst hxb
      rw [probe_param "b" ctxIn entry probed (some owner) probe] at hrun
      rw [← Option.some.inj (Except.ok.inj (Prod.mk.inj hrun).1)]
      exact owner_plain)
    nav_settled production_entry

end ParamRefSpreadNone

namespace ParamSpreadFails
open KatLang.MemberStabilityInstances.ParamSpreadFails

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctxIn.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctxIn.callStack = top :: ctxIn.callStack.tail) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (structureNormal owner = true) ∧
    (capturedId? "b" ctxIn = none) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctxIn.callStack = top :: ctxIn.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctxIn envIn).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry :=
  complete_of_B production_entry_done

theorem probe : (resolveDotReceiver? (.param "b") ctxIn).runState entry = (.ok (some owner), probed) := by
  have h := probe_entry
  rw [probe_owner] at h
  exact h
/-- The projected CALLABLE is structure-normal (decided on the probe's actual result). -/
theorem owner_plain : structureNormal owner = true :=
  facts.2.2.1

/-- `b` is a parameter of the site itself: no captured activation is read. -/
theorem own_parameter : capturedId? "b" ctxIn = none :=
  facts.2.2.2

theorem activation_recorded : ∀ id, capturedId? "b" ctxIn = some id → id < entry.lexicalActivations.size := by
  intro id h
  rw [own_parameter] at h
  cases h

/-- **`navSettled_param_of_probe` APPLIED**: after the probe — the parameter's FIRST CALLABLE
    projection, which WROTE its memo (`probe_wrote`) — the navigation is settled over every
    navigation extension. -/
theorem nav_settled : NavSettled (.param "b") ctxIn owner probed :=
  navSettled_param_of_probe "b" ctxIn entry probed owner owner probe activation_recorded
    (structSettled_normal owner ctxIn probed owner_plain)

/-- **`member_bridge_of_settled` APPLIED** from the state before the classification: the probe is the
    writing one. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_settled k (.param "b") N (.resolve N) args ctxIn envIn entry probed alg? owner p probe_entry
    selected
    (fun x o t hx hrun => by
      have hxb : "b" = x := by simpa [target, headParam?] using hx
      subst hxb
      rw [probe_param "b" ctxIn entry probed (some owner) probe] at hrun
      rw [← Option.some.inj (Except.ok.inj (Prod.mk.inj hrun).1)]
      exact owner_plain)
    nav_settled production_entry

end ParamSpreadFails

/-! ## A parameter-rooted path: `b.Sub` -/

namespace ParamPathEmpty
open KatLang.MemberStabilityInstances.ParamPathEmpty

/-- The site: the head of the context the plan is written in. -/
def top : Algorithm := (ctxIn.callStack.head?).getD (alg [] [] [] [])
def dflt : ResolvedProperty := { owner := top, binding := { name := "", alg := top, isPublic := false }, alg := top }
/-- The path's HEAD: the parameter `b`; its own production probe is its FIRST CALLABLE projection. -/
def headOwner : Algorithm :=
  match ((resolveDotReceiver? (.param "b") ctxIn).runState entry).1 with
  | .ok (some a) => a
  | _ => top
def q : PropDef := (Algorithm.lookupPropDefAny? headOwner "Sub").getD { name := "", alg := top, isPublic := false }
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    (ctxIn.callStack = top :: ctxIn.callStack.tail) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    ((resolveDotReceiver? (.param "b") ctxIn).runState entry = (.ok (some headOwner), probed)) ∧
    (structureNormal headOwner = true) ∧
    (capturedId? "b" ctxIn = none) ∧
    (Algorithm.lookupPropDefAny? headOwner "Sub" = some q) ∧
    (memberAccessible? ctxIn headOwner q = true) ∧
    (childOfInContext headOwner q.alg ctxIn = owner) ∧
    (structureNormal owner = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

theorem hcs : ctxIn.callStack = top :: ctxIn.callStack.tail :=
  facts.1

theorem production_entry_done : completeB ((evalCounted src ctxIn envIn).runState entry).1 = true :=
  facts.2.1

/-- Production completes from the state BEFORE the plan's classification. -/
theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry :=
  complete_of_B production_entry_done

theorem head_probe : (resolveDotReceiver? (.param "b") ctxIn).runState entry = (.ok (some headOwner), probed) :=
  facts.2.2.1

theorem head_plain : structureNormal headOwner = true :=
  facts.2.2.2.1

theorem own_parameter : capturedId? "b" ctxIn = none :=
  facts.2.2.2.2.1

theorem activation_recorded : ∀ id, capturedId? "b" ctxIn = some id → id < entry.lexicalActivations.size := by
  intro id h
  rw [own_parameter] at h
  cases h
theorem head_settled : NavSettled (.param "b") ctxIn headOwner probed :=
  navSettled_param_of_probe "b" ctxIn entry probed headOwner headOwner head_probe activation_recorded
    (structSettled_normal headOwner ctxIn probed head_plain)
theorem member_declared : Algorithm.lookupPropDefAny? headOwner "Sub" = some q :=
  facts.2.2.2.2.2.1

theorem member_accessible : memberAccessible? ctxIn headOwner q = true :=
  facts.2.2.2.2.2.2.1

theorem member_owner : childOfInContext headOwner q.alg ctxIn = owner :=
  facts.2.2.2.2.2.2.2.1

theorem member_plain : structureNormal owner = true :=
  facts.2.2.2.2.2.2.2.2

/-- **A PARAMETER-ROOTED PATH**: `navSettled_member` over `navSettled_param_of_probe`. -/
theorem nav_settled : NavSettled target ctxIn owner probed := by
  have h := navSettled_member (.param "b") "Sub" (.resolve "Sub") ctxIn headOwner q
    (childOfInContext headOwner q.alg ctxIn) probed head_settled member_declared member_accessible
    (structSettled_normal _ ctxIn probed (by rw [member_owner]; exact member_plain))
  rw [member_owner] at h
  exact h

theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_settled k target N (.resolve N) args ctxIn envIn entry probed alg? owner p probe_entry selected
    (fun x o t hx hrun => by
      have hxb : "b" = x := by simpa [target, headParam?] using hx
      subst hxb
      rw [probe_param "b" ctxIn entry probed (some headOwner) head_probe] at hrun
      rw [← Option.some.inj (Except.ok.inj (Prod.mk.inj hrun).1)]
      exact head_plain)
    nav_settled production_entry

end ParamPathEmpty

end KatLang.MemberSettledInstances
