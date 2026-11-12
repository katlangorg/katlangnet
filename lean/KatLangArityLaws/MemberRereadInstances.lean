import KatLangArityLaws.StoredCallableNormal
import KatLangArityLaws.MemberBridgeSourceAliases
import KatLangArityLaws.MemberBridgeSourcePaths
import KatLangArityLaws.MemberBridgeSourceParameters

/-!
# The member bridge FROM THE PROBE, applied to source programs (E-18 step 1, M1)

`NavigationSettled.member_bridge_of_probe` is the member bridge for every bundle with the production
probe as its only navigation premise. This module APPLIES it — one theorem, every receiver class —
from the state BEFORE the plan's classification (`entry`, the state the VALUE shell runs the plan
from):

| namespace | receiver | what the probe's navigation does |
| --- | --- | --- |
| `RuntimeEmpty`, `RuntimeSpreadNone`, `RuntimeSpreadOne`, `RuntimeSpreadFails` | `RTC = Capture(FM(0)).Algorithm` | RUNTIME-TARGET ALIAS: route decision, binding cell recorded, its CALLABLE projected (a flight that evaluates the receiver) |
| `RuntimeNamedOrdinary`, `RuntimeNamedSpreadOne`, `RuntimeNamedSpreadFails` | `RTA = RC.Algorithm` | runtime-target alias over a STATIC receiver `RC` |
| `PathRefEmpty`, `PathRefSpreadNone`, `PathRefSpreadOne`, `PathRefSpreadFails`, `PathRefOrdinary` | `ALS = Lib.Sub` | transparent reference whose row is a MEMBER PATH |
| `RefEmpty`, `RefSpreadNone`, `RefSpreadOne`, `RefSpreadFails`, `RefOrdinary` | `AB = Box` | transparent reference, name row |
| `OpenEmpty`, `OpenSpreadNone` | `OBox`, through `open OLib` | opened name |
| `NestedEmpty`, `NestedSpreadOne`, `NestedSpreadFails` | `Lib.Sub` | nested member path (`probe_member`) |
| `ParamEmpty`, `ParamRefSpreadNone`, `ParamSpreadFails` | `b` | parameter: first projection of its cell |
| `ParamPathEmpty` | `b.Sub` | PARAMETER-ROOTED member path |

Bundles: empty, a spread forming no cell, a spread forming one cell, a FAILING spread, an ordinary
list.

Per instance, the premises of `member_bridge_of_probe` and where each is proved:

* `nav_run` — `NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed)`: the
  navigation core completes the probe from `entry` (`navFuel` at an explicit fuel, by `cbv`); it is
  the production probe (`NavRuns.production`, `probe_entry`);
* `no_mint` — the probe advanced no runtime-declaration identity;
* `select` — production's own dot decision selects the DECLARED member;
* `head_normal` (parameter heads) — the CALLABLE the parameter's cell projects is structure-normal:
  DERIVED by `StoredCallableNormal.param_head_normal` from two facts of the reached heap (the
  parameter's cell awaits its first projection, and was supplied with a written name);
* `production_entry` — production completes from `entry`.

`nav_settled` is the DERIVED `NavSettled` (over every navigation extension of the probe's exit) and
`bridge_of_probe` the theorem applied. Nothing here assumes settledness, an alias-key fact or an
activation fact.

The namespaces of `MemberBridgeSource*` are re-used with their definitions and reachability chain
(`captured`, `program_run`, `plan_cell`, `flight`, `demand_passes`); the namespaces new here
(`RuntimeSpreadNone`, `RuntimeSpreadFails`, `RuntimeNamedSpreadOne`, `RuntimeNamedSpreadFails`, `PathRefSpreadNone`,
`PathRefSpreadOne`, `PathRefSpreadFails`, `PathRefOrdinary`) carry their own.

NOT here, and why: the EMPTY bundle over the named runtime-target alias (`RTA.Pair()`): the receiver
`RC` is a cached property, and the zero-supply call's CACHE-PUB-1 publication compares its
`reprStr`-built cache key with `RC`'s — a comparison of two printed keys of different owners, which
no Lean proof decides (`Std.Format.pretty` is opaque). `RTC.Pair()` (`RuntimeEmpty`) is the empty
bundle of the class; `RTA` has the ordinary, spread-first and failing-spread bundles.

NOT here: a reference CHAIN of two steps (`AB2 = AB`). The theorem covers it without any key
premise, but the instance's run facts cannot be proved by any Lean proof: the chase compares the
second step's `reprStr`-built key with the first's, and `Std.Format.pretty` is opaque
(`NavigationRereadGuards` checks that run by execution instead).

GENERATED text (`artifacts/validation/e18-step1-m1-20261112/scratch/gen_reread.py`).
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.NavigationReread KatLang.NavigationSettled KatLang.StoredCallableNormal
open KatLang.MemberStabilityInstances
open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
open KatLang.PlanAlgorithmBridgeInstances.Source (demand_passes_flight)

namespace KatLang.MemberRereadInstances

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## `RuntimeEmpty`: `RTC.Pair()` — a RUNTIME-TARGET alias, empty bundle -/

namespace RuntimeEmpty
open KatLang.MemberStabilityInstances.RuntimeEmpty

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeEmpty

/-! ## `RuntimeSpreadOne`: `RTC.G([5]*)` — a runtime-target alias, a spread forming one cell -/

namespace RuntimeSpreadOne
open KatLang.MemberStabilityInstances.RuntimeSpreadOne

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeSpreadOne

/-! ## `RuntimeNamedOrdinary`: `RTA.G(2)` — a runtime-target alias over the STATIC receiver `RC`, ordinary bundle -/

namespace RuntimeNamedOrdinary
open KatLang.MemberStabilityInstances.RuntimeNamedOrdinary

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeNamedOrdinary

/-! ## `PathRefEmpty`: `ALS.K()` — a transparent reference to a MEMBER PATH, empty bundle -/

namespace PathRefEmpty
open KatLang.MemberStabilityInstances.PathRefEmpty

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end PathRefEmpty

/-! ## `RefEmpty`: `AB.V()` — a transparent reference, empty bundle -/

namespace RefEmpty
open KatLang.MemberStabilityInstances.RefEmpty

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RefEmpty

/-! ## `RefSpreadNone`: `AB.V(()*)` — a transparent reference, a spread forming no cell -/

namespace RefSpreadNone
open KatLang.MemberStabilityInstances.RefSpreadNone

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RefSpreadNone

/-! ## `RefSpreadOne`: `AB.G([5]*)` — a transparent reference, a spread forming one cell -/

namespace RefSpreadOne
open KatLang.MemberStabilityInstances.RefSpreadOne

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RefSpreadOne

/-! ## `RefSpreadFails`: `AB.G((1 / 0)*)` — a transparent reference, a FAILING spread -/

namespace RefSpreadFails
open KatLang.MemberStabilityInstances.RefSpreadFails

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RefSpreadFails

/-! ## `RefOrdinary`: `AB.G(2)` — a transparent reference, ordinary bundle -/

namespace RefOrdinary
open KatLang.MemberStabilityInstances.RefOrdinary

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RefOrdinary

/-! ## `OpenEmpty`: `OBox.V()` — an OPENED name, empty bundle -/

namespace OpenEmpty
open KatLang.MemberStabilityInstances.OpenEmpty

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end OpenEmpty

/-! ## `OpenSpreadNone`: `OBox.V(()*)` — an opened name, a spread forming no cell -/

namespace OpenSpreadNone
open KatLang.MemberStabilityInstances.OpenSpreadNone

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end OpenSpreadNone

/-! ## `NestedEmpty`: `Lib.Sub.K()` — a NESTED member path, empty bundle -/

namespace NestedEmpty
open KatLang.MemberStabilityInstances.NestedEmpty

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end NestedEmpty

/-! ## `NestedSpreadOne`: `Lib.Sub.H([5]*)` — a nested member path, a spread forming one cell -/

namespace NestedSpreadOne
open KatLang.MemberStabilityInstances.NestedSpreadOne

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end NestedSpreadOne

/-! ## `NestedSpreadFails`: `Lib.Sub.H((1 / 0)*)` — a nested member path, a FAILING spread -/

namespace NestedSpreadFails
open KatLang.MemberStabilityInstances.NestedSpreadFails

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end NestedSpreadFails

/-! ## `ParamEmpty`: `b.V()` — a PARAMETER receiver, empty bundle -/

namespace ParamEmpty
open KatLang.MemberStabilityInstances.ParamEmpty

/-- The cell the head parameter `b` holds at `entry`. -/
def cellB : Nat := (parameterAddressIn entry.lexicalActivations "b" ctxIn).getD 0

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB) ∧
    (staticUnprojected entry cellB = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry` — the
    parameter's captured activation is recorded (`NavigationReread.anchored`). -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry := complete_of_B rfacts.2.2.1

theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The parameter's cell at `entry`, and its state: awaiting its FIRST projection, supplied with a
    written name (`StoredCallableNormal.staticUnprojected`). -/
theorem head_cell : parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB := rfacts.2.2.2.1

theorem head_unprojected : staticUnprojected entry cellB = true := rfacts.2.2.2.2

/-- **`param_head_normal` APPLIED**: the CALLABLE the head parameter's cell projects is
    structure-normal — DERIVED from the cell's own suspension, not assumed. -/
theorem head_normal : ∀ x o v, headParam? target = some x →
    (projectParameterCallable x ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true := by
  intro x o v hx hrun
  have hb : headParam? target = some "b" := rfl
  rw [hb] at hx
  cases hx
  exact param_head_normal "b" ctxIn entry cellB head_cell head_unprojected o v hrun

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctxIn owner probed :=
  navSettled_of_navRuns target ctxIn entry probed owner rfl nav_run no_mint head_normal

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_probe k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint select
    head_normal production_entry

end ParamEmpty

/-! ## `ParamRefSpreadNone`: `b.V(()*)` — a parameter bound to a transparent reference, a spread forming no cell -/

namespace ParamRefSpreadNone
open KatLang.MemberStabilityInstances.ParamRefSpreadNone

/-- The cell the head parameter `b` holds at `entry`. -/
def cellB : Nat := (parameterAddressIn entry.lexicalActivations "b" ctxIn).getD 0

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB) ∧
    (staticUnprojected entry cellB = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry` — the
    parameter's captured activation is recorded (`NavigationReread.anchored`). -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry := complete_of_B rfacts.2.2.1

theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The parameter's cell at `entry`, and its state: awaiting its FIRST projection, supplied with a
    written name (`StoredCallableNormal.staticUnprojected`). -/
theorem head_cell : parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB := rfacts.2.2.2.1

theorem head_unprojected : staticUnprojected entry cellB = true := rfacts.2.2.2.2

/-- **`param_head_normal` APPLIED**: the CALLABLE the head parameter's cell projects is
    structure-normal — DERIVED from the cell's own suspension, not assumed. -/
theorem head_normal : ∀ x o v, headParam? target = some x →
    (projectParameterCallable x ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true := by
  intro x o v hx hrun
  have hb : headParam? target = some "b" := rfl
  rw [hb] at hx
  cases hx
  exact param_head_normal "b" ctxIn entry cellB head_cell head_unprojected o v hrun

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctxIn owner probed :=
  navSettled_of_navRuns target ctxIn entry probed owner rfl nav_run no_mint head_normal

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_probe k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint select
    head_normal production_entry

end ParamRefSpreadNone

/-! ## `ParamSpreadFails`: `b.G((1 / 0)*)` — a parameter receiver, a FAILING spread -/

namespace ParamSpreadFails
open KatLang.MemberStabilityInstances.ParamSpreadFails

/-- The cell the head parameter `b` holds at `entry`. -/
def cellB : Nat := (parameterAddressIn entry.lexicalActivations "b" ctxIn).getD 0

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB) ∧
    (staticUnprojected entry cellB = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry` — the
    parameter's captured activation is recorded (`NavigationReread.anchored`). -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry := complete_of_B rfacts.2.2.1

theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The parameter's cell at `entry`, and its state: awaiting its FIRST projection, supplied with a
    written name (`StoredCallableNormal.staticUnprojected`). -/
theorem head_cell : parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB := rfacts.2.2.2.1

theorem head_unprojected : staticUnprojected entry cellB = true := rfacts.2.2.2.2

/-- **`param_head_normal` APPLIED**: the CALLABLE the head parameter's cell projects is
    structure-normal — DERIVED from the cell's own suspension, not assumed. -/
theorem head_normal : ∀ x o v, headParam? target = some x →
    (projectParameterCallable x ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true := by
  intro x o v hx hrun
  have hb : headParam? target = some "b" := rfl
  rw [hb] at hx
  cases hx
  exact param_head_normal "b" ctxIn entry cellB head_cell head_unprojected o v hrun

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctxIn owner probed :=
  navSettled_of_navRuns target ctxIn entry probed owner rfl nav_run no_mint head_normal

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_probe k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint select
    head_normal production_entry

end ParamSpreadFails

/-! ## `ParamPathEmpty`: `b.Sub.K()` — a PARAMETER-ROOTED member path, empty bundle -/

namespace ParamPathEmpty
open KatLang.MemberStabilityInstances.ParamPathEmpty

/-- The cell the head parameter `b` holds at `entry`. -/
def cellB : Nat := (parameterAddressIn entry.lexicalActivations "b" ctxIn).getD 0

theorem rfacts :
    ((navFuel 64 (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
    (parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB) ∧
    (staticUnprojected entry cellB = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The probe's own run over recorded data: the navigation core completes it from `entry` — the
    parameter's captured activation is recorded (`NavigationReread.anchored`). -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
  have h := rfacts.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry := complete_of_B rfacts.2.2.1

theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The parameter's cell at `entry`, and its state: awaiting its FIRST projection, supplied with a
    written name (`StoredCallableNormal.staticUnprojected`). -/
theorem head_cell : parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB := rfacts.2.2.2.1

theorem head_unprojected : staticUnprojected entry cellB = true := rfacts.2.2.2.2

/-- **`param_head_normal` APPLIED**: the CALLABLE the head parameter's cell projects is
    structure-normal — DERIVED from the cell's own suspension, not assumed. -/
theorem head_normal : ∀ x o v, headParam? target = some x →
    (projectParameterCallable x ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true := by
  intro x o v hx hrun
  have hb : headParam? target = some "b" := rfl
  rw [hb] at hx
  cases hx
  exact param_head_normal "b" ctxIn entry cellB head_cell head_unprojected o v hrun

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctxIn owner probed :=
  navSettled_of_navRuns target ctxIn entry probed owner rfl nav_run no_mint head_normal

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute k shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
  member_bridge_of_probe k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint select
    head_normal production_entry

end ParamPathEmpty

/-! ## `RuntimeSpreadNone`: `RTC.Pair(()*)` — a RUNTIME-TARGET alias, a spread forming no cell -/

namespace RuntimeSpreadNone

/-- `RTC = Capture(FM(0)).Algorithm`: a runtime-target alias. -/
def target : Expr := .resolve "RTC"
def N : Ident := "Pair"
def args : OutputBundle := [.sequenceSpread (.emptySequence 0)]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTC.Pair(()*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTC.Pair(()*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.sequenceValue [.atom 7, .atom 8], 1)) ∧
    (probed.aliasCells.length = entry.aliasCells.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The call's value: the member `Pair` of the projected callable. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.sequenceValue [.atom 7, .atom 8], 1) := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The first navigation WRITES: the alias's binding cell is recorded. -/
theorem probe_effect : probed.aliasCells.length = entry.aliasCells.length + 1 := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeSpreadNone

/-! ## `RuntimeSpreadFails`: `RTC.G((1 / 0)*)` — a RUNTIME-TARGET alias, a FAILING spread -/

namespace RuntimeSpreadFails

/-- `RTC = Capture(FM(0)).Algorithm`: a runtime-target alias. -/
def target : Expr := .resolve "RTC"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.binary .div (.num 1) (.num 0))]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTC.G((1 / 0)*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTC.G((1 / 0)*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none) ∧
    (probed.aliasCells.length = entry.aliasCells.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The supply formation FAILS (the spread divides by zero): both sides fail alike. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The first navigation WRITES: the alias's binding cell is recorded. -/
theorem probe_effect : probed.aliasCells.length = entry.aliasCells.length + 1 := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeSpreadFails

/-! ## `RuntimeNamedSpreadOne`: `RTA.G([5]*)` — a runtime-target alias over the STATIC receiver `RC`, a spread forming one cell -/

namespace RuntimeNamedSpreadOne

/-- `RTA = RC.Algorithm`, `RC = Capture(FM(0))`: a runtime-target alias over a static receiver. -/
def target : Expr := .resolve "RTA"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.listLiteral [.num 5])]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTA.G([5]*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTA.G([5]*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 5, 1)) ∧
    (probed.aliasCells.length = entry.aliasCells.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The call's value: `G(5) = 5`. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 5, 1) := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The first navigation WRITES: the alias's binding cell is recorded. -/
theorem probe_effect : probed.aliasCells.length = entry.aliasCells.length + 1 := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeNamedSpreadOne

/-! ## `RuntimeNamedSpreadFails`: `RTA.G((1 / 0)*)` — a runtime-target alias over the STATIC receiver `RC`, a FAILING spread -/

namespace RuntimeNamedSpreadFails

/-- `RTA = RC.Algorithm`, `RC = Capture(FM(0))`: a runtime-target alias over a static receiver. -/
def target : Expr := .resolve "RTA"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.binary .div (.num 1) (.num 0))]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTA.G((1 / 0)*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTA.G((1 / 0)*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none) ∧
    (probed.aliasCells.length = entry.aliasCells.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The supply formation FAILS (the spread divides by zero): both sides fail alike. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The first navigation WRITES: the alias's binding cell is recorded. -/
theorem probe_effect : probed.aliasCells.length = entry.aliasCells.length + 1 := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end RuntimeNamedSpreadFails

/-! ## `PathRefSpreadNone`: `ALS.K(()*)` — a transparent reference to a MEMBER PATH, a spread forming no cell -/

namespace PathRefSpreadNone

/-- `ALS = Lib.Sub`: the reference's own row is a member path. -/
def target : Expr := .resolve "ALS"
def N : Ident := "K"
def args : OutputBundle := [.sequenceSpread (.emptySequence 0)]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `ALS.K(()*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(ALS.K(()*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 3, 1)) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The call's value. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 3, 1) := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A static reference: the probe writes nothing. -/
theorem probe_effect : probed = entry := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end PathRefSpreadNone

/-! ## `PathRefSpreadOne`: `ALS.H([5]*)` — a transparent reference to a member path, a spread forming one cell -/

namespace PathRefSpreadOne

/-- `ALS = Lib.Sub`: the reference's own row is a member path. -/
def target : Expr := .resolve "ALS"
def N : Ident := "H"
def args : OutputBundle := [.sequenceSpread (.listLiteral [.num 5])]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `ALS.H([5]*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(ALS.H([5]*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 6, 1)) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The call's value: `H(5) = 6`. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 6, 1) := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A static reference: the probe writes nothing. -/
theorem probe_effect : probed = entry := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end PathRefSpreadOne

/-! ## `PathRefSpreadFails`: `ALS.H((1 / 0)*)` — a transparent reference to a member path, a FAILING spread -/

namespace PathRefSpreadFails

/-- `ALS = Lib.Sub`: the reference's own row is a member path. -/
def target : Expr := .resolve "ALS"
def N : Ident := "H"
def args : OutputBundle := [.sequenceSpread (.binary .div (.num 1) (.num 0))]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `ALS.H((1 / 0)*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(ALS.H((1 / 0)*))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The supply formation FAILS (the spread divides by zero): both sides fail alike. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1.toOption = none := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A static reference: the probe writes nothing. -/
theorem probe_effect : probed = entry := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end PathRefSpreadFails

/-! ## `PathRefOrdinary`: `ALS.H(2)` — a transparent reference to a member path, ordinary bundle -/

namespace PathRefOrdinary

/-- `ALS = Lib.Sub`: the reference's own row is a member path. -/
def target : Expr := .resolve "ALS"
def N : Ident := "H"
def args : OutputBundle := [.num 2]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `ALS.H(2)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(ALS.H(2))`. -/
def row : Expr := MemberStabilityInstances.capture src
def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- The plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed

/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
theorem rfacts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((navFuel 64 (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
    (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
    (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 3, 1)) ∧
    (probed = entry) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

theorem program_run :
    (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) := rfacts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

/-- The production probe from `entry`. -/
theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  rfacts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
  have h := rfacts.2.2.2.2.2.2.2.2.2.1
  rw [probe_owner] at h
  exact ⟨64, h, nofun⟩

theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
  rfacts.2.2.2.2.2.2.2.2.2.2.1

theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
  complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
  have h := selected
  rw [probe_owner] at h
  exact h

/-- The call's value: `H(2) = 3`. -/
theorem outcome : ((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1 = .ok (.atom 3, 1) := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A static reference: the probe writes nothing. -/
theorem probe_effect : probed = entry := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
    navigation extension — derived from the probe. -/
theorem nav_settled : NavSettled target ctx owner probed :=
  navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)

/-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
theorem bridge_of_probe :
    (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
      (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
  member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
    (fun _ _ _ hx => nomatch hx) production_entry

end PathRefOrdinary

end KatLang.MemberRereadInstances
