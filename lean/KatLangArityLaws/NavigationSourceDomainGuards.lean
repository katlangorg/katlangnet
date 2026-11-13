import KatLangArityLaws.NavigationSourceDomain
import KatLangArityLaws.NavigationContractGuards

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.NavigationReread KatLang.NavigationSettled KatLang.NavigationAdmission
open KatLang.NavigationContract KatLang.NavigationSourceDomain

/-!
# The static input domain: examples, and what it does NOT give (ledger E-18, step 1, B2 preparation)

`NavigationSourceDomain` states the static premises of navigation admissibility as predicates of a
program expression. This module checks them on trees, and bounds what they can be used for.

## 1. Host-built trees outside the domain (`HostBuilt`, `ExposureFragment`, `OpenedFragment`)

* `NavigationContractGuards.MisExposed` — a parameter-row member marked `exported` — is NOT
  exposure-complete, in either mode; the same tree with the member marked local-only is in the
  source domain.
* A tree with a `.param` no level binds is not `paramsBound`.
* `ExposureFragment` / `OpenedFragment` — a member whose only dependency is a member it selects by a
  static dotted path (`Lib.Q`) or through an `open` (`open Lib` / `Q`), with that dependency's
  requirement removed from its metadata: the direct-lexical fragment (`SourceLike`) accepts the
  corrupted tree, the full closure (`SourceDomain`) refuses it and accepts the corrected one.

## 2. Source trees inside the domain (`OutsideContainer`, `EscapedContainer`, `FrontEnd`)

The two reached-state fixtures, five public-entry guards and the four `FrontEnd` programs below are
the C# front end's own elaborated trees of the quoted sources, encoded by `LeanAstEncoder`.
Maintained C# fidelity tests check those eleven encodings (`NavigationSourceDomainWitnessTests`).
Each is in `SourceDomain`; the `ExposureFragment` and `OpenedFragment` examples are intentionally
host-corrupted.

## 3. The two former counterexamples, under the anchoring of a container's chain

The proposed invariant of `NavigationContract` asks every chased alias to be `ParamRowOwned`: a
parameter-row alias sits under its owner's ACTIVATION. The B2 preparation (2026-11-12) found two
source programs that broke it; the owner decision of 2026-11-13 (E-18 anchoring, `anchorChain`
under `scopeInContext`) changed the language so that both now keep it.

`OutsideContainer` — a container that declares a capturing member, navigated OUTSIDE its owner's
activation and used INSIDE one:

    F(y) = {
      p = {
        Q = y
        1
      }
      Capture(Use(y.Q))
    }
    F(F.p)

`p`'s own value requires nothing, so the front end marks `p` exported and `F.p` is navigated from the
root: `p` is wired under the UNACTIVATED level of `F`. Inside `F`'s activation, `y.Q` selects the
member `Q` of that container. Before the decision, `childOfInContext` wired `Q` under the container's
own chain, the member was not `ParamRowOwned`, and its parameter was read from the READING context's
tier — a callee's same-named binding inside that callee (the `shadowedRead` guard returned 99). Now
the container's chain is read in the site's context: its static level of `F` is the activation the
site is inside, so the member production reaches IS owned (`OutsideContainer.reached_member_is_owned`)
and the navigation core admits its chase (`OutsideContainer.admitted`).

`EscapedContainer` — the same container read in a body of `F` invoked outside `F`'s evaluation
through a call reference (`R.Algorithm(F.p)`), where the reading tier binds `z` only:

    F(y) = {
      p = {
        Q = y
        1
      }
      Inner(z) = Capture(Use(z.Q))
      K(meta r) = r
      K(Inner(0))
    }
    R = F(5)
    R.Algorithm(F.p)

Before the decision the member's structure chase allocated a cell on each of its first two
consecutive chases and was no navigation-core run, and the read was `unknownName`. Now the member is
wired under the activation of `F` the reference captured: it is owned, its chase completes without
allocating or minting, and a second chase from the exit state answers the same and changes nothing
(`EscapedContainer.source_navigation_is_reread`); the read is that call's `y`, 5.

Both programs still fail `exposureDeep` (a static predicate; the decision changed no metadata).
Whether `SourceLike` gives the proposed invariant IN GENERAL is not proved here. C# agrees with the
Lean results below on every program (`NavigationSourceDomainWitnessTests`); nothing here is a
theorem about C#.

## Scope of the reached states

As in `NavigationContractGuards.MisExposed`, the theorem-level contexts are the program root alone,
without the prelude level: a wiring decision under a scope that is not on the site chain compares
the prelude's PRINTED scope (`sameDeclaringScope`'s `reprStr` arm), which no Lean proof decides.
The `#guard`s at the end run the same programs through `runResult`, prelude included.
-/

namespace KatLang.NavigationSourceDomainGuards

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## 1. Host-built trees outside the domain -/

namespace HostBuilt

open KatLang.NavigationContractGuards (MisExposed.program MisExposed.localOnly)

/-- The exported parameter-row member of `MisExposed` is not exposure-complete … -/
theorem mis_exposed_is_incomplete : exposureComplete (MisExposed.program .exported) = false := by cbv

/-- … its parameter is bound, so the tree fails the exposure premise alone … -/
theorem mis_exposed_is_bound : paramsBound (MisExposed.program .exported) = true := by cbv

theorem mis_exposed_is_not_sourceLike : ¬ SourceLike (MisExposed.program .exported) :=
  fun h => by have := h.exposed; rw [mis_exposed_is_incomplete] at this; cases this

/-- … and the same tree with the member marked local-only is in the domain, deep reading included. -/
theorem well_exposed_is_sourceLike : SourceLike (MisExposed.program MisExposed.localOnly) :=
  ⟨by cbv, by cbv⟩

theorem well_exposed_is_deep : DeepSourceLike (MisExposed.program MisExposed.localOnly) :=
  ⟨by cbv, by cbv⟩

/-- The full closure refuses the exported parameter-row member too … -/
theorem mis_exposed_is_not_full : exposureFull (MisExposed.program .exported) = false := by cbv

theorem mis_exposed_is_not_sourceDomain : ¬ SourceDomain (MisExposed.program .exported) :=
  fun h => by have := h.exposed; rw [mis_exposed_is_not_full] at this; cases this

/-- … and accepts the local-only one. -/
theorem well_exposed_is_sourceDomain : SourceDomain (MisExposed.program MisExposed.localOnly) :=
  ⟨by cbv, by cbv⟩

/-- `F = { A = y ⏎ 0 }` with no level binding `y`: a `.param` without an owner. -/
def unbound : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg [] []
    [privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))] [.num 0])] [.num 0])

theorem unbound_is_not_bound : paramsBound unbound = false := by cbv

theorem unbound_is_not_sourceLike : ¬ SourceLike unbound :=
  fun h => by have := h.bound; rw [unbound_is_not_bound] at this; cases this

theorem unbound_is_not_sourceDomain : ¬ SourceDomain unbound :=
  fun h => by have := h.bound; rw [unbound_is_not_bound] at this; cases this

end HostBuilt

/-! ## A dotted dependency: the fragment cannot see it, the full closure does

The direct-lexical closure is a NECESSARY FRAGMENT, not full exposure completeness. `Lib.Q`
requires `F`'s `y`, although `Lib`'s own output does not. The fragment does not select `Q` through
`Lib`, so it accepts a host-corrupted exported `A = Lib.Q + 0` (the B2 preparation review's finding
F1). The full closure selects `Q` by the static path and refuses the corrupted tree.
-/

namespace ExposureFragment

def program (exposure : PropExposure) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [privateProp "Lib" (alg [] []
      [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with
          requiredOwnerDepths := some [("y", some 1)] }] [.num 1]),
     { (privateLocalProp "A" exposure (alg [] [] []
         [.binary .add (.dotCall (.resolve "Lib") "Q" none) (.num 0)])) with
         requiredOwnerDepths := if exposure.isExported then none else some [("y", some 0)] }]
    [.param "y"])] [.num 0])

/-- The fragment accepts the missing transitive requirement through `Lib.Q`. -/
theorem misses_dotted_requirement : SourceLike (program .exported) := ⟨by cbv, by cbv⟩

/-- Correcting that requirement also satisfies the fragment: it cannot distinguish the two trees. -/
theorem admits_corrected_requirement : SourceLike (program (.localCapturedAncestorParams ["y"])) :=
  ⟨by cbv, by cbv⟩

/-- **The full closure refuses the corrupted tree** … -/
theorem full_refuses_missing_dotted_requirement : exposureFull (program .exported) = false := by cbv

theorem corrupted_is_not_sourceDomain : ¬ SourceDomain (program .exported) :=
  fun h => by have := h.exposed; rw [full_refuses_missing_dotted_requirement] at this; cases this

/-- … and accepts the corrected one. -/
theorem corrected_is_sourceDomain : SourceDomain (program (.localCapturedAncestorParams ["y"])) :=
  ⟨by cbv, by cbv⟩

end ExposureFragment

/-! ## An opened dependency

`A = { open Lib ⏎ Q + 0 }` reads `Lib.Q` through its own `open`: no level declares `Q`, so the
lexical lookup falls to the opens (`lookupOpenPropertiesInChain`), and `A` requires what `Q`
declares. The fragment counts nothing for an opened name.
-/

namespace OpenedFragment

def program (exposure : PropExposure) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [privateProp "Lib" (alg [] []
      [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with
          requiredOwnerDepths := some [("y", some 1)] }] [.num 1]),
     { (privateLocalProp "A" exposure (alg [] [.resolve "Lib"] []
         [.binary .add (.resolve "Q") (.num 0)])) with
         requiredOwnerDepths := if exposure.isExported then none else some [("y", some 0)] }]
    [.param "y"])] [.num 0])

theorem fragment_misses_opened_requirement : SourceLike (program .exported) := ⟨by cbv, by cbv⟩

theorem full_refuses_missing_opened_requirement : exposureFull (program .exported) = false := by cbv

theorem corrected_is_sourceDomain : SourceDomain (program (.localCapturedAncestorParams ["y"])) :=
  ⟨by cbv, by cbv⟩

end OpenedFragment

/-! ## Source trees with a selected dependency (`FrontEnd`)

The corpora hold no program whose member depends on another only through a static dotted path, and
two whose member depends on one only through an `open` (`case_ownership_open_*`). These four
programs are the C# front end's own trees (`NavigationSourceDomainWitnessTests` checks the
encodings): `A` reads `F`'s `y` only through a selection, the front end marks `A` local-only with
`y`, each is in `SourceDomain`, each runs to `5` (C# agrees), and the same tree with `A`
host-corrupted to exported passes the fragment and fails the full closure.
-/

namespace FrontEnd

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        F(y) = {
          Lib = {
            public Q = y
            1
          }
          A = Lib.Q + 0
          A
        }
        F(5)

    `A` reads `F`'s `y` only through a static dotted path; the front end marks it local-only. -/
def dotted : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "Lib") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem dotted_sourceDomain : SourceDomain dotted := ⟨by cbv, by cbv⟩

/-- The same tree with `A` host-corrupted to exported: the fragment accepts it, the full closure does not. -/
def dottedExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Lib") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem dotted_exported_refused : exposureComplete dottedExported = true ∧ exposureFull dottedExported = false := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

#guard (match runResult dotted with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        F(y) = {
          Lib = {
            public Sub = {
              public Q = y
              1
            }
            1
          }
          A = Lib.Sub.Q + 0
          A
        }
        F(5)

    `A` reads `F`'s `y` only through a two-step static dotted path; the front end marks it local-only. -/
def nested : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem nested_sourceDomain : SourceDomain nested := ⟨by cbv, by cbv⟩

/-- The same tree with `A` host-corrupted to exported: the fragment accepts it, the full closure does not. -/
def nestedExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem nested_exported_refused : exposureComplete nestedExported = true ∧ exposureFull nestedExported = false := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

#guard (match runResult nested with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        F(y) = {
          Lib = {
            public Sub = {
              public Q = y
              1
            }
            1
          }
          L = Lib.Sub
          A = L.Q + 0
          A
        }
        F(5)

    `A` reads `F`'s `y` only through a dotted path through a transparent reference (`L = Lib.Sub`); the front end marks it local-only. -/
def reference : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "L" (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none))), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem reference_sourceDomain : SourceDomain reference := ⟨by cbv, by cbv⟩

/-- The same tree with `A` host-corrupted to exported: the fragment accepts it, the full closure does not. -/
def referenceExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "L" (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none))), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem reference_exported_refused : exposureComplete referenceExported = true ∧ exposureFull referenceExported = false := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

#guard (match runResult reference with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        F(y) = {
          Lib = {
            public Q = y
            1
          }
          A = {
            open Lib
            Q + 0
          }
          A
        }
        F(5)

    `A` reads `F`'s `y` only through a name its own `open` provides; the front end marks it local-only. -/
def opened : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem opened_sourceDomain : SourceDomain opened := ⟨by cbv, by cbv⟩

/-- The same tree with `A` host-corrupted to exported: the fragment accepts it, the full closure does not. -/
def openedExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem opened_exported_refused : exposureComplete openedExported = true ∧ exposureFull openedExported = false := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

#guard (match runResult opened with | .ok (.atom 5) => true | _ => false)

end FrontEnd

/-! ## Shared definitions of the reached-state fixtures -/

/-- The root with the declaration identities `runResultM` assigns. -/
def rootOf (program : Expr) : Algorithm :=
  match (identifyPropertyExpr program).run' 0 with
  | .algorithmExpr a => a
  | _ => preludeAlg

/-- A decision procedure for `ParamRowOwned`. -/
def paramRowOwnedB : Algorithm → Bool
  | .alias parent _ _ (.param y) _ _ =>
      ((parent.bind fun p => requiredParameterOwner? p y).bind ScopeCtx.activation).isSome
  | _ => true

/-- What the decision procedure accepts is `ParamRowOwned`. -/
theorem paramRowOwned_of_B {a : Algorithm} (h : paramRowOwnedB a = true) : ParamRowOwned a := by
  cases a with
  | «alias» parent opens props target id reference =>
    cases target with
    | param y =>
      cases parent with
      | none => simp [paramRowOwnedB] at h
      | some p =>
        cases hown : requiredParameterOwner? p y with
        | none => simp [paramRowOwnedB, hown] at h
        | some owner =>
          cases hid : owner.activation with
          | none => simp [paramRowOwnedB, hown, hid] at h
          | some i => exact ⟨p, owner, i, rfl, hown, hid⟩
    | _ => trivial
  | _ => trivial

/-! ## 2–3. `OutsideContainer`: a capturing member of a container navigated outside its owner -/

namespace OutsideContainer

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        Capture(meta op) = op
        Use(f) = 1
        F(y) = {
          p = {
            Q = y
            1
          }
          Capture(Use(y.Q))
        }
        F(F.p)                                                                                  -/
def program : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "Use" (alg ["f"] [] [] [.num 1]), privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1])] [(.call (.resolve "Capture") [(.call (.resolve "Use") [(.dotCall (.param "y") "Q" none)])])])] [(.call (.resolve "F") [(.dotCall (.resolve "F") "p" none)])])

/-- The source tree is in the assumed source domain … -/
theorem sourceLike : SourceLike program := ⟨by cbv, by cbv⟩

theorem sourceDomain : SourceDomain program := ⟨by cbv, by cbv⟩

/-- … and outside the restricted one: the exported container `p` declares a capturing member. -/
theorem not_deep : exposureDeep program = false := by cbv

def root : Algorithm := rootOf program
/-- The root alone as the context of the program's rows (see the module note on the prelude). -/
def ctx : EvalCtx := { callStack := [root] }
/-- The program's one row, `F(F.p)`. -/
def row : Expr := root.output.headD (.num 0)
/-- The state production leaves after the row. -/
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell of the captured call `Use(y.Q)`. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE CONTEXT of `F`'s body, read off the plan cell the program's binders built. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
/-- The written argument `y.Q`. -/
def path : Expr := .dotCall (.param "y") "Q" none
/-- The member production's structural projection of `y.Q` returns. -/
def wiredQ : Algorithm :=
  match ((projectNeedStructuralMember path ctxIn).runState fin).1 with
  | .ok (some a) => a
  | _ => preludeAlg
/-- The state after that projection (the parameter's own CALLABLE was projected). -/
def mid : EvalState := ((projectNeedStructuralMember path ctxIn).runState fin).2
/-- The exit state of the member's structure chase. -/
def chased : EvalState := ((resolveAliasStructure wiredQ ctxIn).runState mid).2

theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((projectNeedStructuralMember path ctxIn).runState fin = (.ok (some wiredQ), mid)) ∧
    (paramRowOwnedB wiredQ = true) ∧
    (paramRowAdmits wiredQ ctxIn mid = true) ∧
    (((resolveAliasStructure wiredQ ctxIn).runState mid).1.isIncomplete = false) ∧
    (ScopeCtx.activationChain (siteScope? ctxIn) = [some 0, none]) ∧
    (ScopeCtx.activationChain wiredQ.parent = [none, some 0, none]) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED.** Production's evaluation of the program's row from the empty state captures the plan
    of `Use(y.Q)`, written in `F`'s body. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) := facts.1

/-- In that body's own context production selects the member `Q` of the container the parameter
    holds: accessibility ACCEPTS it. -/
theorem projected : (projectNeedStructuralMember path ctxIn).runState fin = (.ok (some wiredQ), mid) := facts.2.1

/-- The reading site is inside an activation of `F`, and so, ANCHORED, is the member's own chain: the
    container's static level of `F` became that activation. -/
theorem chains : ScopeCtx.activationChain (siteScope? ctxIn) = [some 0, none] ∧
    ScopeCtx.activationChain wiredQ.parent = [none, some 0, none] := ⟨facts.2.2.2.2.2.1, facts.2.2.2.2.2.2⟩

/-- **THE CELL CLAUSE HOLDS ON THIS SOURCE PROGRAM** (formerly its counterexample): the member
    production wires is a parameter-row alias whose owner, on its own chain, is activated. -/
theorem reached_member_is_owned : ParamRowOwned wiredQ := paramRowOwned_of_B facts.2.2.1

/-- The navigation core admits that member's chase, through the owner's activation. -/
theorem admitted : navAdmits (.resolveAliasChase false true wiredQ ctxIn [] none) mid = true := facts.2.2.2.1

theorem chase_completes : ProductionCompletes (evalUnbounded (.resolveAliasStructure wiredQ ctxIn)) mid := by
  intro h
  have hinc : ((resolveAliasStructure wiredQ ctxIn).runState mid).1.isIncomplete = false := facts.2.2.2.2.1
  have h' : ((resolveAliasStructure wiredQ ctxIn).runState mid).1 = .error .fuelExhausted := h
  rw [h'] at hinc
  cases hinc

end OutsideContainer

/-! ## `EscapedContainer`: the same member read in a body invoked through a call reference -/

namespace EscapedContainer

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        Capture(meta op) = op
        Use(f) = 1
        F(y) = {
          p = {
            Q = y
            1
          }
          Inner(z) = Capture(Use(z.Q))
          K(meta r) = r
          K(Inner(0))
        }
        R = F(5)
        R.Algorithm(F.p)                                                                        -/
def program : Expr :=
  .algorithmExpr (alg [] [] [privateProp "R" (alg [] [] [] [(.call (.resolve "F") [.num 5])]), privateProp "Capture" (algWithParameters [{ name := "op", kind := .metaRef }] [] [] [.param "op"]), privateProp "Use" (alg ["f"] [] [] [.num 1]), privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "Inner" (alg ["z"] [] [] [(.call (.resolve "Capture") [(.call (.resolve "Use") [(.dotCall (.param "z") "Q" none)])])]), privateProp "K" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"])] [(.call (.resolve "K") [(.call (.resolve "Inner") [.num 0])])])] [(.dotCall (.resolve "R") "Algorithm" (some [(.dotCall (.resolve "F") "p" none)]))])

theorem sourceLike : SourceLike program := ⟨by cbv, by cbv⟩

theorem sourceDomain : SourceDomain program := ⟨by cbv, by cbv⟩

theorem not_deep : exposureDeep program = false := by cbv

def root : Algorithm := rootOf program
def ctx : EvalCtx := { callStack := [root] }
/-- The program's one row, `R.Algorithm(F.p)`. -/
def row : Expr := root.output.headD (.num 0)
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell of the captured call `Use(z.Q)`. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE CONTEXT of `Inner`'s body, invoked outside `F`'s evaluation through the reference. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def path : Expr := .dotCall (.param "z") "Q" none
def wiredQ : Algorithm :=
  match ((projectNeedStructuralMember path ctxIn).runState fin).1 with
  | .ok (some a) => a
  | _ => preludeAlg
def mid : EvalState := ((projectNeedStructuralMember path ctxIn).runState fin).2
/-- The exit state of the member's structure chase. -/
def once : EvalState := ((resolveAliasStructure wiredQ ctxIn).runState mid).2

theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((projectNeedStructuralMember path ctxIn).runState fin = (.ok (some wiredQ), mid)) ∧
    ((resolveAliasStructure wiredQ ctxIn).runState mid = (.ok none, once)) ∧
    (once.needs.size = mid.needs.size) ∧ (once.nextRuntimeDeclaration = mid.nextRuntimeDeclaration) ∧
    ((resolveAliasStructure wiredQ ctxIn).runState once = (.ok none, once)) ∧
    (paramRowOwnedB wiredQ = true) ∧
    (paramRowAdmits wiredQ ctxIn mid = true) ∧
    (ScopeCtx.activationChain (siteScope? ctxIn) = [some 2, some 0, none]) ∧
    (ScopeCtx.activationChain wiredQ.parent = [none, some 0, none]) ∧
    (ctxIn.needEnv.map Prod.fst = ["z"]) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **REACHED.** Production's evaluation of the program's row from the empty state: `R`'s reference
    is read, `R.Algorithm(F.p)` invokes `Inner`, and `Inner`'s body captures the plan of `Use(z.Q)`. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) := facts.1

/-- In `Inner`'s own context the member `Q` is accessible: the site chain holds `F`'s activation. -/
theorem projected : (projectNeedStructuralMember path ctxIn).runState fin = (.ok (some wiredQ), mid) := facts.2.1

/-- The reading site holds the activations of `Inner` and of `F`; the member's anchored chain holds
    that activation of `F`, although the reading tier binds `z` only. -/
theorem chains : ScopeCtx.activationChain (siteScope? ctxIn) = [some 2, some 0, none] ∧
    ScopeCtx.activationChain wiredQ.parent = [none, some 0, none] ∧ ctxIn.needEnv.map Prod.fst = ["z"] :=
  ⟨facts.2.2.2.2.2.2.2.2.1, facts.2.2.2.2.2.2.2.2.2.1, facts.2.2.2.2.2.2.2.2.2.2⟩

/-- The member is owned, and the navigation core admits its chase. -/
theorem reached_member_is_owned : ParamRowOwned wiredQ ∧
    navAdmits (.resolveAliasChase false true wiredQ ctxIn [] none) mid = true :=
  ⟨paramRowOwned_of_B facts.2.2.2.2.2.2.1, facts.2.2.2.2.2.2.2.1⟩

/-- **THE FORMER COUNTEREXAMPLE IS RE-READ.** From a state production reaches by the program's own
    row, in the context the program's own binders built, the structure chase of the member production
    selected completes, allocates no cell, mints no runtime identity, and a second chase from its
    exit state gives the same answer and changes nothing. The program is `SourceLike`. -/
theorem source_navigation_is_reread :
    SourceLike program ∧
    (projectNeedStructuralMember path ctxIn).runState fin = (.ok (some wiredQ), mid) ∧
    (resolveAliasStructure wiredQ ctxIn).runState mid = (.ok none, once) ∧
    once.needs.size = mid.needs.size ∧ once.nextRuntimeDeclaration = mid.nextRuntimeDeclaration ∧
    (resolveAliasStructure wiredQ ctxIn).runState once = (.ok none, once) :=
  ⟨sourceLike, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1, facts.2.2.2.2.2.1⟩

end EscapedContainer

/-! ## The same programs through `runResult`, prelude included

Execution checks of the model's behaviour since the anchoring decision of 2026-11-13 (C# returns the
same values, `NavigationSourceDomainWitnessTests`). The language rule itself is pinned by
CoreTests `NameOwnership` (`anchored*`); these record the proof programme's own witnesses. -/

/-- The innermost error of an outcome. -/
def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | other => other

/-- `F(y) = { p = { Q = y ⏎ 1 } ⏎ y.Q }` / `F(F.p)`: the member is read; `y` is `F.p`, whose value is 1. -/
def outsideValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1])] [(.dotCall (.param "y") "Q" none)])] [(.call (.resolve "F") [(.dotCall (.resolve "F") "p" none)])])

#guard (match runResult outsideValue with | .ok (.atom 1) => true | _ => false)

/-- `F(y) = { p = { Q = y ⏎ 1 } ⏎ G(g, y) = g.Q ⏎ G(y, 99) }` / `F(F.p)`: the member `Q = y`, whose
    `y` is `F`'s parameter, is read inside `G`, whose own parameter is also named `y`. -/
def shadowedRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "G" (alg ["g", "y"] [] [] [(.dotCall (.param "g") "Q" none)])] [(.call (.resolve "G") [.param "y", .num 99])])] [(.call (.resolve "F") [(.dotCall (.resolve "F") "p" none)])])

theorem shadowedRead_sourceLike : SourceLike shadowedRead := ⟨by cbv, by cbv⟩

theorem shadowedRead_sourceDomain : SourceDomain shadowedRead := ⟨by cbv, by cbv⟩

-- THE READ IS THE OWNER'S BINDING: the value of `F`'s `y`, 1 (before the anchoring, `G`'s 99).
#guard (match runResult shadowedRead with | .ok (.atom 1) => true | _ => false)

/-- The control: the same container obtained INSIDE the activation reads `F`'s parameter. -/
def insideRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "G" (alg ["g", "y"] [] [] [(.dotCall (.param "g") "Q" none)])] [(.call (.resolve "G") [.resolve "p", .num 99])])] [(.call (.resolve "F") [.num 5])])

#guard (match runResult insideRead with | .ok (.atom 5) => true | _ => false)

/-- `… Inner(z) = z.Q ⏎ K(meta r) = r ⏎ K(Inner(0)) }` / `R = F(5)` / `R.Algorithm(F.p)`: the member is
    read in `Inner`'s body, invoked through the reference that captured `F(5)`; it reads that call's
    `y`, 5 (before the anchoring, `unknownName`: the reading tier binds `z` only). -/
def escapedValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "R" (alg [] [] [] [(.call (.resolve "F") [.num 5])]), privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "Inner" (alg ["z"] [] [] [(.dotCall (.param "z") "Q" none)]), privateProp "K" (algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"])] [(.call (.resolve "K") [(.call (.resolve "Inner") [.num 0])])])] [(.dotCall (.resolve "R") "Algorithm" (some [(.dotCall (.resolve "F") "p" none)]))])

#guard (match runResult escapedValue with | .ok (.atom 5) => true | _ => false)

/-- The control from outside every activation: `F.p.Q` at the root is refused. -/
def rootRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "p" (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1])] [.param "y"])] [(.dotCall (.dotCall (.resolve "F") "p" none) "Q" none)])

#guard (match runResult rootRead with
  | .error e => (match innermost e with | .localOnlyProperty _ "Q" _ => true | _ => false)
  | .ok _ => false)

/-! ## Selection gaps in the candidate domain (independent review, 2026-11-13)

`exposureFull` extends the lexical fragment but is not complete exposure. These source-valid routes
are omitted by its static selector: one provider opened twice, a dotted receiver head supplied by an
open, and a transparent-reference chain beyond `selFuel`. The front end marks each reader `A`
local-only with required `y` (`NavigationSourceDomainWitnessTests`); the candidate domain accepts
both that metadata and its host-corrupted exported counterpart. These are counterexamples to the
completeness of the PREDICATE, not to the production evaluator or the proposed runtime invariant.
-/

namespace SelectionGaps

/-- Source tree of `A = { open Lib, Lib ⏎ Q + 0 }` inside `F(y)`, where `Lib.Q = y`.
    The front end deduplicates the provider; `openedAt` incorrectly counts two hits. -/
def duplicateOpened : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib", .resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

def duplicateOpenedExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib", .resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem duplicate_opened_sourceDomain : SourceDomain duplicateOpened := ⟨by cbv, by cbv⟩

/-- Missing `y` is not detected: the selector mistakes repeated targets for ambiguity. -/
theorem duplicate_opened_exported_admitted : SourceDomain duplicateOpenedExported := ⟨by cbv, by cbv⟩

#guard (match runResult duplicateOpened with | .ok (.atom 5) => true | _ => false)

/-- Source tree of `A = { open Lib ⏎ Box.Q + 0 }`, where `Lib.Box.Q = y`.
    Ordinary lexical lookup resolves `Box` through the open; `walkPath` only searches properties. -/
def openedReceiver : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

def openedReceiverExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem opened_receiver_sourceDomain : SourceDomain openedReceiver := ⟨by cbv, by cbv⟩

/-- Missing `y` is not detected when the dotted receiver head is open-provided. -/
theorem opened_receiver_exported_admitted : SourceDomain openedReceiverExported := ⟨by cbv, by cbv⟩

#guard (match runResult openedReceiver with | .ok (.atom 5) => true | _ => false)

/-- A source-shaped receiver chain longer than the model's fixed fuel, with no cycle.
    The C# witness separately checks the 65-link source program and its local-only reader. -/
def longChain (exposure : PropExposure) : Expr :=
  let name (i : Nat) := "L" ++ toString i
  let links := (List.range (selFuel + 1)).map fun i =>
    privateProp (name i) (.alias none [] [] (.resolve (if i = 0 then "Lib" else name (i-1))))
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    ([privateProp "Lib" (alg [] []
      [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with
          requiredOwnerDepths := some [("y", some 1)] }] [.num 1])] ++ links ++
     [{ (privateLocalProp "A" exposure (alg [] [] []
         [.binary .add (.dotCall (.resolve (name selFuel)) "Q" none) (.num 0)])) with
         requiredOwnerDepths := if exposure.isExported then none else some [("y", some 0)] }])
    [.resolve "A"])] [.call (.resolve "F") [.num 5]])

theorem long_chain_exported_admitted : SourceDomain (longChain .exported) := ⟨by cbv, by cbv⟩
theorem long_chain_sourceDomain : SourceDomain (longChain (.localCapturedAncestorParams ["y"])) := ⟨by cbv, by cbv⟩

end SelectionGaps

end KatLang.NavigationSourceDomainGuards
