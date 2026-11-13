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
* `SelectionGaps` / `SelectionRoutes` / `AccessChecks` (end of the module) — for every static
  selection route the selection model covers, a host-built counterfactual with the reader's
  requirement (or the rule's condition) removed, refused by `SourceDomain` (`*_refused`); in
  `AccessChecks` the counterfactual is the pre-fix front end's own tree (E-18 exposure access
  checks, owner decision 2026-11-13).

## 2. Source trees inside the domain (`OutsideContainer`, `EscapedContainer`, `FrontEnd`, `SelectionGaps`, `SelectionRoutes`, `AccessChecks`)

The two reached-state fixtures, five public-entry guards, the four `FrontEnd` programs, the three
`SelectionGaps` sources, the eight `SelectionRoutes` sources and the ten `AccessChecks` sources below
are the C# front end's own elaborated trees of the quoted sources, encoded by `LeanAstEncoder`.
Maintained C# fidelity tests check those thirty-two encodings (`NavigationSourceDomainWitnessTests`;
`moduleCut` through the asynchronous front end with its loaded module). Each is in `SourceDomain`; the `ExposureFragment`
and `OpenedFragment` examples and every `Exported` / host-built counterfactual are intentionally
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

/-! ## Selection gaps of the former candidate domain (independent review, 2026-11-13), closed

The B2 preparation's bounded selector omitted three source-valid routes: one provider opened twice
(raw written hits, no provider deduplication), a dotted receiver head supplied by an `open` (a
direct-lexical head only), and a transparent-reference chain beyond a fixed fuel of 64 (dropped
silently). The front end marks each reader `A` local-only with required `y`
(`NavigationSourceDomainWitnessTests`). The selection model's `exposureFull` refuses each host-corrupted
exported counterpart (`*_exported_refused`, formerly `*_exported_admitted`) and keeps admitting the
source trees.
-/

namespace SelectionGaps

/-- Source tree of `A = { open Lib, Lib ⏎ Q + 0 }` inside `F(y)`, where `Lib.Q = y`.
    One provider, written twice: the hit is counted once. -/
def duplicateOpened : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib", .resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def duplicateOpenedExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib", .resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem duplicate_opened_sourceDomain : SourceDomain duplicateOpened := ⟨by cbv, by cbv⟩

/-- The missing `y` is detected: the repeated target is one provider. -/
theorem duplicate_opened_exported_refused : ¬ SourceDomain duplicateOpenedExported :=
  fun h => by have := h.exposed; rw [show exposureFull duplicateOpenedExported = false by cbv] at this; cases this

#guard (match runResult duplicateOpened with | .ok (.atom 5) => true | _ => false)

/-- Source tree of `A = { open Lib ⏎ Box.Q + 0 }`, where `Lib.Box.Q = y`.
    The dotted head `Box` is resolved by the full lookup, through the open. -/
def openedReceiver : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def openedReceiverExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.resolve "Box") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem opened_receiver_sourceDomain : SourceDomain openedReceiver := ⟨by cbv, by cbv⟩

/-- The missing `y` is detected when the dotted receiver head is open-provided. -/
theorem opened_receiver_exported_refused : ¬ SourceDomain openedReceiverExported :=
  fun h => by have := h.exposed; rw [show exposureFull openedReceiverExported = false by cbv] at this; cases this

#guard (match runResult openedReceiver with | .ok (.atom 5) => true | _ => false)

/-- Host-built generator of a receiver chain of 65 transparent references (`L0 = Lib`,
    `Lk = L(k-1)`) and `A = L64.Q + 0`; with `A` local-only it is the source tree `longChainSource`. -/
def longChain (exposure : PropExposure) : Expr :=
  let name (i : Nat) := "L" ++ toString i
  let links := (List.range 65).map fun i =>
    privateProp (name i) (.alias none [] [] (.resolve (if i = 0 then "Lib" else name (i-1))))
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    ([privateProp "Lib" (alg [] []
      [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with
          requiredOwnerDepths := some [("y", some 1)] }] [.num 1])] ++ links ++
     [{ (privateLocalProp "A" exposure (alg [] [] []
         [.binary .add (.dotCall (.resolve (name 64)) "Q" none) (.num 0)])) with
         requiredOwnerDepths := if exposure.isExported then none else some [("y", some 0)] }])
    [.resolve "A"])] [.call (.resolve "F") [.num 5]])

/-- `LeanAstEncoder`'s encoding of the front end's tree of the 65-link chain
    (`F(y) = { Lib = { public Q = y ⏎ 1 } ⏎ L0 = Lib ⏎ … ⏎ L64 = L63 ⏎ A = L64.Q + 0 ⏎ A }` / `F(5)`). -/
def longChainSource : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "L0" (.alias none [] [] (.resolve "Lib")), privateProp "L1" (.alias none [] [] (.resolve "L0")), privateProp "L2" (.alias none [] [] (.resolve "L1")), privateProp "L3" (.alias none [] [] (.resolve "L2")), privateProp "L4" (.alias none [] [] (.resolve "L3")), privateProp "L5" (.alias none [] [] (.resolve "L4")), privateProp "L6" (.alias none [] [] (.resolve "L5")), privateProp "L7" (.alias none [] [] (.resolve "L6")), privateProp "L8" (.alias none [] [] (.resolve "L7")), privateProp "L9" (.alias none [] [] (.resolve "L8")), privateProp "L10" (.alias none [] [] (.resolve "L9")), privateProp "L11" (.alias none [] [] (.resolve "L10")), privateProp "L12" (.alias none [] [] (.resolve "L11")), privateProp "L13" (.alias none [] [] (.resolve "L12")), privateProp "L14" (.alias none [] [] (.resolve "L13")), privateProp "L15" (.alias none [] [] (.resolve "L14")), privateProp "L16" (.alias none [] [] (.resolve "L15")), privateProp "L17" (.alias none [] [] (.resolve "L16")), privateProp "L18" (.alias none [] [] (.resolve "L17")), privateProp "L19" (.alias none [] [] (.resolve "L18")), privateProp "L20" (.alias none [] [] (.resolve "L19")), privateProp "L21" (.alias none [] [] (.resolve "L20")), privateProp "L22" (.alias none [] [] (.resolve "L21")), privateProp "L23" (.alias none [] [] (.resolve "L22")), privateProp "L24" (.alias none [] [] (.resolve "L23")), privateProp "L25" (.alias none [] [] (.resolve "L24")), privateProp "L26" (.alias none [] [] (.resolve "L25")), privateProp "L27" (.alias none [] [] (.resolve "L26")), privateProp "L28" (.alias none [] [] (.resolve "L27")), privateProp "L29" (.alias none [] [] (.resolve "L28")), privateProp "L30" (.alias none [] [] (.resolve "L29")), privateProp "L31" (.alias none [] [] (.resolve "L30")), privateProp "L32" (.alias none [] [] (.resolve "L31")), privateProp "L33" (.alias none [] [] (.resolve "L32")), privateProp "L34" (.alias none [] [] (.resolve "L33")), privateProp "L35" (.alias none [] [] (.resolve "L34")), privateProp "L36" (.alias none [] [] (.resolve "L35")), privateProp "L37" (.alias none [] [] (.resolve "L36")), privateProp "L38" (.alias none [] [] (.resolve "L37")), privateProp "L39" (.alias none [] [] (.resolve "L38")), privateProp "L40" (.alias none [] [] (.resolve "L39")), privateProp "L41" (.alias none [] [] (.resolve "L40")), privateProp "L42" (.alias none [] [] (.resolve "L41")), privateProp "L43" (.alias none [] [] (.resolve "L42")), privateProp "L44" (.alias none [] [] (.resolve "L43")), privateProp "L45" (.alias none [] [] (.resolve "L44")), privateProp "L46" (.alias none [] [] (.resolve "L45")), privateProp "L47" (.alias none [] [] (.resolve "L46")), privateProp "L48" (.alias none [] [] (.resolve "L47")), privateProp "L49" (.alias none [] [] (.resolve "L48")), privateProp "L50" (.alias none [] [] (.resolve "L49")), privateProp "L51" (.alias none [] [] (.resolve "L50")), privateProp "L52" (.alias none [] [] (.resolve "L51")), privateProp "L53" (.alias none [] [] (.resolve "L52")), privateProp "L54" (.alias none [] [] (.resolve "L53")), privateProp "L55" (.alias none [] [] (.resolve "L54")), privateProp "L56" (.alias none [] [] (.resolve "L55")), privateProp "L57" (.alias none [] [] (.resolve "L56")), privateProp "L58" (.alias none [] [] (.resolve "L57")), privateProp "L59" (.alias none [] [] (.resolve "L58")), privateProp "L60" (.alias none [] [] (.resolve "L59")), privateProp "L61" (.alias none [] [] (.resolve "L60")), privateProp "L62" (.alias none [] [] (.resolve "L61")), privateProp "L63" (.alias none [] [] (.resolve "L62")), privateProp "L64" (.alias none [] [] (.resolve "L63")), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "L64") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- The generator reproduces the source tree. -/
theorem longChain_is_source : longChain (.localCapturedAncestorParams ["y"]) = longChainSource := by rfl

theorem long_chain_sourceDomain : SourceDomain longChainSource := ⟨by cbv, by cbv⟩

/-- The fuel is derived from the program (`selFuel`): the 65-link chase completes, and the missing
    `y` is detected. -/
theorem long_chain_exported_refused : ¬ SourceDomain (longChain .exported) :=
  fun h => by have := h.exposed; rw [show exposureFull (longChain .exported) = false by cbv] at this; cases this

#guard (match runResult longChainSource with | .ok (.atom 5) => true | _ => false)

end SelectionGaps

/-! ## Every newly modeled selection route: a source control and a host-built counterfactual

Each `def` documented as `LeanAstEncoder`'s encoding is the front end's tree of the quoted source
(`NavigationSourceDomainWitnessTests` checks the encoding, the value and the reader's metadata);
each is in `SourceDomain` and runs to the value its `#guard` records. Each host-built
counterfactual is the same tree with the reader's requirement removed (or, for the rules that make
a reader require NOTHING — two providers, a selected member, the prelude, the module cut — the same
tree with that rule's condition removed), and `SourceDomain` refuses it.
-/

namespace SelectionRoutes

/-- `LeanAstEncoder`'s encoding of the front end's tree of a TRANSPARENT REFERENCE whose target head an OPEN provides (the suspected fourth gap,
    confirmed):

        F(y) = {
          Lib = {
            public Box = {
              public Q = y
              1
            }
            1
          }
          A = {
            open Lib
            L = Box
            L.Q + 0
          }
          A
        }
        F(5)

    `L.Q` reads `L`'s structure: `Box`, resolved in `L`'s own scope by the full lookup
    (`staticPathSelectWith`), through `A`'s open. -/
def openedAliasTarget : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib"] [privateProp "L" (.alias none [] [] (.resolve "Box"))] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def openedAliasTargetExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [privateProp "L" (.alias none [] [] (.resolve "Box"))] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem openedAliasTarget_sourceDomain : SourceDomain openedAliasTarget := ⟨by cbv, by cbv⟩

theorem openedAliasTarget_exported_refused : ¬ SourceDomain openedAliasTargetExported :=
  fun h => by have := h.exposed; rw [show exposureFull openedAliasTargetExported = false by cbv] at this; cases this

#guard (match runResult openedAliasTarget with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of one PROVIDER under two SPELLINGS (`open Sub, Lib.Sub`, `Sub = Lib.Sub`):

        F(y) = {
          Lib = {
            public Sub = {
              public Q = y
              1
            }
            1
          }
          Sub = Lib.Sub
          A = {
            open Sub, Lib.Sub
            Q + 0
          }
          A
        }
        F(5)

    Both targets resolve to the declaration `Lib.Sub` (the reference normalized): one provider, one hit. -/
def sameProvider : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "Sub" (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none))), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Sub", (.dotCall (.resolve "Lib") "Sub" none)] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def sameProviderExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "Sub" (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none))), privateProp "A" (alg [] [.resolve "Sub", (.dotCall (.resolve "Lib") "Sub" none)] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem sameProvider_sourceDomain : SourceDomain sameProvider := ⟨by cbv, by cbv⟩

theorem sameProvider_exported_refused : ¬ SourceDomain sameProviderExported :=
  fun h => by have := h.exposed; rw [show exposureFull sameProviderExported = false by cbv] at this; cases this

#guard (match runResult sameProvider with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of an OPEN-PROVIDED HEAD inside a NESTED path:

        F(y) = {
          Lib = {
            public Box = {
              public Sub = {
                public Q = y
                1
              }
              1
            }
            1
          }
          A = {
            open Lib
            Box.Sub.Q + 0
          }
          A
        }
        F(5) -/
def openedNestedHead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 3)] }] [.num 1])] [.num 1])] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.dotCall (.resolve "Box") "Sub" none) "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def openedNestedHeadExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 3)] }] [.num 1])] [.num 1])] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.dotCall (.dotCall (.resolve "Box") "Sub" none) "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem openedNestedHead_sourceDomain : SourceDomain openedNestedHead := ⟨by cbv, by cbv⟩

theorem openedNestedHead_exported_refused : ¬ SourceDomain openedNestedHeadExported :=
  fun h => by have := h.exposed; rw [show exposureFull openedNestedHeadExported = false by cbv] at this; cases this

#guard (match runResult openedNestedHead with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of a reference whose target head an ENCLOSING level's open provides:

        F(y) = {
          open Lib
          Lib = {
            public Box = {
              public Q = y
              1
            }
            1
          }
          L = Box
          A = L.Q + 0
          A
        }
        F(5) -/
def outerOpenAliasTarget : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "L" (.alias none [] [] (.resolve "Box")), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` host-corrupted to exported. -/
def outerOpenAliasTargetExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "Box" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 2)] }] [.num 1])] [.num 1]), privateProp "L" (.alias none [] [] (.resolve "Box")), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem outerOpenAliasTarget_sourceDomain : SourceDomain outerOpenAliasTarget := ⟨by cbv, by cbv⟩

theorem outerOpenAliasTarget_exported_refused : ¬ SourceDomain outerOpenAliasTargetExported :=
  fun h => by have := h.exposed; rw [show exposureFull outerOpenAliasTargetExported = false by cbv] at this; cases this

#guard (match runResult outerOpenAliasTarget with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of TWO DISTINCT PROVIDERS at one level,
    read through a POSSIBLE dot fallback:

        F(y) = {
          Lib1 = {
            public Q = y
            1
          }
          Lib2 = {
            public Q = y
            2
          }
          Box = {
            public Q = 5
            0
          }
          G(obj) = {
            open Lib1, Lib2
            obj.Q
          }
          G(Box)
        }
        F(5)

    The fallback `Q` names two providers: the level selects NOTHING (`ambiguousOpen`) and charges
    nothing, so the front end keeps `G` exported (a written ambiguous read is a front-end error). -/
def ambiguousFallback : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib1" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "Lib2" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 2]), privateProp "Box" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 5])] [.num 0]), privateProp "G" (alg ["obj"] [.resolve "Lib1", .resolve "Lib2"] [] [(.dotCall (.param "obj") "Q" none)])] [(.call (.resolve "G") [.resolve "Box"])])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with ONE provider (`open Lib1`), `G` still exported. The fallback now
    selects `Lib1.Q`. -/
def singleProviderFallback : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib1" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "Lib2" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 1)] }] [.num 2]), privateProp "Box" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 5])] [.num 0]), privateProp "G" (alg ["obj"] [.resolve "Lib1"] [] [(.dotCall (.param "obj") "Q" none)])] [(.call (.resolve "G") [.resolve "Box"])])] [(.call (.resolve "F") [.num 5])])

/-- Two distinct providers charge nothing: the exported `G` is in the domain. -/
theorem ambiguousFallback_sourceDomain : SourceDomain ambiguousFallback := ⟨by cbv, by cbv⟩

/-- With one provider the possible fallback requires `y`: the exported `G` is refused. -/
theorem singleProviderFallback_refused : ¬ SourceDomain singleProviderFallback :=
  fun h => by have := h.exposed; rw [show exposureFull singleProviderFallback = false by cbv] at this; cases this

#guard (match runResult ambiguousFallback with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of a dot edge whose path SELECTS a member
    of a receiver that itself requires `y`:

        F(y) = {
          Lib = {
            public Q = 1
            y
          }
          A = Lib.Q + 0
          A
        }
        F(5)

    The evaluator reads the selected `Q` only, never `Lib`'s value: the front end keeps `A`
    exported. (The former candidate charged the head and refused this source tree.) -/
def selectedMemberOnly : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Lib" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Lib") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree reading a member `Lib` does not declare (`Lib.Z`): the edge selects
    nothing, the fallback `Z(Lib)` reads `Lib`'s value, so the exported `A` misses `y`. -/
def missReadsReceiverExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Lib" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "Lib") "Z" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem selectedMemberOnly_sourceDomain : SourceDomain selectedMemberOnly := ⟨by cbv, by cbv⟩

theorem missReadsReceiver_refused : ¬ SourceDomain missReadsReceiverExported :=
  fun h => by have := h.exposed; rw [show exposureFull missReadsReceiverExported = false by cbv] at this; cases this

#guard (match runResult selectedMemberOnly with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of a name the PRELUDE declares, also
    provided by an open:

        F(y) = {
          Lib = {
            public count(xs) = y
            1
          }
          A = {
            open Lib
            count((1, 2)) + 0
          }
          A
        }
        F(5)

    The ownership-first lookup reaches the prelude's builtin `count` before any open: `A` is exported. -/
def preludeBeforeOpens : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "count" (.localCapturedAncestorParams ["y"]) (alg ["xs"] [] [] [.param "y"])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.call (.resolve "count") [(.capture [.num 1, .num 2])]) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with the member and the read renamed `cnt`, which the prelude does
    not declare: the open provides it, and the exported `A` misses `y`. -/
def openedNotPrelude : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "cnt" (.localCapturedAncestorParams ["y"]) (alg ["xs"] [] [] [.param "y"])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.call (.resolve "cnt") [(.capture [.num 1, .num 2])]) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem preludeBeforeOpens_sourceDomain : SourceDomain preludeBeforeOpens := ⟨by cbv, by cbv⟩

theorem openedNotPrelude_refused : ¬ SourceDomain openedNotPrelude :=
  fun h => by have := h.exposed; rw [show exposureFull openedNotPrelude = false by cbv] at this; cases this

#guard (match runResult preludeBeforeOpens with | .ok (.atom 2) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree (asynchronous, with the loaded module) of

        F(y) = {
          Q = y
          M = load('https://mods.test/m.kat')
          M.V + 0
        }
        F(7)

    where the module is `G(k) = { Lib = { public Q = k ⏎ 1 } ⏎ A = { open Lib ⏎ Q + 0 } ⏎ A }`
    `⏎ public V = G(5)`. A LOADED MODULE is rooted at the prelude: inside it `Q` is not the holder's
    `Q` but `Lib.Q`, through `A`'s open, and requires the module's `k`. (Without the cut the former
    candidate selected the holder's `Q` and refused this source tree.) -/
def moduleCut : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (alg [] [] [publicProp "V" (alg [] [] [] [(.call (.resolve "G") [.num 5])]), privateProp "G" (alg ["k"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["k"]) (.alias none [] [] (.param "k"))) with requiredOwnerDepths := some [("k", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["k"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("k", some 0)] }] [.resolve "A"])] []))] [(.binary .add (.dotCall (.resolve "M") "V" none) (.num 0))])] [(.call (.resolve "F") [.num 7])])

/-- Host-built: the same tree with the module's `A` host-corrupted to exported. -/
def moduleCutExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (alg [] [] [publicProp "V" (alg [] [] [] [(.call (.resolve "G") [.num 5])]), privateProp "G" (alg ["k"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["k"]) (.alias none [] [] (.param "k"))) with requiredOwnerDepths := some [("k", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] []))] [(.binary .add (.dotCall (.resolve "M") "V" none) (.num 0))])] [(.call (.resolve "F") [.num 7])])

theorem moduleCut_sourceDomain : SourceDomain moduleCut := ⟨by cbv, by cbv⟩

theorem moduleCut_exported_refused : ¬ SourceDomain moduleCutExported :=
  fun h => by have := h.exposed; rw [show exposureFull moduleCutExported = false by cbv] at this; cases this

#guard (match runResult moduleCut with | .ok (.atom 5) => true | _ => false)

end SelectionRoutes

/-! ## Access checks the exposure pass formerly under-charged (E-18, owner decision 2026-11-13)

Exposure charges exactly the access checks and value reads the evaluator performs on static
selections. One source program per class the C# front end under-charged before the fix — a
transparent reference crossed as a path head, a chain of references, an inline-block head, an open
through a reference, an enclosing level's open (used and unused) — is admitted (`*_sourceDomain`),
and the pre-fix front end's own tree of the same source, which exported the reader, is refused
(`*_hostBuilt_refused`). The F1 review's `intermediateSource` is admitted and its
`intermediateCorrupt` refused (`intermediateCorrupt_refused`). Three exported controls (a member-less
reference, a named head and an inline-block head whose member is selected) are admitted. The C#
fidelity tests are `NavigationSourceDomainWitnessTests` (scope `AccessChecks`) and
`ExposureAccessCheckTests`.
-/

namespace AccessChecks

/-- `LeanAstEncoder`'s encoding of the front end's tree of `Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 }`, `L = Lib.Sub`, `A = L.Q + 0`, inside `F(y)` / `F(5)`:
    a transparent reference crossed as a path head. `A` is local-only on `y`. -/
def referenceWalk : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def referenceWalkHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem referenceWalk_sourceDomain : SourceDomain referenceWalk := ⟨by cbv, by cbv⟩

theorem referenceWalk_hostBuilt_refused : ¬ SourceDomain referenceWalkHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull referenceWalkHostBuilt = false by cbv] at this; cases this

#guard (match runResult referenceWalk with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `L0 = Lib.Sub`, `M = L0.T`, `A = M.Q + 0` (`Sub` declares `public T = { public Q = 1 }`), inside `F(y)` / `F(5)`:
    a chain of references, each crossed. `A` is local-only on `y`. -/
def referenceChain : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "T" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L0" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "M" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "L0") "T" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.resolve "M") "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def referenceChainHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "T" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L0" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (.alias none [] [] ((.dotCall (.resolve "L0") "T" none))), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "M") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem referenceChain_sourceDomain : SourceDomain referenceChain := ⟨by cbv, by cbv⟩

theorem referenceChain_hostBuilt_refused : ¬ SourceDomain referenceChainHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull referenceChainHostBuilt = false by cbv] at this; cases this

#guard (match runResult referenceChain with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `A = { public Sub = { public Q = 1 ⏎ y } }.Sub.Q + 0`, inside `F(y)` / `F(5)`:
    an inline-block path head. `A` is local-only on `y`. -/
def blockHead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.algorithmExpr (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 2)] }] [])) "Sub" none) "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def blockHeadHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.algorithmExpr (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 2)] }] [])) "Sub" none) "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem blockHead_sourceDomain : SourceDomain blockHead := ⟨by cbv, by cbv⟩

theorem blockHead_hostBuilt_refused : ¬ SourceDomain blockHeadHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull blockHeadHostBuilt = false by cbv] at this; cases this

#guard (match runResult blockHead with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 }`, `L = Lib.Sub`, `A = { open L ⏎ Q + 0 }`, inside `F(y)` / `F(5)`:
    an open target that is a reference. `A` is local-only on `y`. -/
def openThroughReference : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [.resolve "L"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def openThroughReferenceHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.resolve "Lib") "Sub" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [.resolve "L"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem openThroughReference_sourceDomain : SourceDomain openThroughReference := ⟨by cbv, by cbv⟩

theorem openThroughReference_hostBuilt_refused : ¬ SourceDomain openThroughReferenceHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull openThroughReferenceHostBuilt = false by cbv] at this; cases this

#guard (match runResult openThroughReference with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `F(y) = { open Lib.Sub ⏎ Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 } ⏎ A = Q + 0 ⏎ A }`, inside `F(y)` / `F(5)`:
    an open of an enclosing level. `A` is local-only on `y`. -/
def enclosingOpen : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none)] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def enclosingOpenHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none)] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "A" (alg [] [] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem enclosingOpen_sourceDomain : SourceDomain enclosingOpen := ⟨by cbv, by cbv⟩

theorem enclosingOpen_hostBuilt_refused : ¬ SourceDomain enclosingOpenHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull enclosingOpenHostBuilt = false by cbv] at this; cases this

#guard (match runResult enclosingOpen with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `F(y) = { open Lib.Sub, Other ⏎ Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 } ⏎ Other = { public X = 2 } ⏎ A = X + 0 ⏎ A }`, inside `F(y)` / `F(5)`:
    an enclosing open target that does not provide the name. `A` is local-only on `y`. -/
def enclosingUnusedOpen : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "Other"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "X" (alg [] [] [] [.num 2])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-fix front end's tree of the same source, with `A` exported. -/
def enclosingUnusedOpenHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "Other"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "X" (alg [] [] [] [.num 2])] []), privateProp "A" (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem enclosingUnusedOpen_sourceDomain : SourceDomain enclosingUnusedOpen := ⟨by cbv, by cbv⟩

theorem enclosingUnusedOpen_hostBuilt_refused : ¬ SourceDomain enclosingUnusedOpenHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull enclosingUnusedOpenHostBuilt = false by cbv] at this; cases this

#guard (match runResult enclosingUnusedOpen with | .ok (.atom 2) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 }`, `A = Lib.Sub.Q + 0`, inside `F(y)` / `F(5)`:
    the review's source tree: both selections charged. -/
def intermediateSource : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Q" none) (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem intermediateSource_sourceDomain : SourceDomain intermediateSource := ⟨by cbv, by cbv⟩

#guard (match runResult intermediateSource with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `Lib = { public Q = 1 ⏎ y }`, `L = Lib`, `A = L.Q + 0`, inside `F(y)` / `F(5)`:
    a member-less reference to a lexically found name: its VALUE is not read, `A` stays exported. -/
def valueOnlyReference : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Lib" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.resolve "Lib"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem valueOnlyReference_sourceDomain : SourceDomain valueOnlyReference := ⟨by cbv, by cbv⟩

#guard (match runResult valueOnlyReference with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `B = { public Q = 1 ⏎ y + 0 }`, `A = B.Q + 0`, inside `F(y)` / `F(5)`:
    a name head whose member is selected: `A` stays exported. -/
def namedMemberOnly : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "B" (.localCapturedAncestorParams ["y"]) (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.resolve "B") "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem namedMemberOnly_sourceDomain : SourceDomain namedMemberOnly := ⟨by cbv, by cbv⟩

#guard (match runResult namedMemberOnly with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `A = { public Q = 1 ⏎ y + 0 }.Q + 0`, inside `F(y)` / `F(5)`:
    the block-head relaxation: the block's VALUE is not read, `A` is exported. -/
def blockHeadRelaxed : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.algorithmExpr (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [(.binary .add (.param "y") (.num 0))])) "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem blockHeadRelaxed_sourceDomain : SourceDomain blockHeadRelaxed := ⟨by cbv, by cbv⟩

#guard (match runResult blockHeadRelaxed with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open L, Other`, `L = y`, `Other = { public Q = 1 }`,
    `A = Q + 0`, inside `F(y)` / `F(5)`: opening a RUNTIME reference charges nothing (owner decision 3,
    2026-11-13). `openStructure` opens `L`'s own namespace — `structureOf`'s open mode gives a non-static target
    the reference itself with an empty trail — so the walk of `F`'s opens selects nothing and `A` stays exported.
    The access-checks candidate's over-charged tree (`A` local-only on `y`) is sound and needs no refusal. -/
def runtimeReferenceOpen : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "L", .resolve "Other"] [{ (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "Other" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] []), privateProp "A" (alg [] [] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem runtimeReferenceOpen_sourceDomain : SourceDomain runtimeReferenceOpen := ⟨by cbv, by cbv⟩

#guard (match runResult runtimeReferenceOpen with | .ok (.atom 1) => true | _ => false)

/-- Host-built (the F1 review): `intermediateSource` with `A`'s requirement removed. Every selection of
    `Lib.Sub.Q` is charged, so the missing `Sub` requirement is detected. -/
def intermediateCorrupt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "A" (alg [] [] [] [(.binary .add (.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Q" none) (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem intermediateCorrupt_refused : ¬ SourceDomain intermediateCorrupt :=
  fun h => by have := h.exposed; rw [show exposureFull intermediateCorrupt = false by cbv] at this; cases this

end AccessChecks

end KatLang.NavigationSourceDomainGuards
