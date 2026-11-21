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
* `ModuleProviders` (end of the module) — a loaded module is ONE open provider wherever it is
  reached: the model's selection beside production's on every route, and a reader whose requirement
  comes only from the walk of an open level that two holders of one module decide, refused when
  that requirement is removed (E-18 model correction, 2026-11-18).
* `ReferenceRootCut` (end of the module) — a loaded module whose ROOT is an alias is rooted at the
  prelude like any module: a name its holder also declares is the module's own, as in production,
  beside the ordinary alias twin that reads the holder's (E-18 model correction, 2026-11-19). Two
  SOURCE trees the model formerly refused (a module whose one row is an alias target), and host-built
  transparent-reference roots.
* `SharedProviders` (end of the module) — a declaration with a supplied `shared` identity is one open
  provider under one declaring scope outside a module too (same correction, optional part).

## 2. Source trees inside the domain (`OutsideContainer`, `EscapedContainer`, `FrontEnd`, `SelectionGaps`, `SelectionRoutes`, `AccessChecks`, `ModuleProviders`)

The two reached-state fixtures, five public-entry guards, the four `FrontEnd` programs, the three
`SelectionGaps` sources, the eight `SelectionRoutes` sources and the ten `AccessChecks` sources below
are the C# front end's own elaborated trees of the quoted sources, encoded by `LeanAstEncoder`.
Maintained C# fidelity tests check those thirty-two encodings (`NavigationSourceDomainWitnessTests`;
`moduleCut` through the asynchronous front end with its loaded module). Each is in `SourceDomain`; the `ExposureFragment`
and `OpenedFragment` examples and every `Exported` / host-built counterfactual are intentionally
host-corrupted. The same tests check the twelve `ModuleProviders` encodings through the asynchronous
front end: eight verbatim, and four whose source reads an ambiguous name (a front-end error), encoded
from the same source with the output row `1` and that row replaced. They check the two
`ReferenceRootCut` source encodings (`carrierMember`, `carrierRow`) the same way, and that each
host-built twin of those is the encoding with the documented single replacement.

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
    (navAdmits (.resolveAliasChase false true wiredQ ctxIn [] none) mid = true) ∧
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
    (navAdmits (.resolveAliasChase false true wiredQ ctxIn [] none) mid = true) ∧
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

/-! ## Check sites and impossible checks (E-18 F1, owner decisions Q1–Q3, 2026-11-14)

Each access check is charged at the site the evaluator makes it, and a check that can never pass
there requires nothing. One source program per rule:

* `openCrossingInside`: a reference opened INSIDE `Mid`'s activation is walked from the consulted
  level, so `Sub` (which needs `Mid`'s `p`) is selected there and the reader requires `p` (Q2). The
  same tree with the reader exported is refused.
* `valueCrossingOutside`: a VALUE read through the reference walks its target in the reference's own
  scope, outside `Mid`. That check can never pass, so the reader requires nothing (Q1, Q2); the read
  sits in a branch that does not run.
* `consultedOutside`: an `open` written on `F`, outside `Mid`, is checked on `F`, whoever reads
  through it: the reader inside `Mid` requires nothing, and the run fails at `Sub`.
* `untakenImpossible`: `F.A` written outside `F` can never be read; in an untaken branch it is no
  requirement of the algorithm around it (Q1).
* `staticPrefixRuntimeOpen`: opening `L = Lib.Sub.Algorithm` checks `Sub` before the runtime link, so
  the reader requires `y`; the same tree with the reader exported is refused (the C1/I28 review's
  counterexample: the runtime end of a walk keeps the checks of its static prefix).
* `blockHeadedOpen`: a block-headed reference is opened like a named one, so the reader requires what
  the provided member requires (Q3); the same tree with the reader exported is refused.

The C# fidelity tests are `NavigationSourceDomainWitnessTests` (scope `CheckSites`) and
`ExposureAccessCheckTests`.
-/

namespace CheckSites

/-- `LeanAstEncoder`'s encoding of the front end's tree of `L = Lib.Mid.Sub`, `Lib = { public Mid(p) = { public Sub = { public Q = 1 ⏎ p } ⏎ B(z) = { open L ⏎ Q + 0 } ⏎ B(0) } ⏎ 0 }`, `Lib.Mid(y)`, inside `F(y)` / `F(5)`:
    an open crossing inside `Mid`. `B` is local-only on `p`. -/
def openCrossingInside : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "L" (.alias none [] [] ((.dotCall (.dotCall (.resolve "Lib") "Mid" none) "Sub" none))), privateProp "Lib" (alg [] [] [publicProp "Mid" (alg ["p"] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["p"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "p") none false)) with requiredOwnerDepths := some [("p", some 0)] }, { (privateLocalProp "B" (.localCapturedAncestorParams ["p"]) (alg ["z"] [.resolve "L"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("p", some 0)] }] [(.call (.resolve "B") [.num 0])])] [.num 0])] [(.dotCall (.resolve "Lib") "Mid" (some [.param "y"]))])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `B` exported. -/
def openCrossingInsideHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "L" (.alias none [] [] ((.dotCall (.dotCall (.resolve "Lib") "Mid" none) "Sub" none))), privateProp "Lib" (alg [] [] [publicProp "Mid" (alg ["p"] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["p"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "p") none false)) with requiredOwnerDepths := some [("p", some 0)] }, privateProp "B" (alg ["z"] [.resolve "L"] [] [(.binary .add (.resolve "Q") (.num 0))])] [(.call (.resolve "B") [.num 0])])] [.num 0])] [(.dotCall (.resolve "Lib") "Mid" (some [.param "y"]))])] [(.call (.resolve "F") [.num 5])])

theorem openCrossingInside_sourceDomain : SourceDomain openCrossingInside := ⟨by cbv, by cbv⟩

theorem openCrossingInside_hostBuilt_refused : ¬ SourceDomain openCrossingInsideHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull openCrossingInsideHostBuilt = false by cbv] at this; cases this

#guard (match runResult openCrossingInside with | .ok (.atom 1) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `L = Lib.Mid.Sub` (the same `Lib`, with no reader inside `Mid`), `Box = { public A = if(false, L.Q + 0, 7) }`, `Box.A`, inside `F(y)` / `F(5)`:
    a value crossing checked in `L`'s own scope, outside `Mid`. `A` is exported. -/
def valueCrossingOutside : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [privateProp "L" (.alias none [] [] ((.dotCall (.dotCall (.resolve "Lib") "Mid" none) "Sub" none))), privateProp "Lib" (alg [] [] [publicProp "Mid" (alg ["p"] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["p"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "p") none false)) with requiredOwnerDepths := some [("p", some 0)] }] [.num 0])] [.num 0]), privateProp "Box" (alg [] [] [publicProp "A" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.binary .add (.dotCall (.resolve "L") "Q" none) (.num 0)), .num 7])])] [])] [(.dotCall (.resolve "Box") "A" none)])] [(.call (.resolve "F") [.num 5])])

theorem valueCrossingOutside_sourceDomain : SourceDomain valueCrossingOutside := ⟨by cbv, by cbv⟩

#guard (match runResult valueCrossingOutside with | .ok (.atom 7) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open Lib.Mid.Sub` written on `F`, with the reader `A(z) = Q + 0` inside `Mid` / `F(5)`:
    the consulted level is outside `Mid`. `A` is exported, and the run fails at `Sub`. -/
def consultedOutside : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [(.dotCall (.dotCall (.resolve "Lib") "Mid" none) "Sub" none)] [privateProp "Lib" (alg [] [] [publicProp "Mid" (alg ["p"] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["p"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "p") none false)) with requiredOwnerDepths := some [("p", some 0)] }, privateProp "A" (alg ["z"] [] [] [(.binary .add (.resolve "Q") (.num 0))])] [(.call (.resolve "A") [.num 0])])] [.num 0])] [(.dotCall (.resolve "Lib") "Mid" (some [.param "y"]))])] [(.call (.resolve "F") [.num 5])])

theorem consultedOutside_sourceDomain : SourceDomain consultedOutside := ⟨by cbv, by cbv⟩

#guard (match runResult consultedOutside with
  | .error e => (match innermost e with | .localOnlyProperty _ "Sub" _ => true | _ => false)
  | .ok _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `F(y) = { A = y + 1 ⏎ A }`, `Box = { public R = if(false, F.A, 0) }` / `Box.R`:
    an impossible read in a branch that does not run. `R` is exported. -/
def untakenImpossible : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Box" (alg [] [] [publicProp "R" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.dotCall (.resolve "F") "A" none), .num 0])])] []), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 1))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.dotCall (.resolve "Box") "R" none)])

theorem untakenImpossible_sourceDomain : SourceDomain untakenImpossible := ⟨by cbv, by cbv⟩

#guard (match runResult untakenImpossible with | .ok (.atom 0) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open L, Other`, `L = Lib.Sub.Algorithm`, `Lib = { public Sub = { public Q = 1 ⏎ y } ⏎ 0 }`, `Other = { public Z = 2 }`, `A = Z + 0`, inside `F(y)` / `F(5)`:
    the static prefix of a runtime open. `A` is local-only on `y`. -/
def staticPrefixRuntimeOpen : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "L", .resolve "Other"] [{ (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "Z" (alg [] [] [] [.num 2])] []), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "Z") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the same tree with `A` exported (the review's counterexample of 2026-11-14). -/
def staticPrefixRuntimeOpenHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "L", .resolve "Other"] [{ (privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (.alias none [] [] ((.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Algorithm" none)))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (.alias none [] [publicProp "Q" (alg [] [] [] [.num 1])] (.param "y") none false)) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "Other" (alg [] [] [publicProp "Z" (alg [] [] [] [.num 2])] []), privateProp "A" (alg [] [] [] [(.binary .add (.resolve "Z") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem staticPrefixRuntimeOpen_sourceDomain : SourceDomain staticPrefixRuntimeOpen := ⟨by cbv, by cbv⟩

theorem staticPrefixRuntimeOpen_hostBuilt_refused : ¬ SourceDomain staticPrefixRuntimeOpenHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull staticPrefixRuntimeOpenHostBuilt = false by cbv] at this; cases this

#guard (match runResult staticPrefixRuntimeOpen with | .ok (.atom 2) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open L`, `L = { public Sub = { public Q = y ⏎ 0 } }.Sub`, `A = Q + 0`, inside `F(y)` / `F(5)`:
    a block-headed reference opened like a named one. `A` is local-only on `y`. -/
def blockHeadedOpen : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "L" (.alias none [] [] ((.dotCall (.algorithmExpr (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 3)] }] [.num 0])] [])) "Sub" none))), { (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

/-- Host-built: the pre-Q3 front end's tree of the same source, with `A` exported. -/
def blockHeadedOpenHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [.resolve "L"] [privateProp "L" (.alias none [] [] ((.dotCall (.algorithmExpr (alg [] [] [publicProp "Sub" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 3)] }] [.num 0])] [])) "Sub" none))), privateProp "A" (alg [] [] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] [(.call (.resolve "F") [.num 5])])

theorem blockHeadedOpen_sourceDomain : SourceDomain blockHeadedOpen := ⟨by cbv, by cbv⟩

theorem blockHeadedOpen_hostBuilt_refused : ¬ SourceDomain blockHeadedOpenHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull blockHeadedOpenHostBuilt = false by cbv] at this; cases this

#guard (match runResult blockHeadedOpen with | .ok (.atom 5) => true | _ => false)

end CheckSites

/-! ## One loaded module is one open provider (E-18 model correction, 2026-11-18)

A loaded module is ONE declaration wherever it is held or written (`PropertyIdentity.module`, Q-32
I-U), so `resolveAllOpens` counts every reach of it as one provider (`sameRepeatedCallableIdentity`):
two holders, a holder and a written `load`, a member of it reached through either, a transparent
reference to one of those. The model keyed every declaration by its POSITION, so two holders were two
providers: it selected nothing where production selects the member, and required nothing of the
reader. `Located.providerKey` compares module roots by token and shared descendants in their
declaring scopes. `openedAt` compares the providers before looking up the name.

Selection — `rootSelection`, the model's decision for the root's read of `X`, beside production's:

* `twoHolders`, `holderAndWrittenLoad`, `memberHolder`, `descendant`, `descendantReference`,
  `writtenLoadDescendant`: one provider. The member is selected through the FIRST reach (its location
  is that holder's), after the walk of every target, a repeated reach's included.
* `twoModules`, `twoModuleDescendants` (two canonical URLs, equal bytes), `distinctDescendants` (two
  declarations of one module) and `writtenBlocks` (two written blocks): two providers. Nothing is
  selected, as before, and production answers `ambiguousOpen`.
* `failingTarget`: a target that fails beside a repeated provider fails the level.
* Host-built identities (the encoder emits none of them from source): `twoViews` — two views of one
  module declaration are one provider (`PropertyIdentity.callableDeclaration` erases the own view) —
  `viewDescendants` — their members are two (`sameDeclaringScope` keeps a declaring scope's view) —
  `referenceTargets` — so are the targets of a reference-rooted module's two views — and
  `sharedMember` — two providers that provide one module as their member are two (providers are
  counted, never members).

Exposure — `captureWitness`: `R` reads `X` through `F`'s opens `Lib.Sub, A, B`. Production resolves all
three targets, checks `Sub` (which needs `F`'s `y`) and selects the one module's `X`, so `R` requires
`y`; the front end marks it so. `captureWitnessHostBuilt` is that tree with `R`'s requirement removed.
The baseline model admitted it (two providers selected nothing, so the walk of `Lib.Sub` was never
charged); the model now refuses it, and production shows what the missing requirement costs: `F(7),
F.R` reads `R` outside the call from the call's cache entry. `captureTwoModulesHostBuilt`, the same
copy over two module identities, is still admitted: nothing is selected there. `selfNested` is the
same reader INSIDE a module (host-built), where the module's level is on the reader's own stack.

Each `def` documented as `LeanAstEncoder`'s encoding is checked against the asynchronous front end's
own tree by `NavigationSourceDomainWitnessTests` (`ModuleProviderWitness_*`,
`ModuleProviderCaptureWitness_*`); the same tests check that the two host-built copies of the capture
witness are its encoding with `R`'s property replaced and nothing else.
-/

namespace ModuleProviders

/-- What the model decides for a name an `open` provides. -/
inductive Selection where
  /-- One provider: the selected member's key, the keys of the declarations access-checked on the
      way, and the property each level of the member's declaring stack is the body of. -/
  | member (key : List String) (trail : List (List String)) (declaredIn : List (Option Ident))
  /-- No selection: no provider, two or more (`ambiguousOpen`), or a failing target. -/
  | nothing
  /-- Not decided statically (`runtime`, `stuck`). -/
  | undecided
  deriving BEq

/-- The model's decision for the read of `X` written at the program root. -/
def rootSelection (program : Expr) : Selection :=
  match program with
  | .algorithmExpr a =>
      let root := levelOf [] none a
      match openedAt [root] (selFuel [root] (.resolve "X")) "X" [root] (readerMap [root] 0) with
      | .found h => .member h.loc.key (h.trail.map (·.key)) (h.loc.stack.map (·.self))
      | .miss _ => .nothing
      | _ => .undecided
  | _ => .undecided

/-- Production's `ambiguousOpen` for `X`. -/
def ambiguousX (program : Expr) : Bool :=
  match runResult program with
  | .error e => (match innermost e with | .ambiguousOpen "X" _ => true | _ => false)
  | .ok _ => false

/-- Production refuses the open target `Lib.Sub`: its member `Sub` needs an activation the reading
    context cannot use. Since EXPORTED-DETACHED (November 2026) that is the outcome of every witness
    below whose reader `R` is marked exported: `R` is evaluated detached from the call around it, and
    the open walk that looks `X` up checks `Lib.Sub`, which needs that call's `y`. -/
def refusesSub (program : Expr) : Bool :=
  match runResult program with
  | .error e => (match innermost e with | .localOnlyProperty "Lib" "Sub" _ => true | _ => false)
  | .ok _ => false

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open A, B` / `A = load('x.kat')` /
    `B = load('x.kat')` / `X`, the module `public X = 5`: two holders of one module. -/
def twoHolders : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] []))] [.resolve "X"])

#guard rootSelection twoHolders == .member ["A", "X"] [["A", "X"]] [some "A"]
#guard (match runResult twoHolders with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open A, load('x.kat')` / `A = load('x.kat')` / `X`:
    a holder and a written `load` of one module. -/
def holderAndWrittenLoad : Expr :=
  .algorithmExpr (alg [] [.resolve "A", (.algorithmExpr (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])))] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] []))] [.resolve "X"])

#guard rootSelection holderAndWrittenLoad == .member ["A", "X"] [["A", "X"]] [some "A"]
#guard (match runResult holderAndWrittenLoad with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open Box.M, A` / `Box = { public M = load('x.kat') }` /
    `A = load('x.kat')` / `X`: the module held by a MEMBER of a container, and by a holder. The step
    `M` is access-checked on the way. -/
def memberHolder : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "Box") "M" none), .resolve "A"] [privateProp "Box" (alg [] [] [publicProp "M" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] []))] []), privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] []))] [.resolve "X"])

#guard rootSelection memberHolder == .member ["Box", "M", "X"] [["Box", "M"], ["Box", "M", "X"]] [some "M"]
#guard (match runResult memberHolder with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open A.Sub, B.Sub` / `A = load('sub.kat')` /
    `B = load('sub.kat')` / `X`, the module `public Sub = { public X = 5 }`: one member of one module
    through both holders. Both targets are walked; the member is the first reach's. -/
def descendant : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "Sub" none), (.dotCall (.resolve "B") "Sub" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] []))] [.resolve "X"])

#guard rootSelection descendant ==
  .member ["A", "Sub", "X"] [["A", "Sub"], ["B", "Sub"], ["A", "Sub", "X"]] [some "Sub", some "A"]
#guard (match runResult descendant with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open A.Sub, L` / `A = load('sub.kat')` /
    `B = load('sub.kat')` / `L = B.Sub` / `X`: a transparent reference to the other holder's route. -/
def descendantReference : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "Sub" none), .resolve "L"] [privateProp "A" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] [])), privateProp "L" (.alias none [] [] ((.dotCall (.resolve "B") "Sub" none)))] [.resolve "X"])

#guard rootSelection descendantReference ==
  .member ["A", "Sub", "X"] [["A", "Sub"], ["B", "Sub"], ["A", "Sub", "X"]] [some "Sub", some "A"]
#guard (match runResult descendantReference with | .ok (.atom 5) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of `open load('sub.kat').Sub, A.Sub` /
    `A = load('sub.kat')` / `X`: the member through a written `load` head and through a holder. -/
def writtenLoadDescendant : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.algorithmExpr (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] []))) "Sub" none), (.dotCall (.resolve "A") "Sub" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] []))] [.resolve "X"])

#guard rootSelection writtenLoadDescendant ==
  .member ["#open0", "Sub", "X"] [["#open0", "Sub"], ["A", "Sub"], ["#open0", "Sub", "X"]] [some "Sub", none]
#guard (match runResult writtenLoadDescendant with | .ok (.atom 5) => true | _ => false)

theorem oneModule_sourceDomain :
    SourceDomain twoHolders ∧ SourceDomain holderAndWrittenLoad ∧ SourceDomain memberHolder ∧
      SourceDomain descendant ∧ SourceDomain descendantReference ∧ SourceDomain writtenLoadDescendant :=
  ⟨⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩⟩

/-- `open A, B` / `A = load('x.kat')` / `B = load('y.kat')` / `X`, two canonical URLs serving the bytes
    `public X = 5`: `LeanAstEncoder`'s encoding of the front end's tree of the same source with the
    output row `1`, that row replaced by `X` (the front end refuses the read: `AmbiguousOpen`). -/
def twoModules : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" (Algorithm.withDeclarationId (some (.module 0)) (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] []))] [.resolve "X"])

#guard rootSelection twoModules == .nothing
#guard ambiguousX twoModules

/-- `open A.Sub, B.Sub` / `A = load('sub.kat')` / `B = load('sub2.kat')` / `X`, two canonical URLs serving
    the bytes `public Sub = { public X = 5 }`: the encoding of the source with the output row `1`,
    that row replaced by `X`. -/
def twoModuleDescendants : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "Sub" none), (.dotCall (.resolve "B") "Sub" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.module 0)) (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] [])] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] [])] []))] [.resolve "X"])

#guard rootSelection twoModuleDescendants == .nothing
#guard ambiguousX twoModuleDescendants

/-- `open A.S1, B.S2` / `A = load('two.kat')` / `B = load('two.kat')` / `X`, the module
    `public S1 = { public X = 5 }` / `public S2 = { public X = 5 }`: the encoding of the source with the
    output row `1`, that row replaced by `X`. Two declarations of one module are two providers. -/
def distinctDescendants : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "S1" none), (.dotCall (.resolve "B") "S2" none)] [privateProp "A" (Algorithm.withDeclarationId (some (.module 4)) (alg [] [] [{ (publicProp "S1" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }, { (publicProp "S2" (Algorithm.withDeclarationId (some (.shared 3)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [.num 5]))) with identity := some (.shared 3) }] []))) with identity := some (.shared 2) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 4)) (alg [] [] [{ (publicProp "S1" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }, { (publicProp "S2" (Algorithm.withDeclarationId (some (.shared 3)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 2)) (alg [] [] [] [.num 5]))) with identity := some (.shared 3) }] []))) with identity := some (.shared 2) }] []))] [.resolve "X"])

#guard rootSelection distinctDescendants == .nothing
#guard ambiguousX distinctDescendants

/-- `open { public X = 5 }, { public X = 5 }` / `X`: the encoding of the source with the output row `1`,
    that row replaced by `X`. Two written blocks are two providers, keyed by position. -/
def writtenBlocks : Expr :=
  .algorithmExpr (alg [] [(.algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] [])), (.algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] []))] [] [.resolve "X"])

#guard rootSelection writtenBlocks == .nothing
#guard ambiguousX writtenBlocks

/-- The module `public X = 5` with declaration identity `id`, its member as the encoder marks it. -/
def xModule (id : PropertyIdentity) : Algorithm :=
  Algorithm.withDeclarationId (some id) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])

/-- The module `public Sub = { public X = 5 }` with declaration identity `id`. -/
def subModule (id : PropertyIdentity) : Algorithm :=
  Algorithm.withDeclarationId (some id) (alg [] [] [{ (publicProp "Sub" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }] [])

/-- Host-built: `twoHolders` with a third target `Missing` that no level declares. The level fails. -/
def failingTarget : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B", .resolve "Missing"]
    [privateProp "A" (xModule (.module 1)), privateProp "B" (xModule (.module 1))] [.resolve "X"])

#guard rootSelection failingTarget == .nothing
#guard (match runResult failingTarget with
  | .error e => (match innermost e with | .unknownName "Missing" => true | _ => false)
  | .ok _ => false)

/-- Host-built: two VIEWS of one module declaration, held by `A` and `B`. One provider. -/
def twoViews : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"]
    [privateProp "A" (xModule (.moduleView 1 1)), privateProp "B" (xModule (.moduleView 1 2))] [.resolve "X"])

#guard rootSelection twoViews == .member ["A", "X"] [["A", "X"]] [some "A"]
#guard (match runResult twoViews with | .ok (.atom 5) => true | _ => false)

/-- Host-built: `open A.Sub, B.Sub` over two views of one module declaration. A view is a declaring
    scope of its own, so the two `Sub` are two providers. -/
def viewDescendants : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "Sub" none), (.dotCall (.resolve "B") "Sub" none)]
    [privateProp "A" (subModule (.moduleView 2 1)), privateProp "B" (subModule (.moduleView 2 2))] [.resolve "X"])

#guard rootSelection viewDescendants == .nothing
#guard ambiguousX viewDescendants

/-- Host-built: the same targets over ONE view. One provider. -/
def sameViewDescendants : Expr :=
  .algorithmExpr (alg [] [(.dotCall (.resolve "A") "Sub" none), (.dotCall (.resolve "B") "Sub" none)]
    [privateProp "A" (subModule (.moduleView 2 1)), privateProp "B" (subModule (.moduleView 2 1))] [.resolve "X"])

#guard rootSelection sameViewDescendants ==
  .member ["A", "Sub", "X"] [["A", "Sub"], ["B", "Sub"], ["A", "Sub", "X"]] [some "Sub", some "A"]
#guard (match runResult sameViewDescendants with | .ok (.atom 5) => true | _ => false)

/-- Host-built: two written providers `P` and `Q` whose member `X` is one module. The PROVIDERS are
    two, although the member they provide is one declaration. -/
def sharedMember : Expr :=
  .algorithmExpr (alg [] [.resolve "P", .resolve "Q"]
    [privateProp "P" (alg [] [] [publicProp "X" (xModule (.module 1))] []),
     privateProp "Q" (alg [] [] [publicProp "X" (xModule (.module 1))] [])] [.dotCall (.resolve "X") "X" none])

#guard rootSelection sharedMember == .nothing
#guard ambiguousX sharedMember

/-- A module whose ROOT is a transparent reference to its own member `T = { public X = 5 }`, with
    declaration identity `id`. -/
def referenceModule (id : PropertyIdentity) : Algorithm :=
  .alias none []
    [{ (publicProp "T" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }]
    (.resolve "T") (some id) true

/-- Host-built: `open A, B` over two holders of `referenceModule`. The provider is the reference's
    TARGET, a member of the module: one under one view, two under two views. -/
def referenceTargets (a b : PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"]
    [privateProp "A" (referenceModule a), privateProp "B" (referenceModule b)] [.resolve "X"])

-- The member's key and trail; its location is the next guard's (since the reference-root cut of
-- 2026-11-19 the target is walked on the module's own level, and its chain ends at the module `A`).
#guard (match rootSelection (referenceTargets (.moduleView 1 1) (.moduleView 1 1)) with
  | .member key trail _ => key == ["A", "T", "X"] && trail == [["A", "T", "X"]]
  | _ => false)
#guard rootSelection (referenceTargets (.moduleView 1 1) (.moduleView 1 1)) ==
  .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A"]
#guard (match runResult (referenceTargets (.moduleView 1 1) (.moduleView 1 1)) with | .ok (.atom 5) => true | _ => false)
#guard rootSelection (referenceTargets (.moduleView 1 1) (.moduleView 1 2)) == .nothing
#guard ambiguousX (referenceTargets (.moduleView 1 1) (.moduleView 1 2))

/-- Host-built descendants with independent control of the member and parent identities. -/
private def openDescendants (a b : Algorithm) (path : List Ident) : Expr :=
  let target name := path.foldl (fun e step => Expr.dotCall e step none) (.resolve name)
  .algorithmExpr (alg [] [target "A", target "B"] [privateProp "A" a, privateProp "B" b] [.resolve "X"])

private def holding (parent : PropertyIdentity) (name : Ident) (member : Algorithm) : Algorithm :=
  (alg [] [] [publicProp name member] []).withDeclarationId (some parent)

private def subWithId (id : Option PropertyIdentity) : Algorithm :=
  (alg [] [] [publicProp "X" (alg [] [] [] [.num 5])] []).withDeclarationId id

private def memberPair (a b : Option PropertyIdentity) : Expr :=
  openDescendants (holding (.module 2) "Sub" (subWithId a)) (holding (.module 2) "Sub" (subWithId b)) ["Sub"]

-- Production assigns a fresh syntax id to each unmarked occurrence. The same member name under a
-- common module token cannot merge these declarations or override distinct explicit identities.
#guard rootSelection (memberPair none none) == .nothing
#guard ambiguousX (memberPair none none)
#guard rootSelection (memberPair (some (.shared 7)) (some (.shared 8))) == .nothing
#guard ambiguousX (memberPair (some (.shared 7)) (some (.shared 8)))

-- The provider's own view is erased even when it is a shared descendant of the module.
#guard rootSelection (memberPair (some (.sharedView 7 1)) (some (.sharedView 7 2))) == rootSelection descendant
#guard (match runResult (memberPair (some (.sharedView 7 1)) (some (.sharedView 7 2))) with
  | .ok (.atom 5) => true | _ => false)

private def innerView (view : Nat) : Algorithm :=
  holding (.module 2) "Inner" (holding (.sharedView 3 view) "Sub" (subWithId (some (.shared 1))))

-- A view at an intermediate declaring level participates in a deeper provider's identity.
#guard rootSelection (openDescendants (innerView 1) (innerView 2) ["Inner", "Sub"]) == .nothing
#guard ambiguousX (openDescendants (innerView 1) (innerView 2) ["Inner", "Sub"])
#guard (match rootSelection (openDescendants (innerView 1) (innerView 1) ["Inner", "Sub"]) with
  | .member key _ _ => key == ["A", "Inner", "Sub", "X"]
  | _ => false)
#guard (match runResult (openDescendants (innerView 1) (innerView 1) ["Inner", "Sub"]) with
  | .ok (.atom 5) => true | _ => false)

/-- Two written reaches of a module whose root is a transparent reference. -/
private def writtenReferenceModule : Expr :=
  let m := referenceModule (.module 3)
  .algorithmExpr (alg [] [.algorithmExpr m, .algorithmExpr m] [] [.resolve "X"])

#guard (match rootSelection writtenReferenceModule with
  | .member key _ _ => key == ["#open0", "T", "X"] | _ => false)
#guard (match runResult writtenReferenceModule with | .ok (.atom 5) => true | _ => false)

/-- A module carrier keeps its own `X` when reached as a written block and through a holder. -/
private def writtenCarrier : Expr :=
  let m := Algorithm.alias none [] [publicProp "X" (alg [] [] [] [.num 5]), privateProp "T" (alg [] [] [] [.num 9])]
    (.resolve "T") (some (.module 3)) false
  .algorithmExpr (alg [] [.algorithmExpr m, .resolve "A"] [privateProp "A" m] [.resolve "X"])

#guard rootSelection writtenCarrier == .member ["#open0", "X"] [["#open0", "X"]] [none]
#guard (match runResult writtenCarrier with | .ok (.atom 5) => true | _ => false)

/-- Chasing one view through a second occurrence of the same module token terminates at `Second.T`.
    Using the provider key as the cycle key would stop at `Second` and lose the member. -/
private def viewWalk : Expr :=
  let second := referenceModule (.moduleView 5 2)
  let first := Algorithm.alias none [] [privateProp "Second" second] (.resolve "Second") (some (.moduleView 5 1)) true
  .algorithmExpr (alg [] [.resolve "First"] [privateProp "First" first] [.resolve "X"])

#guard (match rootSelection viewWalk with
  | .member key _ _ => key == ["First", "Second", "T", "X"] | _ => false)
#guard (match runResult viewWalk with | .ok (.atom 5) => true | _ => false)

/-- Host-built module whose open list reaches `F.Sub` directly and through `L`. Neither target
    needs an input. The selected `Sub.X` requires `F`'s `y`, which is available at the reader
    `F.R` but absent from the consulted module level. Only the member's reader-site check can
    require this metadata on `R`. -/
private def readerSite (keepRequirement : Bool) : Expr :=
  let x := { (publicLocalProp "X" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [.param "y"]))
    with requiredOwnerDepths := some [("y", some 1)] }
  let sub := (alg [] [] [x] [.num 0]).withDeclarationId (some (.shared 1))
  let body := alg [] [] [] [.binary .add (.resolve "X") (.num 0)]
  let reader := if keepRequirement then
    { (privateLocalProp "R" (.localCapturedAncestorParams ["y"]) body) with requiredOwnerDepths := some [("y", some 0)] }
    else privateProp "R" body
  let f := (alg ["y"] [] [publicProp "Sub" sub, reader] [.resolve "R"]).withDeclarationId (some (.shared 2))
  let target := Expr.dotCall (.resolve "F") "Sub" none
  let m := (alg [] [target, .resolve "L"] [publicProp "F" f, privateProp "L" (.alias none [] [] target)] [])
    |>.withDeclarationId (some (.module 3))
  .algorithmExpr (alg [] [] [privateProp "M" m] [.dotCall (.resolve "M") "F" (some [.num 7])])

#guard exposureFull (readerSite true)
#guard !exposureFull (readerSite false)
#guard (match runResult (readerSite true) with | .ok (.atom 7) => true | _ => false)

/-- `LeanAstEncoder`'s encoding of the front end's tree of

        A = load('https://mods.test/x.kat')
        B = load('https://mods.test/x.kat')
        F(y) = {
          open Lib.Sub, A, B
          Lib = {
            public Sub = { y + 0 }
            0
          }
          R = X + 0
          R
        }
        F(7)

    with the module `public X = 5`. `R` reads `X` through `F`'s opens: every target is walked, `Sub`
    (which needs `y`) included, and the one module provides `X`. `R` is local-only on `y`. -/
def captureWitness : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "A", .resolve "B"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "R" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "R"])] [(.call (.resolve "F") [.num 7])])

/-- `LeanAstEncoder`'s encoding of the front end's tree of the same source with the output `F(7), F.R`. -/
def captureWitnessEscaped : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "A", .resolve "B"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), { (privateLocalProp "R" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "R"])] [(.call (.resolve "F") [.num 7]), (.dotCall (.resolve "F") "R" none)])

/-- Host-built: `captureWitness` with `R`'s requirement removed (`R` exported). -/
def captureWitnessHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "A", .resolve "B"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "R" (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])] [.resolve "R"])] [(.call (.resolve "F") [.num 7])])

/-- Host-built: `captureWitnessHostBuilt` with the output `F(7), F.R`. -/
def captureWitnessHostBuiltEscaped : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "A", .resolve "B"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "R" (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])] [.resolve "R"])] [(.call (.resolve "F") [.num 7]), (.dotCall (.resolve "F") "R" none)])

/-- Host-built: `captureWitnessHostBuilt` with `B` a second module identity of the same text (token 2).
    Two providers select nothing: `R` requires nothing. -/
def captureTwoModulesHostBuilt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "B" (Algorithm.withDeclarationId (some (.module 2)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 0) }] [])), privateProp "F" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "A", .resolve "B"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]), privateProp "R" (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])] [.resolve "R"])] [(.call (.resolve "F") [.num 7])])

theorem captureWitness_sourceDomain : SourceDomain captureWitness := ⟨by cbv, by cbv⟩

/-- **The model refuses the copy without `R`'s requirement** (the baseline model admitted it). -/
theorem captureWitness_hostBuilt_refused : ¬ SourceDomain captureWitnessHostBuilt :=
  fun h => by have := h.exposed; rw [show exposureFull captureWitnessHostBuilt = false by cbv] at this; cases this

/-- The control: over two module identities nothing is selected, and the same copy is admitted. -/
theorem captureTwoModules_hostBuilt_sourceDomain : SourceDomain captureTwoModulesHostBuilt := ⟨by cbv, by cbv⟩

#guard (match runResult captureWitness with | .ok (.atom 5) => true | _ => false)

-- Outside the call the source tree refuses `R` itself …
#guard (match runResult captureWitnessEscaped with
  | .error e => (match innermost e with | .localOnlyProperty _ "R" _ => true | _ => false)
  | .ok _ => false)

-- … while the copy without the requirement is refused INSIDE the call: production now refuses what
-- the model refuses. Formerly the call succeeded and `F.R` read its cache entry, `(5, 5)`.
#guard refusesSub captureWitnessHostBuiltEscaped

-- The admitted control fails either way. The model charges an ambiguous lookup nothing; production
-- formerly reached the ambiguity (`ambiguousOpen X`) and now refuses the walk's check of `Lib.Sub`
-- before it.
#guard refusesSub captureTwoModulesHostBuilt

/-! A module level on the reader's stack carries its declaration id too (`levelOf`). No source
reaches a module inside itself — the loader refuses a load cycle — so the tree below is host-built:
one member `S` of the module is a provider twice at an open level INSIDE the module, by the reader's
own stack (`S`) and through a holder `P` of the same token (`P.S`). Production counts one provider. -/

/-- The member `S = { public X = 5 }`, marked as the encoder marks a declaration reached twice. -/
def nestedS : PropDef :=
  { (publicProp "S" (Algorithm.withDeclarationId (some (.shared 1)) (alg [] [] [{ (publicProp "X" (Algorithm.withDeclarationId (some (.shared 0)) (alg [] [] [] [.num 5]))) with identity := some (.shared 1) }] []))) with identity := some (.shared 0) }

/-- Host-built: the module (token 0), held by `A`, of `S`, a holder `P` of the module token `inner`
    with the same `S`, `G(y) = { open Lib.Sub, S, P.S ⏎ Lib = { public Sub = { y + 0 } ⏎ 0 } ⏎ R = X + 0 ⏎ R }`
    and `public V` with the rows `output`; the program reads `A.V`. `R` is local-only on `y`
    (`localOnly`) or has that requirement removed. -/
def selfNested (inner : Nat) (localOnly : Bool) (output : List Expr) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (Algorithm.withDeclarationId (some (.module 0)) (alg [] []
    [nestedS,
     privateProp "P" (Algorithm.withDeclarationId (some (.module inner)) (alg [] [] [nestedS] [])),
     privateProp "G" (alg ["y"] [(.dotCall (.resolve "Lib") "Sub" none), .resolve "S", (.dotCall (.resolve "P") "S" none)]
       [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.param "y") (.num 0))])) with requiredOwnerDepths := some [("y", some 1)] }] [.num 0]),
        (if localOnly then
          { (privateLocalProp "R" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))])) with requiredOwnerDepths := some [("y", some 0)] }
        else privateProp "R" (alg [] [] [] [(.binary .add (.resolve "X") (.num 0))]))] [.resolve "R"]),
     publicProp "V" (alg [] [] [] output)] []))] [.dotCall (.resolve "A") "V" none])

/-- The rows `G(7)`. -/
def nestedCall : List Expr := [(.call (.resolve "G") [.num 7])]

/-- The rows `G(7), G.R`. -/
def nestedCallThenRead : List Expr := [(.call (.resolve "G") [.num 7]), .dotCall (.resolve "G") "R" none]

theorem selfNested_sourceDomain : SourceDomain (selfNested 0 true nestedCall) := ⟨by cbv, by cbv⟩

/-- One provider inside the module too: the copy without `R`'s requirement is refused. -/
theorem selfNested_hostBuilt_refused : ¬ SourceDomain (selfNested 0 false nestedCall) :=
  fun h => by have := h.exposed; rw [show exposureFull (selfNested 0 false nestedCall) = false by cbv] at this; cases this

/-- The control: `P` a second module identity. Two providers select nothing; the copy is admitted. -/
theorem selfNested_twoModules_sourceDomain : SourceDomain (selfNested 1 false nestedCall) := ⟨by cbv, by cbv⟩

#guard (match runResult (selfNested 0 true nestedCall) with | .ok (.atom 5) => true | _ => false)
#guard (match runResult (selfNested 0 true nestedCallThenRead) with
  | .error e => (match innermost e with | .localOnlyProperty _ "R" _ => true | _ => false)
  | .ok _ => false)
-- The copy without the requirement is refused inside the call (formerly `(5, 5)`), and so is the
-- admitted two-provider control (formerly `ambiguousOpen X`): `refusesSub`.
#guard refusesSub (selfNested 0 false nestedCallThenRead)
#guard refusesSub (selfNested 1 false nestedCall)

end ModuleProviders

/-! ## A loaded module is rooted at the prelude whatever its root is (E-18 model correction, 2026-11-19)

`Algorithm.withParent` re-parents a module-identified ALIAS onto the chain's root exactly as it
re-parents a module-identified block: a loaded module never sees a name of its holder. The model cut
the chain for a block root only (`chkAlg`, `collectAlg`, `memberOf`). A module whose root is a
transparent reference had its target walked on its HOLDER's stack (`structureOf`), so the model
selected a holder-level target where production answers `unknownName`; an alias root's row and
members were checked at the holder's levels. The chain is now cut at the module in all of them
(`Located.ownScope`).

SOURCE REACHES AN ALIAS ROOT. The front end elaborates a loaded module whose ONE ROW is a callable
alias target to an alias that keeps the module mark (C# `Algorithm.Alias.IsModuleElaborated`) — a
CARRIER, never a transparent reference (`Algorithm.Alias.IsReference` excludes a module body). So the
walkers' part of the cut concerns source trees: `carrierMember` and `carrierRow` are the front end's
own trees of two such programs. Both evaluators answer 5, the front end raises no diagnostic, and
the model formerly REFUSED both: it found the holder's declaration on the direct chain where the
module reads its own opened member. A module whose root is a TRANSPARENT REFERENCE is host-built
only; those fixtures, and the walker fixtures beside them, take the root's identity as a
parameter, so that the ORDINARY alias (no identity) and its MODULE twin are one tree that differs
in that slot only. The ordinary alias finds a target of its enclosing scope and the module twin
does not; this pair is what refuses a cut applied to every alias. Production's outcome is asserted
first, then the model's.

* Source (`carrierMember`, `carrierRow`): each in `SourceDomain`; its ordinary twin — the same tree
  without the module identity, where production reads the holder's declaration and answers 7 — is
  refused, and so is `carrierMemberExported`, the module's own reader host-corrupted to exported: the
  inside of an alias-rooted module is still checked.

* Open route (`open A` / `X`; the provider is read through `openStructure`): `openHolderTarget`,
  the target a declaration of the holder — the reported case — and `openOwnTarget`, the control with
  the target declared by the module itself beside a different holder `T`.
* Value route (the written path `A.X`; the receiver is read through the structure chase, whose head
  lookup is the FULL one): `valueHolderTarget` and `valueOwnTarget` as above; `valueHolderOpen`, the
  target a member only the HOLDER's `open` provides, and `valueOwnOpen`, the control whose module
  opens its own provider. Before the cut the holder's open level was consulted and its provider's
  walk was on the trail.
* The walkers: `rowReadsHolder` (the root's row names the holder's `Q`), `inlineRowReadsWriter` (the
  root written INLINE as a row, naming a member of the body it is written in) and
  `memberReadsHolder` (a member of the root names the holder's `Q`) require nothing of the holder
  when the root is a module, exactly as the block-rooted module `memberReadsHolderBlock` already
  did; `paramRow` (the root's row is the holder's parameter) is unbound there, as its block twin
  `paramRowBlock` already was.
-/

namespace ReferenceRootCut

open ModuleProviders (Selection rootSelection)

/-- Production answers the atom `n`. -/
def answers (n : Int) (program : Expr) : Bool :=
  match runResult program with
  | .ok (.atom value) => value == n
  | _ => false

/-- Production's `unknownName name`. -/
def unknownName (name : Ident) (program : Expr) : Bool :=
  match runResult program with
  | .error e => (match innermost e with | .unknownName found => found == name | _ => false)
  | .ok _ => false

/-- The model's decision for the written path `A.X` at the program root. -/
def pathSelection (program : Expr) : Selection :=
  let path := Expr.dotCall (.resolve "A") "X" none
  match program, Expr.staticAliasPath? path with
  | .algorithmExpr a, some (head, steps) =>
      let root := levelOf [] none a
      match walkPath [root] .value (selFuel [root] path) [] [root] (readerMap [root] 0) head steps
          (stackKey [root] ++ ["#block"]) with
      | .found h => .member h.loc.key (h.trail.map (·.key)) (h.loc.stack.map (·.self))
      | .miss _ => .nothing
      | _ => .undecided
  | _, _ => .undecided

/-- The three identities of a root: an ordinary alias, a module, a view of a module. -/
def ordinary : Option PropertyIdentity := none
def moduleRoot : Option PropertyIdentity := some (.module 1)
def moduleViewRoot : Option PropertyIdentity := some (.moduleView 1 1)

/-- `{ public X = n }`. -/
def xBlock (n : Int) : Algorithm := alg [] [] [publicProp "X" (alg [] [] [] [.num n])] []

/-- A transparent reference to `T` with the identity `id`, the members `props` and the opens `opens`. -/
def referenceToT (id : Option PropertyIdentity) (props : List PropDef := []) (opens : List Expr := []) : Algorithm :=
  .alias none opens props (.resolve "T") id true

/-! ### Source: a module whose one row is an alias target -/

/-- `LeanAstEncoder`'s encoding of the front end's tree (asynchronous, with the loaded module) of

        F(y) = {
          Q = y
          M = load('https://mods.test/carrier.kat')
          M.V + 0
        }
        F(7)

    where the module is `SelectionRoutes.moduleCut`'s with the one row `V` added:
    `G(k) = { Lib = { public Q = k ⏎ 1 } ⏎ A = { open Lib ⏎ Q + 0 } ⏎ A }` `⏎ public V = G(5)` `⏎ V`.
    The module's root is an ALIAS (a carrier). Inside it `Q` is `Lib.Q`, through `A`'s open, and
    requires the module's `k`; it is not the holder's `Q`. (Before the cut the model walked the
    root's members at the holder's levels, selected the holder's `Q` on the direct chain and
    REFUSED this source tree.) -/
def carrierMember : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (.alias none [] [publicProp "V" (alg [] [] [] [(.call (.resolve "G") [.num 5])]), privateProp "G" (alg ["k"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["k"]) (.alias none [] [] (.param "k"))) with requiredOwnerDepths := some [("k", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["k"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("k", some 0)] }] [.resolve "A"])] (.resolve "V") none false))] [(.binary .add (.dotCall (.resolve "M") "V" none) (.num 0))])] [(.call (.resolve "F") [.num 7])])

/-- Host-built: `carrierMember` without the module identity, an ordinary carrier at the same place.
    Its members are declared under `F`, so `Q` is the holder's. -/
def carrierMemberOrdinary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" ((.alias none [] [publicProp "V" (alg [] [] [] [(.call (.resolve "G") [.num 5])]), privateProp "G" (alg ["k"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["k"]) (.alias none [] [] (.param "k"))) with requiredOwnerDepths := some [("k", some 1)] }] [.num 1]), { (privateLocalProp "A" (.localCapturedAncestorParams ["k"]) (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])) with requiredOwnerDepths := some [("k", some 0)] }] [.resolve "A"])] (.resolve "V") none false))] [(.binary .add (.dotCall (.resolve "M") "V" none) (.num 0))])] [(.call (.resolve "F") [.num 7])])

/-- Host-built: `carrierMember` with the module's `A` host-corrupted to exported. -/
def carrierMemberExported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (.alias none [] [publicProp "V" (alg [] [] [] [(.call (.resolve "G") [.num 5])]), privateProp "G" (alg ["k"] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "Q" (.localCapturedAncestorParams ["k"]) (.alias none [] [] (.param "k"))) with requiredOwnerDepths := some [("k", some 1)] }] [.num 1]), privateProp "A" (alg [] [.resolve "Lib"] [] [(.binary .add (.resolve "Q") (.num 0))])] [.resolve "A"])] (.resolve "V") none false))] [(.binary .add (.dotCall (.resolve "M") "V" none) (.num 0))])] [(.call (.resolve "F") [.num 7])])

/-- `LeanAstEncoder`'s encoding of the front end's tree (asynchronous, with the loaded module) of

        F(y) = {
          W = y
          M = load('https://mods.test/opened.kat')
          M + 0
        }
        F(7)

    where the module is `open Lib` `⏎ Lib = { public W = 5 }` `⏎ W`: its root is an alias whose .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "W" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (.alias none [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "W" (alg [] [] [] [.num 5])] [])] (.resolve "W") none false))] [(.binary .add (.resolve "M") (.num 0))])] [(.call (.resolve "F") [.num 7])])
    names a member only the module's OWN open provides. The row is not the holder's `W`, and `M`
    requires nothing of `F`. (Before the cut the model collected the root's row at the holder's
    levels, charged `M` the holder's `y` and REFUSED this source tree.) -/
def carrierRow : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "W" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" (Algorithm.withDeclarationId (some (.module 0)) (.alias none [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "W" (alg [] [] [] [.num 5])] [])] (.resolve "W") none false))] [(.binary .add (.resolve "M") (.num 0))])] [(.call (.resolve "F") [.num 7])])

/-- Host-built: `carrierRow` without the module identity. Its row is the holder's `W`. -/
def carrierRowOrdinary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] [] [{ (privateLocalProp "W" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y"))) with requiredOwnerDepths := some [("y", some 0)] }, privateProp "M" ((.alias none [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "W" (alg [] [] [] [.num 5])] [])] (.resolve "W") none false))] [(.binary .add (.resolve "M") (.num 0))])] [(.call (.resolve "F") [.num 7])])

theorem carrierMember_sourceDomain : SourceDomain carrierMember := ⟨by cbv, by cbv⟩

theorem carrierRow_sourceDomain : SourceDomain carrierRow := ⟨by cbv, by cbv⟩

/-- The ordinary carrier's reader `A` reads the holder's `Q` and declares only `k`: refused. -/
theorem carrierMember_ordinary_refused : ¬ SourceDomain carrierMemberOrdinary :=
  fun h => by have := h.exposed; rw [show exposureFull carrierMemberOrdinary = false by cbv] at this; cases this

/-- The ordinary carrier's row is the holder's `W`, which requires `y`; `M` is exported: refused. -/
theorem carrierRow_ordinary_refused : ¬ SourceDomain carrierRowOrdinary :=
  fun h => by have := h.exposed; rw [show exposureFull carrierRowOrdinary = false by cbv] at this; cases this

/-- The inside of an alias-rooted module is still checked: its reader without its requirement is refused. -/
theorem carrierMember_exported_refused : ¬ SourceDomain carrierMemberExported :=
  fun h => by have := h.exposed; rw [show exposureFull carrierMemberExported = false by cbv] at this; cases this

-- Production: the module reads its own opened member. The ordinary carrier's ROW is its holder's `W`,
-- a reference that owns no cache entry and is chased where it is read. Its MEMBER reader `A` is a
-- property the model refuses as exported, and production refuses it too (EXPORTED-DETACHED): evaluated
-- detached from `F`'s call, its read of the holder's `y` finds no binding (formerly 7).
#guard answers 5 carrierMember
#guard answers 5 carrierRow
#guard unknownName "y" carrierMemberOrdinary
#guard answers 7 carrierRowOrdinary

/-! ### Open route -/

/-- Host-built: `open A` / `T = { public X = 5 }` / `A` a reference to `T`, which only its HOLDER
    declares / `X`. -/
def openHolderTarget (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.resolve "A"]
    [privateProp "T" (xBlock 5), privateProp "A" (referenceToT id)] [.resolve "X"])

/-- Host-built: the same with `T = { public X = 5 }` declared by `A` ITSELF, beside a holder
    `T = { public X = 9 }`. -/
def openOwnTarget (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.resolve "A"]
    [privateProp "T" (xBlock 9), privateProp "A" (referenceToT id [publicProp "T" (xBlock 5)])] [.resolve "X"])

-- Production: the ordinary alias finds its enclosing scope's `T`; the module twin does not.
#guard answers 5 (openHolderTarget ordinary)
#guard unknownName "T" (openHolderTarget moduleRoot)
#guard unknownName "T" (openHolderTarget moduleViewRoot)

-- The model: the same. (Before the cut it selected `T.X` for all three.)
#guard rootSelection (openHolderTarget ordinary) == .member ["T", "X"] [["T", "X"]] [some "T", none]
#guard rootSelection (openHolderTarget moduleRoot) == .nothing
#guard rootSelection (openHolderTarget moduleViewRoot) == .nothing

-- The control: a target the root declares itself is found by all three, and never the holder's `T`.
#guard answers 5 (openOwnTarget ordinary)
#guard answers 5 (openOwnTarget moduleRoot)
#guard answers 5 (openOwnTarget moduleViewRoot)
#guard rootSelection (openOwnTarget ordinary) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A", none]
-- The module's member is declared in a chain that ends at the module.
#guard rootSelection (openOwnTarget moduleRoot) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A"]
#guard rootSelection (openOwnTarget moduleViewRoot) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A"]

/-- The positions on the reader's stack of the levels the selected member is declared in
    (`Located.map`): one per level of its declaring chain. -/
def rootPositions (program : Expr) : Option (List (Option Nat)) :=
  match program with
  | .algorithmExpr a =>
      let root := levelOf [] none a
      match openedAt [root] (selFuel [root] (.resolve "X")) "X" [root] (readerMap [root] 0) with
      | .found h => some h.loc.map
      | _ => none
  | _ => none

-- The positions are cut with the chain: the ordinary alias's member sits under the root level (the
-- reader's own, position 0); the module's has no level of its holder to count a requirement at.
#guard rootPositions (openOwnTarget ordinary) == some [none, none, some 0]
#guard rootPositions (openOwnTarget moduleRoot) == some [none, none]
#guard rootPositions (openOwnTarget moduleViewRoot) == some [none, none]

/-! ### Value route -/

/-- Host-built: `T = { public X = 5 }` / `A` a reference to the holder's `T` / `A.X`. -/
def valueHolderTarget (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (xBlock 5), privateProp "A" (referenceToT id)]
    [.dotCall (.resolve "A") "X" none])

/-- Host-built: the same with `T` declared by `A` itself, beside a holder `T = { public X = 9 }`. -/
def valueOwnTarget (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (xBlock 9), privateProp "A" (referenceToT id [publicProp "T" (xBlock 5)])]
    [.dotCall (.resolve "A") "X" none])

/-- Host-built: `open Lib` / `Lib = { public T = { public X = 5 } }` / `A` a reference to `T`, which
    only the HOLDER's `open` provides / `A.X`. -/
def valueHolderOpen (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.resolve "Lib"]
    [privateProp "Lib" (alg [] [] [publicProp "T" (xBlock 5)] []), privateProp "A" (referenceToT id)]
    [.dotCall (.resolve "A") "X" none])

/-- Host-built: the same with `A` opening its OWN `Lib` (`T.X = 5`), beside the holder's (`T.X = 9`). -/
def valueOwnOpen (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.resolve "Lib"]
    [privateProp "Lib" (alg [] [] [publicProp "T" (xBlock 9)] []),
     privateProp "A" (referenceToT id [privateProp "Lib" (alg [] [] [publicProp "T" (xBlock 5)] [])] [.resolve "Lib"])]
    [.dotCall (.resolve "A") "X" none])

-- Production: a holder's declaration …
#guard answers 5 (valueHolderTarget ordinary)
#guard unknownName "T" (valueHolderTarget moduleRoot)
#guard unknownName "T" (valueHolderTarget moduleViewRoot)
-- … and a member the holder's `open` provides.
#guard answers 5 (valueHolderOpen ordinary)
#guard unknownName "T" (valueHolderOpen moduleRoot)
#guard unknownName "T" (valueHolderOpen moduleViewRoot)

-- The model: the same.
#guard pathSelection (valueHolderTarget ordinary) == .member ["T", "X"] [["T", "X"]] [some "T", none]
#guard pathSelection (valueHolderTarget moduleRoot) == .nothing
#guard pathSelection (valueHolderTarget moduleViewRoot) == .nothing
-- The ordinary alias consults its holder's open level (the provider's walk `Lib.T` is on the trail);
-- the module twin consults no level of its holder.
#guard pathSelection (valueHolderOpen ordinary) ==
  .member ["Lib", "T", "X"] [["Lib", "T"], ["Lib", "T", "X"]] [some "T", some "Lib", none]
#guard pathSelection (valueHolderOpen moduleRoot) == .nothing
#guard pathSelection (valueHolderOpen moduleViewRoot) == .nothing

-- The controls: the root's own declaration, and a member its own `open` provides.
#guard answers 5 (valueOwnTarget ordinary)
#guard answers 5 (valueOwnTarget moduleRoot)
#guard answers 5 (valueOwnTarget moduleViewRoot)
#guard pathSelection (valueOwnTarget ordinary) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A", none]
#guard pathSelection (valueOwnTarget moduleRoot) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A"]
#guard pathSelection (valueOwnTarget moduleViewRoot) == .member ["A", "T", "X"] [["A", "T", "X"]] [some "T", some "A"]
#guard answers 5 (valueOwnOpen ordinary)
#guard answers 5 (valueOwnOpen moduleRoot)
#guard answers 5 (valueOwnOpen moduleViewRoot)
#guard pathSelection (valueOwnOpen ordinary) ==
  .member ["A", "Lib", "T", "X"] [["A", "Lib", "T"], ["A", "Lib", "T", "X"]] [some "T", some "Lib", some "A", none]
#guard pathSelection (valueOwnOpen moduleRoot) ==
  .member ["A", "Lib", "T", "X"] [["A", "Lib", "T"], ["A", "Lib", "T", "X"]] [some "T", some "Lib", some "A"]
#guard pathSelection (valueOwnOpen moduleViewRoot) ==
  .member ["A", "Lib", "T", "X"] [["A", "Lib", "T"], ["A", "Lib", "T", "X"]] [some "T", some "Lib", some "A"]

/-! ### The walkers: an alias root's row and members -/

/-- `Q = y`, local-only on its declaring level's `y`. -/
def holderQ : PropDef :=
  { (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y")))
    with requiredOwnerDepths := some [("y", some 0)] }

/-- Host-built: `F(y) = { Q = y ⏎ A = Q ⏎ A }` / `F(7)`, `A` a reference with the identity `id`,
    marked exported. -/
def rowReadsHolder (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [holderQ, privateProp "A" (.alias none [] [] (.resolve "Q") id true)] [.resolve "A"])] [.call (.resolve "F") [.num 7]])

/-- Host-built: `F(y) = { G = { Q = y ⏎ <alias> } ⏎ G }` / `F(7)`: a reference to `Q` with the identity
    `id` written INLINE as `G`'s row; `G` is marked exported. The writer's level `G` is between the
    root and the holder `F`. -/
def inlineRowReadsWriter (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [privateProp "G" (alg [] []
      [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y")))
         with requiredOwnerDepths := some [("y", some 1)] }]
      [.algorithmExpr (.alias none [] [] (.resolve "Q") id true)])] [.resolve "G"])] [.call (.resolve "F") [.num 7]])

/-- Host-built: `F(y) = { Q = y ⏎ A = <carrier> ⏎ A.P }` / `F(7)`, the carrier `A` (identity `id`)
    declaring `public P = Q + 0`, marked exported. -/
def memberReadsHolder (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [holderQ,
     privateProp "A" (.alias none []
       [publicProp "P" (alg [] [] [] [.binary .add (.resolve "Q") (.num 0)]), privateProp "Z" (alg [] [] [] [.num 0])]
       (.resolve "Z") id false)]
    [.dotCall (.resolve "A") "P" none])] [.call (.resolve "F") [.num 7]])

/-- Host-built: the BLOCK-rooted twin of `memberReadsHolder`. -/
def memberReadsHolderBlock (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [holderQ,
     privateProp "A" ((alg [] [] [publicProp "P" (alg [] [] [] [.binary .add (.resolve "Q") (.num 0)])] [.num 0]).withDeclarationId id)]
    [.dotCall (.resolve "A") "P" none])] [.call (.resolve "F") [.num 7]])

/-- Host-built: `F(y) = { A = y ⏎ A }` / `F(7)`, `A` a parameter-row alias with the identity `id`. -/
def paramRow (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) (.alias none [] [] (.param "y") id true))
       with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [.call (.resolve "F") [.num 7]])

/-- Host-built: the BLOCK-rooted twin of `paramRow`, `A`'s body the row `y`. -/
def paramRowBlock (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["y"] []
    [{ (privateLocalProp "A" (.localCapturedAncestorParams ["y"]) ((alg [] [] [] [.param "y"]).withDeclarationId id))
       with requiredOwnerDepths := some [("y", some 0)] }] [.resolve "A"])] [.call (.resolve "F") [.num 7]])

-- Production: the ordinary alias reads its holder's `Q`; a module, whatever its root, does not.
-- `G` and `P` are PROPERTIES marked exported: since EXPORTED-DETACHED they are evaluated detached from
-- `F`'s call, so the `y` their route reaches has no binding (formerly 7). The reference `A` of
-- `rowReadsHolder` owns no cache entry and is chased where it is read.
#guard answers 7 (rowReadsHolder ordinary)
#guard unknownName "Q" (rowReadsHolder moduleRoot)
#guard unknownName "y" (inlineRowReadsWriter ordinary)
#guard unknownName "Q" (inlineRowReadsWriter moduleRoot)
#guard unknownName "y" (memberReadsHolder ordinary)
#guard unknownName "Q" (memberReadsHolder moduleRoot)
#guard unknownName "Q" (memberReadsHolderBlock moduleRoot)

/-- The ordinary alias's row requires its holder's `y`: the exported copy is refused. -/
theorem rowReadsHolder_ordinary_refused : ¬ SourceDomain (rowReadsHolder ordinary) :=
  fun h => by have := h.exposed; rw [show exposureFull (rowReadsHolder ordinary) = false by cbv] at this; cases this

/-- **The module root's row sees no level of its holder**: it requires nothing of `F`. (Before the
    cut the model refused this tree, charging the holder's `Q`.) -/
theorem rowReadsHolder_module_sourceDomain : SourceDomain (rowReadsHolder moduleRoot) := ⟨by cbv, by cbv⟩

/-- The same of a root written inline: neither the body it is written in nor a level above it is
    seen. The ordinary alias written there requires `y` of `G`, whose exported copy is refused. -/
theorem inlineRowReadsWriter_module_sourceDomain : SourceDomain (inlineRowReadsWriter moduleRoot) := ⟨by cbv, by cbv⟩

theorem inlineRowReadsWriter_ordinary_refused : ¬ SourceDomain (inlineRowReadsWriter ordinary) :=
  fun h => by have := h.exposed; rw [show exposureFull (inlineRowReadsWriter ordinary) = false by cbv] at this; cases this

/-- The same of a member of an alias root, as of a member of a block root. -/
theorem memberReadsHolder_module_sourceDomain :
    SourceDomain (memberReadsHolder moduleRoot) ∧ SourceDomain (memberReadsHolderBlock moduleRoot) :=
  ⟨⟨by cbv, by cbv⟩, ⟨by cbv, by cbv⟩⟩

#guard !exposureFull (memberReadsHolder ordinary)
#guard !exposureFull (memberReadsHolderBlock ordinary)
#guard exposureFull (rowReadsHolder moduleViewRoot)
#guard exposureFull (inlineRowReadsWriter moduleViewRoot)
#guard exposureFull (memberReadsHolder moduleViewRoot)

-- A parameter only the holder binds is UNBOUND in a module, whatever its root. Production reads it
-- from the reading context's own tier (the read has no owner), which is what `paramsBound` excludes.
#guard paramsBound (paramRow ordinary)
#guard !paramsBound (paramRow moduleRoot)
#guard !paramsBound (paramRow moduleViewRoot)
#guard paramsBound (paramRowBlock ordinary)
#guard !paramsBound (paramRowBlock moduleRoot)
#guard answers 7 (paramRow ordinary)
#guard answers 7 (paramRow moduleRoot)

/-- Why `reqAlg_paramRow` and `declared_paramRow` exclude a module's root (`hroot`): under a level
    that binds `y`, the module-rooted parameter-row alias requires nothing — its chain is cut — while
    the ordinary one requires `y` there. -/
theorem moduleRoot_paramRow_requires_nothing :
    let holder : Level := { params := ["y"], props := [] }
    ownerIndex? [holder] "y" = some 0 ∧
      reqAlg ⟨false, true⟩ [holder] [] (some "A") (.alias none [] [] (.param "y") (some (.module 1)) true) = [] ∧
      reqAlg ⟨false, true⟩ [holder] [] (some "A") (.alias none [] [] (.param "y") none true) = [("y", 0)] := by
  refine ⟨by cbv, by cbv, by cbv⟩

end ReferenceRootCut

/-! ## A shared declaration is one open provider under one declaring scope (E-18 model correction, 2026-11-19)

`resolveAllOpens` counts a provider once by its callable identity: its declaration and its declaring
scope (`sameRepeatedCallableIdentity`, `sameDeclaringScope`). The model compared a declaration with a
supplied `shared` identity that way only inside a module; outside one it kept the written position,
so two holders of one such declaration were two providers where production counts one.
`declaringScope` now ends the comparison at a module or at the first level production identifies
afresh — an unmarked occurrence, a fresh syntax id per written occurrence, hence its position.

Every tree here is HOST-BUILT. The encoder marks a declaration shared when the C# tree reaches it
twice; no source program is known to hold one twice under one declaring scope outside a module (the
three source-derived Lean corpora carry no shared identity at all). Production's outcome is asserted
beside the model's.

* One provider: `twoNames` over one declaration, over two VIEWS of it (the provider's own view is
  erased), `twoPaths` under two holders of ONE shared declaration, and one declaration written as
  two `open` blocks (both wired at the prelude).
* Two providers, as before: two declarations; one declaration under two UNMARKED holders, under two
  shared holder declarations, under two views of one, under one with different binder names; one
  declaration at the root and under a container, inside a module, or written as an `open` block.
* Exposure — `capture`, the reader of `ModuleProviders.captureWitness` over two holders of one shared
  declaration: the copy without `R`'s requirement was admitted (two providers selected nothing) and
  is now refused; production reads `R` outside the call from the call's cache entry on that copy.
-/

namespace SharedProviders

open ModuleProviders (Selection rootSelection ambiguousX refusesSub)
open ReferenceRootCut (answers)

/-- `{ public X = n }` with the declaration identity `id`. -/
def xBlock (id : Option PropertyIdentity) (n : Int := 5) : Algorithm :=
  (alg [] [] [publicProp "X" (alg [] [] [] [.num n])] []).withDeclarationId id

/-- `{ public S = member }` with the declaration identity `id` and the parameters `params`. -/
def holding (id : Option PropertyIdentity) (member : Algorithm) (params : List Ident := []) : Algorithm :=
  (alg params [] [publicProp "S" member] (if params.isEmpty then [] else [.num 0])).withDeclarationId id

/-- Host-built: `open A, B` / `A = a` / `B = b` / `X`. -/
def twoNames (a b : Algorithm) : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" a, privateProp "B" b] [.resolve "X"])

/-- Host-built: `open A.S, B.S` / `A = a` / `B = b` / `X`. -/
def twoPaths (a b : Algorithm) : Expr :=
  .algorithmExpr (alg [] [.dotCall (.resolve "A") "S" none, .dotCall (.resolve "B") "S" none]
    [privateProp "A" a, privateProp "B" b] [.resolve "X"])

/-- The shared declaration `{ public X = 5 }`. -/
def one : Algorithm := xBlock (some (.shared 7))

-- One declaration held twice at one level: one provider, the first reach's (its copy answers).
#guard answers 5 (twoNames one one)
#guard rootSelection (twoNames one one) == .member ["A", "X"] [["A", "X"]] [some "A", none]
#guard answers 5 (twoNames one (xBlock (some (.shared 7)) 6))
#guard rootSelection (twoNames one (xBlock (some (.shared 7)) 6)) == .member ["A", "X"] [["A", "X"]] [some "A", none]

-- The provider's own view is erased.
#guard answers 5 (twoNames (xBlock (some (.sharedView 7 1))) (xBlock (some (.sharedView 7 2))))
#guard rootSelection (twoNames (xBlock (some (.sharedView 7 1))) (xBlock (some (.sharedView 7 2)))) ==
  .member ["A", "X"] [["A", "X"]] [some "A", none]

-- Two declarations, and unmarked ones, are two providers.
#guard ambiguousX (twoNames one (xBlock (some (.shared 8))))
#guard rootSelection (twoNames one (xBlock (some (.shared 8)))) == .nothing
#guard ambiguousX (twoNames (xBlock none) (xBlock none))
#guard rootSelection (twoNames (xBlock none) (xBlock none)) == .nothing

-- One declaration under two holders of ONE shared declaration: one declaring scope. Both targets
-- are walked; the member is the first reach's.
#guard answers 5 (twoPaths (holding (some (.shared 3)) one) (holding (some (.shared 3)) one))
#guard rootSelection (twoPaths (holding (some (.shared 3)) one) (holding (some (.shared 3)) one)) ==
  .member ["A", "S", "X"] [["A", "S"], ["B", "S"], ["A", "S", "X"]] [some "S", some "A", none]

-- Its declaring scope decides: unmarked holders (a fresh identity each), two holder declarations,
-- two views of one, one with different binder names.
#guard ambiguousX (twoPaths (holding none one) (holding none one))
#guard rootSelection (twoPaths (holding none one) (holding none one)) == .nothing
#guard ambiguousX (twoPaths (holding (some (.shared 3)) one) (holding (some (.shared 4)) one))
#guard rootSelection (twoPaths (holding (some (.shared 3)) one) (holding (some (.shared 4)) one)) == .nothing
#guard ambiguousX (twoPaths (holding (some (.sharedView 3 1)) one) (holding (some (.sharedView 3 2)) one))
#guard rootSelection (twoPaths (holding (some (.sharedView 3 1)) one) (holding (some (.sharedView 3 2)) one)) == .nothing
#guard ambiguousX (twoPaths (holding (some (.shared 3)) one ["p"]) (holding (some (.shared 3)) one ["q"]))
#guard rootSelection (twoPaths (holding (some (.shared 3)) one ["p"]) (holding (some (.shared 3)) one ["q"])) == .nothing

/-- Host-built: one shared declaration written as two `open` blocks. Both are wired at the prelude. -/
def writtenTwice : Expr :=
  .algorithmExpr (alg [] [.algorithmExpr one, .algorithmExpr one] [] [.resolve "X"])

#guard answers 5 writtenTwice
#guard rootSelection writtenTwice == .member ["#open0", "X"] [["#open0", "X"]] [none]

/-- Host-built: the declaration under two written blocks of the holder declaration `id`. -/
def underWrittenBlocks (id : Option PropertyIdentity) : Expr :=
  .algorithmExpr (alg [] [.dotCall (.algorithmExpr (holding id one)) "S" none,
    .dotCall (.algorithmExpr (holding id one)) "S" none] [] [.resolve "X"])

#guard answers 5 (underWrittenBlocks (some (.shared 3)))
#guard rootSelection (underWrittenBlocks (some (.shared 3))) ==
  .member ["#open0", "S", "X"] [["#open0", "S"], ["#open1", "S"], ["#open0", "S", "X"]] [some "S", none]
#guard ambiguousX (underWrittenBlocks none)
#guard rootSelection (underWrittenBlocks none) == .nothing

/-- Two unmarked owners hold the same shared declaration under different names. One owner is
    the first inline open block, the other a host-built property literally named `#open0`. -/
def openBlockAndNamedHolder : Expr :=
  let holder (memberName : Ident) := alg [] [] [publicProp memberName one] []
  .algorithmExpr (alg []
    [.dotCall (.algorithmExpr (holder "P")) "P" none, .dotCall (.resolve "#open0") "Q" none]
    [privateProp "#open0" (holder "Q")] [.resolve "X"])

#guard ambiguousX openBlockAndNamedHolder
#guard rootSelection openBlockAndNamedHolder == .nothing

/-- Host-built: the declaration held at the root and reached a second way: under an unmarked
    container (`C.S`), inside a module (`M.S`), or written as an `open` block. Three declaring
    scopes that are not the root's. -/
def rootAnd (second : Expr) (holder : List PropDef) : Expr :=
  .algorithmExpr (alg [] [.resolve "A", second] (privateProp "A" one :: holder) [.resolve "X"])

#guard ambiguousX (rootAnd (.dotCall (.resolve "C") "S" none) [privateProp "C" (holding none one)])
#guard rootSelection (rootAnd (.dotCall (.resolve "C") "S" none) [privateProp "C" (holding none one)]) == .nothing
#guard ambiguousX (rootAnd (.dotCall (.resolve "M") "S" none) [privateProp "M" (holding (some (.module 1)) one)])
#guard rootSelection (rootAnd (.dotCall (.resolve "M") "S" none) [privateProp "M" (holding (some (.module 1)) one)]) == .nothing
#guard ambiguousX (rootAnd (.algorithmExpr one) [])
#guard rootSelection (rootAnd (.algorithmExpr one) []) == .nothing

/-- Host-built: `A = a` / `B = b` / `F(y) = { open Lib.Sub, A, B ⏎ Lib = { public Sub = { y + 0 } ⏎ 0 }`
    `⏎ R = X + 0 ⏎ R }` with the rows `output`: the reader of `ModuleProviders.captureWitness`. `R` is
    local-only on `y` (`localOnly`) or has that requirement removed. -/
def capture (a b : Algorithm) (localOnly : Bool) (output : List Expr) : Expr :=
  let body := alg [] [] [] [.binary .add (.resolve "X") (.num 0)]
  let reader := if localOnly then
    { (privateLocalProp "R" (.localCapturedAncestorParams ["y"]) body) with requiredOwnerDepths := some [("y", some 0)] }
    else privateProp "R" body
  let sub := { (publicLocalProp "Sub" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [.binary .add (.param "y") (.num 0)]))
    with requiredOwnerDepths := some [("y", some 1)] }
  .algorithmExpr (alg [] [] [privateProp "A" a, privateProp "B" b,
    privateProp "F" (alg ["y"] [.dotCall (.resolve "Lib") "Sub" none, .resolve "A", .resolve "B"]
      [privateProp "Lib" (alg [] [] [sub] [.num 0]), reader] [.resolve "R"])] output)

/-- The rows `F(7)`. -/
def call : List Expr := [.call (.resolve "F") [.num 7]]

/-- The rows `F(7), F.R`. -/
def callThenRead : List Expr := [.call (.resolve "F") [.num 7], .dotCall (.resolve "F") "R" none]

theorem capture_sourceDomain : SourceDomain (capture one one true call) := ⟨by cbv, by cbv⟩

/-- **One provider outside a module too: the copy without `R`'s requirement is refused** (the model
    admitted it while two holders of one shared declaration were two providers). -/
theorem capture_hostBuilt_refused : ¬ SourceDomain (capture one one false call) :=
  fun h => by have := h.exposed; rw [show exposureFull (capture one one false call) = false by cbv] at this; cases this

/-- The control: over two declarations nothing is selected, and the same copy is admitted. -/
theorem capture_twoDeclarations_sourceDomain :
    SourceDomain (capture one (xBlock (some (.shared 8))) false call) := ⟨by cbv, by cbv⟩

#guard answers 5 (capture one one true call)
#guard (match runResult (capture one one true callThenRead) with
  | .error e => (match innermost e with | .localOnlyProperty _ "R" _ => true | _ => false)
  | .ok _ => false)
-- The copy without the requirement is refused inside the call (formerly `(5, 5)`), and so is the
-- admitted two-declaration control (formerly `ambiguousOpen X`): `refusesSub`.
#guard refusesSub (capture one one false callThenRead)
#guard refusesSub (capture one (xBlock (some (.shared 8))) false call)

end SharedProviders

end KatLang.NavigationSourceDomainGuards
