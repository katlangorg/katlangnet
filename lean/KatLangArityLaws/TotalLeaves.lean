import KatLang

open KatLang

/-!
# E-6 Tier 3: the remaining leaves of the public run are total

E-6 Tier 2 made the pre-evaluation validation total; this task removes the remaining `partial`
definitions of `lean/KatLang.lean` (15 → 0) and the derived `Repr` printers of the nested
inductives, which were the last KatLang constants kernel-opaque on `runResultM`'s path:

* well-founded or structural now: `lookupInParentsDirect`, `lookupLexicalDirect` (never recursive),
  `requiredParameterOwner?`, the `cache*Shape` group, `scopeChainContains`,
  `sequenceConstructLeavesLoop`, `peelSequenceSpread`, `peelSequenceSpreadLayers`,
  `exprDiagnosticName` (with its two `where` helpers),
  `postElabInvariant` / `postElabInvariantAlg`;
* written total printers, the derived ones term for term: `Pattern`, `ParameterPattern`, `Result`
  and the types of the AST block (`lean/KatLang.lean` § Total `Repr` printers).

(Two of the definitions this task made total, the interpolation hole test
`holeMayRenderLeadingBrace` and the printer of `InterpolationLink`, left the model with string
interpolation: STR-03, November 2026.)

Names, signatures, bodies and check order are unchanged. Where a total body differs in FORM from
the former `partial` one — a parent's equation named for the termination proof, an optional child
matched explicitly instead of `Option.map`, a block's rows walked through `attach` — the former
body is an equation of the total definition (§ 1). Bodies whose form did not change need none:
their equation lemma (`f.eq_def`) IS the former body. The printers cannot be proved equal to the
derived ones (those are opaque); the bounded comparison of the E-6 Tier 3 report checks them, and
`List.repr_eq_reprFormatList` (`lean/KatLang.lean`) proves the one generic step they share with
core's `List.repr`.
-/

namespace KatLang.TotalLeaves

/-! ## 1. The former bodies -/

/-- The former body of `lookupInParentsDirect` (the parent's match unnamed). -/
theorem lookupInParentsDirect_equation (sc : ScopeCtx) (name : Ident) :
    lookupInParentsDirect sc name = match lookupPropAny (ScopeCtx.props sc) name with
      | some child => some (Algorithm.withParent (some sc) child)
      | none =>
          match ScopeCtx.parent sc with
          | some sc' => lookupInParentsDirect sc' name
          | none => none := by
  rw [lookupInParentsDirect.eq_def]
  cases lookupPropAny (ScopeCtx.props sc) name with
  | some child => rfl
  | none => dsimp only; split <;> simp_all

/-- The former body of `requiredParameterOwner?` (the parent's match unnamed). -/
theorem requiredParameterOwner?_equation (scope : ScopeCtx) (name : Ident) :
    requiredParameterOwner? scope name =
      if (ScopeCtx.params scope).contains name then some scope
      else
        match ScopeCtx.parent scope with
        | some parent => requiredParameterOwner? parent name
        | none => none := by
  rw [requiredParameterOwner?.eq_def]
  split
  · rfl
  · split <;> simp_all

/-- `cacheParentShape` is the former `Option.map cacheScopeShape`. -/
theorem cacheParentShape_eq_map (p : Option ScopeCtx) : cacheParentShape p = p.map cacheScopeShape := by
  cases p <;> rw [cacheParentShape.eq_def] <;> rfl

/-- The former `dotMember` row of `cacheExprShape` (`args.map (List.map cacheExprShape)`). -/
theorem cacheExprShape_dotMember (target : Expr) (name : Ident) (fallback : Expr) (args : Option (List Expr)) :
    cacheExprShape (.dotMember target name fallback args) =
      .dotMember (cacheExprShape target) name (cacheExprShape fallback) (args.map (List.map cacheExprShape)) := by
  rw [cacheExprShape.eq_def]
  cases args <;> rfl

/-- The former body of `cacheAlgorithmShape` (each parent through `Option.map`). -/
theorem cacheAlgorithmShape_equation (a : Algorithm) :
    cacheAlgorithmShape a = match a with
      | .builtin b => .builtin b
      | .mk parent parameters opens props output _ =>
          .mk (parent.map cacheScopeShape) parameters (opens.map cacheExprShape)
            (props.map cachePropertyShape) (output.map cacheExprShape)
      | .conditional parent opens branches _ =>
          .conditional (parent.map cacheScopeShape) (opens.map cacheExprShape)
            (branches.map fun b => { b with body := cacheAlgorithmShape b.body })
      | .alias parent opens props target _ reference =>
          .alias (parent.map cacheScopeShape) (opens.map cacheExprShape)
            (props.map cachePropertyShape) (cacheExprShape target) none reference := by
  rw [cacheAlgorithmShape.eq_def]
  cases a <;> simp only [cacheParentShape_eq_map]

/-- The former body of `cacheScopeShape` (the parent through `Option.map`). -/
theorem cacheScopeShape_equation (s : ScopeCtx) :
    cacheScopeShape s = match s with
      | .mk parent _ opens props _ _ _ _ =>
          .mk (parent.map cacheScopeShape) [] (opens.map cacheExprShape)
            (props.map cachePropertyShape) [] [] none none := by
  rw [cacheScopeShape.eq_def]
  cases s; simp only [cacheParentShape_eq_map]

/-- The former `algorithmExpr` row of `exprDiagnosticName` (the rows walked directly). -/
theorem exprDiagnosticName_algorithmExpr (a : Algorithm) :
    exprDiagnosticName (.algorithmExpr a) =
      "(" ++ String.intercalate ", " ((Algorithm.output a).map exprDiagnosticName) ++ ")" := by
  rw [exprDiagnosticName.eq_def]
  simp only
  congr 2
  conv => rhs; rw [← List.attach_map_subtype_val (Algorithm.output a), List.map_map]
  rfl

/-- The former body of `scopeChainContains` (unchanged: its equation lemma). -/
theorem scopeChainContains_equation (level : Option ScopeCtx) (owner : ScopeCtx) :
    scopeChainContains level owner = match level with
      | none => false
      | some scope =>
          (sameDeclaringScope scope owner && scope.activation.isSome &&
            compatibleActivations (some owner) (some scope)) ||
          scopeChainContains scope.parent owner := by
  rw [scopeChainContains.eq_def]; rfl

/-- The former body of `sequenceConstructLeavesLoop` (unchanged: its equation lemma). -/
theorem sequenceConstructLeavesLoop_equation (pending acc : List Expr) :
    sequenceConstructLeavesLoop pending acc = match pending, acc with
      | [], acc => acc.reverse
      | current :: rest, acc =>
          match current with
          | .sequenceConstruct left right => sequenceConstructLeavesLoop (left :: right :: rest) acc
          | leaf => sequenceConstructLeavesLoop rest (leaf :: acc) := by
  rw [sequenceConstructLeavesLoop.eq_def]; rfl

/-! ## 2. Kernel computation

The structural leaves reduce in the kernel (`rfl`): the formerly opaque peel and brace tests. -/

example : peelSequenceSpreadLayers (.sequenceSpread (.sequenceSpread (.num 1))) 0 = (.num 1, 2) := rfl
example : peelSequenceSpread (.sequenceSpread (.sequenceSpread (.param "x"))) = .param "x" := rfl

end KatLang.TotalLeaves
