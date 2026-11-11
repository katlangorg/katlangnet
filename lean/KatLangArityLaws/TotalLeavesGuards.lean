import KatLangArityLaws.TotalLeaves
import KatLangArityLaws.AdmittedSet

open KatLang

/-!
# E-6 Tier 3 guards: the written printers and the total leaves

The written `Repr` printers print exactly what `deriving Repr` printed (the bounded comparison of
the E-6 Tier 3 report re-derives the printers and compares them over the corpora); these guards pin
a few outputs — constructor arguments at `max_prec`, list and optional fields, structure rows with
their nesting, a nested pattern, a nested value — so a drift of either side shows here too. Then
the formerly opaque leaves on concrete inputs.
-/

namespace KatLang.TotalLeavesGuards

#guard reprStr (Expr.num (-3)) == "KatLang.Expr.num (-3)"

#guard reprStr (Expr.dotMember (.resolve "A") "f" (.resolve "f") (some [.num 1, .stringLiteral "x"])) ==
  "KatLang.Expr.dotMember\n  (KatLang.Expr.resolve \"A\")\n  \"f\"\n  (KatLang.Expr.resolve \"f\")\n  (some [KatLang.Expr.num 1, KatLang.Expr.stringLiteral \"x\"])"

#guard reprStr (Algorithm.mk none [.capture { name := "x" }] []
    [{ name := "P", alg := .builtin .countBuiltin, isPublic := true }] [.param "x"] none) ==
  "KatLang.Algorithm.mk\n  none\n  [KatLang.ParameterPattern.capture { name := \"x\", kind := KatLang.ParameterKind.normal }]\n  []\n  [{ name := \"P\",\n     alg := KatLang.Algorithm.builtin (KatLang.Builtin.countBuiltin),\n     isPublic := true,\n     exposure := KatLang.PropExposure.exported,\n     identity := none,\n     requiredOwnerDepths := none }]\n  [KatLang.Expr.param \"x\"]\n  none"

#guard reprStr (ScopeCtx.mk (some (ScopeCtx.mk none [] [] [] [] [] none (some (.host 4)))) ["x"] [] [] []
    [{ pattern := .sequenceValue [.bind "a", .litInt 2], body := .builtin .ifBuiltin }] (some 2) none) ==
  "KatLang.ScopeCtx.mk\n  (some (KatLang.ScopeCtx.mk none [] [] [] [] [] none (some (KatLang.PropertyIdentity.host 4))))\n  [\"x\"]\n  []\n  []\n  []\n  [{ pattern := KatLang.Pattern.sequenceValue [KatLang.Pattern.bind \"a\", KatLang.Pattern.litInt 2],\n     body := KatLang.Algorithm.builtin (KatLang.Builtin.ifBuiltin) }]\n  (some 2)\n  none"

#guard reprStr (Result.sequenceValue [.atom 1, .listValue [.str "a", .bool true], .callRef 3]) ==
  "KatLang.Result.sequenceValue\n  [KatLang.Result.atom 1,\n   KatLang.Result.listValue [KatLang.Result.str \"a\", KatLang.Result.bool true],\n   KatLang.Result.callRef 3]"

-- The leaves.
#guard exprDiagnosticName (.binary .add (.binary .add (.num 1) (.num 2)) (.algorithmExpr (Algorithm.ofExpr (.num 3)))) ==
  "1 + 2 + (3)"
#guard (sequenceConstructLeaves (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3))).length == 3
#guard reprStr (cacheScopeShape (ScopeCtx.mk none ["x"] [] [] [.num 1] [] (some 5) (some (.syntax 9)))) ==
  reprStr (ScopeCtx.mk none [] [] [] [] [] none none)
#guard (requiredParameterOwner? (ScopeCtx.mk (some (ScopeCtx.mk none ["y"] [] [] [] [] none none)) ["x"] [] [] [] [] none none) "y").isSome
#guard (requiredParameterOwner? (ScopeCtx.mk none ["x"] [] [] [] [] none none) "y").isNone
#guard (lookupInParentsDirect (ScopeCtx.mk (some (ScopeCtx.mk none [] []
    [{ name := "Q", alg := .builtin .countBuiltin, isPublic := true }] [] [] none none)) [] [] [] [] [] none none) "Q").isSome
#guard !scopeChainContains none (ScopeCtx.mk none [] [] [] [] [] none none)
#guard !postElabInvariant (.call (.resolve "load") [.stringLiteral "u"])

end KatLang.TotalLeavesGuards
