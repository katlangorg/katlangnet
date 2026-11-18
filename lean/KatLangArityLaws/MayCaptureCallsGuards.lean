import KatLangArityLaws.MayCaptureCalls
import KatLangArityLaws.PlanConservativityAdmissibleGuards

open KatLang KatLang.PlanConservativityGuards KatLang.PlanConservativityAdmissibleGuards

/-!
# Guards of the Lean program gate (`MayCaptureCalls.lean`; ledger E-21)

Fixture checks of `Expr.mayCaptureCalls` / `Algorithm.mayCaptureCalls` / `ScopeCtx.mayCaptureCalls`:

* the gate FIRES on every fixture the plan-conservativity guards use to leave the reference-free
  domain: the loop-only program (`loopOnlyRoot`), both META counterexamples (`selfInvokeDecls`,
  `viewReadDecls`) and the META root (`metaRoot`); and on each clause at each position of the walk —
  a `meta` parameter, the loop names as a name and as a dot member, a loop builtin node, an attached
  parent scope;
* the gate does NOT fire on the META-free corpus (`metaFreeSources`, their root, and the whole
  programs over that root).

Agreement with C#'s gate on the differential corpora is the generated
`MayCaptureCallsCorpus.lean`.
-/

namespace KatLang.MayCaptureCallsGuards

/-! ## The loop names come from the prelude -/

#guard metaBuiltinNames == ["while", "repeat"]
#guard isMetaBuiltinName "while" && isMetaBuiltinName "repeat"
#guard !isMetaBuiltinName "if" && !isMetaBuiltinName "reduce" && !isMetaBuiltinName "While"
-- The prelude holds the loop builtins: it is not part of a program and is never walked.
#guard Algorithm.mayCaptureCalls preludeAlg

/-! ## The gate fires -/

-- The loop-only fixture: no `meta` declaration, one `repeat` spelled in a body.
#guard Algorithm.mayCaptureCalls loopOnlyRoot
#guard Expr.mayCaptureCalls (.algorithmExpr loopOnlyRoot)
#guard !Expr.mayCaptureCalls (callN "Loop" [.num 5])

-- Both META counterexamples, as the whole programs their guards run.
#guard Expr.mayCaptureCalls (program selfInvokeDecls [firstOf (argsOf R)])
#guard Expr.mayCaptureCalls (program selfInvokeDecls [countOf (argsOf R)])
#guard Expr.mayCaptureCalls (program viewReadDecls [countOf (argsOf R)])
-- The positive control over the same shared declarations (`Capture(meta op)`), and the META root.
#guard Expr.mayCaptureCalls (program plainDecls [countOf (argsOf R)])
#guard Algorithm.mayCaptureCalls metaRoot

-- A `meta` parameter: at top level, and inside a structural pattern (refused by
-- `ParameterPattern.metaViolation?`, still a META binder for the gate).
def metaCapture : ParameterPattern := .capture { name := "op", kind := .metaRef }
#guard Algorithm.mayCaptureCalls (algWithParameterPatterns [metaCapture] [] [] [.param "op"])
#guard Algorithm.mayCaptureCalls
  (algWithParameterPatterns [.capture { name := "x" }, .sequenceValue [.capture { name := "y" }, metaCapture]] [] [] [.num 1])
#guard Algorithm.mayCaptureCalls (algWithParameterPatterns [.listValue [metaCapture]] [] [] [.num 1])
#guard Algorithm.mayCaptureCalls (algWithParameterPatterns [.unpacking [metaCapture]] [] [] [.num 1])
#guard !Algorithm.mayCaptureCalls
  (algWithParameterPatterns [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }] [] [] [.param "x"])

-- `while` and `repeat` spelled as a NAME.
#guard Expr.mayCaptureCalls (.resolve "while")
#guard Expr.mayCaptureCalls (.resolve "repeat")
#guard Expr.mayCaptureCalls (.call (.resolve "while") [callN "Step" [.num 1]])
#guard Expr.mayCaptureCalls (.call (.resolve "repeat") [callN "Inc" [.num 1], .num 3])

-- `while` and `repeat` spelled as a DOT MEMBER, with and without an argument list; and reached
-- only through a dot edge's elaborated fallback.
#guard Expr.mayCaptureCalls (.dotCall (callN "Step" [.num 1]) "while" none)
#guard Expr.mayCaptureCalls (.dotCall (callN "Inc" [.num 1]) "repeat" (some [.num 3]))
#guard Expr.mayCaptureCalls (.dotMember (.num 1) "Twice" (.resolve "repeat") none)
#guard !Expr.mayCaptureCalls (.dotMember (.num 1) "Twice" (.resolve "Twice") (some [.num 2]))

-- A name that is not a name NODE does not fire: a parameter, a string, a property's own name.
#guard !Expr.mayCaptureCalls (.param "while")
#guard !Expr.mayCaptureCalls (.stringLiteral "repeat")
#guard !Algorithm.mayCaptureCalls (algPrivate [] [] [("while", alg ["x"] [] [] [.param "x"])] [.num 1])

-- A loop builtin NODE (host-built): the two builtins whose signature declares `meta`, no other.
#guard Algorithm.mayCaptureCalls (.builtin .whileBuiltin)
#guard Algorithm.mayCaptureCalls (.builtin .repeatBuiltin)
#guard !Algorithm.mayCaptureCalls (.builtin .ifBuiltin) && !Algorithm.mayCaptureCalls (.builtin .reduceBuiltin)
#guard Expr.mayCaptureCalls (.call (.algorithmExpr (.builtin .repeatBuiltin)) [callN "Inc" [.num 1], .num 3])

-- Every position of the walk: an open, a property, an output row, a clause branch body, an alias
-- target, an argument, a selector, a comparison link, a list item, a captured row, a spread.
def loopRow : Expr := .call (.resolve "repeat") [.num 1, .num 2]
#guard Algorithm.mayCaptureCalls (alg [] [loopRow] [] [.num 1])
#guard Algorithm.mayCaptureCalls (algPrivate [] [] [("P", alg [] [] [] [loopRow])] [.num 1])
#guard Algorithm.mayCaptureCalls (alg [] [] [] [.num 1, loopRow])
#guard Algorithm.mayCaptureCalls (.conditional none [] [⟨.litInt 0, alg [] [] [] [.num 0]⟩, ⟨.bind "n", alg [] [] [] [loopRow]⟩])
#guard Algorithm.mayCaptureCalls (.conditional none [loopRow] [⟨.bind "n", alg [] [] [] [.num 0]⟩])
#guard Algorithm.mayCaptureCalls (.alias none [] [] (.resolve "while"))
#guard Algorithm.mayCaptureCalls (.alias none [] (propsPrivate [("P", alg [] [] [] [loopRow])]) (.resolve "F"))
#guard Expr.mayCaptureCalls (.call (.resolve "F") [.num 1, loopRow])
#guard Expr.mayCaptureCalls (.index (.resolve "F") [loopRow])
#guard Expr.mayCaptureCalls (.comparison (.num 1) [⟨.lt, .num 2⟩, ⟨.lt, loopRow⟩])
#guard Expr.mayCaptureCalls (.listLiteral [.num 1, loopRow])
#guard Expr.mayCaptureCalls (.capture [.num 1, loopRow])
#guard Expr.mayCaptureCalls (.sequenceSpread loopRow)
#guard Expr.mayCaptureCalls (.sequenceConstruct (.num 1) loopRow)
#guard Expr.mayCaptureCalls (.unary .minus loopRow)
#guard Expr.mayCaptureCalls (.binary .add (.num 1) loopRow)

-- An attached PARENT SCOPE contributes its properties, opens and parent. The last two scope
-- guards distinguish those children from the Lean-only body fields used for owner reconstruction.
def cleanScope : ScopeCtx := .mk none [] [] (propsPrivate [("K", alg [] [] [] [.num 7])]) [] [] none none
def loopScope : ScopeCtx := .mk none [] [] (propsPrivate [("L", alg [] [] [] [loopRow])]) [] [] none none
#guard !ScopeCtx.mayCaptureCalls cleanScope
#guard ScopeCtx.mayCaptureCalls loopScope
#guard ScopeCtx.mayCaptureCalls (.mk (some loopScope) [] [] [] [] [] none none)
#guard ScopeCtx.mayCaptureCalls (.mk none [] [loopRow] [] [] [] none none)
#guard !ScopeCtx.mayCaptureCalls (.mk none [] [] [] [loopRow] [] none none)
#guard !ScopeCtx.mayCaptureCalls (.mk none [] [] [] [] [⟨.bind "n", alg [] [] [] [loopRow]⟩] none none)
#guard !Algorithm.mayCaptureCalls (Algorithm.mk (some cleanScope) [] [] [] [.resolve "K"])
#guard Algorithm.mayCaptureCalls (Algorithm.mk (some loopScope) [] [] [] [.resolve "K"])
#guard Algorithm.mayCaptureCalls (.conditional (some loopScope) [] [⟨.bind "n", alg [] [] [] [.num 0]⟩])
#guard Algorithm.mayCaptureCalls (.alias (some loopScope) [] [] (.resolve "K"))

/-! ## The gate does not fire on the META-free corpus -/

#guard metaFreeSources.all fun src => !Expr.mayCaptureCalls src
#guard !Algorithm.mayCaptureCalls KatLang.CallPlanGuards.root
#guard !Algorithm.mayCaptureCalls KatLang.CallPlanGuards.otherRoot
-- The whole programs: each source as the one output row of the corpus's root.
#guard metaFreeSources.all fun src =>
  match KatLang.CallPlanGuards.root with
  | .mk parent patterns opens properties _ id =>
      !Expr.mayCaptureCalls (.algorithmExpr (.mk parent patterns opens properties [src] id))
  | _ => false

end KatLang.MayCaptureCallsGuards
