import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

Canonical executable language specification, Lean half
(source corpus: tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs).

Each `#guard` pins the CANONICAL expectation of one specification case —
not an observed value. The C# runner (LanguageSpecRunnerTests) asserts the
C# engine matches the same canonical neutral observation, so together the
two builds keep Lean, C#, and the specification aligned case-by-case.
This is bounded differential validation over the Lean-guarded partition,
not a formal verification of the evaluators.

Partition (machine-checked by the `specCaseIds.length` guard below):
- specification surface cases: 163
- excluded parse-level cases (Lean has no surface parser): 5
- excluded C#-only cases (each carries an explicit reason in the corpus): 1
- Lean-guarded cases: 157
- probe observations (C#-only by design): 227
- internal-node cases live in the semantic-explorer corpus, not here: see
  lean/SemanticExplorerCases.lean

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
  dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
-/

namespace LanguageSpecCases
open KatLang

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, sequence -> `S[a, b]`, empty -> `S[]`,
    exact list -> `L[a, b]`. -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .sequenceValue rs => "S[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .listValue rs => "L[" ++ String.intercalate ", " (rs.map neutral) ++ "]"

/-- Innermost-error category shared with the C# harness
    (`SemanticExplorerHarness.ErrorCategory`). -/
partial def errCategory : Error -> String
  | .withContext _ inner => errCategory inner
  | .arityMismatch _ _ => "arity"
  | .badArity => "arity"
  | .branchArityMismatch _ _ _ => "arity"
  | .branchOutputArityMismatch _ _ _ => "arity"
  | .badIndex => "index"
  | .typeMismatch _ => "type"
  | .missingOutput => "missingOutput"
  | .spreadMissingOutput => "spreadMissingOutput"
  | .unknownName _ => "unknownName"
  | .divByZero => "div0"
  | .noMatchingBranch _ => "branch"
  | .unknownProperty _ _ => "unknownProperty"
  | .notPublicProperty _ _ => "notPublicProperty"
  | .localOnlyProperty _ _ _ => "localOnlyProperty"
  | .notAnAlgorithm _ => "notAnAlgorithm"
  | .illegalInOpen _ => "illegalInOpen"
  | .badOpenForm _ => "badOpenForm"
  | .illegalInEval _ => "illegalInEval"
  | .ambiguousOpen _ _ => "ambiguousOpen"
  | .duplicateProperty _ => "duplicateProperty"
  | .duplicateBranchPattern => "duplicateBranchPattern"
  | .explicitParamsRequireOutput => "explicitParamsRequireOutput"
  | .unresolvedImplicitParams _ => "unresolvedImplicitParams"

/-- Counted variant of `runResultM`: the same root wiring, but keeping the
    root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
    C# `Evaluator.RunCounted` observation. -/
def runCountedM (e : Expr) : EvalM CountedResult := do
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .block a =>
      let wired := wireToCaller ctx a
      if (Algorithm.params wired).length = 0 then
        evalAlgOutputCounted wired ctx []
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => evalCounted e ctx []

/-- Neutral observation string shared verbatim with the C# harness.
    Also cross-checks Lean's plain (`runResult`) and counted evaluators on
    every case: any disagreement between the two produces an
    `internalMismatch ...` observation, which can never equal a pinned
    expectation, so the guard fails and names the case. -/
def obs (e : Expr) : String :=
  match runCountedM e |>.run EvalState.empty, runResult e with
  | .ok ((r, n), _), .ok r2 =>
      if r == r2 then s!"ok raw={neutral r} n={n}"
      else s!"internalMismatch counted={neutral r} plain={neutral r2}"
  | .error e1, .error e2 =>
      if errCategory e1 == errCategory e2 then s!"err {errCategory e1}"
      else s!"internalMismatch countedErr={errCategory e1} plainErr={errCategory e2}"
  | .ok ((r, _), _), .error e2 => s!"internalMismatch counted=ok:{neutral r} plain=err:{errCategory e2}"
  | .error e1, .ok r2 => s!"internalMismatch counted=err:{errCategory e1} plain=ok:{neutral r2}"

-- first-program [arithmetic]: 2 + 3 * 4
def case_first_program : Expr :=
  .block (alg [] [] [] [.binary .add (.num 2) (.binary .mul (.num 3) (.num 4))])
#guard obs case_first_program == "ok raw=14 n=1"

-- property-access-and-call [arithmetic]: # Define a property: \n Answer = 42 \n  \n # Property-style access: \n Answer \n  \n # Explicit zero-parameter call: \n Answer()
def case_property_access_and_call : Expr :=
  .block (alg [] [] [privateProp "Answer" (alg [] [] [] [.num 42])] [.resolve "Answer", .call (.resolve "Answer") (alg [] [] [] [])])
#guard obs case_property_access_and_call == "ok raw=S[42, 42] n=2"

-- output-is-ordinary-property [arithmetic]: Output = 5 \n Output
def case_output_is_ordinary_property : Expr :=
  .block (alg [] [] [privateProp "Output" (alg [] [] [] [.num 5])] [.resolve "Output"])
#guard obs case_output_is_ordinary_property == "ok raw=5 n=1"

-- empty-literal [empty-and-singleton]: ()
def case_empty_literal : Expr :=
  .block (alg [] [] [] [(.emptySequence 0)])
#guard obs case_empty_literal == "ok raw=S[] n=1"

-- empty-wrapped [empty-and-singleton]: (())
def case_empty_wrapped : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])
#guard obs case_empty_wrapped == "ok raw=S[] n=1"

-- empty-wrapped-twice [empty-and-singleton]: ((()))
def case_empty_wrapped_twice : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]))])
#guard obs case_empty_wrapped_twice == "ok raw=S[] n=1"

-- singleton-paren [empty-and-singleton]: (7)
def case_singleton_paren : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [.num 7]))])
#guard obs case_singleton_paren == "ok raw=7 n=1"

-- singleton-paren-deep [empty-and-singleton]: (((7)))
def case_singleton_paren_deep : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 7]))]))]))])
#guard obs case_singleton_paren_deep == "ok raw=7 n=1"

-- empty-eq-family [empty-and-singleton]: () == ()      # 1 \n () == (())    # 1 \n () != (())    # 0 \n count(())     # 0 \n count((()))   # 0
def case_empty_eq_family : Expr :=
  .block (alg [] [] [] [.binary .eq (.emptySequence 0) (.emptySequence 0), .binary .eq (.emptySequence 0) (.block (alg [] [] [] [(.emptySequence 0)])), .binary .ne (.emptySequence 0) (.block (alg [] [] [] [(.emptySequence 0)])), .call (.resolve "count") (alg [] [] [] [(.emptySequence 0)]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_empty_eq_family == "ok raw=S[1, 1, 0, 0, 0] n=5"

-- empty-capture [empty-and-singleton]: A = () \n A
def case_empty_capture : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.emptySequence 0)])] [.resolve "A"])
#guard obs case_empty_capture == "ok raw=S[] n=1"

-- supply-three-rows [item-supply-vs-value]: 10, 20, 30
def case_supply_three_rows : Expr :=
  .block (alg [] [] [] [.num 10, .num 20, .num 30])
#guard obs case_supply_three_rows == "ok raw=S[10, 20, 30] n=3"

-- value-three-items [item-supply-vs-value]: (1 + 1, 2 + 2, 3 + 3)
def case_value_three_items : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [.binary .add (.num 1) (.num 1), .binary .add (.num 2) (.num 2), .binary .add (.num 3) (.num 3)]))])
#guard obs case_value_three_items == "ok raw=S[2, 4, 6] n=1"

-- adjacency-is-comma [item-supply-vs-value]: 1 2 3
def case_adjacency_is_comma : Expr :=
  .block (alg [] [] [] [.num 1, .num 2, .num 3])
#guard obs case_adjacency_is_comma == "ok raw=S[1, 2, 3] n=3"

-- capture-supply [item-supply-vs-value]: A = 1, 2, 3 \n A
def case_capture_supply : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.resolve "A"])
#guard obs case_capture_supply == "ok raw=S[1, 2, 3] n=1"

-- capture-supply-spread [item-supply-vs-value]: A = 1, 2, 3 \n A*
def case_capture_supply_spread : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.sequenceSpread (.resolve "A")])
#guard obs case_capture_supply_spread == "ok raw=S[1, 2, 3] n=3"

-- call-reentry-identity [item-supply-vs-value]: I(a) = a \n A = 1, 2, 3 \n I(I(A))
def case_call_reentry_identity : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "A"])])])
#guard obs case_call_reentry_identity == "ok raw=S[1, 2, 3] n=1"

-- call-value-boundary [item-supply-vs-value]: F(*a) = a \n F(5, 9) \n F(5, 9)*
def case_call_value_boundary : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.num 5, .num 9]), .sequenceSpread (.call (.resolve "F") (alg [] [] [] [.num 5, .num 9]))])
#guard obs case_call_value_boundary == "ok raw=S[L[5, 9], 5, 9] n=3"

-- property-value-boundary [item-supply-vs-value]: Coordinates = 10, 20 \n Coordinates \n Coordinates*
def case_property_value_boundary : Expr :=
  .block (alg [] [] [privateProp "Coordinates" (alg [] [] [] [.num 10, .num 20])] [.resolve "Coordinates", .sequenceSpread (.resolve "Coordinates")])
#guard obs case_property_value_boundary == "ok raw=S[S[10, 20], 10, 20] n=3"

-- spread-capture-count [item-supply-vs-value]: A = [1, 2, 3] \n  \n (A*).count
def case_spread_capture_count : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])] [.dotCall (.block (alg [] [] [] [.sequenceSpread (.resolve "A")])) "count" none])
#guard obs case_spread_capture_count == "ok raw=3 n=1"

-- repeated-spread-fixed-point [item-supply-vs-value]: Collect(*items) = items \n A = [[1, 2], [3, 4]] \n  \n Collect(A*) \n Collect(A**) \n Collect((A*)*)
def case_repeated_spread_fixed_point : Expr :=
  .block (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "A" (alg [] [] [] [(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])])] [.call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.resolve "A")]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.sequenceSpread (.resolve "A"))]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [.sequenceSpread (.resolve "A")]))])])
#guard obs case_repeated_spread_fixed_point == "ok raw=S[L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]]] n=3"

-- repeated-spread-singleton-opens [item-supply-vs-value]: Collect(*items) = items \n  \n Collect([[7]]*) \n Collect([[7]]**) \n Collect([7]*) \n Collect([7]**)
def case_repeated_spread_singleton_opens : Expr :=
  .block (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [.call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.listLiteral [.listLiteral [.num 7]])]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.sequenceSpread (.listLiteral [.listLiteral [.num 7]]))]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.listLiteral [.num 7])]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_repeated_spread_singleton_opens == "ok raw=S[L[L[7]], L[7], L[7], L[7]] n=4"

-- scalar-spread-neutral [item-supply-vs-value]: Collect(*items) = items \n  \n Collect(5) \n Collect(5*)
def case_scalar_spread_neutral : Expr :=
  .block (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [.call (.resolve "Collect") (alg [] [] [] [.num 5]), .call (.resolve "Collect") (alg [] [] [] [.sequenceSpread (.num 5)])])
#guard obs case_scalar_spread_neutral == "ok raw=S[L[5], L[5]] n=2"

-- select-spread-vs-capture-select [item-supply-vs-value]: A = [[1, 2], [3, 4]] \n  \n (A:0)* \n (A*):0
def case_select_spread_vs_capture_select : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])])] [.sequenceSpread (.block (alg [] [] [] [.index (.resolve "A") (.num 0)])), .index (.block (alg [] [] [] [.sequenceSpread (.resolve "A")])) (.num 0)])
#guard obs case_select_spread_vs_capture_select == "ok raw=S[1, 2, L[1, 2]] n=3"

-- fixed-call-preserves-boundaries [item-supply-vs-value]: Pair = 10, 20 \n Add(x, y) = x + y \n  \n Add(Pair)
def case_fixed_call_preserves_boundaries : Expr :=
  .block (alg [] [] [privateProp "Pair" (alg [] [] [] [.num 10, .num 20]), privateProp "Add" (alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")])] [.call (.resolve "Add") (alg [] [] [] [.resolve "Pair"])])
#guard obs case_fixed_call_preserves_boundaries == "err arity"

-- spread-fills-remaining-slots [item-supply-vs-value]: Tail = 2, 3 \n Use(a, b, c) = a + b + c \n  \n Use(1, Tail*)
def case_spread_fills_remaining_slots : Expr :=
  .block (alg [] [] [privateProp "Tail" (alg [] [] [] [.num 2, .num 3]), privateProp "Use" (alg ["a", "b", "c"] [] [] [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")])] [.call (.resolve "Use") (alg [] [] [] [.num 1, .sequenceSpread (.resolve "Tail")])])
#guard obs case_spread_fills_remaining_slots == "ok raw=6 n=1"

-- empty-count-one-arg [empty-visible-vs-spread]: count(())
def case_empty_count_one_arg : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_empty_count_one_arg == "ok raw=0 n=1"

-- empty-count-two-args [empty-visible-vs-spread]: count(((), ()))
def case_empty_count_two_args : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_empty_count_two_args == "ok raw=2 n=1"

-- fixed-empty-arg-visible [empty-visible-vs-spread]: F(a) = a \n F(())
def case_fixed_empty_arg_visible : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_fixed_empty_arg_visible == "ok raw=S[] n=1"

-- fixed-empty-spread-zero-items [empty-visible-vs-spread]: F(a) = a \n F(()*)
def case_fixed_empty_spread_zero_items : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_fixed_empty_spread_zero_items == "err arity"

-- variadic-empty-arg-vs-spread [empty-visible-vs-spread]: F(*a) = a.count \n F(())
def case_variadic_empty_arg_vs_spread : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.dotCall (.param "a") "count" none])] [.call (.resolve "F") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_variadic_empty_arg_vs_spread == "ok raw=1 n=1"

-- spread-empty-in-sequence [empty-visible-vs-spread]: (()*, 99)
def case_spread_empty_in_sequence : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [.sequenceSpread (.emptySequence 0), .num 99]))])
#guard obs case_spread_empty_in_sequence == "ok raw=99 n=1"

-- empty-visible-in-sequence [empty-visible-vs-spread]: ((), 99)
def case_empty_visible_in_sequence : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), .num 99]))])
#guard obs case_empty_visible_in_sequence == "ok raw=S[S[], 99] n=1"

-- empty-visible-at-root [empty-visible-vs-spread]: (), 99
def case_empty_visible_at_root : Expr :=
  .block (alg [] [] [] [(.emptySequence 0), .num 99])
#guard obs case_empty_visible_at_root == "ok raw=S[S[], 99] n=2"

-- decon-pair [deconstruction]: x, y = 1, 2 \n x \n y
def case_decon_pair : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x", .resolve "y"])
#guard obs case_decon_pair == "ok raw=S[1, 2] n=2"

-- decon-collecting-tail [deconstruction]: x, *rest = 1, 2, 3 \n rest
def case_decon_collecting_tail : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "rest" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) (alg [] [] [] [.resolve "d"])])] [.resolve "rest"])
#guard obs case_decon_collecting_tail == "ok raw=L[2, 3] n=1"

-- decon-collecting-head [deconstruction]: *head, last = 1, 2, 3 \n head \n last
def case_decon_collecting_head : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "head" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "head", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "head"])) (alg [] [] [] [.resolve "d"])]), privateProp "last" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "head", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "last"])) (alg [] [] [] [.resolve "d"])])] [.resolve "head", .resolve "last"])
#guard obs case_decon_collecting_head == "ok raw=S[L[1, 2], 3] n=2"

-- decon-collecting-middle [deconstruction]: x, *middle, z = 1, 2, 3, 4 \n middle
def case_decon_collecting_middle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4]), privateProp "middle" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "middle", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "middle"])) (alg [] [] [] [.resolve "d"])])] [.resolve "middle"])
#guard obs case_decon_collecting_middle == "ok raw=L[2, 3] n=1"

-- decon-empty-collecting [deconstruction]: x, *rest = 1 \n rest \n x
def case_decon_empty_collecting : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1]), privateProp "rest" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) (alg [] [] [] [.resolve "d"])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "rest", .resolve "x"])
#guard obs case_decon_empty_collecting == "ok raw=S[L[], 1] n=2"

-- decon-arity-under [deconstruction]: x, y = 1 \n x
def case_decon_arity_under : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_decon_arity_under == "err arity"

-- decon-arity-over [deconstruction]: x, y = 1, 2, 3 \n x
def case_decon_arity_over : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_decon_arity_over == "err arity"

-- decon-unpacks-stored-value [deconstruction]: A = 1, 2, 3 \n x, y, z = A \n y
def case_decon_unpacks_stored_value : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "d" (alg [] [] [] [.resolve "A"]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_decon_unpacks_stored_value == "ok raw=2 n=1"

-- decon-tutorial-full [deconstruction]: A = 1, 2, 3, 4, 5 \n  \n x, *y, z = A \n x \n y \n z
def case_decon_tutorial_full : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]), privateProp "d" (alg [] [] [] [.resolve "A"]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x", .resolve "y", .resolve "z"])
#guard obs case_decon_tutorial_full == "ok raw=S[1, L[2, 3, 4], 5] n=3"

-- decon-lone-collecting [deconstruction]: *all = 1, 2, 3 \n all
def case_decon_lone_collecting : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "all" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "all", kind := .collecting }]] [] [] [.param "all"])) (alg [] [] [] [.resolve "d"])])] [.resolve "all"])
#guard obs case_decon_lone_collecting == "ok raw=L[1, 2, 3] n=1"

-- variadic-grouped-and-spread [variadic-calls]: A = 1, 2, 3, 4, 5 \n  \n G(*x) = x.sum \n  \n G(A*) \n G(1, 2, 3, 4, 5)
def case_variadic_grouped_and_spread : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]), privateProp "G" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [.dotCall (.param "x") "sum" none])] [.call (.resolve "G") (alg [] [] [] [.sequenceSpread (.resolve "A")]), .call (.resolve "G") (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])])
#guard obs case_variadic_grouped_and_spread == "ok raw=S[15, 15] n=2"

-- variadic-siblings-preserved [variadic-calls]: A = 1, 2 \n B = 3, 4 \n  \n G(*x) = x.count \n  \n G(A, B) \n G(A*, B*)
def case_variadic_siblings_preserved : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2]), privateProp "B" (alg [] [] [] [.num 3, .num 4]), privateProp "G" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [.dotCall (.param "x") "count" none])] [.call (.resolve "G") (alg [] [] [] [.resolve "A", .resolve "B"]), .call (.resolve "G") (alg [] [] [] [.sequenceSpread (.resolve "A"), .sequenceSpread (.resolve "B")])])
#guard obs case_variadic_siblings_preserved == "ok raw=S[2, 4] n=2"

-- variadic-capture-collects-list [variadic-calls]: F(*x) = x \n F(1, 2, 3)
def case_variadic_capture_collects_list : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [.param "x"])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])
#guard obs case_variadic_capture_collects_list == "ok raw=L[1, 2, 3] n=1"

-- variadic-forwarding-list-spread [variadic-calls]: Target(*items) = items \n Forward(*items) = Target(items*) \n  \n Forward(1, 2) \n Forward([1, 2])
def case_variadic_forwarding_list_spread : Expr :=
  .block (alg [] [] [privateProp "Target" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Forward" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.call (.resolve "Target") (alg [] [] [] [.sequenceSpread (.param "items")])])] [.call (.resolve "Forward") (alg [] [] [] [.num 1, .num 2]), .call (.resolve "Forward") (alg [] [] [] [(.listLiteral [.num 1, .num 2])])])
#guard obs case_variadic_forwarding_list_spread == "ok raw=S[L[1, 2], L[L[1, 2]]] n=2"

-- implicit-forwarding-source-kind [variadic-calls]: Target(*items) = items \n Use(items) = Target \n UseVariadic(*items) = Target \n  \n Use([1, 2]) \n Use((1, 2)) \n UseVariadic(1, 2)
def case_implicit_forwarding_source_kind : Expr :=
  .block (alg [] [] [privateProp "Target" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Use" (alg ["items"] [] [] [.call (.resolve "Target") (alg [] [] [] [.param "items"])]), privateProp "UseVariadic" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.call (.resolve "Target") (alg [] [] [] [.sequenceSpread (.param "items")])])] [.call (.resolve "Use") (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), .call (.resolve "Use") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))]), .call (.resolve "UseVariadic") (alg [] [] [] [.num 1, .num 2])])
#guard obs case_implicit_forwarding_source_kind == "ok raw=S[L[L[1, 2]], L[S[1, 2]], L[1, 2]] n=3"

-- variadic-receiver-distinction [variadic-calls]: Inspect(*items) = items \n A = [1, 2, 3] \n  \n Inspect(A) \n Inspect(A*)
def case_variadic_receiver_distinction : Expr :=
  .block (alg [] [] [privateProp "Inspect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])] [.call (.resolve "Inspect") (alg [] [] [] [.resolve "A"]), .call (.resolve "Inspect") (alg [] [] [] [.sequenceSpread (.resolve "A")])])
#guard obs case_variadic_receiver_distinction == "ok raw=S[L[L[1, 2, 3]], L[1, 2, 3]] n=2"

-- mixed-collecting-parameter [variadic-calls]: F(x, *y, z) = x + y.sum + z \n F(1, 2, 3, 4, 5)
def case_mixed_collecting_parameter : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "x" }, { name := "y", kind := .collecting }, { name := "z" }] [] [] [.binary .add (.binary .add (.param "x") (.dotCall (.param "y") "sum" none)) (.param "z")])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])])
#guard obs case_mixed_collecting_parameter == "ok raw=15 n=1"

-- mixed-front-back-family [variadic-calls]: Arg = 1, 2, 3 \n  \n Head(first, *rest) = first \n Tail(first, *rest) = rest \n Init(*init, last) = init \n Last(*init, last) = last \n  \n Head(1, (2, 3)) \n Tail(1, (2, 3)) \n Init((1, 2), 3) \n Last(Arg, 3)
def case_mixed_front_back_family : Expr :=
  .block (alg [] [] [privateProp "Arg" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "Head" (algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "first"]), privateProp "Tail" (algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "rest"]), privateProp "Init" (algWithParameters [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "init"]), privateProp "Last" (algWithParameters [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "last"])] [.call (.resolve "Head") (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))]), .call (.resolve "Tail") (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))]), .call (.resolve "Init") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), .num 3]), .call (.resolve "Last") (alg [] [] [] [.resolve "Arg", .num 3])])
#guard obs case_mixed_front_back_family == "ok raw=S[1, L[S[2, 3]], L[S[1, 2]], 3] n=4"

-- collecting-minimum-arity [variadic-calls]: F(first, *middle, last) = middle \n  \n F(1, 2) \n F(1, 2, 3)
def case_collecting_minimum_arity : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }] [] [] [.param "middle"])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2]), .call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])
#guard obs case_collecting_minimum_arity == "ok raw=S[L[], L[2]] n=2"

-- variadic-grouped-vs-spread [variadic-calls]: H(h, *t) = t \n H((1, 2))
def case_variadic_grouped_vs_spread : Expr :=
  .block (alg [] [] [privateProp "H" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [.call (.resolve "H") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])])
#guard obs case_variadic_grouped_vs_spread == "ok raw=L[] n=1"

-- variadic-nested-not-flattened [variadic-calls]: Arg = (1, 2), (3, 4) \n  \n Many(*values) = values.count \n Flattened = atoms(Arg).count \n  \n Many(Arg*) \n Flattened
def case_variadic_nested_not_flattened : Expr :=
  .block (alg [] [] [privateProp "Arg" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]), privateProp "Many" (algWithParameters [{ name := "values", kind := .collecting }] [] [] [.dotCall (.param "values") "count" none]), privateProp "Flattened" (alg [] [] [] [.dotCall (.call (.resolve "atoms") (alg [] [] [] [.resolve "Arg"])) "count" none])] [.call (.resolve "Many") (alg [] [] [] [.sequenceSpread (.resolve "Arg")]), .resolve "Flattened"])
#guard obs case_variadic_nested_not_flattened == "ok raw=S[2, 4] n=2"

-- supply-vs-value-patterns [variadic-calls]: CountValues(*values) = values.count \n CountSequenceValue((*values)) = values.count \n  \n CountValues() \n CountValues(1, 2, 3) \n CountValues((1, 2, 3)) \n CountSequenceValue((1, 2, 3))
def case_supply_vs_value_patterns : Expr :=
  .block (alg [] [] [privateProp "CountValues" (algWithParameters [{ name := "values", kind := .collecting }] [] [] [.dotCall (.param "values") "count" none]), privateProp "CountSequenceValue" (algWithParameterPatterns [.sequenceValue [.capture { name := "values", kind := .collecting }]] [] [] [.dotCall (.param "values") "count" none])] [.call (.resolve "CountValues") (alg [] [] [] []), .call (.resolve "CountValues") (alg [] [] [] [.num 1, .num 2, .num 3]), .call (.resolve "CountValues") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]), .call (.resolve "CountSequenceValue") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))])])
#guard obs case_supply_vs_value_patterns == "ok raw=S[0, 3, 1, 3] n=4"

-- redundant-call-parens-canonical [variadic-calls]: Inner = (1, 2, 3) \n CountSequenceValue((*values)) = values.count \n NestedCount(((*values))) = values.count \n  \n CountSequenceValue(Inner) \n CountSequenceValue((Inner)) \n CountSequenceValue(((1, 2, 3))) \n NestedCount(((1, 2, 3))) \n NestedCount((((1, 2, 3))))
def case_redundant_call_parens_canonical : Expr :=
  .block (alg [] [] [privateProp "Inner" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]), privateProp "CountSequenceValue" (algWithParameterPatterns [.sequenceValue [.capture { name := "values", kind := .collecting }]] [] [] [.dotCall (.param "values") "count" none]), privateProp "NestedCount" (algWithParameterPatterns [.sequenceValue [.sequenceValue [.capture { name := "values", kind := .collecting }]]] [] [] [.dotCall (.param "values") "count" none])] [.call (.resolve "CountSequenceValue") (alg [] [] [] [.resolve "Inner"]), .call (.resolve "CountSequenceValue") (alg [] [] [] [(.block (alg [] [] [] [.resolve "Inner"]))]), .call (.resolve "CountSequenceValue") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]))]), .call (.resolve "NestedCount") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]))]), .call (.resolve "NestedCount") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]))]))])])
#guard obs case_redundant_call_parens_canonical == "ok raw=S[3, 1, 1, 3, 3] n=5"

-- call-spread-into-conditional-clauses [variadic-calls]: F(0, 0) = 100 \n F(x, y) = x + y \n A = (1, 2) \n F(A*)
def case_call_spread_into_conditional_clauses : Expr :=
  .block (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.litInt 0, .litInt 0], alg [] [] [] [.num 100]⟩, ⟨.sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")]⟩]), privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.resolve "A")])])
#guard obs case_call_spread_into_conditional_clauses == "ok raw=3 n=1"

-- patterned-user-call-is-one-value-boundary [item-supply-vs-value]: F((x)) = 1, 2 \n F((7))
def case_patterned_user_call_is_one_value_boundary : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }]] [] [] [.num 1, .num 2])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [.num 7]))])])
#guard obs case_patterned_user_call_is_one_value_boundary == "ok raw=S[1, 2] n=1"

-- conditional-singleton-head-binds-its-argument-whole [conditionals]: F((x)) = x \n F(n) = 0 \n F([1, 2])
def case_conditional_singleton_head_binds_its_argument_whole : Expr :=
  .block (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.sequenceValue [.bind "x"]], (alg [] [] [] [.param "x"])⟩, ⟨.bind "n", (alg [] [] [] [.num 0])⟩])] [(.call (.resolve "F") (alg [] [] [] [(.listLiteral [.num 1, .num 2])]))])
#guard obs case_conditional_singleton_head_binds_its_argument_whole == "ok raw=L[1, 2] n=1"

-- conditional-clause-head-rejects-extra-arguments [conditionals]: F(0) = 1 \n F(n) = 2 \n F(1, 2)
def case_conditional_clause_head_rejects_extra_arguments : Expr :=
  .block (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [.num 2])⟩])] [(.call (.resolve "F") (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_conditional_clause_head_rejects_extra_arguments == "err branch"

-- call-spread-dispatches-before-clause-selection [variadic-calls]: F(0, 0) = 100 \n F(x, y) = x + y \n A = (0, 0) \n F(A*)
def case_call_spread_dispatches_before_clause_selection : Expr :=
  .block (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.litInt 0, .litInt 0], alg [] [] [] [.num 100]⟩, ⟨.sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")]⟩]), privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 0, .num 0]))])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.resolve "A")])])
#guard obs case_call_spread_dispatches_before_clause_selection == "ok raw=100 n=1"

-- call-spread-into-patterned-callee [variadic-calls]: F(x, x) = x + 1 \n A = (7, 7) \n F(A*)
def case_call_spread_into_patterned_callee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "x" }, { name := "x" }] [] [] [.binary .add (.param "x") (.num 1)]), privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 7, .num 7]))])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.resolve "A")])])
#guard obs case_call_spread_into_patterned_callee == "ok raw=8 n=1"

-- wrapped-pair-collapses [sequence-construction]: ((1, 2))
def case_wrapped_pair_collapses : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))]))])
#guard obs case_wrapped_pair_collapses == "ok raw=S[1, 2] n=1"

-- pair-of-pairs-preserved [sequence-construction]: ((1, 2), (3, 4))
def case_pair_of_pairs_preserved : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])
#guard obs case_pair_of_pairs_preserved == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- pair-then-empty-preserved [sequence-construction]: ((1, 2), ())
def case_pair_then_empty_preserved : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.emptySequence 0)]))])
#guard obs case_pair_then_empty_preserved == "ok raw=S[S[1, 2], S[]] n=1"

-- spread-splices-into-sequence [sequence-construction]: x = (1, 2) \n (x*, 99)
def case_spread_splices_into_sequence : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [(.block (alg [] [] [] [.sequenceSpread (.resolve "x"), .num 99]))])
#guard obs case_spread_splices_into_sequence == "ok raw=S[1, 2, 99] n=1"

-- spread-empty-between-siblings [sequence-construction]: (1*, (), 2*)
def case_spread_empty_between_siblings : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [.sequenceSpread (.num 1), (.emptySequence 0), .sequenceSpread (.num 2)]))])
#guard obs case_spread_empty_between_siblings == "ok raw=S[1, S[], 2] n=1"

-- root-spread-beside-slot [sequence-construction]: A = (1, 2) \n A*, 99
def case_root_spread_beside_slot : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.sequenceSpread (.resolve "A"), .num 99])
#guard obs case_root_spread_beside_slot == "ok raw=S[1, 2, 99] n=3"

-- root-spread-then-value-slot [sequence-construction]: First = 1, 2 \n Second = 3, 4 \n  \n First*, Second
def case_root_spread_then_value_slot : Expr :=
  .block (alg [] [] [privateProp "First" (alg [] [] [] [.num 1, .num 2]), privateProp "Second" (alg [] [] [] [.num 3, .num 4])] [.sequenceSpread (.resolve "First"), .resolve "Second"])
#guard obs case_root_spread_then_value_slot == "ok raw=S[1, 2, S[3, 4]] n=3"

-- spread-slots-capture [sequence-construction]: A = 1, 2 \n B = 1*, 2 \n  \n A.count \n B.count
def case_spread_slots_capture : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2]), privateProp "B" (alg [] [] [] [.sequenceSpread (.num 1), .num 2])] [.dotCall (.resolve "A") "count" none, .dotCall (.resolve "B") "count" none])
#guard obs case_spread_slots_capture == "ok raw=S[2, 2] n=2"

-- spread-one-level-only [sequence-construction]: (1, (2, 3))*, 4
def case_spread_one_level_only : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))])), .num 4])
#guard obs case_spread_one_level_only == "ok raw=S[1, S[2, 3], 4] n=3"

-- dot-access-value-boundary [access-boundaries]: A = { \n     X = 1, 2, 3 \n } \n A.X
def case_dot_access_value_boundary : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dot_access_value_boundary == "ok raw=S[1, 2, 3] n=1"

-- output-dotted-access-ordinary [access-boundaries]: A = { \n     Output = 9 \n } \n  \n A.Output
def case_output_dotted_access_ordinary : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [privateProp "Output" (alg [] [] [] [.num 9])] [])] [.dotCall (.resolve "A") "Output" none])
#guard obs case_output_dotted_access_ordinary == "ok raw=9 n=1"

-- property-call-boundary [access-boundaries]: P = 1, 2, 3 \n P()
def case_property_call_boundary : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.call (.resolve "P") (alg [] [] [] [])])
#guard obs case_property_call_boundary == "ok raw=S[1, 2, 3] n=1"

-- builtin-result-reentry [access-boundaries]: x = take((1, 2, 3), 2) \n x
def case_builtin_result_reentry : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .num 2])])] [.resolve "x"])
#guard obs case_builtin_result_reentry == "ok raw=L[1, 2] n=1"

-- zero-arg-access-of-parametrized [access-boundaries]: Add(a, b) = a + b \n  \n Add \n (1, 2)
def case_zero_arg_access_of_parametrized : Expr :=
  .block (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")])] [.resolve "Add", (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_zero_arg_access_of_parametrized == "err arity"

-- take-prefix [collection-builtins]: take((1, 2, 3, 4, 5), 3)
def case_take_prefix : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])), .num 3])])
#guard obs case_take_prefix == "ok raw=L[1, 2, 3] n=1"

-- take-single-survivor [collection-builtins]: take(((1, 2), (3, 4)), 1)
def case_take_single_survivor : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1])])
#guard obs case_take_single_survivor == "ok raw=L[S[1, 2]] n=1"

-- take-zero-empty [collection-builtins]: take((1, 2, 3), 0)
def case_take_zero_empty : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .num 0])])
#guard obs case_take_zero_empty == "ok raw=L[] n=1"

-- skip-prefix [collection-builtins]: skip((1, 2, 3, 4, 5), 3)
def case_skip_prefix : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])), .num 3])])
#guard obs case_skip_prefix == "ok raw=L[4, 5] n=1"

-- filter-keeps-matching [collection-builtins]: IsEven = x mod 2 == 0 \n filter((1, 2, 3, 4, 5, 6), IsEven)
def case_filter_keeps_matching : Expr :=
  .block (alg [] [] [privateProp "IsEven" (alg ["x"] [] [] [.binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5, .num 6])), .resolve "IsEven"])])
#guard obs case_filter_keeps_matching == "ok raw=L[2, 4, 6] n=1"

-- filter-single-survivor [collection-builtins]: Big(a) = a > 2 \n filter((1, 2, 3), Big)
def case_filter_single_survivor : Expr :=
  .block (alg [] [] [privateProp "Big" (alg ["a"] [] [] [.binary .gt (.param "a") (.num 2)])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "Big"])])
#guard obs case_filter_single_survivor == "ok raw=L[3] n=1"

-- filter-none-empty [collection-builtins]: No(a) = 0 \n filter((1, 2, 3), No)
def case_filter_none_empty : Expr :=
  .block (alg [] [] [privateProp "No" (alg ["a"] [] [] [.num 0])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "No"])])
#guard obs case_filter_none_empty == "ok raw=L[] n=1"

-- map-transforms-items [collection-builtins]: Double = x * 2 \n map((1, 2, 3), Double)
def case_map_transforms_items : Expr :=
  .block (alg [] [] [privateProp "Double" (alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "Double"])])
#guard obs case_map_transforms_items == "ok raw=L[2, 4, 6] n=1"

-- map-single-item [collection-builtins]: M(a) = a \n map((7), M)
def case_map_single_item : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [.num 7])), .resolve "M"])])
#guard obs case_map_single_item == "ok raw=L[7] n=1"

-- map-pair-callback [collection-builtins]: Swap(a, b) = (b, a) \n map(((1, 2), (3, 4)), Swap)
def case_map_pair_callback : Expr :=
  .block (alg [] [] [privateProp "Swap" (alg ["a", "b"] [] [] [(.block (alg [] [] [] [.param "b", .param "a"]))])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .resolve "Swap"])])
#guard obs case_map_pair_callback == "ok raw=L[S[2, 1], S[4, 3]] n=1"

-- callback-variadic-collects [collection-builtins]: Collect(*items) = items \n  \n [7].map(Collect) \n [(1, 2)].map(Collect) \n [[1, 2]].map(Collect)
def case_callback_variadic_collects : Expr :=
  .block (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [.dotCall (.listLiteral [.num 7]) "map" (some (alg [] [] [] [.resolve "Collect"])), .dotCall (.listLiteral [.block (alg [] [] [] [.num 1, .num 2])]) "map" (some (alg [] [] [] [.resolve "Collect"])), .dotCall (.listLiteral [.listLiteral [.num 1, .num 2]]) "map" (some (alg [] [] [] [.resolve "Collect"]))])
#guard obs case_callback_variadic_collects == "ok raw=S[L[L[7]], L[L[S[1, 2]]], L[L[L[1, 2]]]] n=3"

-- callback-mixed-variadic-rows [collection-builtins]: F(first, *middle, last) = middle \n Rows = [(1, 2, 3, 4)] \n  \n Rows.map(F)
def case_callback_mixed_variadic_rows : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }] [] [] [.param "middle"]), privateProp "Rows" (alg [] [] [] [(.listLiteral [.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4])])])] [.dotCall (.resolve "Rows") "map" (some (alg [] [] [] [.resolve "F"]))])
#guard obs case_callback_mixed_variadic_rows == "ok raw=L[L[2, 3]] n=1"

-- distinct-preserves-first [collection-builtins]: distinct((3, 1, 3, 2, 1, 2))
def case_distinct_preserves_first : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2]))])])
#guard obs case_distinct_preserves_first == "ok raw=L[3, 1, 2] n=1"

-- distinct-structural-pairs [collection-builtins]: distinct(((1, 2), (1, 2), (3, 4)))
def case_distinct_structural_pairs : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])])
#guard obs case_distinct_structural_pairs == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- take-family-tutorial [collection-builtins]: take((1, 2, 3, 4, 5), 3) \n  \n take(((1, 2), (3, 4)), 1) \n  \n range(1, 5).take(2)
def case_take_family_tutorial : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])), .num 3]), .call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1]), .dotCall (.call (.resolve "range") (alg [] [] [] [.num 1, .num 5])) "take" (some (alg [] [] [] [.num 2]))])
#guard obs case_take_family_tutorial == "ok raw=S[L[1, 2, 3], L[S[1, 2]], L[1, 2]] n=3"

-- distinct-family-tutorial [collection-builtins]: distinct((3, 1, 3, 2, 1, 2)) \n  \n distinct(((1, 2), (1, 2), (3, 4))) \n  \n Values = 3, 1, 3, 2, 1, 2 \n Values.distinct
def case_distinct_family_tutorial : Expr :=
  .block (alg [] [] [privateProp "Values" (alg [] [] [] [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2])] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2]))]), .call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))]), .dotCall (.resolve "Values") "distinct" none])
#guard obs case_distinct_family_tutorial == "ok raw=S[L[3, 1, 2], L[S[1, 2], S[3, 4]], L[3, 1, 2]] n=3"

-- spread-one-level-family [sequence-construction]: (1, 2)*, 3 \n 1*, (2, 3) \n (1, (2, 3))*, 4
def case_spread_one_level_family : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [.num 1, .num 2])), .num 3, .sequenceSpread (.num 1), (.block (alg [] [] [] [.num 2, .num 3])), .sequenceSpread (.block (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))])), .num 4])
#guard obs case_spread_one_level_family == "ok raw=S[1, 2, 3, 1, S[2, 3], 1, S[2, 3], 4] n=8"

-- distinct-empties-collapse [collection-builtins]: distinct(((), ()))
def case_distinct_empties_collapse : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_distinct_empties_collapse == "ok raw=L[S[]] n=1"

-- order-sorts-atoms [collection-builtins]: order((3, 4, 2, 1, 3, 3))
def case_order_sorts_atoms : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]))])])
#guard obs case_order_sorts_atoms == "ok raw=L[1, 2, 3, 3, 3, 4] n=1"

-- range-inclusive [collection-builtins]: range(1, 5)
def case_range_inclusive : Expr :=
  .block (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 5])])
#guard obs case_range_inclusive == "ok raw=L[1, 2, 3, 4, 5] n=1"

-- range-single-value [collection-builtins]: range(3, 3)
def case_range_single_value : Expr :=
  .block (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 3, .num 3])])
#guard obs case_range_single_value == "ok raw=L[3] n=1"

-- spread-arguments-keep-written-order [collection-builtins]: Lo = 2 \n Hi = 4 \n range(Lo*, Hi*)
def case_spread_arguments_keep_written_order : Expr :=
  .block (alg [] [] [privateProp "Lo" (alg [] [] [] [.num 2]), privateProp "Hi" (alg [] [] [] [.num 4])] [.call (.resolve "range") (alg [] [] [] [.sequenceSpread (.resolve "Lo"), .sequenceSpread (.resolve "Hi")])])
#guard obs case_spread_arguments_keep_written_order == "ok raw=L[2, 3, 4] n=1"

-- atoms-recursive-flatten [collection-builtins]: atoms(((1, 2), (3, 4)))
def case_atoms_recursive_flatten : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])])
#guard obs case_atoms_recursive_flatten == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms-exact-list-result [collection-builtins]: atoms(7)
def case_atoms_exact_list_result : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [.num 7])])
#guard obs case_atoms_exact_list_result == "ok raw=L[7] n=1"

-- atoms-list-traversal [collection-builtins]: atoms([1, 2])
def case_atoms_list_traversal : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [.listLiteral [.num 1, .num 2]])])
#guard obs case_atoms_list_traversal == "ok raw=L[1, 2] n=1"

-- atoms-mixed-traversal [collection-builtins]: atoms([(1, 2), [3, [4]]])
def case_atoms_mixed_traversal : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [.listLiteral [(.block (alg [] [] [] [.num 1, .num 2])), .listLiteral [.num 3, .listLiteral [.num 4]]]])])
#guard obs case_atoms_mixed_traversal == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms-list-composition [collection-builtins]: [1, 2, 3].skip(1).atoms
def case_atoms_list_composition : Expr :=
  .block (alg [] [] [] [.dotCall (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) "skip" (some (alg [] [] [] [.num 1]))) "atoms" none])
#guard obs case_atoms_list_composition == "ok raw=L[2, 3] n=1"

-- atoms-no-truthiness [collection-builtins]: if((1, [2]), 10, 20)
def case_atoms_no_truthiness : Expr :=
  .block (alg [] [] [] [.call (.resolve "if") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .listLiteral [.num 2]])), .num 10, .num 20])])
#guard obs case_atoms_no_truthiness == "ok raw=10 n=1"

-- sum-of-range-collection [collection-builtins]: sum(range(1, 3))
def case_sum_of_range_collection : Expr :=
  .block (alg [] [] [] [.call (.resolve "sum") (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])])])
#guard obs case_sum_of_range_collection == "ok raw=6 n=1"

-- count-family [collection-builtins]: count(()) \n count((())) \n  \n count(range(1, 5)) \n  \n count((10, 20, 30)) \n  \n count((3, 4, range(1, 5)*, 7)) \n  \n count((range(1, 5)*, 7)) \n  \n count(((1, 2), (3, 4))) \n  \n Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5) \n (Data:0).count
def case_count_family : Expr :=
  .block (alg [] [] [privateProp "Data" (alg [] [] [] [(.block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1])), (.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]))])] [.call (.resolve "count") (alg [] [] [] [(.emptySequence 0)]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), .call (.resolve "count") (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 5])]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [.num 10, .num 20, .num 30]))]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [.num 3, .num 4, .sequenceSpread (.call (.resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7]))]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [.sequenceSpread (.call (.resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7]))]), .call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))]), .dotCall (.index (.resolve "Data") (.num 0)) "count" none])
#guard obs case_count_family == "ok raw=S[0, 0, 5, 3, 8, 6, 2, 5] n=8"

-- count-scalar-and-string [collection-builtins]: count(5)
def case_count_scalar_and_string : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.num 5])])
#guard obs case_count_scalar_and_string == "ok raw=1 n=1"

-- count-dotcount-agree [collection-builtins]: T = (1, 2, 3) \n T.count \n  \n A = 1, 2, 3 \n A.count \n  \n count(A)
def case_count_dotcount_agree : Expr :=
  .block (alg [] [] [privateProp "T" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))]), privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.dotCall (.resolve "T") "count" none, .dotCall (.resolve "A") "count" none, .call (.resolve "count") (alg [] [] [] [.resolve "A"])])
#guard obs case_count_dotcount_agree == "ok raw=S[3, 3, 3] n=3"

-- if-value-boundary [collection-builtins]: X = 1, 2, 3 \n if(1, X, X)
def case_if_value_boundary : Expr :=
  .block (alg [] [] [privateProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [.call (.resolve "if") (alg [] [] [] [.num 1, .resolve "X", .resolve "X"])])
#guard obs case_if_value_boundary == "ok raw=S[1, 2, 3] n=1"

-- builtin-fixed-collection-arity [collection-builtins]: count((1, 2, 3))
def case_builtin_fixed_collection_arity : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3]))])])
#guard obs case_builtin_fixed_collection_arity == "ok raw=3 n=1"

-- reduce-accumulates-value [collection-builtins]: Append(item, *history) = (history*, item) \n reduce((2, 3, 4), Append, 1)
def case_reduce_accumulates_value : Expr :=
  .block (alg [] [] [privateProp "Append" (algWithParameters [{ name := "item" }, { name := "history", kind := .collecting }] [] [] [(.block (alg [] [] [] [.sequenceSpread (.param "history"), .param "item"]))])] [.call (.resolve "reduce") (alg [] [] [] [(.block (alg [] [] [] [.num 2, .num 3, .num 4])), .resolve "Append", .num 1])])
#guard obs case_reduce_accumulates_value == "ok raw=S[1, 2, 3, 4] n=1"

-- reduce-empty-initial-is-one-value [collection-builtins]: R(x, acc) = acc + x \n Init = 1, 2 \n reduce((), R, Init)
def case_reduce_empty_initial_is_one_value : Expr :=
  .block (alg [] [] [privateProp "R" (alg ["x", "acc"] [] [] [.binary .add (.param "acc") (.param "x")]), privateProp "Init" (alg [] [] [] [.num 1, .num 2])] [.call (.resolve "reduce") (alg [] [] [] [(.emptySequence 0), .resolve "R", .resolve "Init"])])
#guard obs case_reduce_empty_initial_is_one_value == "ok raw=S[1, 2] n=1"

-- eq-structural-nested [equality-and-indexing]: A = 1, (2, 3) \n B = 1, (2, 3) \n A == B
def case_eq_structural_nested : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))]), privateProp "B" (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 2, .num 3]))])] [.binary .eq (.resolve "A") (.resolve "B")])
#guard obs case_eq_structural_nested == "ok raw=1 n=1"

-- index-selects-atom [equality-and-indexing]: Nums = 10, 20, 30, 40, 50 \n  \n # Select the third value (index 2): \n Nums:2
def case_index_selects_atom : Expr :=
  .block (alg [] [] [privateProp "Nums" (alg [] [] [] [.num 10, .num 20, .num 30, .num 40, .num 50])] [.index (.resolve "Nums") (.num 2)])
#guard obs case_index_selects_atom == "ok raw=30 n=1"

-- index-projects-one-level [equality-and-indexing]: Pairs = (1, 2), (3, 4) \n Pairs:0
def case_index_projects_one_level : Expr :=
  .block (alg [] [] [privateProp "Pairs" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])] [.index (.resolve "Pairs") (.num 0)])
#guard obs case_index_projects_one_level == "ok raw=S[1, 2] n=2"

-- index-nested-stays-intact [equality-and-indexing]: Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8)) \n Bags:0 \n Bags:0:1
def case_index_nested_stays_intact : Expr :=
  .block (alg [] [] [privateProp "Bags" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), (.block (alg [] [] [] [(.block (alg [] [] [] [.num 5, .num 6])), (.block (alg [] [] [] [.num 7, .num 8]))]))])] [.index (.resolve "Bags") (.num 0), .index (.index (.resolve "Bags") (.num 0)) (.num 1)])
#guard obs case_index_nested_stays_intact == "ok raw=S[S[S[1, 2], S[3, 4]], S[3, 4]] n=4"

-- index-empty-item-visible [equality-and-indexing]: x = ((), ()) \n x:0
def case_index_empty_item_visible : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index_empty_item_visible == "ok raw=S[] n=1"

-- index-out-of-range [equality-and-indexing]: x = (1, 2) \n x:9
def case_index_out_of_range : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_index_out_of_range == "err index"

-- index-captured-requality [equality-and-indexing]: x = ((1, 2), (3, 4)) \n y = x:0 \n y == (1, 2)
def case_index_captured_requality : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))]), privateProp "y" (alg [] [] [] [.index (.resolve "x") (.num 0)])] [.binary .eq (.resolve "y") (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_index_captured_requality == "ok raw=1 n=1"

-- output-rows-interleave-definitions [parser-layout]: A = 3 \n A + B \n B = 2
def case_output_rows_interleave_definitions : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 3]), privateProp "B" (alg [] [] [] [.num 2])] [.binary .add (.resolve "A") (.resolve "B")])
#guard obs case_output_rows_interleave_definitions == "ok raw=5 n=1"

-- trailing-comma-continues-line [parser-layout]: 1, \n 2
def case_trailing_comma_continues_line : Expr :=
  .block (alg [] [] [] [.num 1, .num 2])
#guard obs case_trailing_comma_continues_line == "ok raw=S[1, 2] n=2"

-- adjacency-call-across-space [parser-layout]: Add(a, b) = a + b \n  \n Add(1, 2)    # 3 \n Add (1, 2)   # the same call, 3
def case_adjacency_call_across_space : Expr :=
  .block (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")])] [.call (.resolve "Add") (alg [] [] [] [.num 1, .num 2]), .call (.resolve "Add") (alg [] [] [] [.num 1, .num 2])])
#guard obs case_adjacency_call_across_space == "ok raw=S[3, 3] n=2"

-- multiline-call-open-delimiter [parser-layout]: Add(a, b) = a + b \n  \n Add( \n   1, 2 \n )
def case_multiline_call_open_delimiter : Expr :=
  .block (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")])] [.call (.resolve "Add") (alg [] [] [] [.num 1, .num 2])])
#guard obs case_multiline_call_open_delimiter == "ok raw=3 n=1"

-- newline-ends-property-body [parser-layout]: P = 1 \n 2
def case_newline_ends_property_body : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1])] [.num 2])
#guard obs case_newline_ends_property_body == "ok raw=2 n=1"

-- comment-does-not-change-parse [parser-layout]: # comment \n 1 + 1
def case_comment_does_not_change_parse : Expr :=
  .block (alg [] [] [] [.binary .add (.num 1) (.num 1)])
#guard obs case_comment_does_not_change_parse == "ok raw=2 n=1"

-- spread-binds-before-list [parser-layout]: X(*vals) = vals.count \n b = (1, 2) \n X(7 b*)
def case_spread_binds_before_list : Expr :=
  .block (alg [] [] [privateProp "X" (algWithParameters [{ name := "vals", kind := .collecting }] [] [] [.dotCall (.param "vals") "count" none]), privateProp "b" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.call (.resolve "X") (alg [] [] [] [.num 7, .sequenceSpread (.resolve "b")])])
#guard obs case_spread_binds_before_list == "ok raw=3 n=1"

-- dot-chain-continuation [parser-layout]: (1, 2, 3) \n .map { n * 2 } \n .sum
def case_dot_chain_continuation : Expr :=
  .block (alg [] [] [] [.dotCall (.dotCall (.block (alg [] [] [] [.num 1, .num 2, .num 3])) "map" (some (alg [] [] [] [.block (alg ["n"] [] [] [.binary .mul (.param "n") (.num 2)])]))) "sum" none])
#guard obs case_dot_chain_continuation == "ok raw=12 n=1"

-- arity-too-many-arguments [errors]: KeepFirst(a, b) = a \n KeepFirst(42, 999, 1)
def case_arity_too_many_arguments : Expr :=
  .block (alg [] [] [privateProp "KeepFirst" (alg ["a", "b"] [] [] [.param "a"])] [.call (.resolve "KeepFirst") (alg [] [] [] [.num 42, .num 999, .num 1])])
#guard obs case_arity_too_many_arguments == "err arity"

-- missing-output-not-a-value [errors]: A = { \n } \n A
def case_missing_output_not_a_value : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [])] [.resolve "A"])
#guard obs case_missing_output_not_a_value == "err missingOutput"

-- missing-output-as-builtin-arg [errors]: count({})
def case_missing_output_as_builtin_arg : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] []))])])
#guard obs case_missing_output_as_builtin_arg == "err missingOutput"

-- scalar-op-rejects-sequence [errors]: (1, 2) + 1
def case_scalar_op_rejects_sequence : Expr :=
  .block (alg [] [] [] [.binary .add (.block (alg [] [] [] [.num 1, .num 2])) (.num 1)])
#guard obs case_scalar_op_rejects_sequence == "err type"

-- order-rejects-non-numeric [errors]: order((1, 'hello'))
def case_order_rejects_non_numeric : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [.num 1, (.stringLiteral "hello")]))])])
#guard obs case_order_rejects_non_numeric == "err arity"

-- division-by-zero [errors]: 1 / 0
def case_division_by_zero : Expr :=
  .block (alg [] [] [] [.binary .div (.num 1) (.num 0)])
#guard obs case_division_by_zero == "err div0"

-- spread-arguments-fail-left-to-right [errors]: P = 1 / 0 \n Q = 'x' + 1 \n range(P*, Q*)
def case_spread_arguments_fail_left_to_right : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.binary .div (.num 1) (.num 0)]), privateProp "Q" (alg [] [] [] [.binary .add (.stringLiteral "x") (.num 1)])] [.call (.resolve "range") (alg [] [] [] [.sequenceSpread (.resolve "P"), .sequenceSpread (.resolve "Q")])])
#guard obs case_spread_arguments_fail_left_to_right == "err div0"

-- unresolved-implicit-parameter [errors]: Nope
def case_unresolved_implicit_parameter : Expr :=
  .block (alg ["Nope"] [] [] [.param "Nope"])
#guard obs case_unresolved_implicit_parameter == "err unresolvedImplicitParams"

-- string-equality-exact [strings]: 'ab' == 'ab'
def case_string_equality_exact : Expr :=
  .block (alg [] [] [] [.binary .eq (.stringLiteral "ab") (.stringLiteral "ab")])
#guard obs case_string_equality_exact == "ok raw=1 n=1"

-- string-displays-unquoted [strings]: x = 'ab' \n x
def case_string_displays_unquoted : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.stringLiteral "ab")])] [.resolve "x"])
#guard obs case_string_displays_unquoted == "ok raw='ab' n=1"

-- list-literal [lists]: [1, 2, 3]
def case_list_literal : Expr :=
  .block (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])
#guard obs case_list_literal == "ok raw=L[1, 2, 3] n=1"

-- list-exactness [lists]: [7] == 7 \n [[1, 2]] == [1, 2] \n [[]] == []
def case_list_exactness : Expr :=
  .block (alg [] [] [] [.binary .eq (.listLiteral [.num 7]) (.num 7), .binary .eq (.listLiteral [.listLiteral [.num 1, .num 2]]) (.listLiteral [.num 1, .num 2]), .binary .eq (.listLiteral [.listLiteral []]) (.listLiteral [])])
#guard obs case_list_exactness == "ok raw=S[0, 0, 0] n=3"

-- list-vs-sequence-kind [lists]: [] == () \n [1, 2] == (1, 2)
def case_list_vs_sequence_kind : Expr :=
  .block (alg [] [] [] [.binary .eq (.listLiteral []) (.emptySequence 0), .binary .eq (.listLiteral [.num 1, .num 2]) (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_list_vs_sequence_kind == "ok raw=S[0, 0] n=2"

-- list-index-selects-element [lists]: [1, 2, 3]:0
def case_list_index_selects_element : Expr :=
  .block (alg [] [] [] [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0)])
#guard obs case_list_index_selects_element == "ok raw=1 n=1"

-- list-index-nested-element-stays-exact [lists]: Rows = [[1, 2], [3, 4]] \n Rows:0 \n Rows:0:1
def case_list_index_nested_element_stays_exact : Expr :=
  .block (alg [] [] [privateProp "Rows" (alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]])] [.index (.resolve "Rows") (.num 0), .index (.index (.resolve "Rows") (.num 0)) (.num 1)])
#guard obs case_list_index_nested_element_stays_exact == "ok raw=S[L[1, 2], 2] n=2"

-- list-index-out-of-range [lists]: []:0
def case_list_index_out_of_range : Expr :=
  .block (alg [] [] [] [.index (.listLiteral []) (.num 0)])
#guard obs case_list_index_out_of_range == "err index"

-- list-index-builtin-results [lists]: range(1, 3):2
def case_list_index_builtin_results : Expr :=
  .block (alg [] [] [] [.index (.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])) (.num 2)])
#guard obs case_list_index_builtin_results == "ok raw=3 n=1"

-- list-redundant-parens-canonicalize [lists]: ([1, 2]) == [1, 2]
def case_list_redundant_parens_canonicalize : Expr :=
  .block (alg [] [] [] [.binary .eq (.block (alg [] [] [] [.listLiteral [.num 1, .num 2]])) (.listLiteral [.num 1, .num 2])])
#guard obs case_list_redundant_parens_canonicalize == "ok raw=1 n=1"

-- list-spread-capture [lists]: A = [1, 2, 3] \n  \n x = A \n y = A* \n  \n x \n y
def case_list_spread_capture : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [.resolve "A"]), privateProp "y" (alg [] [] [] [.sequenceSpread (.resolve "A")])] [.resolve "x", .resolve "y"])
#guard obs case_list_spread_capture == "ok raw=S[L[1, 2, 3], S[1, 2, 3]] n=2"

-- list-spread-edges [lists]: A = [] \n B = [7] \n C = [[7]] \n  \n A* \n B* \n C*
def case_list_spread_edges : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "C" (alg [] [] [] [(.listLiteral [.listLiteral [.num 7]])])] [.sequenceSpread (.resolve "A"), .sequenceSpread (.resolve "B"), .sequenceSpread (.resolve "C")])
#guard obs case_list_spread_edges == "ok raw=S[7, L[7]] n=2"

-- list-literal-spread-elements [lists]: A = 1, 2, 3 \n  \n [A*] \n [0, A*, 4]
def case_list_literal_spread_elements : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.listLiteral [.sequenceSpread (.resolve "A")], .listLiteral [.num 0, .sequenceSpread (.resolve "A"), .num 4]])
#guard obs case_list_literal_spread_elements == "ok raw=S[L[1, 2, 3], L[0, 1, 2, 3, 4]] n=2"

-- list-elements-preserve-boundaries [lists]: A = [1, 2] \n B = [3, 4] \n  \n [A, B] \n [A*, B*] \n [A, B*]
def case_list_elements_preserve_boundaries : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [.listLiteral [.resolve "A", .resolve "B"], .listLiteral [.sequenceSpread (.resolve "A"), .sequenceSpread (.resolve "B")], .listLiteral [.resolve "A", .sequenceSpread (.resolve "B")]])
#guard obs case_list_elements_preserve_boundaries == "ok raw=S[L[L[1, 2], L[3, 4]], L[1, 2, 3, 4], L[L[1, 2], 3, 4]] n=3"

-- list-written-slot-reifies-projection [lists]: S = ((1, 2), (3, 4)) \n  \n [S:0, 5] \n [S:0*, 5]
def case_list_written_slot_reifies_projection : Expr :=
  .block (alg [] [] [privateProp "S" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])] [.listLiteral [.index (.resolve "S") (.num 0), .num 5], .listLiteral [.sequenceSpread (.index (.resolve "S") (.num 0)), .num 5]])
#guard obs case_list_written_slot_reifies_projection == "ok raw=S[L[S[1, 2], 5], L[1, 2, 5]] n=2"

-- list-empty-spread-neutral [lists]: [1, []*, 2] \n [1, ()*, 2]
def case_list_empty_spread_neutral : Expr :=
  .block (alg [] [] [] [.listLiteral [.num 1, .sequenceSpread (.listLiteral []), .num 2], .listLiteral [.num 1, .sequenceSpread (.emptySequence 0), .num 2]])
#guard obs case_list_empty_spread_neutral == "ok raw=S[L[1, 2], L[1, 2]] n=2"

-- list-call-boundary [lists]: F(a, b, c) = a + b + c \n One(x) = 7 \n  \n A = [1, 2, 3] \n  \n One(A) \n F(A*)
def case_list_call_boundary : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a", "b", "c"] [] [] [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]), privateProp "One" (alg ["x"] [] [] [.num 7]), privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])] [.call (.resolve "One") (alg [] [] [] [.resolve "A"]), .call (.resolve "F") (alg [] [] [] [.sequenceSpread (.resolve "A")])])
#guard obs case_list_call_boundary == "ok raw=S[7, 6] n=2"

-- list-lone-deconstruction [lists]: x, y, z = [1, 2, 3] \n  \n x \n y \n z
def case_list_lone_deconstruction : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x", .resolve "y", .resolve "z"])
#guard obs case_list_lone_deconstruction == "ok raw=S[1, 2, 3] n=3"

-- list-deconstruction-not-recursive [lists]: x, y = [[1, 2], 3] \n  \n x \n y
def case_list_deconstruction_not_recursive : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.listLiteral [.num 1, .num 2], .num 3])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x", .resolve "y"])
#guard obs case_list_deconstruction_not_recursive == "ok raw=S[L[1, 2], 3] n=2"

-- collecting-binding-exact-list [lists]: x, *rest = [1, 2, 3] \n  \n x \n rest
def case_collecting_binding_exact_list : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])]), privateProp "rest" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x", .resolve "rest"])
#guard obs case_collecting_binding_exact_list == "ok raw=S[1, L[2, 3]] n=2"

-- list-lone-collecting-assignment [lists]: *items = [1, 2, 3] \n items
def case_list_lone_collecting_assignment : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "items" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "items", kind := .collecting }]] [] [] [.param "items"])) (alg [] [] [] [.resolve "d"])])] [.resolve "items"])
#guard obs case_list_lone_collecting_assignment == "ok raw=L[1, 2, 3] n=1"

-- list-builtin-collection [lists]: count([1, 2, 3])
def case_list_builtin_collection : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])])
#guard obs case_list_builtin_collection == "ok raw=3 n=1"

-- 157 canonical Lean-guarded specification cases.

/--
Machine-checked Lean-guarded partition count: the id list is built by the
same loop that emits the guards above, while the expected total is computed
independently from the corpus partition, so a generation bug fails `lake build`.
-/
def specCaseIds : List String := [
  "first-program",
  "property-access-and-call",
  "output-is-ordinary-property",
  "empty-literal",
  "empty-wrapped",
  "empty-wrapped-twice",
  "singleton-paren",
  "singleton-paren-deep",
  "empty-eq-family",
  "empty-capture",
  "supply-three-rows",
  "value-three-items",
  "adjacency-is-comma",
  "capture-supply",
  "capture-supply-spread",
  "call-reentry-identity",
  "call-value-boundary",
  "property-value-boundary",
  "spread-capture-count",
  "repeated-spread-fixed-point",
  "repeated-spread-singleton-opens",
  "scalar-spread-neutral",
  "select-spread-vs-capture-select",
  "fixed-call-preserves-boundaries",
  "spread-fills-remaining-slots",
  "empty-count-one-arg",
  "empty-count-two-args",
  "fixed-empty-arg-visible",
  "fixed-empty-spread-zero-items",
  "variadic-empty-arg-vs-spread",
  "spread-empty-in-sequence",
  "empty-visible-in-sequence",
  "empty-visible-at-root",
  "decon-pair",
  "decon-collecting-tail",
  "decon-collecting-head",
  "decon-collecting-middle",
  "decon-empty-collecting",
  "decon-arity-under",
  "decon-arity-over",
  "decon-unpacks-stored-value",
  "decon-tutorial-full",
  "decon-lone-collecting",
  "variadic-grouped-and-spread",
  "variadic-siblings-preserved",
  "variadic-capture-collects-list",
  "variadic-forwarding-list-spread",
  "implicit-forwarding-source-kind",
  "variadic-receiver-distinction",
  "mixed-collecting-parameter",
  "mixed-front-back-family",
  "collecting-minimum-arity",
  "variadic-grouped-vs-spread",
  "variadic-nested-not-flattened",
  "supply-vs-value-patterns",
  "redundant-call-parens-canonical",
  "call-spread-into-conditional-clauses",
  "patterned-user-call-is-one-value-boundary",
  "conditional-singleton-head-binds-its-argument-whole",
  "conditional-clause-head-rejects-extra-arguments",
  "call-spread-dispatches-before-clause-selection",
  "call-spread-into-patterned-callee",
  "wrapped-pair-collapses",
  "pair-of-pairs-preserved",
  "pair-then-empty-preserved",
  "spread-splices-into-sequence",
  "spread-empty-between-siblings",
  "root-spread-beside-slot",
  "root-spread-then-value-slot",
  "spread-slots-capture",
  "spread-one-level-only",
  "dot-access-value-boundary",
  "output-dotted-access-ordinary",
  "property-call-boundary",
  "builtin-result-reentry",
  "zero-arg-access-of-parametrized",
  "take-prefix",
  "take-single-survivor",
  "take-zero-empty",
  "skip-prefix",
  "filter-keeps-matching",
  "filter-single-survivor",
  "filter-none-empty",
  "map-transforms-items",
  "map-single-item",
  "map-pair-callback",
  "callback-variadic-collects",
  "callback-mixed-variadic-rows",
  "distinct-preserves-first",
  "distinct-structural-pairs",
  "take-family-tutorial",
  "distinct-family-tutorial",
  "spread-one-level-family",
  "distinct-empties-collapse",
  "order-sorts-atoms",
  "range-inclusive",
  "range-single-value",
  "spread-arguments-keep-written-order",
  "atoms-recursive-flatten",
  "atoms-exact-list-result",
  "atoms-list-traversal",
  "atoms-mixed-traversal",
  "atoms-list-composition",
  "atoms-no-truthiness",
  "sum-of-range-collection",
  "count-family",
  "count-scalar-and-string",
  "count-dotcount-agree",
  "if-value-boundary",
  "builtin-fixed-collection-arity",
  "reduce-accumulates-value",
  "reduce-empty-initial-is-one-value",
  "eq-structural-nested",
  "index-selects-atom",
  "index-projects-one-level",
  "index-nested-stays-intact",
  "index-empty-item-visible",
  "index-out-of-range",
  "index-captured-requality",
  "output-rows-interleave-definitions",
  "trailing-comma-continues-line",
  "adjacency-call-across-space",
  "multiline-call-open-delimiter",
  "newline-ends-property-body",
  "comment-does-not-change-parse",
  "spread-binds-before-list",
  "dot-chain-continuation",
  "arity-too-many-arguments",
  "missing-output-not-a-value",
  "missing-output-as-builtin-arg",
  "scalar-op-rejects-sequence",
  "order-rejects-non-numeric",
  "division-by-zero",
  "spread-arguments-fail-left-to-right",
  "unresolved-implicit-parameter",
  "string-equality-exact",
  "string-displays-unquoted",
  "list-literal",
  "list-exactness",
  "list-vs-sequence-kind",
  "list-index-selects-element",
  "list-index-nested-element-stays-exact",
  "list-index-out-of-range",
  "list-index-builtin-results",
  "list-redundant-parens-canonicalize",
  "list-spread-capture",
  "list-spread-edges",
  "list-literal-spread-elements",
  "list-elements-preserve-boundaries",
  "list-written-slot-reifies-projection",
  "list-empty-spread-neutral",
  "list-call-boundary",
  "list-lone-deconstruction",
  "list-deconstruction-not-recursive",
  "collecting-binding-exact-list",
  "list-lone-collecting-assignment",
  "list-builtin-collection"
]
#guard specCaseIds.length == 157

end LanguageSpecCases
