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
- specification surface cases: 401
- excluded parse-level cases (Lean has no surface parser): 60
- excluded C#-only cases (each carries an explicit reason in the corpus): 21
- Lean-guarded cases: 320
- probe observations (C#-only by design): 1255
- internal-node cases live in the semantic-explorer corpus, not here: see
  lean/SemanticExplorerCases.lean

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
  dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
-/

namespace LanguageSpecCases
open KatLang

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, Boolean -> `true` / `false`,
    sequence -> `S[a, b]`, empty -> `S[]`, exact list -> `L[a, b]`. -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .bool b => Result.boolText b
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
  | .demandCycle => "demandCycle"
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

/-- Counted variant of `runResultM`: the same declaration identification and root wiring, but keeping the
    root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
    C# `Evaluator.RunCounted` observation. -/
def runCountedM (e : Expr) : EvalM CountedResult := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      if Algorithm.acceptsZeroSuppliedArguments wired then
        evalZeroArgumentDemandOutputCounted wired ctx []
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

-- need-closed-core-demand-is-runtime [errors]: A(q) = q + 1 \n F(x) = A + 0 \n F(7)
def case_need_closed_core_demand_is_runtime : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["q"] [] [] [(.binary .add (.param "q") (.num 1))]), privateProp "F" (alg ["x"] [] [] [(.binary .add (.resolve "A") (.num 0))])] [(.call (.resolve "F") [.num 7])])
#guard obs case_need_closed_core_demand_is_runtime == "err arity"

-- need-unused-ordinary-argument [variadic-calls]: F(x) = 10 \n F(1 / 0)
def case_need_unused_ordinary_argument : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [.num 10])] [(.call (.resolve "F") [(.binary .div (.num 1) (.num 0))])])
#guard obs case_need_unused_ordinary_argument == "ok raw=10 n=1"

-- need-unused-collector-slice [variadic-calls]: F(*xs) = 10 \n F(1, 1 / 0)
def case_need_unused_collector_slice : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 10])] [(.call (.resolve "F") [.num 1, (.binary .div (.num 1) (.num 0))])])
#guard obs case_need_unused_collector_slice == "ok raw=10 n=1"

-- need-forwarding-preserves-unused-cell [variadic-calls]: G(x) = 10 \n F(x) = G \n F(1 / 0)
def case_need_forwarding_preserves_unused_cell : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (alg ["x"] [] [] [.num 10]), privateProp "F" (alg ["x"] [] [] [(.call (.resolve "G") [.param "x"])])] [(.call (.resolve "F") [(.binary .div (.num 1) (.num 0))])])
#guard obs case_need_forwarding_preserves_unused_cell == "ok raw=10 n=1"

-- need-collector-forwarding-preserves-unused-slice [variadic-calls]: G(*xs) = 10 \n F(*xs) = G \n F(1, 1 / 0)
def case_need_collector_forwarding_preserves_unused_slice : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 10]), privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.call (.resolve "G") [(.sequenceSpread (.param "xs"))])])] [(.call (.resolve "F") [.num 1, (.binary .div (.num 1) (.num 0))])])
#guard obs case_need_collector_forwarding_preserves_unused_slice == "ok raw=10 n=1"

-- need-ordinary-conditional-selects-one-cell [variadic-calls]: Choose(true, yes, no) = yes \n Choose(false, yes, no) = no \n Choose(true, 7, 1 / 0)
def case_need_ordinary_conditional_selects_one_cell : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Choose" (.conditional none [] [⟨.sequenceValue [.litBool true, .bind "yes", .bind "no"], (alg [] [] [] [.param "yes"])⟩, ⟨.sequenceValue [.litBool false, .bind "yes", .bind "no"], (alg [] [] [] [.param "no"])⟩])] [(.call (.resolve "Choose") [.boolLiteral true, .num 7, (.binary .div (.num 1) (.num 0))])])
#guard obs case_need_ordinary_conditional_selects_one_cell == "ok raw=7 n=1"

-- need-family-shares-failed-attempt-value [variadic-calls]: F(0, x) = 7 \n F(n, 0) = n \n F(3, 0)
def case_need_family_shares_failed_attempt_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.litInt 0, .bind "x"], (alg [] [] [] [.num 7])⟩, ⟨.sequenceValue [.bind "n", .litInt 0], (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "F") [.num 3, .num 0])])
#guard obs case_need_family_shares_failed_attempt_value == "ok raw=3 n=1"

-- need-first-loop-step-can-ignore-initial [variadic-calls]: Step(x) = 7 \n repeat(Step, 1, 1 / 0)
def case_need_first_loop_step_can_ignore_initial : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (alg ["x"] [] [] [.num 7])] [(.call (.resolve "repeat") [.resolve "Step", .num 1, (.binary .div (.num 1) (.num 0))])])
#guard obs case_need_first_loop_step_can_ignore_initial == "ok raw=7 n=1"

-- need-closed-demand-can-remain-unused [variadic-calls]: A(q) = q + 1 \n Keep(x) = 7 \n F(x) = Keep(count(A)) \n F(0)
def case_need_closed_demand_can_remain_unused : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["q"] [] [] [(.binary .add (.param "q") (.num 1))]), privateProp "Keep" (alg ["x"] [] [] [.num 7]), privateProp "F" (alg ["x"] [] [] [(.call (.resolve "Keep") [(.call (.resolve "count") [.resolve "A"])])])] [(.call (.resolve "F") [.num 0])])
#guard obs case_need_closed_demand_can_remain_unused == "ok raw=7 n=1"

-- need-wrong-arity-precedes-cell-demand [variadic-calls]: F(x) = x \n F(1 / 0, 2)
def case_need_wrong_arity_precedes_cell_demand : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "F") [(.binary .div (.num 1) (.num 0)), .num 2])])
#guard obs case_need_wrong_arity_precedes_cell_demand == "err arity"

-- need-explicit-spread-precedes-arity [variadic-calls]: F(x) = 7 \n F(9, (1 / 0)*)
def case_need_explicit_spread_precedes_arity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [.num 7])] [(.call (.resolve "F") [.num 9, (.sequenceSpread (.binary .div (.num 1) (.num 0)))])])
#guard obs case_need_explicit_spread_precedes_arity == "err div0"

-- need-collector-demand-materializes-whole-slice [variadic-calls]: F(*xs) = xs.first \n F(1, 1 / 0)
def case_need_collector_demand_materializes_whole_slice : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.param "xs") "first" none)])] [(.call (.resolve "F") [.num 1, (.binary .div (.num 1) (.num 0))])])
#guard obs case_need_collector_demand_materializes_whole_slice == "err div0"

-- need-callable-projection-does-not-force-value [variadic-calls]: Inc(x) = x + 1 \n Apply(f) = f(4) \n Apply(Inc)
def case_need_callable_projection_does_not_force_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [] [(.call (.param "f") [.num 4])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_need_callable_projection_does_not_force_value == "ok raw=5 n=1"

-- need-demand-order-decides-the-first-failure [errors]: F(x, y) = y + x \n F(1 / 0, 'a' + 1)
def case_need_demand_order_decides_the_first_failure : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x", "y"] [] [] [(.binary .add (.param "y") (.param "x"))])] [(.call (.resolve "F") [(.binary .div (.num 1) (.num 0)), (.binary .add (.stringLiteral "a") (.num 1))])])
#guard obs case_need_demand_order_decides_the_first_failure == "err type"

-- need-wrapper-keeps-builtin-if-selection [conditionals]: MyIf(c, t, e) = if(c, t, e) \n Apply3(f, a, b, c) = f(a, b, c) \n MyIf(true, 1, 1 / 0) \n Apply3(if, false, 1 / 0, 2)
def case_need_wrapper_keeps_builtin_if_selection : Expr :=
  .algorithmExpr (alg [] [] [privateProp "MyIf" (alg ["c", "t", "e"] [] [] [(.call (.resolve "if") [.param "c", .param "t", .param "e"])]), privateProp "Apply3" (alg ["f", "a", "b", "c"] [] [] [(.call (.param "f") [.param "a", .param "b", .param "c"])])] [(.call (.resolve "MyIf") [.boolLiteral true, .num 1, (.binary .div (.num 1) (.num 0))]), (.call (.resolve "Apply3") [.resolve "if", .boolLiteral false, (.binary .div (.num 1) (.num 0)), .num 2])])
#guard obs case_need_wrapper_keeps_builtin_if_selection == "ok raw=S[1, 2] n=2"

-- need-container-call-checks-cardinality-first [errors]: A = { \n     public X = 1 \n } \n A(6)
def case_need_container_call_checks_cardinality_first : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [])] [(.call (.resolve "A") [.num 6])])
#guard obs case_need_container_call_checks_cardinality_first == "err arity"

-- need-collection-builtin-demands-its-collection-first [collection-builtins]: take(1 / 0, 'a' + 1)
def case_need_collection_builtin_demands_its_collection_first : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.binary .div (.num 1) (.num 0)), (.binary .add (.stringLiteral "a") (.num 1))])])
#guard obs case_need_collection_builtin_demands_its_collection_first == "err div0"

-- collected-callable-survives-explicit-respread [variadic-calls]: Inc(x) = x + 1 \n Apply(f) = f(9) \n Fwd(*fs) = Apply(fs*) \n Fwd(Inc)
def case_collected_callable_survives_explicit_respread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [] [(.call (.param "f") [.num 9])]), privateProp "Fwd" (algWithParameters [{ name := "fs", kind := .collecting }] [] [] [(.call (.resolve "Apply") [(.sequenceSpread (.param "fs"))])])] [(.call (.resolve "Fwd") [.resolve "Inc"])])
#guard obs case_collected_callable_survives_explicit_respread == "ok raw=10 n=1"

-- first-program [arithmetic]: 2 + 3 * 4
def case_first_program : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.num 2) (.binary .mul (.num 3) (.num 4)))])
#guard obs case_first_program == "ok raw=14 n=1"

-- boolean-values-and-equality [arithmetic]: true \n false \n [true, 1, false, 0] \n true == 1 \n 1 == true \n false != 0 \n 0 != false \n distinct([true, 1, false, 0, true])
def case_boolean_values_and_equality : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral true, .boolLiteral false, (.listLiteral [.boolLiteral true, .num 1, .boolLiteral false, .num 0]), (.comparison (.boolLiteral true) [{ op := .eq, operand := (.num 1) }]), (.comparison (.num 1) [{ op := .eq, operand := (.boolLiteral true) }]), (.comparison (.boolLiteral false) [{ op := .ne, operand := (.num 0) }]), (.comparison (.num 0) [{ op := .ne, operand := (.boolLiteral false) }]), (.call (.resolve "distinct") [(.listLiteral [.boolLiteral true, .num 1, .boolLiteral false, .num 0, .boolLiteral true])])])
#guard obs case_boolean_values_and_equality == "ok raw=S[true, false, L[true, 1, false, 0], false, false, true, true, L[true, 1, false, 0]] n=8"

-- boolean-predicates-and-patterns [conditionals]: F(true) = false \n F(false) = true \n F(true) \n F(false) \n range(-2, 2).filter{x >= 0} \n range(-2, 2).map{x >= 0}.contains(true) \n if(not 1 == 1, 10, 20)
def case_boolean_predicates_and_patterns : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litBool true, (alg [] [] [] [.boolLiteral false])⟩, ⟨.litBool false, (alg [] [] [] [.boolLiteral true])⟩])] [(.call (.resolve "F") [.boolLiteral true]), (.call (.resolve "F") [.boolLiteral false]), (.dotCall (.call (.resolve "range") [(.unary .minus (.num 2)), .num 2]) "filter" (some [(.algorithmExpr (alg ["x"] [] [] [(.comparison (.param "x") [{ op := .ge, operand := (.num 0) }])]))])), (.dotCall (.dotCall (.call (.resolve "range") [(.unary .minus (.num 2)), .num 2]) "map" (some [(.algorithmExpr (alg ["x"] [] [] [(.comparison (.param "x") [{ op := .ge, operand := (.num 0) }])]))])) "contains" (some [.boolLiteral true])), (.call (.resolve "if") [(.unary .not (.comparison (.num 1) [{ op := .eq, operand := (.num 1) }])), .num 10, .num 20])])
#guard obs case_boolean_predicates_and_patterns == "ok raw=S[false, true, L[0, 1, 2], true, 20] n=5"

-- boolean-loop-state-transition [conditionals]: S(x) = if(x == true, 0, true), x != 0 \n S.while(true)
def case_boolean_loop_state_transition : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["x"] [] [] [(.call (.resolve "if") [(.comparison (.param "x") [{ op := .eq, operand := (.boolLiteral true) }]), .num 0, .boolLiteral true]), (.comparison (.param "x") [{ op := .ne, operand := (.num 0) }])])] [(.dotCall (.resolve "S") "while" (some [.boolLiteral true]))])
#guard obs case_boolean_loop_state_transition == "ok raw=0 n=1"

-- boolean-predicate-rejects-visible-empty [conditionals]: F(x) = true, () \n range(0, 2).filter(F).count
def case_boolean_predicate_rejects_visible_empty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [.boolLiteral true, (.emptySequence 0)])] [(.dotCall (.dotCall (.call (.resolve "range") [.num 0, .num 2]) "filter" (some [.resolve "F"])) "count" none)])
#guard obs case_boolean_predicate_rejects_visible_empty == "err type"

-- power-unary-precedence [arithmetic]: -2 ^ 2 \n (-2) ^ 2 \n 2 ^ 3 ^ 2
def case_power_unary_precedence : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.binary .pow (.num 2) (.num 2))), (.binary .pow (.unary .minus (.num 2)) (.num 2)), (.binary .pow (.num 2) (.binary .pow (.num 3) (.num 2)))])
#guard obs case_power_unary_precedence == "ok raw=S[-4, 4, 512] n=3"

-- not-binds-below-comparisons [arithmetic]: not 5 > 3 \n not 2 > 3 \n not 5 == 5 \n not 5 == 4 \n not true == false \n not true == 1
def case_not_binds_below_comparisons : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .not (.comparison (.num 5) [{ op := .gt, operand := (.num 3) }])), (.unary .not (.comparison (.num 2) [{ op := .gt, operand := (.num 3) }])), (.unary .not (.comparison (.num 5) [{ op := .eq, operand := (.num 5) }])), (.unary .not (.comparison (.num 5) [{ op := .eq, operand := (.num 4) }])), (.unary .not (.comparison (.boolLiteral true) [{ op := .eq, operand := (.boolLiteral false) }])), (.unary .not (.comparison (.boolLiteral true) [{ op := .eq, operand := (.num 1) }]))])
#guard obs case_not_binds_below_comparisons == "ok raw=S[false, true, false, true, true, true] n=6"

-- comparison-chains-compare-adjacent-pairs [arithmetic]: 1 < 2 < 3 \n 1 < 2 <= 2 == 2 != 3 \n 1 == 1 == 1 \n 1 != 2 != 1 \n 1 != 1 != 1 \n 3 < 2 < 1 \n 1 == 1 < 2 \n 1 < 2 == true
def case_comparison_chains_compare_adjacent_pairs : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 3) }]), (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .le, operand := (.num 2) }, { op := .eq, operand := (.num 2) }, { op := .ne, operand := (.num 3) }]), (.comparison (.num 1) [{ op := .eq, operand := (.num 1) }, { op := .eq, operand := (.num 1) }]), (.comparison (.num 1) [{ op := .ne, operand := (.num 2) }, { op := .ne, operand := (.num 1) }]), (.comparison (.num 1) [{ op := .ne, operand := (.num 1) }, { op := .ne, operand := (.num 1) }]), (.comparison (.num 3) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 1) }]), (.comparison (.num 1) [{ op := .eq, operand := (.num 1) }, { op := .lt, operand := (.num 2) }]), (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .eq, operand := (.boolLiteral true) }])])
#guard obs case_comparison_chains_compare_adjacent_pairs == "ok raw=S[true, true, true, true, false, false, true, false] n=8"

-- comparison-chain-boolean-and-arithmetic-operands [arithmetic]: true == true == true \n true != false != true \n true == 1 == false \n true == true == false \n 1 + 1 < 3 == 2 + 0 \n -2 ^ 2 < 0 == true
def case_comparison_chain_boolean_and_arithmetic_operands : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.boolLiteral true) [{ op := .eq, operand := (.boolLiteral true) }, { op := .eq, operand := (.boolLiteral true) }]), (.comparison (.boolLiteral true) [{ op := .ne, operand := (.boolLiteral false) }, { op := .ne, operand := (.boolLiteral true) }]), (.comparison (.boolLiteral true) [{ op := .eq, operand := (.num 1) }, { op := .eq, operand := (.boolLiteral false) }]), (.comparison (.boolLiteral true) [{ op := .eq, operand := (.boolLiteral true) }, { op := .eq, operand := (.boolLiteral false) }]), (.comparison (.binary .add (.num 1) (.num 1)) [{ op := .lt, operand := (.num 3) }, { op := .eq, operand := (.binary .add (.num 2) (.num 0)) }]), (.comparison (.unary .minus (.binary .pow (.num 2) (.num 2))) [{ op := .lt, operand := (.num 0) }, { op := .eq, operand := (.boolLiteral true) }])])
#guard obs case_comparison_chain_boolean_and_arithmetic_operands == "ok raw=S[true, true, false, false, false, false] n=6"

-- comparison-chain-is-eager-after-false [errors]: 3 < 2 < true
def case_comparison_chain_is_eager_after_false : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 3) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.boolLiteral true) }])])
#guard obs case_comparison_chain_is_eager_after_false == "err type"

-- integer-division-truncates [arithmetic]: -7 div 2 \n -7 mod 2 \n 7 div 2
def case_integer_division_truncates : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .idiv (.unary .minus (.num 7)) (.num 2)), (.binary .mod (.unary .minus (.num 7)) (.num 2)), (.binary .idiv (.num 7) (.num 2))])
#guard obs case_integer_division_truncates == "ok raw=S[-3, -1, 3] n=3"

-- integer-division-exact-quotient [arithmetic]: X = 8999999999999999999999999999999999 \n X div 3 \n X mod 3 \n X == 3 * (X div 3) + (X mod 3) \n Y = 3e32 \n (13 * Y - 1) div Y \n (12 * Y + 1) div Y \n -X div 3 \n X div -3 \n -X div -3 \n 1e34 div 7 \n 1e34 mod 7 \n 1e40 div 1e5
def case_integer_division_exact_quotient : Expr :=
  .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 8999999999999999999999999999999999]), privateProp "Y" (alg [] [] [] [.num 300000000000000000000000000000000])] [(.binary .idiv (.resolve "X") (.num 3)), (.binary .mod (.resolve "X") (.num 3)), (.comparison (.resolve "X") [{ op := .eq, operand := (.binary .add (.binary .mul (.num 3) (.binary .idiv (.resolve "X") (.num 3))) (.binary .mod (.resolve "X") (.num 3))) }]), (.binary .idiv (.binary .sub (.binary .mul (.num 13) (.resolve "Y")) (.num 1)) (.resolve "Y")), (.binary .idiv (.binary .add (.binary .mul (.num 12) (.resolve "Y")) (.num 1)) (.resolve "Y")), (.binary .idiv (.unary .minus (.resolve "X")) (.num 3)), (.binary .idiv (.resolve "X") (.unary .minus (.num 3))), (.binary .idiv (.unary .minus (.resolve "X")) (.unary .minus (.num 3))), (.binary .idiv (.num 10000000000000000000000000000000000) (.num 7)), (.binary .mod (.num 10000000000000000000000000000000000) (.num 7)), (.binary .idiv (.num 10000000000000000000000000000000000000000) (.num 100000))])
#guard obs case_integer_division_exact_quotient == "ok raw=S[2999999999999999999999999999999999, 2, true, 12, 12, -2999999999999999999999999999999999, -2999999999999999999999999999999999, 2999999999999999999999999999999999, 1428571428571428571428571428571428, 4, 100000000000000000000000000000000000] n=11"

-- property-access-and-call [arithmetic]: # Define a property: \n Answer = 42 \n  \n # Property-style access: \n Answer \n  \n # Explicit zero-parameter call: \n Answer()
def case_property_access_and_call : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Answer" (alg [] [] [] [.num 42])] [.resolve "Answer", (.call (.resolve "Answer") [])])
#guard obs case_property_access_and_call == "ok raw=S[42, 42] n=2"

-- output-is-ordinary-property [arithmetic]: Output = 5 \n Output
def case_output_is_ordinary_property : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Output" (alg [] [] [] [.num 5])] [.resolve "Output"])
#guard obs case_output_is_ordinary_property == "ok raw=5 n=1"

-- empty-literal [empty-and-singleton]: ()
def case_empty_literal : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_empty_literal == "ok raw=S[] n=1"

-- empty-wrapped [empty-and-singleton]: (())
def case_empty_wrapped : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_empty_wrapped == "ok raw=S[] n=1"

-- empty-wrapped-twice [empty-and-singleton]: ((()))
def case_empty_wrapped_twice : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_empty_wrapped_twice == "ok raw=S[] n=1"

-- singleton-paren [empty-and-singleton]: (7)
def case_singleton_paren : Expr :=
  .algorithmExpr (alg [] [] [] [.num 7])
#guard obs case_singleton_paren == "ok raw=7 n=1"

-- singleton-paren-deep [empty-and-singleton]: (((7)))
def case_singleton_paren_deep : Expr :=
  .algorithmExpr (alg [] [] [] [.num 7])
#guard obs case_singleton_paren_deep == "ok raw=7 n=1"

-- empty-eq-family [empty-and-singleton]: () == ()      # true \n () == (())    # true \n () != (())    # false \n count(())     # 0 \n count((()))   # 0
def case_empty_eq_family : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.emptySequence 0) [{ op := .eq, operand := (.emptySequence 0) }]), (.comparison (.emptySequence 0) [{ op := .eq, operand := (.emptySequence 0) }]), (.comparison (.emptySequence 0) [{ op := .ne, operand := (.emptySequence 0) }]), (.call (.resolve "count") [(.emptySequence 0)]), (.call (.resolve "count") [(.emptySequence 0)])])
#guard obs case_empty_eq_family == "ok raw=S[true, true, false, 0, 0] n=5"

-- empty-capture [empty-and-singleton]: A = () \n A
def case_empty_capture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.emptySequence 0)])] [.resolve "A"])
#guard obs case_empty_capture == "ok raw=S[] n=1"

-- supply-three-rows [item-supply-vs-value]: 10, 20, 30
def case_supply_three_rows : Expr :=
  .algorithmExpr (alg [] [] [] [.num 10, .num 20, .num 30])
#guard obs case_supply_three_rows == "ok raw=S[10, 20, 30] n=3"

-- value-three-items [item-supply-vs-value]: (1 + 1, 2 + 2, 3 + 3)
def case_value_three_items : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.binary .add (.num 1) (.num 1)), (.binary .add (.num 2) (.num 2)), (.binary .add (.num 3) (.num 3))])])
#guard obs case_value_three_items == "ok raw=S[2, 4, 6] n=1"

-- capture-supply [item-supply-vs-value]: A = 1, 2, 3 \n A
def case_capture_supply : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.resolve "A"])
#guard obs case_capture_supply == "ok raw=S[1, 2, 3] n=1"

-- capture-supply-spread [item-supply-vs-value]: A = 1, 2, 3 \n A*
def case_capture_supply_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.sequenceSpread (.resolve "A"))])
#guard obs case_capture_supply_spread == "ok raw=S[1, 2, 3] n=3"

-- call-reentry-identity [item-supply-vs-value]: I(a) = a \n A = 1, 2, 3 \n I(I(A))
def case_call_reentry_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "A"])])])
#guard obs case_call_reentry_identity == "ok raw=S[1, 2, 3] n=1"

-- call-value-boundary [item-supply-vs-value]: F(*a) = a \n F(5, 9) \n F(5, 9)*
def case_call_value_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 5, .num 9]), (.sequenceSpread (.call (.resolve "F") [.num 5, .num 9]))])
#guard obs case_call_value_boundary == "ok raw=S[L[5, 9], 5, 9] n=3"

-- loop-result-is-one-value [item-supply-vs-value]: Fibonacci(a, b) = b, a + b \n Fibonacci.repeat(10, 0, 1) \n Fibonacci.repeat(10, 0, 1)*, \n Fibonacci.repeat(10, 0, 1), 7
def case_loop_result_is_one_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Fibonacci" (alg ["a", "b"] [] [] [.param "b", (.binary .add (.param "a") (.param "b"))])] [(.dotCall (.resolve "Fibonacci") "repeat" (some [.num 10, .num 0, .num 1])), (.sequenceSpread (.dotCall (.resolve "Fibonacci") "repeat" (some [.num 10, .num 0, .num 1]))), (.dotCall (.resolve "Fibonacci") "repeat" (some [.num 10, .num 0, .num 1])), .num 7])
#guard obs case_loop_result_is_one_value == "ok raw=S[S[55, 89], 55, 89, S[55, 89], 7] n=5"

-- loop-step-patterns-only-bind [item-supply-vs-value]: Dup(x, x) = { (x + 1, x + 1)* } \n Same(x, x) = { x + 1, x + 1 } \n Step((a, b)) = (b, a + b) \n Dup.repeat(2, 1, 1), Same.repeat(2, 1, 1), Step.repeat(3, (0, 1))
def case_loop_step_patterns_only_bind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Dup" (alg ["x", "x"] [] [] [(.sequenceSpread (.capture [(.binary .add (.param "x") (.num 1)), (.binary .add (.param "x") (.num 1))]))]), privateProp "Same" (alg ["x", "x"] [] [] [(.binary .add (.param "x") (.num 1)), (.binary .add (.param "x") (.num 1))]), privateProp "Step" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.capture [.param "b", (.binary .add (.param "a") (.param "b"))])])] [(.dotCall (.resolve "Dup") "repeat" (some [.num 2, .num 1, .num 1])), (.dotCall (.resolve "Same") "repeat" (some [.num 2, .num 1, .num 1])), (.dotCall (.resolve "Step") "repeat" (some [.num 3, (.capture [.num 0, .num 1])]))])
#guard obs case_loop_step_patterns_only_bind == "ok raw=S[S[3, 3], S[3, 3], S[2, 3]] n=3"

-- loop-nested-step-row-is-one-slot [item-supply-vs-value]: Fibonacci(a, b) = b, a + b \n Two(a, b) = { repeat(Fibonacci, 2, a, b)* } \n Two.repeat(3, 0, 1)
def case_loop_nested_step_row_is_one_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Fibonacci" (alg ["a", "b"] [] [] [.param "b", (.binary .add (.param "a") (.param "b"))]), privateProp "Two" (alg ["a", "b"] [] [] [(.sequenceSpread (.call (.resolve "repeat") [.resolve "Fibonacci", .num 2, .param "a", .param "b"]))])] [(.dotCall (.resolve "Two") "repeat" (some [.num 3, .num 0, .num 1]))])
#guard obs case_loop_nested_step_row_is_one_slot == "ok raw=S[8, 13] n=1"

-- loop-step-clause-family [conditionals]: Step(0) = 0 \n Step(n) = n - 1 \n repeat(Step, 2, 3), Step.repeat(5, 3), Step(Step(3))
def case_loop_step_clause_family : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 0])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .sub (.param "n") (.num 1))])⟩])] [(.call (.resolve "repeat") [.resolve "Step", .num 2, .num 3]), (.dotCall (.resolve "Step") "repeat" (some [.num 5, .num 3])), (.call (.resolve "Step") [(.call (.resolve "Step") [.num 3])])])
#guard obs case_loop_step_clause_family == "ok raw=S[1, 0, 1] n=3"

-- loop-step-family-while [conditionals]: Countdown(0) = 0, false \n Countdown(n) = n - 1, true \n Countdown.while(3)
def case_loop_step_family_while : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Countdown" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 0, .boolLiteral false])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .sub (.param "n") (.num 1)), .boolLiteral true])⟩])] [(.dotCall (.resolve "Countdown") "while" (some [.num 3]))])
#guard obs case_loop_step_family_while == "ok raw=0 n=1"

-- loop-step-family-multi-slot [conditionals]: Gcd(a, 0) = a, 0, false \n Gcd(a, b) = b, a mod b, true \n Gcd.while(48, 18):0
def case_loop_step_family_multi_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Gcd" (.conditional none [] [⟨.sequenceValue [.bind "a", .litInt 0], (alg [] [] [] [.param "a", .num 0, .boolLiteral false])⟩, ⟨.sequenceValue [.bind "a", .bind "b"], (alg [] [] [] [.param "b", (.binary .mod (.param "a") (.param "b")), .boolLiteral true])⟩])] [(.index (.dotCall (.resolve "Gcd") "while" (some [.num 48, .num 18])) (.num 0))])
#guard obs case_loop_step_family_multi_slot == "ok raw=6 n=1"

-- loop-step-builtin-is-one-row-wrapper [collection-builtins]: C(c) = count(c) \n repeat(count, 1, [1, 2]) == repeat(C, 1, [1, 2]), count.repeat(1, [1, 2])
def case_loop_step_builtin_is_one_row_wrapper : Expr :=
  .algorithmExpr (alg [] [] [privateProp "C" (alg ["c"] [] [] [(.call (.resolve "count") [.param "c"])])] [(.comparison (.call (.resolve "repeat") [.resolve "count", .num 1, (.listLiteral [.num 1, .num 2])]) [{ op := .eq, operand := (.call (.resolve "repeat") [.resolve "C", .num 1, (.listLiteral [.num 1, .num 2])]) }]), (.dotCall (.resolve "count") "repeat" (some [.num 1, (.listLiteral [.num 1, .num 2])]))])
#guard obs case_loop_step_builtin_is_one_row_wrapper == "ok raw=S[true, 2] n=2"

-- loop-step-builtin-empty-result-is-one-slot [empty-visible-vs-spread]: while(first, [()])
def case_loop_step_builtin_empty_result_is_one_slot : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "while") [.resolve "first", (.listLiteral [(.emptySequence 0)])])])
#guard obs case_loop_step_builtin_empty_result_is_one_slot == "err type"

-- loop-step-alias-follows-target [name-resolution]: Step(0) = 0 \n Step(n) = n - 1 \n A = Step \n C = count \n repeat(A, 2, 3), repeat(C, 1, [1, 2])
def case_loop_step_alias_follows_target : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Step")), privateProp "C" (.alias none [] [] (.resolve "count")), privateProp "Step" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 0])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .sub (.param "n") (.num 1))])⟩])] [(.call (.resolve "repeat") [.resolve "A", .num 2, .num 3]), (.call (.resolve "repeat") [.resolve "C", .num 1, (.listLiteral [.num 1, .num 2])])])
#guard obs case_loop_step_alias_follows_target == "ok raw=S[1, 2] n=2"

-- loop-step-value-is-rejected [errors]: repeat(5, 1, 0)
def case_loop_step_value_is_rejected : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.num 5, .num 1, .num 0])])
#guard obs case_loop_step_value_is_rejected == "err notAnAlgorithm"

-- loop-step-zero-iterations-never-projects [item-supply-vs-value]: repeat(5, 0, 1), repeat(1 / 0, 0, 5)
def case_loop_step_zero_iterations_never_projects : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.num 5, .num 0, .num 1]), (.call (.resolve "repeat") [(.binary .div (.num 1) (.num 0)), .num 0, .num 5])])
#guard obs case_loop_step_zero_iterations_never_projects == "ok raw=S[1, 5] n=2"

-- loop-step-family-no-match-is-ordinary [conditionals]: F(0) = 1 \n F(1) = 2 \n repeat(F, 1, 5)
def case_loop_step_family_no_match_is_ordinary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.litInt 1, (alg [] [] [] [.num 2])⟩])] [(.call (.resolve "repeat") [.resolve "F", .num 1, .num 5])])
#guard obs case_loop_step_family_no_match_is_ordinary == "err branch"

-- loop-step-lazy-builtin-roles [collection-builtins]: repeat(if, 1, false, 1 / 0, 2)
def case_loop_step_lazy_builtin_roles : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.resolve "if", .num 1, .boolLiteral false, (.binary .div (.num 1) (.num 0)), .num 2])])
#guard obs case_loop_step_lazy_builtin_roles == "ok raw=2 n=1"

-- property-value-boundary [item-supply-vs-value]: Coordinates = 10, 20 \n Coordinates \n Coordinates*
def case_property_value_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Coordinates" (alg [] [] [] [.num 10, .num 20])] [.resolve "Coordinates", (.sequenceSpread (.resolve "Coordinates"))])
#guard obs case_property_value_boundary == "ok raw=S[S[10, 20], 10, 20] n=3"

-- spread-capture-count [item-supply-vs-value]: A = [1, 2, 3] \n  \n (A*).count
def case_spread_capture_count : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])] [(.dotCall (.capture [(.sequenceSpread (.resolve "A"))]) "count" none)])
#guard obs case_spread_capture_count == "ok raw=3 n=1"

-- repeated-spread-fixed-point [item-supply-vs-value]: Collect(*items) = items \n A = [[1, 2], [3, 4]] \n  \n Collect(A*) \n Collect(A**) \n Collect((A*)*)
def case_repeated_spread_fixed_point : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), (.listLiteral [.num 3, .num 4])])]), privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.call (.resolve "Collect") [(.sequenceSpread (.resolve "A"))]), (.call (.resolve "Collect") [(.sequenceSpread (.sequenceSpread (.resolve "A")))]), (.call (.resolve "Collect") [(.sequenceSpread (.capture [(.sequenceSpread (.resolve "A"))]))])])
#guard obs case_repeated_spread_fixed_point == "ok raw=S[L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]]] n=3"

-- repeated-spread-singleton-opens [item-supply-vs-value]: Collect(*items) = items \n  \n Collect([[7]]*) \n Collect([[7]]**) \n Collect([7]*) \n Collect([7]**)
def case_repeated_spread_singleton_opens : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.call (.resolve "Collect") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 7])]))]), (.call (.resolve "Collect") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [.num 7])])))]), (.call (.resolve "Collect") [(.sequenceSpread (.listLiteral [.num 7]))]), (.call (.resolve "Collect") [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 7])))])])
#guard obs case_repeated_spread_singleton_opens == "ok raw=S[L[L[7]], L[7], L[7], L[7]] n=4"

-- scalar-spread-neutral [item-supply-vs-value]: Collect(*items) = items \n  \n Collect(5) \n Collect(5*)
def case_scalar_spread_neutral : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.call (.resolve "Collect") [.num 5]), (.call (.resolve "Collect") [(.sequenceSpread (.num 5))])])
#guard obs case_scalar_spread_neutral == "ok raw=S[L[5], L[5]] n=2"

-- select-spread-vs-capture-select [item-supply-vs-value]: A = [[1, 2], [3, 4]] \n  \n (A:0)*, \n (A*):0
def case_select_spread_vs_capture_select : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), (.listLiteral [.num 3, .num 4])])])] [(.sequenceSpread (.index (.resolve "A") (.num 0))), (.index (.capture [(.sequenceSpread (.resolve "A"))]) (.num 0))])
#guard obs case_select_spread_vs_capture_select == "ok raw=S[1, 2, L[1, 2]] n=3"

-- fixed-call-preserves-boundaries [item-supply-vs-value]: Pair = 10, 20 \n Add(x, y) = x + y \n  \n Add(Pair)
def case_fixed_call_preserves_boundaries : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Pair" (alg [] [] [] [.num 10, .num 20]), privateProp "Add" (alg ["x", "y"] [] [] [(.binary .add (.param "x") (.param "y"))])] [(.call (.resolve "Add") [.resolve "Pair"])])
#guard obs case_fixed_call_preserves_boundaries == "err arity"

-- spread-fills-remaining-slots [item-supply-vs-value]: Tail = 2, 3 \n Use(a, b, c) = a + b + c \n  \n Use(1, Tail*)
def case_spread_fills_remaining_slots : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Tail" (alg [] [] [] [.num 2, .num 3]), privateProp "Use" (alg ["a", "b", "c"] [] [] [(.binary .add (.binary .add (.param "a") (.param "b")) (.param "c"))])] [(.call (.resolve "Use") [.num 1, (.sequenceSpread (.resolve "Tail"))])])
#guard obs case_spread_fills_remaining_slots == "ok raw=6 n=1"

-- empty-count-one-arg [empty-visible-vs-spread]: count(())
def case_empty_count_one_arg : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.emptySequence 0)])])
#guard obs case_empty_count_one_arg == "ok raw=0 n=1"

-- empty-count-two-args [empty-visible-vs-spread]: count(((), ()))
def case_empty_count_two_args : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_empty_count_two_args == "ok raw=2 n=1"

-- fixed-empty-arg-visible [empty-visible-vs-spread]: F(a) = a \n F(())
def case_fixed_empty_arg_visible : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.emptySequence 0)])])
#guard obs case_fixed_empty_arg_visible == "ok raw=S[] n=1"

-- fixed-empty-spread-zero-items [empty-visible-vs-spread]: F(a) = a \n F(()*)
def case_fixed_empty_spread_zero_items : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_fixed_empty_spread_zero_items == "err arity"

-- variadic-empty-arg-vs-spread [empty-visible-vs-spread]: F(*a) = a.count \n F((), ())
def case_variadic_empty_arg_vs_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [(.dotCall (.param "a") "count" none)])] [(.call (.resolve "F") [(.emptySequence 0), (.emptySequence 0)])])
#guard obs case_variadic_empty_arg_vs_spread == "ok raw=2 n=1"

-- spread-empty-in-sequence [empty-visible-vs-spread]: (()*, 99)
def case_spread_empty_in_sequence : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0)), .num 99])])
#guard obs case_spread_empty_in_sequence == "ok raw=99 n=1"

-- empty-visible-in-sequence [empty-visible-vs-spread]: ((), 99)
def case_empty_visible_in_sequence : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), .num 99])])
#guard obs case_empty_visible_in_sequence == "ok raw=S[S[], 99] n=1"

-- empty-visible-at-root [empty-visible-vs-spread]: (), 99
def case_empty_visible_at_root : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0), .num 99])
#guard obs case_empty_visible_at_root == "ok raw=S[S[], 99] n=2"

-- decon-pair [deconstruction]: x, y = 1, 2 \n x \n y
def case_decon_pair : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x", .resolve "y"])
#guard obs case_decon_pair == "ok raw=S[1, 2] n=2"

-- decon-rhs-implicit-parameter [deconstruction]: F = { \n     a, b = x, 10 \n     a + b \n } \n F(1)
def case_decon_rhs_implicit_parameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [{ (privateLocalProp "$deconstruct$0" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [.param "x", .num 10])) with requiredOwnerDepths := some [("x", some 0)] }, { (privateLocalProp "a" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("x", some 0)] }, { (privateLocalProp "b" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("x", some 0)] }] [(.binary .add (.resolve "a") (.resolve "b"))])] [(.call (.resolve "F") [.num 1])])
#guard obs case_decon_rhs_implicit_parameter == "ok raw=11 n=1"

-- decon-rhs-brace-scope [deconstruction]: F = { \n     Q = 100 \n     a, b = { Q = 7 \n         Q, 10 } \n     a + b \n } \n F
def case_decon_rhs_brace_scope : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg [] [] [privateProp "Q" (alg [] [] [] [.num 100]), privateProp "$deconstruct$0" (alg [] [] [] [(.algorithmExpr (alg [] [] [privateProp "Q" (alg [] [] [] [.num 7])] [.resolve "Q", .num 10]))]), privateProp "a" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])]), privateProp "b" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])] [(.binary .add (.resolve "a") (.resolve "b"))])] [.resolve "F"])
#guard obs case_decon_rhs_brace_scope == "ok raw=17 n=1"

-- decon-rhs-lifted-parameter-order [deconstruction]: P = x * 2 \n R = y * 3 \n F = { \n     a, b = P, 10 \n     R + a + b \n } \n F(1, 2)
def case_decon_rhs_lifted_parameter_order : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))]), privateProp "R" (alg ["y"] [] [] [(.binary .mul (.param "y") (.num 3))]), privateProp "F" (alg ["x", "y"] [] [{ (privateLocalProp "$deconstruct$0" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.resolve "P") [.param "x"]), .num 10])) with requiredOwnerDepths := some [("x", some 0)] }, { (privateLocalProp "a" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("x", some 0)] }, { (privateLocalProp "b" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "b"])) [.resolve "$deconstruct$0"])])) with requiredOwnerDepths := some [("x", some 0)] }] [(.binary .add (.binary .add (.call (.resolve "R") [.param "y"]) (.resolve "a")) (.resolve "b"))])] [(.call (.resolve "F") [.num 1, .num 2])])
#guard obs case_decon_rhs_lifted_parameter_order == "ok raw=18 n=1"

-- decon-collecting-tail [deconstruction]: x, *rest = 1, 2, 3 \n rest
def case_decon_collecting_tail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "rest" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) [.resolve "$deconstruct$0"])])] [.resolve "rest"])
#guard obs case_decon_collecting_tail == "ok raw=L[2, 3] n=1"

-- decon-collecting-head [deconstruction]: *head, last = 1, 2, 3 \n head \n last
def case_decon_collecting_head : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "head" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "head", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "head"])) [.resolve "$deconstruct$0"])]), privateProp "last" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "head", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "last"])) [.resolve "$deconstruct$0"])])] [.resolve "head", .resolve "last"])
#guard obs case_decon_collecting_head == "ok raw=S[L[1, 2], 3] n=2"

-- decon-collecting-middle [deconstruction]: x, *middle, z = 1, 2, 3, 4 \n middle
def case_decon_collecting_middle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "middle", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "middle" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "middle", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "middle"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "middle", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "middle"])
#guard obs case_decon_collecting_middle == "ok raw=L[2, 3] n=1"

-- decon-empty-collecting [deconstruction]: x, *rest = 1 \n rest \n x
def case_decon_empty_collecting : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "rest" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) [.resolve "$deconstruct$0"])])] [.resolve "rest", .resolve "x"])
#guard obs case_decon_empty_collecting == "ok raw=S[L[], 1] n=2"

-- decon-arity-under [deconstruction]: x, y = 1 \n x
def case_decon_arity_under : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_decon_arity_under == "err arity"

-- decon-arity-over [deconstruction]: x, y = 1, 2, 3 \n x
def case_decon_arity_over : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_decon_arity_over == "err arity"

-- decon-unpacks-stored-value [deconstruction]: A = 1, 2, 3 \n x, y, z = A \n y
def case_decon_unpacks_stored_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "$deconstruct$0" (alg [] [] [] [.resolve "A"]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_decon_unpacks_stored_value == "ok raw=2 n=1"

-- decon-tutorial-full [deconstruction]: A = 1, 2, 3, 4, 5 \n  \n x, *y, z = A \n x \n y \n z
def case_decon_tutorial_full : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]), privateProp "$deconstruct$0" (alg [] [] [] [.resolve "A"]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "x", .resolve "y", .resolve "z"])
#guard obs case_decon_tutorial_full == "ok raw=S[1, L[2, 3, 4], 5] n=3"

-- decon-lone-collecting [deconstruction]: *all = 1, 2, 3 \n all
def case_decon_lone_collecting : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "all" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "all", kind := .collecting }]] [] [] [.param "all"])) [.resolve "$deconstruct$0"])])] [.resolve "all"])
#guard obs case_decon_lone_collecting == "ok raw=L[1, 2, 3] n=1"

-- variadic-grouped-and-spread [variadic-calls]: A = 1, 2, 3, 4, 5 \n  \n G(*x) = x.sum \n  \n G(A*) \n G(1, 2, 3, 4, 5)
def case_variadic_grouped_and_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]), privateProp "G" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [(.dotCall (.param "x") "sum" none)])] [(.call (.resolve "G") [(.sequenceSpread (.resolve "A"))]), (.call (.resolve "G") [.num 1, .num 2, .num 3, .num 4, .num 5])])
#guard obs case_variadic_grouped_and_spread == "ok raw=S[15, 15] n=2"

-- variadic-siblings-preserved [variadic-calls]: A = 1, 2 \n B = 3, 4 \n  \n G(*x) = x.count \n  \n G(A, B) \n G(A*, B*)
def case_variadic_siblings_preserved : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2]), privateProp "B" (alg [] [] [] [.num 3, .num 4]), privateProp "G" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [(.dotCall (.param "x") "count" none)])] [(.call (.resolve "G") [.resolve "A", .resolve "B"]), (.call (.resolve "G") [(.sequenceSpread (.resolve "A")), (.sequenceSpread (.resolve "B"))])])
#guard obs case_variadic_siblings_preserved == "ok raw=S[2, 4] n=2"

-- variadic-capture-collects-list [variadic-calls]: F(*x) = x \n F(1, 2, 3)
def case_variadic_capture_collects_list : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "x", kind := .collecting }] [] [] [.param "x"])] [(.call (.resolve "F") [.num 1, .num 2, .num 3])])
#guard obs case_variadic_capture_collects_list == "ok raw=L[1, 2, 3] n=1"

-- variadic-forwarding-list-spread [variadic-calls]: Target(*items) = items \n Forward(*items) = Target(items*) \n  \n Forward(1, 2) \n Forward([1, 2])
def case_variadic_forwarding_list_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Target" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Forward" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [(.call (.resolve "Target") [(.sequenceSpread (.param "items"))])])] [(.call (.resolve "Forward") [.num 1, .num 2]), (.call (.resolve "Forward") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_variadic_forwarding_list_spread == "ok raw=S[L[1, 2], L[L[1, 2]]] n=2"

-- implicit-forwarding-source-kind [variadic-calls]: Target(tag, *items) = items \n Use(tag, items) = Target \n UseVariadic(tag, *items) = Target \n  \n Use(0, [1, 2]) \n Use(0, (1, 2)) \n UseVariadic(0, 1, 2)
def case_implicit_forwarding_source_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Target" (algWithParameters [{ name := "tag" }, { name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Use" (alg ["tag", "items"] [] [] [(.call (.resolve "Target") [.param "tag", .param "items"])]), privateProp "UseVariadic" (algWithParameters [{ name := "tag" }, { name := "items", kind := .collecting }] [] [] [(.call (.resolve "Target") [.param "tag", (.sequenceSpread (.param "items"))])])] [(.call (.resolve "Use") [.num 0, (.listLiteral [.num 1, .num 2])]), (.call (.resolve "Use") [.num 0, (.capture [.num 1, .num 2])]), (.call (.resolve "UseVariadic") [.num 0, .num 1, .num 2])])
#guard obs case_implicit_forwarding_source_kind == "ok raw=S[L[L[1, 2]], L[S[1, 2]], L[1, 2]] n=3"

-- variadic-receiver-distinction [variadic-calls]: Inspect(*items) = items \n A = [1, 2, 3] \n  \n Inspect(A) \n Inspect(A*)
def case_variadic_receiver_distinction : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "Inspect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.call (.resolve "Inspect") [.resolve "A"]), (.call (.resolve "Inspect") [(.sequenceSpread (.resolve "A"))])])
#guard obs case_variadic_receiver_distinction == "ok raw=S[L[L[1, 2, 3]], L[1, 2, 3]] n=2"

-- dot-receiver-passes-a-value [variadic-calls]: Mean(*Vector) = Vector.sum / Vector.count \n  \n Mean(1, 2, 3) \n (1, 2, 3)*.Mean \n [1, 2, 3]*.Mean
def case_dot_receiver_passes_a_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Mean" (algWithParameters [{ name := "Vector", kind := .collecting }] [] [] [(.binary .div (.dotCall (.param "Vector") "sum" none) (.dotCall (.param "Vector") "count" none))])] [(.call (.resolve "Mean") [.num 1, .num 2, .num 3]), (.call (.resolve "Mean") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))]), (.call (.resolve "Mean") [(.sequenceSpread (.listLiteral [.num 1, .num 2, .num 3]))])])
#guard obs case_dot_receiver_passes_a_value == "ok raw=S[2, 2, 2] n=3"

-- values-stay-values [variadic-calls]: Coll(*xs) = xs \n Cnt(*xs) = xs.count \n CntValue(x) = x.count \n  \n Coll((1, 2)) \n Coll([1, 2]) \n Coll((1, 2)*) \n Cnt((10, 7)) \n CntValue((10, 7))
def case_values_stay_values : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Coll" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]), privateProp "Cnt" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.param "xs") "count" none)]), privateProp "CntValue" (alg ["x"] [] [] [(.dotCall (.param "x") "count" none)])] [(.call (.resolve "Coll") [(.capture [.num 1, .num 2])]), (.call (.resolve "Coll") [(.listLiteral [.num 1, .num 2])]), (.call (.resolve "Coll") [(.sequenceSpread (.capture [.num 1, .num 2]))]), (.call (.resolve "Cnt") [(.capture [.num 10, .num 7])]), (.call (.resolve "CntValue") [(.capture [.num 10, .num 7])])])
#guard obs case_values_stay_values == "ok raw=S[L[S[1, 2]], L[L[1, 2]], L[1, 2], 1, 2] n=5"

-- callback-element-is-one-argument [collection-builtins]: AddPair((x, y)) = x + y \n LAddPair([x, y]) = x + y \n  \n map([(1, 2)], AddPair) \n map([[1, 2]], LAddPair)
def case_callback_element_is_one_argument : Expr :=
  .algorithmExpr (alg [] [] [privateProp "AddPair" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))]), privateProp "LAddPair" (algWithParameterPatterns [.listValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "AddPair"]), (.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1, .num 2])]), .resolve "LAddPair"])])
#guard obs case_callback_element_is_one_argument == "ok raw=S[L[3], L[3]] n=2"

-- parentheses-group-syntax [item-supply-vs-value]: Collect(*items) = items \n S = 1, 2 \n L = [1, 2] \n E = () \n  \n Collect(S), Collect((S)), Collect(((S))) \n Collect(L), Collect((L)) \n Collect(E), Collect((E)) \n S.Collect, (S).Collect, ((S)).Collect \n E*.Collect, (E)*.Collect
def case_parentheses_group_syntax : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg [] [] [] [.num 1, .num 2]), privateProp "L" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "E" (alg [] [] [] [(.emptySequence 0)]), privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.call (.resolve "Collect") [.resolve "S"]), (.call (.resolve "Collect") [.resolve "S"]), (.call (.resolve "Collect") [.resolve "S"]), (.call (.resolve "Collect") [.resolve "L"]), (.call (.resolve "Collect") [.resolve "L"]), (.call (.resolve "Collect") [.resolve "E"]), (.call (.resolve "Collect") [.resolve "E"]), (.dotCall (.resolve "S") "Collect" none), (.dotCall (.resolve "S") "Collect" none), (.dotCall (.resolve "S") "Collect" none), (.call (.resolve "Collect") [(.sequenceSpread (.resolve "E"))]), (.call (.resolve "Collect") [(.sequenceSpread (.resolve "E"))])])
#guard obs case_parentheses_group_syntax == "ok raw=S[L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[L[1, 2]], L[L[1, 2]], L[S[]], L[S[]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[], L[]] n=12"

-- mixed-collecting-parameter [variadic-calls]: F(x, *y, z) = x + y.sum + z \n F(1, 2, 3, 4, 5)
def case_mixed_collecting_parameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "x" }, { name := "y", kind := .collecting }, { name := "z" }] [] [] [(.binary .add (.binary .add (.param "x") (.dotCall (.param "y") "sum" none)) (.param "z"))])] [(.call (.resolve "F") [.num 1, .num 2, .num 3, .num 4, .num 5])])
#guard obs case_mixed_collecting_parameter == "ok raw=15 n=1"

-- mixed-front-back-family [variadic-calls]: Arg = 1, 2, 3 \n  \n Head(first, *rest) = first \n Tail(first, *rest) = rest \n Init(*init, last) = init \n Last(*init, last) = last \n  \n Head(1, (2, 3)) \n Tail(1, (2, 3)) \n Init((1, 2), 3) \n Last(Arg, 3)
def case_mixed_front_back_family : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Arg" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "Head" (algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "first"]), privateProp "Tail" (algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "rest"]), privateProp "Init" (algWithParameters [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "init"]), privateProp "Last" (algWithParameters [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "last"])] [(.call (.resolve "Head") [.num 1, (.capture [.num 2, .num 3])]), (.call (.resolve "Tail") [.num 1, (.capture [.num 2, .num 3])]), (.call (.resolve "Init") [(.capture [.num 1, .num 2]), .num 3]), (.call (.resolve "Last") [.resolve "Arg", .num 3])])
#guard obs case_mixed_front_back_family == "ok raw=S[1, L[S[2, 3]], L[S[1, 2]], 3] n=4"

-- collecting-minimum-arity [variadic-calls]: F(first, *middle, last) = middle \n  \n F(1, 2) \n F(1, 2, 3)
def case_collecting_minimum_arity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }] [] [] [.param "middle"])] [(.call (.resolve "F") [.num 1, .num 2]), (.call (.resolve "F") [.num 1, .num 2, .num 3])])
#guard obs case_collecting_minimum_arity == "ok raw=S[L[], L[2]] n=2"

-- variadic-grouped-vs-spread [variadic-calls]: H(h, *t) = t \n H((1, 2))
def case_variadic_grouped_vs_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "H" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "H") [(.capture [.num 1, .num 2])])])
#guard obs case_variadic_grouped_vs_spread == "ok raw=L[] n=1"

-- variadic-nested-not-flattened [variadic-calls]: Arg = (1, 2), (3, 4) \n  \n Many(*values) = values.count \n Flattened = atoms(Arg).count \n  \n Many(Arg*) \n Flattened
def case_variadic_nested_not_flattened : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Arg" (alg [] [] [] [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), privateProp "Flattened" (alg [] [] [] [(.dotCall (.call (.resolve "atoms") [.resolve "Arg"]) "count" none)]), privateProp "Many" (algWithParameters [{ name := "values", kind := .collecting }] [] [] [(.dotCall (.param "values") "count" none)])] [(.call (.resolve "Many") [(.sequenceSpread (.resolve "Arg"))]), .resolve "Flattened"])
#guard obs case_variadic_nested_not_flattened == "ok raw=S[2, 4] n=2"

-- supply-vs-value-patterns [variadic-calls]: CountValues(*values) = values.count \n CountSequenceValue((*values)) = values.count \n  \n CountValues() \n CountValues(1, 2, 3) \n CountValues((1, 2, 3)) \n CountSequenceValue((1, 2, 3))
def case_supply_vs_value_patterns : Expr :=
  .algorithmExpr (alg [] [] [privateProp "CountValues" (algWithParameters [{ name := "values", kind := .collecting }] [] [] [(.dotCall (.param "values") "count" none)]), privateProp "CountSequenceValue" (algWithParameterPatterns [.sequenceValue [.capture { name := "values", kind := .collecting }]] [] [] [(.dotCall (.param "values") "count" none)])] [(.call (.resolve "CountValues") []), (.call (.resolve "CountValues") [.num 1, .num 2, .num 3]), (.call (.resolve "CountValues") [(.capture [.num 1, .num 2, .num 3])]), (.call (.resolve "CountSequenceValue") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_supply_vs_value_patterns == "ok raw=S[0, 3, 1, 3] n=4"

-- list-patterns-cover-every-cardinality [lists]: L([*xs]) = xs \n Only([x]) = x \n Pair([x, y]) = x + y \n Ends([first, *middle, last]) = first, middle, last \n  \n L([]), L([1]), L([1, 2]) \n Only([10]) \n Pair([10, 20]) \n Ends([1, 2, 3, 4])
def case_list_patterns_cover_every_cardinality : Expr :=
  .algorithmExpr (alg [] [] [privateProp "L" (algWithParameterPatterns [.listValue [.capture { name := "xs", kind := .collecting }]] [] [] [.param "xs"]), privateProp "Only" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [.param "x"]), privateProp "Pair" (algWithParameterPatterns [.listValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))]), privateProp "Ends" (algWithParameterPatterns [.listValue [.capture { name := "first" }, .capture { name := "middle", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "first", .param "middle", .param "last"])] [(.call (.resolve "L") [(.listLiteral [])]), (.call (.resolve "L") [(.listLiteral [.num 1])]), (.call (.resolve "L") [(.listLiteral [.num 1, .num 2])]), (.call (.resolve "Only") [(.listLiteral [.num 10])]), (.call (.resolve "Pair") [(.listLiteral [.num 10, .num 20])]), (.call (.resolve "Ends") [(.listLiteral [.num 1, .num 2, .num 3, .num 4])])])
#guard obs case_list_patterns_cover_every_cardinality == "ok raw=S[L[], L[1], L[1, 2], 10, 30, S[1, L[2, 3], 4]] n=6"

-- nested-structural-patterns-keep-their-kind [variadic-calls]: F(([x, y], z)) = x + y + z \n G([(x, y), z]) = x + y + z \n  \n F(([10, 20], 30)) \n G([(1, 2), 3])
def case_nested_structural_patterns_keep_their_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "x" }, .capture { name := "y" }], .capture { name := "z" }]] [] [] [(.binary .add (.binary .add (.param "x") (.param "y")) (.param "z"))]), privateProp "G" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }], .capture { name := "z" }]] [] [] [(.binary .add (.binary .add (.param "x") (.param "y")) (.param "z"))])] [(.call (.resolve "F") [(.capture [(.listLiteral [.num 10, .num 20]), .num 30])]), (.call (.resolve "G") [(.listLiteral [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_nested_structural_patterns_keep_their_kind == "ok raw=S[60, 6] n=2"

-- structural-patterns-open-only-their-own-kind [variadic-calls]: PairSum((x, y)) = x + y \n ListSum([x, y]) = x + y \n  \n PairSum((2, 3)) \n ListSum([2, 3])
def case_structural_patterns_open_only_their_own_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "PairSum" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))]), privateProp "ListSum" (algWithParameterPatterns [.listValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))])] [(.call (.resolve "PairSum") [(.capture [.num 2, .num 3])]), (.call (.resolve "ListSum") [(.listLiteral [.num 2, .num 3])])])
#guard obs case_structural_patterns_open_only_their_own_kind == "ok raw=S[5, 5] n=2"

-- binding-failure-outranks-repeated-name-conflict [variadic-calls]: Bad = 1 / 0 \n P(x, x, (a, b)) = a \n  \n P(1, 2, Bad)
def case_binding_failure_outranks_repeated_name_conflict : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Bad" (alg [] [] [] [(.binary .div (.num 1) (.num 0))]), privateProp "P" (algWithParameterPatterns [.capture { name := "x" }, .capture { name := "x" }, .sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])] [(.call (.resolve "P") [.num 1, .num 2, .resolve "Bad"])])
#guard obs case_binding_failure_outranks_repeated_name_conflict == "err arity"

-- repeated-name-binding-is-order-independent [variadic-calls]: A = 5 \n B = 2 + 3 \n P(f, f, f) = f \n  \n P(A, 5, B)
def case_repeated_name_binding_is_order_independent : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 5]), privateProp "B" (alg [] [] [] [(.binary .add (.num 2) (.num 3))]), privateProp "P" (alg ["f", "f", "f"] [] [] [.param "f"])] [(.call (.resolve "P") [.resolve "A", .num 5, .resolve "B"])])
#guard obs case_repeated_name_binding_is_order_independent == "err type"

-- repeated-name-is-a-constraint-not-a-merge [variadic-calls]: Inc(y) = y + 1 \n P(x, x) = x, x(5) \n  \n P(Inc, 1)
def case_repeated_name_is_a_constraint_not_a_merge : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["y"] [] [] [(.binary .add (.param "y") (.num 1))]), privateProp "P" (alg ["x", "x"] [] [] [.param "x", (.call (.param "x") [.num 5])])] [(.call (.resolve "P") [.resolve "Inc", .num 1])])
#guard obs case_repeated_name_is_a_constraint_not_a_merge == "err arity"

-- repeated-equal-values-require-one-callable-identity [variadic-calls]: A(*xs) = 5 \n B(*xs) = 5 + xs.count \n P(f, f) = f(1) \n P(A, B)
def case_repeated_equal_values_require_one_callable_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 5]), privateProp "B" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.binary .add (.num 5) (.dotCall (.param "xs") "count" none))]), privateProp "P" (alg ["f", "f"] [] [] [(.call (.param "f") [.num 1])])] [(.call (.resolve "P") [.resolve "A", .resolve "B"])])
#guard obs case_repeated_equal_values_require_one_callable_identity == "err type"

-- implicit-forwarding-is-by-binding-name [variadic-calls]: F(x) = x + 1 \n G(x) = x * 2 \n H = F + G \n  \n Common(x, x) = x \n Twice = Common * 2 \n  \n H(3) \n Twice(7)
def case_implicit_forwarding_is_by_binding_name : Expr :=
  .algorithmExpr (alg [] [] [privateProp "H" (alg ["x"] [] [] [(.binary .add (.call (.resolve "F") [.param "x"]) (.call (.resolve "G") [.param "x"]))]), privateProp "Twice" (alg ["x"] [] [] [(.binary .mul (.call (.resolve "Common") [.param "x", .param "x"]) (.num 2))]), privateProp "F" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "G" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))]), privateProp "Common" (alg ["x", "x"] [] [] [.param "x"])] [(.call (.resolve "H") [.num 3]), (.call (.resolve "Twice") [.num 7])])
#guard obs case_implicit_forwarding_is_by_binding_name == "ok raw=S[10, 14] n=2"

-- formula-lifting-is-one-law-for-every-callable [variadic-calls]: Lib = { \n     public Inc(x) = x + 1 \n } \n E(0) = 100 \n E(n) = n \n Total = count + 0 \n Next = Lib.Inc + 0 \n Fam = E + 1 \n  \n Total((1, 2, 3)) \n Next(4) \n Fam(0)
def case_formula_lifting_is_one_law_for_every_callable : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] []), privateProp "Total" (alg ["collection"] [] [] [(.binary .add (.call (.resolve "count") [.param "collection"]) (.num 0))]), privateProp "Next" (alg ["x"] [] [] [(.binary .add (.dotCall (.resolve "Lib") "Inc" (some [.param "x"])) (.num 0))]), privateProp "Fam" (alg ["n"] [] [] [(.binary .add (.call (.resolve "E") [.param "n"]) (.num 1))]), privateProp "E" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "Total") [(.capture [.num 1, .num 2, .num 3])]), (.call (.resolve "Next") [.num 4]), (.call (.resolve "Fam") [.num 0])])
#guard obs case_formula_lifting_is_one_law_for_every_callable == "ok raw=S[3, 5, 101] n=3"

-- formula-lifting-follows-the-consumers-role [variadic-calls]: Inc(x) = x + 1 \n Apply(f) = f(10) \n  \n Values = [Inc, Inc * 2] \n Kept = Apply(Inc) \n Branch = if(true, Inc, 0) \n  \n Values(4) \n Kept \n Branch(4)
def case_formula_lifting_follows_the_consumers_role : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Values" (alg ["x"] [] [] [(.listLiteral [(.call (.resolve "Inc") [.param "x"]), (.binary .mul (.call (.resolve "Inc") [.param "x"]) (.num 2))])]), privateProp "Kept" (alg [] [] [] [(.call (.resolve "Apply") [.resolve "Inc"])]), privateProp "Branch" (alg ["x"] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Inc") [.param "x"]), .num 0])]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [] [(.call (.param "f") [.num 10])])] [(.call (.resolve "Values") [.num 4]), .resolve "Kept", (.call (.resolve "Branch") [.num 4])])
#guard obs case_formula_lifting_follows_the_consumers_role == "ok raw=S[L[5, 10], 11, 5] n=3"

-- repeated-name-wrapper-keeps-independent-arguments [variadic-calls]: Common(x, x) = x \n Both(a, b) = Common(a, b) \n Twice(v) = Common(v, v) \n Some = Common \n  \n Both(7, 7) \n Twice(8) \n Some(9, 9)
def case_repeated_name_wrapper_keeps_independent_arguments : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Some" (.alias none [] [] (.resolve "Common")), privateProp "Common" (alg ["x", "x"] [] [] [.param "x"]), privateProp "Both" (alg ["a", "b"] [] [] [(.call (.resolve "Common") [.param "a", .param "b"])]), privateProp "Twice" (alg ["v"] [] [] [(.call (.resolve "Common") [.param "v", .param "v"])])] [(.call (.resolve "Both") [.num 7, .num 7]), (.call (.resolve "Twice") [.num 8]), (.call (.resolve "Some") [.num 9, .num 9])])
#guard obs case_repeated_name_wrapper_keeps_independent_arguments == "ok raw=S[7, 8, 9] n=3"

-- implicit-forwarding-preserves-structural-kind [variadic-calls]: Single([x]) = x \n A = Single \n Add((x, y)) = x + y \n B = Add \n C((*xs)) = xs.count \n Count = C \n G([x]) = Single \n  \n A([7]) \n A([[7]]) \n B((10, 20)) \n Count((1, 2, 3)) \n G([7])
def case_implicit_forwarding_preserves_structural_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Single")), privateProp "B" (.alias none [] [] (.resolve "Add")), privateProp "Count" (.alias none [] [] (.resolve "C")), privateProp "Single" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [.param "x"]), privateProp "Add" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.binary .add (.param "x") (.param "y"))]), privateProp "C" (algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [(.dotCall (.param "xs") "count" none)]), privateProp "G" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [(.call (.resolve "Single") [(.listLiteral [.param "x"])])])] [(.call (.resolve "A") [(.listLiteral [.num 7])]), (.call (.resolve "A") [(.listLiteral [(.listLiteral [.num 7])])]), (.call (.resolve "B") [(.capture [.num 10, .num 20])]), (.call (.resolve "Count") [(.capture [.num 1, .num 2, .num 3])]), (.call (.resolve "G") [(.listLiteral [.num 7])])])
#guard obs case_implicit_forwarding_preserves_structural_kind == "ok raw=S[7, L[7], 30, 3, 7] n=5"

-- alias-forwarding-and-explicit-call [name-resolution]: Double(x) = x * 2 \n Other(y) = y * 2 \n  \n Alias = Double \n Forward(x) = Double \n Explicit(x) = Other(x) \n Formula = Double + 1 \n  \n Alias(5) \n Forward(5) \n Explicit(5) \n Formula(5)
def case_alias_forwarding_and_explicit_call : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Alias" (.alias none [] [] (.resolve "Double")), privateProp "Formula" (alg ["x"] [] [] [(.binary .add (.call (.resolve "Double") [.param "x"]) (.num 1))]), privateProp "Double" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))]), privateProp "Other" (alg ["y"] [] [] [(.binary .mul (.param "y") (.num 2))]), privateProp "Forward" (alg ["x"] [] [] [(.call (.resolve "Double") [.param "x"])]), privateProp "Explicit" (alg ["x"] [] [] [(.call (.resolve "Other") [.param "x"])])] [(.call (.resolve "Alias") [.num 5]), (.call (.resolve "Forward") [.num 5]), (.call (.resolve "Explicit") [.num 5]), (.call (.resolve "Formula") [.num 5])])
#guard obs case_alias_forwarding_and_explicit_call == "ok raw=S[10, 10, 10, 11] n=4"

-- alias-structural-forwarding-and-written-call [name-resolution]: Single([x]) = x \n  \n Alias = Single \n SameShape([x]) = Single \n Explicit(x) = Single(x) \n Construct = Single([x]) \n  \n Alias([7]) \n SameShape([7]) \n Explicit([7]) \n Construct(7)
def case_alias_structural_forwarding_and_written_call : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Alias" (.alias none [] [] (.resolve "Single")), privateProp "Construct" (alg ["x"] [] [] [(.call (.resolve "Single") [(.listLiteral [.param "x"])])]), privateProp "Single" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [.param "x"]), privateProp "SameShape" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [(.call (.resolve "Single") [(.listLiteral [.param "x"])])]), privateProp "Explicit" (alg ["x"] [] [] [(.call (.resolve "Single") [.param "x"])])] [(.call (.resolve "Alias") [(.listLiteral [.num 7])]), (.call (.resolve "SameShape") [(.listLiteral [.num 7])]), (.call (.resolve "Explicit") [(.listLiteral [.num 7])]), (.call (.resolve "Construct") [.num 7])])
#guard obs case_alias_structural_forwarding_and_written_call == "ok raw=S[7, 7, 7, 7] n=4"

-- alias-preserves-the-callee-signature [name-resolution]: Single([x]) = x \n P(x, x) = x \n E((), []) = 1 \n A = Single \n B = A \n C = B \n AP = P \n AE = E \n  \n C([7]) \n C([[7]]) \n AP(5, 5) \n AE((), [])
def case_alias_preserves_the_callee_signature : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Single")), privateProp "B" (.alias none [] [] (.resolve "A")), privateProp "C" (.alias none [] [] (.resolve "B")), privateProp "AP" (.alias none [] [] (.resolve "P")), privateProp "AE" (.alias none [] [] (.resolve "E")), privateProp "Single" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [.param "x"]), privateProp "P" (alg ["x", "x"] [] [] [.param "x"]), privateProp "E" (algWithParameterPatterns [.sequenceValue [], .listValue []] [] [] [.num 1])] [(.call (.resolve "C") [(.listLiteral [.num 7])]), (.call (.resolve "C") [(.listLiteral [(.listLiteral [.num 7])])]), (.call (.resolve "AP") [.num 5, .num 5]), (.call (.resolve "AE") [(.emptySequence 0), (.listLiteral [])])])
#guard obs case_alias_preserves_the_callee_signature == "ok raw=S[7, L[7], 5, 1] n=4"

-- alias-of-a-builtin-is-the-builtin [name-resolution]: C = count \n I = if \n M = map \n Bad(x) = x / 0 \n  \n C([1, 2, 3]) \n I(true, 1, 1 / 0) \n M([], Bad)
def case_alias_of_a_builtin_is_the_builtin : Expr :=
  .algorithmExpr (alg [] [] [privateProp "C" (.alias none [] [] (.resolve "count")), privateProp "I" (.alias none [] [] (.resolve "if")), privateProp "M" (.alias none [] [] (.resolve "map")), privateProp "Bad" (alg ["x"] [] [] [(.binary .div (.param "x") (.num 0))])] [(.call (.resolve "C") [(.listLiteral [.num 1, .num 2, .num 3])]), (.call (.resolve "I") [.boolLiteral true, .num 1, (.binary .div (.num 1) (.num 0))]), (.call (.resolve "M") [(.listLiteral []), .resolve "Bad"])])
#guard obs case_alias_of_a_builtin_is_the_builtin == "ok raw=S[3, 1, L[]] n=3"

-- alias-of-a-clause-family-dispatches-as-the-family [name-resolution]: Fact(0) = 1 \n Fact(n) = n * Fact(n - 1) \n F = Fact \n  \n F(4)
def case_alias_of_a_clause_family_dispatches_as_the_family : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.alias none [] [] (.resolve "Fact")), privateProp "Fact" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [(.binary .mul (.param "n") (.call (.resolve "Fact") [(.binary .sub (.param "n") (.num 1))]))])⟩])] [(.call (.resolve "F") [.num 4])])
#guard obs case_alias_of_a_clause_family_dispatches_as_the_family == "ok raw=24 n=1"

-- alias-arguments-take-the-targets-roles [variadic-calls]: Inc(x) = x + 1 \n I = if \n K = I(c, Inc, 0) \n  \n K(true, 4)
def case_alias_arguments_take_the_targets_roles : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (.alias none [] [] (.resolve "if")), privateProp "K" (alg ["c", "x"] [] [] [(.call (.resolve "I") [.param "c", (.call (.resolve "Inc") [.param "x"]), .num 0])]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "K") [.boolLiteral true, .num 4])])
#guard obs case_alias_arguments_take_the_targets_roles == "ok raw=5 n=1"

-- alias-is-the-targets-callable [name-resolution]: P(f, f) = f(7) \n Only(*xs) = 0 \n A = Only \n  \n P(A, Only)
def case_alias_is_the_targets_callable : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Only")), privateProp "P" (alg ["f", "f"] [] [] [(.call (.param "f") [.num 7])]), privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 0])] [(.call (.resolve "P") [.resolve "A", .resolve "Only"])])
#guard obs case_alias_is_the_targets_callable == "ok raw=0 n=1"

-- alias-declares-only-its-own-members [name-resolution]: Lib(x) = { \n   K = 5 \n   x \n } \n A = Lib \n Navigate(f) = f.K \n  \n Lib.K \n Navigate(A)
def case_alias_declares_only_its_own_members : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Lib")), privateProp "Lib" (alg ["x"] [] [privateProp "K" (alg [] [] [] [.num 5])] [.param "x"]), privateProp "Navigate" (alg ["f"] [] [] [(.dotCall (.param "f") "K" none)])] [(.dotCall (.resolve "Lib") "K" none), (.call (.resolve "Navigate") [.resolve "A"])])
#guard obs case_alias_declares_only_its_own_members == "ok raw=S[5, 5] n=2"

-- bare-forwarding-keeps-each-parameter-kind [name-resolution]: Add((a, b)) = a + b \n Coll(*vs) = vs \n Mid([first, *middle, last]) = [first, middle, last] \n Pair((a, b)) = Add \n Many(*vs) = Coll \n Same([first, *middle, last]) = Mid \n  \n Pair((2, 3)) \n Many(1, 2) \n Same([1, 2, 3, 4])
def case_bare_forwarding_keeps_each_parameter_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Add" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.binary .add (.param "a") (.param "b"))]), privateProp "Coll" (algWithParameters [{ name := "vs", kind := .collecting }] [] [] [.param "vs"]), privateProp "Mid" (algWithParameterPatterns [.listValue [.capture { name := "first" }, .capture { name := "middle", kind := .collecting }, .capture { name := "last" }]] [] [] [(.listLiteral [.param "first", .param "middle", .param "last"])]), privateProp "Pair" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.call (.resolve "Add") [(.capture [.param "a", .param "b"])])]), privateProp "Many" (algWithParameters [{ name := "vs", kind := .collecting }] [] [] [(.call (.resolve "Coll") [(.sequenceSpread (.param "vs"))])]), privateProp "Same" (algWithParameterPatterns [.listValue [.capture { name := "first" }, .capture { name := "middle", kind := .collecting }, .capture { name := "last" }]] [] [] [(.call (.resolve "Mid") [(.listLiteral [.param "first", (.sequenceSpread (.param "middle")), .param "last"])])])] [(.call (.resolve "Pair") [(.capture [.num 2, .num 3])]), (.call (.resolve "Many") [.num 1, .num 2]), (.call (.resolve "Same") [(.listLiteral [.num 1, .num 2, .num 3, .num 4])])])
#guard obs case_bare_forwarding_keeps_each_parameter_kind == "ok raw=S[5, L[1, 2], L[1, L[2, 3], 4]] n=3"

-- written-call-infers-its-written-names [name-resolution]: Add((a, b)) = a + b \n Single([a]) = a \n G = Add((x, y)) \n Construct = Single([x]) \n  \n G(2, 3) \n Construct(7)
def case_written_call_infers_its_written_names : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (alg ["x", "y"] [] [] [(.call (.resolve "Add") [(.capture [.param "x", .param "y"])])]), privateProp "Construct" (alg ["x"] [] [] [(.call (.resolve "Single") [(.listLiteral [.param "x"])])]), privateProp "Add" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.binary .add (.param "a") (.param "b"))]), privateProp "Single" (algWithParameterPatterns [.listValue [.capture { name := "a" }]] [] [] [.param "a"])] [(.call (.resolve "G") [.num 2, .num 3]), (.call (.resolve "Construct") [.num 7])])
#guard obs case_written_call_infers_its_written_names == "ok raw=S[5, 7] n=2"

-- repeated-callable-success-preserves-both-channels [variadic-calls]: B(*xs) = 5 + xs.count \n P(f, f, f, f, f) = [f, f(1), map([7], f)] \n P(B, 5, B, 5, 5) \n P(5, B, 5, 5, B)
def case_repeated_callable_success_preserves_both_channels : Expr :=
  .algorithmExpr (alg [] [] [privateProp "B" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.binary .add (.num 5) (.dotCall (.param "xs") "count" none))]), privateProp "P" (alg ["f", "f", "f", "f", "f"] [] [] [(.listLiteral [.param "f", (.call (.param "f") [.num 1]), (.call (.resolve "map") [(.listLiteral [.num 7]), .param "f"])])])] [(.call (.resolve "P") [.resolve "B", .num 5, .resolve "B", .num 5, .num 5]), (.call (.resolve "P") [.num 5, .resolve "B", .num 5, .num 5, .resolve "B"])])
#guard obs case_repeated_callable_success_preserves_both_channels == "ok raw=S[L[5, 6, L[6]], L[5, 6, L[6]]] n=2"

-- repeated-genuine-aliases-preserve-complete-binding [variadic-calls]: A(*xs) = 5 + xs.count \n P(f, f) = [f, f.count, f(1), map([7], f)] \n Both(left, right) = [P(left, right), P(right, left)] \n Share(original) = Both(original, original) \n Share(A)
def case_repeated_genuine_aliases_preserve_complete_binding : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.binary .add (.num 5) (.dotCall (.param "xs") "count" none))]), privateProp "P" (alg ["f", "f"] [] [] [(.listLiteral [.param "f", (.dotCall (.param "f") "count" none), (.call (.param "f") [.num 1]), (.call (.resolve "map") [(.listLiteral [.num 7]), .param "f"])])]), privateProp "Both" (alg ["left", "right"] [] [] [(.listLiteral [(.call (.resolve "P") [.param "left", .param "right"]), (.call (.resolve "P") [.param "right", .param "left"])])]), privateProp "Share" (alg ["original"] [] [] [(.call (.resolve "Both") [.param "original", .param "original"])])] [(.call (.resolve "Share") [.resolve "A"])])
#guard obs case_repeated_genuine_aliases_preserve_complete_binding == "ok raw=L[L[5, 1, 6, L[6]], L[5, 1, 6, L[6]]] n=1"

-- repeated-callable-identity-includes-captured-activation [variadic-calls]: P(f, f) = f(1) \n Outer(n, previous) = { \n   Inner(*xs) = 5 + n * xs.count \n   if(n == 1, Outer(2, Inner), P(previous, Inner)) \n } \n Outer(1, 0)
def case_repeated_callable_identity_includes_captured_activation : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg ["f", "f"] [] [] [(.call (.param "f") [.num 1])]), privateProp "Outer" (alg ["n", "previous"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["n"]) (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.binary .add (.num 5) (.binary .mul (.param "n") (.dotCall (.param "xs") "count" none)))])) with requiredOwnerDepths := some [("n", some 0)] }] [(.call (.resolve "if") [(.comparison (.param "n") [{ op := .eq, operand := (.num 1) }]), (.call (.resolve "Outer") [.num 2, .resolve "Inner"]), (.call (.resolve "P") [.param "previous", .resolve "Inner"])])])] [(.call (.resolve "Outer") [.num 1, .num 0])])
#guard obs case_repeated_callable_identity_includes_captured_activation == "err type"

-- repeated-dot-results-have-distinct-wrapper-identities [variadic-calls]: Obj = { public V = 5 } \n P(f, f) = f \n P(Obj.V, Obj.V)
def case_repeated_dot_results_have_distinct_wrapper_identities : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []), privateProp "P" (alg ["f", "f"] [] [] [.param "f"])] [(.call (.resolve "P") [(.dotCall (.resolve "Obj") "V" none), (.dotCall (.resolve "Obj") "V" none)])])
#guard obs case_repeated_dot_results_have_distinct_wrapper_identities == "ok raw=5 n=1"

-- repeated-forwarded-dot-wrapper-keeps-identity [variadic-calls]: Obj = { public V = 5 } \n P(f, f) = f() \n Pass(g) = P(g, g) \n Pass(Obj.V)
def case_repeated_forwarded_dot_wrapper_keeps_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 5])] []), privateProp "P" (alg ["f", "f"] [] [] [(.call (.param "f") [])]), privateProp "Pass" (alg ["g"] [] [] [(.call (.resolve "P") [.param "g", .param "g"])])] [(.call (.resolve "Pass") [(.dotCall (.resolve "Obj") "V" none)])])
#guard obs case_repeated_forwarded_dot_wrapper_keeps_identity == "ok raw=5 n=1"

-- collecting-pattern-list-merges-after-the-collector [variadic-calls]: Bad = 1 / 0 \n P(x, *rest, x) = x \n  \n P(1, Bad, 2)
def case_collecting_pattern_list_merges_after_the_collector : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Bad" (alg [] [] [] [(.binary .div (.num 1) (.num 0))]), privateProp "P" (algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }, { name := "x" }] [] [] [.param "x"])] [(.call (.resolve "P") [.num 1, .resolve "Bad", .num 2])])
#guard obs case_collecting_pattern_list_merges_after_the_collector == "err arity"

-- redundant-call-parens-canonical [variadic-calls]: Inner = (1, 2, 3) \n CountSequenceValue((*values)) = values.count \n NestedCount([(*values)]) = values.count \n  \n CountSequenceValue(Inner) \n CountSequenceValue((Inner)) \n CountSequenceValue(((1, 2, 3))) \n NestedCount([(1, 2, 3)]) \n NestedCount(([(1, 2, 3)]))
def case_redundant_call_parens_canonical : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inner" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "CountSequenceValue" (algWithParameterPatterns [.sequenceValue [.capture { name := "values", kind := .collecting }]] [] [] [(.dotCall (.param "values") "count" none)]), privateProp "NestedCount" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "values", kind := .collecting }]]] [] [] [(.dotCall (.param "values") "count" none)])] [(.call (.resolve "CountSequenceValue") [.resolve "Inner"]), (.call (.resolve "CountSequenceValue") [.resolve "Inner"]), (.call (.resolve "CountSequenceValue") [(.capture [.num 1, .num 2, .num 3])]), (.call (.resolve "NestedCount") [(.listLiteral [(.capture [.num 1, .num 2, .num 3])])]), (.call (.resolve "NestedCount") [(.listLiteral [(.capture [.num 1, .num 2, .num 3])])])])
#guard obs case_redundant_call_parens_canonical == "ok raw=S[3, 3, 3, 3, 3] n=5"

-- call-spread-into-conditional-clauses [variadic-calls]: F(0, 0) = 100 \n F(x, y) = x + y \n A = (1, 2) \n F(A*)
def case_call_spread_into_conditional_clauses : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (.conditional none [] [⟨.sequenceValue [.litInt 0, .litInt 0], (alg [] [] [] [.num 100])⟩, ⟨.sequenceValue [.bind "x", .bind "y"], (alg [] [] [] [(.binary .add (.param "x") (.param "y"))])⟩])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "A"))])])
#guard obs case_call_spread_into_conditional_clauses == "ok raw=3 n=1"

-- patterned-user-call-is-one-value-boundary [item-supply-vs-value]: F([x]) = 1, 2 \n F([7])
def case_patterned_user_call_is_one_value_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameterPatterns [.listValue [.capture { name := "x" }]] [] [] [.num 1, .num 2])] [(.call (.resolve "F") [(.listLiteral [.num 7])])])
#guard obs case_patterned_user_call_is_one_value_boundary == "ok raw=S[1, 2] n=1"

-- conditional-one-element-list-pattern [conditionals]: F([x]) = x \n F(n) = 0 \n  \n F([7]) \n F([1, 2])
def case_conditional_one_element_list_pattern : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.listValue [.bind "x"]], (alg [] [] [] [.param "x"])⟩, ⟨.bind "n", (alg [] [] [] [.num 0])⟩])] [(.call (.resolve "F") [(.listLiteral [.num 7])]), (.call (.resolve "F") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_conditional_one_element_list_pattern == "ok raw=S[7, 0] n=2"

-- conditional-sequence-pattern-matches-sequence-values-only [conditionals]: F((x, y)) = x + y \n F(z) = 0 \n  \n F((2, 3)) \n F([2, 3])
def case_conditional_sequence_pattern_matches_sequence_values_only : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.sequenceValue [.sequenceValue [.bind "x", .bind "y"]], (alg [] [] [] [(.binary .add (.param "x") (.param "y"))])⟩, ⟨.bind "z", (alg [] [] [] [.num 0])⟩])] [(.call (.resolve "F") [(.capture [.num 2, .num 3])]), (.call (.resolve "F") [(.listLiteral [.num 2, .num 3])])])
#guard obs case_conditional_sequence_pattern_matches_sequence_values_only == "ok raw=S[5, 0] n=2"

-- empty-structural-patterns-are-distinct-heads [conditionals]: Kind(()) = 'empty sequence' \n Kind([]) = 'empty list' \n Kind(x) = 'other' \n  \n Kind(()) \n Kind([]) \n Kind(0)
def case_empty_structural_patterns_are_distinct_heads : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Kind" (.conditional none [] [⟨.sequenceValue [.sequenceValue []], (alg [] [] [] [.stringLiteral "empty sequence"])⟩, ⟨.sequenceValue [.listValue []], (alg [] [] [] [.stringLiteral "empty list"])⟩, ⟨.bind "x", (alg [] [] [] [.stringLiteral "other"])⟩])] [(.call (.resolve "Kind") [(.emptySequence 0)]), (.call (.resolve "Kind") [(.listLiteral [])]), (.call (.resolve "Kind") [.num 0])])
#guard obs case_empty_structural_patterns_are_distinct_heads == "ok raw=S['empty sequence', 'empty list', 'other'] n=3"

-- conditional-clause-head-rejects-extra-arguments [conditionals]: F(0) = 1 \n F(n) = 2 \n F(1, 2)
def case_conditional_clause_head_rejects_extra_arguments : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [.num 2])⟩])] [(.call (.resolve "F") [.num 1, .num 2])])
#guard obs case_conditional_clause_head_rejects_extra_arguments == "err arity"

-- call-spread-dispatches-before-clause-selection [variadic-calls]: F(0, 0) = 100 \n F(x, y) = x + y \n A = (0, 0) \n F(A*)
def case_call_spread_dispatches_before_clause_selection : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 0, .num 0])]), privateProp "F" (.conditional none [] [⟨.sequenceValue [.litInt 0, .litInt 0], (alg [] [] [] [.num 100])⟩, ⟨.sequenceValue [.bind "x", .bind "y"], (alg [] [] [] [(.binary .add (.param "x") (.param "y"))])⟩])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "A"))])])
#guard obs case_call_spread_dispatches_before_clause_selection == "ok raw=100 n=1"

-- call-spread-into-patterned-callee [variadic-calls]: F(x, x) = x + 1 \n A = (7, 7) \n F(A*)
def case_call_spread_into_patterned_callee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 7, .num 7])]), privateProp "F" (alg ["x", "x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "A"))])])
#guard obs case_call_spread_into_patterned_callee == "ok raw=8 n=1"

-- wrapped-pair-collapses [sequence-construction]: ((1, 2))
def case_wrapped_pair_collapses : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2])])
#guard obs case_wrapped_pair_collapses == "ok raw=S[1, 2] n=1"

-- pair-of-pairs-preserved [sequence-construction]: ((1, 2), (3, 4))
def case_pair_of_pairs_preserved : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])
#guard obs case_pair_of_pairs_preserved == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- pair-then-empty-preserved [sequence-construction]: ((1, 2), ())
def case_pair_then_empty_preserved : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])
#guard obs case_pair_then_empty_preserved == "ok raw=S[S[1, 2], S[]] n=1"

-- spread-splices-into-sequence [sequence-construction]: x = (1, 2) \n (x*, 99)
def case_spread_splices_into_sequence : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.capture [(.sequenceSpread (.resolve "x")), .num 99])])
#guard obs case_spread_splices_into_sequence == "ok raw=S[1, 2, 99] n=1"

-- spread-empty-between-siblings [sequence-construction]: (1*, (), 2*)
def case_spread_empty_between_siblings : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 1)), (.emptySequence 0), (.sequenceSpread (.num 2))])])
#guard obs case_spread_empty_between_siblings == "ok raw=S[1, S[], 2] n=1"

-- root-spread-beside-slot [sequence-construction]: A = (1, 2) \n A*, 99
def case_root_spread_beside_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.sequenceSpread (.resolve "A")), .num 99])
#guard obs case_root_spread_beside_slot == "ok raw=S[1, 2, 99] n=3"

-- root-spread-then-value-slot [sequence-construction]: First = 1, 2 \n Second = 3, 4 \n  \n First*, Second
def case_root_spread_then_value_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "First" (alg [] [] [] [.num 1, .num 2]), privateProp "Second" (alg [] [] [] [.num 3, .num 4])] [(.sequenceSpread (.resolve "First")), .resolve "Second"])
#guard obs case_root_spread_then_value_slot == "ok raw=S[1, 2, S[3, 4]] n=3"

-- spread-slots-capture [sequence-construction]: A = 1, 2 \n B = 1*, 2 \n  \n A.count \n B.count
def case_spread_slots_capture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2]), privateProp "B" (alg [] [] [] [(.sequenceSpread (.num 1)), .num 2])] [(.dotCall (.resolve "A") "count" none), (.dotCall (.resolve "B") "count" none)])
#guard obs case_spread_slots_capture == "ok raw=S[2, 2] n=2"

-- spread-one-level-only [sequence-construction]: (1, (2, 3))*, 4
def case_spread_one_level_only : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, (.capture [.num 2, .num 3])])), .num 4])
#guard obs case_spread_one_level_only == "ok raw=S[1, S[2, 3], 4] n=3"

-- dot-access-value-boundary [access-boundaries]: A = { \n     X = 1, 2, 3 \n } \n A.X
def case_dot_access_value_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dot_access_value_boundary == "ok raw=S[1, 2, 3] n=1"

-- open-local-only-through-capture-row [access-boundaries]: Outer(p) = { \n     open Lib \n     Lib = { public G = { Q = p + 1 \n     (Q) } } \n     G \n } \n Outer(1)
def case_open_local_only_through_capture_row : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["p"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "G" (.localCapturedAncestorParams ["p"]) (alg [] [] [{ (privateLocalProp "Q" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [(.binary .add (.param "p") (.num 1))])) with requiredOwnerDepths := some [("p", some 2)] }] [.resolve "Q"])) with requiredOwnerDepths := some [("p", some 1)] }] [])] [.resolve "G"])] [(.call (.resolve "Outer") [.num 1])])
#guard obs case_open_local_only_through_capture_row == "ok raw=2 n=1"

-- open-self-contained-beside-same-named-sibling [access-boundaries]: Outer(p) = { \n     open Lib \n     Lib = { \n         public G = { Q = 7 \n         (Q) } \n         Q = p + 1 \n     } \n     G \n } \n Outer(1)
def case_open_self_contained_beside_same_named_sibling : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["p"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "G" (alg [] [] [privateProp "Q" (alg [] [] [] [.num 7])] [.resolve "Q"]), { (privateLocalProp "Q" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [(.binary .add (.param "p") (.num 1))])) with requiredOwnerDepths := some [("p", some 1)] }] [])] [.resolve "G"])] [(.call (.resolve "Outer") [.num 1])])
#guard obs case_open_self_contained_beside_same_named_sibling == "ok raw=7 n=1"

-- zero-param-block-higher-order [access-boundaries]: Call0 = f() \n Call0({42})
def case_zero_param_block_higher_order : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Call0" (alg ["f"] [] [] [(.call (.param "f") [])])] [(.call (.resolve "Call0") [(.algorithmExpr (alg [] [] [] [.num 42]))])])
#guard obs case_zero_param_block_higher_order == "ok raw=42 n=1"

-- dot-member-higher-order-parameter [access-boundaries]: K(a, t) = t(a) \n D(a, t) = a.t \n  \n K(7, {a+1}) \n D(7, {a+1})
def case_dot_member_higher_order_parameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["a", "t"] [] [] [(.call (.param "t") [.param "a"])]), privateProp "D" (alg ["a", "t"] [] [] [(.dotMember (.param "a") "t" (.param "t") none)])] [(.call (.resolve "K") [.num 7, (.algorithmExpr (alg ["a"] [] [] [(.binary .add (.param "a") (.num 1))]))]), (.call (.resolve "D") [.num 7, (.algorithmExpr (alg ["a"] [] [] [(.binary .add (.param "a") (.num 1))]))])])
#guard obs case_dot_member_higher_order_parameter == "ok raw=S[8, 8] n=2"

-- dot-member-fallback-implicit-signature [access-boundaries]: K = a.t \n K(7, {a+1})
def case_dot_member_fallback_implicit_signature : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["a", "t"] [] [] [(.dotMember (.param "a") "t" (.param "t") none)])] [(.call (.resolve "K") [.num 7, (.algorithmExpr (alg ["a"] [] [] [(.binary .add (.param "a") (.num 1))]))])])
#guard obs case_dot_member_fallback_implicit_signature == "ok raw=8 n=1"

-- grace-dot-higher-order-implicit [access-boundaries]: K = a~.t \n K({a+1}, 7)
def case_grace_dot_higher_order_implicit : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["t", "a"] [] [] [(.dotMember (.param "a") "t" (.param "t") none)])] [(.call (.resolve "K") [(.algorithmExpr (alg ["a"] [] [] [(.binary .add (.param "a") (.num 1))])), .num 7])])
#guard obs case_grace_dot_higher_order_implicit == "ok raw=8 n=1"

-- grace-dot-keeps-structural-precedence [access-boundaries]: V(x) = 99 \n Obj = { \n     public V = 42 \n     0 \n } \n Read = o~.V \n  \n Obj.V \n Read(Obj)
def case_grace_dot_keeps_structural_precedence : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 42])] [.num 0]), privateProp "Read" (alg ["o"] [] [] [(.dotCall (.param "o") "V" none)]), privateProp "V" (alg ["x"] [] [] [.num 99])] [(.dotCall (.resolve "Obj") "V" none), (.call (.resolve "Read") [.resolve "Obj"])])
#guard obs case_grace_dot_keeps_structural_precedence == "ok raw=S[42, 42] n=2"

-- dot-member-fallback-in-closed-parameter-list [access-boundaries]: K(x) = x.V \n Obj = {public V = 42} \n  \n K(Obj)
def case_dot_member_fallback_in_closed_parameter_list : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 42])] []), privateProp "K" (alg ["x"] [] [] [(.dotCall (.param "x") "V" none)])] [(.call (.resolve "K") [.resolve "Obj"])])
#guard obs case_dot_member_fallback_in_closed_parameter_list == "ok raw=42 n=1"

-- dot-fallback-on-known-receiver-stays-valid [access-boundaries]: Lib = { \n     public Double(x) = 2 * x \n } \n Dubel(a, b) = b * 3 \n  \n Lib.Dubel(4)
def case_dot_fallback_on_known_receiver_stays_valid : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "Double" (alg ["x"] [] [] [(.binary .mul (.num 2) (.param "x"))])] []), privateProp "Dubel" (alg ["a", "b"] [] [] [(.binary .mul (.param "b") (.num 3))])] [(.dotCall (.resolve "Lib") "Dubel" (some [.num 4]))])
#guard obs case_dot_fallback_on_known_receiver_stays_valid == "ok raw=12 n=1"

-- dot-string-declared-member-wins [strings]: Obj = { \n     public string = 5 \n     7 \n } \n  \n Obj.string
def case_dot_string_declared_member_wins : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "string" (alg [] [] [] [.num 5])] [.num 7])] [(.dotCall (.resolve "Obj") "string" none)])
#guard obs case_dot_string_declared_member_wins == "ok raw=5 n=1"

-- dot-string-intrinsic-on-structural-miss [strings]: string(x) = 99 \n Obj = { \n     public V = 1 \n     7 \n } \n  \n 3.string \n Obj.string \n string(3)
def case_dot_string_intrinsic_on_structural_miss : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 1])] [.num 7]), privateProp "string" (alg ["x"] [] [] [.num 99])] [(.dotCall (.num 3) "string" none), (.dotCall (.resolve "Obj") "string" none), (.call (.resolve "string") [.num 3])])
#guard obs case_dot_string_intrinsic_on_structural_miss == "ok raw=S['3', '7', 99] n=3"

-- grouped-structural-callee-is-the-member [access-boundaries]: Box = { \n     public G(x) = x * 10 \n } \n Apply(f, v) = f(v) \n  \n Box.G(2) \n (Box.G)(2) \n Apply(Box.G, 2)
def case_grouped_structural_callee_is_the_member : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Box" (alg [] [] [publicProp "G" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 10))])] []), privateProp "Apply" (alg ["f", "v"] [] [] [(.call (.param "f") [.param "v"])])] [(.dotCall (.resolve "Box") "G" (some [.num 2])), (.call (.dotCall (.resolve "Box") "G" none) [.num 2]), (.call (.resolve "Apply") [(.dotCall (.resolve "Box") "G" none), .num 2])])
#guard obs case_grouped_structural_callee_is_the_member == "ok raw=S[20, 20, 20] n=3"

-- grouped-zero-arg-member-call-is-fresh [access-boundaries]: Box = { \n     public V = 7 \n } \n  \n Box.V \n Box.V() \n (Box.V)()
def case_grouped_zero_arg_member_call_is_fresh : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Box" (alg [] [] [publicProp "V" (alg [] [] [] [.num 7])] [])] [(.dotCall (.resolve "Box") "V" none), (.dotCall (.resolve "Box") "V" (some [])), (.call (.dotCall (.resolve "Box") "V" none) [])])
#guard obs case_grouped_zero_arg_member_call_is_fresh == "ok raw=S[7, 7, 7] n=3"

-- computed-dot-callee-is-not-callable [errors]: Inc(x) = x + 1 \n (5.Inc)()
def case_computed_dot_callee_is_not_callable : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.dotCall (.num 5) "Inc" none) [])])
#guard obs case_computed_dot_callee_is_not_callable == "err notAnAlgorithm"

-- closed-list-may-fallback-name-is-runtime [access-boundaries]: Get(obj) = obj.size \n Obj = { \n     public size = 11 \n } \n size(v) = 77 \n  \n Get(Obj) \n Get(3)
def case_closed_list_may_fallback_name_is_runtime : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "size" (alg [] [] [] [.num 11])] []), privateProp "Get" (alg ["obj"] [] [] [(.dotCall (.param "obj") "size" none)]), privateProp "size" (alg ["v"] [] [] [.num 77])] [(.call (.resolve "Get") [.resolve "Obj"]), (.call (.resolve "Get") [.num 3])])
#guard obs case_closed_list_may_fallback_name_is_runtime == "ok raw=S[11, 77] n=2"

-- open-local-only-member-inside-owner [access-boundaries]: Outer(n) = { \n     open Inner \n     Inner = { \n         public X = n \n     } \n     X + 0 \n } \n Outer(5)
def case_open_local_only_member_inside_owner : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["n"] [.resolve "Inner"] [privateProp "Inner" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.param "n"])) with requiredOwnerDepths := some [("n", some 1)] }] [])] [(.binary .add (.resolve "X") (.num 0))])] [(.call (.resolve "Outer") [.num 5])])
#guard obs case_open_local_only_member_inside_owner == "ok raw=5 n=1"

-- dot-local-only-member-outside-owner [access-boundaries]: Outer(n) = { \n     Inner = { \n         public X = n \n     } \n     Inner.X \n } \n Outer.Inner.X
def case_dot_local_only_member_outside_owner : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["n"] [] [privateProp "Inner" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["n"]) (alg [] [] [] [.param "n"])) with requiredOwnerDepths := some [("n", some 1)] }] [])] [(.dotCall (.resolve "Inner") "X" none)])] [(.dotCall (.dotCall (.resolve "Outer") "Inner" none) "X" none)])
#guard obs case_dot_local_only_member_outside_owner == "err localOnlyProperty"

-- open-two-spellings-one-provider [name-resolution]: Lib = { \n     public Sub = { \n         public X = 1 \n     } \n     public R = { \n         open Sub, Lib.Sub \n         X \n     } \n } \n Lib.R
def case_open_two_spellings_one_provider : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []), publicProp "R" (alg [] [.resolve "Sub", (.dotCall (.resolve "Lib") "Sub" none)] [] [.resolve "X"])] [])] [(.dotCall (.resolve "Lib") "R" none)])
#guard obs case_open_two_spellings_one_provider == "ok raw=1 n=1"

-- ambiguous-open-unused-overlap-is-valid [name-resolution]: open A, B \n A = { \n     public X = 1 \n     public P = 10 \n } \n B = { \n     public X = 2 \n     public Q = 20 \n } \n P + Q
def case_ambiguous_open_unused_overlap_is_valid : Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1]), publicProp "P" (alg [] [] [] [.num 10])] []), privateProp "B" (alg [] [] [publicProp "X" (alg [] [] [] [.num 2]), publicProp "Q" (alg [] [] [] [.num 20])] [])] [(.binary .add (.resolve "P") (.resolve "Q"))])
#guard obs case_ambiguous_open_unused_overlap_is_valid == "ok raw=30 n=1"

-- dot-chain-structural-member-beats-extension [access-boundaries]: Lib = { \n     public Sub = { \n         public Q = 1 \n     } \n } \n  \n Q(x) = 99 \n  \n Lib.Sub.Q
def case_dot_chain_structural_member_beats_extension : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [])] []), privateProp "Q" (alg ["x"] [] [] [.num 99])] [(.dotCall (.dotCall (.resolve "Lib") "Sub" none) "Q" none)])
#guard obs case_dot_chain_structural_member_beats_extension == "ok raw=1 n=1"

-- dot-chain-extension-fallback-composes [access-boundaries]: A = x + 7 \n B = x * 5 \n  \n 3.A.B \n B(A(3)) \n B(3.A)
def case_dot_chain_extension_fallback_composes : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 7))]), privateProp "B" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 5))])] [(.dotCall (.dotCall (.num 3) "A" none) "B" none), (.call (.resolve "B") [(.call (.resolve "A") [.num 3])]), (.call (.resolve "B") [(.dotCall (.num 3) "A" none)])])
#guard obs case_dot_chain_extension_fallback_composes == "ok raw=S[50, 50, 50] n=3"

-- dot-chain-nested-structural-members [access-boundaries]: A = { \n     public B = { \n         public C = { \n             public D = 7 \n         } \n     } \n } \n D(x) = 93 \n  \n A.B.C.D
def case_dot_chain_nested_structural_members : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [publicProp "B" (alg [] [] [publicProp "C" (alg [] [] [publicProp "D" (alg [] [] [] [.num 7])] [])] [])] []), privateProp "D" (alg ["x"] [] [] [.num 93])] [(.dotCall (.dotCall (.dotCall (.resolve "A") "B" none) "C" none) "D" none)])
#guard obs case_dot_chain_nested_structural_members == "ok raw=7 n=1"

-- dot-chain-local-only-member-is-not-a-fallback [access-boundaries]: G(x) = { \n     public Sub = { \n         public Q = 1 \n         x \n     } \n     0 \n } \n Q(v) = 99 \n  \n G.Sub.Q
def case_dot_chain_local_only_member_is_not_a_fallback : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (alg ["x"] [] [{ (publicLocalProp "Sub" (.localCapturedAncestorParams ["x"]) (alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [.param "x"])) with requiredOwnerDepths := some [("x", some 0)] }] [.num 0]), privateProp "Q" (alg ["v"] [] [] [.num 99])] [(.dotCall (.dotCall (.resolve "G") "Sub" none) "Q" none)])
#guard obs case_dot_chain_local_only_member_is_not_a_fallback == "err localOnlyProperty"

-- capture-suppresses-higher-order-identity [access-boundaries]: Apply = f(9) \n Increment(x) = x + 1 \n Probe(u) = Apply((Increment, Increment)) \n Probe(0)
def case_capture_suppresses_higher_order_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Apply" (alg ["f"] [] [] [(.call (.param "f") [.num 9])]), privateProp "Increment" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Probe" (alg ["u"] [] [] [(.call (.resolve "Apply") [(.capture [.resolve "Increment", .resolve "Increment"])])])] [(.call (.resolve "Probe") [.num 0])])
#guard obs case_capture_suppresses_higher_order_identity == "err notAnAlgorithm"

-- capture-suppresses-structural-members [access-boundaries]: V(x) = 99 \n Obj = { \n     public V = 7 \n     0 \n } \n  \n Obj.V \n (Obj).V \n (Obj*).V
def case_capture_suppresses_structural_members : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "V" (alg [] [] [] [.num 7])] [.num 0]), privateProp "V" (alg ["x"] [] [] [.num 99])] [(.dotCall (.resolve "Obj") "V" none), (.dotCall (.resolve "Obj") "V" none), (.dotCall (.capture [(.sequenceSpread (.resolve "Obj"))]) "V" none)])
#guard obs case_capture_suppresses_structural_members == "ok raw=S[7, 7, 99] n=3"

-- output-dotted-access-ordinary [access-boundaries]: A = { \n     Output = 9 \n } \n  \n A.Output
def case_output_dotted_access_ordinary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "Output" (alg [] [] [] [.num 9])] [])] [(.dotCall (.resolve "A") "Output" none)])
#guard obs case_output_dotted_access_ordinary == "ok raw=9 n=1"

-- dot-call-structural-member-is-not-a-lexical-rewrite [access-boundaries]: B(a, c) = a * 100 + c \n Obj = { \n     public B(c) = c + 1 \n } \n  \n Obj.B(5) \n 3.B(5)
def case_dot_call_structural_member_is_not_a_lexical_rewrite : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Obj" (alg [] [] [publicProp "B" (alg ["c"] [] [] [(.binary .add (.param "c") (.num 1))])] []), privateProp "B" (alg ["a", "c"] [] [] [(.binary .add (.binary .mul (.param "a") (.num 100)) (.param "c"))])] [(.dotCall (.resolve "Obj") "B" (some [.num 5])), (.dotCall (.num 3) "B" (some [.num 5]))])
#guard obs case_dot_call_structural_member_is_not_a_lexical_rewrite == "ok raw=S[6, 305] n=2"

-- visibility-private-member-is-structural-not-exported [access-boundaries]: Lib = { \n     public Area = 4 \n     Helper = Area / 2 \n } \n  \n Lib.Area \n Lib.Helper
def case_visibility_private_member_is_structural_not_exported : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "Area" (alg [] [] [] [.num 4]), privateProp "Helper" (alg [] [] [] [(.binary .div (.resolve "Area") (.num 2))])] [])] [(.dotCall (.resolve "Lib") "Area" none), (.dotCall (.resolve "Lib") "Helper" none)])
#guard obs case_visibility_private_member_is_structural_not_exported == "ok raw=S[4, 2] n=2"

-- property-call-boundary [access-boundaries]: P = 1, 2, 3 \n P()
def case_property_call_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.call (.resolve "P") [])])
#guard obs case_property_call_boundary == "ok raw=S[1, 2, 3] n=1"

-- builtin-result-reentry [access-boundaries]: x = take((1, 2, 3), 2) \n x
def case_builtin_result_reentry : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 2])])] [.resolve "x"])
#guard obs case_builtin_result_reentry == "ok raw=L[1, 2] n=1"

-- zero-arg-access-of-parametrized [access-boundaries]: Add(a, b) = a + b \n  \n Add \n (1, 2)
def case_zero_arg_access_of_parametrized : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.param "b"))])] [.resolve "Add", (.capture [.num 1, .num 2])])
#guard obs case_zero_arg_access_of_parametrized == "err arity"

-- take-prefix [collection-builtins]: take((1, 2, 3, 4, 5), 3)
def case_take_prefix : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3, .num 4, .num 5]), .num 3])])
#guard obs case_take_prefix == "ok raw=L[1, 2, 3] n=1"

-- take-single-survivor [collection-builtins]: take(((1, 2), (3, 4)), 1)
def case_take_single_survivor : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])
#guard obs case_take_single_survivor == "ok raw=L[S[1, 2]] n=1"

-- take-zero-empty [collection-builtins]: take((1, 2, 3), 0)
def case_take_zero_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 0])])
#guard obs case_take_zero_empty == "ok raw=L[] n=1"

-- skip-prefix [collection-builtins]: skip((1, 2, 3, 4, 5), 3)
def case_skip_prefix : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.num 1, .num 2, .num 3, .num 4, .num 5]), .num 3])])
#guard obs case_skip_prefix == "ok raw=L[4, 5] n=1"

-- filter-keeps-matching [collection-builtins]: IsEven = x mod 2 == 0 \n filter((1, 2, 3, 4, 5, 6), IsEven)
def case_filter_keeps_matching : Expr :=
  .algorithmExpr (alg [] [] [privateProp "IsEven" (alg ["x"] [] [] [(.comparison (.binary .mod (.param "x") (.num 2)) [{ op := .eq, operand := (.num 0) }])])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3, .num 4, .num 5, .num 6]), .resolve "IsEven"])])
#guard obs case_filter_keeps_matching == "ok raw=L[2, 4, 6] n=1"

-- filter-single-survivor [collection-builtins]: Big(a) = a > 2 \n filter((1, 2, 3), Big)
def case_filter_single_survivor : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Big" (alg ["a"] [] [] [(.comparison (.param "a") [{ op := .gt, operand := (.num 2) }])])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "Big"])])
#guard obs case_filter_single_survivor == "ok raw=L[3] n=1"

-- filter-none-empty [collection-builtins]: No(a) = false \n filter((1, 2, 3), No)
def case_filter_none_empty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "No" (alg ["a"] [] [] [.boolLiteral false])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "No"])])
#guard obs case_filter_none_empty == "ok raw=L[] n=1"

-- map-transforms-items [collection-builtins]: Double = x * 2 \n map((1, 2, 3), Double)
def case_map_transforms_items : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Double" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))])] [(.call (.resolve "map") [(.capture [.num 1, .num 2, .num 3]), .resolve "Double"])])
#guard obs case_map_transforms_items == "ok raw=L[2, 4, 6] n=1"

-- map-single-item [collection-builtins]: M(a) = a \n map((7), M)
def case_map_single_item : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 7, .resolve "M"])])
#guard obs case_map_single_item == "ok raw=L[7] n=1"

-- map-pair-callback [collection-builtins]: Swap((a, b)) = (b, a) \n map(((1, 2), (3, 4)), Swap)
def case_map_pair_callback : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Swap" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.capture [.param "b", .param "a"])])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "Swap"])])
#guard obs case_map_pair_callback == "ok raw=L[S[2, 1], S[4, 3]] n=1"

-- clause-family-multirow-callback-rejected [collection-builtins]: F(0) = 1, 2 \n F(n) = n, n \n map([0, 3], F)
def case_clause_family_multirow_callback_rejected : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1, .num 2])⟩, ⟨.bind "n", (alg [] [] [] [.param "n", .param "n"])⟩])] [(.call (.resolve "map") [(.listLiteral [.num 0, .num 3]), .resolve "F"])])
#guard obs case_clause_family_multirow_callback_rejected == "err arity"

-- clause-family-multirow-reduce-step-rejected [collection-builtins]: R(e, 0) = e, 0 \n R(e, acc) = e, acc \n reduce([1], R, 0)
def case_clause_family_multirow_reduce_step_rejected : Expr :=
  .algorithmExpr (alg [] [] [privateProp "R" (.conditional none [] [⟨.sequenceValue [.bind "e", .litInt 0], (alg [] [] [] [.param "e", .num 0])⟩, ⟨.sequenceValue [.bind "e", .bind "acc"], (alg [] [] [] [.param "e", .param "acc"])⟩])] [(.call (.resolve "reduce") [(.listLiteral [.num 1]), .resolve "R", .num 0])])
#guard obs case_clause_family_multirow_reduce_step_rejected == "err arity"

-- clause-family-callback-single-value-accepted [collection-builtins]: F(0) = 1, 2 \n P(0) = (1, 2) \n P(n) = (n, n) \n L(0) = [] \n L(n) = [n] \n map([0, 3], P), map([0, 3], L), F(0) == P(0)
def case_clause_family_callback_single_value_accepted : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1, .num 2])⟩]), privateProp "P" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [(.capture [.num 1, .num 2])])⟩, ⟨.bind "n", (alg [] [] [] [(.capture [.param "n", .param "n"])])⟩]), privateProp "L" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [(.listLiteral [])])⟩, ⟨.bind "n", (alg [] [] [] [(.listLiteral [.param "n"])])⟩])] [(.call (.resolve "map") [(.listLiteral [.num 0, .num 3]), .resolve "P"]), (.call (.resolve "map") [(.listLiteral [.num 0, .num 3]), .resolve "L"]), (.comparison (.call (.resolve "F") [.num 0]) [{ op := .eq, operand := (.call (.resolve "P") [.num 0]) }])])
#guard obs case_clause_family_callback_single_value_accepted == "ok raw=S[L[S[1, 2], S[3, 3]], L[L[], L[3]], true] n=3"

-- callback-variadic-collects [collection-builtins]: Collect(*items) = items \n  \n [7].map(Collect) \n [(1, 2)].map(Collect) \n [[1, 2]].map(Collect)
def case_callback_variadic_collects : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.dotCall (.listLiteral [.num 7]) "map" (some [.resolve "Collect"])), (.dotCall (.listLiteral [(.capture [.num 1, .num 2])]) "map" (some [.resolve "Collect"])), (.dotCall (.listLiteral [(.listLiteral [.num 1, .num 2])]) "map" (some [.resolve "Collect"]))])
#guard obs case_callback_variadic_collects == "ok raw=S[L[L[7]], L[L[S[1, 2]]], L[L[L[1, 2]]]] n=3"

-- callback-mixed-variadic-rows [collection-builtins]: F((first, *middle, last)) = middle \n Rows = [(1, 2, 3, 4)] \n  \n Rows.map(F)
def case_callback_mixed_variadic_rows : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Rows" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2, .num 3, .num 4])])]), privateProp "F" (algWithParameterPatterns [.sequenceValue [.capture { name := "first" }, .capture { name := "middle", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "middle"])] [(.dotCall (.resolve "Rows") "map" (some [.resolve "F"]))])
#guard obs case_callback_mixed_variadic_rows == "ok raw=L[L[2, 3]] n=1"

-- callback-nested-pattern-binds-like-call [collection-builtins]: Head((x, *rest)) = [x, rest] \n  \n Head((7, 8)) \n [(7, 8)].map(Head) \n map([(7, 8), (9, 10, 11)], Head)
def case_callback_nested_pattern_binds_like_call : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Head" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [(.listLiteral [.param "x", .param "rest"])])] [(.call (.resolve "Head") [(.capture [.num 7, .num 8])]), (.dotCall (.listLiteral [(.capture [.num 7, .num 8])]) "map" (some [.resolve "Head"])), (.call (.resolve "map") [(.listLiteral [(.capture [.num 7, .num 8]), (.capture [.num 9, .num 10, .num 11])]), .resolve "Head"])])
#guard obs case_callback_nested_pattern_binds_like_call == "ok raw=S[L[7, L[8]], L[L[7, L[8]]], L[L[7, L[8]], L[9, L[10, 11]]]] n=3"

-- forwarded-callable-keeps-its-algorithm-channel [collection-builtins]: Cnt(*xs) = xs.count \n SumWhile(*s) = s.sum + 1, s.sum + 1 < 3 \n Apply(f, xs) = xs.map(f) \n Loop(g) = while(g, 0) \n Outer(xs) = { \n   Inner(g) = xs.map(g) \n   Inner(Cnt) \n } \n  \n Apply(Cnt, [1, 2]) \n Loop(SumWhile) \n Outer([1, 2])
def case_forwarded_callable_keeps_its_algorithm_channel : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Cnt" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.param "xs") "count" none)]), privateProp "SumWhile" (algWithParameters [{ name := "s", kind := .collecting }] [] [] [(.binary .add (.dotCall (.param "s") "sum" none) (.num 1)), (.comparison (.binary .add (.dotCall (.param "s") "sum" none) (.num 1)) [{ op := .lt, operand := (.num 3) }])]), privateProp "Apply" (alg ["f", "xs"] [] [] [(.dotCall (.param "xs") "map" (some [.param "f"]))]), privateProp "Loop" (alg ["g"] [] [] [(.call (.resolve "while") [.param "g", .num 0])]), privateProp "Outer" (alg ["xs"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["xs"]) (alg ["g"] [] [] [(.dotCall (.param "xs") "map" (some [.param "g"]))])) with requiredOwnerDepths := some [("xs", some 0)] }] [(.call (.resolve "Inner") [.resolve "Cnt"])])] [(.call (.resolve "Apply") [.resolve "Cnt", (.listLiteral [.num 1, .num 2])]), (.call (.resolve "Loop") [.resolve "SumWhile"]), (.call (.resolve "Outer") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_forwarded_callable_keeps_its_algorithm_channel == "ok raw=S[L[1, 1], 2, L[1, 1]] n=3"

-- builtin-call-assembly-respects-argument-roles [collection-builtins]: L = L + 1 \n Add(a, b) = a + b \n  \n map([], L) \n filter([], L) \n reduce([], L, 7) \n reduce([1, 2], Add, 10)
def case_builtin_call_assembly_respects_argument_roles : Expr :=
  .algorithmExpr (alg [] [] [privateProp "L" (alg [] [] [] [(.binary .add (.resolve "L") (.num 1))]), privateProp "Add" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.param "b"))])] [(.call (.resolve "map") [(.listLiteral []), .resolve "L"]), (.call (.resolve "filter") [(.listLiteral []), .resolve "L"]), (.call (.resolve "reduce") [(.listLiteral []), .resolve "L", .num 7]), (.call (.resolve "reduce") [(.listLiteral [.num 1, .num 2]), .resolve "Add", .num 10])])
#guard obs case_builtin_call_assembly_respects_argument_roles == "ok raw=S[L[], L[], 7, 13] n=4"

-- distinct-preserves-first [collection-builtins]: distinct((3, 1, 3, 2, 1, 2))
def case_distinct_preserves_first : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2])])])
#guard obs case_distinct_preserves_first == "ok raw=L[3, 1, 2] n=1"

-- distinct-structural-pairs [collection-builtins]: distinct(((1, 2), (1, 2), (3, 4)))
def case_distinct_structural_pairs : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_distinct_structural_pairs == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- take-family-tutorial [collection-builtins]: take((1, 2, 3, 4, 5), 3) \n  \n take(((1, 2), (3, 4)), 1) \n  \n range(1, 5).take(2)
def case_take_family_tutorial : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3, .num 4, .num 5]), .num 3]), (.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1]), (.dotCall (.call (.resolve "range") [.num 1, .num 5]) "take" (some [.num 2]))])
#guard obs case_take_family_tutorial == "ok raw=S[L[1, 2, 3], L[S[1, 2]], L[1, 2]] n=3"

-- distinct-family-tutorial [collection-builtins]: distinct((3, 1, 3, 2, 1, 2)) \n  \n distinct(((1, 2), (1, 2), (3, 4))) \n  \n Values = 3, 1, 3, 2, 1, 2 \n Values.distinct
def case_distinct_family_tutorial : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Values" (alg [] [] [] [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2])] [(.call (.resolve "distinct") [(.capture [.num 3, .num 1, .num 3, .num 2, .num 1, .num 2])]), (.call (.resolve "distinct") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), (.dotCall (.resolve "Values") "distinct" none)])
#guard obs case_distinct_family_tutorial == "ok raw=S[L[3, 1, 2], L[S[1, 2], S[3, 4]], L[3, 1, 2]] n=3"

-- spread-one-level-family [sequence-construction]: (1, 2)*, 3 \n 1*, (2, 3) \n (1, (2, 3))*, 4
def case_spread_one_level_family : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, .num 2])), .num 3, (.sequenceSpread (.num 1)), (.capture [.num 2, .num 3]), (.sequenceSpread (.capture [.num 1, (.capture [.num 2, .num 3])])), .num 4])
#guard obs case_spread_one_level_family == "ok raw=S[1, 2, 3, 1, S[2, 3], 1, S[2, 3], 4] n=8"

-- distinct-empties-collapse [collection-builtins]: distinct(((), ()))
def case_distinct_empties_collapse : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_distinct_empties_collapse == "ok raw=L[S[]] n=1"

-- order-sorts-atoms [collection-builtins]: order((3, 4, 2, 1, 3, 3))
def case_order_sorts_atoms : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])])])
#guard obs case_order_sorts_atoms == "ok raw=L[1, 2, 3, 3, 3, 4] n=1"

-- range-inclusive [collection-builtins]: range(1, 5)
def case_range_inclusive : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "range") [.num 1, .num 5])])
#guard obs case_range_inclusive == "ok raw=L[1, 2, 3, 4, 5] n=1"

-- range-single-value [collection-builtins]: range(3, 3)
def case_range_single_value : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "range") [.num 3, .num 3])])
#guard obs case_range_single_value == "ok raw=L[3] n=1"

-- spread-arguments-keep-written-order [collection-builtins]: Lo = 2 \n Hi = 4 \n range(Lo*, Hi*)
def case_spread_arguments_keep_written_order : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lo" (alg [] [] [] [.num 2]), privateProp "Hi" (alg [] [] [] [.num 4])] [(.call (.resolve "range") [(.sequenceSpread (.resolve "Lo")), (.sequenceSpread (.resolve "Hi"))])])
#guard obs case_spread_arguments_keep_written_order == "ok raw=L[2, 3, 4] n=1"

-- atoms-recursive-flatten [collection-builtins]: atoms(((1, 2), (3, 4)))
def case_atoms_recursive_flatten : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_atoms_recursive_flatten == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms-exact-list-result [collection-builtins]: atoms(7)
def case_atoms_exact_list_result : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.num 7])])
#guard obs case_atoms_exact_list_result == "ok raw=L[7] n=1"

-- atoms-list-traversal [collection-builtins]: atoms([1, 2])
def case_atoms_list_traversal : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_atoms_list_traversal == "ok raw=L[1, 2] n=1"

-- atoms-mixed-traversal [collection-builtins]: atoms([(1, 2), [3, [4]]])
def case_atoms_mixed_traversal : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.capture [.num 1, .num 2]), (.listLiteral [.num 3, (.listLiteral [.num 4])])])])])
#guard obs case_atoms_mixed_traversal == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms-list-composition [collection-builtins]: [1, 2, 3].skip(1).atoms
def case_atoms_list_composition : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) "skip" (some [.num 1])) "atoms" none)])
#guard obs case_atoms_list_composition == "ok raw=L[2, 3] n=1"

-- atoms-no-truthiness [collection-builtins]: if(atoms((1, [2])), 10, 20)
def case_atoms_no_truthiness : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "if") [(.call (.resolve "atoms") [(.capture [.num 1, (.listLiteral [.num 2])])]), .num 10, .num 20])])
#guard obs case_atoms_no_truthiness == "err type"

-- sum-of-range-collection [collection-builtins]: sum(range(1, 3))
def case_sum_of_range_collection : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "sum") [(.call (.resolve "range") [.num 1, .num 3])])])
#guard obs case_sum_of_range_collection == "ok raw=6 n=1"

-- count-family [collection-builtins]: count(()) \n count((())) \n  \n count(range(1, 5)) \n  \n count((10, 20, 30)) \n  \n count((3, 4, range(1, 5)*, 7)) \n  \n count((range(1, 5)*, 7)) \n  \n count(((1, 2), (3, 4))) \n  \n Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5) \n (Data:0).count
def case_count_family : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Data" (alg [] [] [] [(.capture [.num 7, .num 6, .num 4, .num 2, .num 1]), (.capture [.num 1, .num 2, .num 3, .num 4, .num 5])])] [(.call (.resolve "count") [(.emptySequence 0)]), (.call (.resolve "count") [(.emptySequence 0)]), (.call (.resolve "count") [(.call (.resolve "range") [.num 1, .num 5])]), (.call (.resolve "count") [(.capture [.num 10, .num 20, .num 30])]), (.call (.resolve "count") [(.capture [.num 3, .num 4, (.sequenceSpread (.call (.resolve "range") [.num 1, .num 5])), .num 7])]), (.call (.resolve "count") [(.capture [(.sequenceSpread (.call (.resolve "range") [.num 1, .num 5])), .num 7])]), (.call (.resolve "count") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), (.dotCall (.index (.resolve "Data") (.num 0)) "count" none)])
#guard obs case_count_family == "ok raw=S[0, 0, 5, 3, 8, 6, 2, 5] n=8"

-- count-scalar-and-string [collection-builtins]: count(5)
def case_count_scalar_and_string : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.num 5])])
#guard obs case_count_scalar_and_string == "ok raw=1 n=1"

-- count-dotcount-agree [collection-builtins]: T = (1, 2, 3) \n T.count \n  \n A = 1, 2, 3 \n A.count \n  \n count(A)
def case_count_dotcount_agree : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.dotCall (.resolve "T") "count" none), (.dotCall (.resolve "A") "count" none), (.call (.resolve "count") [.resolve "A"])])
#guard obs case_count_dotcount_agree == "ok raw=S[3, 3, 3] n=3"

-- if-value-boundary [collection-builtins]: X = 1, 2, 3 \n if(true, X, X)
def case_if_value_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.call (.resolve "if") [.boolLiteral true, .resolve "X", .resolve "X"])])
#guard obs case_if_value_boundary == "ok raw=S[1, 2, 3] n=1"

-- builtin-fixed-collection-arity [collection-builtins]: count((1, 2, 3))
def case_builtin_fixed_collection_arity : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_builtin_fixed_collection_arity == "ok raw=3 n=1"

-- reduce-accumulates-value [collection-builtins]: Append(item, (*history)) = (history*, item) \n reduce((2, 3, 4), Append, (0, 1))
def case_reduce_accumulates_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Append" (algWithParameterPatterns [.capture { name := "item" }, .sequenceValue [.capture { name := "history", kind := .collecting }]] [] [] [(.capture [(.sequenceSpread (.param "history")), .param "item"])])] [(.call (.resolve "reduce") [(.capture [.num 2, .num 3, .num 4]), .resolve "Append", (.capture [.num 0, .num 1])])])
#guard obs case_reduce_accumulates_value == "ok raw=S[0, 1, 2, 3, 4] n=1"

-- reduce-empty-initial-is-one-value [collection-builtins]: R(x, acc) = acc + x \n Init = 1, 2 \n reduce((), R, Init)
def case_reduce_empty_initial_is_one_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Init" (alg [] [] [] [.num 1, .num 2]), privateProp "R" (alg ["x", "acc"] [] [] [(.binary .add (.param "acc") (.param "x"))])] [(.call (.resolve "reduce") [(.emptySequence 0), .resolve "R", .resolve "Init"])])
#guard obs case_reduce_empty_initial_is_one_value == "ok raw=S[1, 2] n=1"

-- eq-structural-nested [equality-and-indexing]: A = 1, (2, 3) \n B = 1, (2, 3) \n A == B
def case_eq_structural_nested : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, (.capture [.num 2, .num 3])]), privateProp "B" (alg [] [] [] [.num 1, (.capture [.num 2, .num 3])])] [(.comparison (.resolve "A") [{ op := .eq, operand := (.resolve "B") }])])
#guard obs case_eq_structural_nested == "ok raw=true n=1"

-- index-selects-atom [equality-and-indexing]: Nums = 10, 20, 30, 40, 50 \n  \n # Select the third value (index 2): \n Nums:2
def case_index_selects_atom : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Nums" (alg [] [] [] [.num 10, .num 20, .num 30, .num 40, .num 50])] [(.index (.resolve "Nums") (.num 2))])
#guard obs case_index_selects_atom == "ok raw=30 n=1"

-- index-selects-one-value [equality-and-indexing]: Pairs = (1, 2), (3, 4) \n Pairs:0
def case_index_selects_one_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Pairs" (alg [] [] [] [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])] [(.index (.resolve "Pairs") (.num 0))])
#guard obs case_index_selects_one_value == "ok raw=S[1, 2] n=1"

-- selection-forms-agree [equality-and-indexing]: Coll(*xs) = xs \n Pairs = (1, 2), (3, 4) \n first(Pairs).Coll \n Pairs:0.Coll \n (Pairs:0)*.Coll \n Pairs:0.Coll(3)
def case_selection_forms_agree : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Pairs" (alg [] [] [] [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), privateProp "Coll" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.dotCall (.call (.resolve "first") [.resolve "Pairs"]) "Coll" none), (.dotCall (.index (.resolve "Pairs") (.num 0)) "Coll" none), (.call (.resolve "Coll") [(.sequenceSpread (.index (.resolve "Pairs") (.num 0)))]), (.dotCall (.index (.resolve "Pairs") (.num 0)) "Coll" (some [.num 3]))])
#guard obs case_selection_forms_agree == "ok raw=S[L[S[1, 2]], L[S[1, 2]], L[1, 2], L[S[1, 2], 3]] n=4"

-- index-nested-stays-intact [equality-and-indexing]: Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8)) \n Bags:0 \n Bags:0:1
def case_index_nested_stays_intact : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Bags" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), (.capture [(.capture [.num 5, .num 6]), (.capture [.num 7, .num 8])])])] [(.index (.resolve "Bags") (.num 0)), (.index (.index (.resolve "Bags") (.num 0)) (.num 1))])
#guard obs case_index_nested_stays_intact == "ok raw=S[S[S[1, 2], S[3, 4]], S[3, 4]] n=2"

-- index-empty-item-visible [equality-and-indexing]: x = ((), ()) \n x:0
def case_index_empty_item_visible : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index_empty_item_visible == "ok raw=S[] n=1"

-- index-out-of-range [equality-and-indexing]: x = (1, 2) \n x:9
def case_index_out_of_range : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_index_out_of_range == "err index"

-- index-captured-requality [equality-and-indexing]: x = ((1, 2), (3, 4)) \n y = x:0 \n y == (1, 2)
def case_index_captured_requality : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "y" (alg [] [] [] [(.index (.resolve "x") (.num 0))])] [(.comparison (.resolve "y") [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_index_captured_requality == "ok raw=true n=1"

-- output-rows-interleave-definitions [parser-layout]: A = 3 \n A + B \n B = 2
def case_output_rows_interleave_definitions : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 3]), privateProp "B" (alg [] [] [] [.num 2])] [(.binary .add (.resolve "A") (.resolve "B"))])
#guard obs case_output_rows_interleave_definitions == "ok raw=5 n=1"

-- trailing-comma-continues-line [parser-layout]: 1, \n 2
def case_trailing_comma_continues_line : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1, .num 2])
#guard obs case_trailing_comma_continues_line == "ok raw=S[1, 2] n=2"

-- star-before-operand-row-is-multiplication [parser-layout]: A = 4 \n B = 6 \n A* \n B
def case_star_before_operand_row_is_multiplication : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 4]), privateProp "B" (alg [] [] [] [.num 6])] [(.binary .mul (.resolve "A") (.resolve "B"))])
#guard obs case_star_before_operand_row_is_multiplication == "ok raw=24 n=1"

-- star-before-declaration-or-boundary-is-spread [parser-layout]: A = (1, 2) \n A* \n B = 5 \n B
def case_star_before_declaration_or_boundary_is_spread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [.num 5])] [(.sequenceSpread (.resolve "A")), .resolve "B"])
#guard obs case_star_before_declaration_or_boundary_is_spread == "ok raw=S[1, 2, 5] n=3"

-- line-final-star-in-definition-continues [parser-layout]: A = 2 \n X = A* \n 3 \n X
def case_line_final_star_in_definition_continues : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 2]), privateProp "X" (alg [] [] [] [(.binary .mul (.resolve "A") (.num 3))])] [.resolve "X"])
#guard obs case_line_final_star_in_definition_continues == "ok raw=6 n=1"

-- grace-in-branch-nested-block-belongs-to-the-block [name-resolution]: Apply(f) = f(1, 10) \n F(0) = Apply({ y - ~x }) \n F(0)
def case_grace_in_branch_nested_block_belongs_to_the_block : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Apply" (alg ["f"] [] [] [(.call (.param "f") [.num 1, .num 10])]), privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [(.call (.resolve "Apply") [(.algorithmExpr (alg ["x", "y"] [] [] [(.binary .sub (.param "y") (.param "x"))]))])])⟩])] [(.call (.resolve "F") [.num 0])])
#guard obs case_grace_in_branch_nested_block_belongs_to_the_block == "ok raw=9 n=1"

-- grace-saturation-is-valid [parser-layout]: F = ~x + 1 \n A = p - q \n G = A - z~ \n H = ~a + b * 10 \n F(3), G(1, 2, 3), H(1, 2)
def case_grace_saturation_is_valid : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "A" (alg ["p", "q"] [] [] [(.binary .sub (.param "p") (.param "q"))]), privateProp "G" (alg ["z", "p", "q"] [] [] [(.binary .sub (.call (.resolve "A") [.param "p", .param "q"]) (.param "z"))]), privateProp "H" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.binary .mul (.param "b") (.num 10)))])] [(.call (.resolve "F") [.num 3]), (.call (.resolve "G") [.num 1, .num 2, .num 3]), (.call (.resolve "H") [.num 1, .num 2])])
#guard obs case_grace_saturation_is_valid == "ok raw=S[4, -2, 21] n=3"

-- grace-weights-accumulate [parser-layout]: Weighted = a + 10 * b + 100 * ~~c \n  \n Weighted(1, 2, 3)
def case_grace_weights_accumulate : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Weighted" (alg ["c", "a", "b"] [] [] [(.binary .add (.binary .add (.param "a") (.binary .mul (.num 10) (.param "b"))) (.binary .mul (.num 100) (.param "c")))])] [(.call (.resolve "Weighted") [.num 1, .num 2, .num 3])])
#guard obs case_grace_weights_accumulate == "ok raw=132 n=1"

-- grace-front-first-movement [parser-layout]: A = s * 100 + ~x * 10 + ~y \n B = s~ * 100 + x~ * 10 + y \n C = a * 100 + b~ * 10 + ~~c \n D = a~ * 100 + b * 10 + ~c \n E = ~a * 100 + b * 10 + ~~c \n A(1, 2, 3), B(1, 2, 3), C(1, 2, 3), D(1, 2, 3), E(1, 2, 3)
def case_grace_front_first_movement : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["x", "y", "s"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "s") (.num 100)) (.binary .mul (.param "x") (.num 10))) (.param "y"))]), privateProp "B" (alg ["y", "s", "x"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "s") (.num 100)) (.binary .mul (.param "x") (.num 10))) (.param "y"))]), privateProp "C" (alg ["c", "a", "b"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "a") (.num 100)) (.binary .mul (.param "b") (.num 10))) (.param "c"))]), privateProp "D" (alg ["b", "c", "a"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "a") (.num 100)) (.binary .mul (.param "b") (.num 10))) (.param "c"))]), privateProp "E" (alg ["a", "c", "b"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "a") (.num 100)) (.binary .mul (.param "b") (.num 10))) (.param "c"))])] [(.call (.resolve "A") [.num 1, .num 2, .num 3]), (.call (.resolve "B") [.num 1, .num 2, .num 3]), (.call (.resolve "C") [.num 1, .num 2, .num 3]), (.call (.resolve "D") [.num 1, .num 2, .num 3]), (.call (.resolve "E") [.num 1, .num 2, .num 3])])
#guard obs case_grace_front_first_movement == "ok raw=S[312, 231, 231, 312, 132] n=5"

-- grace-prefix-marker-led-row [parser-layout]: K = { \n   a \n   ~b \n } \n K(10, 20)
def case_grace_prefix_marker_led_row : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["b", "a"] [] [] [.param "a", .param "b"])] [(.call (.resolve "K") [.num 10, .num 20])])
#guard obs case_grace_prefix_marker_led_row == "ok raw=S[20, 10] n=1"

-- adjacency-call-across-space [parser-layout]: Add(a, b) = a + b \n  \n Add(1, 2)    # 3 \n Add (1, 2)   # the same call, 3
def case_adjacency_call_across_space : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.param "b"))])] [(.call (.resolve "Add") [.num 1, .num 2]), (.call (.resolve "Add") [.num 1, .num 2])])
#guard obs case_adjacency_call_across_space == "ok raw=S[3, 3] n=2"

-- multiline-call-open-delimiter [parser-layout]: Add(a, b) = a + b \n  \n Add( \n   1, 2 \n )
def case_multiline_call_open_delimiter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Add" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.param "b"))])] [(.call (.resolve "Add") [.num 1, .num 2])])
#guard obs case_multiline_call_open_delimiter == "ok raw=3 n=1"

-- newline-ends-property-body [parser-layout]: P = 1 \n 2
def case_newline_ends_property_body : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1])] [.num 2])
#guard obs case_newline_ends_property_body == "ok raw=2 n=1"

-- comment-does-not-change-parse [parser-layout]: # comment \n 1 + 1
def case_comment_does_not_change_parse : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.num 1) (.num 1))])
#guard obs case_comment_does_not_change_parse == "ok raw=2 n=1"

-- spread-binds-before-list [parser-layout]: X(*vals) = vals.count \n b = (1, 2) \n X(7, b*)
def case_spread_binds_before_list : Expr :=
  .algorithmExpr (alg [] [] [privateProp "b" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "X" (algWithParameters [{ name := "vals", kind := .collecting }] [] [] [(.dotCall (.param "vals") "count" none)])] [(.call (.resolve "X") [.num 7, (.sequenceSpread (.resolve "b"))])])
#guard obs case_spread_binds_before_list == "ok raw=3 n=1"

-- dot-chain-continuation [parser-layout]: (1, 2, 3) \n .map { n * 2 } \n .sum
def case_dot_chain_continuation : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.dotCall (.capture [.num 1, .num 2, .num 3]) "map" (some [(.algorithmExpr (alg ["n"] [] [] [(.binary .mul (.param "n") (.num 2))]))])) "sum" none)])
#guard obs case_dot_chain_continuation == "ok raw=12 n=1"

-- arity-too-many-arguments [errors]: KeepFirst(a, b) = a \n KeepFirst(42, 999, 1)
def case_arity_too_many_arguments : Expr :=
  .algorithmExpr (alg [] [] [privateProp "KeepFirst" (alg ["a", "b"] [] [] [.param "a"])] [(.call (.resolve "KeepFirst") [.num 42, .num 999, .num 1])])
#guard obs case_arity_too_many_arguments == "err arity"

-- missing-output-not-a-value [errors]: A = { \n } \n A
def case_missing_output_not_a_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [])] [.resolve "A"])
#guard obs case_missing_output_not_a_value == "err missingOutput"

-- missing-output-as-builtin-arg [errors]: count({})
def case_missing_output_as_builtin_arg : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.algorithmExpr (alg [] [] [] []))])])
#guard obs case_missing_output_as_builtin_arg == "err missingOutput"

-- output-less-argument-is-not-an-omitted-argument [errors]: Coll(*xs) = xs \n Coll({})
def case_output_less_argument_is_not_an_omitted_argument : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Coll" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.call (.resolve "Coll") [(.algorithmExpr (alg [] [] [] []))])])
#guard obs case_output_less_argument_is_not_an_omitted_argument == "err missingOutput"

-- argument-value-outcome-is-final [errors]: Plus(f, x) = f + x \n Plus({x + 1}, 5)
def case_argument_value_outcome_is_final : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Plus" (alg ["f", "x"] [] [] [(.binary .add (.param "f") (.param "x"))])] [(.call (.resolve "Plus") [(.algorithmExpr (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])), .num 5])])
#guard obs case_argument_value_outcome_is_final == "err unresolvedImplicitParams"

-- scalar-op-rejects-sequence [errors]: (1, 2) + 1
def case_scalar_op_rejects_sequence : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.capture [.num 1, .num 2]) (.num 1))])
#guard obs case_scalar_op_rejects_sequence == "err type"

-- empty-sequence-is-not-an-operator-identity [errors]: 10 / ()
def case_empty_sequence_is_not_an_operator_identity : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .div (.num 10) (.emptySequence 0))])
#guard obs case_empty_sequence_is_not_an_operator_identity == "err type"

-- order-rejects-non-numeric [errors]: order((1, 'hello'))
def case_order_rejects_non_numeric : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 1, .stringLiteral "hello"])])])
#guard obs case_order_rejects_non_numeric == "err type"

-- division-by-zero [errors]: 1 / 0
def case_division_by_zero : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .div (.num 1) (.num 0))])
#guard obs case_division_by_zero == "err div0"

-- invoking-slot-without-callable-is-not-an-algorithm [errors]: map([1, 2], 5)
def case_invoking_slot_without_callable_is_not_an_algorithm : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), .num 5])])
#guard obs case_invoking_slot_without_callable_is_not_an_algorithm == "err notAnAlgorithm"

-- zero-parameter-callable-in-invoking-slot-is-arity [errors]: A = 7 \n map([1, 2], A)
def case_zero_parameter_callable_in_invoking_slot_is_arity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 7])] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), .resolve "A"])])
#guard obs case_zero_parameter_callable_in_invoking_slot_is_arity == "err arity"

-- kind-errors-are-type-mismatch [errors]: -()
def case_kind_errors_are_type_mismatch : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.emptySequence 0))])
#guard obs case_kind_errors_are_type_mismatch == "err type"

-- first-last-empty-is-bad-index [errors]: first(())
def case_first_last_empty_is_bad_index : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.emptySequence 0)])])
#guard obs case_first_last_empty_is_bad_index == "err index"

-- aggregate-empty-is-domain-error [errors]: min(())
def case_aggregate_empty_is_domain_error : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.emptySequence 0)])])
#guard obs case_aggregate_empty_is_domain_error == "err illegalInEval"

-- spread-arguments-fail-left-to-right [errors]: P = 1 / 0 \n Q = 'x' + 1 \n range(P*, Q*)
def case_spread_arguments_fail_left_to_right : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.binary .div (.num 1) (.num 0))]), privateProp "Q" (alg [] [] [] [(.binary .add (.stringLiteral "x") (.num 1))])] [(.call (.resolve "range") [(.sequenceSpread (.resolve "P")), (.sequenceSpread (.resolve "Q"))])])
#guard obs case_spread_arguments_fail_left_to_right == "err div0"

-- unresolved-implicit-parameter [errors]: Nope
def case_unresolved_implicit_parameter : Expr :=
  .algorithmExpr (alg ["Nope"] [] [] [.param "Nope"])
#guard obs case_unresolved_implicit_parameter == "err unresolvedImplicitParams"

-- string-equality-exact [strings]: 'ab' == 'ab'
def case_string_equality_exact : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.stringLiteral "ab") [{ op := .eq, operand := (.stringLiteral "ab") }])])
#guard obs case_string_equality_exact == "ok raw=true n=1"

-- string-displays-unquoted [strings]: x = 'ab' \n x
def case_string_displays_unquoted : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.stringLiteral "ab"])] [.resolve "x"])
#guard obs case_string_displays_unquoted == "ok raw='ab' n=1"

-- list-literal [lists]: [1, 2, 3]
def case_list_literal : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])])
#guard obs case_list_literal == "ok raw=L[1, 2, 3] n=1"

-- list-exactness [lists]: [7] == 7 \n [[1, 2]] == [1, 2] \n [[]] == []
def case_list_exactness : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral [.num 7]) [{ op := .eq, operand := (.num 7) }]), (.comparison (.listLiteral [(.listLiteral [.num 1, .num 2])]) [{ op := .eq, operand := (.listLiteral [.num 1, .num 2]) }]), (.comparison (.listLiteral [(.listLiteral [])]) [{ op := .eq, operand := (.listLiteral []) }])])
#guard obs case_list_exactness == "ok raw=S[false, false, false] n=3"

-- list-vs-sequence-kind [lists]: [] == () \n [1, 2] == (1, 2)
def case_list_vs_sequence_kind : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral []) [{ op := .eq, operand := (.emptySequence 0) }]), (.comparison (.listLiteral [.num 1, .num 2]) [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_list_vs_sequence_kind == "ok raw=S[false, false] n=2"

-- list-index-selects-element [lists]: [1, 2, 3]:0
def case_list_index_selects_element : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0))])
#guard obs case_list_index_selects_element == "ok raw=1 n=1"

-- list-index-nested-element-stays-exact [lists]: Rows = [[1, 2], [3, 4]] \n Rows:0 \n Rows:0:1
def case_list_index_nested_element_stays_exact : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Rows" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), (.listLiteral [.num 3, .num 4])])])] [(.index (.resolve "Rows") (.num 0)), (.index (.index (.resolve "Rows") (.num 0)) (.num 1))])
#guard obs case_list_index_nested_element_stays_exact == "ok raw=S[L[1, 2], 2] n=2"

-- list-index-out-of-range [lists]: []:0
def case_list_index_out_of_range : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.listLiteral []) (.num 0))])
#guard obs case_list_index_out_of_range == "err index"

-- list-index-builtin-results [lists]: range(1, 3):2
def case_list_index_builtin_results : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.call (.resolve "range") [.num 1, .num 3]) (.num 2))])
#guard obs case_list_index_builtin_results == "ok raw=3 n=1"

-- list-redundant-parens-canonicalize [lists]: ([1, 2]) == [1, 2]
def case_list_redundant_parens_canonicalize : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral [.num 1, .num 2]) [{ op := .eq, operand := (.listLiteral [.num 1, .num 2]) }])])
#guard obs case_list_redundant_parens_canonicalize == "ok raw=true n=1"

-- list-spread-capture [lists]: A = [1, 2, 3] \n  \n x = A \n y = (A*) \n  \n x \n y
def case_list_spread_capture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [.resolve "A"]), privateProp "y" (alg [] [] [] [(.capture [(.sequenceSpread (.resolve "A"))])])] [.resolve "x", .resolve "y"])
#guard obs case_list_spread_capture == "ok raw=S[L[1, 2, 3], S[1, 2, 3]] n=2"

-- list-spread-edges [lists]: A = [] \n B = [7] \n C = [[7]] \n  \n A*, \n B*, \n C*
def case_list_spread_edges : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "C" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 7])])])] [(.sequenceSpread (.resolve "A")), (.sequenceSpread (.resolve "B")), (.sequenceSpread (.resolve "C"))])
#guard obs case_list_spread_edges == "ok raw=S[7, L[7]] n=2"

-- list-literal-spread-elements [lists]: A = 1, 2, 3 \n  \n [A*] \n [0, A*, 4]
def case_list_literal_spread_elements : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.listLiteral [(.sequenceSpread (.resolve "A"))]), (.listLiteral [.num 0, (.sequenceSpread (.resolve "A")), .num 4])])
#guard obs case_list_literal_spread_elements == "ok raw=S[L[1, 2, 3], L[0, 1, 2, 3, 4]] n=2"

-- list-elements-preserve-boundaries [lists]: A = [1, 2] \n B = [3, 4] \n  \n [A, B] \n [A*, B*] \n [A, B*]
def case_list_elements_preserve_boundaries : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [(.listLiteral [.resolve "A", .resolve "B"]), (.listLiteral [(.sequenceSpread (.resolve "A")), (.sequenceSpread (.resolve "B"))]), (.listLiteral [.resolve "A", (.sequenceSpread (.resolve "B"))])])
#guard obs case_list_elements_preserve_boundaries == "ok raw=S[L[L[1, 2], L[3, 4]], L[1, 2, 3, 4], L[L[1, 2], 3, 4]] n=3"

-- list-written-slot-reifies-selection [lists]: S = ((1, 2), (3, 4)) \n  \n [S:0, 5] \n [S:0*, 5]
def case_list_written_slot_reifies_selection : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.listLiteral [(.index (.resolve "S") (.num 0)), .num 5]), (.listLiteral [(.sequenceSpread (.index (.resolve "S") (.num 0))), .num 5])])
#guard obs case_list_written_slot_reifies_selection == "ok raw=S[L[S[1, 2], 5], L[1, 2, 5]] n=2"

-- list-empty-spread-neutral [lists]: [1, []*, 2] \n [1, ()*, 2]
def case_list_empty_spread_neutral : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, (.sequenceSpread (.listLiteral [])), .num 2]), (.listLiteral [.num 1, (.sequenceSpread (.emptySequence 0)), .num 2])])
#guard obs case_list_empty_spread_neutral == "ok raw=S[L[1, 2], L[1, 2]] n=2"

-- list-call-boundary [lists]: F(a, b, c) = a + b + c \n One(x) = 7 \n  \n A = [1, 2, 3] \n  \n One(A) \n F(A*)
def case_list_call_boundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "F" (alg ["a", "b", "c"] [] [] [(.binary .add (.binary .add (.param "a") (.param "b")) (.param "c"))]), privateProp "One" (alg ["x"] [] [] [.num 7])] [(.call (.resolve "One") [.resolve "A"]), (.call (.resolve "F") [(.sequenceSpread (.resolve "A"))])])
#guard obs case_list_call_boundary == "ok raw=S[7, 6] n=2"

-- list-lone-deconstruction [lists]: x, y, z = [1, 2, 3] \n  \n x \n y \n z
def case_list_lone_deconstruction : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "x", .resolve "y", .resolve "z"])
#guard obs case_list_lone_deconstruction == "ok raw=S[1, 2, 3] n=3"

-- list-deconstruction-not-recursive [lists]: x, y = [[1, 2], 3] \n  \n x \n y
def case_list_deconstruction_not_recursive : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x", .resolve "y"])
#guard obs case_list_deconstruction_not_recursive == "ok raw=S[L[1, 2], 3] n=2"

-- collecting-binding-exact-list [lists]: x, *rest = [1, 2, 3] \n  \n x \n rest
def case_collecting_binding_exact_list : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "rest" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) [.resolve "$deconstruct$0"])])] [.resolve "x", .resolve "rest"])
#guard obs case_collecting_binding_exact_list == "ok raw=S[1, L[2, 3]] n=2"

-- list-lone-collecting-assignment [lists]: *items = [1, 2, 3] \n items
def case_list_lone_collecting_assignment : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "items" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.unpacking [.capture { name := "items", kind := .collecting }]] [] [] [.param "items"])) [.resolve "$deconstruct$0"])])] [.resolve "items"])
#guard obs case_list_lone_collecting_assignment == "ok raw=L[1, 2, 3] n=1"

-- list-builtin-collection [lists]: count([1, 2, 3])
def case_list_builtin_collection : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.num 1, .num 2, .num 3])])])
#guard obs case_list_builtin_collection == "ok raw=3 n=1"

-- callable-argument-parameter-shadowing [access-boundaries]: A = q + 1 \n Add1(x) = x + 1 \n F(x) = Add1(A) \n  \n F(7)
def case_callable_argument_parameter_shadowing : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["q"] [] [] [(.binary .add (.param "q") (.num 1))]), privateProp "Add1" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "F" (alg ["x"] [] [] [(.call (.resolve "Add1") [.resolve "A"])])] [(.call (.resolve "F") [.num 7])])
#guard obs case_callable_argument_parameter_shadowing == "err arity"

-- value-argument-parameter-shadowing [access-boundaries]: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(f) = f(2) \n     Inner(5) \n } \n  \n Apply(Inc)
def case_value_argument_parameter_shadowing : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [privateProp "Inner" (alg ["f"] [] [] [(.call (.param "f") [.num 2])])] [(.call (.resolve "Inner") [.num 5])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_value_argument_parameter_shadowing == "err notAnAlgorithm"

-- value-parameter-shadowing-through-nested-scope [access-boundaries]: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(f) = { \n         Local(y) = f(y) \n         Local(2) \n     } \n     Inner(5) \n } \n  \n Apply(Inc)
def case_value_parameter_shadowing_through_nested_scope : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [privateProp "Inner" (alg ["f"] [] [{ (privateLocalProp "Local" (.localCapturedAncestorParams ["f"]) (alg ["y"] [] [] [(.call (.param "f") [.param "y"])])) with requiredOwnerDepths := some [("f", some 0)] }] [(.call (.resolve "Local") [.num 2])])] [(.call (.resolve "Inner") [.num 5])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_value_parameter_shadowing_through_nested_scope == "err notAnAlgorithm"

-- value-binder-parameter-shadowing [conditionals]: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(0) = 0 \n     Inner(f) = f(2) \n     Inner(5) \n } \n  \n Apply(Inc)
def case_value_binder_parameter_shadowing : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [privateProp "Inner" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 0])⟩, ⟨.bind "f", (alg [] [] [] [(.call (.param "f") [.num 2])])⟩])] [(.call (.resolve "Inner") [.num 5])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_value_binder_parameter_shadowing == "err notAnAlgorithm"

-- ancestor-callable-visible-without-same-named-parameter [access-boundaries]: Inc(x) = x + 1 \n  \n Apply(f) = { \n     Inner(x) = f(x) \n     Inner(5) \n } \n  \n Apply(Inc)
def case_ancestor_callable_visible_without_same_named_parameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["f"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["f"]) (alg ["x"] [] [] [(.call (.param "f") [.param "x"])])) with requiredOwnerDepths := some [("f", some 0)] }] [(.call (.resolve "Inner") [.num 5])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_ancestor_callable_visible_without_same_named_parameter == "ok raw=6 n=1"

-- forwarded-parameter-leaves-an-opened-reference [name-resolution]: Lib = { public v = 99 } \n Outer = { \n     Inner = { open Lib \n         v \n     } \n     Need = v \n     Inner + Need \n } \n Outer(7)
def case_forwarded_parameter_leaves_an_opened_reference : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "v" (alg [] [] [] [.num 99])] []), privateProp "Outer" (alg ["v"] [] [privateProp "Inner" (alg [] [.resolve "Lib"] [] [.resolve "v"]), privateProp "Need" (alg ["v"] [] [] [.param "v"])] [(.binary .add (.resolve "Inner") (.call (.resolve "Need") [.param "v"]))])] [(.call (.resolve "Outer") [.num 7])])
#guard obs case_forwarded_parameter_leaves_an_opened_reference == "ok raw=106 n=1"

-- forwarding-reuses-a-captured-ancestor-parameter [name-resolution]: A = y + 1 \n F(y) = { \n     G = y * 1000 + A \n     H(y) = G \n     H(100) \n } \n F(3)
def case_forwarding_reuses_a_captured_ancestor_parameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["y"] [] [] [(.binary .add (.param "y") (.num 1))]), privateProp "F" (alg ["y"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [(.binary .add (.binary .mul (.param "y") (.num 1000)) (.call (.resolve "A") [.param "y"]))])) with requiredOwnerDepths := some [("y", some 0)] }, { (privateLocalProp "H" (.localCapturedAncestorParams ["y"]) (alg ["y"] [] [] [.resolve "G"])) with requiredOwnerDepths := some [("y", some 0)] }] [(.call (.resolve "H") [.num 100])])] [(.call (.resolve "F") [.num 3])])
#guard obs case_forwarding_reuses_a_captured_ancestor_parameter == "ok raw=3004 n=1"

-- forwarding-never-supplies-a-property-an-open-or-a-builtin [name-resolution]: v = 99 \n Need(v) = v \n Outer = Need + 1 \n Outer(7)
def case_forwarding_never_supplies_a_property_an_open_or_a_builtin : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v" (alg [] [] [] [.num 99]), privateProp "Outer" (alg ["v"] [] [] [(.binary .add (.call (.resolve "Need") [.param "v"]) (.num 1))]), privateProp "Need" (alg ["v"] [] [] [.param "v"])] [(.call (.resolve "Outer") [.num 7])])
#guard obs case_forwarding_never_supplies_a_property_an_open_or_a_builtin == "ok raw=8 n=1"

-- forwarding-reused-binding-kind-preserves-values [name-resolution]: Target(tag, *items) = items \n Collected(tag, *items) = { \n     G(q) = [Target]:0 \n     G(99) \n } \n Fixed(tag, items) = { \n     G(q) = [Target]:0 \n     G(99) \n } \n Head(x, *rest) = x + rest.count \n Partial(x) = { \n     H = [Head]:0 \n     [H, H(10, 20)] \n } \n [Collected(0, (1, 2), [3], ()), Fixed(0, [(1, 2), [3], ()]), Partial(4)]
def case_forwarding_reused_binding_kind_preserves_values : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Target" (algWithParameters [{ name := "tag" }, { name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Collected" (algWithParameters [{ name := "tag" }, { name := "items", kind := .collecting }] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["items", "tag"]) (alg ["q"] [] [] [(.index (.listLiteral [(.call (.resolve "Target") [.param "tag", (.sequenceSpread (.param "items"))])]) (.num 0))])) with requiredOwnerDepths := some [("items", some 0), ("tag", some 0)] }] [(.call (.resolve "G") [.num 99])]), privateProp "Fixed" (alg ["tag", "items"] [] [{ (privateLocalProp "G" (.localCapturedAncestorParams ["items", "tag"]) (alg ["q"] [] [] [(.index (.listLiteral [(.call (.resolve "Target") [.param "tag", .param "items"])]) (.num 0))])) with requiredOwnerDepths := some [("items", some 0), ("tag", some 0)] }] [(.call (.resolve "G") [.num 99])]), privateProp "Head" (algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }] [] [] [(.binary .add (.param "x") (.dotCall (.param "rest") "count" none))]), privateProp "Partial" (alg ["x"] [] [{ (privateLocalProp "H" (.localCapturedAncestorParams ["x"]) (algWithParameters [{ name := "rest", kind := .collecting }] [] [] [(.index (.listLiteral [(.call (.resolve "Head") [.param "x", (.sequenceSpread (.param "rest"))])]) (.num 0))])) with requiredOwnerDepths := some [("x", some 0)] }] [(.listLiteral [.resolve "H", (.call (.resolve "H") [.num 10, .num 20])])])] [(.listLiteral [(.call (.resolve "Collected") [.num 0, (.capture [.num 1, .num 2]), (.listLiteral [.num 3]), (.emptySequence 0)]), (.call (.resolve "Fixed") [.num 0, (.listLiteral [(.capture [.num 1, .num 2]), (.listLiteral [.num 3]), (.emptySequence 0)])]), (.call (.resolve "Partial") [.num 4])])])
#guard obs case_forwarding_reused_binding_kind_preserves_values == "ok raw=L[L[S[1, 2], L[3], S[]], L[L[S[1, 2], L[3], S[]]], L[4, 6]] n=1"

-- ownership-captured-parameter-beats-outer-property [name-resolution]: v = 99 \n Outer(v) = { \n     Inner = v + 1 \n     Inner \n } \n Outer(7)
def case_ownership_captured_parameter_beats_outer_property : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v" (alg [] [] [] [.num 99]), privateProp "Outer" (alg ["v"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["v"]) (alg [] [] [] [(.binary .add (.param "v") (.num 1))])) with requiredOwnerDepths := some [("v", some 0)] }] [.resolve "Inner"])] [(.call (.resolve "Outer") [.num 7])])
#guard obs case_ownership_captured_parameter_beats_outer_property == "ok raw=8 n=1"

-- ownership-nearest-enclosing-parameter-wins [name-resolution]: v = 99 \n Outer(v) = { \n     Mid(v) = { \n         Inner = v + 1 \n         Inner \n     } \n     Mid(7) \n } \n Outer(20)
def case_ownership_nearest_enclosing_parameter_wins : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v" (alg [] [] [] [.num 99]), privateProp "Outer" (alg ["v"] [] [privateProp "Mid" (alg ["v"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["v"]) (alg [] [] [] [(.binary .add (.param "v") (.num 1))])) with requiredOwnerDepths := some [("v", some 0)] }] [.resolve "Inner"])] [(.call (.resolve "Mid") [.num 7])])] [(.call (.resolve "Outer") [.num 20])])
#guard obs case_ownership_nearest_enclosing_parameter_wins == "ok raw=8 n=1"

-- ownership-parameter-beats-prelude-alias [name-resolution]: Outer(pi) = { \n     Inner = pi + 1 \n     Inner \n } \n Outer(7)
def case_ownership_parameter_beats_prelude_alias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["pi"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["pi"]) (alg [] [] [] [(.binary .add (.param "pi") (.num 1))])) with requiredOwnerDepths := some [("pi", some 0)] }] [.resolve "Inner"])] [(.call (.resolve "Outer") [.num 7])])
#guard obs case_ownership_parameter_beats_prelude_alias == "ok raw=8 n=1"

-- ownership-parameter-beats-opened-name [name-resolution]: Lib = { \n     public v = 99 \n } \n Outer(v) = { \n     open Lib \n     Inner = v + 1 \n     Inner \n } \n Outer(7)
def case_ownership_parameter_beats_opened_name : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "v" (alg [] [] [] [.num 99])] []), privateProp "Outer" (alg ["v"] [.resolve "Lib"] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["v"]) (alg [] [] [] [(.binary .add (.param "v") (.num 1))])) with requiredOwnerDepths := some [("v", some 0)] }] [.resolve "Inner"])] [(.call (.resolve "Outer") [.num 7])])
#guard obs case_ownership_parameter_beats_opened_name == "ok raw=8 n=1"

-- clause-family-nested-in-branch-body-binds-its-own-binders [conditionals]: n = 99 \n F(0) = { \n   G(0) = 'zero' \n   G(n) = n \n   G(5) \n } \n F(k) = k \n  \n F(0)
def case_clause_family_nested_in_branch_body_binds_its_own_binders : Expr :=
  .algorithmExpr (alg [] [] [privateProp "n" (alg [] [] [] [.num 99]), privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [privateProp "G" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.stringLiteral "zero"])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "G") [.num 5])])⟩, ⟨.bind "k", (alg [] [] [] [.param "k"])⟩])] [(.call (.resolve "F") [.num 0])])
#guard obs case_clause_family_nested_in_branch_body_binds_its_own_binders == "ok raw=5 n=1"

-- conditional-branch-pattern-is-a-closed-input-specification [conditionals]: A = x + 1 \n F(0) = A + 0 \n F(n) = n \n  \n F(0)
def case_conditional_branch_pattern_is_a_closed_input_specification : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [(.binary .add (.resolve "A") (.num 0))])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "F") [.num 0])])
#guard obs case_conditional_branch_pattern_is_a_closed_input_specification == "err arity"

-- conditional-branch-inline-open-exposes-members-to-the-branch [conditionals]: F(0) = { \n   open { \n     public Helper = 5 \n   } \n   Helper \n } \n F(n) = n \n  \n F(0)
def case_conditional_branch_inline_open_exposes_members_to_the_branch : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [(.algorithmExpr (alg [] [] [publicProp "Helper" (alg [] [] [] [.num 5])] []))] [] [.resolve "Helper"])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "F") [.num 0])])
#guard obs case_conditional_branch_inline_open_exposes_members_to_the_branch == "ok raw=5 n=1"

-- conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches [conditionals]: open Lib \n Lib = { \n   public Helper = 7 \n } \n F(0) = { \n   open { \n     public Helper = 5 \n   } \n   Helper \n } \n F(1) = Helper \n F(n) = n \n  \n F(0), F(1), F(2)
def case_conditional_branch_inline_open_does_not_shadow_an_enclosing_open_in_sibling_branches : Expr :=
  .algorithmExpr (alg [] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [publicProp "Helper" (alg [] [] [] [.num 7])] []), privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [(.algorithmExpr (alg [] [] [publicProp "Helper" (alg [] [] [] [.num 5])] []))] [] [.resolve "Helper"])⟩, ⟨.litInt 1, (alg [] [] [] [.resolve "Helper"])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "F") [.num 0]), (.call (.resolve "F") [.num 1]), (.call (.resolve "F") [.num 2])])
#guard obs case_conditional_branch_inline_open_does_not_shadow_an_enclosing_open_in_sibling_branches == "ok raw=S[5, 7, 2] n=3"

-- conditional-branch-local-library-is-openable-within-the-branch [conditionals]: F(0) = { \n   Lib = { \n     public X = 1 \n   } \n   G = { \n     open Lib \n     X \n   } \n   G \n } \n F(n) = n \n  \n F(0)
def case_conditional_branch_local_library_is_openable_within_the_branch : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []), privateProp "G" (alg [] [.resolve "Lib"] [] [.resolve "X"])] [.resolve "G"])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩])] [(.call (.resolve "F") [.num 0])])
#guard obs case_conditional_branch_local_library_is_openable_within_the_branch == "ok raw=1 n=1"

-- builtin-callable-is-an-ordinary-prelude-binding [name-resolution]: if(x) = x + 1 \n  \n if(7) \n 7.if \n if((7)*)
def case_builtin_callable_is_an_ordinary_prelude_binding : Expr :=
  .algorithmExpr (alg [] [] [privateProp "if" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.num 7]), (.dotCall (.num 7) "if" none), (.call (.resolve "if") [(.sequenceSpread (.num 7))])])
#guard obs case_builtin_callable_is_an_ordinary_prelude_binding == "ok raw=S[8, 8, 8] n=3"

-- no-arity-based-callable-selection [name-resolution]: if(x) = x + 1 \n  \n if(true, 2, 3)
def case_no_arity_based_callable_selection : Expr :=
  .algorithmExpr (alg [] [] [privateProp "if" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, .num 2, .num 3])])
#guard obs case_no_arity_based_callable_selection == "err arity"

-- if-composition-forms-agree [conditionals]: Cond = true \n Branches = (10, 20) \n Apply3(f, a, b, c) = f(a, b, c) \n  \n if(Cond, 10, 20) \n Cond.if(10, 20) \n if(Cond, Branches*) \n Cond.if(Branches*) \n Apply3(if, Cond, 10, 20)
def case_if_composition_forms_agree : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Cond" (alg [] [] [] [.boolLiteral true]), privateProp "Branches" (alg [] [] [] [(.capture [.num 10, .num 20])]), privateProp "Apply3" (alg ["f", "a", "b", "c"] [] [] [(.call (.param "f") [.param "a", .param "b", .param "c"])])] [(.call (.resolve "if") [.resolve "Cond", .num 10, .num 20]), (.dotCall (.resolve "Cond") "if" (some [.num 10, .num 20])), (.call (.resolve "if") [.resolve "Cond", (.sequenceSpread (.resolve "Branches"))]), (.dotCall (.resolve "Cond") "if" (some [(.sequenceSpread (.resolve "Branches"))])), (.call (.resolve "Apply3") [.resolve "if", .resolve "Cond", .num 10, .num 20])])
#guard obs case_if_composition_forms_agree == "ok raw=S[10, 10, 10, 10, 10] n=5"

-- if-arity-is-uniform-across-spellings [conditionals]: if(true, 2)
def case_if_arity_is_uniform_across_spellings : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, .num 2])])
#guard obs case_if_arity_is_uniform_across_spellings == "err arity"

-- if-laziness-follows-the-resolved-identity [conditionals]: Boom = 1 / 0 \n  \n if(true, 10, Boom) \n false.if(Boom, 20)
def case_if_laziness_follows_the_resolved_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Boom" (alg [] [] [] [(.binary .div (.num 1) (.num 0))])] [(.call (.resolve "if") [.boolLiteral true, .num 10, .resolve "Boom"]), (.dotCall (.boolLiteral false) "if" (some [.resolve "Boom", .num 20]))])
#guard obs case_if_laziness_follows_the_resolved_identity == "ok raw=S[10, 20] n=2"

-- lazy-slot-demand-is-the-ordinary-zero-argument-demand [conditionals]: Inc(x) = x + 1 \n Probe(u) = if(true, Inc, 0) \n Probe(0)
def case_lazy_slot_demand_is_the_ordinary_zero_argument_demand : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Probe" (alg ["u"] [] [] [(.call (.resolve "if") [.boolLiteral true, .resolve "Inc", .num 0])])] [(.call (.resolve "Probe") [.num 0])])
#guard obs case_lazy_slot_demand_is_the_ordinary_zero_argument_demand == "err arity"

-- lazy-slot-demand-covers-every-builtin-value-slot [collection-builtins]: Inc(x) = x + 1 \n Step(s) = s + 1 \n Probe(u) = repeat(Step, 1, Inc) \n Probe(0)
def case_lazy_slot_demand_covers_every_builtin_value_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Step" (alg ["s"] [] [] [(.binary .add (.param "s") (.num 1))]), privateProp "Probe" (alg ["u"] [] [] [(.call (.resolve "repeat") [.resolve "Step", .num 1, .resolve "Inc"])])] [(.call (.resolve "Probe") [.num 0])])
#guard obs case_lazy_slot_demand_covers_every_builtin_value_slot == "err arity"

-- dot-string-receiver-is-a-zero-argument-value-demand [strings]: Inc(x) = x + 1 \n Probe(u) = Inc.string \n Probe(0)
def case_dot_string_receiver_is_a_zero_argument_value_demand : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Probe" (alg ["u"] [] [] [(.dotCall (.resolve "Inc") "string" none)])] [(.call (.resolve "Probe") [.num 0])])
#guard obs case_dot_string_receiver_is_a_zero_argument_value_demand == "err arity"

-- zero-argument-demand-follows-actual-call-arity [variadic-calls]: Only(*xs) = xs \n Only
def case_zero_argument_demand_follows_actual_call_arity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [.resolve "Only"])
#guard obs case_zero_argument_demand_follows_actual_call_arity == "ok raw=L[] n=1"

-- zero-argument-callable-name-is-read-not-lifted [variadic-calls]: Cnt(*xs) = xs.count \n Pair(*xs) = 10, 20 \n Alias = Cnt \n Twice(*items) = Cnt + Cnt \n  \n Cnt + 1, [Cnt], Cnt == Cnt, Pair:1 \n Alias, Alias() \n Twice(1, 2, 3)
def case_zero_argument_callable_name_is_read_not_lifted : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Alias" (.alias none [] [] (.resolve "Cnt")), privateProp "Cnt" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.param "xs") "count" none)]), privateProp "Pair" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 10, .num 20]), privateProp "Twice" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [(.binary .add (.resolve "Cnt") (.resolve "Cnt"))])] [(.binary .add (.resolve "Cnt") (.num 1)), (.listLiteral [.resolve "Cnt"]), (.comparison (.resolve "Cnt") [{ op := .eq, operand := (.resolve "Cnt") }]), (.index (.resolve "Pair") (.num 1)), .resolve "Alias", (.call (.resolve "Alias") []), (.call (.resolve "Twice") [.num 1, .num 2, .num 3])])
#guard obs case_zero_argument_callable_name_is_read_not_lifted == "ok raw=S[1, L[0], true, 20, 0, 0, 0] n=7"

-- same-arity-user-if-keeps-user-identity [name-resolution]: if(a, b, c) = a + b + c \n if(1, 10, 20) \n 1.if(10, 20)
def case_same_arity_user_if_keeps_user_identity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "if" (alg ["a", "b", "c"] [] [] [(.binary .add (.binary .add (.param "a") (.param "b")) (.param "c"))])] [(.call (.resolve "if") [.num 1, .num 10, .num 20]), (.dotCall (.num 1) "if" (some [.num 10, .num 20]))])
#guard obs case_same_arity_user_if_keeps_user_identity == "ok raw=S[31, 31] n=2"

-- parameter-named-if-carries-the-supplied-callable [name-resolution]: Apply(if, x) = { Inner = if(x) \n  Inner } \n Inc(x) = x + 1 \n Apply(Inc, 7)
def case_parameter_named_if_carries_the_supplied_callable : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Apply" (alg ["if", "x"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["if", "x"]) (alg [] [] [] [(.call (.param "if") [.param "x"])])) with requiredOwnerDepths := some [("if", some 0), ("x", some 0)] }] [.resolve "Inner"]), privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "Apply") [.resolve "Inc", .num 7])])
#guard obs case_parameter_named_if_carries_the_supplied_callable == "ok raw=8 n=1"

-- if-spread-builds-values-before-branch-selection [conditionals]: Risky = (10, 1 / 0) \n if(true, Risky*)
def case_if_spread_builds_values_before_branch_selection : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Risky" (alg [] [] [] [(.capture [.num 10, (.binary .div (.num 1) (.num 0))])])] [(.call (.resolve "if") [.boolLiteral true, (.sequenceSpread (.resolve "Risky"))])])
#guard obs case_if_spread_builds_values_before_branch_selection == "err div0"

-- dot-string-intrinsic-rejects-arguments [strings]: A = 42 \n A.string(1)
def case_dot_string_intrinsic_rejects_arguments : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 42])] [(.dotCall (.resolve "A") "string" (some [.num 1]))])
#guard obs case_dot_string_intrinsic_rejects_arguments == "err arity"

-- ownership-open-provided-captured-member-read-by-sibling-is-local-only [access-boundaries]: Outer(p) = { \n     open Lib \n     Lib = { public X = p } \n     public Y = X \n     Y \n } \n Outer.Y
def case_ownership_open_provided_captured_member_read_by_sibling_is_local_only : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["p"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [.param "p"])) with requiredOwnerDepths := some [("p", some 1)] }] []), { (publicLocalProp "Y" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [.resolve "X"])) with requiredOwnerDepths := some [("p", some 0)] }] [.resolve "Y"])] [(.dotCall (.resolve "Outer") "Y" none)])
#guard obs case_ownership_open_provided_captured_member_read_by_sibling_is_local_only == "err localOnlyProperty"

-- ownership-open-head-between-opener-and-settling-level-charges-the-capture [access-boundaries]: Outer(p) = { \n     Mid = { \n         Lib = { public X = p } \n         Inner = { \n             open Lib \n             X \n         } \n         Inner \n     } \n     Mid \n } \n Outer.Mid
def case_ownership_open_head_between_opener_and_settling_level_charges_the_capture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["p"] [] [{ (privateLocalProp "Mid" (.localCapturedAncestorParams ["p"]) (alg [] [] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [.param "p"])) with requiredOwnerDepths := some [("p", some 2)] }] []), { (privateLocalProp "Inner" (.localCapturedAncestorParams ["p"]) (alg [] [.resolve "Lib"] [] [.resolve "X"])) with requiredOwnerDepths := some [("p", some 1)] }] [.resolve "Inner"])) with requiredOwnerDepths := some [("p", some 0)] }] [.resolve "Mid"])] [(.dotCall (.resolve "Outer") "Mid" none)])
#guard obs case_ownership_open_head_between_opener_and_settling_level_charges_the_capture == "err localOnlyProperty"

-- grace-in-redundant-group-is-grace-on-the-name [name-resolution]: V(x) = x * 2 \n F = b + (~a).V \n F(5, 1)
def case_grace_in_redundant_group_is_grace_on_the_name : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [(.binary .add (.param "b") (.dotCall (.param "a") "V" none))]), privateProp "V" (alg ["x"] [] [] [(.binary .mul (.param "x") (.num 2))])] [(.call (.resolve "F") [.num 5, .num 1])])
#guard obs case_grace_in_redundant_group_is_grace_on_the_name == "ok raw=11 n=1"

-- 320 canonical Lean-guarded specification cases.

/--
Machine-checked Lean-guarded partition count: the id list is built by the
same loop that emits the guards above, while the expected total is computed
independently from the corpus partition, so a generation bug fails `lake build`.
-/
def specCaseIds : List String := [
  "need-closed-core-demand-is-runtime",
  "need-unused-ordinary-argument",
  "need-unused-collector-slice",
  "need-forwarding-preserves-unused-cell",
  "need-collector-forwarding-preserves-unused-slice",
  "need-ordinary-conditional-selects-one-cell",
  "need-family-shares-failed-attempt-value",
  "need-first-loop-step-can-ignore-initial",
  "need-closed-demand-can-remain-unused",
  "need-wrong-arity-precedes-cell-demand",
  "need-explicit-spread-precedes-arity",
  "need-collector-demand-materializes-whole-slice",
  "need-callable-projection-does-not-force-value",
  "need-demand-order-decides-the-first-failure",
  "need-wrapper-keeps-builtin-if-selection",
  "need-container-call-checks-cardinality-first",
  "need-collection-builtin-demands-its-collection-first",
  "collected-callable-survives-explicit-respread",
  "first-program",
  "boolean-values-and-equality",
  "boolean-predicates-and-patterns",
  "boolean-loop-state-transition",
  "boolean-predicate-rejects-visible-empty",
  "power-unary-precedence",
  "not-binds-below-comparisons",
  "comparison-chains-compare-adjacent-pairs",
  "comparison-chain-boolean-and-arithmetic-operands",
  "comparison-chain-is-eager-after-false",
  "integer-division-truncates",
  "integer-division-exact-quotient",
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
  "capture-supply",
  "capture-supply-spread",
  "call-reentry-identity",
  "call-value-boundary",
  "loop-result-is-one-value",
  "loop-step-patterns-only-bind",
  "loop-nested-step-row-is-one-slot",
  "loop-step-clause-family",
  "loop-step-family-while",
  "loop-step-family-multi-slot",
  "loop-step-builtin-is-one-row-wrapper",
  "loop-step-builtin-empty-result-is-one-slot",
  "loop-step-alias-follows-target",
  "loop-step-value-is-rejected",
  "loop-step-zero-iterations-never-projects",
  "loop-step-family-no-match-is-ordinary",
  "loop-step-lazy-builtin-roles",
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
  "decon-rhs-implicit-parameter",
  "decon-rhs-brace-scope",
  "decon-rhs-lifted-parameter-order",
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
  "dot-receiver-passes-a-value",
  "values-stay-values",
  "callback-element-is-one-argument",
  "parentheses-group-syntax",
  "mixed-collecting-parameter",
  "mixed-front-back-family",
  "collecting-minimum-arity",
  "variadic-grouped-vs-spread",
  "variadic-nested-not-flattened",
  "supply-vs-value-patterns",
  "list-patterns-cover-every-cardinality",
  "nested-structural-patterns-keep-their-kind",
  "structural-patterns-open-only-their-own-kind",
  "binding-failure-outranks-repeated-name-conflict",
  "repeated-name-binding-is-order-independent",
  "repeated-name-is-a-constraint-not-a-merge",
  "repeated-equal-values-require-one-callable-identity",
  "implicit-forwarding-is-by-binding-name",
  "formula-lifting-is-one-law-for-every-callable",
  "formula-lifting-follows-the-consumers-role",
  "repeated-name-wrapper-keeps-independent-arguments",
  "implicit-forwarding-preserves-structural-kind",
  "alias-forwarding-and-explicit-call",
  "alias-structural-forwarding-and-written-call",
  "alias-preserves-the-callee-signature",
  "alias-of-a-builtin-is-the-builtin",
  "alias-of-a-clause-family-dispatches-as-the-family",
  "alias-arguments-take-the-targets-roles",
  "alias-is-the-targets-callable",
  "alias-declares-only-its-own-members",
  "bare-forwarding-keeps-each-parameter-kind",
  "written-call-infers-its-written-names",
  "repeated-callable-success-preserves-both-channels",
  "repeated-genuine-aliases-preserve-complete-binding",
  "repeated-callable-identity-includes-captured-activation",
  "repeated-dot-results-have-distinct-wrapper-identities",
  "repeated-forwarded-dot-wrapper-keeps-identity",
  "collecting-pattern-list-merges-after-the-collector",
  "redundant-call-parens-canonical",
  "call-spread-into-conditional-clauses",
  "patterned-user-call-is-one-value-boundary",
  "conditional-one-element-list-pattern",
  "conditional-sequence-pattern-matches-sequence-values-only",
  "empty-structural-patterns-are-distinct-heads",
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
  "open-local-only-through-capture-row",
  "open-self-contained-beside-same-named-sibling",
  "zero-param-block-higher-order",
  "dot-member-higher-order-parameter",
  "dot-member-fallback-implicit-signature",
  "grace-dot-higher-order-implicit",
  "grace-dot-keeps-structural-precedence",
  "dot-member-fallback-in-closed-parameter-list",
  "dot-fallback-on-known-receiver-stays-valid",
  "dot-string-declared-member-wins",
  "dot-string-intrinsic-on-structural-miss",
  "grouped-structural-callee-is-the-member",
  "grouped-zero-arg-member-call-is-fresh",
  "computed-dot-callee-is-not-callable",
  "closed-list-may-fallback-name-is-runtime",
  "open-local-only-member-inside-owner",
  "dot-local-only-member-outside-owner",
  "open-two-spellings-one-provider",
  "ambiguous-open-unused-overlap-is-valid",
  "dot-chain-structural-member-beats-extension",
  "dot-chain-extension-fallback-composes",
  "dot-chain-nested-structural-members",
  "dot-chain-local-only-member-is-not-a-fallback",
  "capture-suppresses-higher-order-identity",
  "capture-suppresses-structural-members",
  "output-dotted-access-ordinary",
  "dot-call-structural-member-is-not-a-lexical-rewrite",
  "visibility-private-member-is-structural-not-exported",
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
  "clause-family-multirow-callback-rejected",
  "clause-family-multirow-reduce-step-rejected",
  "clause-family-callback-single-value-accepted",
  "callback-variadic-collects",
  "callback-mixed-variadic-rows",
  "callback-nested-pattern-binds-like-call",
  "forwarded-callable-keeps-its-algorithm-channel",
  "builtin-call-assembly-respects-argument-roles",
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
  "index-selects-one-value",
  "selection-forms-agree",
  "index-nested-stays-intact",
  "index-empty-item-visible",
  "index-out-of-range",
  "index-captured-requality",
  "output-rows-interleave-definitions",
  "trailing-comma-continues-line",
  "star-before-operand-row-is-multiplication",
  "star-before-declaration-or-boundary-is-spread",
  "line-final-star-in-definition-continues",
  "grace-in-branch-nested-block-belongs-to-the-block",
  "grace-saturation-is-valid",
  "grace-weights-accumulate",
  "grace-front-first-movement",
  "grace-prefix-marker-led-row",
  "adjacency-call-across-space",
  "multiline-call-open-delimiter",
  "newline-ends-property-body",
  "comment-does-not-change-parse",
  "spread-binds-before-list",
  "dot-chain-continuation",
  "arity-too-many-arguments",
  "missing-output-not-a-value",
  "missing-output-as-builtin-arg",
  "output-less-argument-is-not-an-omitted-argument",
  "argument-value-outcome-is-final",
  "scalar-op-rejects-sequence",
  "empty-sequence-is-not-an-operator-identity",
  "order-rejects-non-numeric",
  "division-by-zero",
  "invoking-slot-without-callable-is-not-an-algorithm",
  "zero-parameter-callable-in-invoking-slot-is-arity",
  "kind-errors-are-type-mismatch",
  "first-last-empty-is-bad-index",
  "aggregate-empty-is-domain-error",
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
  "list-written-slot-reifies-selection",
  "list-empty-spread-neutral",
  "list-call-boundary",
  "list-lone-deconstruction",
  "list-deconstruction-not-recursive",
  "collecting-binding-exact-list",
  "list-lone-collecting-assignment",
  "list-builtin-collection",
  "callable-argument-parameter-shadowing",
  "value-argument-parameter-shadowing",
  "value-parameter-shadowing-through-nested-scope",
  "value-binder-parameter-shadowing",
  "ancestor-callable-visible-without-same-named-parameter",
  "forwarded-parameter-leaves-an-opened-reference",
  "forwarding-reuses-a-captured-ancestor-parameter",
  "forwarding-never-supplies-a-property-an-open-or-a-builtin",
  "forwarding-reused-binding-kind-preserves-values",
  "ownership-captured-parameter-beats-outer-property",
  "ownership-nearest-enclosing-parameter-wins",
  "ownership-parameter-beats-prelude-alias",
  "ownership-parameter-beats-opened-name",
  "clause-family-nested-in-branch-body-binds-its-own-binders",
  "conditional-branch-pattern-is-a-closed-input-specification",
  "conditional-branch-inline-open-exposes-members-to-the-branch",
  "conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches",
  "conditional-branch-local-library-is-openable-within-the-branch",
  "builtin-callable-is-an-ordinary-prelude-binding",
  "no-arity-based-callable-selection",
  "if-composition-forms-agree",
  "if-arity-is-uniform-across-spellings",
  "if-laziness-follows-the-resolved-identity",
  "lazy-slot-demand-is-the-ordinary-zero-argument-demand",
  "lazy-slot-demand-covers-every-builtin-value-slot",
  "dot-string-receiver-is-a-zero-argument-value-demand",
  "zero-argument-demand-follows-actual-call-arity",
  "zero-argument-callable-name-is-read-not-lifted",
  "same-arity-user-if-keeps-user-identity",
  "parameter-named-if-carries-the-supplied-callable",
  "if-spread-builds-values-before-branch-selection",
  "dot-string-intrinsic-rejects-arguments",
  "ownership-open-provided-captured-member-read-by-sibling-is-local-only",
  "ownership-open-head-between-opener-and-settling-level-charges-the-capture",
  "grace-in-redundant-group-is-grace-on-the-name"
]
#guard specCaseIds.length == 320

end LanguageSpecCases
