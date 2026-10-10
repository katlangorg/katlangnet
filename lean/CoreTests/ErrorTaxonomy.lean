import KatLang
import CoreTests.Common

namespace KatLangTests.ErrorTaxonomy
open KatLang

/-! # The evaluation-error taxonomy (Q-06 + Q-27, decided 2026-10-05)

An evaluation error names the FIRST semantic contract the executed operation
cannot satisfy, in that operation's ordinary evaluation order:

* missing CALLABLE capability in an invoking position (a user higher-order
  parameter, a builtin callback, a `repeat`/`while` step, an invoking slot of a
  builtin used as a step) is `notAnAlgorithm` — decided by CALLABLE projection
  only when the slot is about to be invoked, never by demanding its VALUE, and
  never for an unused slot;
* a present VALUE of the wrong kind is `typeMismatch`;
* supply/output cardinality — a callable or binder that cannot accept the
  supplied structure, an operation that receives the wrong number of emitted
  slots, NEED-04's unequal repeated VALUE contributions — is `arityMismatch` /
  `badArity`;
* a selection that names no position is `badIndex` — `first`/`last` on an
  empty collection included, since they ARE selections (SEQ-04);
* a zero divisor is `divByZero`, every other valid-kind domain failure (a
  negative `repeat` count, `min`/`max`/`avg` of an empty collection, ...) is
  `illegalInEval`;
* a callable keeps every ordinary binder verdict: a zero-parameter callable
  invoked with an item is `arityMismatch`, a structural pattern of the other
  kind `typeMismatch`, NEED-04's incompatible callable identities `typeMismatch`.

One guard per clause, on the innermost constructor (and the `arityMismatch`
payload). Each program is the elaborated AST of a written source (the derived
encoding the generated corpora use), run as the derived-corpus runner runs it.
C#: `ErrorTaxonomyPolicyTests` (six routes). -/

partial def fine : Error -> String
  | .withContext _ inner => fine inner
  | .arityMismatch e a => s!"arityMismatch({e},{a})"
  | .badArity => "badArity"
  | .typeMismatch _ => "typeMismatch"
  | .badIndex => "badIndex"
  | .notAnAlgorithm _ => "notAnAlgorithm"
  | .divByZero => "divByZero"
  | .illegalInEval _ => "illegalInEval"
  | .noMatchingBranch _ => "noMatchingBranch"
  | _ => "other"

/-- The derived-corpus runner (as in the generated `LanguageSpecCases`/`SemanticExplorerCases`
    headers): declaration identification, the explicit-parameter output invariant, root wiring. -/
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

def obsFine (e : Expr) : String :=
  match runCountedM e |>.run EvalState.empty with
  | .ok ((_, n), _) => s!"ok n={n}"
  | .error err => s!"err {fine err}"

def case_guard_callability__map_number : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), .num 5])])
#guard obsFine case_guard_callability__map_number == "err notAnAlgorithm"

def case_guard_callability__map_division : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), (.binary .div (.num 1) (.num 0))])])
#guard obsFine case_guard_callability__map_division == "err notAnAlgorithm"

def case_guard_callability__filter_boolean : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "filter") [(.listLiteral [.num 1]), .boolLiteral true])])
#guard obsFine case_guard_callability__filter_boolean == "err notAnAlgorithm"

def case_guard_callability__reduce_number : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "reduce") [(.listLiteral [.num 1, .num 2]), .num 5, .num 0])])
#guard obsFine case_guard_callability__reduce_number == "err notAnAlgorithm"

def case_guard_callability__fused_filter_count : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "filter") [(.listLiteral [.num 1, .num 2]), .num 5])])])
#guard obsFine case_guard_callability__fused_filter_count == "err notAnAlgorithm"

def case_guard_callability__forwarded : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Through" (alg ["xs", "f"] [] [] [(.call (.resolve "map") [.param "xs", .param "f"])])] [(.call (.resolve "Through") [(.listLiteral [.num 1]), (.binary .div (.num 1) (.num 0))])])
#guard obsFine case_guard_callability__forwarded == "err notAnAlgorithm"

def case_guard_callability__repeat_number : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.num 5, .num 1, .num 0])])
#guard obsFine case_guard_callability__repeat_number == "err notAnAlgorithm"

def case_guard_callability__while_boolean : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "while") [.boolLiteral true, .num 0])])
#guard obsFine case_guard_callability__while_boolean == "err notAnAlgorithm"

def case_guard_callability__builtin_step_callback : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.resolve "map", .num 1, (.listLiteral [.num 1, .num 2]), .num 5])])
#guard obsFine case_guard_callability__builtin_step_callback == "err notAnAlgorithm"

def case_guard_callability__user_hof : Expr :=
  .algorithmExpr (alg [] [] [privateProp "App" (alg ["f", "x"] [] [] [(.call (.param "f") [.param "x"])])] [(.call (.resolve "App") [(.binary .div (.num 1) (.num 0)), .num 1])])
#guard obsFine case_guard_callability__user_hof == "err notAnAlgorithm"

def case_guard_zero_parameter__property_in_map : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 7])] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), .resolve "A"])])
#guard obsFine case_guard_zero_parameter__property_in_map == "err arityMismatch(0,1)"

def case_guard_zero_parameter__block_in_map : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), (.algorithmExpr (alg [] [] [] [.num 5]))])])
#guard obsFine case_guard_zero_parameter__block_in_map == "err arityMismatch(0,1)"

def case_guard_zero_parameter__property_step : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Z" (alg [] [] [] [.num 5])] [(.call (.resolve "repeat") [.resolve "Z", .num 1, .num 0])])
#guard obsFine case_guard_zero_parameter__property_step == "err arityMismatch(0,1)"

def case_guard_zero_parameter__user_hof_property : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 7]), privateProp "App" (alg ["f", "x"] [] [] [(.call (.param "f") [.param "x"])])] [(.call (.resolve "App") [.resolve "A", .num 1])])
#guard obsFine case_guard_zero_parameter__user_hof_property == "err arityMismatch(0,1)"

def case_guard_kind__unary_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.emptySequence 0))])
#guard obsFine case_guard_kind__unary_empty == "err typeMismatch"

def case_guard_kind__unary_pair : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.capture [.num 1, .num 2]))])
#guard obsFine case_guard_kind__unary_pair == "err typeMismatch"

def case_guard_kind__unary_list : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.listLiteral [.num 1]))])
#guard obsFine case_guard_kind__unary_list == "err typeMismatch"

def case_guard_kind__selector_list : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2])] [(.index (.resolve "A") (.listLiteral [.num 0]))])
#guard obsFine case_guard_kind__selector_list == "err typeMismatch"

def case_guard_kind__selector_empty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2])] [(.index (.resolve "A") (.emptySequence 0))])
#guard obsFine case_guard_kind__selector_empty == "err typeMismatch"

def case_guard_kind__range_list : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "range") [(.listLiteral [.num 1]), .num 3])])
#guard obsFine case_guard_kind__range_list == "err typeMismatch"

def case_guard_kind__repeat_count_list : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [(.algorithmExpr (alg ["x"] [] [] [.param "x"])), (.listLiteral [.num 1]), .num 0])])
#guard obsFine case_guard_kind__repeat_count_list == "err typeMismatch"

def case_guard_kind__sum_boolean : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "sum") [(.capture [.num 1, .boolLiteral true])])])
#guard obsFine case_guard_kind__sum_boolean == "err typeMismatch"

def case_guard_kind__order_list_item : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 3, (.listLiteral [.num 1])])])])
#guard obsFine case_guard_kind__order_list_item == "err typeMismatch"

def case_guard_kind__sum_scalar_string : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "sum") [.stringLiteral "a"])])
#guard obsFine case_guard_kind__sum_scalar_string == "err typeMismatch"

def case_guard_kind__take_string : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .stringLiteral "x"])])
#guard obsFine case_guard_kind__take_string == "err typeMismatch"

def case_guard_kind__skip_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.num 1, .num 2]), (.emptySequence 0)])])
#guard obsFine case_guard_kind__skip_empty == "err typeMismatch"

def case_guard_domain__first_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.emptySequence 0)])])
#guard obsFine case_guard_domain__first_empty == "err badIndex"

def case_guard_domain__last_empty_list : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "last") [(.listLiteral [])])])
#guard obsFine case_guard_domain__last_empty_list == "err badIndex"

def case_guard_domain__dot_first_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.emptySequence 0) "first" none)])
#guard obsFine case_guard_domain__dot_first_empty == "err badIndex"

def case_guard_domain__min_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.emptySequence 0)])])
#guard obsFine case_guard_domain__min_empty == "err illegalInEval"

def case_guard_domain__avg_empty_list : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "avg") [(.listLiteral [])])])
#guard obsFine case_guard_domain__avg_empty_list == "err illegalInEval"

def case_guard_domain__index_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.emptySequence 0) (.num 0))])
#guard obsFine case_guard_domain__index_empty == "err badIndex"

def case_guard_domain__repeat_negative : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [(.algorithmExpr (alg ["x"] [] [] [.param "x"])), (.unary .minus (.num 1)), .num 0])])
#guard obsFine case_guard_domain__repeat_negative == "err illegalInEval"

def case_guard_cardinality__user_call : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Add" (alg ["x", "y"] [] [] [(.binary .add (.param "x") (.param "y"))])] [(.call (.resolve "Add") [(.capture [.num 1, .num 2])])])
#guard obsFine case_guard_cardinality__user_call == "err arityMismatch(2,1)"

def case_guard_cardinality__builtin_call : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.num 1]), (.listLiteral [.num 2])])])
#guard obsFine case_guard_cardinality__builtin_call == "err arityMismatch(1,2)"

def case_guard_cardinality__loop_state : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a", "b"] [] [] [.param "a", .param "b"])] [(.call (.resolve "repeat") [.resolve "S", .num 1, .num 1])])
#guard obsFine case_guard_cardinality__loop_state == "err arityMismatch(2,1)"

def case_guard_cardinality__pattern_length : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])] [(.call (.resolve "P") [(.capture [.num 1, .num 2, .num 3])])])
#guard obsFine case_guard_cardinality__pattern_length == "err arityMismatch(2,3)"

-- HO-03 (Q-25 resolved, Option B, October 2026): a map transform's two rows are its ordinary call
-- result, one sequence value — no longer a callback-result cardinality failure.
def case_callback_result__map_result_rows_are_one_value : Expr :=
  .algorithmExpr (alg [] [] [privateProp "D" (alg ["x"] [] [] [.param "x", .param "x"])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "D"])])
#guard obsFine case_callback_result__map_result_rows_are_one_value == "ok n=1"

def case_guard_cardinality__while_no_slot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "W" (alg ["x"] [] [] [(.sequenceSpread (.param "x"))])] [(.call (.resolve "while") [.resolve "W", (.emptySequence 0)])])
#guard obsFine case_guard_cardinality__while_no_slot == "err badArity"

def case_guard_cardinality__repeated_values : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Same" (alg ["x", "x"] [] [] [.param "x"])] [(.call (.resolve "Same") [.num 4, .num 5])])
#guard obsFine case_guard_cardinality__repeated_values == "err badArity"

def case_guard_cardinality__repeated_identities : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 5]), privateProp "B" (alg [] [] [] [.num 5]), privateProp "P" (alg ["f", "f"] [] [] [.param "f"])] [(.call (.resolve "P") [.resolve "A", .resolve "B"])])
#guard obsFine case_guard_cardinality__repeated_identities == "err typeMismatch"

def case_guard_cardinality__pattern_kind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [.param "a"])] [(.call (.resolve "P") [.num 5])])
#guard obsFine case_guard_cardinality__pattern_kind == "err typeMismatch"

-- An invoking slot that is never invoked is neither projected nor validated:
-- `map([], 5)`, `reduce([], 5, 7)` and `repeat(5, 0, 1)` succeed.
def case_guard_unused__map_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "map") [(.listLiteral []), .num 5])])
#guard obsFine case_guard_unused__map_empty == "ok n=1"

def case_guard_unused__reduce_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "reduce") [(.listLiteral []), .num 5, .num 7])])
#guard obsFine case_guard_unused__reduce_empty == "ok n=1"

def case_guard_unused__repeat_zero : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "repeat") [.num 5, .num 0, .num 1])])
#guard obsFine case_guard_unused__repeat_zero == "ok n=1"

end KatLangTests.ErrorTaxonomy
