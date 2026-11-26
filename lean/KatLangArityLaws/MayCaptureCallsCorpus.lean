import KatLangArityLaws.MayCaptureCalls
import LanguageSpecCases
import SemanticExplorerCases
import CoreTests.SemanticGeneratedCases
import CoreTests.HostParentDifferential
import CoreTests.ModuleDifferential
import CoreTests.PlannedLoopTempFamily

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

Lean's program gate against C#'s gate of invocation-plan retention (ledger E-21).

C# retains invocation plans only in a run whose admitted program may capture calls
(J7, `AstStructuralPreflight.MayCaptureCalls`, decided by the admission walk
`CheckAdmittedProgram`). `Expr.mayCaptureCalls` (`MayCaptureCalls.lean`) is the Lean form of
that gate. Each `#guard` below pins C#'s verdict on one program of a differential corpus
(dotnet/tests/KatLang.Tests/MayCaptureCallsLeanArtifactTests.cs): a failing guard is a program on
which the two gates disagree.

The Lean program of a guard is the definition the corpus's own generated module holds for
the tree C# decided (imported above; no program is re-emitted here), so both verdicts are
of the same elaborated tree. This file depends on no proof.

Partition (machine-checked by the `*.length` guards below; nothing is sampled):
- corpus programs: 4610
- guarded: 4472 (664 may capture calls, 3808 cannot)
- excluded: 138
  language-spec: 810 programs, 697 guarded (89 may capture calls), 89 excluded: the source does not parse (Lean has no surface parser), 24 excluded: C#-only by the corpus's reviewed reason
  explorer: 2821 programs, 2808 guarded (131 may capture calls), 13 excluded: the source does not parse (Lean has no surface parser)
  explorer-internal: 19 programs, 19 guarded (0 may capture calls)
  generated: 744 programs, 735 guarded (365 may capture calls), 9 excluded: invalid front-end programs (Lean has no surface front end)
  host-parent: 170 programs, 170 guarded (43 may capture calls)
  modules: 10 programs, 7 guarded (0 may capture calls), 3 excluded: C#-only by the corpus's reviewed reason
  planned-loop-temps: 36 programs, 36 guarded (36 may capture calls)

Exclusion rules that currently exclude nothing: a tree the structural preflight refuses (no
run admits it); a tree that holds a deferred module region (C#'s first clause; Lean has no
deferred region); a hand-authored Lean program.

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_MAY_CAPTURE_CALLS = "1"
  dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter MayCaptureCallsLeanArtifact
-/

namespace KatLang.MayCaptureCallsCorpus
open KatLang

/-! ## language-spec -/

#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_selected_signature_payload == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_variadic_minimum_payload == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_closed_core_demand_is_runtime == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_unused_ordinary_argument == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_unused_collector_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_forwarding_preserves_unused_cell == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_collector_forwarding_preserves_unused_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_ordinary_conditional_selects_one_cell == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_family_shares_failed_attempt_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_first_loop_step_can_ignore_initial == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_closed_demand_can_remain_unused == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_wrong_arity_precedes_cell_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_explicit_spread_precedes_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_collector_demand_materializes_whole_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_callable_projection_does_not_force_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_demand_order_decides_the_first_failure == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_wrapper_keeps_builtin_if_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_container_call_checks_cardinality_first == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_collection_builtin_demands_its_collection_first == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_dot_receiver_is_a_supplied_computation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_dot_receiver_follows_callee_demand_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_family_binder_keeps_the_callable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_need_deconstruction_runs_on_first_target_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_alias_keeps_known_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_alias_keeps_callable_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_alias_demand_raises_the_element_failure == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_carrier_spread_is_arbitrary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_reference_argument_keeps_known_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_reference_argument_is_one_argument == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_reference_argument_keeps_callable_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_reference_argument_arity_precedes_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_reference_argument_carrier_stays_arbitrary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_count_reads_positions == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_selection_demands_selected_positions == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_first_selects_one_element == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_take_demands_its_prefix == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_take_needs_the_prefix_element == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_effects_follow_first_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_reads_through_a_transparent_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_whole_value_stays_eager == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_written_list_stays_eager == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_carrier_stays_eager == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_member_path_keeps_known_slice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_member_path_keeps_callable_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_member_path_demand_raises_the_element_failure == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collector_member_nontransparent_spread_is_arbitrary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collected_callable_survives_explicit_respread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_first_program == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_boolean_values_and_equality == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_boolean_predicates_and_patterns == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_boolean_loop_state_transition == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_boolean_predicate_rejects_visible_empty == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_logical_and_or_short_circuit == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_logical_short_circuit_skips_effects == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_logical_left_operand_is_judged_first == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_power_unary_precedence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_not_binds_below_comparisons == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_comparison_chains_compare_adjacent_pairs == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_comparison_chain_boolean_and_arithmetic_operands == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_comparison_chain_is_eager_after_false == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_integer_division_truncates == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_integer_division_exact_quotient == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_property_access_and_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_is_ordinary_property == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_literal == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_wrapped == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_wrapped_twice == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_singleton_paren == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_singleton_paren_deep == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_eq_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_capture == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_supply_three_rows == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_value_three_items == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_capture_supply == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_capture_supply_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_reentry_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_value_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_result_is_one_value == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_patterns_only_bind == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_nested_step_row_is_one_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_clause_family == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_family_while == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_while_condition_first_skips_transition == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_while_condition_first_trailing_empty_spread == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_while_condition_first_row_granular == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_family_multi_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_builtin_is_one_row_wrapper == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_builtin_empty_result_is_one_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_alias_follows_target == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_value_is_rejected == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_zero_iterations_never_projects == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_family_no_match_is_ordinary == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_lazy_builtin_roles == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_step_builtin_argument_blame == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_plain_and_dot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_no_implicit_provenance == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_zero_state == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_spread_before_count == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_qualified_step == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_exact_arity == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_loop_meta_forwarding == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_property_value_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_capture_count == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_spread_fixed_point == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_spread_singleton_opens == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_scalar_spread_neutral == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_select_spread_vs_capture_select == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_fixed_call_preserves_boundaries == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_fills_remaining_slots == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_count_one_arg == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_count_two_args == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_fixed_empty_arg_visible == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_fixed_empty_spread_zero_items == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_empty_arg_vs_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_empty_in_sequence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_visible_in_sequence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_visible_at_root == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_pair == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_rhs_implicit_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_rhs_brace_scope == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_rhs_lifted_parameter_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_collecting_tail == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_collecting_head == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_collecting_middle == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_empty_collecting == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_arity_under == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_arity_over == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_unpacks_stored_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_tutorial_full == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_lone_collecting == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_grouped_and_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_siblings_preserved == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_capture_collects_list == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_forwarding_list_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_implicit_forwarding_source_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_receiver_distinction == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_receiver_passes_a_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_values_stay_values == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_element_is_one_argument == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_parentheses_group_syntax == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_mixed_collecting_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_mixed_front_back_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collecting_minimum_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_grouped_vs_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_nested_not_flattened == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_supply_vs_value_patterns == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_patterns_cover_every_cardinality == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_nested_structural_patterns_keep_their_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_structural_patterns_open_only_their_own_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_binding_failure_outranks_repeated_name_conflict == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_name_binding_is_order_independent == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_name_is_a_constraint_not_a_merge == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_equal_values_require_one_callable_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarding_single_collector_by_shape == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_implicit_forwarding_is_by_binding_name == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_formula_lifting_is_one_law_for_every_callable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_formula_lifting_follows_the_consumers_role == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_root_row_block_head_is_elaborated == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_name_wrapper_keeps_independent_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_implicit_forwarding_preserves_structural_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_forwarding_and_explicit_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_structural_forwarding_and_written_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_preserves_the_callee_signature == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inline_alias_value_demand_is_the_target_contract == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inline_formula_block_keeps_unresolved_implicit_params == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_of_a_builtin_is_the_builtin == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_of_a_clause_family_dispatches_as_the_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_arguments_take_the_targets_roles == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_alias_is_the_targets_callable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_members_are_the_targets_carrier_members_its_own == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_and_carrier_transport_the_whole_definition == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_name_matches_definitions_by_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_through_a_reference_opens_the_target == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_member_path_alias_is_a_member_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_bare_forwarding_keeps_each_parameter_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_written_call_infers_its_written_names == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_callable_success_preserves_both_channels == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_genuine_aliases_preserve_complete_binding == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_callable_identity_includes_captured_activation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_dot_results_have_distinct_wrapper_identities == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_repeated_forwarded_dot_wrapper_keeps_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collecting_pattern_list_merges_after_the_collector == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_redundant_call_parens_canonical == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_spread_into_conditional_clauses == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_patterned_user_call_is_one_value_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_one_element_list_pattern == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_sequence_pattern_matches_sequence_values_only == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_structural_patterns_are_distinct_heads == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_clause_head_rejects_extra_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_spread_dispatches_before_clause_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_spread_into_patterned_callee == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_wrapped_pair_collapses == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_pair_of_pairs_preserved == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_pair_then_empty_preserved == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_splices_into_sequence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_empty_between_siblings == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_root_spread_beside_slot == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_root_spread_then_value_slot == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_slots_capture == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_one_level_only == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_access_value_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_local_only_through_capture_row == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_self_contained_beside_same_named_sibling == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_zero_param_block_higher_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_member_higher_order_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_member_fallback_implicit_signature == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_dot_higher_order_implicit == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_dot_keeps_structural_precedence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_member_fallback_in_closed_parameter_list == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_fallback_on_known_receiver_stays_valid == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_string_declared_member_wins == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_string_intrinsic_on_structural_miss == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grouped_structural_callee_is_the_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grouped_zero_arg_member_call_is_fresh == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_computed_dot_callee_is_not_callable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_closed_list_may_fallback_name_is_runtime == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_local_only_member_inside_owner == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_local_only_member_read_by_inferring_sibling == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_local_only_member_outside_owner == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_local_only_reference_target_walk == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_local_only_inline_block_head == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_local_only_through_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_local_only_enclosing_level == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_block_headed_reference_keeps_requirement == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_impossible_read_in_untaken_branch_charges_nothing == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_reference_checked_where_it_is_opened == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_exported_inline_block_head_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_exported_value_only_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_exported_runtime_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_path_fallback_edges_charge_their_callee == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_path_fallback_edges_inline_block_head == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_deconstruction_source_inline_block_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_two_spellings_one_provider == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ambiguous_open_unused_overlap_is_valid == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_chain_structural_member_beats_extension == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_chain_extension_fallback_composes == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_chain_nested_structural_members == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_chain_local_only_member_is_not_a_fallback == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_capture_suppresses_higher_order_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_capture_suppresses_structural_members == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_dotted_access_ordinary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_call_structural_member_is_not_a_lexical_rewrite == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_visibility_private_member_is_structural_not_exported == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_property_call_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_builtin_result_reentry == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_zero_arg_access_of_parametrized == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_take_prefix == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_take_single_survivor == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_take_zero_empty == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_skip_prefix == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_filter_keeps_matching == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_filter_single_survivor == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_filter_none_empty == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_map_transforms_items == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_map_single_item == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_map_pair_callback == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_clause_family_multirow_callback_is_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_clause_family_multirow_reduce_step_is_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_clause_family_callback_single_value_accepted == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_result_is_the_ordinary_call_result == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_selection_reads_only_the_selected_position == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_map_runs_its_mapper_only_for_the_positions_read == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_filter_discovers_only_the_matches_it_needs == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_positions_are_shared_and_follow_demand_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_run_output_is_read_after_it_is_assembled == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_take_validates_its_count_before_any_position == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_pattern_checks_cardinality_before_its_fields == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_equality_reads_both_operands_whole == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_list_holding_itself_is_a_demand_cycle_when_read_whole == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_accumulators_are_evaluated_on_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_demands_only_the_steps_it_needs == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_effects_follow_accumulator_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_empty_collection_demands_initial_once == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_map_reads_each_source_position_before_its_transform == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_expanded_map_calls_may_skip_indexed_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_map_identity_preserves_empty_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_accumulator_may_be_empty == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_variadic_collects == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_mixed_variadic_rows == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_nested_pattern_binds_like_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarded_callable_keeps_its_algorithm_channel == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_builtin_call_assembly_respects_argument_roles == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_distinct_preserves_first == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_distinct_structural_pairs == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_take_family_tutorial == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_distinct_family_tutorial == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_one_level_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_distinct_empties_collapse == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_order_sorts_atoms == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_range_inclusive == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_range_single_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_arguments_keep_written_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_recursive_flatten == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_exact_list_result == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_list_traversal == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_mixed_traversal == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_list_composition == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_atoms_no_truthiness == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_sum_of_range_collection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_count_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_count_scalar_and_string == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_count_dotcount_agree == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_if_value_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_builtin_fixed_collection_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_accumulates_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reduce_empty_initial_is_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_eq_structural_nested == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_selects_atom == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_selects_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selection_forms_agree == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_nested_stays_intact == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_empty_item_visible == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_out_of_range == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_several_values == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_keeps_empty_values == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_spread_forms_before_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_shares_the_positional_view == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_bracket_on_a_later_line_is_a_list == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_variadic_selection_has_no_callable_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_negative_index_selects_no_position == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_index_captured_requality == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_rows_interleave_definitions == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_trailing_comma_continues_line == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_star_before_operand_row_is_multiplication == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_star_before_declaration_or_boundary_is_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_line_final_star_in_definition_continues == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_in_branch_nested_block_belongs_to_the_block == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_saturation_is_valid == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_weights_accumulate == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_front_first_movement == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_prefix_marker_led_row == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_adjacency_call_across_space == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_multiline_call_open_delimiter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_newline_grammar_priority_continuation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_line_final_star_attached_at_eof_is_spread == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_newline_ends_property_body == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_comment_does_not_change_parse == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_binds_before_list == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_chain_continuation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_arity_too_many_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_missing_output_not_a_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_preserves_nested_missing_output == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_missing_output_as_builtin_arg == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_less_argument_is_not_an_omitted_argument == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_argument_value_outcome_is_final == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_scalar_op_rejects_sequence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_empty_sequence_is_not_an_operator_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_order_rejects_non_numeric == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_division_by_zero == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_invoking_slot_without_callable_is_not_an_algorithm == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_zero_parameter_callable_in_invoking_slot_is_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_kind_errors_are_type_mismatch == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_first_last_empty_is_bad_index == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_aggregate_empty_is_domain_error == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_spread_arguments_fail_left_to_right == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_unresolved_implicit_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_string_equality_exact == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_string_displays_unquoted == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_literal == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_exactness == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_vs_sequence_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_index_selects_element == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_index_nested_element_stays_exact == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_index_out_of_range == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_index_builtin_results == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_redundant_parens_canonicalize == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_spread_capture == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_spread_edges == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_literal_spread_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_elements_preserve_boundaries == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_written_slot_reifies_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_empty_spread_neutral == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_call_boundary == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_lone_deconstruction == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_deconstruction_not_recursive == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_collecting_binding_exact_list == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_lone_collecting_assignment == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_list_builtin_collection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callable_argument_parameter_shadowing == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_value_argument_parameter_shadowing == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_value_parameter_shadowing_through_nested_scope == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_value_binder_parameter_shadowing == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ancestor_callable_visible_without_same_named_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarded_parameter_leaves_an_opened_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarding_reuses_a_captured_ancestor_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarding_never_supplies_a_property_an_open_or_a_builtin == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_forwarding_reused_binding_kind_preserves_values == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_captured_parameter_beats_outer_property == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_nearest_enclosing_parameter_wins == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_parameter_beats_prelude_alias == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_parameter_beats_opened_name == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_clause_family_nested_in_branch_body_binds_its_own_binders == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_branch_pattern_is_a_closed_input_specification == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_branch_inline_open_exposes_members_to_the_branch == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_branch_inline_open_does_not_shadow_an_enclosing_open_in_sibling_branches == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_conditional_branch_local_library_is_openable_within_the_branch == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_builtin_callable_is_an_ordinary_prelude_binding == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_no_arity_based_callable_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_if_composition_forms_agree == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_if_arity_is_uniform_across_spellings == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_if_laziness_follows_the_resolved_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_slot_demand_is_the_ordinary_zero_argument_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_lazy_slot_demand_covers_every_builtin_value_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_string_receiver_is_a_zero_argument_value_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_string_parameter_receiver_reports_the_written_argument == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_zero_argument_demand_follows_actual_call_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_zero_argument_callable_name_is_read_not_lifted == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_same_arity_user_if_keeps_user_identity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_parameter_named_if_carries_the_supplied_callable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_if_spread_builds_values_before_branch_selection == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_dot_string_intrinsic_rejects_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_open_provided_captured_member_read_by_sibling_is_local_only == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_ownership_open_head_between_opener_and_settling_level_charges_the_capture == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grace_in_redundant_group_is_grace_on_the_name == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_string_single_quoted_text_is_raw == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_string_literal_pattern_selects_a_clause == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_string_and_number_stay_separate_items == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_meta_capture_invokes_the_original_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_meta_capture_sees_through_forwarding_and_value == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_meta_refuses_anything_but_a_written_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_invoke_needs_its_argument_list == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_invoke_is_not_an_extension_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_reference_never_leaves_its_run == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_reference_arguments_view == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_arguments_spread_forwards_the_original_arguments == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_arguments_view_is_not_a_collection == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_arguments_is_not_an_extension_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_reference_algorithm_projection == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_call_reference_algorithm_loops == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_algorithm_is_not_an_extension_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_algorithm_projection_cycle == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_of_a_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_of_a_projection == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_of_a_parameter_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_transport_reads_the_target_members == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_namespace_of_its_own_declarations == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_failure_is_not_absence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cycle == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cell_read_and_path_share_one_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cell_explicit_call_is_fresh == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cell_fresh_in_every_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cell_unused_sibling_changes_nothing == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_cell_read_from_outside_after_a_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inner_property_lifetime_every_call_is_fresh == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inner_property_lifetime_inside_and_outside_a_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inner_property_lifetime_explicit_call_from_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_inner_property_lifetime_alias_in_every_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_runtime_alias_self_link_is_a_demand_cycle == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_head_resolves_in_its_own_scope == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_receiver_is_its_target_structure == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_block_headed_reference_navigates_its_block == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_behind_a_carrier_that_reads_it_back == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_through_a_carrier_reads_the_carriers_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_same_shape_references_are_distinct_bindings == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_algorithm_member_of_a_reference_behind_a_carrier == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_carrier_of_a_parameter_in_every_activation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_cycle_through_an_open_is_no_alias == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_sibling_cycle_member_path_is_read_statically == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_block_member_reference_opens_its_target == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_block_receiver_reference_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_cycle_only_the_final_providers_close_is_no_alias == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_member_path_through_a_lower_cyclic_receiver_is_no_alias == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_reference_head_is_the_parameter_its_own_scope_binds == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_counts_executions_in_the_run == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_property_is_cached_call_is_fresh == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_argument_is_one_lazy_computation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_callable_reference_is_not_an_execution == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_meta_replay_is_fresh == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_bare_value_requires_invocation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_argument_is_an_arity_error == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_tick_is_an_ordinary_shadowable_binding == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grouped_runtime_member_value_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_grouped_runtime_member_value_arity == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_reference_private_member_provides_public_names == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_runtime_link_provides_its_own_namespace == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_open_of_a_link_over_a_cyclic_head_compiles_in_every_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_receiver_expansion_return_through_a_reference == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_receiver_expansion_return_through_a_reference_link == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_receiver_expansion_return_through_a_self_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_receiver_expansion_consumed_members_are_no_return == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_marked_call_spreads_its_rows == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_argument_and_element_slots == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_alias_inherits_the_marker == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_value_positions_keep_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_builtin_argument_is_spread_too == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_not_through_a_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_lifted_call_spreads == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_loop_step_through_a_wrapper == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_marked_call_as_loop_receiver == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_zero_parameter_only_explicit_calls == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_argument_runs_at_formation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_opens_one_level == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_receiver_edge_is_the_lowered_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_lifted_call_ends_known_positions == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_output_spread_reference_certainly_read == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dot_path_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dot_path_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dot_path_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dot_path_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dotted_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dotted_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dotted_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_dotted_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_open_of_reference_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_open_of_reference_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_open_of_reference_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_open_of_reference_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_enclosing_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_enclosing_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_enclosing_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_member_enclosing_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dot_path_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dot_path_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dot_path_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dot_path_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dotted_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dotted_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dotted_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_dotted_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_open_of_reference_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_open_of_reference_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_open_of_reference_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_open_of_reference_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_enclosing_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_enclosing_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_enclosing_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_reference_enclosing_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dot_path_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dot_path_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dot_path_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dot_path_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dotted_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dotted_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dotted_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_dotted_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dot_path_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dot_path_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dot_path_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dot_path_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dotted_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_dotted_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_row_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_row_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_enclosing_open_member_capture_inside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_exposure_shape_inline_head_enclosing_open_member_capture_outside == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_inline_block_head_per_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_opened_member_read_per_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_carrier_of_dependent_property_per_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_deconstruction_target_per_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_lifted_formula_uses_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_bare_forwarding_clause_uses_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_inline_open_target_lifted_with_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_self_contained_property_fresh_in_every_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_dependent_property_evaluated_per_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_call_reference_property_per_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_exposure_member_mixes_exported_and_dependent == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_carrier_call_fresh_bare_read_target == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_deconstruction_call_establishes_target_entry == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_collecting_only_owner_read_and_calls == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_collecting_only_owner_exported_member == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_collecting_owner_dependent_member_refused_at_root == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_declared_algorithm_member_grouped_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_alias_of_member_path_shares_member_entry == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_carrier_own_member_and_forwarded_read == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_explicit_call_establishes_inner_reads_cached == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_reentrant_explicit_call_inside_owner == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_carrier_call_uses_declaring_activation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_explicit_owner_call_binds_fresh_activation == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_explicit_call_owns_empty_key == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_deconstruction_in_loop_step_per_round == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_alias_of_collecting_owner == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_cache_carrier_forwards_supplied_calls_fresh == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_exported == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_local == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_per_loop_round == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_callback_invocation_establishes_no_cache_entry == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_spread_formed_before_ordinary_cells == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_collector_selection_demands_one_cell_once == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_repeated_name_value_contribution_anchors == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_family_shares_one_supply_across_clauses == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_unused_fixed_argument_never_runs == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_need_callback_argument_evaluated_once == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_while_false_round_forms_no_earlier_rows == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_while_empty_trailing_spread_passed_over == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_while_single_item_state_and_flag == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_repeat_prepares_supply_before_count == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_repeat_zero_never_projects_step == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_repeat_step_without_callable == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_builtin_step_result_is_one_row == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_carrier_step_forwards == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_nested_loop_is_one_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_meta_parameter_cannot_forward_step == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_bare_member_path_is_no_step == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_local_step_temporary_per_round == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_step_temporary_read_then_call == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_exported_temporary_call_is_fresh == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_step_structural_head_binds_state == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_step_collecting_head_collects_state == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_loop_step_repeated_name_must_agree == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_invalid_position_stops_before_later_selector == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_selectors_demanded_left_to_right == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_negative_index_is_bad_index == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_boolean_selector_is_type == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_first_selector_failure_wins == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_selection_scalar_boolean_selects_itself == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_capture_is_inert == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_invoke_reuses_sticky_supply == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_arguments_count_demands_nothing == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_arguments_selection_validates_before_reading == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_extension_route_receiver_first == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_intrinsic_route_refuses_invocation == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_arguments_and_invoke_share_cells == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_member_route_invoke_is_fresh == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_sticky_supply_self_demand_cycle == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_arguments_count_inside_own_argument == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_invoke_body_fresh_arguments_sticky == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_algorithm_call_takes_fresh_supply == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_cycle_settles_as_one_signature == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_cycle_declaration_order_unobservable == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_mutual_recursion_settles == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_recursive_formula_settles == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_postfix_moves_ysx == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_three_postfix_markers == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_three_prefix_markers == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_mixed_markers == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_group_pattern_first_occurrence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_group_pattern_second_occurrence == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_group_of_one_binder_is_the_binder == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_list_group_keeps_kind == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_shared_collector_name_is_one_binding == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_new_parameter_beside_property_read == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_dot_call_order_receiver_member_arguments == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_on_dot_receiver == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_clause_family_plain_binder_slot == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_through_alias_chain == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_if_branch_lifts_whether_selected == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_lifting_list_element_value_role == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_marked_family == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_bare_read_is_one_value == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_zero_supply_call_spreads == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_if_slot_no_exemption == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_selector_slot == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_step_row_spreads == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_unmarked_step_row_is_one_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_marked_step_call_is_two_arguments == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_through_transparent_alias == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_not_through_carrier == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_member_path_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_empty_rows_supply_nothing == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_nested_marked_calls == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_repeat_count_slot == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_output_spread_extension_receiver == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_carried_container_reads_the_current_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_static_owner_above_activation_refused == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_container_written_in_other_call_refused == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_root_alias_of_container == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_container_through_call_reference == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_open_member_and_carried_container == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_anchoring_recursive_owner_innermost_call == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_open_owner_walk_before_opens == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_open_prelude_before_opens == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_open_nested_levels_inner_first == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_open_overlap_without_use_is_legal == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_builtin_reduce_demands_initial_on_empty == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_builtin_filter_count_predicate_per_item == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_meta_family_redispatch_on_new_supply == true
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_family_repeated_name_identity_nonmatch == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_family_empty_and_pair_sequence_patterns == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_comparison_chain_operands_once == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_logical_xor_operands_both_evaluated == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_builtin_map_callbacks_run_in_collection_order == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_closed_bare_row_uses_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_closed_bare_row_uses_own_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_closed_formula_reuses_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_branch_formula_reuses_enclosing_parameter == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_closed_list_without_source_is_a_demand == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_collector_to_collector_respreads == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_fixed_binding_passed_whole == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_collecting_only_callee_is_read == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_grace_block_inside_closed_branch == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_builtin_parameter_by_name == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_enclosing_bindings_at_two_levels == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_nearest_parameter_binding_wins == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_hunt_forwarding_property_is_never_a_source == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_take_zero_demands_no_element == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_selective_collector_take_count_error_precedes_elements == false
#guard Expr.mayCaptureCalls LanguageSpecCases.case_decon_target_calls_reuse_the_shared_source == false

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def languageSpecPrograms : List Expr := [
  LanguageSpecCases.case_need_selected_signature_payload,
  LanguageSpecCases.case_need_variadic_minimum_payload,
  LanguageSpecCases.case_need_closed_core_demand_is_runtime,
  LanguageSpecCases.case_need_unused_ordinary_argument,
  LanguageSpecCases.case_need_unused_collector_slice,
  LanguageSpecCases.case_need_forwarding_preserves_unused_cell,
  LanguageSpecCases.case_need_collector_forwarding_preserves_unused_slice,
  LanguageSpecCases.case_need_ordinary_conditional_selects_one_cell,
  LanguageSpecCases.case_need_family_shares_failed_attempt_value,
  LanguageSpecCases.case_need_first_loop_step_can_ignore_initial,
  LanguageSpecCases.case_need_closed_demand_can_remain_unused,
  LanguageSpecCases.case_need_wrong_arity_precedes_cell_demand,
  LanguageSpecCases.case_need_explicit_spread_precedes_arity,
  LanguageSpecCases.case_need_collector_demand_materializes_whole_slice,
  LanguageSpecCases.case_need_callable_projection_does_not_force_value,
  LanguageSpecCases.case_need_demand_order_decides_the_first_failure,
  LanguageSpecCases.case_need_wrapper_keeps_builtin_if_selection,
  LanguageSpecCases.case_need_container_call_checks_cardinality_first,
  LanguageSpecCases.case_need_collection_builtin_demands_its_collection_first,
  LanguageSpecCases.case_need_dot_receiver_is_a_supplied_computation,
  LanguageSpecCases.case_need_dot_receiver_follows_callee_demand_order,
  LanguageSpecCases.case_need_family_binder_keeps_the_callable,
  LanguageSpecCases.case_need_deconstruction_runs_on_first_target_demand,
  LanguageSpecCases.case_collector_alias_keeps_known_slice,
  LanguageSpecCases.case_collector_alias_keeps_callable_elements,
  LanguageSpecCases.case_collector_alias_demand_raises_the_element_failure,
  LanguageSpecCases.case_collector_carrier_spread_is_arbitrary,
  LanguageSpecCases.case_collector_reference_argument_keeps_known_slice,
  LanguageSpecCases.case_collector_reference_argument_is_one_argument,
  LanguageSpecCases.case_collector_reference_argument_keeps_callable_elements,
  LanguageSpecCases.case_collector_reference_argument_arity_precedes_elements,
  LanguageSpecCases.case_collector_reference_argument_carrier_stays_arbitrary,
  LanguageSpecCases.case_selective_collector_count_reads_positions,
  LanguageSpecCases.case_selective_collector_selection_demands_selected_positions,
  LanguageSpecCases.case_selective_collector_first_selects_one_element,
  LanguageSpecCases.case_selective_collector_take_demands_its_prefix,
  LanguageSpecCases.case_selective_collector_take_needs_the_prefix_element,
  LanguageSpecCases.case_selective_collector_effects_follow_first_demand,
  LanguageSpecCases.case_selective_collector_reads_through_a_transparent_reference,
  LanguageSpecCases.case_selective_collector_whole_value_stays_eager,
  LanguageSpecCases.case_selective_collector_written_list_stays_eager,
  LanguageSpecCases.case_selective_collector_carrier_stays_eager,
  LanguageSpecCases.case_collector_member_path_keeps_known_slice,
  LanguageSpecCases.case_collector_member_path_keeps_callable_elements,
  LanguageSpecCases.case_collector_member_path_demand_raises_the_element_failure,
  LanguageSpecCases.case_collector_member_nontransparent_spread_is_arbitrary,
  LanguageSpecCases.case_collected_callable_survives_explicit_respread,
  LanguageSpecCases.case_first_program,
  LanguageSpecCases.case_boolean_values_and_equality,
  LanguageSpecCases.case_boolean_predicates_and_patterns,
  LanguageSpecCases.case_boolean_loop_state_transition,
  LanguageSpecCases.case_boolean_predicate_rejects_visible_empty,
  LanguageSpecCases.case_logical_and_or_short_circuit,
  LanguageSpecCases.case_logical_short_circuit_skips_effects,
  LanguageSpecCases.case_logical_left_operand_is_judged_first,
  LanguageSpecCases.case_power_unary_precedence,
  LanguageSpecCases.case_not_binds_below_comparisons,
  LanguageSpecCases.case_comparison_chains_compare_adjacent_pairs,
  LanguageSpecCases.case_comparison_chain_boolean_and_arithmetic_operands,
  LanguageSpecCases.case_comparison_chain_is_eager_after_false,
  LanguageSpecCases.case_integer_division_truncates,
  LanguageSpecCases.case_integer_division_exact_quotient,
  LanguageSpecCases.case_property_access_and_call,
  LanguageSpecCases.case_output_is_ordinary_property,
  LanguageSpecCases.case_empty_literal,
  LanguageSpecCases.case_empty_wrapped,
  LanguageSpecCases.case_empty_wrapped_twice,
  LanguageSpecCases.case_singleton_paren,
  LanguageSpecCases.case_singleton_paren_deep,
  LanguageSpecCases.case_empty_eq_family,
  LanguageSpecCases.case_empty_capture,
  LanguageSpecCases.case_supply_three_rows,
  LanguageSpecCases.case_value_three_items,
  LanguageSpecCases.case_capture_supply,
  LanguageSpecCases.case_capture_supply_spread,
  LanguageSpecCases.case_call_reentry_identity,
  LanguageSpecCases.case_call_value_boundary,
  LanguageSpecCases.case_loop_result_is_one_value,
  LanguageSpecCases.case_loop_step_patterns_only_bind,
  LanguageSpecCases.case_loop_nested_step_row_is_one_slot,
  LanguageSpecCases.case_loop_step_clause_family,
  LanguageSpecCases.case_loop_step_family_while,
  LanguageSpecCases.case_loop_while_condition_first_skips_transition,
  LanguageSpecCases.case_loop_while_condition_first_trailing_empty_spread,
  LanguageSpecCases.case_loop_while_condition_first_row_granular,
  LanguageSpecCases.case_loop_step_family_multi_slot,
  LanguageSpecCases.case_loop_step_builtin_is_one_row_wrapper,
  LanguageSpecCases.case_loop_step_builtin_empty_result_is_one_slot,
  LanguageSpecCases.case_loop_step_alias_follows_target,
  LanguageSpecCases.case_loop_step_value_is_rejected,
  LanguageSpecCases.case_loop_step_zero_iterations_never_projects,
  LanguageSpecCases.case_loop_step_family_no_match_is_ordinary,
  LanguageSpecCases.case_loop_step_lazy_builtin_roles,
  LanguageSpecCases.case_loop_step_builtin_argument_blame,
  LanguageSpecCases.case_loop_meta_plain_and_dot,
  LanguageSpecCases.case_loop_meta_no_implicit_provenance,
  LanguageSpecCases.case_loop_meta_zero_state,
  LanguageSpecCases.case_loop_meta_spread_before_count,
  LanguageSpecCases.case_loop_meta_qualified_step,
  LanguageSpecCases.case_loop_meta_exact_arity,
  LanguageSpecCases.case_loop_meta_forwarding,
  LanguageSpecCases.case_property_value_boundary,
  LanguageSpecCases.case_spread_capture_count,
  LanguageSpecCases.case_repeated_spread_fixed_point,
  LanguageSpecCases.case_repeated_spread_singleton_opens,
  LanguageSpecCases.case_scalar_spread_neutral,
  LanguageSpecCases.case_select_spread_vs_capture_select,
  LanguageSpecCases.case_fixed_call_preserves_boundaries,
  LanguageSpecCases.case_spread_fills_remaining_slots,
  LanguageSpecCases.case_empty_count_one_arg,
  LanguageSpecCases.case_empty_count_two_args,
  LanguageSpecCases.case_fixed_empty_arg_visible,
  LanguageSpecCases.case_fixed_empty_spread_zero_items,
  LanguageSpecCases.case_variadic_empty_arg_vs_spread,
  LanguageSpecCases.case_spread_empty_in_sequence,
  LanguageSpecCases.case_empty_visible_in_sequence,
  LanguageSpecCases.case_empty_visible_at_root,
  LanguageSpecCases.case_decon_pair,
  LanguageSpecCases.case_decon_rhs_implicit_parameter,
  LanguageSpecCases.case_decon_rhs_brace_scope,
  LanguageSpecCases.case_decon_rhs_lifted_parameter_order,
  LanguageSpecCases.case_decon_collecting_tail,
  LanguageSpecCases.case_decon_collecting_head,
  LanguageSpecCases.case_decon_collecting_middle,
  LanguageSpecCases.case_decon_empty_collecting,
  LanguageSpecCases.case_decon_arity_under,
  LanguageSpecCases.case_decon_arity_over,
  LanguageSpecCases.case_decon_unpacks_stored_value,
  LanguageSpecCases.case_decon_tutorial_full,
  LanguageSpecCases.case_decon_lone_collecting,
  LanguageSpecCases.case_variadic_grouped_and_spread,
  LanguageSpecCases.case_variadic_siblings_preserved,
  LanguageSpecCases.case_variadic_capture_collects_list,
  LanguageSpecCases.case_variadic_forwarding_list_spread,
  LanguageSpecCases.case_implicit_forwarding_source_kind,
  LanguageSpecCases.case_variadic_receiver_distinction,
  LanguageSpecCases.case_dot_receiver_passes_a_value,
  LanguageSpecCases.case_values_stay_values,
  LanguageSpecCases.case_callback_element_is_one_argument,
  LanguageSpecCases.case_parentheses_group_syntax,
  LanguageSpecCases.case_mixed_collecting_parameter,
  LanguageSpecCases.case_mixed_front_back_family,
  LanguageSpecCases.case_collecting_minimum_arity,
  LanguageSpecCases.case_variadic_grouped_vs_spread,
  LanguageSpecCases.case_variadic_nested_not_flattened,
  LanguageSpecCases.case_supply_vs_value_patterns,
  LanguageSpecCases.case_list_patterns_cover_every_cardinality,
  LanguageSpecCases.case_nested_structural_patterns_keep_their_kind,
  LanguageSpecCases.case_structural_patterns_open_only_their_own_kind,
  LanguageSpecCases.case_binding_failure_outranks_repeated_name_conflict,
  LanguageSpecCases.case_repeated_name_binding_is_order_independent,
  LanguageSpecCases.case_repeated_name_is_a_constraint_not_a_merge,
  LanguageSpecCases.case_repeated_equal_values_require_one_callable_identity,
  LanguageSpecCases.case_forwarding_single_collector_by_shape,
  LanguageSpecCases.case_implicit_forwarding_is_by_binding_name,
  LanguageSpecCases.case_formula_lifting_is_one_law_for_every_callable,
  LanguageSpecCases.case_formula_lifting_follows_the_consumers_role,
  LanguageSpecCases.case_root_row_block_head_is_elaborated,
  LanguageSpecCases.case_repeated_name_wrapper_keeps_independent_arguments,
  LanguageSpecCases.case_implicit_forwarding_preserves_structural_kind,
  LanguageSpecCases.case_alias_forwarding_and_explicit_call,
  LanguageSpecCases.case_alias_structural_forwarding_and_written_call,
  LanguageSpecCases.case_alias_preserves_the_callee_signature,
  LanguageSpecCases.case_inline_alias_value_demand_is_the_target_contract,
  LanguageSpecCases.case_inline_formula_block_keeps_unresolved_implicit_params,
  LanguageSpecCases.case_alias_of_a_builtin_is_the_builtin,
  LanguageSpecCases.case_alias_of_a_clause_family_dispatches_as_the_family,
  LanguageSpecCases.case_alias_arguments_take_the_targets_roles,
  LanguageSpecCases.case_alias_is_the_targets_callable,
  LanguageSpecCases.case_reference_members_are_the_targets_carrier_members_its_own,
  LanguageSpecCases.case_reference_and_carrier_transport_the_whole_definition,
  LanguageSpecCases.case_repeated_name_matches_definitions_by_identity,
  LanguageSpecCases.case_open_through_a_reference_opens_the_target,
  LanguageSpecCases.case_member_path_alias_is_a_member_reference,
  LanguageSpecCases.case_bare_forwarding_keeps_each_parameter_kind,
  LanguageSpecCases.case_written_call_infers_its_written_names,
  LanguageSpecCases.case_repeated_callable_success_preserves_both_channels,
  LanguageSpecCases.case_repeated_genuine_aliases_preserve_complete_binding,
  LanguageSpecCases.case_repeated_callable_identity_includes_captured_activation,
  LanguageSpecCases.case_repeated_dot_results_have_distinct_wrapper_identities,
  LanguageSpecCases.case_repeated_forwarded_dot_wrapper_keeps_identity,
  LanguageSpecCases.case_collecting_pattern_list_merges_after_the_collector,
  LanguageSpecCases.case_redundant_call_parens_canonical,
  LanguageSpecCases.case_call_spread_into_conditional_clauses,
  LanguageSpecCases.case_patterned_user_call_is_one_value_boundary,
  LanguageSpecCases.case_conditional_one_element_list_pattern,
  LanguageSpecCases.case_conditional_sequence_pattern_matches_sequence_values_only,
  LanguageSpecCases.case_empty_structural_patterns_are_distinct_heads,
  LanguageSpecCases.case_conditional_clause_head_rejects_extra_arguments,
  LanguageSpecCases.case_call_spread_dispatches_before_clause_selection,
  LanguageSpecCases.case_call_spread_into_patterned_callee,
  LanguageSpecCases.case_wrapped_pair_collapses,
  LanguageSpecCases.case_pair_of_pairs_preserved,
  LanguageSpecCases.case_pair_then_empty_preserved,
  LanguageSpecCases.case_spread_splices_into_sequence,
  LanguageSpecCases.case_spread_empty_between_siblings,
  LanguageSpecCases.case_root_spread_beside_slot,
  LanguageSpecCases.case_root_spread_then_value_slot,
  LanguageSpecCases.case_spread_slots_capture,
  LanguageSpecCases.case_spread_one_level_only,
  LanguageSpecCases.case_dot_access_value_boundary,
  LanguageSpecCases.case_open_local_only_through_capture_row,
  LanguageSpecCases.case_open_self_contained_beside_same_named_sibling,
  LanguageSpecCases.case_zero_param_block_higher_order,
  LanguageSpecCases.case_dot_member_higher_order_parameter,
  LanguageSpecCases.case_dot_member_fallback_implicit_signature,
  LanguageSpecCases.case_grace_dot_higher_order_implicit,
  LanguageSpecCases.case_grace_dot_keeps_structural_precedence,
  LanguageSpecCases.case_dot_member_fallback_in_closed_parameter_list,
  LanguageSpecCases.case_dot_fallback_on_known_receiver_stays_valid,
  LanguageSpecCases.case_dot_string_declared_member_wins,
  LanguageSpecCases.case_dot_string_intrinsic_on_structural_miss,
  LanguageSpecCases.case_grouped_structural_callee_is_the_member,
  LanguageSpecCases.case_grouped_zero_arg_member_call_is_fresh,
  LanguageSpecCases.case_computed_dot_callee_is_not_callable,
  LanguageSpecCases.case_closed_list_may_fallback_name_is_runtime,
  LanguageSpecCases.case_open_local_only_member_inside_owner,
  LanguageSpecCases.case_open_local_only_member_read_by_inferring_sibling,
  LanguageSpecCases.case_dot_local_only_member_outside_owner,
  LanguageSpecCases.case_dot_local_only_reference_target_walk,
  LanguageSpecCases.case_dot_local_only_inline_block_head,
  LanguageSpecCases.case_open_local_only_through_reference,
  LanguageSpecCases.case_open_local_only_enclosing_level,
  LanguageSpecCases.case_open_block_headed_reference_keeps_requirement,
  LanguageSpecCases.case_impossible_read_in_untaken_branch_charges_nothing,
  LanguageSpecCases.case_open_reference_checked_where_it_is_opened,
  LanguageSpecCases.case_dot_exported_inline_block_head_member,
  LanguageSpecCases.case_dot_exported_value_only_reference,
  LanguageSpecCases.case_open_exported_runtime_reference,
  LanguageSpecCases.case_dot_path_fallback_edges_charge_their_callee,
  LanguageSpecCases.case_dot_path_fallback_edges_inline_block_head,
  LanguageSpecCases.case_deconstruction_source_inline_block_member,
  LanguageSpecCases.case_open_two_spellings_one_provider,
  LanguageSpecCases.case_ambiguous_open_unused_overlap_is_valid,
  LanguageSpecCases.case_dot_chain_structural_member_beats_extension,
  LanguageSpecCases.case_dot_chain_extension_fallback_composes,
  LanguageSpecCases.case_dot_chain_nested_structural_members,
  LanguageSpecCases.case_dot_chain_local_only_member_is_not_a_fallback,
  LanguageSpecCases.case_capture_suppresses_higher_order_identity,
  LanguageSpecCases.case_capture_suppresses_structural_members,
  LanguageSpecCases.case_output_dotted_access_ordinary,
  LanguageSpecCases.case_dot_call_structural_member_is_not_a_lexical_rewrite,
  LanguageSpecCases.case_visibility_private_member_is_structural_not_exported,
  LanguageSpecCases.case_property_call_boundary,
  LanguageSpecCases.case_builtin_result_reentry,
  LanguageSpecCases.case_zero_arg_access_of_parametrized,
  LanguageSpecCases.case_take_prefix,
  LanguageSpecCases.case_take_single_survivor,
  LanguageSpecCases.case_take_zero_empty,
  LanguageSpecCases.case_skip_prefix,
  LanguageSpecCases.case_filter_keeps_matching,
  LanguageSpecCases.case_filter_single_survivor,
  LanguageSpecCases.case_filter_none_empty,
  LanguageSpecCases.case_map_transforms_items,
  LanguageSpecCases.case_map_single_item,
  LanguageSpecCases.case_map_pair_callback,
  LanguageSpecCases.case_clause_family_multirow_callback_is_one_value,
  LanguageSpecCases.case_clause_family_multirow_reduce_step_is_one_value,
  LanguageSpecCases.case_clause_family_callback_single_value_accepted,
  LanguageSpecCases.case_callback_result_is_the_ordinary_call_result,
  LanguageSpecCases.case_lazy_list_selection_reads_only_the_selected_position,
  LanguageSpecCases.case_lazy_map_runs_its_mapper_only_for_the_positions_read,
  LanguageSpecCases.case_lazy_filter_discovers_only_the_matches_it_needs,
  LanguageSpecCases.case_lazy_list_positions_are_shared_and_follow_demand_order,
  LanguageSpecCases.case_lazy_list_run_output_is_read_after_it_is_assembled,
  LanguageSpecCases.case_lazy_take_validates_its_count_before_any_position,
  LanguageSpecCases.case_lazy_list_pattern_checks_cardinality_before_its_fields,
  LanguageSpecCases.case_lazy_list_equality_reads_both_operands_whole,
  LanguageSpecCases.case_lazy_list_holding_itself_is_a_demand_cycle_when_read_whole,
  LanguageSpecCases.case_reduce_accumulators_are_evaluated_on_demand,
  LanguageSpecCases.case_reduce_demands_only_the_steps_it_needs,
  LanguageSpecCases.case_reduce_effects_follow_accumulator_demand,
  LanguageSpecCases.case_reduce_empty_collection_demands_initial_once,
  LanguageSpecCases.case_map_reads_each_source_position_before_its_transform,
  LanguageSpecCases.case_expanded_map_calls_may_skip_indexed_arguments,
  LanguageSpecCases.case_map_identity_preserves_empty_elements,
  LanguageSpecCases.case_reduce_accumulator_may_be_empty,
  LanguageSpecCases.case_callback_variadic_collects,
  LanguageSpecCases.case_callback_mixed_variadic_rows,
  LanguageSpecCases.case_callback_nested_pattern_binds_like_call,
  LanguageSpecCases.case_forwarded_callable_keeps_its_algorithm_channel,
  LanguageSpecCases.case_builtin_call_assembly_respects_argument_roles,
  LanguageSpecCases.case_distinct_preserves_first,
  LanguageSpecCases.case_distinct_structural_pairs,
  LanguageSpecCases.case_take_family_tutorial,
  LanguageSpecCases.case_distinct_family_tutorial,
  LanguageSpecCases.case_spread_one_level_family,
  LanguageSpecCases.case_distinct_empties_collapse,
  LanguageSpecCases.case_order_sorts_atoms,
  LanguageSpecCases.case_range_inclusive,
  LanguageSpecCases.case_range_single_value,
  LanguageSpecCases.case_spread_arguments_keep_written_order,
  LanguageSpecCases.case_atoms_recursive_flatten,
  LanguageSpecCases.case_atoms_exact_list_result,
  LanguageSpecCases.case_atoms_list_traversal,
  LanguageSpecCases.case_atoms_mixed_traversal,
  LanguageSpecCases.case_atoms_list_composition,
  LanguageSpecCases.case_atoms_no_truthiness,
  LanguageSpecCases.case_sum_of_range_collection,
  LanguageSpecCases.case_count_family,
  LanguageSpecCases.case_count_scalar_and_string,
  LanguageSpecCases.case_count_dotcount_agree,
  LanguageSpecCases.case_if_value_boundary,
  LanguageSpecCases.case_builtin_fixed_collection_arity,
  LanguageSpecCases.case_reduce_accumulates_value,
  LanguageSpecCases.case_reduce_empty_initial_is_one_value,
  LanguageSpecCases.case_eq_structural_nested,
  LanguageSpecCases.case_index_selects_atom,
  LanguageSpecCases.case_index_selects_one_value,
  LanguageSpecCases.case_selection_forms_agree,
  LanguageSpecCases.case_index_nested_stays_intact,
  LanguageSpecCases.case_index_empty_item_visible,
  LanguageSpecCases.case_index_out_of_range,
  LanguageSpecCases.case_variadic_selection_several_values,
  LanguageSpecCases.case_variadic_selection_keeps_empty_values,
  LanguageSpecCases.case_variadic_selection_spread_forms_before_selection,
  LanguageSpecCases.case_variadic_selection_shares_the_positional_view,
  LanguageSpecCases.case_variadic_selection_bracket_on_a_later_line_is_a_list,
  LanguageSpecCases.case_variadic_selection_has_no_callable_identity,
  LanguageSpecCases.case_negative_index_selects_no_position,
  LanguageSpecCases.case_index_captured_requality,
  LanguageSpecCases.case_output_rows_interleave_definitions,
  LanguageSpecCases.case_trailing_comma_continues_line,
  LanguageSpecCases.case_star_before_operand_row_is_multiplication,
  LanguageSpecCases.case_star_before_declaration_or_boundary_is_spread,
  LanguageSpecCases.case_line_final_star_in_definition_continues,
  LanguageSpecCases.case_grace_in_branch_nested_block_belongs_to_the_block,
  LanguageSpecCases.case_grace_saturation_is_valid,
  LanguageSpecCases.case_grace_weights_accumulate,
  LanguageSpecCases.case_grace_front_first_movement,
  LanguageSpecCases.case_grace_prefix_marker_led_row,
  LanguageSpecCases.case_adjacency_call_across_space,
  LanguageSpecCases.case_multiline_call_open_delimiter,
  LanguageSpecCases.case_newline_grammar_priority_continuation,
  LanguageSpecCases.case_line_final_star_attached_at_eof_is_spread,
  LanguageSpecCases.case_newline_ends_property_body,
  LanguageSpecCases.case_comment_does_not_change_parse,
  LanguageSpecCases.case_spread_binds_before_list,
  LanguageSpecCases.case_dot_chain_continuation,
  LanguageSpecCases.case_arity_too_many_arguments,
  LanguageSpecCases.case_missing_output_not_a_value,
  LanguageSpecCases.case_spread_preserves_nested_missing_output,
  LanguageSpecCases.case_missing_output_as_builtin_arg,
  LanguageSpecCases.case_output_less_argument_is_not_an_omitted_argument,
  LanguageSpecCases.case_argument_value_outcome_is_final,
  LanguageSpecCases.case_scalar_op_rejects_sequence,
  LanguageSpecCases.case_empty_sequence_is_not_an_operator_identity,
  LanguageSpecCases.case_order_rejects_non_numeric,
  LanguageSpecCases.case_division_by_zero,
  LanguageSpecCases.case_invoking_slot_without_callable_is_not_an_algorithm,
  LanguageSpecCases.case_zero_parameter_callable_in_invoking_slot_is_arity,
  LanguageSpecCases.case_kind_errors_are_type_mismatch,
  LanguageSpecCases.case_first_last_empty_is_bad_index,
  LanguageSpecCases.case_aggregate_empty_is_domain_error,
  LanguageSpecCases.case_spread_arguments_fail_left_to_right,
  LanguageSpecCases.case_unresolved_implicit_parameter,
  LanguageSpecCases.case_string_equality_exact,
  LanguageSpecCases.case_string_displays_unquoted,
  LanguageSpecCases.case_list_literal,
  LanguageSpecCases.case_list_exactness,
  LanguageSpecCases.case_list_vs_sequence_kind,
  LanguageSpecCases.case_list_index_selects_element,
  LanguageSpecCases.case_list_index_nested_element_stays_exact,
  LanguageSpecCases.case_list_index_out_of_range,
  LanguageSpecCases.case_list_index_builtin_results,
  LanguageSpecCases.case_list_redundant_parens_canonicalize,
  LanguageSpecCases.case_list_spread_capture,
  LanguageSpecCases.case_list_spread_edges,
  LanguageSpecCases.case_list_literal_spread_elements,
  LanguageSpecCases.case_list_elements_preserve_boundaries,
  LanguageSpecCases.case_list_written_slot_reifies_selection,
  LanguageSpecCases.case_list_empty_spread_neutral,
  LanguageSpecCases.case_list_call_boundary,
  LanguageSpecCases.case_list_lone_deconstruction,
  LanguageSpecCases.case_list_deconstruction_not_recursive,
  LanguageSpecCases.case_collecting_binding_exact_list,
  LanguageSpecCases.case_list_lone_collecting_assignment,
  LanguageSpecCases.case_list_builtin_collection,
  LanguageSpecCases.case_callable_argument_parameter_shadowing,
  LanguageSpecCases.case_value_argument_parameter_shadowing,
  LanguageSpecCases.case_value_parameter_shadowing_through_nested_scope,
  LanguageSpecCases.case_value_binder_parameter_shadowing,
  LanguageSpecCases.case_ancestor_callable_visible_without_same_named_parameter,
  LanguageSpecCases.case_forwarded_parameter_leaves_an_opened_reference,
  LanguageSpecCases.case_forwarding_reuses_a_captured_ancestor_parameter,
  LanguageSpecCases.case_forwarding_never_supplies_a_property_an_open_or_a_builtin,
  LanguageSpecCases.case_forwarding_reused_binding_kind_preserves_values,
  LanguageSpecCases.case_ownership_captured_parameter_beats_outer_property,
  LanguageSpecCases.case_ownership_nearest_enclosing_parameter_wins,
  LanguageSpecCases.case_ownership_parameter_beats_prelude_alias,
  LanguageSpecCases.case_ownership_parameter_beats_opened_name,
  LanguageSpecCases.case_clause_family_nested_in_branch_body_binds_its_own_binders,
  LanguageSpecCases.case_conditional_branch_pattern_is_a_closed_input_specification,
  LanguageSpecCases.case_conditional_branch_inline_open_exposes_members_to_the_branch,
  LanguageSpecCases.case_conditional_branch_inline_open_does_not_shadow_an_enclosing_open_in_sibling_branches,
  LanguageSpecCases.case_conditional_branch_local_library_is_openable_within_the_branch,
  LanguageSpecCases.case_builtin_callable_is_an_ordinary_prelude_binding,
  LanguageSpecCases.case_no_arity_based_callable_selection,
  LanguageSpecCases.case_if_composition_forms_agree,
  LanguageSpecCases.case_if_arity_is_uniform_across_spellings,
  LanguageSpecCases.case_if_laziness_follows_the_resolved_identity,
  LanguageSpecCases.case_lazy_slot_demand_is_the_ordinary_zero_argument_demand,
  LanguageSpecCases.case_lazy_slot_demand_covers_every_builtin_value_slot,
  LanguageSpecCases.case_dot_string_receiver_is_a_zero_argument_value_demand,
  LanguageSpecCases.case_dot_string_parameter_receiver_reports_the_written_argument,
  LanguageSpecCases.case_zero_argument_demand_follows_actual_call_arity,
  LanguageSpecCases.case_zero_argument_callable_name_is_read_not_lifted,
  LanguageSpecCases.case_same_arity_user_if_keeps_user_identity,
  LanguageSpecCases.case_parameter_named_if_carries_the_supplied_callable,
  LanguageSpecCases.case_if_spread_builds_values_before_branch_selection,
  LanguageSpecCases.case_dot_string_intrinsic_rejects_arguments,
  LanguageSpecCases.case_ownership_open_provided_captured_member_read_by_sibling_is_local_only,
  LanguageSpecCases.case_ownership_open_head_between_opener_and_settling_level_charges_the_capture,
  LanguageSpecCases.case_grace_in_redundant_group_is_grace_on_the_name,
  LanguageSpecCases.case_string_single_quoted_text_is_raw,
  LanguageSpecCases.case_string_literal_pattern_selects_a_clause,
  LanguageSpecCases.case_string_and_number_stay_separate_items,
  LanguageSpecCases.case_meta_capture_invokes_the_original_call,
  LanguageSpecCases.case_meta_capture_sees_through_forwarding_and_value,
  LanguageSpecCases.case_meta_refuses_anything_but_a_written_call,
  LanguageSpecCases.case_invoke_needs_its_argument_list,
  LanguageSpecCases.case_invoke_is_not_an_extension_call,
  LanguageSpecCases.case_call_reference_never_leaves_its_run,
  LanguageSpecCases.case_call_reference_arguments_view,
  LanguageSpecCases.case_arguments_spread_forwards_the_original_arguments,
  LanguageSpecCases.case_arguments_view_is_not_a_collection,
  LanguageSpecCases.case_arguments_is_not_an_extension_call,
  LanguageSpecCases.case_call_reference_algorithm_projection,
  LanguageSpecCases.case_call_reference_algorithm_loops,
  LanguageSpecCases.case_algorithm_is_not_an_extension_call,
  LanguageSpecCases.case_algorithm_projection_cycle,
  LanguageSpecCases.case_runtime_alias_of_a_parameter,
  LanguageSpecCases.case_runtime_alias_of_a_projection,
  LanguageSpecCases.case_runtime_alias_of_a_parameter_member,
  LanguageSpecCases.case_runtime_alias_transport_reads_the_target_members,
  LanguageSpecCases.case_runtime_alias_namespace_of_its_own_declarations,
  LanguageSpecCases.case_runtime_alias_failure_is_not_absence,
  LanguageSpecCases.case_runtime_alias_cycle,
  LanguageSpecCases.case_runtime_alias_cell_read_and_path_share_one_call,
  LanguageSpecCases.case_runtime_alias_cell_explicit_call_is_fresh,
  LanguageSpecCases.case_runtime_alias_cell_fresh_in_every_call,
  LanguageSpecCases.case_runtime_alias_cell_unused_sibling_changes_nothing,
  LanguageSpecCases.case_runtime_alias_cell_read_from_outside_after_a_call,
  LanguageSpecCases.case_inner_property_lifetime_every_call_is_fresh,
  LanguageSpecCases.case_inner_property_lifetime_inside_and_outside_a_call,
  LanguageSpecCases.case_inner_property_lifetime_explicit_call_from_outside,
  LanguageSpecCases.case_inner_property_lifetime_alias_in_every_call,
  LanguageSpecCases.case_runtime_alias_self_link_is_a_demand_cycle,
  LanguageSpecCases.case_reference_head_resolves_in_its_own_scope,
  LanguageSpecCases.case_reference_receiver_is_its_target_structure,
  LanguageSpecCases.case_block_headed_reference_navigates_its_block,
  LanguageSpecCases.case_reference_behind_a_carrier_that_reads_it_back,
  LanguageSpecCases.case_reference_through_a_carrier_reads_the_carriers_member,
  LanguageSpecCases.case_same_shape_references_are_distinct_bindings,
  LanguageSpecCases.case_algorithm_member_of_a_reference_behind_a_carrier,
  LanguageSpecCases.case_carrier_of_a_parameter_in_every_activation,
  LanguageSpecCases.case_reference_cycle_through_an_open_is_no_alias,
  LanguageSpecCases.case_sibling_cycle_member_path_is_read_statically,
  LanguageSpecCases.case_open_block_member_reference_opens_its_target,
  LanguageSpecCases.case_block_receiver_reference_member,
  LanguageSpecCases.case_reference_cycle_only_the_final_providers_close_is_no_alias,
  LanguageSpecCases.case_member_path_through_a_lower_cyclic_receiver_is_no_alias,
  LanguageSpecCases.case_reference_head_is_the_parameter_its_own_scope_binds,
  LanguageSpecCases.case_tick_counts_executions_in_the_run,
  LanguageSpecCases.case_tick_property_is_cached_call_is_fresh,
  LanguageSpecCases.case_tick_argument_is_one_lazy_computation,
  LanguageSpecCases.case_tick_callable_reference_is_not_an_execution,
  LanguageSpecCases.case_tick_meta_replay_is_fresh,
  LanguageSpecCases.case_tick_bare_value_requires_invocation,
  LanguageSpecCases.case_tick_argument_is_an_arity_error,
  LanguageSpecCases.case_tick_is_an_ordinary_shadowable_binding,
  LanguageSpecCases.case_grouped_runtime_member_value_call,
  LanguageSpecCases.case_grouped_runtime_member_value_arity,
  LanguageSpecCases.case_open_reference_private_member_provides_public_names,
  LanguageSpecCases.case_open_runtime_link_provides_its_own_namespace,
  LanguageSpecCases.case_open_of_a_link_over_a_cyclic_head_compiles_in_every_order,
  LanguageSpecCases.case_receiver_expansion_return_through_a_reference,
  LanguageSpecCases.case_receiver_expansion_return_through_a_reference_link,
  LanguageSpecCases.case_receiver_expansion_return_through_a_self_member,
  LanguageSpecCases.case_receiver_expansion_consumed_members_are_no_return,
  LanguageSpecCases.case_output_spread_marked_call_spreads_its_rows,
  LanguageSpecCases.case_output_spread_argument_and_element_slots,
  LanguageSpecCases.case_output_spread_alias_inherits_the_marker,
  LanguageSpecCases.case_output_spread_value_positions_keep_one_value,
  LanguageSpecCases.case_output_spread_builtin_argument_is_spread_too,
  LanguageSpecCases.case_output_spread_not_through_a_parameter,
  LanguageSpecCases.case_output_spread_lifted_call_spreads,
  LanguageSpecCases.case_output_spread_loop_step_through_a_wrapper,
  LanguageSpecCases.case_output_spread_marked_call_as_loop_receiver,
  LanguageSpecCases.case_output_spread_zero_parameter_only_explicit_calls,
  LanguageSpecCases.case_output_spread_argument_runs_at_formation,
  LanguageSpecCases.case_output_spread_opens_one_level,
  LanguageSpecCases.case_output_spread_receiver_edge_is_the_lowered_call,
  LanguageSpecCases.case_output_spread_lifted_call_ends_known_positions,
  LanguageSpecCases.case_output_spread_reference_certainly_read,
  LanguageSpecCases.case_exposure_shape_member_dot_path_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_dot_path_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_dot_path_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_dot_path_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_dotted_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_dotted_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_dotted_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_dotted_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_open_of_reference_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_open_of_reference_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_open_of_reference_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_open_of_reference_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_enclosing_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_enclosing_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_member_enclosing_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_member_enclosing_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_dot_path_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_dot_path_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_dot_path_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_dot_path_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_dotted_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_dotted_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_dotted_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_dotted_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_open_of_reference_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_open_of_reference_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_open_of_reference_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_open_of_reference_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_enclosing_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_enclosing_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_reference_enclosing_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_reference_enclosing_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_dot_path_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_dot_path_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_dot_path_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_dot_path_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_dotted_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_dotted_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_dotted_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_dotted_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_open_of_reference_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_carrier_enclosing_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_dot_path_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_dot_path_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_dot_path_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_dot_path_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_dotted_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_dotted_open_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_row_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_row_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_open_of_reference_member_capture_outside,
  LanguageSpecCases.case_exposure_shape_inline_head_enclosing_open_member_capture_inside,
  LanguageSpecCases.case_exposure_shape_inline_head_enclosing_open_member_capture_outside,
  LanguageSpecCases.case_hunt_exposure_inline_block_head_per_call,
  LanguageSpecCases.case_hunt_exposure_opened_member_read_per_call,
  LanguageSpecCases.case_hunt_exposure_carrier_of_dependent_property_per_call,
  LanguageSpecCases.case_hunt_exposure_deconstruction_target_per_call,
  LanguageSpecCases.case_hunt_exposure_lifted_formula_uses_enclosing_parameter,
  LanguageSpecCases.case_hunt_exposure_bare_forwarding_clause_uses_enclosing_parameter,
  LanguageSpecCases.case_hunt_exposure_inline_open_target_lifted_with_enclosing_parameter,
  LanguageSpecCases.case_hunt_exposure_self_contained_property_fresh_in_every_call,
  LanguageSpecCases.case_hunt_exposure_dependent_property_evaluated_per_call,
  LanguageSpecCases.case_hunt_exposure_call_reference_property_per_call,
  LanguageSpecCases.case_hunt_exposure_member_mixes_exported_and_dependent,
  LanguageSpecCases.case_hunt_cache_carrier_call_fresh_bare_read_target,
  LanguageSpecCases.case_hunt_cache_deconstruction_call_establishes_target_entry,
  LanguageSpecCases.case_hunt_cache_collecting_only_owner_read_and_calls,
  LanguageSpecCases.case_hunt_cache_collecting_only_owner_exported_member,
  LanguageSpecCases.case_hunt_collecting_owner_dependent_member_refused_at_root,
  LanguageSpecCases.case_hunt_cache_declared_algorithm_member_grouped_call,
  LanguageSpecCases.case_hunt_cache_alias_of_member_path_shares_member_entry,
  LanguageSpecCases.case_hunt_cache_carrier_own_member_and_forwarded_read,
  LanguageSpecCases.case_hunt_cache_explicit_call_establishes_inner_reads_cached,
  LanguageSpecCases.case_hunt_cache_reentrant_explicit_call_inside_owner,
  LanguageSpecCases.case_hunt_cache_carrier_call_uses_declaring_activation,
  LanguageSpecCases.case_hunt_cache_explicit_owner_call_binds_fresh_activation,
  LanguageSpecCases.case_hunt_cache_explicit_call_owns_empty_key,
  LanguageSpecCases.case_hunt_cache_deconstruction_in_loop_step_per_round,
  LanguageSpecCases.case_hunt_cache_alias_of_collecting_owner,
  LanguageSpecCases.case_hunt_cache_carrier_forwards_supplied_calls_fresh,
  LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_exported,
  LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_local,
  LanguageSpecCases.case_hunt_runtime_alias_cell_lifetime_per_loop_round,
  LanguageSpecCases.case_callback_invocation_establishes_no_cache_entry,
  LanguageSpecCases.case_hunt_need_spread_formed_before_ordinary_cells,
  LanguageSpecCases.case_hunt_need_collector_selection_demands_one_cell_once,
  LanguageSpecCases.case_hunt_need_repeated_name_value_contribution_anchors,
  LanguageSpecCases.case_hunt_need_family_shares_one_supply_across_clauses,
  LanguageSpecCases.case_hunt_need_unused_fixed_argument_never_runs,
  LanguageSpecCases.case_hunt_need_callback_argument_evaluated_once,
  LanguageSpecCases.case_hunt_loop_while_false_round_forms_no_earlier_rows,
  LanguageSpecCases.case_hunt_loop_while_empty_trailing_spread_passed_over,
  LanguageSpecCases.case_hunt_loop_while_single_item_state_and_flag,
  LanguageSpecCases.case_hunt_loop_repeat_prepares_supply_before_count,
  LanguageSpecCases.case_hunt_loop_repeat_zero_never_projects_step,
  LanguageSpecCases.case_hunt_loop_repeat_step_without_callable,
  LanguageSpecCases.case_hunt_loop_builtin_step_result_is_one_row,
  LanguageSpecCases.case_hunt_loop_carrier_step_forwards,
  LanguageSpecCases.case_hunt_loop_nested_loop_is_one_slot,
  LanguageSpecCases.case_hunt_loop_meta_parameter_cannot_forward_step,
  LanguageSpecCases.case_hunt_loop_bare_member_path_is_no_step,
  LanguageSpecCases.case_hunt_loop_local_step_temporary_per_round,
  LanguageSpecCases.case_hunt_loop_step_temporary_read_then_call,
  LanguageSpecCases.case_hunt_loop_exported_temporary_call_is_fresh,
  LanguageSpecCases.case_hunt_loop_step_structural_head_binds_state,
  LanguageSpecCases.case_hunt_loop_step_collecting_head_collects_state,
  LanguageSpecCases.case_hunt_loop_step_repeated_name_must_agree,
  LanguageSpecCases.case_hunt_selection_invalid_position_stops_before_later_selector,
  LanguageSpecCases.case_hunt_selection_selectors_demanded_left_to_right,
  LanguageSpecCases.case_hunt_selection_negative_index_is_bad_index,
  LanguageSpecCases.case_hunt_selection_boolean_selector_is_type,
  LanguageSpecCases.case_hunt_selection_first_selector_failure_wins,
  LanguageSpecCases.case_hunt_selection_scalar_boolean_selects_itself,
  LanguageSpecCases.case_hunt_meta_capture_is_inert,
  LanguageSpecCases.case_hunt_meta_invoke_reuses_sticky_supply,
  LanguageSpecCases.case_hunt_meta_arguments_count_demands_nothing,
  LanguageSpecCases.case_hunt_meta_arguments_selection_validates_before_reading,
  LanguageSpecCases.case_hunt_meta_extension_route_receiver_first,
  LanguageSpecCases.case_hunt_meta_intrinsic_route_refuses_invocation,
  LanguageSpecCases.case_hunt_meta_arguments_and_invoke_share_cells,
  LanguageSpecCases.case_hunt_meta_member_route_invoke_is_fresh,
  LanguageSpecCases.case_hunt_meta_sticky_supply_self_demand_cycle,
  LanguageSpecCases.case_hunt_meta_arguments_count_inside_own_argument,
  LanguageSpecCases.case_hunt_meta_invoke_body_fresh_arguments_sticky,
  LanguageSpecCases.case_hunt_meta_algorithm_call_takes_fresh_supply,
  LanguageSpecCases.case_hunt_lifting_cycle_settles_as_one_signature,
  LanguageSpecCases.case_hunt_lifting_cycle_declaration_order_unobservable,
  LanguageSpecCases.case_hunt_lifting_mutual_recursion_settles,
  LanguageSpecCases.case_hunt_lifting_recursive_formula_settles,
  LanguageSpecCases.case_hunt_grace_postfix_moves_ysx,
  LanguageSpecCases.case_hunt_grace_three_postfix_markers,
  LanguageSpecCases.case_hunt_grace_three_prefix_markers,
  LanguageSpecCases.case_hunt_grace_mixed_markers,
  LanguageSpecCases.case_hunt_lifting_group_pattern_first_occurrence,
  LanguageSpecCases.case_hunt_lifting_group_pattern_second_occurrence,
  LanguageSpecCases.case_hunt_lifting_group_of_one_binder_is_the_binder,
  LanguageSpecCases.case_hunt_lifting_list_group_keeps_kind,
  LanguageSpecCases.case_hunt_lifting_shared_collector_name_is_one_binding,
  LanguageSpecCases.case_hunt_forwarding_new_parameter_beside_property_read,
  LanguageSpecCases.case_hunt_lifting_dot_call_order_receiver_member_arguments,
  LanguageSpecCases.case_hunt_grace_on_dot_receiver,
  LanguageSpecCases.case_hunt_lifting_clause_family_plain_binder_slot,
  LanguageSpecCases.case_hunt_lifting_through_alias_chain,
  LanguageSpecCases.case_hunt_lifting_if_branch_lifts_whether_selected,
  LanguageSpecCases.case_hunt_lifting_list_element_value_role,
  LanguageSpecCases.case_hunt_output_spread_marked_family,
  LanguageSpecCases.case_hunt_output_spread_bare_read_is_one_value,
  LanguageSpecCases.case_hunt_output_spread_zero_supply_call_spreads,
  LanguageSpecCases.case_hunt_output_spread_if_slot_no_exemption,
  LanguageSpecCases.case_hunt_output_spread_selector_slot,
  LanguageSpecCases.case_hunt_output_spread_step_row_spreads,
  LanguageSpecCases.case_hunt_output_spread_unmarked_step_row_is_one_slot,
  LanguageSpecCases.case_hunt_output_spread_marked_step_call_is_two_arguments,
  LanguageSpecCases.case_hunt_output_spread_through_transparent_alias,
  LanguageSpecCases.case_hunt_output_spread_not_through_carrier,
  LanguageSpecCases.case_hunt_output_spread_member_path_call,
  LanguageSpecCases.case_hunt_output_spread_empty_rows_supply_nothing,
  LanguageSpecCases.case_hunt_output_spread_nested_marked_calls,
  LanguageSpecCases.case_hunt_output_spread_repeat_count_slot,
  LanguageSpecCases.case_hunt_output_spread_extension_receiver,
  LanguageSpecCases.case_hunt_anchoring_carried_container_reads_the_current_call,
  LanguageSpecCases.case_hunt_anchoring_static_owner_above_activation_refused,
  LanguageSpecCases.case_hunt_anchoring_container_written_in_other_call_refused,
  LanguageSpecCases.case_hunt_anchoring_root_alias_of_container,
  LanguageSpecCases.case_hunt_anchoring_container_through_call_reference,
  LanguageSpecCases.case_hunt_anchoring_open_member_and_carried_container,
  LanguageSpecCases.case_hunt_anchoring_recursive_owner_innermost_call,
  LanguageSpecCases.case_hunt_open_owner_walk_before_opens,
  LanguageSpecCases.case_hunt_open_prelude_before_opens,
  LanguageSpecCases.case_hunt_open_nested_levels_inner_first,
  LanguageSpecCases.case_hunt_open_overlap_without_use_is_legal,
  LanguageSpecCases.case_hunt_builtin_reduce_demands_initial_on_empty,
  LanguageSpecCases.case_hunt_builtin_filter_count_predicate_per_item,
  LanguageSpecCases.case_hunt_meta_family_redispatch_on_new_supply,
  LanguageSpecCases.case_hunt_family_repeated_name_identity_nonmatch,
  LanguageSpecCases.case_hunt_family_empty_and_pair_sequence_patterns,
  LanguageSpecCases.case_hunt_comparison_chain_operands_once,
  LanguageSpecCases.case_hunt_logical_xor_operands_both_evaluated,
  LanguageSpecCases.case_hunt_builtin_map_callbacks_run_in_collection_order,
  LanguageSpecCases.case_hunt_forwarding_closed_bare_row_uses_enclosing_parameter,
  LanguageSpecCases.case_hunt_forwarding_closed_bare_row_uses_own_parameter,
  LanguageSpecCases.case_hunt_forwarding_closed_formula_reuses_enclosing_parameter,
  LanguageSpecCases.case_hunt_forwarding_branch_formula_reuses_enclosing_parameter,
  LanguageSpecCases.case_hunt_forwarding_closed_list_without_source_is_a_demand,
  LanguageSpecCases.case_hunt_forwarding_collector_to_collector_respreads,
  LanguageSpecCases.case_hunt_forwarding_fixed_binding_passed_whole,
  LanguageSpecCases.case_hunt_forwarding_collecting_only_callee_is_read,
  LanguageSpecCases.case_hunt_grace_block_inside_closed_branch,
  LanguageSpecCases.case_hunt_forwarding_builtin_parameter_by_name,
  LanguageSpecCases.case_hunt_forwarding_enclosing_bindings_at_two_levels,
  LanguageSpecCases.case_hunt_forwarding_nearest_parameter_binding_wins,
  LanguageSpecCases.case_hunt_forwarding_property_is_never_a_source,
  LanguageSpecCases.case_selective_collector_take_zero_demands_no_element,
  LanguageSpecCases.case_selective_collector_take_count_error_precedes_elements,
  LanguageSpecCases.case_decon_target_calls_reuse_the_shared_source
]
#guard languageSpecPrograms.length == 697
#guard (languageSpecPrograms.filter Expr.mayCaptureCalls).length == 89

/-! ## explorer -/

#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_root__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_capture__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureCall__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccess__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotAccessCall__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixed__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fixedSpread__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collecting__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingSpread__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingViaProp__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCollectingViaProp__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCollecting__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_fluentSpreadCollecting__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_h__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixed_t__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_t__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mixedBack_z__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_x__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPair_y__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPairSpread_x__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollect_t__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconCollectSpread_t__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_p__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_deconPrefix_z__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapPair__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_seqWrapSolo__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRoot__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadInSeq__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_count__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_countSpread__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_dotCount__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_literalDotCount__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index0__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_index1__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexBig__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_indexNeg__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqSelf__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_neqSelf__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_eqIdentity__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identity__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_identityTwice__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_propChain__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take1__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_take9__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_skip1__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_distinct__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_order__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_mapId__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHead__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternHeadMap__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPair__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_patternPairMap__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHead__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternHeadMap__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPair__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_listPatternPairMap__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_filterKeep__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_atoms__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCapture__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeIdentity__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCount__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_takeCollecting__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_spreadRootStacked__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_collectingStacked__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__n0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__n1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__bt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pbt_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__lbt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__lbt_bf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__lpbt_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p123 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pee == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pe1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p1e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p12_34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pe_12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__ppe1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__ppe == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pp1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__ppp12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__le == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__l7 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__l12_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__lle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__l_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__l_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__p_l12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_captureStacked__pl1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiProp == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropCall == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropDotCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropDot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__dotAccessPublicMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__dotAccessCallPublicMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropIndex0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiPropEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiCollecting == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__multiCollectingCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectingEmptyCall == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectingFwdSum == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectingFwdSpread == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectingJoin == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__range13 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rangeCapture == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rangeCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rangeIndex0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__takeOneSurvivorPair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__takeOneSurvivorPairCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__takeOneSurvivorPairEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__skipToOnePair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__distinctEmpties == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__distinctPairsToOne == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__takeEmpties == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__filterOneSurvivor == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__filterOneSurvivorCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__filterZeroSurvivors == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__mapPairSwap == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__mapPairSwapOk == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__mapPairSwapFlatIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__mapToOne == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderSingle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__atomsNested == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpGreater == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpPlus == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpPlusRight == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpDivRight == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpAnd == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpString == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyOpBoth == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyUnaryMinus == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyUnaryNot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyEqEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyEqNestedEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__emptyNeNestedEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__propBodyEmptySlot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rootEmptySlots == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__seqOfSpreadEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__indexPairInSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__indexEmptyItemRoot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__indexCapturedEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainedListIndex == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listIndexCapturedEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listIndexSelectedKindEqFalse == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderIndex0 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__nestedWrittenArg == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__writtenSlotArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__mixedSingleGrouped == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__sumEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadWithSiblingSeqLiteral == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadEmptyBetween == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rootSpreadExtra == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadOfSpreadSeqLiteral == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__eqSpreadSeqLiteral == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopSpreadHistoryFlat == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifBranchSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__divZero == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__negativeResult == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__strEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainAllTrue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainMixed == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainFalseMiddle == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainFalseLast == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainEqOnly == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainNeAdjacent == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainNeAdjacentFalse == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainEqThenLt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainBoolEqMixed == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainSeqEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainStrEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainParenFirst == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainParenRight == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainParenBoth == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainUnderNot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainUnderAnd == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainArithmeticOperands == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainInvalidLater == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainErrorFirstOperand == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainErrorAfterFalse == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainPropertyOperands == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainCallOperands == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainLtThenEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainLtThenGt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainNeThenLt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainFalseFirstThenEqFalse == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainGroupedNotOperand == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainParenLeftUnderOrdering == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainNegatedBasePower == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainNegatedPowerOperand == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainGroupedNegatedBasePowerOperand == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainArithmeticTiers == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainMiddleOperandError == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__chainGroupedSelectionReceiver == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__strCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__strCapture == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listSpreadOfSeqProp == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listSpreadBetween == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listOfLists == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listSpreadConcat == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listMixedSpread == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listEmptyListSpreadBetween == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listEmptySeqSpreadBetween == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listNeSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listEmptyNeEmptySeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listSingletonNeItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listWrapCanonicalizes == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listSpreadCaptureRoundTrip == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listCollectingNotSequenceKind == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listCollectingCollectsExactList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__implicitForwardOrdinarySource == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__callbackSingleCollectingMap == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__callbackMixedCollectingRow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__callbackMixedCollectingRowPattern == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__callbackCollectingElementIsOneArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectorZeroArgumentCallableFailureIsItsOwn == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listInSeqSpreadKeepsList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listFixedCallBoundary == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listCollectingSpreadCall == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNoOutputBlockRoot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNoOutputBlockList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNoOutputBlockCallArg == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNoOutputResolved == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedDependency == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedDependencyCall == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadOwnInvoked == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedRow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedCapture == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedBuiltinArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedFamilyMatch == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedPatternBinding == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedStringReceiver == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadInnerOwnKept == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadOrdinaryFailureKept == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedSupplySlot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadNestedCallbackSlot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadForwardedOwn == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadForwardedNested == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadCollectorElement == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__spreadForwardedCollectorElement == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__listLoneCollectingAssignment == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minScalar == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minNestedItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__minDot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__maxSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__maxList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__maxEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__maxDot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstScalar == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstListElementStaysExact == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstEmptyItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__firstDot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__lastSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__lastListElementStaysExact == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__lastEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescSeq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescDuplicates == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescScalar == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescEmpty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescString == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__orderDescDot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileCountdown == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileZeroIterations == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileTwoSlotState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileEmptyInitialState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileNonNumericContinuation == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileDot == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopResultIsOneRow == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopResultBesideAnotherRow == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopResultSpreadOpensIt == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopZeroSlotResult == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameStepSpreadRowIsTwoSlots == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameStepDivergingRowsRebindFails == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__structuralStepSpreadRowSuppliesItems == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__structuralStepSpreadRowCannotRebind == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__historyStepSpreadRowEqualsDirectCall == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__nestedLoopStepRowIsOneSlot == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__nestedLoopStepRowSpread == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__callbackBodyLoopIsOneValue == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepClauseFamily == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyWhile == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyMultiSlot == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyRowsAreTheNextState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyNoMatch == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyClauseOrder == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyStructural == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepFamilyRepeatedName == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepBuiltinOneRow == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepBuiltinCollectionNextArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepBuiltinEmptyResultIsTheFlag == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepBuiltinLazyIf == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepAliasOfFamilyAndBuiltin == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepForwardedFamily == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepValueRejected == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepZeroIterationsNeverProject == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaValueRefused == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaPropertyReadRefused == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaPlainAndDot == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaZeroState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaSpreadBeforeCount == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaExactArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaQualifiedCalleeCaptured == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaBareMemberPathRefused == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaRebuiltProjectedStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__metaExtensionReceiverIsSupplied == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopMetaNamedAlias == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__loopStepLoopBuiltinAsStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__containsSequenceItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__containsListItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__containsEmptyItem == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__containsScalarCollection == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__containsAcrossKinds == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openPublicMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openPrivateMemberHidden == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openLocalOnlyCapturedParamsInsideOwner == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openLocalOnlyCapturedParamsOutsideOwner == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openTwoProvidersAmbiguousAtRuntime == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openDuplicateTargetDedup == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openDuplicateDottedTargetDedup == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openTwoSpellingsOneProvider == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openDuplicateInlineBlocksAmbiguousAtRuntime == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openInlineBlock == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openInlineBlockPrivateHidden == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openDottedPath == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openLocalShadowsOpenedName == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openAncestorPropertyWins == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openParentScopeReachesChild == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openNestedDoesNotLeakOutward == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openHeadDefinedLater == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openBuiltinNameCollision == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__structuralDotSeesPrivateMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openPrivateMemberIsNotASecondProvider == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__openLocalOnlyMemberIsASecondProviderAtRuntime == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifSelectedParameterizedBranchIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifSelectedParameterizedFalseBranchIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifParameterizedConditionIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifUnselectedParameterizedBranchStaysLazy == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifZeroParameterBranchIsValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifParameterIgnoringBodyStillArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifCollectingCallableSlotIsCollectedValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifCollectingCallableExplicitCallIsSameValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareCollectingCallableIsAValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareCollectingCallableCountAgreesWithDottedForm == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifRequiredPrefixBesideCollectorIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifRequiredSuffixBesideCollectorIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifNestedCollectingPatternIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__collectingCallableStaysACallbackAlgorithm == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__ifAlgorithmChannelParameterSlotIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatInitialParameterizedSlotIsArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatCountParameterizedSlotIsArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__whileInitialParameterizedSlotIsArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__atomsParameterizedSlotIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__rangeParameterizedSlotIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__dotStringParameterizedReceiverIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__dotStringNavigatedParameterizedMemberIsArity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__reduceParameterIgnoringInitialStillRejected == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatParameterizedStepIsCallback == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingIfBranchLiftsWhileStayingLazy == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingRootValuePositionNeedsTheParameter == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingBuiltinValueSlot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingBuiltinSignature == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingLoopSignature == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingDottedMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingOpenedMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingClauseFamily == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingCaptureElement == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingStringReceiver == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingNestedInUserArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingKeepsCallbacks == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingKeepsUserArguments == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameCallableThenValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameValueThenCallable == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameFailedThenValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameValueThenFailed == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameAcrossCollectorCallable == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameAcrossNestedGroupFailed == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameForwardedCallable == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameDotReceiverFailed == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameValuelessBeforeVerdict == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__repeatedNameAccompanyingChannel == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameAlias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameThreeOccurrences == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameNestedGroup == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameAcrossGroup == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameInsideOneGroup == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameBesideCollector == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameClosedList == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameAcrossCallees == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameFailedArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__forwardByNameCallableArgument == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasKeepsRepeatedSignature == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasKeepsRepeatedConstraint == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasKeepsListPattern == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasKeepsListPatternRejection == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasKeepsBinderlessSignature == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfCollectorKeepsSignature == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasChainKeepsSignature == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfBuiltinCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfIfIsLazy == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfMapDemandsNoCallback == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfRepeatKeepsMinimumArity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasChainOfBuiltin == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfFamilyDispatches == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfFamilyNoMatchingBranch == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasOfUnnameableFamily == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasRolesAreTargetRoles == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasCallableIdentityIsTarget == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__aliasPassedAsCallableNavigatesTarget == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingThroughAlias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__formulaLiftingThroughAlias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingSameName == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingIsNotPositional == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingIgnoresUnusedParameter == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingOfAZeroParameterTarget == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingSamePattern == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingRespreadsItsCollector == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingBranchForwardsItsBinder == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingReusesEnclosingBinding == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__bareForwardingRepeatedName == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__writtenCallInfersWrittenNames == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__writtenCallIgnoresCalleeBinderNames == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0000 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0001 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0002 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0003 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0004 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0005 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0006 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0007 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0008 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0009 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0010 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0011 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0012 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0013 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0014 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0015 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0016 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0017 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0018 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0019 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0020 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0021 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0022 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0023 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenLoopsAG0024 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0000 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0001 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0002 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0003 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0004 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0005 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0006 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0007 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0008 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0009 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0010 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0011 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0012 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0013 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0014 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0015 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0016 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0017 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0018 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFusionAU0019 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0000 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0001 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0002 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0003 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0004 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0005 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0006 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0007 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0008 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0009 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0010 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0011 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0012 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0013 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0014 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0015 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0016 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0017 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0018 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenFaultsAF0019 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0000Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0001Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0002Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0003Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0004Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0005Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0006Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0007Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0008Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0009Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0010Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0011Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0012Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0013Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0014Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0015Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0016Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0017Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0018Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenInferAI0019Base == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0000 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0001 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0002 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0003 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0004 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0005 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0006 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0007 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0008 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0009 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0010 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0011 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0012 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0013 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenEqAQ0014 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0000Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0001Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0002Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0003Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0004Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0005Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0006Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0007Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0008Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpoAX0009Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0000Pair == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0001Pair == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0002Pair == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0003Pair == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0004Pair == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenExpo2AY0005Pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0000 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0001 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0002 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0005 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0006 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0010 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0013 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0015 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0017 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntGenChaosGZ0020 == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E01Direct == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E02Member == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E05Alias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E07RuntimeAliasParam == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E09DeconBoth == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA1Expo1E10ClauseBinder == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N01UndemandedSecond == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N02DemandOrder == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N03AtMostOnce == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N04NeverDemanded == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N05ForwardingNoForce == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need1N06CardinalityFirst == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T01MemberPathTransport == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T02AliasChainTransport == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T03ParamHoldingReference == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T04CountThroughAlias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T05FirstThroughAlias == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA2Need2T06SelectThroughMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C01ReentrantQ37 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C02CollectingAliasOnce == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C03AliasRead == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C04AliasCallEstablishes == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C06CarrierCalls == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache1C07RuntimeMemberValueOnly == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C203FormulaOwnerReadFirst == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C204ExportedOwner == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C205CallbackMemberRead == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C206AliasCellExported == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C207AliasCellLocal == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache2C208AliasCellInLoopStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C301tPropertyTwinExported == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C302tPropertyTwinLocal == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C303AliasCellLoop == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C303tPropertyTwinLoop == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C304tPropertyTwinLocalLoop == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA3Cache3C305AliasCellReadAndCall == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L01WhileBasic == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L08FamilyStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L10AliasStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L13LoopOneValue == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L14ForwardStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA4Loops1L16QualifiedStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA5Select1S03StringCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA5Select1S04EmptyStringSelect == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA5Select1S05StringOnePosition == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA5Select1S06ScalarSelf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA5Select1S07ScalarOut == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P01CollTable == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P02Cnt == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P03CntValue == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P04Withhead == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P05IdPair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA6Spread1P06AddPair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D01ChainFallback == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D02DeclaredString == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D03LexicalStringIgnored == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D04BranchMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D05PrivateStructural == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Dot1D06SpreadReceiver == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H01StatedCarriedContainer == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H05OpenHeadBetween == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H06CarriedViaCallback == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H08CarriedThroughParamChain == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H09ContainerReadAtRoot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA7Anchor1H11ContainerThroughLoopState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA8Alias1X01CarrierForwards == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA8Alias1X02CarrierZeroCall == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA8Alias1X05TransparentMember == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA8Alias1X06CarrierNotTargetIdentity == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M02InvokeFresh == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M05ArgumentsSelect == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M06ArgumentsSelectFail == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M08ArgumentsEmpty == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M09AlgorithmFresh == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta1M10Identity == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M202ArgumentsCycle == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M204MultiSelectView == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M205RebuildCall == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M206SameRefs == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M207SameDifferentRefs == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA9Meta2M208ForwardedReference == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F01CountFormula == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F02IfFormula == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F03RepeatFormula == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F05rMutualLiftReordered == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F07WhileRepeatFormula == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fe1F08BareForwardSameName == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W01ArgSlot == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W01xArgSlotExplicit == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W02List == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W03Group == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W04RootRow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Spread1W04xRootRowExplicit == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fwd1Fw08ForwardCollectorIntoCollector == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fwd1Fw15ForwardingChain == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fwd1Fw18ForwardIf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fwd1Fw19AliasOfMap == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA10Fwd1Fw20ClosedFormulaBuiltin == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA11Cmp1K03TotalEquality == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA11Cmp1K04IfNumber == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA11Cmp1K05TickOnce == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA11Cmp1K06TickEq == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Builtins1B01IfLazy == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Builtins1B02IfCondFail == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Builtins1B04MapTwoRows == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Builtins1B05MapEmptyRow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Builtins1B06FilterNonbool == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G01WhileEmptySpreadOnly == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G02WhileEmptyRow == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G03WhileListFlag == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G04RepeatZeroRowStep == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G05RepeatEmptyState == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Edge2G06FamilyBool == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh01UserFilterCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh02UserFilterBuiltinCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh03BuiltinFilterUserCount == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh04UserCountCallForm == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh05UserRange == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA12Shadow1Sh06UserIfInLoop == true
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R01DivSigns == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R02ExactDiv == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R03Pow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R04ZeroNegPow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R05ModZero == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA13Arith1R06DivZero == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O01SameProviderTwice == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O02SameProviderGrouped == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O03AliasProviderSame == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O05CountShadow == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O06CountUserCallable == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_special__huntA14Open1O09OpenPrivateNotProvided == false

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def explorerPrograms : List Expr := [
  SemanticExplorerCases.case_root__e,
  SemanticExplorerCases.case_root__n0,
  SemanticExplorerCases.case_root__n1,
  SemanticExplorerCases.case_root__bt,
  SemanticExplorerCases.case_root__bf,
  SemanticExplorerCases.case_root__pbt,
  SemanticExplorerCases.case_root__pbt_e,
  SemanticExplorerCases.case_root__pbt_1,
  SemanticExplorerCases.case_root__lbt,
  SemanticExplorerCases.case_root__lbt_bf,
  SemanticExplorerCases.case_root__lpbt_1,
  SemanticExplorerCases.case_root__p1,
  SemanticExplorerCases.case_root__p12,
  SemanticExplorerCases.case_root__p123,
  SemanticExplorerCases.case_root__pee,
  SemanticExplorerCases.case_root__pe1,
  SemanticExplorerCases.case_root__p1e,
  SemanticExplorerCases.case_root__p12_3,
  SemanticExplorerCases.case_root__p12_34,
  SemanticExplorerCases.case_root__pe_12,
  SemanticExplorerCases.case_root__ppe1_2,
  SemanticExplorerCases.case_root__p12_e,
  SemanticExplorerCases.case_root__ppe,
  SemanticExplorerCases.case_root__pp1,
  SemanticExplorerCases.case_root__ppp12,
  SemanticExplorerCases.case_root__le,
  SemanticExplorerCases.case_root__l7,
  SemanticExplorerCases.case_root__l12,
  SemanticExplorerCases.case_root__l12_3,
  SemanticExplorerCases.case_root__lle,
  SemanticExplorerCases.case_root__l_e,
  SemanticExplorerCases.case_root__l_p12,
  SemanticExplorerCases.case_root__p_l12,
  SemanticExplorerCases.case_root__pl1,
  SemanticExplorerCases.case_capture__e,
  SemanticExplorerCases.case_capture__n0,
  SemanticExplorerCases.case_capture__n1,
  SemanticExplorerCases.case_capture__bt,
  SemanticExplorerCases.case_capture__bf,
  SemanticExplorerCases.case_capture__pbt,
  SemanticExplorerCases.case_capture__pbt_e,
  SemanticExplorerCases.case_capture__pbt_1,
  SemanticExplorerCases.case_capture__lbt,
  SemanticExplorerCases.case_capture__lbt_bf,
  SemanticExplorerCases.case_capture__lpbt_1,
  SemanticExplorerCases.case_capture__p1,
  SemanticExplorerCases.case_capture__p12,
  SemanticExplorerCases.case_capture__p123,
  SemanticExplorerCases.case_capture__pee,
  SemanticExplorerCases.case_capture__pe1,
  SemanticExplorerCases.case_capture__p1e,
  SemanticExplorerCases.case_capture__p12_3,
  SemanticExplorerCases.case_capture__p12_34,
  SemanticExplorerCases.case_capture__pe_12,
  SemanticExplorerCases.case_capture__ppe1_2,
  SemanticExplorerCases.case_capture__p12_e,
  SemanticExplorerCases.case_capture__ppe,
  SemanticExplorerCases.case_capture__pp1,
  SemanticExplorerCases.case_capture__ppp12,
  SemanticExplorerCases.case_capture__le,
  SemanticExplorerCases.case_capture__l7,
  SemanticExplorerCases.case_capture__l12,
  SemanticExplorerCases.case_capture__l12_3,
  SemanticExplorerCases.case_capture__lle,
  SemanticExplorerCases.case_capture__l_e,
  SemanticExplorerCases.case_capture__l_p12,
  SemanticExplorerCases.case_capture__p_l12,
  SemanticExplorerCases.case_capture__pl1,
  SemanticExplorerCases.case_captureCall__e,
  SemanticExplorerCases.case_captureCall__n0,
  SemanticExplorerCases.case_captureCall__n1,
  SemanticExplorerCases.case_captureCall__bt,
  SemanticExplorerCases.case_captureCall__bf,
  SemanticExplorerCases.case_captureCall__pbt,
  SemanticExplorerCases.case_captureCall__pbt_e,
  SemanticExplorerCases.case_captureCall__pbt_1,
  SemanticExplorerCases.case_captureCall__lbt,
  SemanticExplorerCases.case_captureCall__lbt_bf,
  SemanticExplorerCases.case_captureCall__lpbt_1,
  SemanticExplorerCases.case_captureCall__p1,
  SemanticExplorerCases.case_captureCall__p12,
  SemanticExplorerCases.case_captureCall__p123,
  SemanticExplorerCases.case_captureCall__pee,
  SemanticExplorerCases.case_captureCall__pe1,
  SemanticExplorerCases.case_captureCall__p1e,
  SemanticExplorerCases.case_captureCall__p12_3,
  SemanticExplorerCases.case_captureCall__p12_34,
  SemanticExplorerCases.case_captureCall__pe_12,
  SemanticExplorerCases.case_captureCall__ppe1_2,
  SemanticExplorerCases.case_captureCall__p12_e,
  SemanticExplorerCases.case_captureCall__ppe,
  SemanticExplorerCases.case_captureCall__pp1,
  SemanticExplorerCases.case_captureCall__ppp12,
  SemanticExplorerCases.case_captureCall__le,
  SemanticExplorerCases.case_captureCall__l7,
  SemanticExplorerCases.case_captureCall__l12,
  SemanticExplorerCases.case_captureCall__l12_3,
  SemanticExplorerCases.case_captureCall__lle,
  SemanticExplorerCases.case_captureCall__l_e,
  SemanticExplorerCases.case_captureCall__l_p12,
  SemanticExplorerCases.case_captureCall__p_l12,
  SemanticExplorerCases.case_captureCall__pl1,
  SemanticExplorerCases.case_dotAccess__e,
  SemanticExplorerCases.case_dotAccess__n0,
  SemanticExplorerCases.case_dotAccess__n1,
  SemanticExplorerCases.case_dotAccess__bt,
  SemanticExplorerCases.case_dotAccess__bf,
  SemanticExplorerCases.case_dotAccess__pbt,
  SemanticExplorerCases.case_dotAccess__pbt_e,
  SemanticExplorerCases.case_dotAccess__pbt_1,
  SemanticExplorerCases.case_dotAccess__lbt,
  SemanticExplorerCases.case_dotAccess__lbt_bf,
  SemanticExplorerCases.case_dotAccess__lpbt_1,
  SemanticExplorerCases.case_dotAccess__p1,
  SemanticExplorerCases.case_dotAccess__p12,
  SemanticExplorerCases.case_dotAccess__p123,
  SemanticExplorerCases.case_dotAccess__pee,
  SemanticExplorerCases.case_dotAccess__pe1,
  SemanticExplorerCases.case_dotAccess__p1e,
  SemanticExplorerCases.case_dotAccess__p12_3,
  SemanticExplorerCases.case_dotAccess__p12_34,
  SemanticExplorerCases.case_dotAccess__pe_12,
  SemanticExplorerCases.case_dotAccess__ppe1_2,
  SemanticExplorerCases.case_dotAccess__p12_e,
  SemanticExplorerCases.case_dotAccess__ppe,
  SemanticExplorerCases.case_dotAccess__pp1,
  SemanticExplorerCases.case_dotAccess__ppp12,
  SemanticExplorerCases.case_dotAccess__le,
  SemanticExplorerCases.case_dotAccess__l7,
  SemanticExplorerCases.case_dotAccess__l12,
  SemanticExplorerCases.case_dotAccess__l12_3,
  SemanticExplorerCases.case_dotAccess__lle,
  SemanticExplorerCases.case_dotAccess__l_e,
  SemanticExplorerCases.case_dotAccess__l_p12,
  SemanticExplorerCases.case_dotAccess__p_l12,
  SemanticExplorerCases.case_dotAccess__pl1,
  SemanticExplorerCases.case_dotAccessCall__e,
  SemanticExplorerCases.case_dotAccessCall__n0,
  SemanticExplorerCases.case_dotAccessCall__n1,
  SemanticExplorerCases.case_dotAccessCall__bt,
  SemanticExplorerCases.case_dotAccessCall__bf,
  SemanticExplorerCases.case_dotAccessCall__pbt,
  SemanticExplorerCases.case_dotAccessCall__pbt_e,
  SemanticExplorerCases.case_dotAccessCall__pbt_1,
  SemanticExplorerCases.case_dotAccessCall__lbt,
  SemanticExplorerCases.case_dotAccessCall__lbt_bf,
  SemanticExplorerCases.case_dotAccessCall__lpbt_1,
  SemanticExplorerCases.case_dotAccessCall__p1,
  SemanticExplorerCases.case_dotAccessCall__p12,
  SemanticExplorerCases.case_dotAccessCall__p123,
  SemanticExplorerCases.case_dotAccessCall__pee,
  SemanticExplorerCases.case_dotAccessCall__pe1,
  SemanticExplorerCases.case_dotAccessCall__p1e,
  SemanticExplorerCases.case_dotAccessCall__p12_3,
  SemanticExplorerCases.case_dotAccessCall__p12_34,
  SemanticExplorerCases.case_dotAccessCall__pe_12,
  SemanticExplorerCases.case_dotAccessCall__ppe1_2,
  SemanticExplorerCases.case_dotAccessCall__p12_e,
  SemanticExplorerCases.case_dotAccessCall__ppe,
  SemanticExplorerCases.case_dotAccessCall__pp1,
  SemanticExplorerCases.case_dotAccessCall__ppp12,
  SemanticExplorerCases.case_dotAccessCall__le,
  SemanticExplorerCases.case_dotAccessCall__l7,
  SemanticExplorerCases.case_dotAccessCall__l12,
  SemanticExplorerCases.case_dotAccessCall__l12_3,
  SemanticExplorerCases.case_dotAccessCall__lle,
  SemanticExplorerCases.case_dotAccessCall__l_e,
  SemanticExplorerCases.case_dotAccessCall__l_p12,
  SemanticExplorerCases.case_dotAccessCall__p_l12,
  SemanticExplorerCases.case_dotAccessCall__pl1,
  SemanticExplorerCases.case_fixed__e,
  SemanticExplorerCases.case_fixed__n0,
  SemanticExplorerCases.case_fixed__n1,
  SemanticExplorerCases.case_fixed__bt,
  SemanticExplorerCases.case_fixed__bf,
  SemanticExplorerCases.case_fixed__pbt,
  SemanticExplorerCases.case_fixed__pbt_e,
  SemanticExplorerCases.case_fixed__pbt_1,
  SemanticExplorerCases.case_fixed__lbt,
  SemanticExplorerCases.case_fixed__lbt_bf,
  SemanticExplorerCases.case_fixed__lpbt_1,
  SemanticExplorerCases.case_fixed__p1,
  SemanticExplorerCases.case_fixed__p12,
  SemanticExplorerCases.case_fixed__p123,
  SemanticExplorerCases.case_fixed__pee,
  SemanticExplorerCases.case_fixed__pe1,
  SemanticExplorerCases.case_fixed__p1e,
  SemanticExplorerCases.case_fixed__p12_3,
  SemanticExplorerCases.case_fixed__p12_34,
  SemanticExplorerCases.case_fixed__pe_12,
  SemanticExplorerCases.case_fixed__ppe1_2,
  SemanticExplorerCases.case_fixed__p12_e,
  SemanticExplorerCases.case_fixed__ppe,
  SemanticExplorerCases.case_fixed__pp1,
  SemanticExplorerCases.case_fixed__ppp12,
  SemanticExplorerCases.case_fixed__le,
  SemanticExplorerCases.case_fixed__l7,
  SemanticExplorerCases.case_fixed__l12,
  SemanticExplorerCases.case_fixed__l12_3,
  SemanticExplorerCases.case_fixed__lle,
  SemanticExplorerCases.case_fixed__l_e,
  SemanticExplorerCases.case_fixed__l_p12,
  SemanticExplorerCases.case_fixed__p_l12,
  SemanticExplorerCases.case_fixed__pl1,
  SemanticExplorerCases.case_fixedSpread__e,
  SemanticExplorerCases.case_fixedSpread__n0,
  SemanticExplorerCases.case_fixedSpread__n1,
  SemanticExplorerCases.case_fixedSpread__bt,
  SemanticExplorerCases.case_fixedSpread__bf,
  SemanticExplorerCases.case_fixedSpread__pbt,
  SemanticExplorerCases.case_fixedSpread__pbt_e,
  SemanticExplorerCases.case_fixedSpread__pbt_1,
  SemanticExplorerCases.case_fixedSpread__lbt,
  SemanticExplorerCases.case_fixedSpread__lbt_bf,
  SemanticExplorerCases.case_fixedSpread__lpbt_1,
  SemanticExplorerCases.case_fixedSpread__p1,
  SemanticExplorerCases.case_fixedSpread__p12,
  SemanticExplorerCases.case_fixedSpread__p123,
  SemanticExplorerCases.case_fixedSpread__pee,
  SemanticExplorerCases.case_fixedSpread__pe1,
  SemanticExplorerCases.case_fixedSpread__p1e,
  SemanticExplorerCases.case_fixedSpread__p12_3,
  SemanticExplorerCases.case_fixedSpread__p12_34,
  SemanticExplorerCases.case_fixedSpread__pe_12,
  SemanticExplorerCases.case_fixedSpread__ppe1_2,
  SemanticExplorerCases.case_fixedSpread__p12_e,
  SemanticExplorerCases.case_fixedSpread__ppe,
  SemanticExplorerCases.case_fixedSpread__pp1,
  SemanticExplorerCases.case_fixedSpread__ppp12,
  SemanticExplorerCases.case_fixedSpread__le,
  SemanticExplorerCases.case_fixedSpread__l7,
  SemanticExplorerCases.case_fixedSpread__l12,
  SemanticExplorerCases.case_fixedSpread__l12_3,
  SemanticExplorerCases.case_fixedSpread__lle,
  SemanticExplorerCases.case_fixedSpread__l_e,
  SemanticExplorerCases.case_fixedSpread__l_p12,
  SemanticExplorerCases.case_fixedSpread__p_l12,
  SemanticExplorerCases.case_fixedSpread__pl1,
  SemanticExplorerCases.case_collecting__e,
  SemanticExplorerCases.case_collecting__n0,
  SemanticExplorerCases.case_collecting__n1,
  SemanticExplorerCases.case_collecting__bt,
  SemanticExplorerCases.case_collecting__bf,
  SemanticExplorerCases.case_collecting__pbt,
  SemanticExplorerCases.case_collecting__pbt_e,
  SemanticExplorerCases.case_collecting__pbt_1,
  SemanticExplorerCases.case_collecting__lbt,
  SemanticExplorerCases.case_collecting__lbt_bf,
  SemanticExplorerCases.case_collecting__lpbt_1,
  SemanticExplorerCases.case_collecting__p1,
  SemanticExplorerCases.case_collecting__p12,
  SemanticExplorerCases.case_collecting__p123,
  SemanticExplorerCases.case_collecting__pee,
  SemanticExplorerCases.case_collecting__pe1,
  SemanticExplorerCases.case_collecting__p1e,
  SemanticExplorerCases.case_collecting__p12_3,
  SemanticExplorerCases.case_collecting__p12_34,
  SemanticExplorerCases.case_collecting__pe_12,
  SemanticExplorerCases.case_collecting__ppe1_2,
  SemanticExplorerCases.case_collecting__p12_e,
  SemanticExplorerCases.case_collecting__ppe,
  SemanticExplorerCases.case_collecting__pp1,
  SemanticExplorerCases.case_collecting__ppp12,
  SemanticExplorerCases.case_collecting__le,
  SemanticExplorerCases.case_collecting__l7,
  SemanticExplorerCases.case_collecting__l12,
  SemanticExplorerCases.case_collecting__l12_3,
  SemanticExplorerCases.case_collecting__lle,
  SemanticExplorerCases.case_collecting__l_e,
  SemanticExplorerCases.case_collecting__l_p12,
  SemanticExplorerCases.case_collecting__p_l12,
  SemanticExplorerCases.case_collecting__pl1,
  SemanticExplorerCases.case_collectingSpread__e,
  SemanticExplorerCases.case_collectingSpread__n0,
  SemanticExplorerCases.case_collectingSpread__n1,
  SemanticExplorerCases.case_collectingSpread__bt,
  SemanticExplorerCases.case_collectingSpread__bf,
  SemanticExplorerCases.case_collectingSpread__pbt,
  SemanticExplorerCases.case_collectingSpread__pbt_e,
  SemanticExplorerCases.case_collectingSpread__pbt_1,
  SemanticExplorerCases.case_collectingSpread__lbt,
  SemanticExplorerCases.case_collectingSpread__lbt_bf,
  SemanticExplorerCases.case_collectingSpread__lpbt_1,
  SemanticExplorerCases.case_collectingSpread__p1,
  SemanticExplorerCases.case_collectingSpread__p12,
  SemanticExplorerCases.case_collectingSpread__p123,
  SemanticExplorerCases.case_collectingSpread__pee,
  SemanticExplorerCases.case_collectingSpread__pe1,
  SemanticExplorerCases.case_collectingSpread__p1e,
  SemanticExplorerCases.case_collectingSpread__p12_3,
  SemanticExplorerCases.case_collectingSpread__p12_34,
  SemanticExplorerCases.case_collectingSpread__pe_12,
  SemanticExplorerCases.case_collectingSpread__ppe1_2,
  SemanticExplorerCases.case_collectingSpread__p12_e,
  SemanticExplorerCases.case_collectingSpread__ppe,
  SemanticExplorerCases.case_collectingSpread__pp1,
  SemanticExplorerCases.case_collectingSpread__ppp12,
  SemanticExplorerCases.case_collectingSpread__le,
  SemanticExplorerCases.case_collectingSpread__l7,
  SemanticExplorerCases.case_collectingSpread__l12,
  SemanticExplorerCases.case_collectingSpread__l12_3,
  SemanticExplorerCases.case_collectingSpread__lle,
  SemanticExplorerCases.case_collectingSpread__l_e,
  SemanticExplorerCases.case_collectingSpread__l_p12,
  SemanticExplorerCases.case_collectingSpread__p_l12,
  SemanticExplorerCases.case_collectingSpread__pl1,
  SemanticExplorerCases.case_collectingViaProp__e,
  SemanticExplorerCases.case_collectingViaProp__n0,
  SemanticExplorerCases.case_collectingViaProp__n1,
  SemanticExplorerCases.case_collectingViaProp__bt,
  SemanticExplorerCases.case_collectingViaProp__bf,
  SemanticExplorerCases.case_collectingViaProp__pbt,
  SemanticExplorerCases.case_collectingViaProp__pbt_e,
  SemanticExplorerCases.case_collectingViaProp__pbt_1,
  SemanticExplorerCases.case_collectingViaProp__lbt,
  SemanticExplorerCases.case_collectingViaProp__lbt_bf,
  SemanticExplorerCases.case_collectingViaProp__lpbt_1,
  SemanticExplorerCases.case_collectingViaProp__p1,
  SemanticExplorerCases.case_collectingViaProp__p12,
  SemanticExplorerCases.case_collectingViaProp__p123,
  SemanticExplorerCases.case_collectingViaProp__pee,
  SemanticExplorerCases.case_collectingViaProp__pe1,
  SemanticExplorerCases.case_collectingViaProp__p1e,
  SemanticExplorerCases.case_collectingViaProp__p12_3,
  SemanticExplorerCases.case_collectingViaProp__p12_34,
  SemanticExplorerCases.case_collectingViaProp__pe_12,
  SemanticExplorerCases.case_collectingViaProp__ppe1_2,
  SemanticExplorerCases.case_collectingViaProp__p12_e,
  SemanticExplorerCases.case_collectingViaProp__ppe,
  SemanticExplorerCases.case_collectingViaProp__pp1,
  SemanticExplorerCases.case_collectingViaProp__ppp12,
  SemanticExplorerCases.case_collectingViaProp__le,
  SemanticExplorerCases.case_collectingViaProp__l7,
  SemanticExplorerCases.case_collectingViaProp__l12,
  SemanticExplorerCases.case_collectingViaProp__l12_3,
  SemanticExplorerCases.case_collectingViaProp__lle,
  SemanticExplorerCases.case_collectingViaProp__l_e,
  SemanticExplorerCases.case_collectingViaProp__l_p12,
  SemanticExplorerCases.case_collectingViaProp__p_l12,
  SemanticExplorerCases.case_collectingViaProp__pl1,
  SemanticExplorerCases.case_dotCollectingViaProp__e,
  SemanticExplorerCases.case_dotCollectingViaProp__n0,
  SemanticExplorerCases.case_dotCollectingViaProp__n1,
  SemanticExplorerCases.case_dotCollectingViaProp__bt,
  SemanticExplorerCases.case_dotCollectingViaProp__bf,
  SemanticExplorerCases.case_dotCollectingViaProp__pbt,
  SemanticExplorerCases.case_dotCollectingViaProp__pbt_e,
  SemanticExplorerCases.case_dotCollectingViaProp__pbt_1,
  SemanticExplorerCases.case_dotCollectingViaProp__lbt,
  SemanticExplorerCases.case_dotCollectingViaProp__lbt_bf,
  SemanticExplorerCases.case_dotCollectingViaProp__lpbt_1,
  SemanticExplorerCases.case_dotCollectingViaProp__p1,
  SemanticExplorerCases.case_dotCollectingViaProp__p12,
  SemanticExplorerCases.case_dotCollectingViaProp__p123,
  SemanticExplorerCases.case_dotCollectingViaProp__pee,
  SemanticExplorerCases.case_dotCollectingViaProp__pe1,
  SemanticExplorerCases.case_dotCollectingViaProp__p1e,
  SemanticExplorerCases.case_dotCollectingViaProp__p12_3,
  SemanticExplorerCases.case_dotCollectingViaProp__p12_34,
  SemanticExplorerCases.case_dotCollectingViaProp__pe_12,
  SemanticExplorerCases.case_dotCollectingViaProp__ppe1_2,
  SemanticExplorerCases.case_dotCollectingViaProp__p12_e,
  SemanticExplorerCases.case_dotCollectingViaProp__ppe,
  SemanticExplorerCases.case_dotCollectingViaProp__pp1,
  SemanticExplorerCases.case_dotCollectingViaProp__ppp12,
  SemanticExplorerCases.case_dotCollectingViaProp__le,
  SemanticExplorerCases.case_dotCollectingViaProp__l7,
  SemanticExplorerCases.case_dotCollectingViaProp__l12,
  SemanticExplorerCases.case_dotCollectingViaProp__l12_3,
  SemanticExplorerCases.case_dotCollectingViaProp__lle,
  SemanticExplorerCases.case_dotCollectingViaProp__l_e,
  SemanticExplorerCases.case_dotCollectingViaProp__l_p12,
  SemanticExplorerCases.case_dotCollectingViaProp__p_l12,
  SemanticExplorerCases.case_dotCollectingViaProp__pl1,
  SemanticExplorerCases.case_literalDotCollecting__e,
  SemanticExplorerCases.case_literalDotCollecting__n0,
  SemanticExplorerCases.case_literalDotCollecting__n1,
  SemanticExplorerCases.case_literalDotCollecting__bt,
  SemanticExplorerCases.case_literalDotCollecting__bf,
  SemanticExplorerCases.case_literalDotCollecting__pbt,
  SemanticExplorerCases.case_literalDotCollecting__pbt_e,
  SemanticExplorerCases.case_literalDotCollecting__pbt_1,
  SemanticExplorerCases.case_literalDotCollecting__lbt,
  SemanticExplorerCases.case_literalDotCollecting__lbt_bf,
  SemanticExplorerCases.case_literalDotCollecting__lpbt_1,
  SemanticExplorerCases.case_literalDotCollecting__p1,
  SemanticExplorerCases.case_literalDotCollecting__p12,
  SemanticExplorerCases.case_literalDotCollecting__p123,
  SemanticExplorerCases.case_literalDotCollecting__pee,
  SemanticExplorerCases.case_literalDotCollecting__pe1,
  SemanticExplorerCases.case_literalDotCollecting__p1e,
  SemanticExplorerCases.case_literalDotCollecting__p12_3,
  SemanticExplorerCases.case_literalDotCollecting__p12_34,
  SemanticExplorerCases.case_literalDotCollecting__pe_12,
  SemanticExplorerCases.case_literalDotCollecting__ppe1_2,
  SemanticExplorerCases.case_literalDotCollecting__p12_e,
  SemanticExplorerCases.case_literalDotCollecting__ppe,
  SemanticExplorerCases.case_literalDotCollecting__pp1,
  SemanticExplorerCases.case_literalDotCollecting__ppp12,
  SemanticExplorerCases.case_literalDotCollecting__le,
  SemanticExplorerCases.case_literalDotCollecting__l7,
  SemanticExplorerCases.case_literalDotCollecting__l12,
  SemanticExplorerCases.case_literalDotCollecting__l12_3,
  SemanticExplorerCases.case_literalDotCollecting__lle,
  SemanticExplorerCases.case_literalDotCollecting__l_e,
  SemanticExplorerCases.case_literalDotCollecting__l_p12,
  SemanticExplorerCases.case_literalDotCollecting__p_l12,
  SemanticExplorerCases.case_literalDotCollecting__pl1,
  SemanticExplorerCases.case_fluentSpreadCollecting__e,
  SemanticExplorerCases.case_fluentSpreadCollecting__n0,
  SemanticExplorerCases.case_fluentSpreadCollecting__n1,
  SemanticExplorerCases.case_fluentSpreadCollecting__bt,
  SemanticExplorerCases.case_fluentSpreadCollecting__bf,
  SemanticExplorerCases.case_fluentSpreadCollecting__pbt,
  SemanticExplorerCases.case_fluentSpreadCollecting__pbt_e,
  SemanticExplorerCases.case_fluentSpreadCollecting__pbt_1,
  SemanticExplorerCases.case_fluentSpreadCollecting__lbt,
  SemanticExplorerCases.case_fluentSpreadCollecting__lbt_bf,
  SemanticExplorerCases.case_fluentSpreadCollecting__lpbt_1,
  SemanticExplorerCases.case_fluentSpreadCollecting__p1,
  SemanticExplorerCases.case_fluentSpreadCollecting__p12,
  SemanticExplorerCases.case_fluentSpreadCollecting__p123,
  SemanticExplorerCases.case_fluentSpreadCollecting__pee,
  SemanticExplorerCases.case_fluentSpreadCollecting__pe1,
  SemanticExplorerCases.case_fluentSpreadCollecting__p1e,
  SemanticExplorerCases.case_fluentSpreadCollecting__p12_3,
  SemanticExplorerCases.case_fluentSpreadCollecting__p12_34,
  SemanticExplorerCases.case_fluentSpreadCollecting__pe_12,
  SemanticExplorerCases.case_fluentSpreadCollecting__ppe1_2,
  SemanticExplorerCases.case_fluentSpreadCollecting__p12_e,
  SemanticExplorerCases.case_fluentSpreadCollecting__ppe,
  SemanticExplorerCases.case_fluentSpreadCollecting__pp1,
  SemanticExplorerCases.case_fluentSpreadCollecting__ppp12,
  SemanticExplorerCases.case_fluentSpreadCollecting__le,
  SemanticExplorerCases.case_fluentSpreadCollecting__l7,
  SemanticExplorerCases.case_fluentSpreadCollecting__l12,
  SemanticExplorerCases.case_fluentSpreadCollecting__l12_3,
  SemanticExplorerCases.case_fluentSpreadCollecting__lle,
  SemanticExplorerCases.case_fluentSpreadCollecting__l_e,
  SemanticExplorerCases.case_fluentSpreadCollecting__l_p12,
  SemanticExplorerCases.case_fluentSpreadCollecting__p_l12,
  SemanticExplorerCases.case_fluentSpreadCollecting__pl1,
  SemanticExplorerCases.case_mixed_h__e,
  SemanticExplorerCases.case_mixed_h__n0,
  SemanticExplorerCases.case_mixed_h__n1,
  SemanticExplorerCases.case_mixed_h__bt,
  SemanticExplorerCases.case_mixed_h__bf,
  SemanticExplorerCases.case_mixed_h__pbt,
  SemanticExplorerCases.case_mixed_h__pbt_e,
  SemanticExplorerCases.case_mixed_h__pbt_1,
  SemanticExplorerCases.case_mixed_h__lbt,
  SemanticExplorerCases.case_mixed_h__lbt_bf,
  SemanticExplorerCases.case_mixed_h__lpbt_1,
  SemanticExplorerCases.case_mixed_h__p1,
  SemanticExplorerCases.case_mixed_h__p12,
  SemanticExplorerCases.case_mixed_h__p123,
  SemanticExplorerCases.case_mixed_h__pee,
  SemanticExplorerCases.case_mixed_h__pe1,
  SemanticExplorerCases.case_mixed_h__p1e,
  SemanticExplorerCases.case_mixed_h__p12_3,
  SemanticExplorerCases.case_mixed_h__p12_34,
  SemanticExplorerCases.case_mixed_h__pe_12,
  SemanticExplorerCases.case_mixed_h__ppe1_2,
  SemanticExplorerCases.case_mixed_h__p12_e,
  SemanticExplorerCases.case_mixed_h__ppe,
  SemanticExplorerCases.case_mixed_h__pp1,
  SemanticExplorerCases.case_mixed_h__ppp12,
  SemanticExplorerCases.case_mixed_h__le,
  SemanticExplorerCases.case_mixed_h__l7,
  SemanticExplorerCases.case_mixed_h__l12,
  SemanticExplorerCases.case_mixed_h__l12_3,
  SemanticExplorerCases.case_mixed_h__lle,
  SemanticExplorerCases.case_mixed_h__l_e,
  SemanticExplorerCases.case_mixed_h__l_p12,
  SemanticExplorerCases.case_mixed_h__p_l12,
  SemanticExplorerCases.case_mixed_h__pl1,
  SemanticExplorerCases.case_mixed_t__e,
  SemanticExplorerCases.case_mixed_t__n0,
  SemanticExplorerCases.case_mixed_t__n1,
  SemanticExplorerCases.case_mixed_t__bt,
  SemanticExplorerCases.case_mixed_t__bf,
  SemanticExplorerCases.case_mixed_t__pbt,
  SemanticExplorerCases.case_mixed_t__pbt_e,
  SemanticExplorerCases.case_mixed_t__pbt_1,
  SemanticExplorerCases.case_mixed_t__lbt,
  SemanticExplorerCases.case_mixed_t__lbt_bf,
  SemanticExplorerCases.case_mixed_t__lpbt_1,
  SemanticExplorerCases.case_mixed_t__p1,
  SemanticExplorerCases.case_mixed_t__p12,
  SemanticExplorerCases.case_mixed_t__p123,
  SemanticExplorerCases.case_mixed_t__pee,
  SemanticExplorerCases.case_mixed_t__pe1,
  SemanticExplorerCases.case_mixed_t__p1e,
  SemanticExplorerCases.case_mixed_t__p12_3,
  SemanticExplorerCases.case_mixed_t__p12_34,
  SemanticExplorerCases.case_mixed_t__pe_12,
  SemanticExplorerCases.case_mixed_t__ppe1_2,
  SemanticExplorerCases.case_mixed_t__p12_e,
  SemanticExplorerCases.case_mixed_t__ppe,
  SemanticExplorerCases.case_mixed_t__pp1,
  SemanticExplorerCases.case_mixed_t__ppp12,
  SemanticExplorerCases.case_mixed_t__le,
  SemanticExplorerCases.case_mixed_t__l7,
  SemanticExplorerCases.case_mixed_t__l12,
  SemanticExplorerCases.case_mixed_t__l12_3,
  SemanticExplorerCases.case_mixed_t__lle,
  SemanticExplorerCases.case_mixed_t__l_e,
  SemanticExplorerCases.case_mixed_t__l_p12,
  SemanticExplorerCases.case_mixed_t__p_l12,
  SemanticExplorerCases.case_mixed_t__pl1,
  SemanticExplorerCases.case_mixedBack_t__e,
  SemanticExplorerCases.case_mixedBack_t__n0,
  SemanticExplorerCases.case_mixedBack_t__n1,
  SemanticExplorerCases.case_mixedBack_t__bt,
  SemanticExplorerCases.case_mixedBack_t__bf,
  SemanticExplorerCases.case_mixedBack_t__pbt,
  SemanticExplorerCases.case_mixedBack_t__pbt_e,
  SemanticExplorerCases.case_mixedBack_t__pbt_1,
  SemanticExplorerCases.case_mixedBack_t__lbt,
  SemanticExplorerCases.case_mixedBack_t__lbt_bf,
  SemanticExplorerCases.case_mixedBack_t__lpbt_1,
  SemanticExplorerCases.case_mixedBack_t__p1,
  SemanticExplorerCases.case_mixedBack_t__p12,
  SemanticExplorerCases.case_mixedBack_t__p123,
  SemanticExplorerCases.case_mixedBack_t__pee,
  SemanticExplorerCases.case_mixedBack_t__pe1,
  SemanticExplorerCases.case_mixedBack_t__p1e,
  SemanticExplorerCases.case_mixedBack_t__p12_3,
  SemanticExplorerCases.case_mixedBack_t__p12_34,
  SemanticExplorerCases.case_mixedBack_t__pe_12,
  SemanticExplorerCases.case_mixedBack_t__ppe1_2,
  SemanticExplorerCases.case_mixedBack_t__p12_e,
  SemanticExplorerCases.case_mixedBack_t__ppe,
  SemanticExplorerCases.case_mixedBack_t__pp1,
  SemanticExplorerCases.case_mixedBack_t__ppp12,
  SemanticExplorerCases.case_mixedBack_t__le,
  SemanticExplorerCases.case_mixedBack_t__l7,
  SemanticExplorerCases.case_mixedBack_t__l12,
  SemanticExplorerCases.case_mixedBack_t__l12_3,
  SemanticExplorerCases.case_mixedBack_t__lle,
  SemanticExplorerCases.case_mixedBack_t__l_e,
  SemanticExplorerCases.case_mixedBack_t__l_p12,
  SemanticExplorerCases.case_mixedBack_t__p_l12,
  SemanticExplorerCases.case_mixedBack_t__pl1,
  SemanticExplorerCases.case_mixedBack_z__e,
  SemanticExplorerCases.case_mixedBack_z__n0,
  SemanticExplorerCases.case_mixedBack_z__n1,
  SemanticExplorerCases.case_mixedBack_z__bt,
  SemanticExplorerCases.case_mixedBack_z__bf,
  SemanticExplorerCases.case_mixedBack_z__pbt,
  SemanticExplorerCases.case_mixedBack_z__pbt_e,
  SemanticExplorerCases.case_mixedBack_z__pbt_1,
  SemanticExplorerCases.case_mixedBack_z__lbt,
  SemanticExplorerCases.case_mixedBack_z__lbt_bf,
  SemanticExplorerCases.case_mixedBack_z__lpbt_1,
  SemanticExplorerCases.case_mixedBack_z__p1,
  SemanticExplorerCases.case_mixedBack_z__p12,
  SemanticExplorerCases.case_mixedBack_z__p123,
  SemanticExplorerCases.case_mixedBack_z__pee,
  SemanticExplorerCases.case_mixedBack_z__pe1,
  SemanticExplorerCases.case_mixedBack_z__p1e,
  SemanticExplorerCases.case_mixedBack_z__p12_3,
  SemanticExplorerCases.case_mixedBack_z__p12_34,
  SemanticExplorerCases.case_mixedBack_z__pe_12,
  SemanticExplorerCases.case_mixedBack_z__ppe1_2,
  SemanticExplorerCases.case_mixedBack_z__p12_e,
  SemanticExplorerCases.case_mixedBack_z__ppe,
  SemanticExplorerCases.case_mixedBack_z__pp1,
  SemanticExplorerCases.case_mixedBack_z__ppp12,
  SemanticExplorerCases.case_mixedBack_z__le,
  SemanticExplorerCases.case_mixedBack_z__l7,
  SemanticExplorerCases.case_mixedBack_z__l12,
  SemanticExplorerCases.case_mixedBack_z__l12_3,
  SemanticExplorerCases.case_mixedBack_z__lle,
  SemanticExplorerCases.case_mixedBack_z__l_e,
  SemanticExplorerCases.case_mixedBack_z__l_p12,
  SemanticExplorerCases.case_mixedBack_z__p_l12,
  SemanticExplorerCases.case_mixedBack_z__pl1,
  SemanticExplorerCases.case_deconPair_x__e,
  SemanticExplorerCases.case_deconPair_x__n0,
  SemanticExplorerCases.case_deconPair_x__n1,
  SemanticExplorerCases.case_deconPair_x__bt,
  SemanticExplorerCases.case_deconPair_x__bf,
  SemanticExplorerCases.case_deconPair_x__pbt,
  SemanticExplorerCases.case_deconPair_x__pbt_e,
  SemanticExplorerCases.case_deconPair_x__pbt_1,
  SemanticExplorerCases.case_deconPair_x__lbt,
  SemanticExplorerCases.case_deconPair_x__lbt_bf,
  SemanticExplorerCases.case_deconPair_x__lpbt_1,
  SemanticExplorerCases.case_deconPair_x__p1,
  SemanticExplorerCases.case_deconPair_x__p12,
  SemanticExplorerCases.case_deconPair_x__p123,
  SemanticExplorerCases.case_deconPair_x__pee,
  SemanticExplorerCases.case_deconPair_x__pe1,
  SemanticExplorerCases.case_deconPair_x__p1e,
  SemanticExplorerCases.case_deconPair_x__p12_3,
  SemanticExplorerCases.case_deconPair_x__p12_34,
  SemanticExplorerCases.case_deconPair_x__pe_12,
  SemanticExplorerCases.case_deconPair_x__ppe1_2,
  SemanticExplorerCases.case_deconPair_x__p12_e,
  SemanticExplorerCases.case_deconPair_x__ppe,
  SemanticExplorerCases.case_deconPair_x__pp1,
  SemanticExplorerCases.case_deconPair_x__ppp12,
  SemanticExplorerCases.case_deconPair_x__le,
  SemanticExplorerCases.case_deconPair_x__l7,
  SemanticExplorerCases.case_deconPair_x__l12,
  SemanticExplorerCases.case_deconPair_x__l12_3,
  SemanticExplorerCases.case_deconPair_x__lle,
  SemanticExplorerCases.case_deconPair_x__l_e,
  SemanticExplorerCases.case_deconPair_x__l_p12,
  SemanticExplorerCases.case_deconPair_x__p_l12,
  SemanticExplorerCases.case_deconPair_x__pl1,
  SemanticExplorerCases.case_deconPair_y__e,
  SemanticExplorerCases.case_deconPair_y__n0,
  SemanticExplorerCases.case_deconPair_y__n1,
  SemanticExplorerCases.case_deconPair_y__bt,
  SemanticExplorerCases.case_deconPair_y__bf,
  SemanticExplorerCases.case_deconPair_y__pbt,
  SemanticExplorerCases.case_deconPair_y__pbt_e,
  SemanticExplorerCases.case_deconPair_y__pbt_1,
  SemanticExplorerCases.case_deconPair_y__lbt,
  SemanticExplorerCases.case_deconPair_y__lbt_bf,
  SemanticExplorerCases.case_deconPair_y__lpbt_1,
  SemanticExplorerCases.case_deconPair_y__p1,
  SemanticExplorerCases.case_deconPair_y__p12,
  SemanticExplorerCases.case_deconPair_y__p123,
  SemanticExplorerCases.case_deconPair_y__pee,
  SemanticExplorerCases.case_deconPair_y__pe1,
  SemanticExplorerCases.case_deconPair_y__p1e,
  SemanticExplorerCases.case_deconPair_y__p12_3,
  SemanticExplorerCases.case_deconPair_y__p12_34,
  SemanticExplorerCases.case_deconPair_y__pe_12,
  SemanticExplorerCases.case_deconPair_y__ppe1_2,
  SemanticExplorerCases.case_deconPair_y__p12_e,
  SemanticExplorerCases.case_deconPair_y__ppe,
  SemanticExplorerCases.case_deconPair_y__pp1,
  SemanticExplorerCases.case_deconPair_y__ppp12,
  SemanticExplorerCases.case_deconPair_y__le,
  SemanticExplorerCases.case_deconPair_y__l7,
  SemanticExplorerCases.case_deconPair_y__l12,
  SemanticExplorerCases.case_deconPair_y__l12_3,
  SemanticExplorerCases.case_deconPair_y__lle,
  SemanticExplorerCases.case_deconPair_y__l_e,
  SemanticExplorerCases.case_deconPair_y__l_p12,
  SemanticExplorerCases.case_deconPair_y__p_l12,
  SemanticExplorerCases.case_deconPair_y__pl1,
  SemanticExplorerCases.case_deconPairSpread_x__e,
  SemanticExplorerCases.case_deconPairSpread_x__n0,
  SemanticExplorerCases.case_deconPairSpread_x__n1,
  SemanticExplorerCases.case_deconPairSpread_x__bt,
  SemanticExplorerCases.case_deconPairSpread_x__bf,
  SemanticExplorerCases.case_deconPairSpread_x__pbt,
  SemanticExplorerCases.case_deconPairSpread_x__pbt_e,
  SemanticExplorerCases.case_deconPairSpread_x__pbt_1,
  SemanticExplorerCases.case_deconPairSpread_x__lbt,
  SemanticExplorerCases.case_deconPairSpread_x__lbt_bf,
  SemanticExplorerCases.case_deconPairSpread_x__lpbt_1,
  SemanticExplorerCases.case_deconPairSpread_x__p1,
  SemanticExplorerCases.case_deconPairSpread_x__p12,
  SemanticExplorerCases.case_deconPairSpread_x__p123,
  SemanticExplorerCases.case_deconPairSpread_x__pee,
  SemanticExplorerCases.case_deconPairSpread_x__pe1,
  SemanticExplorerCases.case_deconPairSpread_x__p1e,
  SemanticExplorerCases.case_deconPairSpread_x__p12_3,
  SemanticExplorerCases.case_deconPairSpread_x__p12_34,
  SemanticExplorerCases.case_deconPairSpread_x__pe_12,
  SemanticExplorerCases.case_deconPairSpread_x__ppe1_2,
  SemanticExplorerCases.case_deconPairSpread_x__p12_e,
  SemanticExplorerCases.case_deconPairSpread_x__ppe,
  SemanticExplorerCases.case_deconPairSpread_x__pp1,
  SemanticExplorerCases.case_deconPairSpread_x__ppp12,
  SemanticExplorerCases.case_deconPairSpread_x__le,
  SemanticExplorerCases.case_deconPairSpread_x__l7,
  SemanticExplorerCases.case_deconPairSpread_x__l12,
  SemanticExplorerCases.case_deconPairSpread_x__l12_3,
  SemanticExplorerCases.case_deconPairSpread_x__lle,
  SemanticExplorerCases.case_deconPairSpread_x__l_e,
  SemanticExplorerCases.case_deconPairSpread_x__l_p12,
  SemanticExplorerCases.case_deconPairSpread_x__p_l12,
  SemanticExplorerCases.case_deconPairSpread_x__pl1,
  SemanticExplorerCases.case_deconCollect_t__e,
  SemanticExplorerCases.case_deconCollect_t__n0,
  SemanticExplorerCases.case_deconCollect_t__n1,
  SemanticExplorerCases.case_deconCollect_t__bt,
  SemanticExplorerCases.case_deconCollect_t__bf,
  SemanticExplorerCases.case_deconCollect_t__pbt,
  SemanticExplorerCases.case_deconCollect_t__pbt_e,
  SemanticExplorerCases.case_deconCollect_t__pbt_1,
  SemanticExplorerCases.case_deconCollect_t__lbt,
  SemanticExplorerCases.case_deconCollect_t__lbt_bf,
  SemanticExplorerCases.case_deconCollect_t__lpbt_1,
  SemanticExplorerCases.case_deconCollect_t__p1,
  SemanticExplorerCases.case_deconCollect_t__p12,
  SemanticExplorerCases.case_deconCollect_t__p123,
  SemanticExplorerCases.case_deconCollect_t__pee,
  SemanticExplorerCases.case_deconCollect_t__pe1,
  SemanticExplorerCases.case_deconCollect_t__p1e,
  SemanticExplorerCases.case_deconCollect_t__p12_3,
  SemanticExplorerCases.case_deconCollect_t__p12_34,
  SemanticExplorerCases.case_deconCollect_t__pe_12,
  SemanticExplorerCases.case_deconCollect_t__ppe1_2,
  SemanticExplorerCases.case_deconCollect_t__p12_e,
  SemanticExplorerCases.case_deconCollect_t__ppe,
  SemanticExplorerCases.case_deconCollect_t__pp1,
  SemanticExplorerCases.case_deconCollect_t__ppp12,
  SemanticExplorerCases.case_deconCollect_t__le,
  SemanticExplorerCases.case_deconCollect_t__l7,
  SemanticExplorerCases.case_deconCollect_t__l12,
  SemanticExplorerCases.case_deconCollect_t__l12_3,
  SemanticExplorerCases.case_deconCollect_t__lle,
  SemanticExplorerCases.case_deconCollect_t__l_e,
  SemanticExplorerCases.case_deconCollect_t__l_p12,
  SemanticExplorerCases.case_deconCollect_t__p_l12,
  SemanticExplorerCases.case_deconCollect_t__pl1,
  SemanticExplorerCases.case_deconCollectSpread_t__e,
  SemanticExplorerCases.case_deconCollectSpread_t__n0,
  SemanticExplorerCases.case_deconCollectSpread_t__n1,
  SemanticExplorerCases.case_deconCollectSpread_t__bt,
  SemanticExplorerCases.case_deconCollectSpread_t__bf,
  SemanticExplorerCases.case_deconCollectSpread_t__pbt,
  SemanticExplorerCases.case_deconCollectSpread_t__pbt_e,
  SemanticExplorerCases.case_deconCollectSpread_t__pbt_1,
  SemanticExplorerCases.case_deconCollectSpread_t__lbt,
  SemanticExplorerCases.case_deconCollectSpread_t__lbt_bf,
  SemanticExplorerCases.case_deconCollectSpread_t__lpbt_1,
  SemanticExplorerCases.case_deconCollectSpread_t__p1,
  SemanticExplorerCases.case_deconCollectSpread_t__p12,
  SemanticExplorerCases.case_deconCollectSpread_t__p123,
  SemanticExplorerCases.case_deconCollectSpread_t__pee,
  SemanticExplorerCases.case_deconCollectSpread_t__pe1,
  SemanticExplorerCases.case_deconCollectSpread_t__p1e,
  SemanticExplorerCases.case_deconCollectSpread_t__p12_3,
  SemanticExplorerCases.case_deconCollectSpread_t__p12_34,
  SemanticExplorerCases.case_deconCollectSpread_t__pe_12,
  SemanticExplorerCases.case_deconCollectSpread_t__ppe1_2,
  SemanticExplorerCases.case_deconCollectSpread_t__p12_e,
  SemanticExplorerCases.case_deconCollectSpread_t__ppe,
  SemanticExplorerCases.case_deconCollectSpread_t__pp1,
  SemanticExplorerCases.case_deconCollectSpread_t__ppp12,
  SemanticExplorerCases.case_deconCollectSpread_t__le,
  SemanticExplorerCases.case_deconCollectSpread_t__l7,
  SemanticExplorerCases.case_deconCollectSpread_t__l12,
  SemanticExplorerCases.case_deconCollectSpread_t__l12_3,
  SemanticExplorerCases.case_deconCollectSpread_t__lle,
  SemanticExplorerCases.case_deconCollectSpread_t__l_e,
  SemanticExplorerCases.case_deconCollectSpread_t__l_p12,
  SemanticExplorerCases.case_deconCollectSpread_t__p_l12,
  SemanticExplorerCases.case_deconCollectSpread_t__pl1,
  SemanticExplorerCases.case_deconPrefix_p__e,
  SemanticExplorerCases.case_deconPrefix_p__n0,
  SemanticExplorerCases.case_deconPrefix_p__n1,
  SemanticExplorerCases.case_deconPrefix_p__bt,
  SemanticExplorerCases.case_deconPrefix_p__bf,
  SemanticExplorerCases.case_deconPrefix_p__pbt,
  SemanticExplorerCases.case_deconPrefix_p__pbt_e,
  SemanticExplorerCases.case_deconPrefix_p__pbt_1,
  SemanticExplorerCases.case_deconPrefix_p__lbt,
  SemanticExplorerCases.case_deconPrefix_p__lbt_bf,
  SemanticExplorerCases.case_deconPrefix_p__lpbt_1,
  SemanticExplorerCases.case_deconPrefix_p__p1,
  SemanticExplorerCases.case_deconPrefix_p__p12,
  SemanticExplorerCases.case_deconPrefix_p__p123,
  SemanticExplorerCases.case_deconPrefix_p__pee,
  SemanticExplorerCases.case_deconPrefix_p__pe1,
  SemanticExplorerCases.case_deconPrefix_p__p1e,
  SemanticExplorerCases.case_deconPrefix_p__p12_3,
  SemanticExplorerCases.case_deconPrefix_p__p12_34,
  SemanticExplorerCases.case_deconPrefix_p__pe_12,
  SemanticExplorerCases.case_deconPrefix_p__ppe1_2,
  SemanticExplorerCases.case_deconPrefix_p__p12_e,
  SemanticExplorerCases.case_deconPrefix_p__ppe,
  SemanticExplorerCases.case_deconPrefix_p__pp1,
  SemanticExplorerCases.case_deconPrefix_p__ppp12,
  SemanticExplorerCases.case_deconPrefix_p__le,
  SemanticExplorerCases.case_deconPrefix_p__l7,
  SemanticExplorerCases.case_deconPrefix_p__l12,
  SemanticExplorerCases.case_deconPrefix_p__l12_3,
  SemanticExplorerCases.case_deconPrefix_p__lle,
  SemanticExplorerCases.case_deconPrefix_p__l_e,
  SemanticExplorerCases.case_deconPrefix_p__l_p12,
  SemanticExplorerCases.case_deconPrefix_p__p_l12,
  SemanticExplorerCases.case_deconPrefix_p__pl1,
  SemanticExplorerCases.case_deconPrefix_z__e,
  SemanticExplorerCases.case_deconPrefix_z__n0,
  SemanticExplorerCases.case_deconPrefix_z__n1,
  SemanticExplorerCases.case_deconPrefix_z__bt,
  SemanticExplorerCases.case_deconPrefix_z__bf,
  SemanticExplorerCases.case_deconPrefix_z__pbt,
  SemanticExplorerCases.case_deconPrefix_z__pbt_e,
  SemanticExplorerCases.case_deconPrefix_z__pbt_1,
  SemanticExplorerCases.case_deconPrefix_z__lbt,
  SemanticExplorerCases.case_deconPrefix_z__lbt_bf,
  SemanticExplorerCases.case_deconPrefix_z__lpbt_1,
  SemanticExplorerCases.case_deconPrefix_z__p1,
  SemanticExplorerCases.case_deconPrefix_z__p12,
  SemanticExplorerCases.case_deconPrefix_z__p123,
  SemanticExplorerCases.case_deconPrefix_z__pee,
  SemanticExplorerCases.case_deconPrefix_z__pe1,
  SemanticExplorerCases.case_deconPrefix_z__p1e,
  SemanticExplorerCases.case_deconPrefix_z__p12_3,
  SemanticExplorerCases.case_deconPrefix_z__p12_34,
  SemanticExplorerCases.case_deconPrefix_z__pe_12,
  SemanticExplorerCases.case_deconPrefix_z__ppe1_2,
  SemanticExplorerCases.case_deconPrefix_z__p12_e,
  SemanticExplorerCases.case_deconPrefix_z__ppe,
  SemanticExplorerCases.case_deconPrefix_z__pp1,
  SemanticExplorerCases.case_deconPrefix_z__ppp12,
  SemanticExplorerCases.case_deconPrefix_z__le,
  SemanticExplorerCases.case_deconPrefix_z__l7,
  SemanticExplorerCases.case_deconPrefix_z__l12,
  SemanticExplorerCases.case_deconPrefix_z__l12_3,
  SemanticExplorerCases.case_deconPrefix_z__lle,
  SemanticExplorerCases.case_deconPrefix_z__l_e,
  SemanticExplorerCases.case_deconPrefix_z__l_p12,
  SemanticExplorerCases.case_deconPrefix_z__p_l12,
  SemanticExplorerCases.case_deconPrefix_z__pl1,
  SemanticExplorerCases.case_seqWrapPair__e,
  SemanticExplorerCases.case_seqWrapPair__n0,
  SemanticExplorerCases.case_seqWrapPair__n1,
  SemanticExplorerCases.case_seqWrapPair__bt,
  SemanticExplorerCases.case_seqWrapPair__bf,
  SemanticExplorerCases.case_seqWrapPair__pbt,
  SemanticExplorerCases.case_seqWrapPair__pbt_e,
  SemanticExplorerCases.case_seqWrapPair__pbt_1,
  SemanticExplorerCases.case_seqWrapPair__lbt,
  SemanticExplorerCases.case_seqWrapPair__lbt_bf,
  SemanticExplorerCases.case_seqWrapPair__lpbt_1,
  SemanticExplorerCases.case_seqWrapPair__p1,
  SemanticExplorerCases.case_seqWrapPair__p12,
  SemanticExplorerCases.case_seqWrapPair__p123,
  SemanticExplorerCases.case_seqWrapPair__pee,
  SemanticExplorerCases.case_seqWrapPair__pe1,
  SemanticExplorerCases.case_seqWrapPair__p1e,
  SemanticExplorerCases.case_seqWrapPair__p12_3,
  SemanticExplorerCases.case_seqWrapPair__p12_34,
  SemanticExplorerCases.case_seqWrapPair__pe_12,
  SemanticExplorerCases.case_seqWrapPair__ppe1_2,
  SemanticExplorerCases.case_seqWrapPair__p12_e,
  SemanticExplorerCases.case_seqWrapPair__ppe,
  SemanticExplorerCases.case_seqWrapPair__pp1,
  SemanticExplorerCases.case_seqWrapPair__ppp12,
  SemanticExplorerCases.case_seqWrapPair__le,
  SemanticExplorerCases.case_seqWrapPair__l7,
  SemanticExplorerCases.case_seqWrapPair__l12,
  SemanticExplorerCases.case_seqWrapPair__l12_3,
  SemanticExplorerCases.case_seqWrapPair__lle,
  SemanticExplorerCases.case_seqWrapPair__l_e,
  SemanticExplorerCases.case_seqWrapPair__l_p12,
  SemanticExplorerCases.case_seqWrapPair__p_l12,
  SemanticExplorerCases.case_seqWrapPair__pl1,
  SemanticExplorerCases.case_seqWrapSolo__e,
  SemanticExplorerCases.case_seqWrapSolo__n0,
  SemanticExplorerCases.case_seqWrapSolo__n1,
  SemanticExplorerCases.case_seqWrapSolo__bt,
  SemanticExplorerCases.case_seqWrapSolo__bf,
  SemanticExplorerCases.case_seqWrapSolo__pbt,
  SemanticExplorerCases.case_seqWrapSolo__pbt_e,
  SemanticExplorerCases.case_seqWrapSolo__pbt_1,
  SemanticExplorerCases.case_seqWrapSolo__lbt,
  SemanticExplorerCases.case_seqWrapSolo__lbt_bf,
  SemanticExplorerCases.case_seqWrapSolo__lpbt_1,
  SemanticExplorerCases.case_seqWrapSolo__p1,
  SemanticExplorerCases.case_seqWrapSolo__p12,
  SemanticExplorerCases.case_seqWrapSolo__p123,
  SemanticExplorerCases.case_seqWrapSolo__pee,
  SemanticExplorerCases.case_seqWrapSolo__pe1,
  SemanticExplorerCases.case_seqWrapSolo__p1e,
  SemanticExplorerCases.case_seqWrapSolo__p12_3,
  SemanticExplorerCases.case_seqWrapSolo__p12_34,
  SemanticExplorerCases.case_seqWrapSolo__pe_12,
  SemanticExplorerCases.case_seqWrapSolo__ppe1_2,
  SemanticExplorerCases.case_seqWrapSolo__p12_e,
  SemanticExplorerCases.case_seqWrapSolo__ppe,
  SemanticExplorerCases.case_seqWrapSolo__pp1,
  SemanticExplorerCases.case_seqWrapSolo__ppp12,
  SemanticExplorerCases.case_seqWrapSolo__le,
  SemanticExplorerCases.case_seqWrapSolo__l7,
  SemanticExplorerCases.case_seqWrapSolo__l12,
  SemanticExplorerCases.case_seqWrapSolo__l12_3,
  SemanticExplorerCases.case_seqWrapSolo__lle,
  SemanticExplorerCases.case_seqWrapSolo__l_e,
  SemanticExplorerCases.case_seqWrapSolo__l_p12,
  SemanticExplorerCases.case_seqWrapSolo__p_l12,
  SemanticExplorerCases.case_seqWrapSolo__pl1,
  SemanticExplorerCases.case_spreadRoot__e,
  SemanticExplorerCases.case_spreadRoot__n0,
  SemanticExplorerCases.case_spreadRoot__n1,
  SemanticExplorerCases.case_spreadRoot__bt,
  SemanticExplorerCases.case_spreadRoot__bf,
  SemanticExplorerCases.case_spreadRoot__pbt,
  SemanticExplorerCases.case_spreadRoot__pbt_e,
  SemanticExplorerCases.case_spreadRoot__pbt_1,
  SemanticExplorerCases.case_spreadRoot__lbt,
  SemanticExplorerCases.case_spreadRoot__lbt_bf,
  SemanticExplorerCases.case_spreadRoot__lpbt_1,
  SemanticExplorerCases.case_spreadRoot__p1,
  SemanticExplorerCases.case_spreadRoot__p12,
  SemanticExplorerCases.case_spreadRoot__p123,
  SemanticExplorerCases.case_spreadRoot__pee,
  SemanticExplorerCases.case_spreadRoot__pe1,
  SemanticExplorerCases.case_spreadRoot__p1e,
  SemanticExplorerCases.case_spreadRoot__p12_3,
  SemanticExplorerCases.case_spreadRoot__p12_34,
  SemanticExplorerCases.case_spreadRoot__pe_12,
  SemanticExplorerCases.case_spreadRoot__ppe1_2,
  SemanticExplorerCases.case_spreadRoot__p12_e,
  SemanticExplorerCases.case_spreadRoot__ppe,
  SemanticExplorerCases.case_spreadRoot__pp1,
  SemanticExplorerCases.case_spreadRoot__ppp12,
  SemanticExplorerCases.case_spreadRoot__le,
  SemanticExplorerCases.case_spreadRoot__l7,
  SemanticExplorerCases.case_spreadRoot__l12,
  SemanticExplorerCases.case_spreadRoot__l12_3,
  SemanticExplorerCases.case_spreadRoot__lle,
  SemanticExplorerCases.case_spreadRoot__l_e,
  SemanticExplorerCases.case_spreadRoot__l_p12,
  SemanticExplorerCases.case_spreadRoot__p_l12,
  SemanticExplorerCases.case_spreadRoot__pl1,
  SemanticExplorerCases.case_spreadInSeq__e,
  SemanticExplorerCases.case_spreadInSeq__n0,
  SemanticExplorerCases.case_spreadInSeq__n1,
  SemanticExplorerCases.case_spreadInSeq__bt,
  SemanticExplorerCases.case_spreadInSeq__bf,
  SemanticExplorerCases.case_spreadInSeq__pbt,
  SemanticExplorerCases.case_spreadInSeq__pbt_e,
  SemanticExplorerCases.case_spreadInSeq__pbt_1,
  SemanticExplorerCases.case_spreadInSeq__lbt,
  SemanticExplorerCases.case_spreadInSeq__lbt_bf,
  SemanticExplorerCases.case_spreadInSeq__lpbt_1,
  SemanticExplorerCases.case_spreadInSeq__p1,
  SemanticExplorerCases.case_spreadInSeq__p12,
  SemanticExplorerCases.case_spreadInSeq__p123,
  SemanticExplorerCases.case_spreadInSeq__pee,
  SemanticExplorerCases.case_spreadInSeq__pe1,
  SemanticExplorerCases.case_spreadInSeq__p1e,
  SemanticExplorerCases.case_spreadInSeq__p12_3,
  SemanticExplorerCases.case_spreadInSeq__p12_34,
  SemanticExplorerCases.case_spreadInSeq__pe_12,
  SemanticExplorerCases.case_spreadInSeq__ppe1_2,
  SemanticExplorerCases.case_spreadInSeq__p12_e,
  SemanticExplorerCases.case_spreadInSeq__ppe,
  SemanticExplorerCases.case_spreadInSeq__pp1,
  SemanticExplorerCases.case_spreadInSeq__ppp12,
  SemanticExplorerCases.case_spreadInSeq__le,
  SemanticExplorerCases.case_spreadInSeq__l7,
  SemanticExplorerCases.case_spreadInSeq__l12,
  SemanticExplorerCases.case_spreadInSeq__l12_3,
  SemanticExplorerCases.case_spreadInSeq__lle,
  SemanticExplorerCases.case_spreadInSeq__l_e,
  SemanticExplorerCases.case_spreadInSeq__l_p12,
  SemanticExplorerCases.case_spreadInSeq__p_l12,
  SemanticExplorerCases.case_spreadInSeq__pl1,
  SemanticExplorerCases.case_count__e,
  SemanticExplorerCases.case_count__n0,
  SemanticExplorerCases.case_count__n1,
  SemanticExplorerCases.case_count__bt,
  SemanticExplorerCases.case_count__bf,
  SemanticExplorerCases.case_count__pbt,
  SemanticExplorerCases.case_count__pbt_e,
  SemanticExplorerCases.case_count__pbt_1,
  SemanticExplorerCases.case_count__lbt,
  SemanticExplorerCases.case_count__lbt_bf,
  SemanticExplorerCases.case_count__lpbt_1,
  SemanticExplorerCases.case_count__p1,
  SemanticExplorerCases.case_count__p12,
  SemanticExplorerCases.case_count__p123,
  SemanticExplorerCases.case_count__pee,
  SemanticExplorerCases.case_count__pe1,
  SemanticExplorerCases.case_count__p1e,
  SemanticExplorerCases.case_count__p12_3,
  SemanticExplorerCases.case_count__p12_34,
  SemanticExplorerCases.case_count__pe_12,
  SemanticExplorerCases.case_count__ppe1_2,
  SemanticExplorerCases.case_count__p12_e,
  SemanticExplorerCases.case_count__ppe,
  SemanticExplorerCases.case_count__pp1,
  SemanticExplorerCases.case_count__ppp12,
  SemanticExplorerCases.case_count__le,
  SemanticExplorerCases.case_count__l7,
  SemanticExplorerCases.case_count__l12,
  SemanticExplorerCases.case_count__l12_3,
  SemanticExplorerCases.case_count__lle,
  SemanticExplorerCases.case_count__l_e,
  SemanticExplorerCases.case_count__l_p12,
  SemanticExplorerCases.case_count__p_l12,
  SemanticExplorerCases.case_count__pl1,
  SemanticExplorerCases.case_countSpread__e,
  SemanticExplorerCases.case_countSpread__n0,
  SemanticExplorerCases.case_countSpread__n1,
  SemanticExplorerCases.case_countSpread__bt,
  SemanticExplorerCases.case_countSpread__bf,
  SemanticExplorerCases.case_countSpread__pbt,
  SemanticExplorerCases.case_countSpread__pbt_e,
  SemanticExplorerCases.case_countSpread__pbt_1,
  SemanticExplorerCases.case_countSpread__lbt,
  SemanticExplorerCases.case_countSpread__lbt_bf,
  SemanticExplorerCases.case_countSpread__lpbt_1,
  SemanticExplorerCases.case_countSpread__p1,
  SemanticExplorerCases.case_countSpread__p12,
  SemanticExplorerCases.case_countSpread__p123,
  SemanticExplorerCases.case_countSpread__pee,
  SemanticExplorerCases.case_countSpread__pe1,
  SemanticExplorerCases.case_countSpread__p1e,
  SemanticExplorerCases.case_countSpread__p12_3,
  SemanticExplorerCases.case_countSpread__p12_34,
  SemanticExplorerCases.case_countSpread__pe_12,
  SemanticExplorerCases.case_countSpread__ppe1_2,
  SemanticExplorerCases.case_countSpread__p12_e,
  SemanticExplorerCases.case_countSpread__ppe,
  SemanticExplorerCases.case_countSpread__pp1,
  SemanticExplorerCases.case_countSpread__ppp12,
  SemanticExplorerCases.case_countSpread__le,
  SemanticExplorerCases.case_countSpread__l7,
  SemanticExplorerCases.case_countSpread__l12,
  SemanticExplorerCases.case_countSpread__l12_3,
  SemanticExplorerCases.case_countSpread__lle,
  SemanticExplorerCases.case_countSpread__l_e,
  SemanticExplorerCases.case_countSpread__l_p12,
  SemanticExplorerCases.case_countSpread__p_l12,
  SemanticExplorerCases.case_countSpread__pl1,
  SemanticExplorerCases.case_dotCount__e,
  SemanticExplorerCases.case_dotCount__n0,
  SemanticExplorerCases.case_dotCount__n1,
  SemanticExplorerCases.case_dotCount__bt,
  SemanticExplorerCases.case_dotCount__bf,
  SemanticExplorerCases.case_dotCount__pbt,
  SemanticExplorerCases.case_dotCount__pbt_e,
  SemanticExplorerCases.case_dotCount__pbt_1,
  SemanticExplorerCases.case_dotCount__lbt,
  SemanticExplorerCases.case_dotCount__lbt_bf,
  SemanticExplorerCases.case_dotCount__lpbt_1,
  SemanticExplorerCases.case_dotCount__p1,
  SemanticExplorerCases.case_dotCount__p12,
  SemanticExplorerCases.case_dotCount__p123,
  SemanticExplorerCases.case_dotCount__pee,
  SemanticExplorerCases.case_dotCount__pe1,
  SemanticExplorerCases.case_dotCount__p1e,
  SemanticExplorerCases.case_dotCount__p12_3,
  SemanticExplorerCases.case_dotCount__p12_34,
  SemanticExplorerCases.case_dotCount__pe_12,
  SemanticExplorerCases.case_dotCount__ppe1_2,
  SemanticExplorerCases.case_dotCount__p12_e,
  SemanticExplorerCases.case_dotCount__ppe,
  SemanticExplorerCases.case_dotCount__pp1,
  SemanticExplorerCases.case_dotCount__ppp12,
  SemanticExplorerCases.case_dotCount__le,
  SemanticExplorerCases.case_dotCount__l7,
  SemanticExplorerCases.case_dotCount__l12,
  SemanticExplorerCases.case_dotCount__l12_3,
  SemanticExplorerCases.case_dotCount__lle,
  SemanticExplorerCases.case_dotCount__l_e,
  SemanticExplorerCases.case_dotCount__l_p12,
  SemanticExplorerCases.case_dotCount__p_l12,
  SemanticExplorerCases.case_dotCount__pl1,
  SemanticExplorerCases.case_literalDotCount__e,
  SemanticExplorerCases.case_literalDotCount__n0,
  SemanticExplorerCases.case_literalDotCount__n1,
  SemanticExplorerCases.case_literalDotCount__bt,
  SemanticExplorerCases.case_literalDotCount__bf,
  SemanticExplorerCases.case_literalDotCount__pbt,
  SemanticExplorerCases.case_literalDotCount__pbt_e,
  SemanticExplorerCases.case_literalDotCount__pbt_1,
  SemanticExplorerCases.case_literalDotCount__lbt,
  SemanticExplorerCases.case_literalDotCount__lbt_bf,
  SemanticExplorerCases.case_literalDotCount__lpbt_1,
  SemanticExplorerCases.case_literalDotCount__p1,
  SemanticExplorerCases.case_literalDotCount__p12,
  SemanticExplorerCases.case_literalDotCount__p123,
  SemanticExplorerCases.case_literalDotCount__pee,
  SemanticExplorerCases.case_literalDotCount__pe1,
  SemanticExplorerCases.case_literalDotCount__p1e,
  SemanticExplorerCases.case_literalDotCount__p12_3,
  SemanticExplorerCases.case_literalDotCount__p12_34,
  SemanticExplorerCases.case_literalDotCount__pe_12,
  SemanticExplorerCases.case_literalDotCount__ppe1_2,
  SemanticExplorerCases.case_literalDotCount__p12_e,
  SemanticExplorerCases.case_literalDotCount__ppe,
  SemanticExplorerCases.case_literalDotCount__pp1,
  SemanticExplorerCases.case_literalDotCount__ppp12,
  SemanticExplorerCases.case_literalDotCount__le,
  SemanticExplorerCases.case_literalDotCount__l7,
  SemanticExplorerCases.case_literalDotCount__l12,
  SemanticExplorerCases.case_literalDotCount__l12_3,
  SemanticExplorerCases.case_literalDotCount__lle,
  SemanticExplorerCases.case_literalDotCount__l_e,
  SemanticExplorerCases.case_literalDotCount__l_p12,
  SemanticExplorerCases.case_literalDotCount__p_l12,
  SemanticExplorerCases.case_literalDotCount__pl1,
  SemanticExplorerCases.case_index0__e,
  SemanticExplorerCases.case_index0__n0,
  SemanticExplorerCases.case_index0__n1,
  SemanticExplorerCases.case_index0__bt,
  SemanticExplorerCases.case_index0__bf,
  SemanticExplorerCases.case_index0__pbt,
  SemanticExplorerCases.case_index0__pbt_e,
  SemanticExplorerCases.case_index0__pbt_1,
  SemanticExplorerCases.case_index0__lbt,
  SemanticExplorerCases.case_index0__lbt_bf,
  SemanticExplorerCases.case_index0__lpbt_1,
  SemanticExplorerCases.case_index0__p1,
  SemanticExplorerCases.case_index0__p12,
  SemanticExplorerCases.case_index0__p123,
  SemanticExplorerCases.case_index0__pee,
  SemanticExplorerCases.case_index0__pe1,
  SemanticExplorerCases.case_index0__p1e,
  SemanticExplorerCases.case_index0__p12_3,
  SemanticExplorerCases.case_index0__p12_34,
  SemanticExplorerCases.case_index0__pe_12,
  SemanticExplorerCases.case_index0__ppe1_2,
  SemanticExplorerCases.case_index0__p12_e,
  SemanticExplorerCases.case_index0__ppe,
  SemanticExplorerCases.case_index0__pp1,
  SemanticExplorerCases.case_index0__ppp12,
  SemanticExplorerCases.case_index0__le,
  SemanticExplorerCases.case_index0__l7,
  SemanticExplorerCases.case_index0__l12,
  SemanticExplorerCases.case_index0__l12_3,
  SemanticExplorerCases.case_index0__lle,
  SemanticExplorerCases.case_index0__l_e,
  SemanticExplorerCases.case_index0__l_p12,
  SemanticExplorerCases.case_index0__p_l12,
  SemanticExplorerCases.case_index0__pl1,
  SemanticExplorerCases.case_index1__e,
  SemanticExplorerCases.case_index1__n0,
  SemanticExplorerCases.case_index1__n1,
  SemanticExplorerCases.case_index1__bt,
  SemanticExplorerCases.case_index1__bf,
  SemanticExplorerCases.case_index1__pbt,
  SemanticExplorerCases.case_index1__pbt_e,
  SemanticExplorerCases.case_index1__pbt_1,
  SemanticExplorerCases.case_index1__lbt,
  SemanticExplorerCases.case_index1__lbt_bf,
  SemanticExplorerCases.case_index1__lpbt_1,
  SemanticExplorerCases.case_index1__p1,
  SemanticExplorerCases.case_index1__p12,
  SemanticExplorerCases.case_index1__p123,
  SemanticExplorerCases.case_index1__pee,
  SemanticExplorerCases.case_index1__pe1,
  SemanticExplorerCases.case_index1__p1e,
  SemanticExplorerCases.case_index1__p12_3,
  SemanticExplorerCases.case_index1__p12_34,
  SemanticExplorerCases.case_index1__pe_12,
  SemanticExplorerCases.case_index1__ppe1_2,
  SemanticExplorerCases.case_index1__p12_e,
  SemanticExplorerCases.case_index1__ppe,
  SemanticExplorerCases.case_index1__pp1,
  SemanticExplorerCases.case_index1__ppp12,
  SemanticExplorerCases.case_index1__le,
  SemanticExplorerCases.case_index1__l7,
  SemanticExplorerCases.case_index1__l12,
  SemanticExplorerCases.case_index1__l12_3,
  SemanticExplorerCases.case_index1__lle,
  SemanticExplorerCases.case_index1__l_e,
  SemanticExplorerCases.case_index1__l_p12,
  SemanticExplorerCases.case_index1__p_l12,
  SemanticExplorerCases.case_index1__pl1,
  SemanticExplorerCases.case_indexBig__e,
  SemanticExplorerCases.case_indexBig__n0,
  SemanticExplorerCases.case_indexBig__n1,
  SemanticExplorerCases.case_indexBig__bt,
  SemanticExplorerCases.case_indexBig__bf,
  SemanticExplorerCases.case_indexBig__pbt,
  SemanticExplorerCases.case_indexBig__pbt_e,
  SemanticExplorerCases.case_indexBig__pbt_1,
  SemanticExplorerCases.case_indexBig__lbt,
  SemanticExplorerCases.case_indexBig__lbt_bf,
  SemanticExplorerCases.case_indexBig__lpbt_1,
  SemanticExplorerCases.case_indexBig__p1,
  SemanticExplorerCases.case_indexBig__p12,
  SemanticExplorerCases.case_indexBig__p123,
  SemanticExplorerCases.case_indexBig__pee,
  SemanticExplorerCases.case_indexBig__pe1,
  SemanticExplorerCases.case_indexBig__p1e,
  SemanticExplorerCases.case_indexBig__p12_3,
  SemanticExplorerCases.case_indexBig__p12_34,
  SemanticExplorerCases.case_indexBig__pe_12,
  SemanticExplorerCases.case_indexBig__ppe1_2,
  SemanticExplorerCases.case_indexBig__p12_e,
  SemanticExplorerCases.case_indexBig__ppe,
  SemanticExplorerCases.case_indexBig__pp1,
  SemanticExplorerCases.case_indexBig__ppp12,
  SemanticExplorerCases.case_indexBig__le,
  SemanticExplorerCases.case_indexBig__l7,
  SemanticExplorerCases.case_indexBig__l12,
  SemanticExplorerCases.case_indexBig__l12_3,
  SemanticExplorerCases.case_indexBig__lle,
  SemanticExplorerCases.case_indexBig__l_e,
  SemanticExplorerCases.case_indexBig__l_p12,
  SemanticExplorerCases.case_indexBig__p_l12,
  SemanticExplorerCases.case_indexBig__pl1,
  SemanticExplorerCases.case_indexNeg__e,
  SemanticExplorerCases.case_indexNeg__n0,
  SemanticExplorerCases.case_indexNeg__n1,
  SemanticExplorerCases.case_indexNeg__bt,
  SemanticExplorerCases.case_indexNeg__bf,
  SemanticExplorerCases.case_indexNeg__pbt,
  SemanticExplorerCases.case_indexNeg__pbt_e,
  SemanticExplorerCases.case_indexNeg__pbt_1,
  SemanticExplorerCases.case_indexNeg__lbt,
  SemanticExplorerCases.case_indexNeg__lbt_bf,
  SemanticExplorerCases.case_indexNeg__lpbt_1,
  SemanticExplorerCases.case_indexNeg__p1,
  SemanticExplorerCases.case_indexNeg__p12,
  SemanticExplorerCases.case_indexNeg__p123,
  SemanticExplorerCases.case_indexNeg__pee,
  SemanticExplorerCases.case_indexNeg__pe1,
  SemanticExplorerCases.case_indexNeg__p1e,
  SemanticExplorerCases.case_indexNeg__p12_3,
  SemanticExplorerCases.case_indexNeg__p12_34,
  SemanticExplorerCases.case_indexNeg__pe_12,
  SemanticExplorerCases.case_indexNeg__ppe1_2,
  SemanticExplorerCases.case_indexNeg__p12_e,
  SemanticExplorerCases.case_indexNeg__ppe,
  SemanticExplorerCases.case_indexNeg__pp1,
  SemanticExplorerCases.case_indexNeg__ppp12,
  SemanticExplorerCases.case_indexNeg__le,
  SemanticExplorerCases.case_indexNeg__l7,
  SemanticExplorerCases.case_indexNeg__l12,
  SemanticExplorerCases.case_indexNeg__l12_3,
  SemanticExplorerCases.case_indexNeg__lle,
  SemanticExplorerCases.case_indexNeg__l_e,
  SemanticExplorerCases.case_indexNeg__l_p12,
  SemanticExplorerCases.case_indexNeg__p_l12,
  SemanticExplorerCases.case_indexNeg__pl1,
  SemanticExplorerCases.case_eqSelf__e,
  SemanticExplorerCases.case_eqSelf__n0,
  SemanticExplorerCases.case_eqSelf__n1,
  SemanticExplorerCases.case_eqSelf__bt,
  SemanticExplorerCases.case_eqSelf__bf,
  SemanticExplorerCases.case_eqSelf__pbt,
  SemanticExplorerCases.case_eqSelf__pbt_e,
  SemanticExplorerCases.case_eqSelf__pbt_1,
  SemanticExplorerCases.case_eqSelf__lbt,
  SemanticExplorerCases.case_eqSelf__lbt_bf,
  SemanticExplorerCases.case_eqSelf__lpbt_1,
  SemanticExplorerCases.case_eqSelf__p1,
  SemanticExplorerCases.case_eqSelf__p12,
  SemanticExplorerCases.case_eqSelf__p123,
  SemanticExplorerCases.case_eqSelf__pee,
  SemanticExplorerCases.case_eqSelf__pe1,
  SemanticExplorerCases.case_eqSelf__p1e,
  SemanticExplorerCases.case_eqSelf__p12_3,
  SemanticExplorerCases.case_eqSelf__p12_34,
  SemanticExplorerCases.case_eqSelf__pe_12,
  SemanticExplorerCases.case_eqSelf__ppe1_2,
  SemanticExplorerCases.case_eqSelf__p12_e,
  SemanticExplorerCases.case_eqSelf__ppe,
  SemanticExplorerCases.case_eqSelf__pp1,
  SemanticExplorerCases.case_eqSelf__ppp12,
  SemanticExplorerCases.case_eqSelf__le,
  SemanticExplorerCases.case_eqSelf__l7,
  SemanticExplorerCases.case_eqSelf__l12,
  SemanticExplorerCases.case_eqSelf__l12_3,
  SemanticExplorerCases.case_eqSelf__lle,
  SemanticExplorerCases.case_eqSelf__l_e,
  SemanticExplorerCases.case_eqSelf__l_p12,
  SemanticExplorerCases.case_eqSelf__p_l12,
  SemanticExplorerCases.case_eqSelf__pl1,
  SemanticExplorerCases.case_neqSelf__e,
  SemanticExplorerCases.case_neqSelf__n0,
  SemanticExplorerCases.case_neqSelf__n1,
  SemanticExplorerCases.case_neqSelf__bt,
  SemanticExplorerCases.case_neqSelf__bf,
  SemanticExplorerCases.case_neqSelf__pbt,
  SemanticExplorerCases.case_neqSelf__pbt_e,
  SemanticExplorerCases.case_neqSelf__pbt_1,
  SemanticExplorerCases.case_neqSelf__lbt,
  SemanticExplorerCases.case_neqSelf__lbt_bf,
  SemanticExplorerCases.case_neqSelf__lpbt_1,
  SemanticExplorerCases.case_neqSelf__p1,
  SemanticExplorerCases.case_neqSelf__p12,
  SemanticExplorerCases.case_neqSelf__p123,
  SemanticExplorerCases.case_neqSelf__pee,
  SemanticExplorerCases.case_neqSelf__pe1,
  SemanticExplorerCases.case_neqSelf__p1e,
  SemanticExplorerCases.case_neqSelf__p12_3,
  SemanticExplorerCases.case_neqSelf__p12_34,
  SemanticExplorerCases.case_neqSelf__pe_12,
  SemanticExplorerCases.case_neqSelf__ppe1_2,
  SemanticExplorerCases.case_neqSelf__p12_e,
  SemanticExplorerCases.case_neqSelf__ppe,
  SemanticExplorerCases.case_neqSelf__pp1,
  SemanticExplorerCases.case_neqSelf__ppp12,
  SemanticExplorerCases.case_neqSelf__le,
  SemanticExplorerCases.case_neqSelf__l7,
  SemanticExplorerCases.case_neqSelf__l12,
  SemanticExplorerCases.case_neqSelf__l12_3,
  SemanticExplorerCases.case_neqSelf__lle,
  SemanticExplorerCases.case_neqSelf__l_e,
  SemanticExplorerCases.case_neqSelf__l_p12,
  SemanticExplorerCases.case_neqSelf__p_l12,
  SemanticExplorerCases.case_neqSelf__pl1,
  SemanticExplorerCases.case_eqIdentity__e,
  SemanticExplorerCases.case_eqIdentity__n0,
  SemanticExplorerCases.case_eqIdentity__n1,
  SemanticExplorerCases.case_eqIdentity__bt,
  SemanticExplorerCases.case_eqIdentity__bf,
  SemanticExplorerCases.case_eqIdentity__pbt,
  SemanticExplorerCases.case_eqIdentity__pbt_e,
  SemanticExplorerCases.case_eqIdentity__pbt_1,
  SemanticExplorerCases.case_eqIdentity__lbt,
  SemanticExplorerCases.case_eqIdentity__lbt_bf,
  SemanticExplorerCases.case_eqIdentity__lpbt_1,
  SemanticExplorerCases.case_eqIdentity__p1,
  SemanticExplorerCases.case_eqIdentity__p12,
  SemanticExplorerCases.case_eqIdentity__p123,
  SemanticExplorerCases.case_eqIdentity__pee,
  SemanticExplorerCases.case_eqIdentity__pe1,
  SemanticExplorerCases.case_eqIdentity__p1e,
  SemanticExplorerCases.case_eqIdentity__p12_3,
  SemanticExplorerCases.case_eqIdentity__p12_34,
  SemanticExplorerCases.case_eqIdentity__pe_12,
  SemanticExplorerCases.case_eqIdentity__ppe1_2,
  SemanticExplorerCases.case_eqIdentity__p12_e,
  SemanticExplorerCases.case_eqIdentity__ppe,
  SemanticExplorerCases.case_eqIdentity__pp1,
  SemanticExplorerCases.case_eqIdentity__ppp12,
  SemanticExplorerCases.case_eqIdentity__le,
  SemanticExplorerCases.case_eqIdentity__l7,
  SemanticExplorerCases.case_eqIdentity__l12,
  SemanticExplorerCases.case_eqIdentity__l12_3,
  SemanticExplorerCases.case_eqIdentity__lle,
  SemanticExplorerCases.case_eqIdentity__l_e,
  SemanticExplorerCases.case_eqIdentity__l_p12,
  SemanticExplorerCases.case_eqIdentity__p_l12,
  SemanticExplorerCases.case_eqIdentity__pl1,
  SemanticExplorerCases.case_identity__e,
  SemanticExplorerCases.case_identity__n0,
  SemanticExplorerCases.case_identity__n1,
  SemanticExplorerCases.case_identity__bt,
  SemanticExplorerCases.case_identity__bf,
  SemanticExplorerCases.case_identity__pbt,
  SemanticExplorerCases.case_identity__pbt_e,
  SemanticExplorerCases.case_identity__pbt_1,
  SemanticExplorerCases.case_identity__lbt,
  SemanticExplorerCases.case_identity__lbt_bf,
  SemanticExplorerCases.case_identity__lpbt_1,
  SemanticExplorerCases.case_identity__p1,
  SemanticExplorerCases.case_identity__p12,
  SemanticExplorerCases.case_identity__p123,
  SemanticExplorerCases.case_identity__pee,
  SemanticExplorerCases.case_identity__pe1,
  SemanticExplorerCases.case_identity__p1e,
  SemanticExplorerCases.case_identity__p12_3,
  SemanticExplorerCases.case_identity__p12_34,
  SemanticExplorerCases.case_identity__pe_12,
  SemanticExplorerCases.case_identity__ppe1_2,
  SemanticExplorerCases.case_identity__p12_e,
  SemanticExplorerCases.case_identity__ppe,
  SemanticExplorerCases.case_identity__pp1,
  SemanticExplorerCases.case_identity__ppp12,
  SemanticExplorerCases.case_identity__le,
  SemanticExplorerCases.case_identity__l7,
  SemanticExplorerCases.case_identity__l12,
  SemanticExplorerCases.case_identity__l12_3,
  SemanticExplorerCases.case_identity__lle,
  SemanticExplorerCases.case_identity__l_e,
  SemanticExplorerCases.case_identity__l_p12,
  SemanticExplorerCases.case_identity__p_l12,
  SemanticExplorerCases.case_identity__pl1,
  SemanticExplorerCases.case_identityTwice__e,
  SemanticExplorerCases.case_identityTwice__n0,
  SemanticExplorerCases.case_identityTwice__n1,
  SemanticExplorerCases.case_identityTwice__bt,
  SemanticExplorerCases.case_identityTwice__bf,
  SemanticExplorerCases.case_identityTwice__pbt,
  SemanticExplorerCases.case_identityTwice__pbt_e,
  SemanticExplorerCases.case_identityTwice__pbt_1,
  SemanticExplorerCases.case_identityTwice__lbt,
  SemanticExplorerCases.case_identityTwice__lbt_bf,
  SemanticExplorerCases.case_identityTwice__lpbt_1,
  SemanticExplorerCases.case_identityTwice__p1,
  SemanticExplorerCases.case_identityTwice__p12,
  SemanticExplorerCases.case_identityTwice__p123,
  SemanticExplorerCases.case_identityTwice__pee,
  SemanticExplorerCases.case_identityTwice__pe1,
  SemanticExplorerCases.case_identityTwice__p1e,
  SemanticExplorerCases.case_identityTwice__p12_3,
  SemanticExplorerCases.case_identityTwice__p12_34,
  SemanticExplorerCases.case_identityTwice__pe_12,
  SemanticExplorerCases.case_identityTwice__ppe1_2,
  SemanticExplorerCases.case_identityTwice__p12_e,
  SemanticExplorerCases.case_identityTwice__ppe,
  SemanticExplorerCases.case_identityTwice__pp1,
  SemanticExplorerCases.case_identityTwice__ppp12,
  SemanticExplorerCases.case_identityTwice__le,
  SemanticExplorerCases.case_identityTwice__l7,
  SemanticExplorerCases.case_identityTwice__l12,
  SemanticExplorerCases.case_identityTwice__l12_3,
  SemanticExplorerCases.case_identityTwice__lle,
  SemanticExplorerCases.case_identityTwice__l_e,
  SemanticExplorerCases.case_identityTwice__l_p12,
  SemanticExplorerCases.case_identityTwice__p_l12,
  SemanticExplorerCases.case_identityTwice__pl1,
  SemanticExplorerCases.case_propChain__e,
  SemanticExplorerCases.case_propChain__n0,
  SemanticExplorerCases.case_propChain__n1,
  SemanticExplorerCases.case_propChain__bt,
  SemanticExplorerCases.case_propChain__bf,
  SemanticExplorerCases.case_propChain__pbt,
  SemanticExplorerCases.case_propChain__pbt_e,
  SemanticExplorerCases.case_propChain__pbt_1,
  SemanticExplorerCases.case_propChain__lbt,
  SemanticExplorerCases.case_propChain__lbt_bf,
  SemanticExplorerCases.case_propChain__lpbt_1,
  SemanticExplorerCases.case_propChain__p1,
  SemanticExplorerCases.case_propChain__p12,
  SemanticExplorerCases.case_propChain__p123,
  SemanticExplorerCases.case_propChain__pee,
  SemanticExplorerCases.case_propChain__pe1,
  SemanticExplorerCases.case_propChain__p1e,
  SemanticExplorerCases.case_propChain__p12_3,
  SemanticExplorerCases.case_propChain__p12_34,
  SemanticExplorerCases.case_propChain__pe_12,
  SemanticExplorerCases.case_propChain__ppe1_2,
  SemanticExplorerCases.case_propChain__p12_e,
  SemanticExplorerCases.case_propChain__ppe,
  SemanticExplorerCases.case_propChain__pp1,
  SemanticExplorerCases.case_propChain__ppp12,
  SemanticExplorerCases.case_propChain__le,
  SemanticExplorerCases.case_propChain__l7,
  SemanticExplorerCases.case_propChain__l12,
  SemanticExplorerCases.case_propChain__l12_3,
  SemanticExplorerCases.case_propChain__lle,
  SemanticExplorerCases.case_propChain__l_e,
  SemanticExplorerCases.case_propChain__l_p12,
  SemanticExplorerCases.case_propChain__p_l12,
  SemanticExplorerCases.case_propChain__pl1,
  SemanticExplorerCases.case_take1__e,
  SemanticExplorerCases.case_take1__n0,
  SemanticExplorerCases.case_take1__n1,
  SemanticExplorerCases.case_take1__bt,
  SemanticExplorerCases.case_take1__bf,
  SemanticExplorerCases.case_take1__pbt,
  SemanticExplorerCases.case_take1__pbt_e,
  SemanticExplorerCases.case_take1__pbt_1,
  SemanticExplorerCases.case_take1__lbt,
  SemanticExplorerCases.case_take1__lbt_bf,
  SemanticExplorerCases.case_take1__lpbt_1,
  SemanticExplorerCases.case_take1__p1,
  SemanticExplorerCases.case_take1__p12,
  SemanticExplorerCases.case_take1__p123,
  SemanticExplorerCases.case_take1__pee,
  SemanticExplorerCases.case_take1__pe1,
  SemanticExplorerCases.case_take1__p1e,
  SemanticExplorerCases.case_take1__p12_3,
  SemanticExplorerCases.case_take1__p12_34,
  SemanticExplorerCases.case_take1__pe_12,
  SemanticExplorerCases.case_take1__ppe1_2,
  SemanticExplorerCases.case_take1__p12_e,
  SemanticExplorerCases.case_take1__ppe,
  SemanticExplorerCases.case_take1__pp1,
  SemanticExplorerCases.case_take1__ppp12,
  SemanticExplorerCases.case_take1__le,
  SemanticExplorerCases.case_take1__l7,
  SemanticExplorerCases.case_take1__l12,
  SemanticExplorerCases.case_take1__l12_3,
  SemanticExplorerCases.case_take1__lle,
  SemanticExplorerCases.case_take1__l_e,
  SemanticExplorerCases.case_take1__l_p12,
  SemanticExplorerCases.case_take1__p_l12,
  SemanticExplorerCases.case_take1__pl1,
  SemanticExplorerCases.case_take9__e,
  SemanticExplorerCases.case_take9__n0,
  SemanticExplorerCases.case_take9__n1,
  SemanticExplorerCases.case_take9__bt,
  SemanticExplorerCases.case_take9__bf,
  SemanticExplorerCases.case_take9__pbt,
  SemanticExplorerCases.case_take9__pbt_e,
  SemanticExplorerCases.case_take9__pbt_1,
  SemanticExplorerCases.case_take9__lbt,
  SemanticExplorerCases.case_take9__lbt_bf,
  SemanticExplorerCases.case_take9__lpbt_1,
  SemanticExplorerCases.case_take9__p1,
  SemanticExplorerCases.case_take9__p12,
  SemanticExplorerCases.case_take9__p123,
  SemanticExplorerCases.case_take9__pee,
  SemanticExplorerCases.case_take9__pe1,
  SemanticExplorerCases.case_take9__p1e,
  SemanticExplorerCases.case_take9__p12_3,
  SemanticExplorerCases.case_take9__p12_34,
  SemanticExplorerCases.case_take9__pe_12,
  SemanticExplorerCases.case_take9__ppe1_2,
  SemanticExplorerCases.case_take9__p12_e,
  SemanticExplorerCases.case_take9__ppe,
  SemanticExplorerCases.case_take9__pp1,
  SemanticExplorerCases.case_take9__ppp12,
  SemanticExplorerCases.case_take9__le,
  SemanticExplorerCases.case_take9__l7,
  SemanticExplorerCases.case_take9__l12,
  SemanticExplorerCases.case_take9__l12_3,
  SemanticExplorerCases.case_take9__lle,
  SemanticExplorerCases.case_take9__l_e,
  SemanticExplorerCases.case_take9__l_p12,
  SemanticExplorerCases.case_take9__p_l12,
  SemanticExplorerCases.case_take9__pl1,
  SemanticExplorerCases.case_skip1__e,
  SemanticExplorerCases.case_skip1__n0,
  SemanticExplorerCases.case_skip1__n1,
  SemanticExplorerCases.case_skip1__bt,
  SemanticExplorerCases.case_skip1__bf,
  SemanticExplorerCases.case_skip1__pbt,
  SemanticExplorerCases.case_skip1__pbt_e,
  SemanticExplorerCases.case_skip1__pbt_1,
  SemanticExplorerCases.case_skip1__lbt,
  SemanticExplorerCases.case_skip1__lbt_bf,
  SemanticExplorerCases.case_skip1__lpbt_1,
  SemanticExplorerCases.case_skip1__p1,
  SemanticExplorerCases.case_skip1__p12,
  SemanticExplorerCases.case_skip1__p123,
  SemanticExplorerCases.case_skip1__pee,
  SemanticExplorerCases.case_skip1__pe1,
  SemanticExplorerCases.case_skip1__p1e,
  SemanticExplorerCases.case_skip1__p12_3,
  SemanticExplorerCases.case_skip1__p12_34,
  SemanticExplorerCases.case_skip1__pe_12,
  SemanticExplorerCases.case_skip1__ppe1_2,
  SemanticExplorerCases.case_skip1__p12_e,
  SemanticExplorerCases.case_skip1__ppe,
  SemanticExplorerCases.case_skip1__pp1,
  SemanticExplorerCases.case_skip1__ppp12,
  SemanticExplorerCases.case_skip1__le,
  SemanticExplorerCases.case_skip1__l7,
  SemanticExplorerCases.case_skip1__l12,
  SemanticExplorerCases.case_skip1__l12_3,
  SemanticExplorerCases.case_skip1__lle,
  SemanticExplorerCases.case_skip1__l_e,
  SemanticExplorerCases.case_skip1__l_p12,
  SemanticExplorerCases.case_skip1__p_l12,
  SemanticExplorerCases.case_skip1__pl1,
  SemanticExplorerCases.case_distinct__e,
  SemanticExplorerCases.case_distinct__n0,
  SemanticExplorerCases.case_distinct__n1,
  SemanticExplorerCases.case_distinct__bt,
  SemanticExplorerCases.case_distinct__bf,
  SemanticExplorerCases.case_distinct__pbt,
  SemanticExplorerCases.case_distinct__pbt_e,
  SemanticExplorerCases.case_distinct__pbt_1,
  SemanticExplorerCases.case_distinct__lbt,
  SemanticExplorerCases.case_distinct__lbt_bf,
  SemanticExplorerCases.case_distinct__lpbt_1,
  SemanticExplorerCases.case_distinct__p1,
  SemanticExplorerCases.case_distinct__p12,
  SemanticExplorerCases.case_distinct__p123,
  SemanticExplorerCases.case_distinct__pee,
  SemanticExplorerCases.case_distinct__pe1,
  SemanticExplorerCases.case_distinct__p1e,
  SemanticExplorerCases.case_distinct__p12_3,
  SemanticExplorerCases.case_distinct__p12_34,
  SemanticExplorerCases.case_distinct__pe_12,
  SemanticExplorerCases.case_distinct__ppe1_2,
  SemanticExplorerCases.case_distinct__p12_e,
  SemanticExplorerCases.case_distinct__ppe,
  SemanticExplorerCases.case_distinct__pp1,
  SemanticExplorerCases.case_distinct__ppp12,
  SemanticExplorerCases.case_distinct__le,
  SemanticExplorerCases.case_distinct__l7,
  SemanticExplorerCases.case_distinct__l12,
  SemanticExplorerCases.case_distinct__l12_3,
  SemanticExplorerCases.case_distinct__lle,
  SemanticExplorerCases.case_distinct__l_e,
  SemanticExplorerCases.case_distinct__l_p12,
  SemanticExplorerCases.case_distinct__p_l12,
  SemanticExplorerCases.case_distinct__pl1,
  SemanticExplorerCases.case_order__e,
  SemanticExplorerCases.case_order__n0,
  SemanticExplorerCases.case_order__n1,
  SemanticExplorerCases.case_order__bt,
  SemanticExplorerCases.case_order__bf,
  SemanticExplorerCases.case_order__pbt,
  SemanticExplorerCases.case_order__pbt_e,
  SemanticExplorerCases.case_order__pbt_1,
  SemanticExplorerCases.case_order__lbt,
  SemanticExplorerCases.case_order__lbt_bf,
  SemanticExplorerCases.case_order__lpbt_1,
  SemanticExplorerCases.case_order__p1,
  SemanticExplorerCases.case_order__p12,
  SemanticExplorerCases.case_order__p123,
  SemanticExplorerCases.case_order__pee,
  SemanticExplorerCases.case_order__pe1,
  SemanticExplorerCases.case_order__p1e,
  SemanticExplorerCases.case_order__p12_3,
  SemanticExplorerCases.case_order__p12_34,
  SemanticExplorerCases.case_order__pe_12,
  SemanticExplorerCases.case_order__ppe1_2,
  SemanticExplorerCases.case_order__p12_e,
  SemanticExplorerCases.case_order__ppe,
  SemanticExplorerCases.case_order__pp1,
  SemanticExplorerCases.case_order__ppp12,
  SemanticExplorerCases.case_order__le,
  SemanticExplorerCases.case_order__l7,
  SemanticExplorerCases.case_order__l12,
  SemanticExplorerCases.case_order__l12_3,
  SemanticExplorerCases.case_order__lle,
  SemanticExplorerCases.case_order__l_e,
  SemanticExplorerCases.case_order__l_p12,
  SemanticExplorerCases.case_order__p_l12,
  SemanticExplorerCases.case_order__pl1,
  SemanticExplorerCases.case_mapId__e,
  SemanticExplorerCases.case_mapId__n0,
  SemanticExplorerCases.case_mapId__n1,
  SemanticExplorerCases.case_mapId__bt,
  SemanticExplorerCases.case_mapId__bf,
  SemanticExplorerCases.case_mapId__pbt,
  SemanticExplorerCases.case_mapId__pbt_e,
  SemanticExplorerCases.case_mapId__pbt_1,
  SemanticExplorerCases.case_mapId__lbt,
  SemanticExplorerCases.case_mapId__lbt_bf,
  SemanticExplorerCases.case_mapId__lpbt_1,
  SemanticExplorerCases.case_mapId__p1,
  SemanticExplorerCases.case_mapId__p12,
  SemanticExplorerCases.case_mapId__p123,
  SemanticExplorerCases.case_mapId__pee,
  SemanticExplorerCases.case_mapId__pe1,
  SemanticExplorerCases.case_mapId__p1e,
  SemanticExplorerCases.case_mapId__p12_3,
  SemanticExplorerCases.case_mapId__p12_34,
  SemanticExplorerCases.case_mapId__pe_12,
  SemanticExplorerCases.case_mapId__ppe1_2,
  SemanticExplorerCases.case_mapId__p12_e,
  SemanticExplorerCases.case_mapId__ppe,
  SemanticExplorerCases.case_mapId__pp1,
  SemanticExplorerCases.case_mapId__ppp12,
  SemanticExplorerCases.case_mapId__le,
  SemanticExplorerCases.case_mapId__l7,
  SemanticExplorerCases.case_mapId__l12,
  SemanticExplorerCases.case_mapId__l12_3,
  SemanticExplorerCases.case_mapId__lle,
  SemanticExplorerCases.case_mapId__l_e,
  SemanticExplorerCases.case_mapId__l_p12,
  SemanticExplorerCases.case_mapId__p_l12,
  SemanticExplorerCases.case_mapId__pl1,
  SemanticExplorerCases.case_patternHead__e,
  SemanticExplorerCases.case_patternHead__n0,
  SemanticExplorerCases.case_patternHead__n1,
  SemanticExplorerCases.case_patternHead__bt,
  SemanticExplorerCases.case_patternHead__bf,
  SemanticExplorerCases.case_patternHead__pbt,
  SemanticExplorerCases.case_patternHead__pbt_e,
  SemanticExplorerCases.case_patternHead__pbt_1,
  SemanticExplorerCases.case_patternHead__lbt,
  SemanticExplorerCases.case_patternHead__lbt_bf,
  SemanticExplorerCases.case_patternHead__lpbt_1,
  SemanticExplorerCases.case_patternHead__p1,
  SemanticExplorerCases.case_patternHead__p12,
  SemanticExplorerCases.case_patternHead__p123,
  SemanticExplorerCases.case_patternHead__pee,
  SemanticExplorerCases.case_patternHead__pe1,
  SemanticExplorerCases.case_patternHead__p1e,
  SemanticExplorerCases.case_patternHead__p12_3,
  SemanticExplorerCases.case_patternHead__p12_34,
  SemanticExplorerCases.case_patternHead__pe_12,
  SemanticExplorerCases.case_patternHead__ppe1_2,
  SemanticExplorerCases.case_patternHead__p12_e,
  SemanticExplorerCases.case_patternHead__ppe,
  SemanticExplorerCases.case_patternHead__pp1,
  SemanticExplorerCases.case_patternHead__ppp12,
  SemanticExplorerCases.case_patternHead__le,
  SemanticExplorerCases.case_patternHead__l7,
  SemanticExplorerCases.case_patternHead__l12,
  SemanticExplorerCases.case_patternHead__l12_3,
  SemanticExplorerCases.case_patternHead__lle,
  SemanticExplorerCases.case_patternHead__l_e,
  SemanticExplorerCases.case_patternHead__l_p12,
  SemanticExplorerCases.case_patternHead__p_l12,
  SemanticExplorerCases.case_patternHead__pl1,
  SemanticExplorerCases.case_patternHeadMap__e,
  SemanticExplorerCases.case_patternHeadMap__n0,
  SemanticExplorerCases.case_patternHeadMap__n1,
  SemanticExplorerCases.case_patternHeadMap__bt,
  SemanticExplorerCases.case_patternHeadMap__bf,
  SemanticExplorerCases.case_patternHeadMap__pbt,
  SemanticExplorerCases.case_patternHeadMap__pbt_e,
  SemanticExplorerCases.case_patternHeadMap__pbt_1,
  SemanticExplorerCases.case_patternHeadMap__lbt,
  SemanticExplorerCases.case_patternHeadMap__lbt_bf,
  SemanticExplorerCases.case_patternHeadMap__lpbt_1,
  SemanticExplorerCases.case_patternHeadMap__p1,
  SemanticExplorerCases.case_patternHeadMap__p12,
  SemanticExplorerCases.case_patternHeadMap__p123,
  SemanticExplorerCases.case_patternHeadMap__pee,
  SemanticExplorerCases.case_patternHeadMap__pe1,
  SemanticExplorerCases.case_patternHeadMap__p1e,
  SemanticExplorerCases.case_patternHeadMap__p12_3,
  SemanticExplorerCases.case_patternHeadMap__p12_34,
  SemanticExplorerCases.case_patternHeadMap__pe_12,
  SemanticExplorerCases.case_patternHeadMap__ppe1_2,
  SemanticExplorerCases.case_patternHeadMap__p12_e,
  SemanticExplorerCases.case_patternHeadMap__ppe,
  SemanticExplorerCases.case_patternHeadMap__pp1,
  SemanticExplorerCases.case_patternHeadMap__ppp12,
  SemanticExplorerCases.case_patternHeadMap__le,
  SemanticExplorerCases.case_patternHeadMap__l7,
  SemanticExplorerCases.case_patternHeadMap__l12,
  SemanticExplorerCases.case_patternHeadMap__l12_3,
  SemanticExplorerCases.case_patternHeadMap__lle,
  SemanticExplorerCases.case_patternHeadMap__l_e,
  SemanticExplorerCases.case_patternHeadMap__l_p12,
  SemanticExplorerCases.case_patternHeadMap__p_l12,
  SemanticExplorerCases.case_patternHeadMap__pl1,
  SemanticExplorerCases.case_patternPair__e,
  SemanticExplorerCases.case_patternPair__n0,
  SemanticExplorerCases.case_patternPair__n1,
  SemanticExplorerCases.case_patternPair__bt,
  SemanticExplorerCases.case_patternPair__bf,
  SemanticExplorerCases.case_patternPair__pbt,
  SemanticExplorerCases.case_patternPair__pbt_e,
  SemanticExplorerCases.case_patternPair__pbt_1,
  SemanticExplorerCases.case_patternPair__lbt,
  SemanticExplorerCases.case_patternPair__lbt_bf,
  SemanticExplorerCases.case_patternPair__lpbt_1,
  SemanticExplorerCases.case_patternPair__p1,
  SemanticExplorerCases.case_patternPair__p12,
  SemanticExplorerCases.case_patternPair__p123,
  SemanticExplorerCases.case_patternPair__pee,
  SemanticExplorerCases.case_patternPair__pe1,
  SemanticExplorerCases.case_patternPair__p1e,
  SemanticExplorerCases.case_patternPair__p12_3,
  SemanticExplorerCases.case_patternPair__p12_34,
  SemanticExplorerCases.case_patternPair__pe_12,
  SemanticExplorerCases.case_patternPair__ppe1_2,
  SemanticExplorerCases.case_patternPair__p12_e,
  SemanticExplorerCases.case_patternPair__ppe,
  SemanticExplorerCases.case_patternPair__pp1,
  SemanticExplorerCases.case_patternPair__ppp12,
  SemanticExplorerCases.case_patternPair__le,
  SemanticExplorerCases.case_patternPair__l7,
  SemanticExplorerCases.case_patternPair__l12,
  SemanticExplorerCases.case_patternPair__l12_3,
  SemanticExplorerCases.case_patternPair__lle,
  SemanticExplorerCases.case_patternPair__l_e,
  SemanticExplorerCases.case_patternPair__l_p12,
  SemanticExplorerCases.case_patternPair__p_l12,
  SemanticExplorerCases.case_patternPair__pl1,
  SemanticExplorerCases.case_patternPairMap__e,
  SemanticExplorerCases.case_patternPairMap__n0,
  SemanticExplorerCases.case_patternPairMap__n1,
  SemanticExplorerCases.case_patternPairMap__bt,
  SemanticExplorerCases.case_patternPairMap__bf,
  SemanticExplorerCases.case_patternPairMap__pbt,
  SemanticExplorerCases.case_patternPairMap__pbt_e,
  SemanticExplorerCases.case_patternPairMap__pbt_1,
  SemanticExplorerCases.case_patternPairMap__lbt,
  SemanticExplorerCases.case_patternPairMap__lbt_bf,
  SemanticExplorerCases.case_patternPairMap__lpbt_1,
  SemanticExplorerCases.case_patternPairMap__p1,
  SemanticExplorerCases.case_patternPairMap__p12,
  SemanticExplorerCases.case_patternPairMap__p123,
  SemanticExplorerCases.case_patternPairMap__pee,
  SemanticExplorerCases.case_patternPairMap__pe1,
  SemanticExplorerCases.case_patternPairMap__p1e,
  SemanticExplorerCases.case_patternPairMap__p12_3,
  SemanticExplorerCases.case_patternPairMap__p12_34,
  SemanticExplorerCases.case_patternPairMap__pe_12,
  SemanticExplorerCases.case_patternPairMap__ppe1_2,
  SemanticExplorerCases.case_patternPairMap__p12_e,
  SemanticExplorerCases.case_patternPairMap__ppe,
  SemanticExplorerCases.case_patternPairMap__pp1,
  SemanticExplorerCases.case_patternPairMap__ppp12,
  SemanticExplorerCases.case_patternPairMap__le,
  SemanticExplorerCases.case_patternPairMap__l7,
  SemanticExplorerCases.case_patternPairMap__l12,
  SemanticExplorerCases.case_patternPairMap__l12_3,
  SemanticExplorerCases.case_patternPairMap__lle,
  SemanticExplorerCases.case_patternPairMap__l_e,
  SemanticExplorerCases.case_patternPairMap__l_p12,
  SemanticExplorerCases.case_patternPairMap__p_l12,
  SemanticExplorerCases.case_patternPairMap__pl1,
  SemanticExplorerCases.case_listPatternHead__e,
  SemanticExplorerCases.case_listPatternHead__n0,
  SemanticExplorerCases.case_listPatternHead__n1,
  SemanticExplorerCases.case_listPatternHead__bt,
  SemanticExplorerCases.case_listPatternHead__bf,
  SemanticExplorerCases.case_listPatternHead__pbt,
  SemanticExplorerCases.case_listPatternHead__pbt_e,
  SemanticExplorerCases.case_listPatternHead__pbt_1,
  SemanticExplorerCases.case_listPatternHead__lbt,
  SemanticExplorerCases.case_listPatternHead__lbt_bf,
  SemanticExplorerCases.case_listPatternHead__lpbt_1,
  SemanticExplorerCases.case_listPatternHead__p1,
  SemanticExplorerCases.case_listPatternHead__p12,
  SemanticExplorerCases.case_listPatternHead__p123,
  SemanticExplorerCases.case_listPatternHead__pee,
  SemanticExplorerCases.case_listPatternHead__pe1,
  SemanticExplorerCases.case_listPatternHead__p1e,
  SemanticExplorerCases.case_listPatternHead__p12_3,
  SemanticExplorerCases.case_listPatternHead__p12_34,
  SemanticExplorerCases.case_listPatternHead__pe_12,
  SemanticExplorerCases.case_listPatternHead__ppe1_2,
  SemanticExplorerCases.case_listPatternHead__p12_e,
  SemanticExplorerCases.case_listPatternHead__ppe,
  SemanticExplorerCases.case_listPatternHead__pp1,
  SemanticExplorerCases.case_listPatternHead__ppp12,
  SemanticExplorerCases.case_listPatternHead__le,
  SemanticExplorerCases.case_listPatternHead__l7,
  SemanticExplorerCases.case_listPatternHead__l12,
  SemanticExplorerCases.case_listPatternHead__l12_3,
  SemanticExplorerCases.case_listPatternHead__lle,
  SemanticExplorerCases.case_listPatternHead__l_e,
  SemanticExplorerCases.case_listPatternHead__l_p12,
  SemanticExplorerCases.case_listPatternHead__p_l12,
  SemanticExplorerCases.case_listPatternHead__pl1,
  SemanticExplorerCases.case_listPatternHeadMap__e,
  SemanticExplorerCases.case_listPatternHeadMap__n0,
  SemanticExplorerCases.case_listPatternHeadMap__n1,
  SemanticExplorerCases.case_listPatternHeadMap__bt,
  SemanticExplorerCases.case_listPatternHeadMap__bf,
  SemanticExplorerCases.case_listPatternHeadMap__pbt,
  SemanticExplorerCases.case_listPatternHeadMap__pbt_e,
  SemanticExplorerCases.case_listPatternHeadMap__pbt_1,
  SemanticExplorerCases.case_listPatternHeadMap__lbt,
  SemanticExplorerCases.case_listPatternHeadMap__lbt_bf,
  SemanticExplorerCases.case_listPatternHeadMap__lpbt_1,
  SemanticExplorerCases.case_listPatternHeadMap__p1,
  SemanticExplorerCases.case_listPatternHeadMap__p12,
  SemanticExplorerCases.case_listPatternHeadMap__p123,
  SemanticExplorerCases.case_listPatternHeadMap__pee,
  SemanticExplorerCases.case_listPatternHeadMap__pe1,
  SemanticExplorerCases.case_listPatternHeadMap__p1e,
  SemanticExplorerCases.case_listPatternHeadMap__p12_3,
  SemanticExplorerCases.case_listPatternHeadMap__p12_34,
  SemanticExplorerCases.case_listPatternHeadMap__pe_12,
  SemanticExplorerCases.case_listPatternHeadMap__ppe1_2,
  SemanticExplorerCases.case_listPatternHeadMap__p12_e,
  SemanticExplorerCases.case_listPatternHeadMap__ppe,
  SemanticExplorerCases.case_listPatternHeadMap__pp1,
  SemanticExplorerCases.case_listPatternHeadMap__ppp12,
  SemanticExplorerCases.case_listPatternHeadMap__le,
  SemanticExplorerCases.case_listPatternHeadMap__l7,
  SemanticExplorerCases.case_listPatternHeadMap__l12,
  SemanticExplorerCases.case_listPatternHeadMap__l12_3,
  SemanticExplorerCases.case_listPatternHeadMap__lle,
  SemanticExplorerCases.case_listPatternHeadMap__l_e,
  SemanticExplorerCases.case_listPatternHeadMap__l_p12,
  SemanticExplorerCases.case_listPatternHeadMap__p_l12,
  SemanticExplorerCases.case_listPatternHeadMap__pl1,
  SemanticExplorerCases.case_listPatternPair__e,
  SemanticExplorerCases.case_listPatternPair__n0,
  SemanticExplorerCases.case_listPatternPair__n1,
  SemanticExplorerCases.case_listPatternPair__bt,
  SemanticExplorerCases.case_listPatternPair__bf,
  SemanticExplorerCases.case_listPatternPair__pbt,
  SemanticExplorerCases.case_listPatternPair__pbt_e,
  SemanticExplorerCases.case_listPatternPair__pbt_1,
  SemanticExplorerCases.case_listPatternPair__lbt,
  SemanticExplorerCases.case_listPatternPair__lbt_bf,
  SemanticExplorerCases.case_listPatternPair__lpbt_1,
  SemanticExplorerCases.case_listPatternPair__p1,
  SemanticExplorerCases.case_listPatternPair__p12,
  SemanticExplorerCases.case_listPatternPair__p123,
  SemanticExplorerCases.case_listPatternPair__pee,
  SemanticExplorerCases.case_listPatternPair__pe1,
  SemanticExplorerCases.case_listPatternPair__p1e,
  SemanticExplorerCases.case_listPatternPair__p12_3,
  SemanticExplorerCases.case_listPatternPair__p12_34,
  SemanticExplorerCases.case_listPatternPair__pe_12,
  SemanticExplorerCases.case_listPatternPair__ppe1_2,
  SemanticExplorerCases.case_listPatternPair__p12_e,
  SemanticExplorerCases.case_listPatternPair__ppe,
  SemanticExplorerCases.case_listPatternPair__pp1,
  SemanticExplorerCases.case_listPatternPair__ppp12,
  SemanticExplorerCases.case_listPatternPair__le,
  SemanticExplorerCases.case_listPatternPair__l7,
  SemanticExplorerCases.case_listPatternPair__l12,
  SemanticExplorerCases.case_listPatternPair__l12_3,
  SemanticExplorerCases.case_listPatternPair__lle,
  SemanticExplorerCases.case_listPatternPair__l_e,
  SemanticExplorerCases.case_listPatternPair__l_p12,
  SemanticExplorerCases.case_listPatternPair__p_l12,
  SemanticExplorerCases.case_listPatternPair__pl1,
  SemanticExplorerCases.case_listPatternPairMap__e,
  SemanticExplorerCases.case_listPatternPairMap__n0,
  SemanticExplorerCases.case_listPatternPairMap__n1,
  SemanticExplorerCases.case_listPatternPairMap__bt,
  SemanticExplorerCases.case_listPatternPairMap__bf,
  SemanticExplorerCases.case_listPatternPairMap__pbt,
  SemanticExplorerCases.case_listPatternPairMap__pbt_e,
  SemanticExplorerCases.case_listPatternPairMap__pbt_1,
  SemanticExplorerCases.case_listPatternPairMap__lbt,
  SemanticExplorerCases.case_listPatternPairMap__lbt_bf,
  SemanticExplorerCases.case_listPatternPairMap__lpbt_1,
  SemanticExplorerCases.case_listPatternPairMap__p1,
  SemanticExplorerCases.case_listPatternPairMap__p12,
  SemanticExplorerCases.case_listPatternPairMap__p123,
  SemanticExplorerCases.case_listPatternPairMap__pee,
  SemanticExplorerCases.case_listPatternPairMap__pe1,
  SemanticExplorerCases.case_listPatternPairMap__p1e,
  SemanticExplorerCases.case_listPatternPairMap__p12_3,
  SemanticExplorerCases.case_listPatternPairMap__p12_34,
  SemanticExplorerCases.case_listPatternPairMap__pe_12,
  SemanticExplorerCases.case_listPatternPairMap__ppe1_2,
  SemanticExplorerCases.case_listPatternPairMap__p12_e,
  SemanticExplorerCases.case_listPatternPairMap__ppe,
  SemanticExplorerCases.case_listPatternPairMap__pp1,
  SemanticExplorerCases.case_listPatternPairMap__ppp12,
  SemanticExplorerCases.case_listPatternPairMap__le,
  SemanticExplorerCases.case_listPatternPairMap__l7,
  SemanticExplorerCases.case_listPatternPairMap__l12,
  SemanticExplorerCases.case_listPatternPairMap__l12_3,
  SemanticExplorerCases.case_listPatternPairMap__lle,
  SemanticExplorerCases.case_listPatternPairMap__l_e,
  SemanticExplorerCases.case_listPatternPairMap__l_p12,
  SemanticExplorerCases.case_listPatternPairMap__p_l12,
  SemanticExplorerCases.case_listPatternPairMap__pl1,
  SemanticExplorerCases.case_filterKeep__e,
  SemanticExplorerCases.case_filterKeep__n0,
  SemanticExplorerCases.case_filterKeep__n1,
  SemanticExplorerCases.case_filterKeep__bt,
  SemanticExplorerCases.case_filterKeep__bf,
  SemanticExplorerCases.case_filterKeep__pbt,
  SemanticExplorerCases.case_filterKeep__pbt_e,
  SemanticExplorerCases.case_filterKeep__pbt_1,
  SemanticExplorerCases.case_filterKeep__lbt,
  SemanticExplorerCases.case_filterKeep__lbt_bf,
  SemanticExplorerCases.case_filterKeep__lpbt_1,
  SemanticExplorerCases.case_filterKeep__p1,
  SemanticExplorerCases.case_filterKeep__p12,
  SemanticExplorerCases.case_filterKeep__p123,
  SemanticExplorerCases.case_filterKeep__pee,
  SemanticExplorerCases.case_filterKeep__pe1,
  SemanticExplorerCases.case_filterKeep__p1e,
  SemanticExplorerCases.case_filterKeep__p12_3,
  SemanticExplorerCases.case_filterKeep__p12_34,
  SemanticExplorerCases.case_filterKeep__pe_12,
  SemanticExplorerCases.case_filterKeep__ppe1_2,
  SemanticExplorerCases.case_filterKeep__p12_e,
  SemanticExplorerCases.case_filterKeep__ppe,
  SemanticExplorerCases.case_filterKeep__pp1,
  SemanticExplorerCases.case_filterKeep__ppp12,
  SemanticExplorerCases.case_filterKeep__le,
  SemanticExplorerCases.case_filterKeep__l7,
  SemanticExplorerCases.case_filterKeep__l12,
  SemanticExplorerCases.case_filterKeep__l12_3,
  SemanticExplorerCases.case_filterKeep__lle,
  SemanticExplorerCases.case_filterKeep__l_e,
  SemanticExplorerCases.case_filterKeep__l_p12,
  SemanticExplorerCases.case_filterKeep__p_l12,
  SemanticExplorerCases.case_filterKeep__pl1,
  SemanticExplorerCases.case_atoms__e,
  SemanticExplorerCases.case_atoms__n0,
  SemanticExplorerCases.case_atoms__n1,
  SemanticExplorerCases.case_atoms__bt,
  SemanticExplorerCases.case_atoms__bf,
  SemanticExplorerCases.case_atoms__pbt,
  SemanticExplorerCases.case_atoms__pbt_e,
  SemanticExplorerCases.case_atoms__pbt_1,
  SemanticExplorerCases.case_atoms__lbt,
  SemanticExplorerCases.case_atoms__lbt_bf,
  SemanticExplorerCases.case_atoms__lpbt_1,
  SemanticExplorerCases.case_atoms__p1,
  SemanticExplorerCases.case_atoms__p12,
  SemanticExplorerCases.case_atoms__p123,
  SemanticExplorerCases.case_atoms__pee,
  SemanticExplorerCases.case_atoms__pe1,
  SemanticExplorerCases.case_atoms__p1e,
  SemanticExplorerCases.case_atoms__p12_3,
  SemanticExplorerCases.case_atoms__p12_34,
  SemanticExplorerCases.case_atoms__pe_12,
  SemanticExplorerCases.case_atoms__ppe1_2,
  SemanticExplorerCases.case_atoms__p12_e,
  SemanticExplorerCases.case_atoms__ppe,
  SemanticExplorerCases.case_atoms__pp1,
  SemanticExplorerCases.case_atoms__ppp12,
  SemanticExplorerCases.case_atoms__le,
  SemanticExplorerCases.case_atoms__l7,
  SemanticExplorerCases.case_atoms__l12,
  SemanticExplorerCases.case_atoms__l12_3,
  SemanticExplorerCases.case_atoms__lle,
  SemanticExplorerCases.case_atoms__l_e,
  SemanticExplorerCases.case_atoms__l_p12,
  SemanticExplorerCases.case_atoms__p_l12,
  SemanticExplorerCases.case_atoms__pl1,
  SemanticExplorerCases.case_takeCapture__e,
  SemanticExplorerCases.case_takeCapture__n0,
  SemanticExplorerCases.case_takeCapture__n1,
  SemanticExplorerCases.case_takeCapture__bt,
  SemanticExplorerCases.case_takeCapture__bf,
  SemanticExplorerCases.case_takeCapture__pbt,
  SemanticExplorerCases.case_takeCapture__pbt_e,
  SemanticExplorerCases.case_takeCapture__pbt_1,
  SemanticExplorerCases.case_takeCapture__lbt,
  SemanticExplorerCases.case_takeCapture__lbt_bf,
  SemanticExplorerCases.case_takeCapture__lpbt_1,
  SemanticExplorerCases.case_takeCapture__p1,
  SemanticExplorerCases.case_takeCapture__p12,
  SemanticExplorerCases.case_takeCapture__p123,
  SemanticExplorerCases.case_takeCapture__pee,
  SemanticExplorerCases.case_takeCapture__pe1,
  SemanticExplorerCases.case_takeCapture__p1e,
  SemanticExplorerCases.case_takeCapture__p12_3,
  SemanticExplorerCases.case_takeCapture__p12_34,
  SemanticExplorerCases.case_takeCapture__pe_12,
  SemanticExplorerCases.case_takeCapture__ppe1_2,
  SemanticExplorerCases.case_takeCapture__p12_e,
  SemanticExplorerCases.case_takeCapture__ppe,
  SemanticExplorerCases.case_takeCapture__pp1,
  SemanticExplorerCases.case_takeCapture__ppp12,
  SemanticExplorerCases.case_takeCapture__le,
  SemanticExplorerCases.case_takeCapture__l7,
  SemanticExplorerCases.case_takeCapture__l12,
  SemanticExplorerCases.case_takeCapture__l12_3,
  SemanticExplorerCases.case_takeCapture__lle,
  SemanticExplorerCases.case_takeCapture__l_e,
  SemanticExplorerCases.case_takeCapture__l_p12,
  SemanticExplorerCases.case_takeCapture__p_l12,
  SemanticExplorerCases.case_takeCapture__pl1,
  SemanticExplorerCases.case_takeIdentity__e,
  SemanticExplorerCases.case_takeIdentity__n0,
  SemanticExplorerCases.case_takeIdentity__n1,
  SemanticExplorerCases.case_takeIdentity__bt,
  SemanticExplorerCases.case_takeIdentity__bf,
  SemanticExplorerCases.case_takeIdentity__pbt,
  SemanticExplorerCases.case_takeIdentity__pbt_e,
  SemanticExplorerCases.case_takeIdentity__pbt_1,
  SemanticExplorerCases.case_takeIdentity__lbt,
  SemanticExplorerCases.case_takeIdentity__lbt_bf,
  SemanticExplorerCases.case_takeIdentity__lpbt_1,
  SemanticExplorerCases.case_takeIdentity__p1,
  SemanticExplorerCases.case_takeIdentity__p12,
  SemanticExplorerCases.case_takeIdentity__p123,
  SemanticExplorerCases.case_takeIdentity__pee,
  SemanticExplorerCases.case_takeIdentity__pe1,
  SemanticExplorerCases.case_takeIdentity__p1e,
  SemanticExplorerCases.case_takeIdentity__p12_3,
  SemanticExplorerCases.case_takeIdentity__p12_34,
  SemanticExplorerCases.case_takeIdentity__pe_12,
  SemanticExplorerCases.case_takeIdentity__ppe1_2,
  SemanticExplorerCases.case_takeIdentity__p12_e,
  SemanticExplorerCases.case_takeIdentity__ppe,
  SemanticExplorerCases.case_takeIdentity__pp1,
  SemanticExplorerCases.case_takeIdentity__ppp12,
  SemanticExplorerCases.case_takeIdentity__le,
  SemanticExplorerCases.case_takeIdentity__l7,
  SemanticExplorerCases.case_takeIdentity__l12,
  SemanticExplorerCases.case_takeIdentity__l12_3,
  SemanticExplorerCases.case_takeIdentity__lle,
  SemanticExplorerCases.case_takeIdentity__l_e,
  SemanticExplorerCases.case_takeIdentity__l_p12,
  SemanticExplorerCases.case_takeIdentity__p_l12,
  SemanticExplorerCases.case_takeIdentity__pl1,
  SemanticExplorerCases.case_takeCount__e,
  SemanticExplorerCases.case_takeCount__n0,
  SemanticExplorerCases.case_takeCount__n1,
  SemanticExplorerCases.case_takeCount__bt,
  SemanticExplorerCases.case_takeCount__bf,
  SemanticExplorerCases.case_takeCount__pbt,
  SemanticExplorerCases.case_takeCount__pbt_e,
  SemanticExplorerCases.case_takeCount__pbt_1,
  SemanticExplorerCases.case_takeCount__lbt,
  SemanticExplorerCases.case_takeCount__lbt_bf,
  SemanticExplorerCases.case_takeCount__lpbt_1,
  SemanticExplorerCases.case_takeCount__p1,
  SemanticExplorerCases.case_takeCount__p12,
  SemanticExplorerCases.case_takeCount__p123,
  SemanticExplorerCases.case_takeCount__pee,
  SemanticExplorerCases.case_takeCount__pe1,
  SemanticExplorerCases.case_takeCount__p1e,
  SemanticExplorerCases.case_takeCount__p12_3,
  SemanticExplorerCases.case_takeCount__p12_34,
  SemanticExplorerCases.case_takeCount__pe_12,
  SemanticExplorerCases.case_takeCount__ppe1_2,
  SemanticExplorerCases.case_takeCount__p12_e,
  SemanticExplorerCases.case_takeCount__ppe,
  SemanticExplorerCases.case_takeCount__pp1,
  SemanticExplorerCases.case_takeCount__ppp12,
  SemanticExplorerCases.case_takeCount__le,
  SemanticExplorerCases.case_takeCount__l7,
  SemanticExplorerCases.case_takeCount__l12,
  SemanticExplorerCases.case_takeCount__l12_3,
  SemanticExplorerCases.case_takeCount__lle,
  SemanticExplorerCases.case_takeCount__l_e,
  SemanticExplorerCases.case_takeCount__l_p12,
  SemanticExplorerCases.case_takeCount__p_l12,
  SemanticExplorerCases.case_takeCount__pl1,
  SemanticExplorerCases.case_takeCollecting__e,
  SemanticExplorerCases.case_takeCollecting__n0,
  SemanticExplorerCases.case_takeCollecting__n1,
  SemanticExplorerCases.case_takeCollecting__bt,
  SemanticExplorerCases.case_takeCollecting__bf,
  SemanticExplorerCases.case_takeCollecting__pbt,
  SemanticExplorerCases.case_takeCollecting__pbt_e,
  SemanticExplorerCases.case_takeCollecting__pbt_1,
  SemanticExplorerCases.case_takeCollecting__lbt,
  SemanticExplorerCases.case_takeCollecting__lbt_bf,
  SemanticExplorerCases.case_takeCollecting__lpbt_1,
  SemanticExplorerCases.case_takeCollecting__p1,
  SemanticExplorerCases.case_takeCollecting__p12,
  SemanticExplorerCases.case_takeCollecting__p123,
  SemanticExplorerCases.case_takeCollecting__pee,
  SemanticExplorerCases.case_takeCollecting__pe1,
  SemanticExplorerCases.case_takeCollecting__p1e,
  SemanticExplorerCases.case_takeCollecting__p12_3,
  SemanticExplorerCases.case_takeCollecting__p12_34,
  SemanticExplorerCases.case_takeCollecting__pe_12,
  SemanticExplorerCases.case_takeCollecting__ppe1_2,
  SemanticExplorerCases.case_takeCollecting__p12_e,
  SemanticExplorerCases.case_takeCollecting__ppe,
  SemanticExplorerCases.case_takeCollecting__pp1,
  SemanticExplorerCases.case_takeCollecting__ppp12,
  SemanticExplorerCases.case_takeCollecting__le,
  SemanticExplorerCases.case_takeCollecting__l7,
  SemanticExplorerCases.case_takeCollecting__l12,
  SemanticExplorerCases.case_takeCollecting__l12_3,
  SemanticExplorerCases.case_takeCollecting__lle,
  SemanticExplorerCases.case_takeCollecting__l_e,
  SemanticExplorerCases.case_takeCollecting__l_p12,
  SemanticExplorerCases.case_takeCollecting__p_l12,
  SemanticExplorerCases.case_takeCollecting__pl1,
  SemanticExplorerCases.case_spreadRootStacked__e,
  SemanticExplorerCases.case_spreadRootStacked__n0,
  SemanticExplorerCases.case_spreadRootStacked__n1,
  SemanticExplorerCases.case_spreadRootStacked__bt,
  SemanticExplorerCases.case_spreadRootStacked__bf,
  SemanticExplorerCases.case_spreadRootStacked__pbt,
  SemanticExplorerCases.case_spreadRootStacked__pbt_e,
  SemanticExplorerCases.case_spreadRootStacked__pbt_1,
  SemanticExplorerCases.case_spreadRootStacked__lbt,
  SemanticExplorerCases.case_spreadRootStacked__lbt_bf,
  SemanticExplorerCases.case_spreadRootStacked__lpbt_1,
  SemanticExplorerCases.case_spreadRootStacked__p1,
  SemanticExplorerCases.case_spreadRootStacked__p12,
  SemanticExplorerCases.case_spreadRootStacked__p123,
  SemanticExplorerCases.case_spreadRootStacked__pee,
  SemanticExplorerCases.case_spreadRootStacked__pe1,
  SemanticExplorerCases.case_spreadRootStacked__p1e,
  SemanticExplorerCases.case_spreadRootStacked__p12_3,
  SemanticExplorerCases.case_spreadRootStacked__p12_34,
  SemanticExplorerCases.case_spreadRootStacked__pe_12,
  SemanticExplorerCases.case_spreadRootStacked__ppe1_2,
  SemanticExplorerCases.case_spreadRootStacked__p12_e,
  SemanticExplorerCases.case_spreadRootStacked__ppe,
  SemanticExplorerCases.case_spreadRootStacked__pp1,
  SemanticExplorerCases.case_spreadRootStacked__ppp12,
  SemanticExplorerCases.case_spreadRootStacked__le,
  SemanticExplorerCases.case_spreadRootStacked__l7,
  SemanticExplorerCases.case_spreadRootStacked__l12,
  SemanticExplorerCases.case_spreadRootStacked__l12_3,
  SemanticExplorerCases.case_spreadRootStacked__lle,
  SemanticExplorerCases.case_spreadRootStacked__l_e,
  SemanticExplorerCases.case_spreadRootStacked__l_p12,
  SemanticExplorerCases.case_spreadRootStacked__p_l12,
  SemanticExplorerCases.case_spreadRootStacked__pl1,
  SemanticExplorerCases.case_collectingStacked__e,
  SemanticExplorerCases.case_collectingStacked__n0,
  SemanticExplorerCases.case_collectingStacked__n1,
  SemanticExplorerCases.case_collectingStacked__bt,
  SemanticExplorerCases.case_collectingStacked__bf,
  SemanticExplorerCases.case_collectingStacked__pbt,
  SemanticExplorerCases.case_collectingStacked__pbt_e,
  SemanticExplorerCases.case_collectingStacked__pbt_1,
  SemanticExplorerCases.case_collectingStacked__lbt,
  SemanticExplorerCases.case_collectingStacked__lbt_bf,
  SemanticExplorerCases.case_collectingStacked__lpbt_1,
  SemanticExplorerCases.case_collectingStacked__p1,
  SemanticExplorerCases.case_collectingStacked__p12,
  SemanticExplorerCases.case_collectingStacked__p123,
  SemanticExplorerCases.case_collectingStacked__pee,
  SemanticExplorerCases.case_collectingStacked__pe1,
  SemanticExplorerCases.case_collectingStacked__p1e,
  SemanticExplorerCases.case_collectingStacked__p12_3,
  SemanticExplorerCases.case_collectingStacked__p12_34,
  SemanticExplorerCases.case_collectingStacked__pe_12,
  SemanticExplorerCases.case_collectingStacked__ppe1_2,
  SemanticExplorerCases.case_collectingStacked__p12_e,
  SemanticExplorerCases.case_collectingStacked__ppe,
  SemanticExplorerCases.case_collectingStacked__pp1,
  SemanticExplorerCases.case_collectingStacked__ppp12,
  SemanticExplorerCases.case_collectingStacked__le,
  SemanticExplorerCases.case_collectingStacked__l7,
  SemanticExplorerCases.case_collectingStacked__l12,
  SemanticExplorerCases.case_collectingStacked__l12_3,
  SemanticExplorerCases.case_collectingStacked__lle,
  SemanticExplorerCases.case_collectingStacked__l_e,
  SemanticExplorerCases.case_collectingStacked__l_p12,
  SemanticExplorerCases.case_collectingStacked__p_l12,
  SemanticExplorerCases.case_collectingStacked__pl1,
  SemanticExplorerCases.case_captureStacked__e,
  SemanticExplorerCases.case_captureStacked__n0,
  SemanticExplorerCases.case_captureStacked__n1,
  SemanticExplorerCases.case_captureStacked__bt,
  SemanticExplorerCases.case_captureStacked__bf,
  SemanticExplorerCases.case_captureStacked__pbt,
  SemanticExplorerCases.case_captureStacked__pbt_e,
  SemanticExplorerCases.case_captureStacked__pbt_1,
  SemanticExplorerCases.case_captureStacked__lbt,
  SemanticExplorerCases.case_captureStacked__lbt_bf,
  SemanticExplorerCases.case_captureStacked__lpbt_1,
  SemanticExplorerCases.case_captureStacked__p1,
  SemanticExplorerCases.case_captureStacked__p12,
  SemanticExplorerCases.case_captureStacked__p123,
  SemanticExplorerCases.case_captureStacked__pee,
  SemanticExplorerCases.case_captureStacked__pe1,
  SemanticExplorerCases.case_captureStacked__p1e,
  SemanticExplorerCases.case_captureStacked__p12_3,
  SemanticExplorerCases.case_captureStacked__p12_34,
  SemanticExplorerCases.case_captureStacked__pe_12,
  SemanticExplorerCases.case_captureStacked__ppe1_2,
  SemanticExplorerCases.case_captureStacked__p12_e,
  SemanticExplorerCases.case_captureStacked__ppe,
  SemanticExplorerCases.case_captureStacked__pp1,
  SemanticExplorerCases.case_captureStacked__ppp12,
  SemanticExplorerCases.case_captureStacked__le,
  SemanticExplorerCases.case_captureStacked__l7,
  SemanticExplorerCases.case_captureStacked__l12,
  SemanticExplorerCases.case_captureStacked__l12_3,
  SemanticExplorerCases.case_captureStacked__lle,
  SemanticExplorerCases.case_captureStacked__l_e,
  SemanticExplorerCases.case_captureStacked__l_p12,
  SemanticExplorerCases.case_captureStacked__p_l12,
  SemanticExplorerCases.case_captureStacked__pl1,
  SemanticExplorerCases.case_special__multiProp,
  SemanticExplorerCases.case_special__multiPropCall,
  SemanticExplorerCases.case_special__multiPropCount,
  SemanticExplorerCases.case_special__multiPropDotCount,
  SemanticExplorerCases.case_special__multiPropDot,
  SemanticExplorerCases.case_special__dotAccessPublicMember,
  SemanticExplorerCases.case_special__dotAccessCallPublicMember,
  SemanticExplorerCases.case_special__multiPropIndex0,
  SemanticExplorerCases.case_special__multiPropEq,
  SemanticExplorerCases.case_special__multiCollecting,
  SemanticExplorerCases.case_special__multiCollectingCount,
  SemanticExplorerCases.case_special__collectingEmptyCall,
  SemanticExplorerCases.case_special__collectingFwdSum,
  SemanticExplorerCases.case_special__collectingFwdSpread,
  SemanticExplorerCases.case_special__collectingJoin,
  SemanticExplorerCases.case_special__range13,
  SemanticExplorerCases.case_special__rangeCapture,
  SemanticExplorerCases.case_special__rangeCount,
  SemanticExplorerCases.case_special__rangeIndex0,
  SemanticExplorerCases.case_special__takeOneSurvivorPair,
  SemanticExplorerCases.case_special__takeOneSurvivorPairCount,
  SemanticExplorerCases.case_special__takeOneSurvivorPairEq,
  SemanticExplorerCases.case_special__skipToOnePair,
  SemanticExplorerCases.case_special__distinctEmpties,
  SemanticExplorerCases.case_special__distinctPairsToOne,
  SemanticExplorerCases.case_special__takeEmpties,
  SemanticExplorerCases.case_special__filterOneSurvivor,
  SemanticExplorerCases.case_special__filterOneSurvivorCount,
  SemanticExplorerCases.case_special__filterZeroSurvivors,
  SemanticExplorerCases.case_special__mapPairSwap,
  SemanticExplorerCases.case_special__mapPairSwapOk,
  SemanticExplorerCases.case_special__mapPairSwapFlatIsArity,
  SemanticExplorerCases.case_special__mapToOne,
  SemanticExplorerCases.case_special__orderSingle,
  SemanticExplorerCases.case_special__orderEmpty,
  SemanticExplorerCases.case_special__atomsNested,
  SemanticExplorerCases.case_special__emptyOpGreater,
  SemanticExplorerCases.case_special__emptyOpPlus,
  SemanticExplorerCases.case_special__emptyOpPlusRight,
  SemanticExplorerCases.case_special__emptyOpDivRight,
  SemanticExplorerCases.case_special__emptyOpAnd,
  SemanticExplorerCases.case_special__emptyOpString,
  SemanticExplorerCases.case_special__emptyOpBoth,
  SemanticExplorerCases.case_special__emptyUnaryMinus,
  SemanticExplorerCases.case_special__emptyUnaryNot,
  SemanticExplorerCases.case_special__emptyEqEmpty,
  SemanticExplorerCases.case_special__emptyEqNestedEmpty,
  SemanticExplorerCases.case_special__emptyNeNestedEmpty,
  SemanticExplorerCases.case_special__propBodyEmptySlot,
  SemanticExplorerCases.case_special__rootEmptySlots,
  SemanticExplorerCases.case_special__seqOfSpreadEmpty,
  SemanticExplorerCases.case_special__indexPairInSeq,
  SemanticExplorerCases.case_special__indexEmptyItemRoot,
  SemanticExplorerCases.case_special__indexCapturedEq,
  SemanticExplorerCases.case_special__chainedListIndex,
  SemanticExplorerCases.case_special__listIndexCapturedEq,
  SemanticExplorerCases.case_special__listIndexSelectedKindEqFalse,
  SemanticExplorerCases.case_special__orderIndex0,
  SemanticExplorerCases.case_special__nestedWrittenArg,
  SemanticExplorerCases.case_special__writtenSlotArity,
  SemanticExplorerCases.case_special__mixedSingleGrouped,
  SemanticExplorerCases.case_special__sumEmpty,
  SemanticExplorerCases.case_special__spreadWithSiblingSeqLiteral,
  SemanticExplorerCases.case_special__spreadEmptyBetween,
  SemanticExplorerCases.case_special__rootSpreadExtra,
  SemanticExplorerCases.case_special__spreadOfSpreadSeqLiteral,
  SemanticExplorerCases.case_special__eqSpreadSeqLiteral,
  SemanticExplorerCases.case_special__loopSpreadHistoryFlat,
  SemanticExplorerCases.case_special__ifBranchSeq,
  SemanticExplorerCases.case_special__divZero,
  SemanticExplorerCases.case_special__negativeResult,
  SemanticExplorerCases.case_special__strEq,
  SemanticExplorerCases.case_special__chainAllTrue,
  SemanticExplorerCases.case_special__chainMixed,
  SemanticExplorerCases.case_special__chainFalseMiddle,
  SemanticExplorerCases.case_special__chainFalseLast,
  SemanticExplorerCases.case_special__chainEqOnly,
  SemanticExplorerCases.case_special__chainNeAdjacent,
  SemanticExplorerCases.case_special__chainNeAdjacentFalse,
  SemanticExplorerCases.case_special__chainEqThenLt,
  SemanticExplorerCases.case_special__chainBoolEqMixed,
  SemanticExplorerCases.case_special__chainSeqEq,
  SemanticExplorerCases.case_special__chainStrEq,
  SemanticExplorerCases.case_special__chainParenFirst,
  SemanticExplorerCases.case_special__chainParenRight,
  SemanticExplorerCases.case_special__chainParenBoth,
  SemanticExplorerCases.case_special__chainUnderNot,
  SemanticExplorerCases.case_special__chainUnderAnd,
  SemanticExplorerCases.case_special__chainArithmeticOperands,
  SemanticExplorerCases.case_special__chainInvalidLater,
  SemanticExplorerCases.case_special__chainErrorFirstOperand,
  SemanticExplorerCases.case_special__chainErrorAfterFalse,
  SemanticExplorerCases.case_special__chainPropertyOperands,
  SemanticExplorerCases.case_special__chainCallOperands,
  SemanticExplorerCases.case_special__chainLtThenEq,
  SemanticExplorerCases.case_special__chainLtThenGt,
  SemanticExplorerCases.case_special__chainNeThenLt,
  SemanticExplorerCases.case_special__chainFalseFirstThenEqFalse,
  SemanticExplorerCases.case_special__chainGroupedNotOperand,
  SemanticExplorerCases.case_special__chainParenLeftUnderOrdering,
  SemanticExplorerCases.case_special__chainNegatedBasePower,
  SemanticExplorerCases.case_special__chainNegatedPowerOperand,
  SemanticExplorerCases.case_special__chainGroupedNegatedBasePowerOperand,
  SemanticExplorerCases.case_special__chainArithmeticTiers,
  SemanticExplorerCases.case_special__chainMiddleOperandError,
  SemanticExplorerCases.case_special__chainGroupedSelectionReceiver,
  SemanticExplorerCases.case_special__strCount,
  SemanticExplorerCases.case_special__strCapture,
  SemanticExplorerCases.case_special__listSpreadOfSeqProp,
  SemanticExplorerCases.case_special__listSpreadBetween,
  SemanticExplorerCases.case_special__listOfLists,
  SemanticExplorerCases.case_special__listSpreadConcat,
  SemanticExplorerCases.case_special__listMixedSpread,
  SemanticExplorerCases.case_special__listEmptyListSpreadBetween,
  SemanticExplorerCases.case_special__listEmptySeqSpreadBetween,
  SemanticExplorerCases.case_special__listNeSeq,
  SemanticExplorerCases.case_special__listEmptyNeEmptySeq,
  SemanticExplorerCases.case_special__listSingletonNeItem,
  SemanticExplorerCases.case_special__listWrapCanonicalizes,
  SemanticExplorerCases.case_special__listSpreadCaptureRoundTrip,
  SemanticExplorerCases.case_special__listCollectingNotSequenceKind,
  SemanticExplorerCases.case_special__listCollectingCollectsExactList,
  SemanticExplorerCases.case_special__implicitForwardOrdinarySource,
  SemanticExplorerCases.case_special__callbackSingleCollectingMap,
  SemanticExplorerCases.case_special__callbackMixedCollectingRow,
  SemanticExplorerCases.case_special__callbackMixedCollectingRowPattern,
  SemanticExplorerCases.case_special__callbackCollectingElementIsOneArgument,
  SemanticExplorerCases.case_special__collectorZeroArgumentCallableFailureIsItsOwn,
  SemanticExplorerCases.case_special__listInSeqSpreadKeepsList,
  SemanticExplorerCases.case_special__listFixedCallBoundary,
  SemanticExplorerCases.case_special__listCollectingSpreadCall,
  SemanticExplorerCases.case_special__spreadNoOutputBlockRoot,
  SemanticExplorerCases.case_special__spreadNoOutputBlockList,
  SemanticExplorerCases.case_special__spreadNoOutputBlockCallArg,
  SemanticExplorerCases.case_special__spreadNoOutputResolved,
  SemanticExplorerCases.case_special__spreadNestedDependency,
  SemanticExplorerCases.case_special__spreadNestedDependencyCall,
  SemanticExplorerCases.case_special__spreadOwnInvoked,
  SemanticExplorerCases.case_special__spreadNestedArgument,
  SemanticExplorerCases.case_special__spreadNestedRow,
  SemanticExplorerCases.case_special__spreadNestedCapture,
  SemanticExplorerCases.case_special__spreadNestedList,
  SemanticExplorerCases.case_special__spreadNestedBuiltinArgument,
  SemanticExplorerCases.case_special__spreadNestedFamilyMatch,
  SemanticExplorerCases.case_special__spreadNestedPatternBinding,
  SemanticExplorerCases.case_special__spreadNestedStringReceiver,
  SemanticExplorerCases.case_special__spreadInnerOwnKept,
  SemanticExplorerCases.case_special__spreadOrdinaryFailureKept,
  SemanticExplorerCases.case_special__spreadNestedSupplySlot,
  SemanticExplorerCases.case_special__spreadNestedCallbackSlot,
  SemanticExplorerCases.case_special__spreadForwardedOwn,
  SemanticExplorerCases.case_special__spreadForwardedNested,
  SemanticExplorerCases.case_special__spreadCollectorElement,
  SemanticExplorerCases.case_special__spreadForwardedCollectorElement,
  SemanticExplorerCases.case_special__listLoneCollectingAssignment,
  SemanticExplorerCases.case_special__minSeq,
  SemanticExplorerCases.case_special__minList,
  SemanticExplorerCases.case_special__minScalar,
  SemanticExplorerCases.case_special__minEmpty,
  SemanticExplorerCases.case_special__minNestedItem,
  SemanticExplorerCases.case_special__minDot,
  SemanticExplorerCases.case_special__maxSeq,
  SemanticExplorerCases.case_special__maxList,
  SemanticExplorerCases.case_special__maxEmpty,
  SemanticExplorerCases.case_special__maxDot,
  SemanticExplorerCases.case_special__firstSeq,
  SemanticExplorerCases.case_special__firstScalar,
  SemanticExplorerCases.case_special__firstListElementStaysExact,
  SemanticExplorerCases.case_special__firstEmptyItem,
  SemanticExplorerCases.case_special__firstEmpty,
  SemanticExplorerCases.case_special__firstDot,
  SemanticExplorerCases.case_special__lastSeq,
  SemanticExplorerCases.case_special__lastListElementStaysExact,
  SemanticExplorerCases.case_special__lastEmpty,
  SemanticExplorerCases.case_special__orderDescSeq,
  SemanticExplorerCases.case_special__orderDescList,
  SemanticExplorerCases.case_special__orderDescDuplicates,
  SemanticExplorerCases.case_special__orderDescScalar,
  SemanticExplorerCases.case_special__orderDescEmpty,
  SemanticExplorerCases.case_special__orderDescString,
  SemanticExplorerCases.case_special__orderDescDot,
  SemanticExplorerCases.case_special__whileCountdown,
  SemanticExplorerCases.case_special__whileZeroIterations,
  SemanticExplorerCases.case_special__whileTwoSlotState,
  SemanticExplorerCases.case_special__whileEmptyInitialState,
  SemanticExplorerCases.case_special__whileNonNumericContinuation,
  SemanticExplorerCases.case_special__whileDot,
  SemanticExplorerCases.case_special__loopResultIsOneRow,
  SemanticExplorerCases.case_special__loopResultBesideAnotherRow,
  SemanticExplorerCases.case_special__loopResultSpreadOpensIt,
  SemanticExplorerCases.case_special__loopZeroSlotResult,
  SemanticExplorerCases.case_special__repeatedNameStepSpreadRowIsTwoSlots,
  SemanticExplorerCases.case_special__repeatedNameStepDivergingRowsRebindFails,
  SemanticExplorerCases.case_special__structuralStepSpreadRowSuppliesItems,
  SemanticExplorerCases.case_special__structuralStepSpreadRowCannotRebind,
  SemanticExplorerCases.case_special__historyStepSpreadRowEqualsDirectCall,
  SemanticExplorerCases.case_special__nestedLoopStepRowIsOneSlot,
  SemanticExplorerCases.case_special__nestedLoopStepRowSpread,
  SemanticExplorerCases.case_special__callbackBodyLoopIsOneValue,
  SemanticExplorerCases.case_special__loopStepClauseFamily,
  SemanticExplorerCases.case_special__loopStepFamilyWhile,
  SemanticExplorerCases.case_special__loopStepFamilyMultiSlot,
  SemanticExplorerCases.case_special__loopStepFamilyRowsAreTheNextState,
  SemanticExplorerCases.case_special__loopStepFamilyNoMatch,
  SemanticExplorerCases.case_special__loopStepFamilyClauseOrder,
  SemanticExplorerCases.case_special__loopStepFamilyStructural,
  SemanticExplorerCases.case_special__loopStepFamilyRepeatedName,
  SemanticExplorerCases.case_special__loopStepBuiltinOneRow,
  SemanticExplorerCases.case_special__loopStepBuiltinCollectionNextArity,
  SemanticExplorerCases.case_special__loopStepBuiltinEmptyResultIsTheFlag,
  SemanticExplorerCases.case_special__loopStepBuiltinLazyIf,
  SemanticExplorerCases.case_special__loopStepAliasOfFamilyAndBuiltin,
  SemanticExplorerCases.case_special__loopStepForwardedFamily,
  SemanticExplorerCases.case_special__loopStepValueRejected,
  SemanticExplorerCases.case_special__loopStepZeroIterationsNeverProject,
  SemanticExplorerCases.case_special__loopMetaValueRefused,
  SemanticExplorerCases.case_special__loopMetaPropertyReadRefused,
  SemanticExplorerCases.case_special__loopMetaPlainAndDot,
  SemanticExplorerCases.case_special__loopMetaZeroState,
  SemanticExplorerCases.case_special__loopMetaSpreadBeforeCount,
  SemanticExplorerCases.case_special__loopMetaExactArity,
  SemanticExplorerCases.case_special__loopMetaQualifiedCalleeCaptured,
  SemanticExplorerCases.case_special__loopMetaBareMemberPathRefused,
  SemanticExplorerCases.case_special__loopMetaRebuiltProjectedStep,
  SemanticExplorerCases.case_special__metaExtensionReceiverIsSupplied,
  SemanticExplorerCases.case_special__loopMetaNamedAlias,
  SemanticExplorerCases.case_special__loopStepLoopBuiltinAsStep,
  SemanticExplorerCases.case_special__containsSequenceItem,
  SemanticExplorerCases.case_special__containsListItem,
  SemanticExplorerCases.case_special__containsEmptyItem,
  SemanticExplorerCases.case_special__containsScalarCollection,
  SemanticExplorerCases.case_special__containsAcrossKinds,
  SemanticExplorerCases.case_special__openPublicMember,
  SemanticExplorerCases.case_special__openPrivateMemberHidden,
  SemanticExplorerCases.case_special__openLocalOnlyCapturedParamsInsideOwner,
  SemanticExplorerCases.case_special__openLocalOnlyCapturedParamsOutsideOwner,
  SemanticExplorerCases.case_special__openTwoProvidersAmbiguousAtRuntime,
  SemanticExplorerCases.case_special__openDuplicateTargetDedup,
  SemanticExplorerCases.case_special__openDuplicateDottedTargetDedup,
  SemanticExplorerCases.case_special__openTwoSpellingsOneProvider,
  SemanticExplorerCases.case_special__openDuplicateInlineBlocksAmbiguousAtRuntime,
  SemanticExplorerCases.case_special__openInlineBlock,
  SemanticExplorerCases.case_special__openInlineBlockPrivateHidden,
  SemanticExplorerCases.case_special__openDottedPath,
  SemanticExplorerCases.case_special__openLocalShadowsOpenedName,
  SemanticExplorerCases.case_special__openAncestorPropertyWins,
  SemanticExplorerCases.case_special__openParentScopeReachesChild,
  SemanticExplorerCases.case_special__openNestedDoesNotLeakOutward,
  SemanticExplorerCases.case_special__openHeadDefinedLater,
  SemanticExplorerCases.case_special__openBuiltinNameCollision,
  SemanticExplorerCases.case_special__structuralDotSeesPrivateMember,
  SemanticExplorerCases.case_special__openPrivateMemberIsNotASecondProvider,
  SemanticExplorerCases.case_special__openLocalOnlyMemberIsASecondProviderAtRuntime,
  SemanticExplorerCases.case_special__ifSelectedParameterizedBranchIsArity,
  SemanticExplorerCases.case_special__ifSelectedParameterizedFalseBranchIsArity,
  SemanticExplorerCases.case_special__ifParameterizedConditionIsArity,
  SemanticExplorerCases.case_special__ifUnselectedParameterizedBranchStaysLazy,
  SemanticExplorerCases.case_special__ifZeroParameterBranchIsValue,
  SemanticExplorerCases.case_special__ifParameterIgnoringBodyStillArity,
  SemanticExplorerCases.case_special__ifCollectingCallableSlotIsCollectedValue,
  SemanticExplorerCases.case_special__ifCollectingCallableExplicitCallIsSameValue,
  SemanticExplorerCases.case_special__bareCollectingCallableIsAValue,
  SemanticExplorerCases.case_special__bareCollectingCallableCountAgreesWithDottedForm,
  SemanticExplorerCases.case_special__ifRequiredPrefixBesideCollectorIsArity,
  SemanticExplorerCases.case_special__ifRequiredSuffixBesideCollectorIsArity,
  SemanticExplorerCases.case_special__ifNestedCollectingPatternIsArity,
  SemanticExplorerCases.case_special__collectingCallableStaysACallbackAlgorithm,
  SemanticExplorerCases.case_special__ifAlgorithmChannelParameterSlotIsArity,
  SemanticExplorerCases.case_special__repeatInitialParameterizedSlotIsArity,
  SemanticExplorerCases.case_special__repeatCountParameterizedSlotIsArity,
  SemanticExplorerCases.case_special__whileInitialParameterizedSlotIsArity,
  SemanticExplorerCases.case_special__atomsParameterizedSlotIsArity,
  SemanticExplorerCases.case_special__rangeParameterizedSlotIsArity,
  SemanticExplorerCases.case_special__dotStringParameterizedReceiverIsArity,
  SemanticExplorerCases.case_special__dotStringNavigatedParameterizedMemberIsArity,
  SemanticExplorerCases.case_special__reduceParameterIgnoringInitialStillRejected,
  SemanticExplorerCases.case_special__repeatParameterizedStepIsCallback,
  SemanticExplorerCases.case_special__formulaLiftingIfBranchLiftsWhileStayingLazy,
  SemanticExplorerCases.case_special__formulaLiftingRootValuePositionNeedsTheParameter,
  SemanticExplorerCases.case_special__formulaLiftingBuiltinValueSlot,
  SemanticExplorerCases.case_special__formulaLiftingBuiltinSignature,
  SemanticExplorerCases.case_special__formulaLiftingLoopSignature,
  SemanticExplorerCases.case_special__formulaLiftingDottedMember,
  SemanticExplorerCases.case_special__formulaLiftingOpenedMember,
  SemanticExplorerCases.case_special__formulaLiftingClauseFamily,
  SemanticExplorerCases.case_special__formulaLiftingCaptureElement,
  SemanticExplorerCases.case_special__formulaLiftingStringReceiver,
  SemanticExplorerCases.case_special__formulaLiftingNestedInUserArgument,
  SemanticExplorerCases.case_special__formulaLiftingKeepsCallbacks,
  SemanticExplorerCases.case_special__formulaLiftingKeepsUserArguments,
  SemanticExplorerCases.case_special__repeatedNameCallableThenValue,
  SemanticExplorerCases.case_special__repeatedNameValueThenCallable,
  SemanticExplorerCases.case_special__repeatedNameFailedThenValue,
  SemanticExplorerCases.case_special__repeatedNameValueThenFailed,
  SemanticExplorerCases.case_special__repeatedNameAcrossCollectorCallable,
  SemanticExplorerCases.case_special__repeatedNameAcrossNestedGroupFailed,
  SemanticExplorerCases.case_special__repeatedNameForwardedCallable,
  SemanticExplorerCases.case_special__repeatedNameDotReceiverFailed,
  SemanticExplorerCases.case_special__repeatedNameValuelessBeforeVerdict,
  SemanticExplorerCases.case_special__repeatedNameAccompanyingChannel,
  SemanticExplorerCases.case_special__forwardByNameAlias,
  SemanticExplorerCases.case_special__forwardByNameThreeOccurrences,
  SemanticExplorerCases.case_special__forwardByNameNestedGroup,
  SemanticExplorerCases.case_special__forwardByNameAcrossGroup,
  SemanticExplorerCases.case_special__forwardByNameInsideOneGroup,
  SemanticExplorerCases.case_special__forwardByNameBesideCollector,
  SemanticExplorerCases.case_special__forwardByNameClosedList,
  SemanticExplorerCases.case_special__forwardByNameAcrossCallees,
  SemanticExplorerCases.case_special__forwardByNameFailedArgument,
  SemanticExplorerCases.case_special__forwardByNameCallableArgument,
  SemanticExplorerCases.case_special__aliasKeepsRepeatedSignature,
  SemanticExplorerCases.case_special__aliasKeepsRepeatedConstraint,
  SemanticExplorerCases.case_special__aliasKeepsListPattern,
  SemanticExplorerCases.case_special__aliasKeepsListPatternRejection,
  SemanticExplorerCases.case_special__aliasKeepsBinderlessSignature,
  SemanticExplorerCases.case_special__aliasOfCollectorKeepsSignature,
  SemanticExplorerCases.case_special__aliasChainKeepsSignature,
  SemanticExplorerCases.case_special__aliasOfBuiltinCount,
  SemanticExplorerCases.case_special__aliasOfIfIsLazy,
  SemanticExplorerCases.case_special__aliasOfMapDemandsNoCallback,
  SemanticExplorerCases.case_special__aliasOfRepeatKeepsMinimumArity,
  SemanticExplorerCases.case_special__aliasChainOfBuiltin,
  SemanticExplorerCases.case_special__aliasOfFamilyDispatches,
  SemanticExplorerCases.case_special__aliasOfFamilyNoMatchingBranch,
  SemanticExplorerCases.case_special__aliasOfUnnameableFamily,
  SemanticExplorerCases.case_special__aliasRolesAreTargetRoles,
  SemanticExplorerCases.case_special__aliasCallableIdentityIsTarget,
  SemanticExplorerCases.case_special__aliasPassedAsCallableNavigatesTarget,
  SemanticExplorerCases.case_special__bareForwardingThroughAlias,
  SemanticExplorerCases.case_special__formulaLiftingThroughAlias,
  SemanticExplorerCases.case_special__bareForwardingSameName,
  SemanticExplorerCases.case_special__bareForwardingIsNotPositional,
  SemanticExplorerCases.case_special__bareForwardingIgnoresUnusedParameter,
  SemanticExplorerCases.case_special__bareForwardingOfAZeroParameterTarget,
  SemanticExplorerCases.case_special__bareForwardingSamePattern,
  SemanticExplorerCases.case_special__bareForwardingRespreadsItsCollector,
  SemanticExplorerCases.case_special__bareForwardingBranchForwardsItsBinder,
  SemanticExplorerCases.case_special__bareForwardingReusesEnclosingBinding,
  SemanticExplorerCases.case_special__bareForwardingRepeatedName,
  SemanticExplorerCases.case_special__writtenCallInfersWrittenNames,
  SemanticExplorerCases.case_special__writtenCallIgnoresCalleeBinderNames,
  SemanticExplorerCases.case_special__huntGenLoopsAG0000,
  SemanticExplorerCases.case_special__huntGenLoopsAG0001,
  SemanticExplorerCases.case_special__huntGenLoopsAG0002,
  SemanticExplorerCases.case_special__huntGenLoopsAG0003,
  SemanticExplorerCases.case_special__huntGenLoopsAG0004,
  SemanticExplorerCases.case_special__huntGenLoopsAG0005,
  SemanticExplorerCases.case_special__huntGenLoopsAG0006,
  SemanticExplorerCases.case_special__huntGenLoopsAG0007,
  SemanticExplorerCases.case_special__huntGenLoopsAG0008,
  SemanticExplorerCases.case_special__huntGenLoopsAG0009,
  SemanticExplorerCases.case_special__huntGenLoopsAG0010,
  SemanticExplorerCases.case_special__huntGenLoopsAG0011,
  SemanticExplorerCases.case_special__huntGenLoopsAG0012,
  SemanticExplorerCases.case_special__huntGenLoopsAG0013,
  SemanticExplorerCases.case_special__huntGenLoopsAG0014,
  SemanticExplorerCases.case_special__huntGenLoopsAG0015,
  SemanticExplorerCases.case_special__huntGenLoopsAG0016,
  SemanticExplorerCases.case_special__huntGenLoopsAG0017,
  SemanticExplorerCases.case_special__huntGenLoopsAG0018,
  SemanticExplorerCases.case_special__huntGenLoopsAG0019,
  SemanticExplorerCases.case_special__huntGenLoopsAG0020,
  SemanticExplorerCases.case_special__huntGenLoopsAG0021,
  SemanticExplorerCases.case_special__huntGenLoopsAG0022,
  SemanticExplorerCases.case_special__huntGenLoopsAG0023,
  SemanticExplorerCases.case_special__huntGenLoopsAG0024,
  SemanticExplorerCases.case_special__huntGenFusionAU0000,
  SemanticExplorerCases.case_special__huntGenFusionAU0001,
  SemanticExplorerCases.case_special__huntGenFusionAU0002,
  SemanticExplorerCases.case_special__huntGenFusionAU0003,
  SemanticExplorerCases.case_special__huntGenFusionAU0004,
  SemanticExplorerCases.case_special__huntGenFusionAU0005,
  SemanticExplorerCases.case_special__huntGenFusionAU0006,
  SemanticExplorerCases.case_special__huntGenFusionAU0007,
  SemanticExplorerCases.case_special__huntGenFusionAU0008,
  SemanticExplorerCases.case_special__huntGenFusionAU0009,
  SemanticExplorerCases.case_special__huntGenFusionAU0010,
  SemanticExplorerCases.case_special__huntGenFusionAU0011,
  SemanticExplorerCases.case_special__huntGenFusionAU0012,
  SemanticExplorerCases.case_special__huntGenFusionAU0013,
  SemanticExplorerCases.case_special__huntGenFusionAU0014,
  SemanticExplorerCases.case_special__huntGenFusionAU0015,
  SemanticExplorerCases.case_special__huntGenFusionAU0016,
  SemanticExplorerCases.case_special__huntGenFusionAU0017,
  SemanticExplorerCases.case_special__huntGenFusionAU0018,
  SemanticExplorerCases.case_special__huntGenFusionAU0019,
  SemanticExplorerCases.case_special__huntGenFaultsAF0000,
  SemanticExplorerCases.case_special__huntGenFaultsAF0001,
  SemanticExplorerCases.case_special__huntGenFaultsAF0002,
  SemanticExplorerCases.case_special__huntGenFaultsAF0003,
  SemanticExplorerCases.case_special__huntGenFaultsAF0004,
  SemanticExplorerCases.case_special__huntGenFaultsAF0005,
  SemanticExplorerCases.case_special__huntGenFaultsAF0006,
  SemanticExplorerCases.case_special__huntGenFaultsAF0007,
  SemanticExplorerCases.case_special__huntGenFaultsAF0008,
  SemanticExplorerCases.case_special__huntGenFaultsAF0009,
  SemanticExplorerCases.case_special__huntGenFaultsAF0010,
  SemanticExplorerCases.case_special__huntGenFaultsAF0011,
  SemanticExplorerCases.case_special__huntGenFaultsAF0012,
  SemanticExplorerCases.case_special__huntGenFaultsAF0013,
  SemanticExplorerCases.case_special__huntGenFaultsAF0014,
  SemanticExplorerCases.case_special__huntGenFaultsAF0015,
  SemanticExplorerCases.case_special__huntGenFaultsAF0016,
  SemanticExplorerCases.case_special__huntGenFaultsAF0017,
  SemanticExplorerCases.case_special__huntGenFaultsAF0018,
  SemanticExplorerCases.case_special__huntGenFaultsAF0019,
  SemanticExplorerCases.case_special__huntGenInferAI0000Base,
  SemanticExplorerCases.case_special__huntGenInferAI0001Base,
  SemanticExplorerCases.case_special__huntGenInferAI0002Base,
  SemanticExplorerCases.case_special__huntGenInferAI0003Base,
  SemanticExplorerCases.case_special__huntGenInferAI0004Base,
  SemanticExplorerCases.case_special__huntGenInferAI0005Base,
  SemanticExplorerCases.case_special__huntGenInferAI0006Base,
  SemanticExplorerCases.case_special__huntGenInferAI0007Base,
  SemanticExplorerCases.case_special__huntGenInferAI0008Base,
  SemanticExplorerCases.case_special__huntGenInferAI0009Base,
  SemanticExplorerCases.case_special__huntGenInferAI0010Base,
  SemanticExplorerCases.case_special__huntGenInferAI0011Base,
  SemanticExplorerCases.case_special__huntGenInferAI0012Base,
  SemanticExplorerCases.case_special__huntGenInferAI0013Base,
  SemanticExplorerCases.case_special__huntGenInferAI0014Base,
  SemanticExplorerCases.case_special__huntGenInferAI0015Base,
  SemanticExplorerCases.case_special__huntGenInferAI0016Base,
  SemanticExplorerCases.case_special__huntGenInferAI0017Base,
  SemanticExplorerCases.case_special__huntGenInferAI0018Base,
  SemanticExplorerCases.case_special__huntGenInferAI0019Base,
  SemanticExplorerCases.case_special__huntGenEqAQ0000,
  SemanticExplorerCases.case_special__huntGenEqAQ0001,
  SemanticExplorerCases.case_special__huntGenEqAQ0002,
  SemanticExplorerCases.case_special__huntGenEqAQ0003,
  SemanticExplorerCases.case_special__huntGenEqAQ0004,
  SemanticExplorerCases.case_special__huntGenEqAQ0005,
  SemanticExplorerCases.case_special__huntGenEqAQ0006,
  SemanticExplorerCases.case_special__huntGenEqAQ0007,
  SemanticExplorerCases.case_special__huntGenEqAQ0008,
  SemanticExplorerCases.case_special__huntGenEqAQ0009,
  SemanticExplorerCases.case_special__huntGenEqAQ0010,
  SemanticExplorerCases.case_special__huntGenEqAQ0011,
  SemanticExplorerCases.case_special__huntGenEqAQ0012,
  SemanticExplorerCases.case_special__huntGenEqAQ0013,
  SemanticExplorerCases.case_special__huntGenEqAQ0014,
  SemanticExplorerCases.case_special__huntGenExpoAX0000Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0001Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0002Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0003Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0004Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0005Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0006Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0007Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0008Pair,
  SemanticExplorerCases.case_special__huntGenExpoAX0009Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0000Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0001Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0002Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0003Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0004Pair,
  SemanticExplorerCases.case_special__huntGenExpo2AY0005Pair,
  SemanticExplorerCases.case_special__huntGenChaosGZ0000,
  SemanticExplorerCases.case_special__huntGenChaosGZ0001,
  SemanticExplorerCases.case_special__huntGenChaosGZ0002,
  SemanticExplorerCases.case_special__huntGenChaosGZ0005,
  SemanticExplorerCases.case_special__huntGenChaosGZ0006,
  SemanticExplorerCases.case_special__huntGenChaosGZ0010,
  SemanticExplorerCases.case_special__huntGenChaosGZ0013,
  SemanticExplorerCases.case_special__huntGenChaosGZ0015,
  SemanticExplorerCases.case_special__huntGenChaosGZ0017,
  SemanticExplorerCases.case_special__huntGenChaosGZ0020,
  SemanticExplorerCases.case_special__huntA1Expo1E01Direct,
  SemanticExplorerCases.case_special__huntA1Expo1E02Member,
  SemanticExplorerCases.case_special__huntA1Expo1E05Alias,
  SemanticExplorerCases.case_special__huntA1Expo1E07RuntimeAliasParam,
  SemanticExplorerCases.case_special__huntA1Expo1E09DeconBoth,
  SemanticExplorerCases.case_special__huntA1Expo1E10ClauseBinder,
  SemanticExplorerCases.case_special__huntA2Need1N01UndemandedSecond,
  SemanticExplorerCases.case_special__huntA2Need1N02DemandOrder,
  SemanticExplorerCases.case_special__huntA2Need1N03AtMostOnce,
  SemanticExplorerCases.case_special__huntA2Need1N04NeverDemanded,
  SemanticExplorerCases.case_special__huntA2Need1N05ForwardingNoForce,
  SemanticExplorerCases.case_special__huntA2Need1N06CardinalityFirst,
  SemanticExplorerCases.case_special__huntA2Need2T01MemberPathTransport,
  SemanticExplorerCases.case_special__huntA2Need2T02AliasChainTransport,
  SemanticExplorerCases.case_special__huntA2Need2T03ParamHoldingReference,
  SemanticExplorerCases.case_special__huntA2Need2T04CountThroughAlias,
  SemanticExplorerCases.case_special__huntA2Need2T05FirstThroughAlias,
  SemanticExplorerCases.case_special__huntA2Need2T06SelectThroughMember,
  SemanticExplorerCases.case_special__huntA3Cache1C01ReentrantQ37,
  SemanticExplorerCases.case_special__huntA3Cache1C02CollectingAliasOnce,
  SemanticExplorerCases.case_special__huntA3Cache1C03AliasRead,
  SemanticExplorerCases.case_special__huntA3Cache1C04AliasCallEstablishes,
  SemanticExplorerCases.case_special__huntA3Cache1C06CarrierCalls,
  SemanticExplorerCases.case_special__huntA3Cache1C07RuntimeMemberValueOnly,
  SemanticExplorerCases.case_special__huntA3Cache2C203FormulaOwnerReadFirst,
  SemanticExplorerCases.case_special__huntA3Cache2C204ExportedOwner,
  SemanticExplorerCases.case_special__huntA3Cache2C205CallbackMemberRead,
  SemanticExplorerCases.case_special__huntA3Cache2C206AliasCellExported,
  SemanticExplorerCases.case_special__huntA3Cache2C207AliasCellLocal,
  SemanticExplorerCases.case_special__huntA3Cache2C208AliasCellInLoopStep,
  SemanticExplorerCases.case_special__huntA3Cache3C301tPropertyTwinExported,
  SemanticExplorerCases.case_special__huntA3Cache3C302tPropertyTwinLocal,
  SemanticExplorerCases.case_special__huntA3Cache3C303AliasCellLoop,
  SemanticExplorerCases.case_special__huntA3Cache3C303tPropertyTwinLoop,
  SemanticExplorerCases.case_special__huntA3Cache3C304tPropertyTwinLocalLoop,
  SemanticExplorerCases.case_special__huntA3Cache3C305AliasCellReadAndCall,
  SemanticExplorerCases.case_special__huntA4Loops1L01WhileBasic,
  SemanticExplorerCases.case_special__huntA4Loops1L08FamilyStep,
  SemanticExplorerCases.case_special__huntA4Loops1L10AliasStep,
  SemanticExplorerCases.case_special__huntA4Loops1L13LoopOneValue,
  SemanticExplorerCases.case_special__huntA4Loops1L14ForwardStep,
  SemanticExplorerCases.case_special__huntA4Loops1L16QualifiedStep,
  SemanticExplorerCases.case_special__huntA5Select1S03StringCount,
  SemanticExplorerCases.case_special__huntA5Select1S04EmptyStringSelect,
  SemanticExplorerCases.case_special__huntA5Select1S05StringOnePosition,
  SemanticExplorerCases.case_special__huntA5Select1S06ScalarSelf,
  SemanticExplorerCases.case_special__huntA5Select1S07ScalarOut,
  SemanticExplorerCases.case_special__huntA6Spread1P01CollTable,
  SemanticExplorerCases.case_special__huntA6Spread1P02Cnt,
  SemanticExplorerCases.case_special__huntA6Spread1P03CntValue,
  SemanticExplorerCases.case_special__huntA6Spread1P04Withhead,
  SemanticExplorerCases.case_special__huntA6Spread1P05IdPair,
  SemanticExplorerCases.case_special__huntA6Spread1P06AddPair,
  SemanticExplorerCases.case_special__huntA7Dot1D01ChainFallback,
  SemanticExplorerCases.case_special__huntA7Dot1D02DeclaredString,
  SemanticExplorerCases.case_special__huntA7Dot1D03LexicalStringIgnored,
  SemanticExplorerCases.case_special__huntA7Dot1D04BranchMember,
  SemanticExplorerCases.case_special__huntA7Dot1D05PrivateStructural,
  SemanticExplorerCases.case_special__huntA7Dot1D06SpreadReceiver,
  SemanticExplorerCases.case_special__huntA7Anchor1H01StatedCarriedContainer,
  SemanticExplorerCases.case_special__huntA7Anchor1H05OpenHeadBetween,
  SemanticExplorerCases.case_special__huntA7Anchor1H06CarriedViaCallback,
  SemanticExplorerCases.case_special__huntA7Anchor1H08CarriedThroughParamChain,
  SemanticExplorerCases.case_special__huntA7Anchor1H09ContainerReadAtRoot,
  SemanticExplorerCases.case_special__huntA7Anchor1H11ContainerThroughLoopState,
  SemanticExplorerCases.case_special__huntA8Alias1X01CarrierForwards,
  SemanticExplorerCases.case_special__huntA8Alias1X02CarrierZeroCall,
  SemanticExplorerCases.case_special__huntA8Alias1X05TransparentMember,
  SemanticExplorerCases.case_special__huntA8Alias1X06CarrierNotTargetIdentity,
  SemanticExplorerCases.case_special__huntA9Meta1M02InvokeFresh,
  SemanticExplorerCases.case_special__huntA9Meta1M05ArgumentsSelect,
  SemanticExplorerCases.case_special__huntA9Meta1M06ArgumentsSelectFail,
  SemanticExplorerCases.case_special__huntA9Meta1M08ArgumentsEmpty,
  SemanticExplorerCases.case_special__huntA9Meta1M09AlgorithmFresh,
  SemanticExplorerCases.case_special__huntA9Meta1M10Identity,
  SemanticExplorerCases.case_special__huntA9Meta2M202ArgumentsCycle,
  SemanticExplorerCases.case_special__huntA9Meta2M204MultiSelectView,
  SemanticExplorerCases.case_special__huntA9Meta2M205RebuildCall,
  SemanticExplorerCases.case_special__huntA9Meta2M206SameRefs,
  SemanticExplorerCases.case_special__huntA9Meta2M207SameDifferentRefs,
  SemanticExplorerCases.case_special__huntA9Meta2M208ForwardedReference,
  SemanticExplorerCases.case_special__huntA10Fe1F01CountFormula,
  SemanticExplorerCases.case_special__huntA10Fe1F02IfFormula,
  SemanticExplorerCases.case_special__huntA10Fe1F03RepeatFormula,
  SemanticExplorerCases.case_special__huntA10Fe1F05rMutualLiftReordered,
  SemanticExplorerCases.case_special__huntA10Fe1F07WhileRepeatFormula,
  SemanticExplorerCases.case_special__huntA10Fe1F08BareForwardSameName,
  SemanticExplorerCases.case_special__huntA10Spread1W01ArgSlot,
  SemanticExplorerCases.case_special__huntA10Spread1W01xArgSlotExplicit,
  SemanticExplorerCases.case_special__huntA10Spread1W02List,
  SemanticExplorerCases.case_special__huntA10Spread1W03Group,
  SemanticExplorerCases.case_special__huntA10Spread1W04RootRow,
  SemanticExplorerCases.case_special__huntA10Spread1W04xRootRowExplicit,
  SemanticExplorerCases.case_special__huntA10Fwd1Fw08ForwardCollectorIntoCollector,
  SemanticExplorerCases.case_special__huntA10Fwd1Fw15ForwardingChain,
  SemanticExplorerCases.case_special__huntA10Fwd1Fw18ForwardIf,
  SemanticExplorerCases.case_special__huntA10Fwd1Fw19AliasOfMap,
  SemanticExplorerCases.case_special__huntA10Fwd1Fw20ClosedFormulaBuiltin,
  SemanticExplorerCases.case_special__huntA11Cmp1K03TotalEquality,
  SemanticExplorerCases.case_special__huntA11Cmp1K04IfNumber,
  SemanticExplorerCases.case_special__huntA11Cmp1K05TickOnce,
  SemanticExplorerCases.case_special__huntA11Cmp1K06TickEq,
  SemanticExplorerCases.case_special__huntA12Builtins1B01IfLazy,
  SemanticExplorerCases.case_special__huntA12Builtins1B02IfCondFail,
  SemanticExplorerCases.case_special__huntA12Builtins1B04MapTwoRows,
  SemanticExplorerCases.case_special__huntA12Builtins1B05MapEmptyRow,
  SemanticExplorerCases.case_special__huntA12Builtins1B06FilterNonbool,
  SemanticExplorerCases.case_special__huntA12Edge2G01WhileEmptySpreadOnly,
  SemanticExplorerCases.case_special__huntA12Edge2G02WhileEmptyRow,
  SemanticExplorerCases.case_special__huntA12Edge2G03WhileListFlag,
  SemanticExplorerCases.case_special__huntA12Edge2G04RepeatZeroRowStep,
  SemanticExplorerCases.case_special__huntA12Edge2G05RepeatEmptyState,
  SemanticExplorerCases.case_special__huntA12Edge2G06FamilyBool,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh01UserFilterCount,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh02UserFilterBuiltinCount,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh03BuiltinFilterUserCount,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh04UserCountCallForm,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh05UserRange,
  SemanticExplorerCases.case_special__huntA12Shadow1Sh06UserIfInLoop,
  SemanticExplorerCases.case_special__huntA13Arith1R01DivSigns,
  SemanticExplorerCases.case_special__huntA13Arith1R02ExactDiv,
  SemanticExplorerCases.case_special__huntA13Arith1R03Pow,
  SemanticExplorerCases.case_special__huntA13Arith1R04ZeroNegPow,
  SemanticExplorerCases.case_special__huntA13Arith1R05ModZero,
  SemanticExplorerCases.case_special__huntA13Arith1R06DivZero,
  SemanticExplorerCases.case_special__huntA14Open1O01SameProviderTwice,
  SemanticExplorerCases.case_special__huntA14Open1O02SameProviderGrouped,
  SemanticExplorerCases.case_special__huntA14Open1O03AliasProviderSame,
  SemanticExplorerCases.case_special__huntA14Open1O05CountShadow,
  SemanticExplorerCases.case_special__huntA14Open1O06CountUserCallable,
  SemanticExplorerCases.case_special__huntA14Open1O09OpenPrivateNotProvided
]
#guard explorerPrograms.length == 2808
#guard (explorerPrograms.filter Expr.mayCaptureCalls).length == 131

/-! ## explorer-internal -/

#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_e_1 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_1_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_e_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_p12_e == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_e_p12 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_1_2 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_p12_p34 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_3 == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_lone_list == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_lone_empty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_lone_pair == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_stacked_lone == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_spread_missing_output == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_count_arg == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_take_collection == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_take_collection_empty == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_take_block_leaf == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_sum_arg == false
#guard Expr.mayCaptureCalls SemanticExplorerCases.case_internal__sc_call_function == false

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def explorerInternalPrograms : List Expr := [
  SemanticExplorerCases.case_internal__sc_e_1,
  SemanticExplorerCases.case_internal__sc_1_e,
  SemanticExplorerCases.case_internal__sc_e_e,
  SemanticExplorerCases.case_internal__sc_p12_e,
  SemanticExplorerCases.case_internal__sc_e_p12,
  SemanticExplorerCases.case_internal__sc_1_2,
  SemanticExplorerCases.case_internal__sc_p12_p34,
  SemanticExplorerCases.case_internal__sc_spread_3,
  SemanticExplorerCases.case_internal__sc_spread_lone_list,
  SemanticExplorerCases.case_internal__sc_spread_lone_empty,
  SemanticExplorerCases.case_internal__sc_spread_lone_pair,
  SemanticExplorerCases.case_internal__sc_spread_stacked_lone,
  SemanticExplorerCases.case_internal__sc_spread_missing_output,
  SemanticExplorerCases.case_internal__sc_count_arg,
  SemanticExplorerCases.case_internal__sc_take_collection,
  SemanticExplorerCases.case_internal__sc_take_collection_empty,
  SemanticExplorerCases.case_internal__sc_take_block_leaf,
  SemanticExplorerCases.case_internal__sc_sum_arg,
  SemanticExplorerCases.case_internal__sc_call_function
]
#guard explorerInternalPrograms.length == 19
#guard (explorerInternalPrograms.filter Expr.mayCaptureCalls).length == 0

/-! ## generated -/

#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F6 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F6_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F7 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F7_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Fcache == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Fcache_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Ffailure == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Ffailure_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Fasync == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Fasync_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_2Dcrossed == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_2Dcrossed_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dflag_2Dfirst == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dflag_2Dfirst_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dfault == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dfault_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fspread_2Dformation == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fspread_2Dformation_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fretained == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fretained_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Feager_2Dresult == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Feager_2Dresult_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freject == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freject_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_2Dsame_2Dargs == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_2Dsame_2Dargs_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_2Dsame_2Dargs == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_2Dsame_2Dargs_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F7 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F7_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F10 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F10_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F11 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F11_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F10 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F10_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F11 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F11_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F5 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F5_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F8 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F8_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F9 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F9_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F12 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F12_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F13 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F13_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15 == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15_alpha == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15_reorder == true
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0_reorder == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F1 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F1_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F2 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F2_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3 == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3_alpha == false
#guard Expr.mayCaptureCalls SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3_reorder == false

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def generatedPrograms : List Expr := [
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2F7_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fmeta_2Dfail_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcollect_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Falias_2Dfail_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2F7_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Floop_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ffailure_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fasync_2Dfail_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Falias_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Fcache,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Flist_2Fcache_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fmeta_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Fcollect_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Fselect_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fwrapper_2Floop_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Ffailure,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Ffailure_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Fasync,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcontext_2Fbrace_2Fasync_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bcache_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bselect_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Falias_2Bmeta_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcache_2Basync_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Bmeta_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Floop_2Basync_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fcancel_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fguard_2Fnested_2Dpattern_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Ffilter_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Freduce_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fcallback_2Fmap_2Dfault_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_2Dcrossed,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Frepeat_2Drows_2Dcrossed_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dflag_2Dfirst,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dflag_2Dfirst_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Ddead_2Dtransition_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dfault,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Floop_2Fwhile_2Dfault_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freceiver_2Dfirst_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fspread_2Dformation,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fspread_2Dformation_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fretained,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Fretained_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Feager_2Dresult,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Feager_2Dresult_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freject,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fselect_2Freject_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fcarrier_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Ftransparent_2Dchain_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fmember_2Fpassed_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_2Dsame_2Dargs,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Finner_2Dlocal_2Dsame_2Dargs_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_2Dsame_2Dargs,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fouter_2Dlocal_2Dsame_2Dargs_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fsys_2Ftick_2Fowners_2Fchain_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F8_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F9_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F13_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000001_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F8_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F9_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F12_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F13_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F14_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000002_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F7_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F8_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F9_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F10_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F11_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F12_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F13_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F14_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000003_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F10_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F11_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F12_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F13_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F14_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000004_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F7_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F8_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F9_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F10_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F11_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F12_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F13_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F14_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000005_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F4_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F5_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F6_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F7_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F8_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F9_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F10_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F11_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F12,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F12_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F13,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F13_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F14_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2F5EED2B000006_2F15_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F1_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F2_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000001_2F3_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F0_reorder,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F1,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F1_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F2,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F2_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3_alpha,
  SemanticGeneratedCases.case_sem2b_2Fv2_2Fseed_2Dnested_2F5EED2B000002_2F3_reorder
]
#guard generatedPrograms.length == 735
#guard (generatedPrograms.filter Expr.mayCaptureCalls).length == 365

/-! ## host-parent -/

#guard Expr.mayCaptureCalls HostParentDifferential.hp_01a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_01b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_01c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_01d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_02f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_03a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_03b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_03c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_03d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_03e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_04a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_04b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_04c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05i == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05j == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_05k == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_06a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_06b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_06c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_06d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_07a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_07b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08i == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08j == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_08k == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_09a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_09b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_09c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_09d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_10i == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_11a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_11b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_11c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_11d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_11e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_12a == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_12b == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_12c == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_12d == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13i == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13j == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13k == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13l == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_13m == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14i == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14j == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14k == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14l == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14m == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14n == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14o == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14p == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14q == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14r == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14s == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14t == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14u == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_14v == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_15a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_15b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_15c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_15d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_15e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_16a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_16b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_16c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_17a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_17b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18a == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18b == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18d == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18e == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18f == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18g == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18h == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18i == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18j == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18k == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18l == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18m == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18n == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18o == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18p == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18q == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18r == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18s == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18t == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_18u == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19a == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19b == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19c == false
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19d == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19e == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19f == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19g == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19h == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19i == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19j == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19k == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19l == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19m == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19n == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19o == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19p == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19q == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19r == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19s == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19t == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19u == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19v == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19w == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19x == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19y == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_19z == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20a == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20b == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20c == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20d == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20e == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20f == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20g == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20h == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_20i == true
#guard Expr.mayCaptureCalls HostParentDifferential.hp_21a == true

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def hostParentPrograms : List Expr := [
  HostParentDifferential.hp_01a,
  HostParentDifferential.hp_01b,
  HostParentDifferential.hp_01c,
  HostParentDifferential.hp_01d,
  HostParentDifferential.hp_02a,
  HostParentDifferential.hp_02b,
  HostParentDifferential.hp_02c,
  HostParentDifferential.hp_02d,
  HostParentDifferential.hp_02e,
  HostParentDifferential.hp_02f,
  HostParentDifferential.hp_03a,
  HostParentDifferential.hp_03b,
  HostParentDifferential.hp_03c,
  HostParentDifferential.hp_03d,
  HostParentDifferential.hp_03e,
  HostParentDifferential.hp_04a,
  HostParentDifferential.hp_04b,
  HostParentDifferential.hp_04c,
  HostParentDifferential.hp_05a,
  HostParentDifferential.hp_05b,
  HostParentDifferential.hp_05c,
  HostParentDifferential.hp_05d,
  HostParentDifferential.hp_05e,
  HostParentDifferential.hp_05f,
  HostParentDifferential.hp_05g,
  HostParentDifferential.hp_05h,
  HostParentDifferential.hp_05i,
  HostParentDifferential.hp_05j,
  HostParentDifferential.hp_05k,
  HostParentDifferential.hp_06a,
  HostParentDifferential.hp_06b,
  HostParentDifferential.hp_06c,
  HostParentDifferential.hp_06d,
  HostParentDifferential.hp_07a,
  HostParentDifferential.hp_07b,
  HostParentDifferential.hp_08a,
  HostParentDifferential.hp_08b,
  HostParentDifferential.hp_08c,
  HostParentDifferential.hp_08d,
  HostParentDifferential.hp_08e,
  HostParentDifferential.hp_08f,
  HostParentDifferential.hp_08g,
  HostParentDifferential.hp_08h,
  HostParentDifferential.hp_08i,
  HostParentDifferential.hp_08j,
  HostParentDifferential.hp_08k,
  HostParentDifferential.hp_09a,
  HostParentDifferential.hp_09b,
  HostParentDifferential.hp_09c,
  HostParentDifferential.hp_09d,
  HostParentDifferential.hp_10a,
  HostParentDifferential.hp_10b,
  HostParentDifferential.hp_10c,
  HostParentDifferential.hp_10d,
  HostParentDifferential.hp_10e,
  HostParentDifferential.hp_10f,
  HostParentDifferential.hp_10g,
  HostParentDifferential.hp_10h,
  HostParentDifferential.hp_10i,
  HostParentDifferential.hp_11a,
  HostParentDifferential.hp_11b,
  HostParentDifferential.hp_11c,
  HostParentDifferential.hp_11d,
  HostParentDifferential.hp_11e,
  HostParentDifferential.hp_12a,
  HostParentDifferential.hp_12b,
  HostParentDifferential.hp_12c,
  HostParentDifferential.hp_12d,
  HostParentDifferential.hp_13a,
  HostParentDifferential.hp_13b,
  HostParentDifferential.hp_13c,
  HostParentDifferential.hp_13d,
  HostParentDifferential.hp_13e,
  HostParentDifferential.hp_13f,
  HostParentDifferential.hp_13g,
  HostParentDifferential.hp_13h,
  HostParentDifferential.hp_13i,
  HostParentDifferential.hp_13j,
  HostParentDifferential.hp_13k,
  HostParentDifferential.hp_13l,
  HostParentDifferential.hp_13m,
  HostParentDifferential.hp_14a,
  HostParentDifferential.hp_14b,
  HostParentDifferential.hp_14c,
  HostParentDifferential.hp_14d,
  HostParentDifferential.hp_14e,
  HostParentDifferential.hp_14f,
  HostParentDifferential.hp_14g,
  HostParentDifferential.hp_14h,
  HostParentDifferential.hp_14i,
  HostParentDifferential.hp_14j,
  HostParentDifferential.hp_14k,
  HostParentDifferential.hp_14l,
  HostParentDifferential.hp_14m,
  HostParentDifferential.hp_14n,
  HostParentDifferential.hp_14o,
  HostParentDifferential.hp_14p,
  HostParentDifferential.hp_14q,
  HostParentDifferential.hp_14r,
  HostParentDifferential.hp_14s,
  HostParentDifferential.hp_14t,
  HostParentDifferential.hp_14u,
  HostParentDifferential.hp_14v,
  HostParentDifferential.hp_15a,
  HostParentDifferential.hp_15b,
  HostParentDifferential.hp_15c,
  HostParentDifferential.hp_15d,
  HostParentDifferential.hp_15e,
  HostParentDifferential.hp_16a,
  HostParentDifferential.hp_16b,
  HostParentDifferential.hp_16c,
  HostParentDifferential.hp_17a,
  HostParentDifferential.hp_17b,
  HostParentDifferential.hp_18a,
  HostParentDifferential.hp_18b,
  HostParentDifferential.hp_18c,
  HostParentDifferential.hp_18d,
  HostParentDifferential.hp_18e,
  HostParentDifferential.hp_18f,
  HostParentDifferential.hp_18g,
  HostParentDifferential.hp_18h,
  HostParentDifferential.hp_18i,
  HostParentDifferential.hp_18j,
  HostParentDifferential.hp_18k,
  HostParentDifferential.hp_18l,
  HostParentDifferential.hp_18m,
  HostParentDifferential.hp_18n,
  HostParentDifferential.hp_18o,
  HostParentDifferential.hp_18p,
  HostParentDifferential.hp_18q,
  HostParentDifferential.hp_18r,
  HostParentDifferential.hp_18s,
  HostParentDifferential.hp_18t,
  HostParentDifferential.hp_18u,
  HostParentDifferential.hp_19a,
  HostParentDifferential.hp_19b,
  HostParentDifferential.hp_19c,
  HostParentDifferential.hp_19d,
  HostParentDifferential.hp_19e,
  HostParentDifferential.hp_19f,
  HostParentDifferential.hp_19g,
  HostParentDifferential.hp_19h,
  HostParentDifferential.hp_19i,
  HostParentDifferential.hp_19j,
  HostParentDifferential.hp_19k,
  HostParentDifferential.hp_19l,
  HostParentDifferential.hp_19m,
  HostParentDifferential.hp_19n,
  HostParentDifferential.hp_19o,
  HostParentDifferential.hp_19p,
  HostParentDifferential.hp_19q,
  HostParentDifferential.hp_19r,
  HostParentDifferential.hp_19s,
  HostParentDifferential.hp_19t,
  HostParentDifferential.hp_19u,
  HostParentDifferential.hp_19v,
  HostParentDifferential.hp_19w,
  HostParentDifferential.hp_19x,
  HostParentDifferential.hp_19y,
  HostParentDifferential.hp_19z,
  HostParentDifferential.hp_20a,
  HostParentDifferential.hp_20b,
  HostParentDifferential.hp_20c,
  HostParentDifferential.hp_20d,
  HostParentDifferential.hp_20e,
  HostParentDifferential.hp_20f,
  HostParentDifferential.hp_20g,
  HostParentDifferential.hp_20h,
  HostParentDifferential.hp_20i,
  HostParentDifferential.hp_21a
]
#guard hostParentPrograms.length == 170
#guard (hostParentPrograms.filter Expr.mayCaptureCalls).length == 43

/-! ## modules -/

#guard Expr.mayCaptureCalls ModuleDifferential.same_url == false
#guard Expr.mayCaptureCalls ModuleDifferential.nested_first == false
#guard Expr.mayCaptureCalls ModuleDifferential.distinct_url == false
#guard Expr.mayCaptureCalls ModuleDifferential.module_shadow == false
#guard Expr.mayCaptureCalls ModuleDifferential.inline_shadow == false
#guard Expr.mayCaptureCalls ModuleDifferential.one_provider == false
#guard Expr.mayCaptureCalls ModuleDifferential.two_providers == false

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def modulePrograms : List Expr := [
  ModuleDifferential.same_url,
  ModuleDifferential.nested_first,
  ModuleDifferential.distinct_url,
  ModuleDifferential.module_shadow,
  ModuleDifferential.inline_shadow,
  ModuleDifferential.one_provider,
  ModuleDifferential.two_providers
]
#guard modulePrograms.length == 7
#guard (modulePrograms.filter Expr.mayCaptureCalls).length == 0

/-! ## planned-loop-temps -/

#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD0R1K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD0R2K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD0R3K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD1R1K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD1R2K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD1R3K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD2R1K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD2R2K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatPlannedD2R3K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD0R1K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD0R2K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD0R3K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD1R1K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD1R2K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD1R3K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD2R1K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD2R2K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltRepeatFallbackD2R3K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD0R1K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD0R2K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD0R3K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD1R1K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD1R2K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD1R3K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD2R1K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD2R2K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhilePlannedD2R3K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD0R1K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD0R2K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD0R3K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD1R1K2 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD1R2K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD1R3K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD2R1K3 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD2R2K1 == true
#guard Expr.mayCaptureCalls PlannedLoopTempFamily.pltWhileFallbackD2R3K2 == true

/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the
    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/
def plannedLoopTempPrograms : List Expr := [
  PlannedLoopTempFamily.pltRepeatPlannedD0R1K1,
  PlannedLoopTempFamily.pltRepeatPlannedD0R2K2,
  PlannedLoopTempFamily.pltRepeatPlannedD0R3K3,
  PlannedLoopTempFamily.pltRepeatPlannedD1R1K2,
  PlannedLoopTempFamily.pltRepeatPlannedD1R2K3,
  PlannedLoopTempFamily.pltRepeatPlannedD1R3K1,
  PlannedLoopTempFamily.pltRepeatPlannedD2R1K3,
  PlannedLoopTempFamily.pltRepeatPlannedD2R2K1,
  PlannedLoopTempFamily.pltRepeatPlannedD2R3K2,
  PlannedLoopTempFamily.pltRepeatFallbackD0R1K1,
  PlannedLoopTempFamily.pltRepeatFallbackD0R2K2,
  PlannedLoopTempFamily.pltRepeatFallbackD0R3K3,
  PlannedLoopTempFamily.pltRepeatFallbackD1R1K2,
  PlannedLoopTempFamily.pltRepeatFallbackD1R2K3,
  PlannedLoopTempFamily.pltRepeatFallbackD1R3K1,
  PlannedLoopTempFamily.pltRepeatFallbackD2R1K3,
  PlannedLoopTempFamily.pltRepeatFallbackD2R2K1,
  PlannedLoopTempFamily.pltRepeatFallbackD2R3K2,
  PlannedLoopTempFamily.pltWhilePlannedD0R1K1,
  PlannedLoopTempFamily.pltWhilePlannedD0R2K2,
  PlannedLoopTempFamily.pltWhilePlannedD0R3K3,
  PlannedLoopTempFamily.pltWhilePlannedD1R1K2,
  PlannedLoopTempFamily.pltWhilePlannedD1R2K3,
  PlannedLoopTempFamily.pltWhilePlannedD1R3K1,
  PlannedLoopTempFamily.pltWhilePlannedD2R1K3,
  PlannedLoopTempFamily.pltWhilePlannedD2R2K1,
  PlannedLoopTempFamily.pltWhilePlannedD2R3K2,
  PlannedLoopTempFamily.pltWhileFallbackD0R1K1,
  PlannedLoopTempFamily.pltWhileFallbackD0R2K2,
  PlannedLoopTempFamily.pltWhileFallbackD0R3K3,
  PlannedLoopTempFamily.pltWhileFallbackD1R1K2,
  PlannedLoopTempFamily.pltWhileFallbackD1R2K3,
  PlannedLoopTempFamily.pltWhileFallbackD1R3K1,
  PlannedLoopTempFamily.pltWhileFallbackD2R1K3,
  PlannedLoopTempFamily.pltWhileFallbackD2R2K1,
  PlannedLoopTempFamily.pltWhileFallbackD2R3K2
]
#guard plannedLoopTempPrograms.length == 36
#guard (plannedLoopTempPrograms.filter Expr.mayCaptureCalls).length == 36

-- 4472 gate guards over 4610 corpus programs.
end KatLang.MayCaptureCallsCorpus
