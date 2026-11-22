# The mutant catalog of scripts/run-lean-model-mutants.ps1 (docs/design/lean-model-mutation-campaign-2026-11.md).
#
# Each mutant changes ONE decision of the Lean model. `Edits` are literal text substitutions on
# lean/KatLang.lean: every `Find` must occur EXACTLY ONCE in the current model (the runner reports any
# other count as a stale anchor and builds nothing for that mutant), and the substitution is applied
# to a COPY of the model in a scratch Lake workspace, never to the tracked file. Line endings are
# normalized to LF on both sides before matching.
#
#   Name             the id used on the command line and in every log name
#   Group            hunt-gaps      the three mutants no generated corpus killed during the 2026-11-20 hunt (F02-F04)
#                    extension      controls for the rules the hunt report named as the next targets
#                    hunt-controls  the seven other mutants of the hunt, which the corpora already killed then
#   Rule             the rule the model implements at the edited site
#   Change           what the mutant does instead
#   Note             what to know when reading its result (optional)
#   Expect           Killed | Survives: the verdict recorded when the entry was last measured; the runner
#                    fails when a run disagrees, so a lost guard and a closed gap are both noticed
#   RequiredKillers  case ids that must be among the failing guards of a Killed mutant
#   Witnesses        cases in LeanMutationWitnesses that must fail even when every corpus passes
#   Gap              for a Survives entry: where the missing witness is tracked
#
# When the model changes at an edited site, re-derive the anchor from the new text and re-measure the
# entry; never loosen an anchor so that it matches more than one place.
@{
    Mutants = @(
        @{
            Name = 'select-demand-all-first'
            Group = 'hunt-gaps'
            Rule = 'Postfix selection demands and validates each selector left to right; an invalid position ends the selection before a later selector is demanded (call-by-need.md, selective reads; F02).'
            Change = '`selectWith` demands every selector before it validates any position.'
            Expect = 'Killed'
            RequiredKillers = @('hunt-selection-invalid-position-stops-before-later-selector')
            Edits = @(
                @{
                    Find = @'
  | cell :: rest => do
      let selected <- selectPosition receiver (<- demand cell)
      let tail <- selectWith demand receiver rest
      pure (selected :: tail)
'@
                    Replace = @'
  | cell :: rest => do
      let v <- demand cell
      let tail <- selectWith demand receiver rest
      let selected <- selectPosition receiver v
      pure (selected :: tail)
'@
                }
            )
        }
        @{
            Name = 'map-right-to-left'
            Group = 'hunt-gaps'
            Rule = '`map` invokes its callback on the collection items from left to right (sequences-lists-and-calls.md, collection builtins; F03).'
            Change = 'Each `mapLoop` step maps the rest of the collection before its own item.'
            Expect = 'Killed'
            RequiredKillers = @('hunt-builtin-map-callbacks-run-in-collection-order')
            Edits = @(
                @{
                    Find = @'
      | item :: rest => do
          let mappedOut <- withCtx
'@
                    Replace = @'
      | item :: rest => do
          let restMapped0 <- mapLoop rest
          let mappedOut <- withCtx
'@
                }
                @{
                    Find = @'
          let restMapped <- mapLoop rest
          pure (mappedOut.fst :: restMapped)
'@
                    Replace = @'
          let restMapped := restMapped0
          pure (mappedOut.fst :: restMapped)
'@
                }
            )
        }
        @{
            Name = 'compare-preevaluate'
            Group = 'hunt-gaps'
            Rule = 'A comparison chain evaluates each operand exactly once, in written order (syntax.md, comparison chains; F04).'
            Change = 'Every link also evaluates all later operands before it compares, so later operands run more than once.'
            Expect = 'Killed'
            RequiredKillers = @('hunt-comparison-chain-operands-once')
            Edits = @(
                @{
                    Find = @'
        let next <- rec.eval link.operand ctx env
        let linkHolds <- applyComparison
'@
                    Replace = @'
        let next <- rec.eval link.operand ctx env
        let _ <- rest.mapM (fun l => rec.eval l.operand ctx env)
        let linkHolds <- applyComparison
'@
                }
            )
        }
        @{
            Name = 'need04-reference-value-at-once'
            Group = 'extension'
            Rule = 'NEED-04, group-aware: a callable-bearing occurrence of a repeated name waits as a pending obligation while its group has no value anchor; its VALUE is not demanded (`Same(Bad, Bad)` is 0).'
            Change = 'A callable-bearing occurrence without an anchor demands its own VALUE at once (the former VALUE-first order).'
            Note = 'Demanding a cyclic reference never ends in the model: the two `reference-cycle-…` specification cases recurse until Lean aborts that module (about three minutes), so the specification corpus reports no guard for this mutant; the kill is the host-parent corpus''s.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
          let agreed <- match group.anchor with
            | some anchor => checkAnchor capabilities name anchor family [address]
            | none => pure true
'@
                    Replace = @'
          let agreed <- match group.anchor with
            | some anchor => checkAnchor capabilities name anchor family [address]
            | none => do
                let _ <- capabilities.value address
                pure true
'@
                }
            )
        }
        @{
            Name = 'need04-pending-before-anchor'
            Group = 'extension'
            Rule = 'NEED-04, the mixed schedule: the first value-only occurrence of a repeated name demands its own VALUE before the earlier pending callable VALUEs, which follow in occurrence order.'
            Change = 'The first value-only occurrence demands the pending callable VALUEs first and its own VALUE after them.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
    | none => do
        let own <- capabilities.value address
        match group.anchor with
'@
                    Replace = @'
    | none => do
        let _ <- (if group.anchor.isNone then group.pending else []).mapM capabilities.value
        let own <- capabilities.value address
        match group.anchor with
'@
                }
            )
        }
        @{
            Name = 'take-not-a-retained-reader'
            Group = 'extension'
            Rule = '`take` over a retained collector reads positions: its count is demanded and validated before any element, and only the kept prefix is demanded (NEED-07).'
            Change = '`take` is no selective reader of a retained collector: it takes the ordinary route, the whole collection VALUE first and the count after it.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  | .countBuiltin | .firstBuiltin | .lastBuiltin | .takeBuiltin => true
  | _ => false

/-- The collection builtins an argument view supports
'@
                    Replace = @'
  | .countBuiltin | .firstBuiltin | .lastBuiltin => true
  | _ => false

/-- The collection builtins an argument view supports
'@
                }
            )
        }
        @{
            Name = 'take-first-element-before-count'
            Group = 'extension'
            Rule = '`take` over a retained collector demands and validates its count BEFORE any element (`xs.take(0)` over `F(1 / 0)` is `[]`).'
            Change = '`take` over a retained collector demands the collector''s first element before its count; the kept prefix is otherwise unchanged.'
            Expect = 'Survives'
            Witnesses = @('take_zero_skips_failing_first', 'take_count_ticks_before_first_element', 'take_count_failure_outranks_first_element')
            Gap = 'docs/design/lean-model-mutation-campaign-2026-11.md, gap G1'
            Edits = @(
                @{
                    Find = @'
            if let some slice <- EvalBody.retainedSliceAt? rec address then
              let suffixArgs <- prepareControls metadata.suffixArgs controlItems
'@
                    Replace = @'
            if let some slice <- EvalBody.retainedSliceAt? rec address then
              if b == Builtin.takeBuiltin then
                discard ((slice.take 1).mapM rec.demandNeedRecursive)
              let suffixArgs <- prepareControls metadata.suffixArgs controlItems
'@
                }
            )
        }
        @{
            Name = 'decon-target-call-reruns-source'
            Group = 'extension'
            Rule = 'Q-38: an explicit call `a()` of a deconstruction target freshly invokes its projection wrapper, which reads the separately cached shared right-hand side; it never requests a fresh evaluation of that right-hand side.'
            Change = 'Only when an unpacking projection is explicitly called, its one hoisted-source argument becomes a fresh zero-supply call. Other bindings and established entries retain ordinary cache semantics.'
            Expect = 'Survives'
            Witnesses = @('decon_target_call_twice', 'decon_target_call_after_read')
            Gap = 'docs/design/lean-model-mutation-campaign-2026-11.md, gap G2'
            Edits = @(
                @{
                    Find = @'
    | .invoke calleeName =>
        match resolvedAlgorithm with
        | .conditional _ _ _ _ =>
'@
                    Replace = @'
    | .invoke calleeName =>
        match resolvedAlgorithm with
        | .mk parent [] [] [] [.call (.algorithmExpr helper@(.mk _ [.unpacking _] _ _ _ _)) [.resolve source]] id =>
            let argument := if source.startsWith "$deconstruct$" then Expr.call (.resolve source) [] else .resolve source
            let wrapper := Algorithm.mk parent [] [] [] [.call (.algorithmExpr helper) [argument]] id
            EvalBody.evalNeedUserSupplyOutput rec wrapper [] ctx env
        | .conditional _ _ _ _ =>
'@
                }
            )
        }
        @{
            Name = 'cache-key-local-as-exported'
            Group = 'extension'
            Rule = 'The zero-argument cache key of a LOCAL-ONLY binding carries its declaring owner''s retained binding context; only an EXPORTED binding is keyed by the owning invocation alone (`zeroArgPropertyCacheKey`).'
            Change = 'Every binding is keyed as an exported one: a local-only binding loses its binding-context component and its value-environment fallback.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  let bindingContextFree := binding.exposure.isExported
'@
                    Replace = @'
  let bindingContextFree := true
'@
                }
            )
        }
        @{
            Name = 'cache-key-exported-as-local'
            Group = 'extension'
            Rule = 'The zero-argument cache key of an EXPORTED binding carries the owning invocation of its declaring chain and no binding context of the access (`zeroArgPropertyCacheKey`).'
            Change = 'Every binding is keyed as a local-only one: an exported binding is keyed by the binding context (or the value environment) of the access.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  let bindingContextFree := binding.exposure.isExported
'@
                    Replace = @'
  let bindingContextFree := false
'@
                }
            )
        }
        @{
            Name = 'while-left-to-right'
            Group = 'hunt-controls'
            Rule = 'A `while` round discovers its flag row first and forms the earlier rows only when the flag holds (LOOP-CF1, condition-first rounds).'
            Change = 'A round forms every row from left to right and reads the flag last.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  match ← discover form rows.reverse with
  | none => noFlag
  | some (earlier, flagItems) =>
    match flagItems.getLast? with
    | none => noFlag
    | some f =>
      if ← flag f then
        let formed ← OutputRows.formLeftToRight form earlier
        pure (some (nextSlots (formed ++ flagItems)))
      else pure none
'@
                    Replace = @'
  let all ← OutputRows.formLeftToRight form rows
  match all.getLast? with
  | none => noFlag
  | some f =>
      if ← flag f then pure (some (nextSlots all)) else pure none
'@
                }
            )
        }
        @{
            Name = 'compare-short-circuit'
            Group = 'hunt-controls'
            Rule = 'A comparison chain evaluates every operand, also after a link is false (no short circuit).'
            Change = 'The chain stops at the first false link without evaluating the later operands.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
    | link :: rest => do
        let next <- rec.eval link.operand ctx env
        let linkHolds <- applyComparison
'@
                    Replace = @'
    | link :: rest => if !holds then pure (Result.bool false, 1) else do
        let next <- rec.eval link.operand ctx env
        let linkHolds <- applyComparison
'@
                }
            )
        }
        @{
            Name = 'repeat-count-first'
            Group = 'hunt-controls'
            Rule = '`repeat` prepares its supply before it demands its count.'
            Change = '`repeat` demands its count before it prepares the supply.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  let captured ← setup
  let n ← count
  pure (captured, n)
'@
                    Replace = @'
  let n ← count
  let captured ← setup
  pure (captured, n)
'@
                }
            )
        }
        @{
            Name = 'cache-pub-1-off'
            Group = 'hunt-controls'
            Rule = 'CACHE-PUB-1: a qualifying explicit zero-supply invocation that finds its key empty and inactive owns the entry and publishes its result.'
            Change = 'An explicit invocation never establishes an entry.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
          else
            let active := state.activeZeroArgProperties
            set { state with activeZeroArgProperties := key :: active }
'@
                    Replace = @'
          else if (match request with | .invoke _ => true | _ => false) then
            EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env
          else
            let active := state.activeZeroArgProperties
            set { state with activeZeroArgProperties := key :: active }
'@
                }
            )
        }
        @{
            Name = 'view-count-demands'
            Group = 'hunt-controls'
            Rule = '`count` over an argument view or a retained collector is the number of cells and demands none of them.'
            Change = '`count` demands every cell before it answers.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
  | .countBuiltin => pure (Result.atom (Int.ofNat cells.length), 1)
  | .firstBuiltin =>
      match cells.head? with
'@
                    Replace = @'
  | .countBuiltin => do
      let _ ← cells.mapM (fun (cell, _) => demandCell cell)
      pure (Result.atom (Int.ofNat cells.length), 1)
  | .firstBuiltin =>
      match cells.head? with
'@
                }
            )
        }
        @{
            Name = 'binary-right-first'
            Group = 'hunt-controls'
            Rule = 'A binary operator evaluates its left operand before its right operand.'
            Change = 'The right operand is evaluated first.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
    let lr <- rec.eval a ctx env
    let rr <- rec.eval b ctx env
    match op with
'@
                    Replace = @'
    let rr <- rec.eval b ctx env
    let lr <- rec.eval a ctx env
    match op with
'@
                }
            )
        }
        @{
            Name = 'cache-owner-d1-off'
            Group = 'hunt-controls'
            Rule = 'CACHE-OWNER-D1: an explicit call of a parameterless owner binds a fresh context; only a property-style read inherits the owner''s activation.'
            Change = 'An explicit owner call reuses the read activation.'
            Expect = 'Killed'
            Edits = @(
                @{
                    Find = @'
        | _ => EvalBody.evalNeedUserSupplyOutput rec resolvedAlgorithm [] ctx env
'@
                    Replace = @'
        | _ => EvalBody.evalPropertyDemandCounted rec resolvedAlgorithm ctx env
'@
                }
            )
        }
    )
}
