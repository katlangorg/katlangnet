# Call-spread and written-slot repair (July 2026)

Repairs the confirmed defects of the July 2026 adversarial semantic audit
(findings F01, F02, F03, F05, F09, F10, F20, F22) while preserving the
verified exact-list and collected-list migrations. This note is the
migration record: every behavior change below is intentional, and the
pre-repair behavior was an implementation accident, not a documented rule.

## 1. One call argument pipeline for every callable shape (F03)

**Rule.** Every call assembles its argument supply in one shared stage
(`BuildCallArgumentInputs` in C#, `collectVariadicCallItems` in Lean):
evaluate each written slot, reify every non-spread slot as exactly one
argument value, expand every explicit spread slot by exactly one value
boundary. Arity checking, clause selection, conditional dispatch, and
pattern binding all happen strictly after assembly. The callee's internal
representation (flat, variadic, repeated-name/patterned, clause family)
never changes the meaning of caller-side spread.

**Before/after.** With `F(0, 0) = 100`, `F(x, y) = x + y`, `A = (1, 2)`:

| Program | Before | After |
|---|---|---|
| `F(A...)` | catch-all-style clause could absorb `A` as ONE closed value (or `NoMatchingBranch`) | `3` — spread supplies two slots, the two-binder clause binds |
| `F(A...)` with `A = (0, 0)` | same absorption | `100` — the literal clause wins, proving dispatch happens after expansion |
| `F(x, x) = x` + `F((7, 7)...)` | arity error `expects 2 arguments, called with 1` | `7` |
| `F((x, y), z) = ...` + `F(A..., 9)` | `(1, 2, 9)` — the spread reached the patterned callee as ONE closed value and the pattern opened it | arity error `expects 2 arguments, called with 3` — write `F(A, 9)` for the destructuring reading (success→error migration fact of the uniform rule) |
| dotted `A.F(C...)` on a patterned callee | arity error (spread stayed closed) | expands like every other shape |

Non-spread arguments are unchanged: `F(A)` still supplies one closed value
for every callee shape. Flat and variadic callees already expanded spread and
are unchanged. Also unified: patterned/conditional callees now respect
dot-call receiver boundary preservation, and an unresolvable non-spread
argument without an algorithm meaning fails at assembly (the same early-error
rule the flat and variadic paths always had). Two error-identity corollaries
of the unification: (a) a wrong-arity patterned call whose extra argument
fails evaluation now reports that argument's error instead of the arity
mismatch, and (b) a conditional call defers an algorithm-resolvable
argument's value error like every other shape, so a later argument's hard
failure can surface first (`F(H, 1 / 0)` reports Division by zero, matching
the flat path) — both are the shared pipeline's uniform error rule, not
incidental drift.

## 2. Written-slot reification (F02)

**Rule.** A non-spread expression occupying one written value slot — a
list-literal element or a written sequence-value pattern argument item —
contributes exactly ONE persistent value (the value its counted supply
denotes), even when the expression emitted zero or many items (index
projections, loop results, counted callback parameters). Only explicit `...`
opens a value into the surrounding slots. Owner:
`EvalExplicitSequenceValueExprSlots` / `evalExplicitSequenceValueExprSlots`
(shared by list literals and written pattern arguments).

**Before/after.** With `S = ((1, 2), (3, 4))`:

| Program | Before | After |
|---|---|---|
| `[S:0, 5]` | `[1, 2, 5]` (spliced) | `[(1, 2), 5]` |
| `[S:0..., 5]` | `[1, 2, 5]` | `[1, 2, 5]` (unchanged — the spread contrast) |
| `F((x, y)) = ...` + `F((S:0, 5))` | written group supplied 3 items | supplies 2 items: `x = (1, 2)`, `y = 5` |
| `[repeat({a + 1, b + a}, 3, 0, 0), 9]` | `[3, 3, 9]` | `[(3, 3), 9]` |
| `((1, 2), (3, 4)).map({[x, x]})` | rows spliced per re-emitted count | `[[(1, 2), (1, 2)], [(3, 4), (3, 4)]]` |

This matches what capture (`z = (S:0, 5)`), call arguments (`G(S:0, 5)`),
root rows beside other rows, and deconstruction always did. Root/body output
rows and loop step outputs are NOT written value slots and keep their
multi-item emission semantics (the lone-root projection display rule is
unchanged).

## 3. Reduce initial accumulator is one written slot (F09)

`reduce(collection, reducer, initial)` reifies the initial accumulator result
at the ordinary value boundary (`reCountValueBoundary`) before reduction
begins. Before: `R(x, acc) = acc + x` + `Init = 1, 2` +
`reduce((), R, Init)` leaked the initial expression's emitted count and
printed two root rows. After: one row `(1, 2)` (count 1), exactly like the
non-empty case threads it.

## 4. Loop optimizer equivalence (F01)

The optimized while/repeat frame packs one value per state slot, so it can
only represent step expressions that emit exactly one value. It now finishes
an already-started iteration exactly once, assembles that iteration's output
slots by the generic rules, and hands those slots to the generic evaluator
whenever a state or continuation expression does not emit exactly one value.
Before: `S = (1, 2), (3, 4)` + `repeat({S:0, a + b}, 1, 0, 0)` returned
`((1, 2), 0)` optimized vs `(1, 2, 0)` generic/Lean. After: `(1, 2, 0)` in
both modes, with identical error identity for the failure shapes. The handoff
does not replay property access, random draws, or failures from the completed
iteration. C#-only (Lean models the generic loop; the optimizer is
implementation machinery).

## 5. Uniform empty loop-state segment (F05)

The flat-variadic loop-state minimum is now the FIXED parameter count, the
same rule as every other collecting binding (`bindParameterPatternList`,
deconstruction, calls, callbacks, and the patterned loop path): the variadic parameter may
collect ZERO slots as the exact empty list `[]`. Before:
`Step(acc, ...x) = ...` + `repeat(Step, 3, 10)` failed with
"expects at least 2 state values". After: binds `acc = 10`, `x = []`.
The old loop-only "the variadic parameter collects at least one slot" restriction had no
independent semantic justification and was bypassed by patterned steps.
Pinned by `bindCallableArguments_mixed_fixed_only_empty_segment` /
`bindCallableArguments_mixed_below_fixed_minimum_fails` (KatLangArityLaws)
and twin C#/Lean tests. Deliberate corollary: a SINGLE-VARIADIC step has zero
fixed parameters, so its state vector may now shrink to ZERO slots, and the
loop then returns the visible empty sequence value `()` where the old
minimum errored (`Step(...x) = x.skip(1)...` + `repeat(Step, 3, 7, 8)` is
`()`); pinned by `Eval_SingleVariadicLoopStep_MayShrinkStateToZeroSlots`.

## 6. Culture-invariant canonical display (F10)

`RunResult` display now formats atoms with `CultureInfo.InvariantCulture` on
the default path (the `DisplayDecimals` path, lexer, `.string`, diagnostics,
and the differential harness were already invariant). Under a comma-decimal
culture such as `de-DE`, `(2.5, 3.5)` previously rendered `(2,5, 3,5)` —
colliding with the element separator. Display-only; no Lean impact.

## 7. Diagnostics (F20, F22)

- Assignment-deconstruction BINDING-SHAPE failures are now phrased against
  the written pattern (`Assignment pattern `a, b` expects 2 values from the
  right-hand side, but it supplied 0 values.`) instead of leaking the
  parser-synthesized helper ("Algorithm `(inline library)` expects ...").
  Mechanism: the parser marks the synthesized helper
  (`Algorithm.User.IsAssignmentDeconstructionHelper`), the patterned binder
  wraps arity failures in `DeconstructionBindingContext`, and the formatter
  owns the wording. The wrapper fires ONLY when every argument slot carried a
  value (a genuine shape failure): a right-hand side whose own evaluation
  failed surfaces its error un-reworded (`a, b = sum` keeps sum's arity
  error; `a, b = G(1)` keeps G's error), so unrelated numbers are never
  attributed to the written pattern. Scope: RHS-evaluation failures and
  unresolved-RHS-name (implicit-parameter) diagnostics still show internal
  context names as before — a separate follow-up. The structured inner error
  kind (`ArityMismatch`) is unchanged, so Lean parity is unaffected.
- A FUNCTION-shaped argument (a builtin, a clause family, or a parameterized
  algorithm — `Algorithm.isFunctionShaped` / `IsFunctionShapedAlgorithm`)
  reaching a TOP-LEVEL collecting binding now reports a targeted `TypeMismatch`
  ("Variadic parameter `...fs` collects values, but a supplied argument is a
  function...") in both C# and Lean, instead of the self-contradictory
  "Expected 0 parameters, but was called with 0 arguments" surfaced from
  evaluating the bare function as a value. A zero-parameter VALUE property
  whose body failed is NOT function-shaped: its genuine evaluation error
  surfaces unchanged (`Bad = 1 / 0` + `G(Bad)` still reports Division by
  zero). Function-valued arguments reaching nested sequence-value patterns or
  conditional clause matching keep the raw baseline error — extending the
  targeted diagnostic there is a follow-up.

## Removed

- The dead pre-capture spread pair `EvalAlgorithmOutputSequenceSpreadItems`
  (C#) / `evalAlgorithmOutputSequenceSpreadItems` (Lean) — unreferenced in
  both languages and preserving superseded raw-supply spread semantics.
- The never-passed `minimumItemCount` override of `BindCallableArguments` /
  `bindCallableArguments` (the loop-state minimum is now the uniform fixed
  count, so the override had no caller). The previously public
  `CallableSignature.RequiredNormalParameterCount` remains as an obsolete
  compatibility shim with its original structural-count value; new code uses
  `TopLevelParameterCount` or `ArityFacts.MinTopLevelArgumentCount` according
  to intent.

## Verification

- New tests: `CallArgumentAssemblyTests` (spread × callee-shape matrix),
  `WrittenSlotReificationTests` (list literals, pattern arguments, reduce
  initial), loop-mode parity tests for multi-emitting state/continuation
  expressions, the while-loop collected-kind pin, culture-invariance display
  tests, and exact-message pins for the new diagnostics.
- New canonical LanguageSpec cases (with generated Lean guards):
  `call-spread-into-conditional-clauses`,
  `call-spread-dispatches-before-clause-selection`,
  `call-spread-into-patterned-callee`,
  `list-written-slot-reifies-projection`,
  `reduce-empty-initial-is-one-value`.
- New real-model theorems: `bindCallableArguments_mixed_fixed_only_empty_segment`,
  `bindCallableArguments_mixed_below_fixed_minimum_fails`.
