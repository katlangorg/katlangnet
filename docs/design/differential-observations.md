# Differential observations (Q-67)

FORMAL-06 is unchanged: successful observations are `ok raw=... n=...`;
failures are `err CATEGORY`. Raw structure, root emitted count and the
innermost semantic category remain the neutral correspondence contract.
Finite generated corpora are bounded evidence, not an evaluator refinement proof.

## Routes and observations

| Route | Before Q-67 | Supplementary evidence |
| --- | --- | --- |
| C# plain / counted | Success/failure, exact value; failure category | Selected structured fields on every failed observation, including internal ASTs |
| Public sync engine | Value/count/display on direct success; skipped direct failures | Every surface case executes the engine; parse diagnostic codes, dynamic failure phase, category and shared payload; root output absence remains NoProgramOutput |
| Lean plain / counted | Same value, counted root count, category; internally cross-checked | Separate `errorObs` cross-checks supported payloads on both routes |
| Explorer generated expectations | C#-observed neutral expectations | Additional payload guards derived from the same C# observation; ordinary successful cases incur no extra runs |
| Canonical specification | Handwritten value/count/category/display | Ten independently handwritten payload expectations checked by C# and generated Lean guards |
| Generic / optimized / forced async | Corpus value/count/category and accounting equivalence | Existing corpus suites also compare shared payloads, with no extra executions |
| Public async | Existing API and route suites | Canonical payload cases additionally check exact failure phase/category/payload against the direct evaluator |
| Effects | Independent C# exact event logs and Lean heap guards | Missing ordinary-failure root/callback/loop terminality witnesses added on six routes |
| Resources | C# host policy, separate bounded-limit suites | Unchanged; no Lean budget or cross-strategy stack-depth requirement |

`DifferentialErrors` owns the C# category and supplementary field policy.
`LeanObsTemplate` owns both generated artifacts' Lean projections. `obs`
retains its original contract; `errorObs` is separate. Failed supported cases
need two extra Lean runs for the supplementary guard; successful cases do not.
The public engine adds one run only on failures and parse rejections where it
was previously skipped. No production evaluator code or normal-run overhead changes.

## Complete constructor policy

“Partial” means a Lean field or a public C# field (a rendered description or
name) is deliberately excluded, so only the named fields are shared; C#-internal
diagnostic metadata (signatures, provenance, blame flags) has no Lean
counterpart and never makes a policy partial. A constructor tag is also
checked for comparable/partial cases. In particular `badArity`, ordinary
counted arity, branch input arity and branch output arity stay distinct.

| Lean Error | C# EvalError | Neutral category | Policy; shared fields | Excluded fields / reason |
| --- | --- | --- | --- | --- |
| arityMismatch | ArityMismatch | arity | Comparable: expected, actual | Diagnostic signature, accepted-arity facts and implicit provenance |
| arityMismatch | VariadicArityMismatch | arity | Partial: expected minimum, actual | Callee display name; minimum/count normalization is the binder's existing contract |
| badArity | BadArity | arity | Comparable: distinct fieldless tag | No count payload exists |
| branchArityMismatch | BranchArityMismatch | arity | Partial: distinct tag, expected, actual | Rendered algorithm path/name |
| branchOutputArityMismatch | BranchOutputArityMismatch | arity | Partial: distinct tag, expected, actual | Rendered algorithm path/name |
| unknownName | UnknownName | unknownName | Comparable: name | None |
| unknownProperty | UnknownProperty | unknownProperty | Partial: property name | Rendered object description |
| notPublicProperty | NotPublicProperty | notPublicProperty | Partial: property name | Rendered object description |
| localOnlyProperty | LocalOnlyProperty | localOnlyProperty | Partial: property name, exposure kind | Object description; Lean embeds required names in exposure, C# has optional diagnostic RequiredParameters; no new ordering/availability contract imposed |
| ambiguousOpen | AmbiguousOpen | ambiguousOpen | Partial: name | Rendered provider descriptions |
| duplicateProperty | DuplicateProperty | duplicateProperty | Comparable: name | None |
| unresolvedImplicitParams | UnresolvedImplicitParams | unresolvedImplicitParams | Comparable: ordered parameter names | Implicit diagnostic provenance |
| typeMismatch | TypeMismatch | type | Category-only | Human message |
| noMatchingBranch | NoMatchingBranch | branch | Category-only | Rendered/synthesized algorithm name |
| notAnAlgorithm | NotAnAlgorithm | notAnAlgorithm | Category-only | Human description |
| illegalInOpen | IllegalInOpen | illegalInOpen | Category-only | Human reason |
| badOpenForm | BadOpenForm | badOpenForm | Category-only | Human reason |
| illegalInEval | IllegalInEval | illegalInEval | Category-only | Human reason |
| badIndex | BadIndex | index | Comparable: fieldless | Neither model carries the rejected index |
| divByZero | DivByZero | div0 | Comparable: fieldless | None |
| demandCycle | DemandCycle | demandCycle | Comparable: fieldless | No heap address is public semantics |
| duplicateBranchPattern | DuplicateBranchPattern | duplicateBranchPattern | Comparable: fieldless | None |
| explicitParamsRequireOutput | ExplicitParametersRequireOutput | explicitParamsRequireOutput | Comparable: fieldless | None |
| missingOutput | MissingOutput | missingOutput | Comparable: fieldless | C#-internal selected-member blame flag (diagnostic metadata, like ArityMismatch's signature) |
| spreadMissingOutput | SpreadMissingOutput | spreadMissingOutput | Comparable: fieldless | None |
| withContext | WithContext | Inner category | Strip wrapper and classify inner | Diagnostic frames, text, spans |
| None | EvaluationDepthExceeded | evaluationDepthExceeded | Host-only | Limit |
| None | EvaluationStepLimitExceeded | evaluationStepLimitExceeded | Host-only | Limit |
| None | EvaluationStackExhausted | evaluationStackExhausted | Host-only | Host stack policy |
| None | CollectionSizeLimitExceeded | collectionSizeLimitExceeded | Host-only | Limit, requested size |
| None | MaterializationLimitExceeded | materializationLimitExceeded | Host-only | Limit |
| None | StringSizeLimitExceeded | stringSizeLimitExceeded | Host-only | Limit, requested size |
| None | StringMaterializationLimitExceeded | stringMaterializationLimitExceeded | Host-only | Limit |
| None | DisplayLengthLimitExceeded | displayLengthLimitExceeded | Host-only | Limit |
| None | AstDepthLimitExceeded | astDepthLimitExceeded | Host-only | Limit |
| None | AstCycleDetected | astCycleDetected | Host-only | Malformed host graph |
| None | ModuleRegionMaterializationFailed | moduleRegionMaterializationFailed | Host-only | Source diagnostics/import provenance |

The fixed/variadic correspondence follows `Evaluator.NeedCallArityError` and
Lean `needCardinalityGate`: both count mandatory top-level supplied slots,
not flattened captures. Branch counts follow the two validation gates.
Ordered names follow `Algorithm.params`; exposure kinds follow the existing
`LeanAstEncoder.EncodeExposure` mapping. Messages and paths have deliberately
different representations and are not normalized into invented semantic fields.
Twenty-eight independent constructor-projection goldens check every shared field and all category-only decisions in both languages, including constructors absent from validated-source executions. These are projections of error values, not evaluator runs or handwritten source translations. All 37 C# variants have a reviewed policy pin; `DifferentialErrors.Observe`
names every variant with no catch-all arm, so a new C# variant fails the test
build (`CS8509`) until it is classified. Lean's projection has no wildcard, so
new constructors require a deliberate decision. Independent policy tests reject
payload downgrades.

## Demand, effects and model boundaries

ModelCProductionTests, ArgumentDemandOrderTests, ModelCPropagationTests and
NeedCellTests already independently assert unused/required computations,
spread formation, cardinality precedence, first demand order, single flight,
sticky failures, projections and cache separation. FailureTerminalityWitnessTests
adds exact six-route logs for root rows, map/filter/reduce and repeat/while,
no partial successful value, and two independently failing demanded cells.

Lean CoreTests/ModelC already observes suspended/completed cells, unchanged
work on repeated successful/failed demands, shared clause attempts, slice
transport, callable projection and the separate property cache. These are
bounded one-sided heap witnesses, not shared universal operational traces.
Host operations remain C#-only. R3 (October 2026) adds kernel theorems for the
Lean BINDER's boundary event schedule (`KatLangArityLaws/BinderTrace.lean`,
`FamilyDispatch.lean`, `BinderCorrespondence.lean`): they are binder-level laws over the Lean model, not a
shared universal operational trace of the evaluator, and say nothing about C#.

The explorer's eleven exclusions remain exactly the existing parse/front-end
cases; its nineteen internal-node cases stay same-AST comparable. Its
collection invariants already use independent structural expectations. The
canonical specification's twenty-two numeric/native exclusions already have
handwritten intent expectations and exact-ID ratchets. No case is newly excluded.

Both generator prompts retain their generated canonical-example block (161
examples of the then 448-case specification when Q-67 landed in `091ddca4`,
2026-10-15; the block header records the current count and is verified by
`LanguageSpecArtifactsGeneratorPromptTests`). Twenty
selected handwritten result claims (ten per prompt) now use the existing TutorialCorpus grammar
and TutorialResultSweepTests assertion, with exact first-row inventories.
This includes the corrected `Many` counts and the decimal Order claim.

The prompts' other examples are indented rows annotated with `# result`
comments, a convention the tutorial grammar does not read (independent review,
2026-10-15: before it, the text prompt's dozens of concrete annotated rows, such
as `Values[1]  # 20`, could be edited with no test failing). Every such row
outside a fence is now classified by its verbatim text in
`PromptFile_AnnotatedExampleRowsExecuteOrAreExempt`: 86 of the 104 distinct
rows execute in their example's context with the annotated display, evaluation
error or front-end rejection, and 18 carry an explicit exemption (network module
loads and rejected load forms, metavariable illustrations, definition
annotations whose claims follow in prose). An unclassified or stale row fails
the census. Claims written inside prose sentences remain outside mechanical
verification, as in the tutorial. The untracked LLM generator harness is an
experimental generation/validity tool, not a result oracle.

Final execution counts, runtime measurements, mutations and Constitution
preservation are recorded in `artifacts/validation/q67-differential-observations/`.
