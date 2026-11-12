import KatLangArityLaws.HeapInsertion

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# The address shift of every evaluator call (ledger E-18, step 1, M2 § 6.2)

The non-observation contract of `PlanAlgorithmBridge.lean` relates the plan-side run of a
computation with its production-side run. For the PER-BODY obligations — every evaluator body
simulates whenever its recursive answer does — the two sides run DIFFERENT calls: the plan side's
arguments are the production side's with every need address shifted past the inserted cells. This
module is that shift, for all 104 operations of the total core:

* the address-bearing auxiliary types of the evaluator — a resolved builtin argument's supplied
  cell (`shiftArgument`), a callee origin (`shiftOrigin`: a written callee's caller context, a
  callee cell), a collection-builtin call item (`shiftItem`: its supplied cell and demanded value),
  a prepared control argument (`shiftSuffix`), bound collection arguments (`shiftBound`), a
  prepared algorithm output (`shiftPrepared`) and a computed spread's supply (`shiftSupply`) —
  the same components `AddressInvariant.CallPre` / `CallPost` bound;
* `shiftCall σ c` — the plan-side call of the production-side call `c`: contexts, value
  environments, values, cell addresses and cell lists shifted; expressions, algorithms, names and
  the one non-address number (`expectPreparedSequenceBuiltinAlgorithmSuffixArg`'s index) kept;
* `shiftRet σ c` — the plan-side result of a production-side result of `c`, at the result type of
  the shifted call (the two result types are the same type, constructor by constructor).

The two tables are generated from the `EvalCall` / `EvalCall.Ret` definitions of `KatLang.lean`
(one arm per constructor, an argument shifted by its TYPE; a `Nat` is an address exactly for the
arguments named `address`, `callee` and `a`) and are kernel-checked here: `shiftRet` typechecks only
because every arm's result type is the shifted call's (`shiftCall_ret`). On the calls the
`.Algorithm` bridge shares between its two sides the shift is the identity up to the receiver
VALUE, because their context and value environment are valid below the insertion
(`PlanAlgorithmBridge.plan_context_unshifted`, `inserted_receiver_read`, `inserted_tail`).

No per-body obligation is discharged here or anywhere in this task: the tables only make the
obligation `PlanAlgorithmBridge.BodyInserted` a concrete statement.
-/

namespace KatLang.HeapInsertion

def shiftArgument (σ : Site) (arg : ResolvedArgumentAlgorithm) : ResolvedArgumentAlgorithm :=
  { arg with need? := arg.need?.map σ.addr }

def shiftOrigin (σ : Site) : CalleeOrigin → CalleeOrigin
  | .written callee caller => .written callee (shiftCtx σ caller)
  | .cell address => .cell (σ.addr address)
  | o => o

def shiftItem (σ : Site) (item : CallableCallItem) : CallableCallItem :=
  { item with need? := item.need?.map σ.addr, value? := item.value?.map (shiftResult σ) }

def shiftSuffix (σ : Site) : PreparedSequenceBuiltinSuffixArg → PreparedSequenceBuiltinSuffixArg
  | .needAlgorithm address => .needAlgorithm (σ.addr address)
  | .value value => .value (shiftResult σ value)
  | arg => arg

def shiftBound (σ : Site) (b : BoundSequenceBuiltinArguments) : BoundSequenceBuiltinArguments :=
  { b with
    preparedInput := { b.preparedInput with items := b.preparedInput.items.map (shiftResult σ) }
    iterationItems := b.iterationItems.map (shiftCounted σ)
    suffixArgs := b.suffixArgs.map (shiftSuffix σ)
    view? := b.view?.map σ.addr
    slice? := b.slice?.map (fun slice => slice.map σ.addr) }

def shiftPrepared (σ : Site) (p : PreparedAlgorithmOutput) : PreparedAlgorithmOutput :=
  { counted := shiftCounted σ p.counted, outputSlots := p.outputSlots.map (shiftResult σ) }

def shiftSupply (σ : Site) : SpreadSupply → SpreadSupply
  | .items values => .items (values.map (shiftResult σ))
  | .cells cells => .cells (shiftSourced σ cells)

/-- The plan-side call of a production-side call: every need address among its arguments shifted. -/
def shiftCall (σ : Site) : EvalCall → EvalCall
  | .whileLoop step ctx env stepName cells => .whileLoop (shiftArgument σ step) (shiftCtx σ ctx) (shiftValEnv σ env) stepName (cells.map σ.addr)
  | .aliasStepIsRuntime step target ctx visited => .aliasStepIsRuntime step target (shiftCtx σ ctx) visited
  | .aliasValue wired ctx env => .aliasValue wired (shiftCtx σ ctx) (shiftValEnv σ env)
  | .resolveAliasChase followCarriers projectRuntime a ctx visited last => .resolveAliasChase followCarriers projectRuntime a (shiftCtx σ ctx) visited last
  | .resolveAliasTarget a ctx => .resolveAliasTarget a (shiftCtx σ ctx)
  | .resolveAliasStructure a ctx => .resolveAliasStructure a (shiftCtx σ ctx)
  | .resolveAliasValueTarget a ctx => .resolveAliasValueTarget a (shiftCtx σ ctx)
  | .aliasOriginBinding? a ctx => .aliasOriginBinding? a (shiftCtx σ ctx)
  | .lookupLexicalProperty a name ctx => .lookupLexicalProperty a name (shiftCtx σ ctx)
  | .lookupLexicalValueProperty a name ctx => .lookupLexicalValueProperty a name (shiftCtx σ ctx)
  | .lookupLexical a name ctx => .lookupLexical a name (shiftCtx σ ctx)
  | .needPlanNormalizeCallee callee ctx => .needPlanNormalizeCallee callee (shiftCtx σ ctx)
  | .resolveAlg e ctx => .resolveAlg e (shiftCtx σ ctx)
  | .projectNeedCallable address => .projectNeedCallable (σ.addr address)
  | .projectNeedWrittenAt address source caller => .projectNeedWrittenAt (σ.addr address) source (shiftCtx σ caller)
  | .linkCallable address => .linkCallable (σ.addr address)
  | .projectParameterCallable x ctx => .projectParameterCallable x (shiftCtx σ ctx)
  | .projectNeedWritten source caller => .projectNeedWritten source (shiftCtx σ caller)
  | .projectNeedStructuralMember source ctx => .projectNeedStructuralMember source (shiftCtx σ ctx)
  | .resolveCalleeAlg f ctx => .resolveCalleeAlg f (shiftCtx σ ctx)
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => .expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors (args.map (shiftSuffix σ)) index
  | .resolveDotReceiver? e ctx => .resolveDotReceiver? e (shiftCtx σ ctx)
  | .resolveDotReceiver e ctx => .resolveDotReceiver e (shiftCtx σ ctx)
  | .algorithmIntrinsicRoute receiver ctx => .algorithmIntrinsicRoute receiver (shiftCtx σ ctx)
  | .demandNeedRecursive address => .demandNeedRecursive (σ.addr address)
  | .evalSuppliedAt address e ctx env => .evalSuppliedAt (σ.addr address) e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .linkValue address => .linkValue (σ.addr address)
  | .algorithmOfValue val argsOpt ctx env => .algorithmOfValue (shiftResult σ val) argsOpt (shiftCtx σ ctx) (shiftValEnv σ env)
  | .capturedCallee callee => .capturedCallee (σ.addr callee)
  | .referenceReceiverValue target targetAlg ctx env => .referenceReceiverValue target targetAlg (shiftCtx σ ctx) (shiftValEnv σ env)
  | .algorithmCalleeOf receiver ctx env => .algorithmCalleeOf receiver (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalSuppliedCallCounted origin callee cells ctx env calleeName => .evalSuppliedCallCounted (shiftOrigin σ origin) callee (shiftSourced σ cells) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalNeedUserSupply callee cells ctx env => .evalNeedUserSupply callee (cells.map σ.addr) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalNeedFamilySupply callee cells ctx env calleeName => .evalNeedFamilySupply callee (cells.map σ.addr) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .invokeNeed arg => .invokeNeed (shiftArgument σ arg)
  | .argumentNeed arg ctx env => .argumentNeed (shiftArgument σ arg) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .runNeedStepSlots step ctx env cells stepName => .runNeedStepSlots step (shiftCtx σ ctx) (shiftValEnv σ env) (cells.map σ.addr) stepName
  | .runNeedWhileRound step ctx env cells stepName => .runNeedWhileRound step (shiftCtx σ ctx) (shiftValEnv σ env) (cells.map σ.addr) stepName
  | .evalAlgOutputCore a ctx env => .evalAlgOutputCore a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalAlgOutput a ctx env => .evalAlgOutput a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalProgramOutput a ctx env => .evalProgramOutput a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalAlgOutputSlots a ctx env => .evalAlgOutputSlots a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .formOutputRow ctx env e => .formOutputRow (shiftCtx σ ctx) (shiftValEnv σ env) e
  | .whileVerdictSlots a ctx env => .whileVerdictSlots a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalSequenceCallbackCall callee item ctx env calleeName => .evalSequenceCallbackCall callee (shiftCounted σ item) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalSequenceCallbackCallCounted callee item ctx env calleeName => .evalSequenceCallbackCallCounted callee (shiftCounted σ item) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalAlgOutputPreparedCore a ctx env => .evalAlgOutputPreparedCore a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalOutputRowsPreparedCore rows rowCtx env => .evalOutputRowsPreparedCore rows (shiftCtx σ rowCtx) (shiftValEnv σ env)
  | .evalCapturePreparedCore rows ctx env => .evalCapturePreparedCore rows (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalCaptureCountedCore rows ctx env => .evalCaptureCountedCore rows (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalCaptureValue rows ctx env => .evalCaptureValue rows (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalAlgOutputCountedCore a ctx env => .evalAlgOutputCountedCore a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalAlgOutputCounted a ctx env => .evalAlgOutputCounted a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalZeroArgumentDemandOutputCounted a ctx env => .evalZeroArgumentDemandOutputCounted a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalZeroArgumentDemandOutput a ctx env => .evalZeroArgumentDemandOutput a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalArgumentValueCounted arg ctx env => .evalArgumentValueCounted (shiftArgument σ arg) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalArgumentValue arg ctx env => .evalArgumentValue (shiftArgument σ arg) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => .evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm (shiftCtx σ ctx) (shiftValEnv σ env) request
  | .evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => .evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalConditionalCallbackCallCounted callee args ctx env calleeName => .evalConditionalCallbackCallCounted callee (args.map (shiftCounted σ)) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalUserCallbackCallCounted callee args ctx env => .evalUserCallbackCallCounted callee (args.map (shiftCounted σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalResolvedCallbackCallCounted callee args ctx env calleeName => .evalResolvedCallbackCallCounted callee (args.map (shiftCounted σ)) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalResolvedCallbackCall callee args ctx env calleeName => .evalResolvedCallbackCall callee (args.map (shiftCounted σ)) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => .evalSequenceReduceStepCounted callee (shiftCounted σ element) (shiftResult σ accumulator) (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .demandSequenceBuiltinCallItemValue item ctx env => .demandSequenceBuiltinCallItemValue (shiftItem σ item) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .bindSequenceBuiltinArguments b metadata args ctx env => .bindSequenceBuiltinArguments b metadata (args.map (shiftArgument σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalReduceCounted collection stepAlg initial ctx env => .evalReduceCounted (collection.map (shiftCounted σ)) stepAlg (shiftResult σ initial) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalFilterCounted items predicateAlg ctx env => .evalFilterCounted (items.map (shiftCounted σ)) predicateAlg (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalMapCounted collection transformAlg ctx env => .evalMapCounted (collection.map (shiftCounted σ)) transformAlg (shiftCtx σ ctx) (shiftValEnv σ env)
  | .applyBuiltinCountedSequence b metadata args ctx env => .applyBuiltinCountedSequence b metadata (args.map (shiftArgument σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .applyBuiltinCounted b args ctx env => .applyBuiltinCounted b (args.map (shiftArgument σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .applyBuiltin b args ctx env => .applyBuiltin b (args.map (shiftArgument σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .applyBuiltinCountedResolved b args ctx env => .applyBuiltinCountedResolved b (args.map (shiftArgument σ)) (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalExplicitSequenceValueItems a ctx env => .evalExplicitSequenceValueItems a (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalExplicitSequenceValueRowSlots rows rowCtx env => .evalExplicitSequenceValueRowSlots rows (shiftCtx σ rowCtx) (shiftValEnv σ env)
  | .evalExplicitSequenceValueExprSlots expr ctx env => .evalExplicitSequenceValueExprSlots expr (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalUserCallCounted callee args ctx env => .evalUserCallCounted callee args (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalConditionalCallCounted callee args ctx env calleeName => .evalConditionalCallCounted callee args (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalResolvedCall callee args ctx env calleeName => .evalResolvedCall callee args (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalResolvedCallCounted callee args ctx env calleeName origin => .evalResolvedCallCounted callee args (shiftCtx σ ctx) (shiftValEnv σ env) calleeName (shiftOrigin σ origin)
  | .evalCallCountedExpr f args ctx env => .evalCallCountedExpr f args (shiftCtx σ ctx) (shiftValEnv σ env)
  | .callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => .callLexicalWithReceiverCounted name receiver fallback extraArgs (shiftCtx σ ctx) (shiftValEnv σ env)
  | .rejectDotStringIntrinsicArguments argsOpt ctx env => .rejectDotStringIntrinsicArguments argsOpt (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalDotStringReceiverValue target targetAlg ctx env => .evalDotStringReceiverValue target targetAlg (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalDotCallCounted target name fallback argsOpt ctx env => .evalDotCallCounted target name fallback argsOpt (shiftCtx σ ctx) (shiftValEnv σ env)
  | .rejectInvokeIntrinsicArguments argsOpt ctx env => .rejectInvokeIntrinsicArguments argsOpt (shiftCtx σ ctx) (shiftValEnv σ env)
  | .invokeCallReferenceValue val => .invokeCallReferenceValue (shiftResult σ val)
  | .argumentViewCells a => .argumentViewCells (σ.addr a)
  | .evalArgumentViewBuiltin b a => .evalArgumentViewBuiltin b (σ.addr a)
  | .evalSequenceSpreadOperandValue e ctx env => .evalSequenceSpreadOperandValue e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalSequenceSpreadCounted e ctx env => .evalSequenceSpreadCounted e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalSupplySpread e ctx env => .evalSupplySpread e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalListLiteralCounted elements ctx env => .evalListLiteralCounted elements (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalSequenceConstructCounted e ctx env => .evalSequenceConstructCounted e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalUnaryCounted op operand ctx env => .evalUnaryCounted op operand (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalBinaryCounted op a b ctx env => .evalBinaryCounted op a b (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalComparisonCounted first links ctx env => .evalComparisonCounted first links (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalComparisonLinksCounted previousExpr previous holds links ctx env => .evalComparisonLinksCounted previousExpr (shiftResult σ previous) holds links (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalCounted e ctx env => .evalCounted e (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalUserCall callee args ctx env => .evalUserCall callee args (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalConditionalCall callee args ctx env calleeName => .evalConditionalCall callee args (shiftCtx σ ctx) (shiftValEnv σ env) calleeName
  | .evalCallExpr f args ctx env => .evalCallExpr f args (shiftCtx σ ctx) (shiftValEnv σ env)
  | .evalDotCall target name fallback argsOpt ctx env => .evalDotCall target name fallback argsOpt (shiftCtx σ ctx) (shiftValEnv σ env)
  | .eval e ctx env => .eval e (shiftCtx σ ctx) (shiftValEnv σ env)

/-- The plan-side result of a production-side result of the call `c`. -/
def shiftRet (σ : Site) : (c : EvalCall) → c.Ret → (shiftCall σ c).Ret
  | .whileLoop .., r => r.map σ.addr
  | .aliasStepIsRuntime .., r => r
  | .aliasValue .., r => shiftCounted σ r
  | .resolveAliasChase .., r => r
  | .resolveAliasTarget .., r => r
  | .resolveAliasStructure .., r => r
  | .resolveAliasValueTarget .., r => r
  | .aliasOriginBinding? .., r => r
  | .lookupLexicalProperty .., r => r
  | .lookupLexicalValueProperty .., r => r
  | .lookupLexical .., r => r
  | .needPlanNormalizeCallee .., r => r
  | .resolveAlg .., r => r
  | .projectNeedCallable .., r => r
  | .projectNeedWrittenAt .., r => r
  | .linkCallable .., r => r
  | .projectParameterCallable .., r => r
  | .projectNeedWritten .., r => r
  | .projectNeedStructuralMember .., r => r
  | .resolveCalleeAlg .., r => r
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg .., r => r
  | .resolveDotReceiver? .., r => r
  | .resolveDotReceiver .., r => r
  | .algorithmIntrinsicRoute .., r => r
  | .demandNeedRecursive .., r => shiftCounted σ r
  | .evalSuppliedAt .., r => shiftCounted σ r
  | .linkValue .., r => shiftCounted σ r
  | .algorithmOfValue .., r => shiftCounted σ r
  | .capturedCallee .., r => r
  | .referenceReceiverValue .., r => shiftResult σ r
  | .algorithmCalleeOf .., r => (r.1, r.2.1, σ.addr r.2.2)
  | .evalSuppliedCallCounted .., r => shiftCounted σ r
  | .evalNeedUserSupply .., r => shiftCounted σ r
  | .evalNeedFamilySupply .., r => shiftCounted σ r
  | .invokeNeed .., r => r
  | .argumentNeed .., r => σ.addr r
  | .runNeedStepSlots .., r => r.map (shiftResult σ)
  | .runNeedWhileRound .., r => r.map (fun xs => xs.map (shiftResult σ))
  | .evalAlgOutputCore .., r => shiftResult σ r
  | .evalAlgOutput .., r => shiftResult σ r
  | .evalProgramOutput .., r => shiftResult σ r
  | .evalAlgOutputSlots .., r => r.map (shiftResult σ)
  | .formOutputRow .., r => r.map (shiftResult σ)
  | .whileVerdictSlots .., r => r.map (fun xs => xs.map (shiftResult σ))
  | .evalSequenceCallbackCall .., r => shiftResult σ r
  | .evalSequenceCallbackCallCounted .., r => shiftCounted σ r
  | .evalAlgOutputPreparedCore .., r => shiftPrepared σ r
  | .evalOutputRowsPreparedCore .., r => shiftPrepared σ r
  | .evalCapturePreparedCore .., r => shiftPrepared σ r
  | .evalCaptureCountedCore .., r => shiftCounted σ r
  | .evalCaptureValue .., r => shiftResult σ r
  | .evalAlgOutputCountedCore .., r => shiftCounted σ r
  | .evalAlgOutputCounted .., r => shiftCounted σ r
  | .evalZeroArgumentDemandOutputCounted .., r => shiftCounted σ r
  | .evalZeroArgumentDemandOutput .., r => shiftResult σ r
  | .evalArgumentValueCounted .., r => shiftCounted σ r
  | .evalArgumentValue .., r => shiftResult σ r
  | .evalZeroArgPropertyAccessCounted .., r => shiftCounted σ r
  | .evalZeroArgPropertyAccess .., r => shiftResult σ r
  | .evalConditionalCallbackCallCounted .., r => shiftCounted σ r
  | .evalUserCallbackCallCounted .., r => shiftCounted σ r
  | .evalResolvedCallbackCallCounted .., r => shiftCounted σ r
  | .evalResolvedCallbackCall .., r => shiftResult σ r
  | .evalSequenceReduceStepCounted .., r => shiftCounted σ r
  | .demandSequenceBuiltinCallItemValue .., r => shiftItem σ r
  | .bindSequenceBuiltinArguments .., r => shiftBound σ r
  | .evalReduceCounted .., r => shiftCounted σ r
  | .evalFilterCounted .., r => shiftCounted σ r
  | .evalMapCounted .., r => shiftCounted σ r
  | .applyBuiltinCountedSequence .., r => shiftCounted σ r
  | .applyBuiltinCounted .., r => shiftCounted σ r
  | .applyBuiltin .., r => shiftResult σ r
  | .applyBuiltinCountedResolved .., r => shiftCounted σ r
  | .evalExplicitSequenceValueItems .., r => r.map (shiftResult σ)
  | .evalExplicitSequenceValueRowSlots .., r => r.map (shiftResult σ)
  | .evalExplicitSequenceValueExprSlots .., r => r.map (shiftResult σ)
  | .evalUserCallCounted .., r => shiftCounted σ r
  | .evalConditionalCallCounted .., r => shiftCounted σ r
  | .evalResolvedCall .., r => shiftResult σ r
  | .evalResolvedCallCounted .., r => shiftCounted σ r
  | .evalCallCountedExpr .., r => shiftCounted σ r
  | .callLexicalWithReceiverCounted .., r => shiftCounted σ r
  | .rejectDotStringIntrinsicArguments .., r => r
  | .evalDotStringReceiverValue .., r => shiftResult σ r
  | .evalDotCallCounted .., r => shiftCounted σ r
  | .rejectInvokeIntrinsicArguments .., r => r
  | .invokeCallReferenceValue .., r => shiftCounted σ r
  | .argumentViewCells .., r => shiftSourced σ r
  | .evalArgumentViewBuiltin .., r => shiftCounted σ r
  | .evalSequenceSpreadOperandValue .., r => shiftResult σ r
  | .evalSequenceSpreadCounted .., r => shiftCounted σ r
  | .evalSupplySpread .., r => shiftSupply σ r
  | .evalListLiteralCounted .., r => shiftCounted σ r
  | .evalSequenceConstructCounted .., r => shiftCounted σ r
  | .evalUnaryCounted .., r => shiftCounted σ r
  | .evalBinaryCounted .., r => shiftCounted σ r
  | .evalComparisonCounted .., r => shiftCounted σ r
  | .evalComparisonLinksCounted .., r => shiftCounted σ r
  | .evalCounted .., r => shiftCounted σ r
  | .evalUserCall .., r => shiftResult σ r
  | .evalConditionalCall .., r => shiftResult σ r
  | .evalCallExpr .., r => shiftResult σ r
  | .evalDotCall .., r => shiftResult σ r
  | .eval .., r => shiftResult σ r

/-- The result type of a shifted call is the call's. -/
theorem shiftCall_ret (σ : Site) (c : EvalCall) : (shiftCall σ c).Ret = c.Ret := by
  cases c <;> rfl

end KatLang.HeapInsertion
