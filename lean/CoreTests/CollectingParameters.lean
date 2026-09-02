import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- collecting user-parameter tests
--------------------------------------------------------------------------------

def variadicCollectAlg : Algorithm :=
  algWithParameters [{ name := "list", kind := .collecting }] [] [] [.param "list"]

def normalCollectAlg : Algorithm :=
  alg ["list"] [] [] [.param "list"]

-- Internal sequence `(10, 20, 30)*`: spread over the constructed sequence value.
def sequenceSpread1230 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 10) (.num 20)) (.num 30))

def variadicSimpleRoot : Algorithm :=
  algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none
  ]

-- `Arg.Collect` is `Collect(Arg)`: the receiver is ONE captured argument
-- slot, so the collecting parameter collects `list = [(1, 2, 3)]` and its count is 1.
def variadicDotCallReceiverIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr variadicSimpleRoot) with
  | Except.ok [1] => true
  | _ => false

#guard variadicDotCallReceiverIsOneCapturedSlot

def normalParameterStillPreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Collect", normalCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard normalParameterStillPreservesBoundary

def variadicNestedSequenceValuesRoot : Algorithm :=
  algPrivate [] [] [
    ("Arg", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none,
    .dotCall (.call (resolve "atoms") [.dotCall (resolve "Arg") "Collect" none]) "count" none
  ]

-- The one captured receiver slot keeps its nested structure intact: `atoms`
-- still reaches all four numeric leaves through the collected list.
def variadicPreservesNestedSequenceValues : Bool :=
  match runFlat (.algorithmExpr variadicNestedSequenceValuesRoot) with
  | Except.ok [1, 4] => true
  | _ => false

#guard variadicPreservesNestedSequenceValues

def variadicScaleAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "factor" }] [] [] [
    .dotCall (.param "values") "map" (some [
      .algorithmExpr (alg ["n"] [] [] [.binary .mul (.param "n") (.param "factor")])
    ])
  ]

def variadicTotalWithFeeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "fee" }] [] [] [
    .binary .add
      (.dotCall (.param "values") "sum" none)
      (.param "fee")
  ]

def variadicMeanAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "values") "sum" none)
      (.dotCall (.param "values") "count" none)
  ]

def variadicCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "count" none
  ]

def variadicAtomsCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.call (resolve "atoms") [.param "values"]) "count" none
  ]

def ordinaryCountAlg : Algorithm :=
  alg ["list"] [] [] [
    .dotCall (.param "list") "count" none
  ]

-- Supplying a NAMED property's items to the variadic mean uses the explicit
-- spread call `Mean(Arg*)` or the grouped-spread receiver `(Arg*).Mean` (whose
-- segment supply is the spread items); both agree with the builtin sum/count
-- pipeline. (A stored receiver `Arg.Mean` supplies one item — see below.)
def variadicMeanMatchesBuiltinSumCount : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Mean", variadicMeanAlg),
    ("Direct", alg [] [] [] [
      .binary .div
        (.dotCall (resolve "Arg") "sum" none)
        (.dotCall (resolve "Arg") "count" none)
    ])
  ] [
    .call (resolve "Mean") [sequenceSpread (resolve "Arg")],
    .dotCall (.capture [sequenceSpread (resolve "Arg")]) "Mean" none,
    resolve "Direct"
  ])) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard variadicMeanMatchesBuiltinSumCount

-- `CountViaVariadic(Arg)` and `Arg.CountViaVariadic` supply ONE argument, so
-- the collecting parameter collects `values = [Arg]` (count 1); the fixed-collection builtin
-- `Arg.count` opens the bound value (count 2); `atoms` recursively reaches
-- all four numeric leaves through the collected list.
def variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("CountViaVariadic", variadicCountAlg),
    ("CountAtoms", variadicAtomsCountAlg)
  ] [
    .call (resolve "CountViaVariadic") [resolve "Arg"],
    .dotCall (resolve "Arg") "CountViaVariadic" none,
    .dotCall (resolve "Arg") "count" none,
    .call (resolve "CountAtoms") [resolve "Arg"]
  ])) with
  | Except.ok [1, 1, 2, 4] => true
  | _ => false

#guard variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms

-- A fixed parameter binds the receiver value itself, so the collection
-- builtin opens it (count 3); a collecting parameter collects the receiver as one
-- list element (count 1). The two shapes are observably different.
def ordinaryAndVariadicCountStayStructurallyDifferent : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Ordinary", ordinaryCountAlg),
    ("Variadic", variadicCountAlg)
  ] [
    .dotCall (resolve "Arg") "Ordinary" none,
    .dotCall (resolve "Arg") "Variadic" none
  ])) with
  | Except.ok [3, 1] => true
  | _ => false

#guard ordinaryAndVariadicCountStayStructurallyDifferent

-- Scaling a named property's ITEMS uses the grouped-spread receiver
-- `(Arg*).Scale(10)`: the suffix takes the factor, and the collector consumes
-- the receiver segment's supply (Arg's three spread items).
def variadicBeforeSuffixSupportsDotCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    .dotCall (.capture [sequenceSpread (resolve "Arg")])
      "Scale" (some [.num 10])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard variadicBeforeSuffixSupportsDotCall

-- TotalWithFee(*values, fee) is a deconstruction parameter list. The inline
-- block receiver exposes its three top-level items (10, 20, 30), so with the
-- suffix the call supplies four items; the variadic captures [10, 20, 30] and
-- `fee` binds 5, giving sum 60 + 5 = 65.
def variadicInlineTupleDotCallWithSuffixCapturesReceiverItems : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [sequenceSpread1230])
      "TotalWithFee" (some [.num 5])
  ])) with
  | Except.ok (.atom 65) => true
  | _ => false

#guard variadicInlineTupleDotCallWithSuffixCapturesReceiverItems

-- `Data.TotalWithFee(5)` supplies the named receiver's value-boundary segment
-- (one item), so the collecting parameter collects `values = [(10, 20, 30)]`
-- and `values.sum` hits the numeric element constraint — unlike the written
-- group receivers above, whose raw row supply feeds the collector.
def collectingNamedMultiOutputDotCallWithSuffixIsGroupedArgument : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (resolve "Data") "TotalWithFee" (some [.num 5])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard collectingNamedMultiOutputDotCallWithSuffixIsGroupedArgument

-- The named receiver's segment supply is one item (numeric-constraint error),
-- while the written grouped-spread receiver `(Data*)` supplies its three raw
-- row items: emission, not spelling, decides what the collector consumes.
def variadicInlineTupleSpreadReceiverDiffersFromNamedReceiver : Bool :=
  let named :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
      ("TotalWithFee", variadicTotalWithFeeAlg)
    ] [
      .dotCall (resolve "Data") "TotalWithFee" (some [.num 5])
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  let spreadReceiver :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
      ("TotalWithFee", variadicTotalWithFeeAlg)
    ] [
      .dotCall (.capture [sequenceSpread1230])
        "TotalWithFee" (some [.num 5])
    ])) with
    | Except.ok [65] => true
    | _ => false
  named && spreadReceiver

#guard variadicInlineTupleSpreadReceiverDiffersFromNamedReceiver

-- A nested inline tuple receiver `((10, 20, 30))` is likewise one grouped
-- argument slot: the collected list holds the sequence value, so `values.sum`
-- hits the numeric element constraint.
def variadicNestedInlineTupleDotCallIsGroupedArgument : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [
      .capture [.num 10, .num 20, .num 30]
    ]) "TotalWithFee" (some [.num 5])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard variadicNestedInlineTupleDotCallIsGroupedArgument

def ordinaryInlineTupleDotCallStillPreservesReceiverBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", ordinaryCountAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20, .num 30]) "Collect" none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard ordinaryInlineTupleDotCallStillPreservesReceiverBoundary

def sequenceBuiltinInlineTupleDotCallBehaviorUnchanged : Bool :=
  let inlineSum :=
    .dotCall (.capture [.num 10, .num 20, .num 30]) "sum" none
  let nestedSum :=
    .dotCall (.capture [
      .capture [.num 10, .num 20, .num 30]
    ]) "sum" none
  let inlineWorks :=
    match runFlat inlineSum with
    | Except.ok [60] => true
    | _ => false
  let nestedFails :=
    match runFlat nestedSum with
    | Except.ok [60] => true
    | _ => false
  inlineWorks && nestedFails

#guard sequenceBuiltinInlineTupleDotCallBehaviorUnchanged

-- `((Arg*).Scale(10), Arg.map{n * 10})*`: a spread over the
-- constructed pair of the spread-receiver variadic scale and the builtin map;
-- both produce the same scaled items.
def variadicScaleMatchesBuiltinMap : Bool :=
  let builtinMap := .dotCall (resolve "Arg") "map" (some [
    .algorithmExpr (alg ["n"] [] [] [.binary .mul (.param "n") (.num 10)])
  ])
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    sequenceSpread
      (.sequenceConstruct
        (.dotCall (.capture [sequenceSpread (resolve "Arg")])
          "Scale" (some [.num 10]))
        builtinMap)
  ])) with
  | Except.ok [10, 20, 30, 10, 20, 30] => true
  | _ => false

#guard variadicScaleMatchesBuiltinMap

def collectingBindingErrorRoot : Algorithm :=
  algPrivate [] [] [
    ("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }, { name := "last" }] [] [] [
      .param "first", .param "rest", .param "last"
    ])
  ] [
    .call (resolve "F") [.num 1]
  ]

def collectingBindingErrorWhenNormalParamsCannotBind : Bool :=
  -- F(first, *rest, last) is a deconstruction parameter list. F(1) supplies one
  -- scalar item, which is not opened (rule 5); the matcher needs at least the two
  -- fixed bindings (first, last), so it reports arityMismatch 2 1.
  match runResult (.algorithmExpr collectingBindingErrorRoot) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard collectingBindingErrorWhenNormalParamsCannotBind

def sequenceValueCollectingCountAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [
    .dotCall (.param "xs") "count" none
  ]

def sequenceValueCollectingFirstAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [
    .index (.param "xs") (.num 0)
  ]

def sequenceValueCollectingMixedAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "xs", kind := .collecting }],
    .capture { name := "a" },
    .capture { name := "b" }
  ] [] [] [
    .dotCall (.param "xs") "count" none,
    .param "a",
    .param "b"
  ]

def sequenceValueCollectingCapturesImmediateSequenceValueItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard sequenceValueCollectingCapturesImmediateSequenceValueItems

def sequenceValueCollectingRemovesOnlyOneSequenceValueBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueCollectingRemovesOnlyOneSequenceValueBoundary

def sequenceValueCollectingPreservesNestedSequenceValueItem : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueCollectingPreservesNestedSequenceValueItem

def sequenceValueCollectingRequiresSequenceValueSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [.num 1, .num 2, .num 3]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | Except.ok _ => false

#guard sequenceValueCollectingRequiresSequenceValueSlot

def sequenceValueCollectingWithMixedTopLevelParameters : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingMixedAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3],
      .num 4,
      .num 5
    ]
  ])) with
  | Except.ok [3, 4, 5] => true
  | _ => false

#guard sequenceValueCollectingWithMixedTopLevelParameters

def sequenceValueSeparateVariadicsDifferentLevelsAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "inner", kind := .collecting }],
    .capture { name := "outer", kind := .collecting }
  ] [] [] [
    .dotCall (.param "inner") "count" none,
    .dotCall (.param "outer") "count" none
  ]

def sequenceValueSeparateVariadicsDifferentLevelsBindIndependently : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSeparateVariadicsDifferentLevelsAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2],
      .num 3,
      .num 4
    ]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard sequenceValueSeparateVariadicsDifferentLevelsBindIndependently

def sequenceValueHeadTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "head" },
      .capture { name := "tail", kind := .collecting }
    ]
  ] [] [] [
    .param "head",
    .dotCall (.param "tail") "count" none
  ]

def sequenceValueHeadTailPatternBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueHeadTailAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3, .num 4]
    ]
  ])) with
  | Except.ok [1, 3] => true
  | _ => false

#guard sequenceValueHeadTailPatternBindsWithinOneSlot

def sequenceValueFirstMiddleLastAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "first" },
      .capture { name := "middle", kind := .collecting },
      .capture { name := "last" }
    ]
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def sequenceValueFirstMiddleLastPatternBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueFirstMiddleLastAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ]
  ])) with
  | Except.ok [1, 3, 5] => true
  | _ => false

#guard sequenceValueFirstMiddleLastPatternBindsWithinOneSlot

def sequenceValueCollectingWithSuffixInsideSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .collecting },
      .capture { name := "pre2" }
    ],
    .capture { name := "pre1" }
  ] [] [] [
    .dotCall (.param "history") "count" none,
    .param "pre2",
    .param "pre1"
  ]

def sequenceValueCollectingWithSuffixInsideSequenceValueBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3],
      .num 4
    ]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard sequenceValueCollectingWithSuffixInsideSequenceValueBindsWithinOneSlot

def sequenceValueCollectingWithSuffixInsideSequenceValueRequiresSuffixValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") [
      .emptySequence 0,
      .num 4
    ]
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard sequenceValueCollectingWithSuffixInsideSequenceValueRequiresSuffixValue

def sequenceValuePairFirstAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y" }]
  ] [] [] [.param "x"]

/-- Regression: `F(((A), 6))` with `A = 5`. The written grouping `(A)` is one
    grouping level around a single already-evaluated item, so pattern binding
    receives the scalar `5` itself -- never a literal-unwritable orphan
    sequence value `(5)` that would compare unequal to `5`. Mirrors assignment
    deconstruction of the same right-hand side. -/
def sequenceValuePatternParenScalarPropertyItemIsNotOrphan : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 5]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .capture [.resolve "A"],
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.atom 5) => true
  | _ => false

#guard sequenceValuePatternParenScalarPropertyItemIsNotOrphan

/-- Regression: `F(((A), 6))` with `A = (1, 2)`. The grouped property reference
    supplies the canonical `(1, 2)` as one item -- not an orphan `((1, 2))`. -/
def sequenceValuePatternParenSequencePropertyItemStaysCanonical : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .capture [.resolve "A"],
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternParenSequencePropertyItemStaysCanonical

/-- Regression: `F(((), 6))`. A non-spread `()` item is one visible item,
    exactly as in ordinary sequence-value construction, so the pattern sees
    `((), 6)` and binds `x` to the empty sequence value. -/
def sequenceValuePatternEmptySequenceSiblingItemIsPreserved : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .emptySequence 0,
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternEmptySequenceSiblingItemIsPreserved

/-- Regression: only an explicit spread contributes zero items. `F((E*, 6))`
    with `E = ()` spreads away the empty value, so the pattern sees the single
    item `6`. -/
def sequenceValuePatternSpreadOfEmptyStillContributesNoItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("E", alg [] [] [] [.emptySequence 0]),
    ("F", sequenceValueCollectingCountAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .sequenceSpread (.resolve "E"),
        .num 6
      ]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceValuePatternSpreadOfEmptyStillContributesNoItems

/-- The shared prepared output pass retains the exact written-slot view while constructing
    the combined counted value: a nested written group stays one grouped item, a list
    stays opaque, and only the explicit spread contributes its immediate items. Patterned call
    assembly consumes this pair directly instead of evaluating the group a second time. -/
def preparedAlgorithmOutputRetainsWrittenSlots : Bool :=
  let nested := KatLang.Expr.capture [.num 1, .num 2]
  let spreadPair := KatLang.Expr.sequenceSpread
    (KatLang.Expr.capture [.num 5, .num 6])
  let output := alg [] [] [] [nested, .listLiteral [.num 3, .num 4], spreadPair]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [
        .sequenceValue [.atom 1, .atom 2],
        .listValue [.atom 3, .atom 4],
        .atom 5,
        .atom 6], 4),
      outputSlots := [
        .sequenceValue [.atom 1, .atom 2],
        .listValue [.atom 3, .atom 4],
        .atom 5,
        .atom 6]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputRetainsWrittenSlots

/-- Discriminator: a multi-emitting single output row stays ONE written slot in the
    prepared view. `((1, 2), (3, 4)):0` re-emits the selected pair with count 2, so
    recovering the slot view by decomposing the combined counted value would present
    `[1, 2]`; the retained accumulator keeps the one written slot `[(1, 2)]`. -/
def preparedAlgorithmOutputKeepsMultiEmittingSlotWhole : Bool :=
  let pairOfPairs := KatLang.Expr.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let output := alg [] [] [] [.index pairOfPairs (.num 0)]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [.atom 1, .atom 2], 2),
      outputSlots := [.sequenceValue [.atom 1, .atom 2]]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputKeepsMultiEmittingSlotWhole

def sequenceValueSingletonFirstAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- End-to-end: the patterned call consumes the retained written slot — the singleton
    pattern binds the whole selected pair even though the projection re-emits count 2
    inside the written group. (The C# surface parser folds redundant parentheses
    around a lone postfix expression, so this written group is exercised on the AST
    channel, mirroring `PatternedCallSingleEvaluationTests`.) -/
def sequenceValueSingletonPatternKeepsMultiEmittingWrittenSlotWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("S", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("F", sequenceValueSingletonFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [.index (resolve "S") (.num 0)]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueSingletonPatternKeepsMultiEmittingWrittenSlotWhole

/-- Regression: `F(((1, 2)))` with `F((x, y)) = x`. The inline-written argument
    `((1, 2))` is one written grouping level around the canonical item
    `(1, 2)`, so the pattern receives exactly ONE written slot and reports
    `arityMismatch 2 1`. Written slots stay authoritative for inline-written
    pattern arguments: binding neither mints an orphan `((1, 2))` nor silently
    opens the single written item. -/
def sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity

/-- Regression: redundant grouping depth canonicalizes away shallowly at each
    level, so `F((((1, 2))))` still writes exactly one slot -- the canonical
    `(1, 2)` -- and reports the same `arityMismatch 2 1`. -/
def sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [
          .capture [.num 1, .num 2]
        ]
      ]
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity

/-- Regression: `A = ((1, 2))` canonicalizes at property construction to
    `(1, 2)`; `F(A)` then opens the stored canonical sequence value for the
    pattern, so `F((x, y)) = x` binds `x = 1`. No hidden orphan `((1, 2))`
    distinguishes the stored value from the writable literal `(1, 2)`. -/
def sequenceValuePatternPropertyStoredWrappedPairOpensCanonically : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.capture [.num 1, .num 2]]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [.resolve "A"]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard sequenceValuePatternPropertyStoredWrappedPairOpensCanonically

def sequenceValuePairFirstWithFixedSuffixAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y" }],
    .capture { name := "z" }
  ] [] [] [.param "x"]

/-- Regression: `KeepFirst(((1, 2)), 3)` with `KeepFirst((x, y), z) = x`. The
    trailing fixed argument binds normally; the sequence-value pattern still
    receives one written slot for `((1, 2))` and reports `arityMismatch 2 1`. -/
def sequenceValuePatternWrappedPairWithFixedSuffixReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstWithFixedSuffixAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ],
      .num 3
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternWrappedPairWithFixedSuffixReportsWrittenSlotArity

def sequenceValueSingleCaptureAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- Regression: `IdSeq(((1, 2)))` with `IdSeq((x)) = x`. The one-capture
    sequence pattern consumes the single written slot, and that slot is the
    CANONICAL item `(1, 2)`: the shallow singleton-erasing combiner never
    materializes a literal-unwritable orphan `((1, 2))` around it. The
    structural match pins the exact shape. -/
def sequenceValuePatternSingleCaptureBindsWrappedPairAsCanonicalItem : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternSingleCaptureBindsWrappedPairAsCanonicalItem

def sequenceValueSingleCaptureCountAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.dotCall (.param "x") "count" none]

/-- Regression: the canonically bound item observes consistently -- `x.count`
    for the `IdSeq(((1, 2)))` binding is 2, matching the structural shape
    `(1, 2)` (an orphan `((1, 2))` would count 1). -/
def sequenceValuePatternSingleCaptureWrappedPairCountsItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureCountAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValuePatternSingleCaptureWrappedPairCountsItems

/-- Guard: the shallow combiner never drops empty-sequence siblings.
    `F(((), ()))` writes two items, so the pair pattern binds both empties
    positionally and `x` is the real empty sequence value. -/
def sequenceValuePatternTwoEmptySiblingItemsBindPositionally : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [.emptySequence 0, .emptySequence 0]
    ]
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternTwoEmptySiblingItemsBindPositionally

def sequenceValueCollectingIsNotTopLevelVariadic : Bool :=
  let sequenceValueCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .collecting }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]))
  let flatCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .collecting }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") [.num 1, .num 2, .num 3]
    ]))
  match sequenceValueCall, flatCall with
  | Except.ok [2, 3], Except.error err => innermostIsArityMismatch 2 3 err
  | _, _ => false

#guard sequenceValueCollectingIsNotTopLevelVariadic

-- Source `Step((*history), previous) = (history*, previous + 1), previous + 1`,
-- matching the C# regression `Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat`.
-- The first output slot is the written sequence value `(history*, previous + 1)`:
-- a written group whose comma rows are `history*` (an explicit spread opening the
-- captured history one level) and `previous + 1`. The written spread splices its
-- items before the sibling slot — the same `(A*, 99)` = `(1, 2, 99)` rule as
-- every written sequence value — so the history slot GROWS FLAT by one item per
-- step. Starting from `(1, 2)` and stepping twice, `:0` selects the flat
-- `(1, 2, 3, 4)`. To deepen instead of flattening, write the history as a
-- non-spread item: `(history, previous + 1)`.
-- (Before the July 2026 alignment fix, `evalAlgOutputCore` kept a non-empty
-- spread output slot grouped as one un-expanded slot, so this program nested to
-- `(((1, 2), 3), 4)` — diverging from `evalAlgOutputCountedCore`, from the C#
-- evaluator, and from written-sequence spread semantics. This guard pins the
-- aligned flat behavior at the exact structural level.)
def sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "previous" }
  ] [] [] [
    .capture [sequenceSpread (.param "history"), .binary .add (.param "previous") (.num 1)],
    .binary .add (.param "previous") (.num 1)
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some [
        .num 2,
        .capture [.num 1, .num 2],
        .num 2
      ]))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat

-- Source `Step((*history, previous), current) = (history*, current), current`.
-- Same shape as `sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat`: the first output
-- slot is the sequence-value pair `(history*, current)` — a written group whose comma rows are
-- `history*` (sequence-spread) and `current` — so it is one next-state slot.
-- (Contrast a spread over `sequenceConstruct history current`, which is a different shape.)
def sequenceValueCollectingLoopStepWithSuffixInsideSequenceValuePreservesStateShape : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .collecting },
      .capture { name := "previous" }
    ],
    .capture { name := "current" }
  ] [] [] [
    .capture [sequenceSpread (.param "history"), .param "current"],
    .param "current"
  ]
  -- Exact structural check. Here the sequence-value pattern `(*history, previous)`
  -- DESTRUCTURES the slot `(1, 2)` into atoms — history captures the leading atom
  -- `1` and `previous` the trailing `2` — so `history*` spreads a bare atom, not
  -- a nested sequence value. The next slot is therefore the FLAT pair `(1, 3)`, and it stays
  -- flat across iterations (dropping the previous `previous`, unlike the
  -- variadic-only `(*history)` capture in
  -- `sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat`, which accumulates).
  -- Asserting the exact `Result` pins this flat shape.
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some [
        .num 2,
        .capture [.num 1, .num 2],
        .num 3
      ]))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 3]) => true
  | _ => false

#guard sequenceValueCollectingLoopStepWithSuffixInsideSequenceValuePreservesStateShape

def loopVariadicHistoryLastExpr : KatLang.Expr :=
  .dotCall (.call (resolve "atoms") [.param "history"]) "last" none

def loopVariadicNextExpr : KatLang.Expr :=
  .binary .add loopVariadicHistoryLastExpr (.num 1)

def loopVariadicAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .collecting }] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopVariadicContinueFlagExpr : KatLang.Expr :=
  .call (resolve "if") [
    .binary .lt loopVariadicNextExpr (.num 6),
    .num 1,
    .num 0
  ]

def loopVariadicWhileAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .collecting }] [] [] [
    .sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr)
      loopVariadicContinueFlagExpr
  ]

def loopVariadicInitialState : Algorithm :=
  alg [] [] [] [.num 1, .num 2, .num 4]

def variadicLoopStepRepeatOneIterationCapturesStateItems : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5]) => true
  | _ => false

#guard variadicLoopStepRepeatOneIterationCapturesStateItems

def variadicLoopStepRepeatTwoIterationsKeepsExpandedState : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 2,
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard variadicLoopStepRepeatTwoIterationsKeepsExpandedState

def variadicLoopStepWhileUsesExpandedState : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicWhileAppendNextAlg)] [
    .dotCall (resolve "Step") "while" (some [
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard variadicLoopStepWhileUsesExpandedState

def sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 3,
        sequenceItems [.num 1, .num 2, .num 4]
      ]))
      "take"
      (some [.num 5])
  ])) with
  | Except.ok [1, 2, 4, 5, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots

-- Aspect 2 loop-state variadic binding (mirrors C# EvaluatorTests.Eval_VariadicLoopStep_*).
-- A top-level variadic loop interface binds state as an item supply: the fixed prefix
-- and suffix bind from the ends, and the collecting parameter collects the matched middle state slots
-- as one exact immutable list. The minimum is the FIXED (non-variadic) parameter count —
-- the collecting parameter may collect ZERO slots (empty collected list = `[]`), the same rule as every other collecting-binding
-- receiver — and the max is unbounded (extra middle slots are accepted).
def loopVariadicPrefixMiddleSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .collecting },
    { name := "last" }
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def loopVariadicPrefixMiddleSuffixIncrementAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .collecting },
    { name := "last" }
  ] [] [] [
    .binary .add (.param "first") (.num 1),
    sequenceSpread (.param "middle"),
    .binary .add (.param "last") (.num 1)
  ]

-- Extra middle: 4 state slots bind first=10/last=40 from the ends, middle = [20, 30]
-- (count 2). Mirrors C# Eval_VariadicLoopStep_WithPrefixMiddleSuffix_PreservesDeclarationOrderBindings.
def variadicLoopStepCapturesExtraMiddleStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20, .num 30, .num 40])
  ])) with
  | Except.ok [10, 2, 40] => true
  | _ => false

#guard variadicLoopStepCapturesExtraMiddleStateSlots

-- Exact structural count: 3 state slots bind first=10/last=30 and middle = [20] (count 1).
def variadicLoopStepExactStructuralCountBinds : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20, .num 30])
  ])) with
  | Except.ok [10, 1, 30] => true
  | _ => false

#guard variadicLoopStepExactStructuralCountBinds

-- Empty collected segment: 2 state slots bind first=10/last=20 from the ends and the collecting parameter
-- collects ZERO middle slots (middle = [], count 0) — the same empty-segment rule
-- as every other collecting binding.
def variadicLoopStepEmptyMiddleBindsEmptyList : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20])
  ])) with
  | Except.ok [10, 0, 20] => true
  | _ => false

#guard variadicLoopStepEmptyMiddleBindsEmptyList

-- Fixed-minimum failure: only 1 state slot cannot satisfy the two FIXED
-- parameters first + last, so this is arityMismatch 2 1.
def variadicLoopStepBelowFixedMinimumFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false

#guard variadicLoopStepBelowFixedMinimumFails

-- The exact reviewed case: Step(first, *middle, last) = first + 1, middle*, last + 1
-- with Step.repeat(2, 0, 5, 5, 10) binds first=0, middle=[5, 5] (the collected exact
-- list), last=10 and, after two iterations (the body re-spreads middle with
-- `.sequenceSpread (.param "middle")`),
-- yields 2, 5, 5, 12 (previously rejected by Lean as arityMismatch 3 4).
def variadicLoopStepExtraMiddleRepeatsTwice : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixIncrementAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, .num 0, .num 5, .num 5, .num 10])
  ])) with
  | Except.ok [2, 5, 5, 12] => true
  | _ => false

#guard variadicLoopStepExtraMiddleRepeatsTwice

def ordinaryRunStepStillRejectsMultiValueState : Bool :=
  match KatLang.runEvalM <| KatLang.runStep
      (alg ["history"] [] [] [.param "history"])
      KatLang.EvalCtx.empty
      []
      (.sequenceValue [.atom 1, .atom 2, .atom 4]) with
  | Except.error err => innermostIsArityMismatch 0 2 err
  | _ => false

#guard ordinaryRunStepStillRejectsMultiValueState

def loopBoundaryPairStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .param "b",
    .binary .add (.param "a") (.param "b")
  ]

def loopBoundaryPairWhileStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.num 1),
    .binary .add (.param "b") (.num 10),
    .binary .lt (.param "a") (.num 2)
  ]

def loopBoundarySequenceValueRepeatStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)]
  ]

def loopBoundarySequenceValueWhileStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)],
    .num 0
  ]

def sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1,
        .num 2
      ]))
      "take"
      (some [.num 1])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1,
        .num 2
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundarySequenceValueRepeatStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem

def sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 0,
        .num 0
      ]))
      "take"
      (some [.num 1])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 0,
        .num 0
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallWhileSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundarySequenceValueWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 1
      ]))
      "count"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileSequenceValueStateCountsOneItem

def loopBoundarySumPairStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.param "b")
  ]

def loopBoundaryIdentityAlg : Algorithm :=
  alg ["history"] [] [] [.param "history"]

def loopBoundaryVariadicIdentityAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [.param "values"]

def loopBoundarySequenceValueHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .capture [
      .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
    ]
  ]

def loopBoundarySpreadHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopInitialManyExplicitArgsCreateManySlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 1, .num 2])
  ])) with
  | Except.ok (.sequenceValue [.atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialManyExplicitArgsCreateManySlots

-- A single-collecting loop step binds many separate init slots as its item supply
-- (Aspect 2: matches C#). Step(*values) = values with repeat(1, 1, 2, 3) collects
-- values = [1, 2, 3] (one exact list) rather than rejecting the extra slots as the
-- old strict path did.
def loopInitialExplicitVariadicStepCapturesManySlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryVariadicIdentityAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 1, .num 2, .num 3])
  ])) with
  | Except.ok (.listValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialExplicitVariadicStepCapturesManySlots

def loopInitialSequenceValuePropertyArgIsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialSequenceValuePropertyArgIsOneSlot

def loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "Pair"])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams

def loopInitialExplicitSelectionsSplitSequenceValueArg : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ])
  ])) with
  | Except.ok (.atom 3) => true
  | _ => false

#guard loopInitialExplicitSelectionsSplitSequenceValueArg

def loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySequenceValueHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat

def loopInitialSpreadStepOutputStillBecomesNextStateSlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySpreadHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSpreadStepOutputStillBecomesNextStateSlots

def loopInitialMultiOutputPropertyArgIsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "Values"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialMultiOutputPropertyArgIsOneSlot

-- Explicit selections that split a multi-output property into separate init slots are
-- bound by the single-collecting step as its item supply (Aspect 2: matches C#), so the
-- three split slots are collected as values = [1, 2, 4] instead of being rejected.
def loopInitialExplicitSelectionsSplitMultiOutputProperty : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryVariadicIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      .index (resolve "Values") (.num 0),
      .index (resolve "Values") (.num 1),
      .index (resolve "Values") (.num 2)
    ])
  ])) with
  | Except.ok (.listValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialExplicitSelectionsSplitMultiOutputProperty

--------------------------------------------------------------------------------
-- User-call parameter binding (movable collecting binding, preserved argument boundaries)
--------------------------------------------------------------------------------
-- F(x, *y, z) is a mixed fixed/collecting parameter list. The supplied call slots
-- are matched prefix/collecting/suffix without implicitly opening a grouped argument;
-- the collecting parameter collects its assigned middle slots as one exact immutable list.

def deconstructSumAlg : Algorithm :=
  algWithParameters [
    { name := "x" }, { name := "y", kind := .collecting }, { name := "z" }
  ] [] [] [
    .binary .add (.binary .add (.param "x") (.dotCall (.param "y") "sum" none)) (.param "z")
  ]

def deconstructFiveItems : List KatLang.Expr := [.num 1, .num 2, .num 3, .num 4, .num 5]
def deconstructFiveArg : Algorithm := alg [] [] [] deconstructFiveItems

-- F(1, 2, 3, 4, 5): five direct item slots.
def deconstructionDirectItemSupply : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") deconstructFiveItems
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionDirectItemSupply

-- F(A) where A = 1, 2, 3, 4, 5: one sequence-valued argument is supplied.
-- Function-call binding does not implicitly open it, so the mixed fixed/variadic
-- shape is under-supplied.
def deconstructionSingleGroupedArgumentRequiresSpread : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") [resolve "A"]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false

#guard deconstructionSingleGroupedArgumentRequiresSpread

-- F(A*): explicit spread supplies five slots.
def deconstructionSpreadArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") [sequenceSpread (resolve "A")]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionSpreadArgument

-- F(1, 2): the collecting parameter collects zero items, so x = 1, y = [], z = 2 and y.sum = 0.
def deconstructionEmptyRest : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") [.num 1, .num 2]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard deconstructionEmptyRest

-- p1, p2, *rest, q1, q2 against seven items binds the middle three to rest.
def deconstructionMatchAlg : Algorithm :=
  algWithParameters [
    { name := "p1" }, { name := "p2" }, { name := "rest", kind := .collecting },
    { name := "q1" }, { name := "q2" }
  ] [] [] [
    .param "p1", .param "p2", .dotCall (.param "rest") "count" none, .param "q1", .param "q2"
  ]

def deconstructionMatchingAlgorithm : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructionMatchAlg)] [
    .call (resolve "F") [.num 1, .num 2, .num 3, .num 4, .num 5, .num 6, .num 7]
  ])) with
  | Except.ok [1, 2, 3, 6, 7] => true
  | _ => false

#guard deconstructionMatchingAlgorithm

-- A single scalar argument is a one-item supply: F(first, *tail) with 1 binds
-- first = 1 and the collecting parameter collects [] (tail.count = 0).
def deconstructFirstTailAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "tail", kind := .collecting }] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def deconstructionScalarArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructFirstTailAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard deconstructionScalarArgument

-- A sequence-value parameter pattern also normalizes a scalar to a one-item
-- supply: F((first, *tail)) with the scalar 1 binds first = 1, tail = [].
def deconstructSequenceValueFirstTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "first" }, .capture { name := "tail", kind := .collecting }]
  ] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def sequenceValuePatternScalarArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard sequenceValuePatternScalarArgument

-- Parity guard: callback deconstruction is intentionally deferred, so the counted
-- callback path keeps the strict singleton-only scalar fallback that C#
-- `BindCountedParameterPattern` uses. Applying the same sequence-value
-- deconstruction callback to scalar map elements must fail (badArity), NOT silently
-- deconstruct each scalar into first/tail. This keeps the counted callback path from
-- accepting callback deconstruction before the C# path does.
def sequenceValueDeconstructionCallbackOnScalarFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "map") [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "F"
    ]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard sequenceValueDeconstructionCallbackOnScalarFails

-- Aspect 2 callback boundary (positive parity, mirrors C#
-- DeconstructionBindingTests.CallbackDeconstruction_OnSequenceValueRows_BindsPerRow):
-- a deconstruction-shaped callback applied per sequence-value row binds x/*y/z
-- within each row. With Rows = (1, 2, 3), (4, 5, 6) and F(x, *y, z) = x + y.sum + z,
-- Rows.map(F) is 6 and 15. Row callbacks work while scalar-element deconstruction
-- stays strict (see sequenceValueDeconstructionCallbackOnScalarFails above).
def deconstructionRowsAlg : Algorithm :=
  alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3],
    sequenceItems [.num 4, .num 5, .num 6]
  ]

def deconstructionCallbackOnSequenceValueRows : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Rows", deconstructionRowsAlg),
    ("F", deconstructSumAlg)
  ] [
    .dotCall (resolve "Rows") "map" (some [resolve "F"])
  ])) with
  | Except.ok [6, 15] => true
  | _ => false

#guard deconstructionCallbackOnSequenceValueRows

-- A single collecting parameter collects the supplied call argument slots as one
-- exact list. One grouped argument is one collected element (`Sum(A)` binds
-- `values = [A]`, so the numeric `sum` constraint rejects the sequence
-- element), while separate slots collect their items.
def restOnlyCollectAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "sum" none
  ]

def restOnlyConsumesItemSupply : Bool :=
  let singleGroupedArg :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [resolve "A"]
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  let multipleSlots :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [.num 1, .num 2, .num 3]
    ])) with
    | Except.ok [6] => true
    | _ => false
  singleGroupedArg && multipleSlots

#guard restOnlyConsumesItemSupply

-- A FUNCTION-shaped argument (a builtin here) reaching a collecting binding reports
-- the targeted typeMismatch: a collecting binding collects VALUES and has no dual
-- algorithm channel. C#: `BindParameterPatternList` (same kind; the C#
-- message additionally names the collecting parameter).
def restFunctionShapedArgumentReportsTypeMismatch : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("G", algWithParameters [{ name := "fs", kind := .collecting }] [] [] [.param "fs"])
  ] [
    .call (resolve "G") [resolve "sum"]
  ])) with
  | Except.error err =>
      innermostIsTypeMismatch
        "A collecting parameter collects values, but a supplied argument is a function. Pass a value, or call the function so its result is collected."
        err
  | _ => false

#guard restFunctionShapedArgumentReportsTypeMismatch

-- A zero-parameter VALUE property whose body fails is NOT function-shaped
-- (`Algorithm.isFunctionShaped`): the genuine evaluation error surfaces
-- through the collecting binding instead of the function diagnostic.
def restErroredValuePropertyArgumentSurfacesRealError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Bad", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
    ("G", algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])
  ] [
    .call (resolve "G") [resolve "Bad"]
  ])) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard restErroredValuePropertyArgumentSurfacesRealError

def mixedVariadicBoundaryAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [
    .dotCall (.param "first") "count" none,
    .dotCall (.param "rest") "count" none
  ]

def mixedVariadicPlainSequenceArgumentPreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") [resolve "A"]
  ])) with
  | Except.ok [2, 0] => true
  | _ => false

#guard mixedVariadicPlainSequenceArgumentPreservesBoundary

def mixedVariadicExplicitSpreadOpensSequenceArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") [sequenceSpread (resolve "A")]
  ])) with
  | Except.ok [1, 1] => true
  | _ => false

#guard mixedVariadicExplicitSpreadOpensSequenceArgument

def itemSupplySumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }] [] [] [
    .dotCall (.param "x") "sum" none
  ]

-- Single-collecting `G(*x)` distinguishes grouped from spread supplies: `G(A)` and
-- the written-tuple call bind ONE collected sequence element (numeric `sum`
-- constraint error), while `G(A*)` and separate slots supply the items and
-- sum to 15.
def restOnlyItemSupplyDistinguishesGroupedFromSpread : Bool :=
  let sumsTo15 (args : List KatLang.Expr) : Bool :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.ok [15] => true
    | _ => false
  let groupedFails (args : List KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  groupedFails [resolve "A"]
    && sumsTo15 [sequenceSpread (resolve "A")]
    && sumsTo15 deconstructFiveItems
    && groupedFails [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]

#guard restOnlyItemSupplyDistinguishesGroupedFromSpread

-- An empty call binds an empty item supply (min arity 0): `G()` sums to 0.
def restOnlyEmptyCallSumsToZero : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", itemSupplySumAlg)] [
    .call (resolve "G") []
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard restOnlyEmptyCallSumsToZero

def itemSupplyCountAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }] [] [] [
    .dotCall (.param "x") "count" none
  ]

-- Multiple sibling grouped values are preserved (G(A, B) binds
-- x = [(1, 2), (3, 4)], count 2), not auto-flattened; only explicit spread
-- opens them into one item supply (G(A*, B*) binds x = [1, 2, 3, 4], count 4).
def restOnlyPreservesSiblingGroupedValues : Bool :=
  let twoItemRoot (argExprs : List KatLang.Expr) : Algorithm :=
    algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4]),
      ("G", itemSupplyCountAlg)
    ] [ .call (resolve "G") argExprs ]
  let preserved :=
    match runFlat (.algorithmExpr (twoItemRoot [resolve "A", resolve "B"])) with
    | Except.ok [2] => true
    | _ => false
  let opened :=
    match runFlat (.algorithmExpr (twoItemRoot [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")])) with
    | Except.ok [4] => true
    | _ => false
  preserved && opened

#guard restOnlyPreservesSiblingGroupedValues

def restPrefixSumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }, { name := "y" }] [] [] [
    .binary .add (.dotCall (.param "x") "sum" none) (.param "y")
  ]

-- `(((1, 2, 3, 4, 5)))` is a doubly-nested singleton sequence value: a capture
-- whose single row is a capture of the five items.
def nestedSingletonFive : KatLang.Expr :=
  .capture [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]

-- Repeated singleton grouping is useful-structure canonicalized as a value, but
-- a function call still receives one argument unless `value*` /
-- `value*` is written.
def repeatedSingletonBoundaryDoesNotImplicitlyOpenCallArgument : Bool :=
  let plainMixed :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") [nestedSingletonFive]
    ])) with
    | Except.error err => innermostIsArityMismatch 2 1 err
    | _ => false
  let spreadMixed :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") [sequenceSpread nestedSingletonFive]
    ])) with
    | Except.ok [15] => true
    | _ => false
  plainMixed && spreadMixed

#guard repeatedSingletonBoundaryDoesNotImplicitlyOpenCallArgument

end KatLangTests
