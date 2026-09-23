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

-- `Arg.Collect` is `Collect(Arg)`: the receiver is ONE written argument
-- slot holding the sequence value `(1, 2, 3)`; it is the lone collector's
-- whole segment, so the collector supply-boundary law opens it one level and
-- the collecting parameter collects `list = [1, 2, 3]` (count 3).
def variadicDotCallReceiverOpensOneLevel : Bool :=
  match runFlat (.algorithmExpr variadicSimpleRoot) with
  | Except.ok [3] => true
  | _ => false

#guard variadicDotCallReceiverOpensOneLevel

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

-- The lone written receiver slot opens exactly ONE level: `Arg.Collect`
-- collects `list = [(1, 2), (3, 4)]` (count 2, the nested pairs intact), and
-- `atoms` still reaches all four numeric leaves through the collected list.
def variadicPreservesNestedSequenceValues : Bool :=
  match runFlat (.algorithmExpr variadicNestedSequenceValuesRoot) with
  | Except.ok [2, 4] => true
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

-- Supplying a NAMED property's items to the variadic mean: the explicit
-- spread call `Mean(Arg*)` and the spread receiver `Arg*.Mean` (which IS
-- `Mean(Arg*)`) supply three final items; the stored receiver `Arg.Mean` is
-- `Mean(Arg)` — one written sequence slot that is the lone collector's whole
-- segment, opened one level to the same three items — and so is the captured
-- spread `(Arg*).Mean` = `Mean((Arg*))`. All agree with the builtin
-- sum/count pipeline.
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
    .dotCall (sequenceSpread (resolve "Arg")) "Mean" none,
    .dotCall (resolve "Arg") "Mean" none,
    .dotCall (sequenceSpreadReceiver (resolve "Arg")) "Mean" none,
    resolve "Direct"
  ])) with
  | Except.ok [2, 2, 2, 2, 2] => true
  | _ => false

#guard variadicMeanMatchesBuiltinSumCount

-- `CountViaVariadic(Arg)` and `Arg.CountViaVariadic` supply ONE written
-- argument slot, the sequence value `((1, 2), (3, 4))`; as the lone
-- collector's whole segment it opens one level, so the collecting parameter
-- collects `values = [(1, 2), (3, 4)]` (count 2) — the same count the
-- fixed-collection builtin `Arg.count` reports through its post-binding
-- view; `atoms` recursively reaches all four numeric leaves through the
-- collected list.
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
  | Except.ok [2, 2, 2, 4] => true
  | _ => false

#guard variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms

-- A fixed parameter binds the receiver value itself, so the collection
-- builtin opens it through its post-binding view (count 3 for a sequence
-- and for a list alike); a collecting parameter applies the collector
-- supply-boundary law to its lone written slot: a SEQUENCE receiver opens
-- one level (count 3), a LIST receiver stays one exact collected element
-- (count 1). The two shapes remain observably different on a list.
def ordinaryAndVariadicCountStayStructurallyDifferent : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("ArgList", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
    ("Ordinary", ordinaryCountAlg),
    ("Variadic", variadicCountAlg)
  ] [
    .dotCall (resolve "Arg") "Ordinary" none,
    .dotCall (resolve "Arg") "Variadic" none,
    .dotCall (resolve "ArgList") "Ordinary" none,
    .dotCall (resolve "ArgList") "Variadic" none
  ])) with
  | Except.ok [3, 3, 3, 1] => true
  | _ => false

#guard ordinaryAndVariadicCountStayStructurallyDifferent

-- Scaling a named property's ITEMS uses the spread receiver `Arg*.Scale(10)`
-- — `Scale(Arg*, 10)`: the suffix takes the factor, and the collector collects
-- Arg's three spread items as ordinary slots.
def variadicBeforeSuffixSupportsDotCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    .dotCall (sequenceSpread (resolve "Arg"))
      "Scale" (some [.num 10])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard variadicBeforeSuffixSupportsDotCall

-- TotalWithFee(*values, fee) is a deconstruction parameter list. The spread
-- group receiver `(10, 20, 30)*.TotalWithFee(5)` is `TotalWithFee(10, 20, 30, 5)`:
-- the call supplies four slots, the variadic collects [10, 20, 30] and `fee`
-- binds 5, giving sum 60 + 5 = 65.
def variadicInlineTupleDotCallWithSuffixCapturesReceiverItems : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall sequenceSpread1230
      "TotalWithFee" (some [.num 5])
  ])) with
  | Except.ok (.atom 65) => true
  | _ => false

#guard variadicInlineTupleDotCallWithSuffixCapturesReceiverItems

-- `Data.TotalWithFee(5)` is `TotalWithFee(Data, 5)`: the named receiver is one
-- written argument slot; the suffix takes 5 first, and the segment left to
-- the collector is that lone sequence value, which opens one level —
-- `values = [10, 20, 30]`, total 65, exactly like the spread receiver above.
def collectingNamedMultiOutputDotCallWithSuffixOpensOneLevel : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (resolve "Data") "TotalWithFee" (some [.num 5])
  ])) with
  | Except.ok [65] => true
  | _ => false

#guard collectingNamedMultiOutputDotCallWithSuffixOpensOneLevel

-- For a SEQUENCE-valued receiver the named receiver, the spread receiver
-- `Data*.TotalWithFee(5)`, and the CAPTURED spread `(Data*).TotalWithFee(5)`
-- all total 65: the named and captured forms are one written sequence slot
-- opened by the collector law, the spread form supplies the three final
-- items. A LIST receiver keeps the distinction: `List.TotalWithFee(5)`
-- collects `[[10, 20, 30]]` (numeric-constraint error) while
-- `List*.TotalWithFee(5)` totals 65 — only the spread marker opens a list.
def variadicInlineTupleSpreadReceiverAgreesForSequenceDiffersForList : Bool :=
  let dataProps : List (Prod String Algorithm) := [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("List", alg [] [] [] [.listLiteral [.num 10, .num 20, .num 30]]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ]
  let totals65 (receiver : KatLang.Expr) : Bool :=
    match runFlat (.algorithmExpr (algPrivate [] [] dataProps [
      .dotCall receiver "TotalWithFee" (some [.num 5])
    ])) with
    | Except.ok [65] => true
    | _ => false
  let rejectsElement (receiver : KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] dataProps [
      .dotCall receiver "TotalWithFee" (some [.num 5])
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  totals65 (resolve "Data") &&
  totals65 (sequenceSpread (resolve "Data")) &&
  totals65 (.capture [sequenceSpread (resolve "Data")]) &&
  rejectsElement (resolve "List") &&
  totals65 (sequenceSpread (resolve "List"))

#guard variadicInlineTupleSpreadReceiverAgreesForSequenceDiffersForList

-- A nested inline sequence receiver `((10, 20, 30))` normalizes to the same
-- sequence value `(10, 20, 30)` and opens one level like it (65), while a
-- genuinely nested receiver `((10, 20), 30)` opens exactly ONE level: the
-- collected list holds the inner pair, so `values.sum` hits the numeric
-- element constraint.
def variadicNestedInlineTupleDotCallOpensOneLevel : Bool :=
  (match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [
      .capture [.num 10, .num 20, .num 30]
    ]) "TotalWithFee" (some [.num 5])
  ])) with
  | Except.ok [65] => true
  | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [
      .capture [.num 10, .num 20], .num 30
    ]) "TotalWithFee" (some [.num 5])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false)

#guard variadicNestedInlineTupleDotCallOpensOneLevel

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

-- `(Arg*.Scale(10), Arg.map{n * 10})*`: a spread over the
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
        (.dotCall (sequenceSpread (resolve "Arg"))
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

/-- Regression: `F(((A), 6))` with `A = 5` — the source program reaches Lean as
    `F((A, 6))` (the C# parser erases the redundant group), and a host-built
    single capture `capture [A]` inside the pair evaluates to the scalar `5`
    itself, so pattern binding receives `5` -- never a literal-unwritable orphan
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

/-- Regression: `F(((A), 6))` with `A = (1, 2)`. The (host-built) grouped
    property reference supplies the canonical `(1, 2)` as one item -- not an
    orphan `((1, 2))` -- exactly as the bare `A` in `F((A, 6))` does. -/
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

/-- Discriminator: a single selection output row is ONE written slot in the
    prepared view AND one emitted value. Selection is a value boundary, so
    `((1, 2), (3, 4)):0` emits the selected pair with count 1 (never re-emitted
    as two values); the retained accumulator keeps the one written slot
    `[(1, 2)]`. The multi-emitting non-spread discriminator is the loop below. -/
def preparedAlgorithmOutputKeepsSelectedSlotWhole : Bool :=
  let pairOfPairs := KatLang.Expr.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let output := alg [] [] [] [.index pairOfPairs (.num 0)]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [.atom 1, .atom 2], 1),
      outputSlots := [.sequenceValue [.atom 1, .atom 2]]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputKeepsSelectedSlotWhole

/-- A non-spread multi-slot loop result still occupies one written slot even
    though its emitted count is two. Selection no longer exercises this distinction. -/
def preparedAlgorithmOutputKeepsMultiSlotLoopWhole : Bool :=
  let loop := KatLang.Expr.call (resolve "repeat")
    [.algorithmExpr (alg ["a", "b"] [] [] [.param "a", .param "b"]), .num 1, .num 1, .num 2]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  let output := KatLang.wireToCaller ctx (alg [] [] [] [loop])
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [.atom 1, .atom 2], 2),
      outputSlots := [.sequenceValue [.atom 1, .atom 2]]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputKeepsMultiSlotLoopWhole

/-- Discriminator: a multi-emitting single output row — the explicit spread of the
    selected pair, `(((1, 2), (3, 4)):0)*` — supplies two slots with count 2, so
    the slot view lists both items; only the spread opens the selection. -/
def preparedAlgorithmOutputSpreadOfSelectionSuppliesItems : Bool :=
  let pairOfPairs := KatLang.Expr.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let output := alg [] [] [] [.sequenceSpread (.index pairOfPairs (.num 0))]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [.atom 1, .atom 2], 2),
      outputSlots := [.atom 1, .atom 2]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputSpreadOfSelectionSuppliesItems

def sequenceValueSingletonFirstAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- End-to-end (PARENTHESES GROUP SYNTAX, September 2026): a sequence-value
    pattern opens the argument's VALUE, never a written slot. The selected pair is
    ONE value (selection is a value boundary) that opens to two items, so the
    singleton pattern `F((x)) = x` rejects `F(S:0)` with `arityMismatch 1 2` — and
    a host-built single capture around the selection (`capture [S:0]`, the shape
    the C# parser no longer writes because `(S:0)` IS `S:0`) is the very same
    rejection: no capture depth restores a written slot for the pattern to bind.
    Mirrors `PatternedCallSingleEvaluationTests`. -/
def sequenceValueSingletonPatternOpensTheSelectedValue : Bool :=
  let s : Algorithm := alg [] [] [] [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let direct := runResult (.algorithmExpr (algPrivate [] [] [
    ("S", s), ("F", sequenceValueSingletonFirstAlg)
  ] [
    .call (resolve "F") [.index (resolve "S") (.num 0)]
  ]))
  let grouped := runResult (.algorithmExpr (algPrivate [] [] [
    ("S", s), ("F", sequenceValueSingletonFirstAlg)
  ] [
    .call (resolve "F") [.capture [.index (resolve "S") (.num 0)]]
  ]))
  (match direct with
   | Except.error err => innermostIsArityMismatch 1 2 err
   | _ => false) &&
  (match grouped with
   | Except.error err => innermostIsArityMismatch 1 2 err
   | _ => false)

#guard sequenceValueSingletonPatternOpensTheSelectedValue

/-- The one-element LIST is what opens to exactly one item: `F([S:0])` binds the
    whole selected pair. -/
def sequenceValueSingletonPatternBindsTheOneListElement : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("S", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("F", sequenceValueSingletonFirstAlg)
  ] [
    .call (resolve "F") [.listLiteral [.index (resolve "S") (.num 0)]]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueSingletonPatternBindsTheOneListElement

/-- PARENTHESES GROUP SYNTAX (September 2026): `F(((1, 2)))` with
    `F((x, y)) = x` IS `F((1, 2))` — the C# parser erases the redundant group, so
    the source program reaches Lean as `.call F [.capture [1, 2]]` and the pattern
    opens the pair's VALUE: `x = 1`. A host-built single capture around the pair
    (`capture [capture [1, 2]]`, a shape no source produces) evaluates to the very
    same value and binds identically — binding never sees written slots, so no
    capture depth can change it. -/
def sequenceValuePatternLiteralWrappedPairOpensLikeThePair : Bool :=
  let source := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [.capture [.num 1, .num 2]]
  ]))
  let hostGrouped := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [.capture [.capture [.num 1, .num 2]]]
  ]))
  let hostDeeplyGrouped := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [.capture [.capture [.capture [.num 1, .num 2]]]]
  ]))
  (match source with | Except.ok (.atom 1) => true | _ => false) &&
  (match hostGrouped with | Except.ok (.atom 1) => true | _ => false) &&
  (match hostDeeplyGrouped with | Except.ok (.atom 1) => true | _ => false)

#guard sequenceValuePatternLiteralWrappedPairOpensLikeThePair

/-- The pattern still demands exactly two items: a three-item value is the
    `arityMismatch 2 3` whatever grouping surrounds it. -/
def sequenceValuePatternThreeItemValueReportsValueArity : Bool :=
  let source := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [.capture [.num 1, .num 2, .num 3]]
  ]))
  let hostGrouped := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [.capture [.capture [.num 1, .num 2, .num 3]]]
  ]))
  (match source with | Except.error err => innermostIsArityMismatch 2 3 err | _ => false) &&
  (match hostGrouped with | Except.error err => innermostIsArityMismatch 2 3 err | _ => false)

#guard sequenceValuePatternThreeItemValueReportsValueArity

/-- Regression: `A = ((1, 2))` normalizes at property construction to
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

/-- `KeepFirst(((1, 2)), 3)` with `KeepFirst((x, y), z) = x` IS
    `KeepFirst((1, 2), 3)`: the trailing fixed argument binds normally and the
    sequence-value pattern opens the pair's value (`x = 1`) — in the source shape
    and in the host-built single-capture shape alike. -/
def sequenceValuePatternWrappedPairWithFixedSuffixOpensLikeThePair : Bool :=
  let source := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstWithFixedSuffixAlg)] [
    .call (resolve "F") [.capture [.num 1, .num 2], .num 3]
  ]))
  let hostGrouped := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstWithFixedSuffixAlg)] [
    .call (resolve "F") [.capture [.capture [.num 1, .num 2]], .num 3]
  ]))
  (match source with | Except.ok (.atom 1) => true | _ => false) &&
  (match hostGrouped with | Except.ok (.atom 1) => true | _ => false)

#guard sequenceValuePatternWrappedPairWithFixedSuffixOpensLikeThePair

def sequenceValueSingleCaptureAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- `IdSeq(((1, 2)))` with `IdSeq((x)) = x` IS `IdSeq((1, 2))`: the singleton
    sequence-value pattern opens the pair's value to TWO items and rejects it
    (`arityMismatch 1 2`) — in the source shape and in the host-built
    single-capture shape alike, because binding never sees written slots. -/
def sequenceValuePatternSingleCaptureRejectsThePair : Bool :=
  let source := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") [.capture [.num 1, .num 2]]
  ]))
  let hostGrouped := runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") [.capture [.capture [.num 1, .num 2]]]
  ]))
  (match source with | Except.error err => innermostIsArityMismatch 1 2 err | _ => false) &&
  (match hostGrouped with | Except.error err => innermostIsArityMismatch 1 2 err | _ => false)

#guard sequenceValuePatternSingleCaptureRejectsThePair

/-- `IdSeq([(1, 2)])`: a one-element list opens to exactly one item, and that item
    is the CANONICAL pair `(1, 2)` — never a literal-unwritable orphan `((1, 2))`.
    The structural match pins the exact shape. -/
def sequenceValuePatternSingleCaptureBindsTheListElementAsCanonicalItem : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") [.listLiteral [.capture [.num 1, .num 2]]]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternSingleCaptureBindsTheListElementAsCanonicalItem

def sequenceValueSingleCaptureCountAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.dotCall (.param "x") "count" none]

/-- The canonically bound item observes consistently -- `x.count` for the
    `IdSeq([(1, 2)])` binding is 2, matching the structural shape `(1, 2)` (an
    orphan `((1, 2))` would count 1). -/
def sequenceValuePatternSingleCaptureListElementCountsItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureCountAlg)] [
    .call (resolve "F") [.listLiteral [.capture [.num 1, .num 2]]]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValuePatternSingleCaptureListElementCountsItems

/-- PARENTHESES GROUP SYNTAX (September 2026): a sequence-value pattern opens the
    argument's VALUE — the two argument shapes whose former written-slot view
    differed from the value view now bind by the value alone.
    `P((A*))` with `A = [[1, 2]]` and `P((*xs)) = xs`: the capture of the lone
    spread item is the list `[1, 2]` (one item normalizes to itself), which the
    pattern opens — `xs = [1, 2]`, exactly as `P([1, 2])` and `P(A*)`.
    `F({S})` with `S = 1, 2` and `F((a, b)) = a + b`: the single-row block's value
    is the pair, which the pattern opens — `3`, exactly as `F(S)` and `F((S))`. -/
def sequenceValuePatternOpensTheValueOfSpreadCapturesAndBlocks : Bool :=
  let collector := algWithParameterPatterns [
    .sequenceValue [.capture { name := "xs", kind := .collecting }]
  ] [] [] [.param "xs"]
  let pairSum := algWithParameterPatterns [
    .sequenceValue [.capture { name := "a" }, .capture { name := "b" }]
  ] [] [] [.binary .add (.param "a") (.param "b")]
  let a := alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2]]]
  let s := alg [] [] [] [.num 1, .num 2]
  let collected (argument : KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", a), ("P", collector)]
      [.call (resolve "P") [argument]])) with
    | Except.ok (.listValue [.atom 1, .atom 2]) => true
    | _ => false
  let summed (argument : KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] [("S", s), ("F", pairSum)]
      [.call (resolve "F") [argument]])) with
    | Except.ok (.atom 3) => true
    | _ => false
  collected (.capture [.sequenceSpread (.resolve "A")]) &&
  collected (.sequenceSpread (.resolve "A")) &&
  collected (.listLiteral [.num 1, .num 2]) &&
  summed (.algorithmExpr (alg [] [] [] [.resolve "S"])) &&
  summed (.resolve "S") &&
  summed (.capture [.num 1, .num 2])

#guard sequenceValuePatternOpensTheValueOfSpreadCapturesAndBlocks

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

/-- Ordinary nested parameter patterns retain scalar one-item fallback. Only a
    list retains a unary structural boundary; scalars need no such boundary.
    This is user-call binding; callback binding shares the same opening rule
    (`Result.sequenceValuePatternItems`, pinned for callbacks by the S3 guards
    in `CoreTests/SequenceCallbackBuiltins.lean`). -/
def nestedParameterPatternKeepsScalarFallback : Bool :=
  let collector := algWithParameterPatterns [
    .sequenceValue [.sequenceValue [.capture { name := "xs", kind := .collecting }]]
  ] [] [] [.param "xs"]
  let call (argument : KatLang.Expr) :=
    runResult (.algorithmExpr (algPrivate [] [] [("P", collector)]
      [.call (resolve "P") [argument]]))
  (match call (.num 7) with
   | .ok (.listValue [.atom 7]) => true | _ => false) &&
  (match call (.boolLiteral true) with
   | .ok (.listValue [.bool true]) => true | _ => false) &&
  (match call (.stringLiteral "s") with
   | .ok (.listValue [.str "s"]) => true | _ => false) &&
  (match call (.listLiteral [.emptySequence 0]) with
   | .ok (.listValue []) => true | _ => false) &&
  (match call (.capture [.num 1, .num 2]) with
   | .error error => innermostIsArityMismatch 1 2 error | _ => false)

#guard nestedParameterPatternKeepsScalarFallback

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
    .compare .lt loopVariadicNextExpr (.num 6),
    .boolLiteral true,
    .boolLiteral false
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

-- The step's ONE output row is the joined sequence `(1, 2, 4, 5, true)`, so
-- the loop sees a single output slot that is not a Boolean continuation flag:
-- the Boolean-requirement error names that slot (a value-kind error, never a
-- truth test of the slot's contents).
def variadicLoopStepWhileUsesExpandedState : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicWhileAppendNextAlg)] [
    .dotCall (resolve "Step") "while" (some [
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.error err =>
      innermostIsBooleanRequired "while continuation flag (the step's last output)"
        "a sequence value with 5 sequence elements: (1, 2, 4, 5, true)" err
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
-- as one list. The minimum is the FIXED (non-variadic) parameter count —
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
    .compare .lt (.param "a") (.num 2)
  ]

def loopBoundarySequenceValueRepeatStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)]
  ]

def loopBoundarySequenceValueWhileStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)],
    .boolLiteral false
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
-- the collecting parameter collects its assigned middle slots as one list.

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
-- Call binding does not implicitly open it, so the mixed fixed/variadic
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

-- Callback binding of a scalar element follows the ordinary call (S3, September
-- 2026; mirrors C# DeconstructionBindingTests
-- .CallbackSequenceValueDeconstruction_OnScalarElement_BindsLikeTheOrdinaryCall):
-- both binders open a nested pattern's value through the ONE rule
-- `Result.sequenceValuePatternItems`, so each scalar map element is the ordinary
-- one-item supply for `(first, *tail)` exactly as in `F(1)` above. The body is one
-- list value so map's single-value contract cannot mask the binding. (The counted
-- callback binder formerly fell back only for one-item groups, and this guard
-- pinned the resulting badArity.)
def deconstructSequenceValueFirstTailListAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "first" }, .capture { name := "tail", kind := .collecting }]
  ] [] [] [
    .listLiteral [.param "first", .dotCall (.param "tail") "count" none]
  ]

def sequenceValueDeconstructionCallbackOnScalarBindsLikeCall : Bool :=
  let program (output : KatLang.Expr) :=
    .algorithmExpr (algPrivate [] [] [("F", deconstructSequenceValueFirstTailListAlg)] [output])
  (match runResult (program (.call (resolve "map") [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "F"
    ])) with
   | Except.ok (.listValue [
       .listValue [.atom 1, .atom 0],
       .listValue [.atom 2, .atom 0],
       .listValue [.atom 3, .atom 0]]) => true
   | _ => false) &&
  (match runResult (program (.call (resolve "F") [.num 1])) with
   | Except.ok (.listValue [.atom 1, .atom 0]) => true
   | _ => false)

#guard sequenceValueDeconstructionCallbackOnScalarBindsLikeCall

-- Aspect 2 callback boundary (positive parity, mirrors C#
-- DeconstructionBindingTests.CallbackDeconstruction_OnSequenceValueRows_BindsPerRow):
-- a deconstruction-shaped callback applied per sequence-value row binds x/*y/z
-- within each row. With Rows = (1, 2, 3), (4, 5, 6) and F(x, *y, z) = x + y.sum + z,
-- Rows.map(F) is 6 and 15. Scalar elements bind like the ordinary call too (see
-- sequenceValueDeconstructionCallbackOnScalarBindsLikeCall above).
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

-- A single collecting parameter collects the segment allocated to it as one
-- exact list. One grouped SEQUENCE argument is the whole segment and opens
-- one level (`Sum(A)` binds `values = [1, 2, 3, 4, 5]`, sum 15), separate
-- slots collect their items (sum 6), and one grouped LIST argument is one
-- exact collected element (`Sum([1, 2, 3])` binds `values = [[1, 2, 3]]`,
-- so the numeric `sum` constraint rejects the list element).
def restOnlyCollectAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "sum" none
  ]

def restOnlyConsumesItemSupply : Bool :=
  let singleGroupedArg :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [resolve "A"]
    ])) with
    | Except.ok [15] => true
    | _ => false
  let multipleSlots :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [.num 1, .num 2, .num 3]
    ])) with
    | Except.ok [6] => true
    | _ => false
  let singleListArg :=
    match runResult (.algorithmExpr (algPrivate [] [] [("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [.listLiteral [.num 1, .num 2, .num 3]]
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  singleGroupedArg && multipleSlots && singleListArg

#guard restOnlyConsumesItemSupply

-- A callable-shaped argument (a builtin here) reaching a collecting binding reports
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
        "A collecting parameter collects values, but a supplied argument is a callable. Pass a value, or call the callable so its result is collected."
        err
  | _ => false

#guard restFunctionShapedArgumentReportsTypeMismatch

-- A zero-parameter VALUE property whose body fails is NOT callable-shaped
-- (`Algorithm.isFunctionShaped`): the genuine evaluation error surfaces
-- through the collecting binding instead of the callable diagnostic.
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

-- Single-collecting `G(*x)`: a lone grouped SEQUENCE argument — `G(A)` and
-- the written-group call alike — is the collector's whole segment and opens
-- one level, so it sums to 15 exactly like `G(A*)` and the separate slots.
-- The grouped value stays exact where it is NOT the whole segment
-- (`G(A, 0)` collects `[(1, …, 5), 0]`, a numeric `sum` constraint error),
-- and a lone LIST argument never opens (`G([1, …, 5])` fails the same way
-- while `G([1, …, 5]*)` sums to 15).
def restOnlyLoneSequenceOpensOneLevel : Bool :=
  let sumsTo15 (args : List KatLang.Expr) : Bool :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.ok [15] => true
    | _ => false
  let elementFails (args : List KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  sumsTo15 [resolve "A"]
    && sumsTo15 [sequenceSpread (resolve "A")]
    && sumsTo15 deconstructFiveItems
    && sumsTo15 [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]
    && elementFails [resolve "A", .num 0]
    && elementFails [.listLiteral deconstructFiveItems]
    && sumsTo15 [sequenceSpread (.listLiteral deconstructFiveItems)]

#guard restOnlyLoneSequenceOpensOneLevel

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

-- Host-built single-row capture around the five-item capture. The source
-- `(((1, 2, 3, 4, 5)))` now parses directly to the inner capture.
def nestedSingletonFive : KatLang.Expr :=
  .capture [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]

-- Repeated singleton grouping is useful-structure normalized as a value, but
-- a call still receives one argument unless `value*` /
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
