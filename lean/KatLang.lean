-- KatLang authoritative language model (core AST + semantics + while/repeat init boundaries + higher-order alg params + conditional algorithms + first-class strings).
-- Release version: see KatLangVersion.props.
-- Core semantics are authoritative. Surface syntax handled externally except
-- where noted (implicit parameter detection, while/repeat init boundaries).
-- Load elaboration is handled entirely in the front-end / elaboration layer;
-- the core AST never contains load nodes (see load elaboration section below).
--
-- Numeric model:
--   The Lean core uses unbounded Int while the C# runtime uses IEEE 754
--   Decimal128 (34-significant-digit decimal floating point).
--   The integer-valued operations use truncation toward zero (Int.tdiv /
--   Int.tmod). On the common exact integer subdomain this agrees with the C#
--   reference, including negative operands (`-7 div 2 = -3`,
--   `-7 mod 2 = -1`). This is not a blanket "integer source = shared model"
--   rule: large integral arithmetic can round or overflow in the
--   finite-precision runtime. `div` itself truncates the EXACT quotient there
--   too (G-3, September 2026 — never a quotient first rounded to 34 digits)
--   and is exact wherever the truncated quotient is representable: every
--   |q| <= 10^34 (the exact consecutive-integer domain) and every representable
--   sparse integer beyond it; a truncated quotient with more than 34
--   significant digits is rounded toward zero to 34 digits in the runtime
--   while this core keeps the exact integer. Fractional
--   results the decimal runtime can represent are another documented Int-core
--   limitation: `/`-style quotients and the `avg` builtin truncate here
--   (`7 / 2 = 3` and `avg((1, 2)) = 1`) but yield decimals in the runtime
--   (`3.5` and `1.5`), and negative exponents with
--   |base| >= 2 raise an explicit error instead of silently truncating the
--   reciprocal to 0 (see `negativeIntPow`). Zero raised to a negative
--   exponent is a language error in BOTH models: the runtime rejects EVERY
--   exponent below zero (`0 ^ -1`, `0 ^ -0.5`, `Math.Pow(0, -2.5)` alike —
--   a negative power of zero is reciprocal-like, and a zero divisor is an
--   error, never IEEE `Infinity`), and the Int core states that same rule at
--   its only reachable instance, integer exponents. Fractional exponents
--   have no Int counterpart, so this is a documented model boundary, not a
--   narrower runtime rule.
--   IEEE special values and range behavior exist only in the runtime: NaN,
--   ±Infinity, signed zero, overflow to infinity, and gradual underflow
--   (subnormals and eventual zero) have no Int
--   counterpart, so the core neither models nor approximates them — they are
--   pinned as C#-only canonical cases in the executable language spec
--   (the LanguageSpecCorpus model-divergence family) and stay excluded from
--   the Lean-guarded corpora. The routing rule for numeric changes is the
--   "Core numeric semantics" row in src/KatLang/SEMANTIC-ALIGNMENT.md.
--
-- Open declarations:
--   `open` is a DECLARATION keyword, not a property assignment.
--   Exact syntax: `open target1, target2, ...` (no `=` sign).
--   Each algorithm may contain at most ONE `open` declaration with a comma-separated
--   list of targets. The opens list maps to `Algorithm.opens : List Expr`.
--
--   Valid open targets (post-elaboration / canonical forms):
--     - identifier:     `open Math`            → Resolve("Math")
--     - dotted path:    `open Lib.Sub`         → DotCall(Resolve("Lib"), "Sub", none)
--     - load:           `open load('url')`     → Call(Resolve("load"), ...) → elaborated to Block (surface-only, not in core Expr)
--     - inline block:   `open { public X = 1 }` → Block(...)
--
--   Exact-syntax sugar (parser-only, not in core model):
--     - `open 'url'` desugars to `open load('url')` before elaboration.
--     Raw string literals do NOT survive into the canonical open list.
--
-- Clause-definition syntax (parser-only, not in core model):
--   Clause-style definitions use syntax:
--     `Name(pattern) = body`
--   This form is recognized only in definition position.
--   In expression position, `Name(args)` remains an ordinary call.
--   On the left-hand side of `=` in definition context, `Name(...)` is not a
--   call expression — it is clause-pattern syntax.
--
--   Elaboration / classification rule:
--     - a same-name clause group elaborates to ordinary `Algorithm.mk` only
--       when the group contains exactly one clause and that sole head is a
--       recursive parameter pattern made only of captures and structural
--       (sequence or list) patterns (for example `Apply(f) = f(4)`,
--       `PairSum((x, y)) = x + y`, `Only([x]) = x`, or
--       `CountSequenceValue((*values)) = values.count`)
--     - multi-clause families and clause heads that require literal or
--       whole-argument conditional matching elaborate to `Algorithm.conditional`
--
--   This split is intentional: ordinary elaboration preserves dual-view call
--   binding for higher-order arguments, while true conditional algorithms keep
--   their full-input-specification and whole-argument matching semantics.
--
-- Structural patterns (September 2026): STRUCTURAL PATTERN DELIMITERS SELECT
--   THE VALUE KIND THEY DESTRUCTURE. In both pattern languages a
--   parenthesized structural pattern `(p1, …, pn)` (`sequenceValue`) matches
--   SEQUENCE values only and a bracketed structural pattern `[p1, …, pn]`
--   (`listValue`) matches LIST values only; neither destructures the other
--   kind, and neither treats a scalar as a one-item structure. A bare
--   binder is the only pattern that takes a value whole, whatever its kind.
--   Because there is no one-item sequence value (`Result.normalize`), a
--   sequence pattern with exactly one non-collecting item — `(x)`, `((x, y))`,
--   `([x])` — describes a boundary no value has and is INVALID
--   (`ParameterPattern.hasSingletonSequenceGroup`,
--   `Pattern.headHasSingletonSequenceGroup`, rejected before evaluation by
--   `validateExplicitParamOutputInvariant`; the C# parser reports
--   `SingletonSequencePattern`), while a collector-only `(*xs)` stays valid
--   because a collector is variadic. The one-element pattern is the list
--   pattern `[x]`. The call head's own parentheses are the call's argument
--   list, never a structural pattern.
--
-- Algorithm output (surface syntax):
--   Every non-definition expression row in an algorithm body contributes to
--   the Algorithm's `output` field. Output rows and property definitions may
--   be interleaved; there is no dedicated output keyword or output-definition
--   syntax, and `Output`/`output` are ordinary identifiers with no special
--   treatment (`Output = expr` is an ordinary property definition).
--
--   Semantic rules (enforced by evaluator, not parser):
--     - Opens provide PUBLIC properties only (lookupOpenProperties filters by isPublic).
--     - Strict isolation: opening a library does NOT import its transitive opens.
--     - Ambiguity: if multiple open targets provide the same public name, and no
--       owned/local/parent property shadows it, `ambiguousOpen` is raised.
--     - Owned/local/parent lookup takes precedence over opens (ownership-first).
--
-- Evaluator architecture (details: comment above the evaluator `mutual` block):
--   The single evaluator `mutual` block is intentionally evaluation-only: it
--   contains the runtime evaluation recursion plus thin wrappers over that
--   recursion, and nothing else. Name/open/lexical resolution, parameter-
--   pattern binding, pure sequence-builtin computations, and argument-shape
--   helpers are total definitions outside the evaluator cycle. Shrinking the
--   block further means touching genuine evaluation recursion, so treat any
--   future reduction as a semantic refactor (for example counted/non-counted
--   unification or a fuel-indexed total evaluator), not an extraction cleanup.

universe u v

namespace KatLang

--------------------------------------------------------------------------------
-- Typed identifiers (lightweight aliases for future-proofing)
--------------------------------------------------------------------------------

abbrev Ident := String    -- algorithm / property / parameter names
abbrev Assoc (K V : Type) := List (Prod K V)  -- association list

/-- How a parameter capture binds its one supplied slot. `meta` (CallReference S1,
    October 2026) is the META modifier `meta name`: the capture binds a run-scoped
    reference to the SUPPLIED CALL's invocation plan (`Result.callRef`, `NeedPattern.meta`)
    instead of the call's cell. It is a FIXED, non-collecting capture — one slot, like
    `normal` — and is valid only as a unique top-level capture of an explicitly written
    ordinary parameter list (`ParameterPattern.metaViolation?`). C#: `ParameterKind.Meta`. -/
inductive ParameterKind where
  | normal
  | collecting
  | metaRef
  deriving Repr, DecidableEq

/-- `==` on parameter kinds IS decidable equality (a lawful `BEq`), so proofs decide kind
    comparisons by constructor disequality. -/
instance : BEq ParameterKind := instBEqOfDecidableEq

structure CallableParameter where
  name : Ident
  kind : ParameterKind := .normal
  deriving Repr, BEq

/-- A parameter pattern of the ORDINARY pattern language: a capture, or a
    structural pattern whose delimiter selects the value kind it destructures —
    `sequenceValue` is the parenthesized sequence pattern `(p1, …, pn)`, which
    opens SEQUENCE values only, and `listValue` is the bracketed list pattern
    `[p1, …, pn]`, which opens LIST values only (see the file header, Structural
    patterns).

    `unpacking` is NOT written syntax: it is the UNPACKING RECEIVER of assignment
    deconstruction (`x, *rest, z = RHS`), which the front end elaborates into one
    per-target helper whose single parameter pattern is `unpacking [targets]`,
    applied to the hoisted right-hand side. It binds its target list against the
    ONE-LEVEL items of the supplied value — a sequence or a list opens one level,
    and any other value is one item (`Result.spreadItems`) — so a lone structure
    of either kind is split while a scalar is one target's value
    (`x, *rest = 1` binds `rest = []`). It has no delimiter that could select a
    value kind, so it opens both kinds alike; the kind-specific structural
    patterns never do. (The algebra's `CoreArityAlgebra.bindDeconstruct` /
    `openLoneStructure` is this receiver.) The right-hand side is demanded as an
    ORDINARY value, so a right-hand side without output is its own missing-output
    failure — never a spread failure.
    C#: `CaptureParameterPattern` / `SequenceValueParameterPattern` /
    `ListValueParameterPattern` / `UnpackingParameterPattern`. -/
inductive ParameterPattern where
  | capture : CallableParameter -> ParameterPattern
  | sequenceValue : List ParameterPattern -> ParameterPattern
  | listValue : List ParameterPattern -> ParameterPattern
  | unpacking : List ParameterPattern -> ParameterPattern
  deriving Repr, BEq

structure CallableSignature where
  name : Ident
  parameters : List CallableParameter
  deriving Repr, BEq

def CallableParameter.displayName (parameter : CallableParameter) : String :=
  match parameter.kind with
  | .normal => parameter.name
  | .collecting => "*" ++ parameter.name
  | .metaRef => "meta " ++ parameter.name

namespace ParameterPattern
  mutual
    /-- The captures of a pattern, left to right at every depth, repeated names and capture
        kinds kept (structural recursion; R3′, October 2026: `capturesOfList items` is
        `items.flatMap captures`, `PatternHelpers.capturesOfList_eq_flatMap`). -/
    def captures : ParameterPattern -> List CallableParameter
      | .capture parameter => [parameter]
      | .sequenceValue items => capturesOfList items
      | .listValue items => capturesOfList items
      | .unpacking items => capturesOfList items

    /-- The captures of a pattern list, in order: `items.flatMap captures`. -/
    def capturesOfList : List ParameterPattern -> List CallableParameter
      | [] => []
      | item :: rest => captures item ++ capturesOfList rest
  end

  def fromParameters (parameters : List CallableParameter) : List ParameterPattern :=
    parameters.map .capture

  def normalPatterns (ps : List Ident) : List ParameterPattern :=
    ps.map (fun p => .capture { name := p })

  /-- Whether a pattern is a structural pattern — a sequence pattern `(…)`, a
      list pattern `[…]`, or the deconstruction unpacking receiver — rather than
      a capture. -/
  def isStructural : ParameterPattern -> Bool
    | .capture _ => false
    | .sequenceValue _ => true
    | .listValue _ => true
    | .unpacking _ => true

  def hasStructured (patterns : List ParameterPattern) : Bool :=
    patterns.any isStructural

  /-- True when the pattern list itself contains a collecting binding (nested
      captures inside structural patterns do not count).
      C#: `ParameterPattern.HasCollectingCaptureAtCurrentLevel`. -/
  def hasCollectingCaptureAtCurrentLevel (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .capture parameter => parameter.kind == ParameterKind.collecting
      | _ => false)

  /-- The MINIMUM number of supplied argument slots a parameter-pattern list
      accepts — the ONE rule the binder enforces, factored out so no other layer can
      re-derive it (the Model-C binder reads the same count over need patterns,
      `needMinimumSuppliedSlots` in `bindNeedLevel`, which EQUALS this one whenever a
      level holds at most one collector — every signature the X-02 gate admits —
      by the theorem `binder_minimum_is_the_signature_minimum`, `KatLangArityLaws.lean`):

      * every pattern consumes exactly ONE supplied slot, whatever it contains —
        a structural pattern (sequence or list) is one slot that the binder
        opens afterwards, so nested structure never changes the count at this
        level;
      * a collecting capture at THIS level consumes NONE: it collects whatever
        slots are left over after the fixed prefix and suffix bind, and an empty
        leftover is the exact empty list (`collectSegment [] = []`).

      So `Only(*xs)` accepts zero supplied slots, while `Head(x, *rest)`,
      `Tail(*rest, z)`, `P((x, *rest))` and `Pair(x, y)` each require at least
      one. A list with two collecting captures is a rejected signature, never a
      lower minimum. C#: `ParameterPattern.MinimumSuppliedSlots`. -/
  def minimumSuppliedSlots (patterns : List ParameterPattern) : Nat :=
    if hasCollectingCaptureAtCurrentLevel patterns then patterns.length - 1 else patterns.length

  def topLevelCaptureKind? (name : Ident) : List ParameterPattern -> Option ParameterKind
    | [] => none
    | .capture parameter :: rest =>
        if parameter.name = name then some parameter.kind else topLevelCaptureKind? name rest
    | .sequenceValue _ :: rest => topLevelCaptureKind? name rest
    | .listValue _ :: rest => topLevelCaptureKind? name rest
    | .unpacking _ :: rest => topLevelCaptureKind? name rest

  mutual
    /-- The written form of a pattern, for diagnostics: `x`, `*xs`, `(x, y)`,
        `[x, *rest]`, and a deconstruction's written target list `x, *rest`.
        C#: `ParameterPattern.DisplayName`. -/
    def displayName : ParameterPattern -> String
      | .capture parameter => parameter.displayName
      | .sequenceValue items => "(" ++ String.intercalate ", " (displayNames items) ++ ")"
      | .listValue items => "[" ++ String.intercalate ", " (displayNames items) ++ "]"
      | .unpacking items => String.intercalate ", " (displayNames items)

    /-- The written forms of a pattern list, in order: `items.map displayName` (structural
        recursion; R3′, `PatternHelpers.displayNames_eq_map`). -/
    def displayNames : List ParameterPattern -> List String
      | [] => []
      | item :: rest => displayName item :: displayNames rest
  end

  /-- THE SINGLETON RULE (September 2026): a sequence pattern whose items are
      exactly ONE non-collecting pattern describes a one-item sequence boundary,
      and KatLang has no one-item sequence value (`Result.normalize` collapses
      it), so no value could ever match it. `(x)`, `((x, y))` and `([x])` are
      therefore invalid, while the collector-only `(*xs)` is valid: a collector
      is variadic and stands for a sequence's elements, not for a sequence of
      one. A list pattern has no such rule — lists keep every cardinality, so
      `[x]` is the one-element structural pattern.
      C#: `ParameterPattern.IsSingletonSequenceItems`. -/
  def isSingletonSequenceItems : List ParameterPattern -> Bool
    | [.capture parameter] =>
        match parameter.kind with
        | .normal => true
        | .collecting => false
        | .metaRef => true
    | [.sequenceValue _] => true
    | [.listValue _] => true
    | [.unpacking _] => true
    | _ => false

  mutual
    /-- Whether a pattern contains an invalid singleton sequence pattern at any
        depth (the singleton rule above). -/
    def hasSingletonSequenceGroup : ParameterPattern -> Bool
      | .capture _ => false
      | .sequenceValue items => isSingletonSequenceItems items || anyHasSingletonSequenceGroup items
      | .listValue items => anyHasSingletonSequenceGroup items
      | .unpacking items => anyHasSingletonSequenceGroup items

    /-- Whether any pattern of a list contains an invalid singleton sequence
        pattern at any depth. -/
    def anyHasSingletonSequenceGroup : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => hasSingletonSequenceGroup pattern || anyHasSingletonSequenceGroup rest
  end

  /-- The number of collecting captures at ONE pattern level; captures nested
      inside a structural pattern belong to that pattern's own level. -/
  def collectingCaptureCountAtCurrentLevel : List ParameterPattern -> Nat
    | [] => 0
    | .capture parameter :: rest =>
        (if parameter.kind == ParameterKind.collecting then 1 else 0)
          + collectingCaptureCountAtCurrentLevel rest
    | .sequenceValue _ :: rest => collectingCaptureCountAtCurrentLevel rest
    | .listValue _ :: rest => collectingCaptureCountAtCurrentLevel rest
    | .unpacking _ :: rest => collectingCaptureCountAtCurrentLevel rest

  mutual
    /-- Whether some pattern level NESTED in a pattern holds more than one
        collecting capture. -/
    def hasMultipleCollectingLevel : ParameterPattern -> Bool
      | .capture _ => false
      | .sequenceValue items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items
      | .listValue items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items
      | .unpacking items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items

    /-- Whether some pattern level nested in any pattern of a list holds more
        than one collecting capture. -/
    def anyHasMultipleCollectingLevel : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => hasMultipleCollectingLevel pattern || anyHasMultipleCollectingLevel rest
  end

  /-- AT MOST ONE COLLECTING CAPTURE PER PATTERN LEVEL: whether a pattern list,
      or some level nested in it, holds more than one. The binder allocates a
      level's supply around ONE collector, the level's first (`needLevelSources`), so a
      second collector at the same level leaves the allocation undefined: such a list is
      a rejected signature, never a lower minimum (`minimumSuppliedSlots`).
      C#: `ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel`. -/
  def hasMultipleCollectingCapturesAtAnyLevel (patterns : List ParameterPattern) : Bool :=
    1 < collectingCaptureCountAtCurrentLevel patterns || anyHasMultipleCollectingLevel patterns

  mutual
    /-- The names of the COLLECTING captures of a pattern, at any depth, left to
        right. Total (unlike `captures`), so the validity laws evaluate. -/
    def collectingNames : ParameterPattern -> List Ident
      | .capture parameter => if parameter.kind == ParameterKind.collecting then [parameter.name] else []
      | .sequenceValue items => anyCollectingNames items
      | .listValue items => anyCollectingNames items
      | .unpacking items => anyCollectingNames items

    def anyCollectingNames : List ParameterPattern -> List Ident
      | [] => []
      | pattern :: rest => collectingNames pattern ++ anyCollectingNames rest
  end

  mutual
    /-- How many captures of a pattern bind `name`, at any depth. -/
    def nameOccurrences (name : Ident) : ParameterPattern -> Nat
      | .capture parameter => if parameter.name == name then 1 else 0
      | .sequenceValue items => anyNameOccurrences name items
      | .listValue items => anyNameOccurrences name items
      | .unpacking items => anyNameOccurrences name items

    def anyNameOccurrences (name : Ident) : List ParameterPattern -> Nat
      | [] => 0
      | pattern :: rest => nameOccurrences name pattern + anyNameOccurrences name rest
  end

  /-- Whether a repeated capture name includes a collecting binding: a written
      head may repeat a name only among fixed captures (Q-05's constraints), never
      with a collector. C#: `ParameterPattern.HasRepeatedCaptureNameIncludingCollecting`. -/
  def hasRepeatedCaptureNameIncludingCollecting (patterns : List ParameterPattern) : Bool :=
    (anyCollectingNames patterns).any (fun name => 2 ≤ anyNameOccurrences name patterns)

  /-- The rule a parameter-pattern list breaks as a callable SIGNATURE, in rule
      order. C#: `ParameterSignatureViolation`. -/
  inductive SignatureViolation where
    | singletonSequencePattern
    | multipleCollectingAtOneLevel
    | repeatedNameIncludesCollecting
    deriving Repr, DecidableEq, BEq

  /-- THE STRUCTURAL VALIDITY OF A SIGNATURE (X-02, September 30 2026): the first
      rule a parameter-pattern list breaks as a callable signature, or `none` for
      a valid one — no one-item sequence pattern at any depth (the singleton
      rule), at most one collecting capture per pattern level, and no repeated
      name that includes a collecting binding. These are exactly the rules a
      WRITTEN parameter list is held to, and the C# front end holds every
      INFERRED signature to them too: formula lifting that would compose an
      invalid contract (`C1(a, *p)`, `C2(b, *q)`, `K = C1 + C2` would give
      `K(a, *p, b, *q)`) is the definition's front-end error, never a signature
      that reaches a binder. A collecting name two callees share is ONE binding
      (`K(a, *rest, b)` is valid), and a collector nested in its own group is its
      group's level. C#: `ParameterPattern.FindSignatureViolation`. -/
  def signatureViolation? (patterns : List ParameterPattern) : Option SignatureViolation :=
    if anyHasSingletonSequenceGroup patterns then some .singletonSequencePattern
    else if hasMultipleCollectingCapturesAtAnyLevel patterns then some .multipleCollectingAtOneLevel
    else if hasRepeatedCaptureNameIncludingCollecting patterns then some .repeatedNameIncludesCollecting
    else none

  mutual
    /-- Whether a META capture occurs anywhere INSIDE a structural pattern. -/
    def hasNestedMeta : ParameterPattern -> Bool
      | .capture _ => false
      | .sequenceValue items => anyHasMetaCapture items
      | .listValue items => anyHasMetaCapture items
      | .unpacking items => anyHasMetaCapture items

    /-- Whether a META capture occurs anywhere in a pattern list, at any depth. -/
    def anyHasMetaCapture : List ParameterPattern -> Bool
      | [] => false
      | .capture parameter :: rest => parameter.kind == ParameterKind.metaRef || anyHasMetaCapture rest
      | pattern :: rest => hasNestedMeta pattern || anyHasMetaCapture rest
  end

  /-- The names of the TOP-LEVEL META captures of a pattern list, in written order. -/
  def topLevelMetaNames (patterns : List ParameterPattern) : List Ident :=
    patterns.filterMap fun
      | .capture parameter => if parameter.kind == ParameterKind.metaRef then some parameter.name else none
      | _ => none

  /-- THE META PLACEMENT RULE (CallReference S1, October 2026): `meta` may modify only a
      TOP-LEVEL capture of a parameter list whose name occurs ONCE in that list — never a
      capture inside a sequence, list or unpacking pattern, and never a repeated name. A
      META capture is fixed by construction (`ParameterKind.metaRef` is not `collecting`). Clause
      families cannot carry META at all: Lean's clause binder `Pattern.bind` has no kind, and
      the C# front end and preflight reject a META clause binder. `none` for a valid list.
      C#: `ParameterPattern.FindMetaViolation`. -/
  def metaViolation? (patterns : List ParameterPattern) : Option Ident :=
    match patterns.find? hasNestedMeta with
    | some pattern => some pattern.displayName
    | none => (topLevelMetaNames patterns).find? (fun name => 2 ≤ anyNameOccurrences name patterns)
end ParameterPattern

def callableParameterNameStartChar (c : Char) : Bool :=
  c == '_' || c.isAlpha

def callableParameterNameRestChar (c : Char) : Bool :=
  c == '_' || c.isAlphanum

def callableParameterNameIsIdentifierLike (name : Ident) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      callableParameterNameStartChar first && rest.all callableParameterNameRestChar

def CallableSignature.collectingCount (signature : CallableSignature) : Nat :=
  (signature.parameters.filter (fun parameter => parameter.kind == ParameterKind.collecting)).length

def CallableSignature.hasAtMostOneCollecting (signature : CallableSignature) : Bool :=
  signature.collectingCount <= 1

def CallableSignature.emptyParameterName? (signature : CallableSignature) : Bool :=
  signature.parameters.any (fun parameter => parameter.name == "")

def CallableSignature.invalidParameterName? (signature : CallableSignature) : Option Ident :=
  (signature.parameters.find? fun parameter =>
    parameter.name != "" && !callableParameterNameIsIdentifierLike parameter.name).map (fun parameter => parameter.name)

def CallableSignature.duplicateParameterName? (signature : CallableSignature) : Option Ident :=
  let rec go : List Ident -> List CallableParameter -> Option Ident
    | _, [] => none
    | seen, parameter :: rest =>
        if seen.contains parameter.name then
          some parameter.name
        else
          go (parameter.name :: seen) rest
  go [] signature.parameters

/-- The validity of callable SIGNATURE METADATA, with its message: at most one collecting
    parameter, and no empty, non-identifier-shaped or duplicate parameter name. It is part of no
    binder and no evaluation path calls it (the Model-C binder reads parameter PATTERNS, whose
    validity is X-02's `ParameterPattern.signatureViolation?`). C#: `CallableSignature.ValidateMessage`
    (with `Validate` / `ValidateOrThrow`), which the builtin registry applies to every builtin
    signature at registration; pinned by `CoreTests.CallableSignatures`. -/
def CallableSignature.validationError? (signature : CallableSignature) : Option String :=
  if !signature.hasAtMostOneCollecting then
    some s!"Callable signature `{signature.name}` cannot contain more than one collecting parameter."
  else if signature.emptyParameterName? then
    some s!"Callable signature `{signature.name}` contains an empty parameter name."
  else
    match signature.invalidParameterName? with
    | some parameterName =>
        some s!"Callable signature `{signature.name}` contains invalid parameter name `{parameterName}`."
    | none =>
        match signature.duplicateParameterName? with
        | some parameterName =>
            some s!"Callable signature `{signature.name}` contains duplicate parameter name `{parameterName}`."
        | none => none

def CallableSignature.collectingIndex? (signature : CallableSignature) : Option Nat :=
  let rec go : Nat -> List CallableParameter -> Option Nat
    | _, [] => none
    | index, parameter :: rest =>
        match parameter.kind with
        | .collecting => some index
        | .normal | .metaRef => go (index + 1) rest
  go 0 signature.parameters

def CallableSignature.requiredNormalParameterCount (signature : CallableSignature) : Nat :=
  (signature.parameters.filter (fun parameter => parameter.kind != ParameterKind.collecting)).length

def CallableSignature.acceptsItemCount (signature : CallableSignature) (count : Nat) : Bool :=
  -- A collecting user signature consumes an item supply: it accepts at least
  -- the fixed (non-collecting) count. Fixed signatures, including collection
  -- builtins, stay exact.
  match signature.collectingIndex? with
  | some _ => count >= signature.requiredNormalParameterCount
  | none => count == signature.parameters.length

/-- Exposure classification of a `PropDef`: an INPUT to lookup, computed by the C# front
    end and never derived here. SELECTION never depends on it: `open` selects public
    members and structural dot access selects declared members; whether the selected
    member may be USED at an access site is `memberAccessible?`, decided after selection.
    `.localCapturedAncestorParams required`: the value requires the inputs `required`,
    which only an enclosing owner's call binds (a parameter, or a conditional branch's
    pattern binder) — the member is LOCAL-CONTEXT-DEPENDENT, usable from every lexical
    context inside the owner of each required name and refused everywhere else, never
    universally hidden. `.localConditional` is the family-level reason a name access
    into a conditional's branch bodies is refused (`conditionalBranchesDefineProperty`);
    the front end never assigns it to a `PropDef` — a branch's own declarations classify
    exactly like declarations in any other body. -/
inductive PropExposure where
  | exported
  | localCapturedAncestorParams (required : List Ident)
  | localConditional
  deriving Repr, DecidableEq

namespace PropExposure
  def isExported : PropExposure -> Bool
    | .exported => true
    | _ => false
end PropExposure

--------------------------------------------------------------------------------
-- Errors / Monad
--------------------------------------------------------------------------------

/-- WHOSE missing output a `missingOutput` failure is (Q-36, decided 2026-10-24). It is raised
    `own` by the output check of the computation being demanded — the body without written
    output; once that failure leaves a SUBORDINATE computation of another one (an output row of a
    body or capture, an operand of an operator or constructor, a builtin's argument or callback,
    an argument inspected while binding, a `.string` receiver) it is `nested`
    (`Error.nestMissingOutput`, `withNestedMissingOutput`). It is part of the COMPLETED outcome,
    so it survives every memo — a property's cached outcome, a need cell's completed outcome — and
    is consumer-independent. Only the spread reads it: the spread operand's `own` missing output
    is `spreadMissingOutput`, a `nested` one is preserved (`spreadOperandFailure`). The public
    category of both is `missingOutput`. C#: `EvalError.MissingOutput.IsNested`. -/
inductive MissingOutputOrigin where
  | own
  | nested
  deriving Repr, DecidableEq

inductive Error where
  | unknownName      : Ident -> Error
  | unknownProperty  : String -> Ident -> Error        -- object desc, property name
  | notPublicProperty : String -> Ident -> Error       -- object desc, property name (exists but private)
  | localOnlyProperty : String -> Ident -> PropExposure -> Error  -- object desc, property name, reason
  | notAnAlgorithm   : String -> Error          -- an invoking position received no callable identity (Q-06)
  | illegalInOpen    : String -> Error                -- semantic restriction (e.g., builtin not allowed)
  | badOpenForm      : String -> Error                -- syntactic form not allowed in open
  | illegalInEval    : String -> Error                -- a value outside the operation's domain (Q-27), or not evaluable
  | ambiguousOpen    : Ident -> List String -> Error   -- name, providers
  | arityMismatch    : Nat -> Nat -> Error     -- supply cardinality: expected, actual
  | badArity         : Error                   -- supply/output cardinality without a count (Q-27)
  | typeMismatch     : String -> Error          -- a present value of the wrong kind (Q-27)
  | badIndex         : Error                   -- a selection names no position (first/last included)
  | divByZero        : Error                   -- division or modulo by zero
  | demandCycle      : Error                   -- a VALUE demand re-enters its evaluating cell
  | noMatchingBranch : Ident -> Error          -- conditional algorithm: no branch matched
  | branchArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchArities)
  | branchOutputArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level output arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchOutputArities)
  | duplicateProperty : Ident -> Error         -- algorithm defines the same property name more than once
  | duplicateBranchPattern : Error             -- conditional algorithm has match-equivalent branch patterns
  | explicitParamsRequireOutput : Error        -- explicit algorithm params require an algorithm output
  | missingOutput    : MissingOutputOrigin -> Error  -- forced user-defined algorithm does not define output (origin: Q-36)
  | spreadMissingOutput : Error          -- the spread operand's OWN output is missing (Q-36)
  | unresolvedImplicitParams : List Ident -> Error  -- top-level block has unresolved implicit parameters
  | withContext      : String -> Error -> Error -- contextual wrapper
  /-- R7: the INCOMPLETE outcome of the fuel-indexed evaluator core (`evalFuel`) — the formal
      computation ran out of its proof index before completing. It is not a language error and
      no C# error kind corresponds to it. No ordinary probe catches it (`evalAttempt`,
      `tryCatch`), so an incomplete computation is not published as a VALUE, CALLABLE, plan
      or property-cache outcome. Compiled production retries incomplete attempts; a completed
      production run does not return this sentinel. The kernel-level default for noncompletion
      in `evalUnbounded` is nevertheless this constructor with the entry state: this encoding
      is an open R7 representation decision, not a proved public nontermination/error boundary. -/
  | fuelExhausted    : Error
  deriving Repr

-- * IMPORTANT: Needed for compiling `partial` definitions.
-- Lean requires `Nonempty` for the function types of partial defs.
instance : Nonempty Error := Nonempty.intro Error.badArity

/-- `CallableSignature.validationError?` as an evaluation error (`illegalInEval`), the shape
    the C# `CallableSignature.Validate` reports. -/
def CallableSignature.validate (signature : CallableSignature) : Except Error Unit :=
  match signature.validationError? with
  | some message => .error (Error.illegalInEval message)
  | none => .ok ()

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

/-- The binary operators: arithmetic (numeric scalar operands, numeric result)
    and the logical operators (Boolean operands, Boolean result). The six
    comparison operators are NOT binary operators — they are the links of a
    comparison chain (`ComparisonOp`, `Expr.comparison`). C#: `BinaryOp`. -/
inductive BinaryOp where
  | add | sub | mul | div | idiv | mod | pow
  | and | or | xor
  deriving Repr, BEq, DecidableEq

def BinaryOp.symbol : BinaryOp -> String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .idiv => "div"
  | .mod => "mod"
  | .pow => "^"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"

/-- The six comparison operators of the ONE comparison precedence tier. The
    ordering comparisons `lt`/`gt`/`le`/`ge` take numeric scalar operands;
    `eq`/`ne` are total structural equality over every value kind. Every
    comparison yields a Boolean value, and unparenthesized comparisons at one
    syntactic level form one `Expr.comparison` chain. C#: `ComparisonOp`. -/
inductive ComparisonOp where
  | lt | gt | le | ge | eq | ne
  deriving Repr, BEq, DecidableEq

def ComparisonOp.symbol : ComparisonOp -> String
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .eq => "=="
  | .ne => "!="

inductive UnaryOp where
  | minus | not
  deriving Repr

inductive Builtin where
  | ifBuiltin | whileBuiltin | repeatBuiltin | atomsBuiltin | rangeBuiltin | filterBuiltin | mapBuiltin | orderBuiltin | orderDescBuiltin | countBuiltin | containsBuiltin | firstBuiltin | lastBuiltin | distinctBuiltin | takeBuiltin | skipBuiltin | minBuiltin | maxBuiltin | sumBuiltin | avgBuiltin | reduceBuiltin
  deriving Repr, BEq, DecidableEq

inductive SequenceBuiltinSuffixArgKind where
  | algorithm
  | value
  | wholeNumber
  deriving Repr, BEq, DecidableEq

structure SequenceBuiltinSuffixArgDescriptor where
  name : Ident
  kind : SequenceBuiltinSuffixArgKind := .algorithm
  deriving Repr, BEq

/-- What a collection builtin does with an EMPTY one-level collection view
    (Q-27): an ordinary input (`allowEmpty`), outside an aggregate's domain
    (`requireAnyItem`, `illegalInEval` — `min`, `max`, `avg`), or a SELECTION
    that has no position to select (`requireSelectablePosition`, `badIndex` —
    `first`, `last`, exactly as `collection[0]`, SEQ-04).
    C#: `SequenceBuiltinEmptyPolicy`. -/
inductive SequenceBuiltinEmptyPolicy where
  | allowEmpty
  | requireAnyItem
  | requireSelectablePosition
  deriving Repr, BEq, DecidableEq

inductive SequenceBuiltinItemShapeConstraint where
  | any
  | singleNumeric
  deriving Repr, BEq, DecidableEq

structure SequenceBuiltinMetadata where
  suffixArgs : List SequenceBuiltinSuffixArgDescriptor := []
  emptyPolicy : SequenceBuiltinEmptyPolicy := .allowEmpty
  itemShapeConstraint : SequenceBuiltinItemShapeConstraint := .any
  deriving Repr, BEq

def SequenceBuiltinMetadata.parameters (metadata : SequenceBuiltinMetadata) : List CallableParameter :=
  { name := "collection" } ::
    metadata.suffixArgs.map (fun descriptor => { name := descriptor.name })

def SequenceBuiltinMetadata.signature (builtinName : Ident) (metadata : SequenceBuiltinMetadata)
    : CallableSignature :=
  { name := builtinName, parameters := metadata.parameters }

/-- Metadata for collection builtins.
  A collection builtin is an ordinary fixed-arity native callable: exactly one
  fixed `collection` parameter followed by its fixed control parameters
  (`count(collection)`, `take(collection, count)`). The bound collection value
  is interpreted through the one-level builtin collection view only AFTER
  binding; argument boundaries are never altered before binding. `suffixArgs`
  describes the fixed control arguments that follow the collection. -/
def sequenceBuiltinMetadata? : Builtin -> Option SequenceBuiltinMetadata
  | .filterBuiltin => some {
      suffixArgs := [{ name := "predicate" }]
    }
  | .mapBuiltin => some {
      suffixArgs := [{ name := "mapper" }]
    }
  | .orderBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .orderDescBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .countBuiltin => some {
    }
  | .containsBuiltin => some {
      suffixArgs := [{ name := "item", kind := .value }]
    }
  | .firstBuiltin => some {
      emptyPolicy := .requireSelectablePosition
    }
  | .lastBuiltin => some {
      emptyPolicy := .requireSelectablePosition
    }
  | .distinctBuiltin => some {
    }
  | .takeBuiltin => some {
      suffixArgs := [{ name := "count", kind := .wholeNumber }]
    }
  | .skipBuiltin => some {
      suffixArgs := [{ name := "count", kind := .wholeNumber }]
    }
  | .minBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .maxBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .sumBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .avgBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .reduceBuiltin => some {
      -- The reducer is a callback the builtin INVOKES; the initial accumulator is
      -- an ordinary VALUE, demanded once (HO-04).
      suffixArgs := [
        { name := "reducer" },
        { name := "initial", kind := .value }
      ]
    }
  | _ => none

/-- What one supplied item position of a collection builtin IS to the builtin's
    argument adapter, decided by the metadata alone (CALL-03):
    - `value`: the `collection` (position 0) or a `.value` / `.wholeNumber`
      control. Demanded ONCE for its value; that outcome — one value or one
      failure — is final for the call.
    - `callback`: an `.algorithm` control (the `filter` predicate, the `map`
      mapper, the `reduce` reducer). It carries its algorithm, and the builtin
      INVOKES it per element; supplying it evaluates nothing.
    - `surplus`: a position beyond the fixed signature. Supplying it makes the
      call an arity error.
    A spread slot is not a position: it is supply assembly, and each of its items
    takes the role of the position it lands on. -/
inductive SequenceBuiltinSlotRole where
  | value
  | callback
  | surplus
  deriving Repr, BEq, DecidableEq

def SequenceBuiltinMetadata.slotRole (metadata : SequenceBuiltinMetadata) (slot : Nat)
    : SequenceBuiltinSlotRole :=
  if slot == 0 then .value
  else match metadata.suffixArgs[slot - 1]? with
    | some descriptor => if descriptor.kind == .algorithm then .callback else .value
    | none => .surplus

private def sequenceBuiltinTotalArgCountDesc
    (signature : CallableSignature) : String :=
  if signature.collectingIndex?.isSome then
    let minimum := signature.requiredNormalParameterCount
    if minimum = 0 then "any number of" else s!"at least {minimum}"
  else
    toString signature.parameters.length

def builtinDisplayName : Builtin -> String
  | .ifBuiltin => "if"
  | .whileBuiltin => "while"
  | .repeatBuiltin => "repeat"
  | .atomsBuiltin => "atoms"
  | .rangeBuiltin => "range"
  | .filterBuiltin => "filter"
  | .mapBuiltin => "map"
  | .orderBuiltin => "order"
  | .orderDescBuiltin => "orderDesc"
  | .countBuiltin => "count"
  | .containsBuiltin => "contains"
  | .firstBuiltin => "first"
  | .lastBuiltin => "last"
  | .distinctBuiltin => "distinct"
  | .takeBuiltin => "take"
  | .skipBuiltin => "skip"
  | .minBuiltin => "min"
  | .maxBuiltin => "max"
  | .sumBuiltin => "sum"
  | .avgBuiltin => "avg"
  | .reduceBuiltin => "reduce"

/-- THE ONE AUTHORITATIVE BUILTIN SIGNATURE (META-S3-3, October 2026): a builtin's ordinary
    parameter patterns, read by its runtime arity (`builtinAcceptsArity`), the META binding of
    a builtin that declares a `meta` parameter (`applyBuiltinCounted`, through the ONE
    binder `bindNeedPatterns`), formula lifting and forwarding (`builtinLiftingSignature`) and
    the lifting roles (`builtinLiftingSlotRole`). Every builtin is an ordinary FIXED-arity
    callable: a collection builtin's registry parameters, `if`'s three, `atoms`' value,
    `range`'s bounds, and the loops `while(meta step)` / `repeat(meta step, count)`, whose
    step is a genuine META parameter (D1): the captured call's own supply is the loop's
    initial state, so there is no variadic `*init` (D2). C#: `BuiltinDescriptor.PlainSignature`. -/
def builtinSignature (b : Builtin) : List ParameterPattern :=
  let fixed (names : List Ident) := names.map (fun name => ParameterPattern.capture { name := name })
  match sequenceBuiltinMetadata? b with
  | some metadata => metadata.parameters.map ParameterPattern.capture
  | none =>
      match b with
      | .ifBuiltin => fixed ["condition", "whenTrue", "whenFalse"]
      | .whileBuiltin => [.capture { name := "step", kind := .metaRef }]
      | .repeatBuiltin => [.capture { name := "step", kind := .metaRef }] ++ fixed ["count"]
      | .atomsBuiltin => fixed ["value"]
      | .rangeBuiltin => fixed ["start", "stop"]
      | _ => []

/-- Whether a builtin's signature declares a META parameter (META-S3-3): such a builtin binds
    its supplied cells through the ONE inspecting binder before its native arm runs
    (`applyBuiltinCounted`). C#: `BuiltinDescriptor.DeclaresMetaParameter`. -/
def builtinDeclaresMeta (b : Builtin) : Bool :=
  ParameterPattern.anyHasMetaCapture (builtinSignature b)

/-- Whether supplied position `position` of a builtin is one of its META parameters (the
    lifting role table reads it: a META position transports its cell, `builtinLiftingSlotRole`).
    C#: `BuiltinDescriptor.IsMetaPosition`. -/
def builtinMetaAt (b : Builtin) (position : Nat) : Bool :=
  match (builtinSignature b)[position]? with
  | some (.capture parameter) => parameter.kind == .metaRef
  | _ => false

/-- The exact arity gate of every builtin, read from THE signature that its binder and
    lifting use. Every builtin parameter is fixed, including META parameters. C#:
    `BuiltinDescriptor.AcceptsArity` (whose fixed arity is checked against its signature). -/
def builtinAcceptsArity (b : Builtin) (n : Nat) : Bool :=
  n == (builtinSignature b).length

/-- Human-readable expected arity string for error messages. -/
def builtinArityDesc : Builtin -> String
  | b =>
      match sequenceBuiltinMetadata? b with
      | some metadata =>
          let signature := metadata.signature (builtinDisplayName b)
          let totalArgCountDesc :=
            sequenceBuiltinTotalArgCountDesc signature
          if metadata.suffixArgs.isEmpty then
            totalArgCountDesc
          else
            let parameters := String.intercalate ", " (signature.parameters.map CallableParameter.displayName)
            s!"{totalArgCountDesc} arguments ({signature.name}({parameters}))"
      | none => toString (builtinSignature b).length

/-- The arity of the builtin (every builtin is fixed-arity, the loops too since META-S3-3):
    exactly the arity `builtinAcceptsArity` admits, the payload of `builtinArityError`. C#:
    `BuiltinDescriptor.ArityFacts.MinTopLevelArgumentCount`. -/
def builtinMinimumArity (b : Builtin) : Nat :=
  (builtinSignature b).length

def builtinArityError (b : Builtin) (actual : Nat) : Error :=
  -- The numeric payload is the builtin's real arity contract (Q-27 payload
  -- hygiene, formerly a placeholder 0 for every builtin but `if`), beside the
  -- descriptive `builtinArityDesc` context. Mirrors the C# `WrongBuiltinArity`.
  Error.withContext s!"expected {builtinArityDesc b} arguments"
    (Error.arityMismatch (builtinMinimumArity b) actual)

--------------------------------------------------------------------------------
-- Patterns (for clause heads and conditional algorithms)
--------------------------------------------------------------------------------

/-- Pattern language for clause heads and conditional algorithm branch matching.
    Recursive capture/structural patterns can elaborate to ordinary explicit
    parameter patterns. Conditional patterns match against Result values at
    call time.
    - `bind x`: matches any Result and binds it to name `x`
    - `litInt n`: matches only `Result.atom n`
    - `litBool b`: matches only `Result.bool b` (the reserved literals `true` /
      `false` in a clause head; a Boolean is never a number, so `F(1)` and
      `F(true)` are different clauses)
    - `sequenceValue ps` (a nested `(p1, …, pn)`): matches ONLY a
      `Result.sequenceValue rs` of the same length, each sub-pattern matching
      its element; never a list and never a scalar. `()` matches only the empty
      sequence value. A one-item `(p)` is invalid (the singleton rule,
      `headHasSingletonSequenceGroup`): no one-item sequence value exists.
    - `listValue ps` (`[p1, …, pn]`): matches ONLY a `Result.listValue rs` of
      the same length, each sub-pattern matching its element; never a sequence
      and never a scalar. `[]` matches only the empty list, `[p]` a one-element
      list.
    At the TOP of a clause head a `sequenceValue` is the head's own argument
    list (`F(x, y)` is `sequenceValue [bind x, bind y]`, `F((x, y))` is
    `sequenceValue [sequenceValue [bind x, bind y]]`, `F([x])` is
    `sequenceValue [listValue [bind x]]`), never a structural pattern.

    Patterns are a separate semantic type, distinct from Expr.
    They do not appear in executable expression positions.

    **Full-input-specification rule**: In a conditional algorithm, the branch
    pattern in `Name(...)` is the COMPLETE INPUT SPECIFICATION of that branch.
    - All branch inputs must appear in the pattern.
    - The branch's OWN level does NOT infer additional implicit parameters
      from free identifiers.  Only names bound by the pattern (plus ordinary
      lexical / property / open / builtin resolution) are available in the
      rows the branch writes.
    - Unused pattern-bound names are allowed.
    - Grace `~` is NOT permitted in patterns or on the branch's own level.
      Patterns contain only matching constructs (binders, literals, nested
      sequence and list patterns), and the branch's own rows have no inferred
      parameter ordering to apply Grace to.  Algorithms NESTED inside a branch
      body (brace blocks, properties, nested families' owners) are ordinary
      independent owners: an inferring one infers its own signature, and may
      use Grace on its own inferred parameters, in the C# front end before
      Lean encoding (Q-16 G-O); its parameters are supplied by its caller and
      are never added to the branch.

    This keeps conditional algorithms self-contained: branch selection and
    branch binding are the same operation, with no hidden remaining parameters
    and no interaction with Grace-based parameter reordering at the branch's
    own level. -/
inductive Pattern where
  | bind      : Ident -> Pattern
  | litInt    : Int -> Pattern
  | litString : String -> Pattern    -- matches only Result.str s (exact string equality)
  | litBool   : Bool -> Pattern      -- matches only Result.bool b (C#: Pattern.LitBool)
  | sequenceValue     : List Pattern -> Pattern   -- `(p1, …, pn)`: sequence values only (C#: Pattern.SequenceValue)
  | listValue         : List Pattern -> Pattern   -- `[p1, …, pn]`: list values only (C#: Pattern.ListValue)
  deriving Repr, BEq

namespace Pattern
  /-- Collect all binder names in a pattern (left-to-right). -/
  def boundNames : Pattern -> List Ident
    | .bind x      => [x]
    | .litInt _    => []
    | .litString _ => []
    | .litBool _   => []
    | .sequenceValue ps    => ps.flatMap boundNames
    | .listValue ps        => ps.flatMap boundNames

  mutual
    /-- THE SINGLETON RULE for the family pattern language (see
        `ParameterPattern.isSingletonSequenceItems`): a NESTED sequence pattern
        with exactly one item describes a one-item sequence, which no value is,
        so it is invalid. A family pattern has no collecting binder, so every
        one-item sequence pattern is a singleton. A list pattern `[p]` is valid. -/
    def hasSingletonSequenceGroup : Pattern -> Bool
      | .sequenceValue ps => ps.length == 1 || anyHasSingletonSequenceGroup ps
      | .listValue ps => anyHasSingletonSequenceGroup ps
      | .bind _ => false
      | .litInt _ => false
      | .litString _ => false
      | .litBool _ => false

    def anyHasSingletonSequenceGroup : List Pattern -> Bool
      | [] => false
      | p :: ps => hasSingletonSequenceGroup p || anyHasSingletonSequenceGroup ps
  end

  /-- The singleton rule over a whole clause HEAD: a top-level `sequenceValue`
      is the head's own argument list (the call's parentheses), never a
      structural pattern, so only the patterns inside it are checked; any other
      head is one argument position checked as a pattern. -/
  def headHasSingletonSequenceGroup : Pattern -> Bool
    | .sequenceValue ps => anyHasSingletonSequenceGroup ps
    | p => hasSingletonSequenceGroup p

  /-- Compute the top-level arity of a pattern.
      - `sequenceValue [p1, ..., pn] ⟹ n` (the head's own argument list)
      - any other pattern, a list pattern included  ⟹ 1

      This defines the outer call interface of a conditional algorithm branch.
      Conditional algorithms require a uniform top-level interface across branches:
      all branches of the same conditional algorithm must have the same
      top-level pattern arity.  Nested substructure may vary, but the outer
      number of inputs must remain consistent. -/
  def topLevelArity : Pattern -> Nat
    | .sequenceValue ps => ps.length
    | _         => 1

  /-- Return positional parameter names only for the strict flat multi-binder
      core subset: a top-level flat sequence-value pattern of multiple plain binders.

      This helper is intentionally narrower than the surface clause
      elaboration rule. It is kept for compatibility with manually constructed
      core `.conditional` values handled by evaluator fallback.

      Rejected on purpose:
      - bare single binders (`.bind x`)
      - any sequence-value pattern containing non-binders
      - any top-level arity-1 sequence-value pattern, including singleton binder forms

      Surface clause elaboration uses `plainClauseParamNames?` below, which
      additionally accepts bare single binders like `F(x) = ...`. -/
  def flatBinderParamNames? : Pattern -> Option (List Ident)
    | .sequenceValue ps =>
        if ps.length <= 1 then
          none
        else
          ps.mapM (fun
            | .bind x => some x
            | _ => none)
    | _ => none

  mutual
    /-- Return parameter names when a sole surface clause head consists only of
        recursive binder/structural (sequence or list) parameter patterns.

        This is only an eligibility helper for the whole same-name clause-group
        elaboration rule; it does not by itself decide ordinary-vs-conditional.

        Rejected on purpose:
        - literal or mixed non-binder pattern structure

        This is the ordinary clause-elaboration boundary: capture/structural-only
        recursive parameter patterns elaborate as ordinary algorithms, while
        literal or mixed patterns stay conditional. Each structural pattern keeps
        its kind: a sequence pattern stays a sequence pattern and a list pattern a
        list pattern. -/
    def parameterPattern? : Pattern -> Option ParameterPattern
      | .bind x => some (.capture { name := x })
      | .sequenceValue ps => do
          let patterns <- parameterPatternsOf? ps
          some (.sequenceValue patterns)
      | .listValue ps => do
          let patterns <- parameterPatternsOf? ps
          some (.listValue patterns)
      | _ => none

    /-- `ps.mapM parameterPattern?`, left to right, the first ineligible item ending the walk
        (structural recursion; R3′, `PatternHelpers.parameterPatternsOf?_eq_mapM`). -/
    def parameterPatternsOf? : List Pattern -> Option (List ParameterPattern)
      | [] => some []
      | p :: rest => do
          let pattern <- parameterPattern? p
          let patterns <- parameterPatternsOf? rest
          some (pattern :: patterns)
  end

  def plainClauseParameterPatterns? : Pattern -> Option (List ParameterPattern)
    | .bind x => some [.capture { name := x }]
    | .sequenceValue ps => parameterPatternsOf? ps
    | .listValue ps => (parameterPattern? (.listValue ps)).map (fun pattern => [pattern])
    | _ => none

  def plainClauseParamNames? : Pattern -> Option (List Ident)
    | p => (plainClauseParameterPatterns? p).map (fun patterns => (patterns.flatMap ParameterPattern.captures).map (fun parameter => parameter.name))

  /-- Check whether two patterns are match-equivalent. Binder spelling is
      irrelevant, but repeated-name equality positions must agree:
      - `bind _` ≡ `bind _` (any binder matches everything)
      - `litInt m` ≡ `litInt n` iff `m = n` (likewise `litString`, `litBool`)
      - `sequenceValue ps` ≡ `sequenceValue qs` iff same length and pairwise match-equivalent
      - `listValue ps` ≡ `listValue qs` iff same length and pairwise match-equivalent

      Used to detect duplicate branch patterns in conditional algorithms.

      Equivalence is structural, not extensional, and the structural KIND is part
      of the shape: a sequence pattern is never match-equivalent to a list
      pattern (`(x, y)` and `[a, b]`, `()` and `[]` match disjoint values), while
      renaming binders never makes two patterns of one shape distinct. -/
  def binderRenaming? (name : Ident) : List (Ident × Ident) -> Option Ident
    | [] => none
    | (left, right) :: rest =>
        if left = name then some right else binderRenaming? name rest

  def binderTargetUsed (name : Ident) : List (Ident × Ident) -> Bool
    | [] => false
    | (_, right) :: rest => right = name || binderTargetUsed name rest

  mutual
  def matchEquivalentWithRenaming : Pattern -> Pattern ->
      List (Ident × Ident) -> Option (List (Ident × Ident))
    | .bind left, .bind right, pairs =>
        match binderRenaming? left pairs with
        | some existing => if existing = right then some pairs else none
        | none =>
            if binderTargetUsed right pairs then none
            else some ((left, right) :: pairs)
    | .litInt m, .litInt n, pairs =>
        if m = n then some pairs else none
    | .litString s, .litString t, pairs =>
        if s = t then some pairs else none
    | .litBool b, .litBool c, pairs =>
        if b = c then some pairs else none
    | .sequenceValue ps, .sequenceValue qs, pairs =>
        if ps.length != qs.length then none else matchEquivalentPairsWithRenaming ps qs pairs
    | .listValue ps, .listValue qs, pairs =>
        if ps.length != qs.length then none else matchEquivalentPairsWithRenaming ps qs pairs
    | _, _, _ => none

  /-- The items of two equally long structural patterns compared in lockstep, left to right,
      threading the renaming table; the first non-equivalent pair ends the walk (structural
      recursion over the left items; R3′, October 2026 — the former local `go` over
      `ps.zip qs`, `PatternHelpers.matchEquivalentPairs_eq_foldlM_zip`). -/
  def matchEquivalentPairsWithRenaming : List Pattern -> List Pattern ->
      List (Ident × Ident) -> Option (List (Ident × Ident))
    | [], [], current => some current
    | p :: ps, q :: qs, current => do
        let next <- matchEquivalentWithRenaming p q current
        matchEquivalentPairsWithRenaming ps qs next
    | _, _, _ => none
  end

  /-- Pairwise match-equivalence of two structural patterns' items of ONE kind: unequal
      lengths are never equivalent, equal lengths compare in lockstep. It is the structural
      arm of `matchEquivalentWithRenaming` (`PatternHelpers.matchEquivalent_sequenceValue`,
      `PatternHelpers.matchEquivalent_listValue`). -/
  def matchEquivalentItemsWithRenaming (ps qs : List Pattern)
      (pairs : List (Ident × Ident)) : Option (List (Ident × Ident)) :=
    if ps.length != qs.length then none else matchEquivalentPairsWithRenaming ps qs pairs

  def isMatchEquivalent (left right : Pattern) : Bool :=
    (matchEquivalentWithRenaming left right []).isSome
end Pattern

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

/-- Declaration identity is independent of executable body equality. Ordinary
    tree declarations receive a fresh `syntax` identity once at run preparation.
    `shared` represents a host AST declaration reused at several syntax sites; encoders
    preserve that DECLARATION sharing explicitly. It does not by itself encode C#'s
    binding-plus-host-scope identity: C# also keys every ownerless host `ScopeCtx` level (the
    declaring level and every host ancestor, HOST-NESTED-1) by OBJECT reference, and Lean has
    no host-object token, so one `shared` id placed under two distinct C# host objects MERGES
    them here (guard 5b of `CoreTests/HostScopePropertyCache.lean`), while default `syntax`
    ids SPLIT one C# host object reached through several edges. A shared declaration is not
    a shared host owner; empty or opens-only host levels carry no declaration to hold an id
    at all. This deferred O-6 boundary also covers alias memos, NEED-04 callable identity and
    Q-19 open providers (SEMANTIC-ALIGNMENT.md, O6-DOCS).
    `module` marks the ONE declaration of a loaded module (Q-31 H-P + Q-32 I-U, decided
    2026-10-06): a hygienic source unit rooted at the prelude, so wherever it is reached it is
    wired under the chain's root level (`Algorithm.withParent`), never under its holder, and
    every holder reaches the one declaration in the one declaring scope. Lean has no loader;
    the encoder emits the mark for the C# tree's loaded-module roots (C#:
    `Algorithm.User.IsModuleElaborated`). -/
inductive PropertyIdentity where
  | syntax : Nat -> PropertyIdentity
  | shared : Nat -> PropertyIdentity
  | runtime : Nat -> PropertyIdentity
  | module : Nat -> PropertyIdentity
  deriving Repr, BEq

mutual
  inductive Expr where
    | param   : Ident -> Expr
    | num     : Int -> Expr
    | stringLiteral : String -> Expr  -- * string literal: first-class value (evaluates to Result.str)
    -- * interpolatedString: a double-quoted string WITH interpolation holes,
    --   `"head{h1}t1…{hn}tn"` (STR-02, VAL-12): the decoded head text and one
    --   link per hole (the hole and the decoded text written after it). A
    --   double-quoted string with no hole is an ordinary `stringLiteral`. Each
    --   hole is ONE ordinary expression of the enclosing algorithm in a VALUE
    --   role. Evaluation (`interpolateWith`): when the node's value is demanded,
    --   the holes are evaluated LEFT TO RIGHT, each EXACTLY ONCE, each value
    --   converted to its structural text (`Result.canonicalText`) as soon as it
    --   is available, and the first failure ends the node; the result is ONE
    --   `Result.str`. As a call argument the node is one suspended cell like any
    --   other expression. No callable identity. The lexing (quotes, escapes,
    --   `{{`/`}}`) and the hole-level restrictions are C#-only front-end rules.
    --   C#: `Expr.InterpolatedString`.
    | interpolatedString : String -> List InterpolationLink -> Expr
    -- * boolLiteral: the reserved Boolean literals `true` / `false`
    --   (evaluates to Result.bool). They are lexer keywords, never
    --   identifiers, so they can be neither declared nor shadowed and never
    --   become implicit parameters. C#: `Expr.BoolLiteral`.
    | boolLiteral : Bool -> Expr
    | unary   : UnaryOp -> Expr -> Expr
    -- * binary: an arithmetic or logical operator over two operands — never a
    --   comparison (see `comparison`).
    | binary  : BinaryOp -> Expr -> Expr -> Expr
    -- * comparison: a COMPARISON CHAIN `first op1 x1 op2 x2 …`, the ONE
    --   representation of every comparison, with one link (`a < b`) or many
    --   (`a < b <= c == d != e`). Unparenthesized comparison operators at one
    --   syntactic level form one chain; a parenthesized comparison is an
    --   ordinary operand (`(a < b) == c` is a one-link chain whose first
    --   operand is a chain). Each link compares the PREVIOUS operand with its
    --   own — adjacent-pair semantics, so `1 != 2 != 1` is `1 != 2` and
    --   `2 != 1` — and the chain is `true` iff every link holds. Evaluation
    --   (`evalComparisonCounted`) is incremental and left to right: every
    --   operand is evaluated EXACTLY ONCE (the previous operand's VALUE is
    --   reused, never its expression), each link is compared as soon as its
    --   operand is available, a `false` link never stops the chain (eager
    --   Boolean composition, so a later invalid comparison is still an error),
    --   and an error terminates it (later operands are not evaluated). A chain
    --   with no links evaluates its first operand and is `true`.
    --   C#: `Expr.Comparison`.
    | comparison : Expr -> List ComparisonLink -> Expr
    -- * index: VARIADIC POSTFIX SELECTION `receiver[s1, …, sn]` (October 2026,
    --   replacing the retired colon form `receiver:s`). The selector list is an
    --   ordinary written expression list (spread slots included) over the
    --   receiver. PARENTHESES INVOKE A COMPUTATION; POSTFIX BRACKETS SELECT FROM
    --   A VALUE; selection never changes how its receiver obtains that value.
    --   Evaluation (the `.index` arm of `evalCounted`): demand the receiver
    --   ONCE through its ordinary value path; form the selector supply exactly
    --   like a call's (`formNeedSupply`: explicit spreads run, ordinary selectors
    --   stay suspended cells); demand, validate and select each supplied index
    --   LEFT TO RIGHT, stopping at the first failure (`selectWith`); capture the
    --   selected values canonically (`combineOutputSlots`: zero → `()`, one →
    --   the value itself, several → one sequence of the values kept whole). The
    --   positional view is the ONE immediate view `count`/`first`/`last` read
    --   (`Result.projectionItems`). No callable identity. C#: `Expr.Index`.
    | index   : Expr -> List Expr -> Expr
    -- * sequenceConstruct: INTERNAL sequence-join node retained for semantic
    --   AST compatibility (surface spreading is the attached postfix spread marker `expr*`,
    --   `sequenceSpread`, and never builds this node).
    --   It is NOT the representation of written sequence-value syntax: the
    --   C# surface parser and production transformations have zero origin
    --   sites for it — surviving parenthesized lists parse to `capture`
    --   nodes and `()` to emptySequence; visitors only rebuild an existing node.
    --   The exported `sequenceConstruct` helper (and the public C# AST API)
    --   is the intentional external origin mechanism. Its value evaluation
    --   DROPS `()` leaves (join semantics), which written parentheses never
    --   do, so routing surface syntax through it would silently violate the
    --   visible-empty rule. A spread leaf contributes exactly its spread items,
    --   read back like a spread output row — one boundary per written star,
    --   never reopened — so the join agrees with the written capture except for
    --   the dropped non-spread `()` leaves. Guarded by
    --   SequenceConstructContainmentTests (C#) and the internal-node cases in
    --   SemanticExplorerCases.lean.
    | sequenceConstruct : Expr -> Expr -> Expr
    -- * emptySequence: the empty sequence value `()`. Repeated ordinary
    --   parentheses around the empty sequence are useful-structure normalized
    --   back to `()` rather than exposing higher-order empty sequence values.
    | emptySequence : Nat -> Expr
    -- * spread: UNARY representation over its single operand. The surface
    --   spelling is the attached postfix spread marker — `A*` lowers to this
    --   one node — so `sequenceSpread expr` spreads the top-level output
    --   items of `expr` and contributes them to the surrounding supply
    --   (conceptually `spread : Value -> Supply`; the receiver decides what
    --   the items become). A star with a same-line right operand is
    --   MULTIPLICATION in surface syntax, so spreading before another
    --   same-line supplied item requires a comma (`A*, B`; `A* B` is
    --   `A * B`); semicolon is not surface expression syntax. Nested
    --   spread such as `A**` is `sequenceSpread (sequenceSpread A)`;
    --   evaluation unwraps the chain iteratively
    --   (`peelSequenceSpreadLayers`, stack-safe) and applies each written
    --   layer compositionally — every layer opens one boundary of the value
    --   the previous layer's supply would re-capture — so `A**` agrees with
    --   `(A*)*` (a fixed point for sequence values; a singleton-list chain
    --   such as `[[7]]**` opens one list boundary per layer, while a
    --   multi-element list re-captures as a sequence after the first layer
    --   and then stays fixed).
    | sequenceSpread : Expr -> Expr
    -- * listLiteral: surface list literal `[e1, ..., en]`. Evaluates to exactly
    --   ONE list value (`Result.listValue`). Element slots follow
    --   the same expression-list rules as written parentheses (an explicit spread
    --   slot opens its operand's immediate items, a non-spread `()` slot stays one
    --   visible element), but the collected elements are stored EXACTLY: no
    --   singleton erasure and no empty-nesting collapse, so `[7]`, `[[7]]`, and
    --   `[]` are all distinct values. C#: `Expr.ListLiteral`.
    | listLiteral : List Expr -> Expr
    | resolve : Ident -> Expr
    -- * algorithmExpr: an algorithm used in expression position, exposing
    --   ALGORITHM IDENTITY: the contained algorithm owns its lexical scope
    --   (parameters, properties, `open`, declaration namespace) and the
    --   expression participates in value, algorithm/callable, and
    --   namespace/`open` interpretation. Surface form: `{ ... }` brace
    --   algorithm literals (also elaborated modules and recovery trees).
    --   C#: `Expr.AlgorithmExpr`.
    | algorithmExpr : Algorithm -> Expr
    -- * capture: a surviving parenthesized capture boundary over an
    --   OutputBundle (an ordered list of written expression rows with no
    --   lexical ownership — the `OutputBundle` abbreviation is declared after
    --   this mutual block). Written parentheses PERFORM capture
    --   (`capture : Supply -> Value`): evaluation supplies the rows through
    --   the shared output-row loop and canonically captures them as one
    --   value. CAPTURE IS NOT ALGORITHM IDENTITY: the algorithm channel sees
    --   only a zero-parameter output thunk over the bundle, never the
    --   algorithm identity of anything inside it. PARENTHESES GROUP SYNTAX;
    --   THEY DO NOT INTRODUCE A SEMANTIC BOUNDARY (September 2026): the C#
    --   parser erases every redundant group — a group of exactly ONE
    --   non-spread slot is that slot's expression whatever its kind, so
    --   `(x)`, `(x.M)`, `(F(1))`, `((1, 2))`, and `(())` never reach this
    --   node — and only a group whose parentheses DO something survives as
    --   it: several written slots (`(1, 2)`) or a lone spread slot (`(A*)`,
    --   the capture of an item supply into one value). A host AST may still
    --   build `capture [e]` directly; its semantics are the ordinary capture
    --   semantics (one row, captured to one value), never a written-slot
    --   boundary that a binder or receiver could observe. C#: `Expr.Capture`.
    | capture : List Expr -> Expr
    -- Call/dot-call arguments are an ordered OutputBundle of the ORIGINAL
    -- written argument expressions (spelled `List Expr` inside this mutual
    -- block), evaluated transparently in the caller's lexical context — never
    -- an Algorithm: an argument list owns no scope, and each slot participates
    -- independently in the value channel and (where permitted) the algorithm
    -- channel. `dotMember`'s `none` means NO argument-list syntax (`a.f`);
    -- `some []` is an explicit empty list (`a.f()`). C#: `Expr.Call`/`Expr.DotCall`.
    | call    : Expr -> List Expr -> Expr
    -- * dotMember: one dot edge `a.f` / `a.f(args)`, carrying the ELABORATED
    --   member facts beside the structural member name: `fallback` is the
    --   member's lexical-fallback callee identity as an ordinary name
    --   expression (`.resolve f`, or `.param f` once a front-end decides the
    --   member is a parameter reference). Resolution is structural-first with
    --   the fallback applying only on a structural miss — at EVERY level of
    --   a chain: a receiver that is itself an argumentless dot edge navigates
    --   its declared structural members (`resolveDotReceiver`), so
    --   `Lib.Sub.Q` reads `Sub`'s own `Q` before any lexical `Q`. Runtime
    --   consumers CONSUME these facts (`resolveAlg fallback`) instead of
    --   reconstructing the Param-vs-Resolve decision from environments. The C# front end
    --   consumes ordinary Grace composed with dot syntax (`a~.f` / `a.~f`),
    --   so Lean receives the SAME `dotMember` executable body as for `a.f`.
    --   Hand-built ordinary/lexical edges use the `Expr.dotCall` smart
    --   constructor declared after this mutual block.
    --   C#: `Expr.DotCall` (`LexicalFallback`).
    | dotMember : Expr -> Ident -> Expr -> Option (List Expr) -> Expr
    -- NOTE: load('url') is surface-only syntax, represented as Call(Resolve("load"), ...)
    -- in the parser and elaborated to algorithmExpr(...) by the load elaboration pass.
    -- It is NOT a core Expr constructor.  See load elaboration section below.
    deriving Repr

  /-- One link of a comparison chain: the operator that compares the PREVIOUS
      operand of the chain with `operand`. C#: `ComparisonLink`. -/
  structure ComparisonLink where
    op      : ComparisonOp
    operand : Expr
    deriving Repr

  /-- One link of an interpolated string: an interpolation `hole` and the
      already-decoded literal `text` written after it (possibly empty).
      C#: `InterpolationLink`. -/
  structure InterpolationLink where
    hole : Expr
    text : String
    deriving Repr

  /-- Property definition with visibility metadata. -/
  structure PropDef where
    name     : Ident
    alg      : Algorithm
    isPublic : Bool
    exposure : PropExposure := .exported
    identity : Option PropertyIdentity := none
    requiredOwnerDepths : Option (List (Ident × Option Nat)) := none
    deriving Repr

  /-- A branch of a conditional algorithm: a pattern and a body algorithm.
      The pattern is the complete input specification of the branch.
      Branch bodies receive bindings ONLY from the matched pattern (plus
      ordinary lexical resolution).  No extra implicit parameters are inferred
      at the branch's own level from free identifiers in the body, and Grace
      `~` is not allowed in patterns or on that level; an algorithm nested in
      the body is an ordinary independent owner (an inferring one may use
      Grace on its own inferred parameters in the C# front end, Q-16 G-O).
      Nested internal output structure may vary. -/
  structure CondBranch where
    pattern : Pattern
    body    : Algorithm
    deriving Repr

    /-- User-defined algorithm with properties, parameters, opens, and output.

      **Unique property name invariant**: the `properties` list must not
      contain two entries with the same `name`.  Properties are immutable
      bindings; redefining a property is a static error detected by the
      front-end / parser.  This invariant ensures that `lookupPropDefAny?`
      (which returns the first match) is unambiguous. -/
    inductive Algorithm where
    | mk :
        (parent     : Option ScopeCtx) ->
      (parameterPatterns : List ParameterPattern) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (output     : List Expr) ->
        (declarationId : Option PropertyIdentity := none) ->
        Algorithm
    | builtin : Builtin -> Algorithm
    /-- Conditional algorithm: ordered pattern branches tried at call time.
        At call time the supply is formed (one suspended cell per argument; only
        explicit spreads are evaluated), a count that no branch head accepts is
        `arityMismatch` before any branch is tried (NEED-05), and the branches are
        then tried in source order over the SAME cells, each pattern demanding only
        the values it inspects (NEED-04; `selectNeedFamilyBranch`).  The first
        matching branch body is evaluated.  If no branch matches a supply of an
        accepted count, evaluation fails with noMatchingBranch.

        **Full-input-specification invariant**: each branch pattern `Name(...)`
        declares the complete input interface of that branch.  A branch's own
        level does NOT infer additional implicit parameters from free
        identifiers — only names bound by the pattern and names resolvable
        through ordinary lexical / property / open / builtin lookup are
        available.  Grace `~` is forbidden in patterns and on the branch's own
        level; algorithms nested in a branch body are ordinary independent
        owners (an inferring one may use Grace on its own inferred parameters in
        the C# front end before Lean encoding, Q-16 G-O), never adding a
        parameter to the branch.

        **Uniform top-level arity invariant**: all branches of the same
        conditional algorithm must have the same top-level pattern arity
        (as defined by `Pattern.topLevelArity`).  Nested internal pattern
        structure may vary, but the outer number of inputs must remain
        consistent.  This preserves a unified outer call interface and
        prevents conditional algorithms from acting as ad hoc overloading
        by varying top-level argument count.

        **Uniform top-level output arity invariant**: all branches of the same
        conditional algorithm must have the same top-level output arity
        (the number of top-level output expressions in the branch body).
        Nested internal output structure may vary, but the outer number of
        outputs must remain consistent.  This preserves a unified output
        interface across branches.

        **Unique branch pattern invariant**: the `branches` list must not
        contain two entries whose patterns are match-equivalent (as defined
        by `Pattern.isMatchEquivalent`).  Duplicate patterns are unreachable
        (first-match semantics) and indicate a static error detected by the
        front-end / parser.

        **Clause elaboration rule**: front-ends should use
        `Algorithm.elaborateClauseGroup` when lowering surface syntax
        `Name(pattern) = body`. The ordinary-vs-conditional split is decided
        for the whole same-name clause group, not per clause. A group
        elaborates to `Algorithm.mk` only when it contains exactly one clause
        and that sole head is a recursive capture/structural parameter pattern such
        as `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, `Only([x]) = x`, or
        `CountSequenceValue((*values)) = values.count`. Multi-clause families and
        literal/mixed heads such as

          F(0) = 0
          F(x) = 1

        still lower to `Algorithm.conditional`.

        The evaluator still recognizes the equivalent single-branch flat
        multi-binder core shape as a compatibility fallback for manually
        constructed `.conditional` ASTs, but clause elaboration must not rely
        on that fallback. -/
    | conditional :
        (parent   : Option ScopeCtx) ->
        (opens    : List Expr) ->
        (branches : List CondBranch) ->
        (declarationId : Option PropertyIdentity := none) ->
        Algorithm
    /-- A RESOLVED ALGORITHM REFERENCE (FWD-02 binding indirection, 2026-10-01; M4★ whole-algorithm
        transport, ALIAS-UNIFY-1, October 2026): a binding whose one written row `target` is a
        reference to an existing algorithm, resolved in the binding's OWN scope at its declaring
        activation. The surface pass produces it for a non-root OPEN body — a named definition or an
        inline block with no written parameter list, owning no parameter after inference — whose one
        written row is a reference (a name, an argumentless structural member path, an argumentless
        `.Algorithm` edge, an enclosing parameter, an argumentless parameter-rooted path), whatever
        the referenced algorithm's arity; nothing is synthesized: no parameter list, no inherited
        signature and no wrapper call. A cyclic static reference chase is no alias (OD-D).

        **Two kinds (M4★, "braces create").** `reference = true` is a TRANSPARENT REFERENCE, the
        unbraced `A = R`: every observation of `A` is `R`'s — its structural identity, members, open
        providers, invocation, bare VALUE and publication origin (`resolveAliasStructure`,
        `resolveAliasTarget`, `resolveAliasValueTarget`, `aliasOriginBinding?`). `reference = false`
        is a STRUCTURAL FORWARDING CARRIER, the written braces `A = { R }` (own declarations allowed,
        an inline `{ R }` too): its STRUCTURE is its own — its own declaration and activation, its own
        `properties` only (no inheritance from the target) and its own public declarations for `open`
        — while every explicit invocation forwards its exact supplied computations FRESHLY to `R`'s
        target and its bare VALUE delegates to the target's bare view (OD-E). Both kinds own NO
        zero-argument cache entry and charge nothing when resolved. A kind's own `opens` and
        `properties` take part in resolving its target in its own scope; a reference's never form
        a surface of its own.

        `target` is a STATIC PATH (`Expr.isStaticAliasPath`) or a RUNTIME ROW
        (`Expr.isRuntimeAliasRow`). C#: `Algorithm.Alias` with `IsReference`. -/
    | alias :
        (parent     : Option ScopeCtx) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (target     : Expr) ->
        (declarationId : Option PropertyIdentity := none) ->
        (reference : Bool := true) ->
        Algorithm
    deriving Repr

  /-- A lexical scope level as the evaluator wires it. `params` are the parameter names
      the level's algorithm binds — its own parameters, or, on the family scope a
      conditional call wires the selected branch body under, the matched pattern
      binders. They take no part in property lookup; they let `memberAccessible?` find
      the owner of a local-only member's required input by the same nearest-owner walk
      the surface layer elaborated the reference with (C#: `ScopeCtx.Parameters`).
      `output` and `branches` retain the owning body for scope reconstruction.
      Declaration and activation IDs distinguish owners even when body components or
      binder names are shared. These IDs are separate from property-cache identity. -/
  inductive ScopeCtx where
    | mk :
        (parent  : Option ScopeCtx) ->
        (params  : List Ident) ->
        (opens   : List Expr) ->
        (props   : List PropDef) ->
        (output  : List Expr) ->
        (branches : List CondBranch) ->
        (activation : Option Nat) ->
        (declarationId : Option PropertyIdentity) ->
        ScopeCtx
    deriving Repr
end

/-- An ordered sequence of original written expression slots with no lexical
    ownership of its own: no parent scope, no parameters, no properties, no
    `open`. It is intensional syntax — how the slots contribute values or
    items is determined entirely by the RECEIVER that consumes the bundle:
    algorithm output evaluation preserves per-row emitted-count semantics,
    `Expr.capture` performs canonical sequence capture, and
    `Expr.listLiteral` collects the slots as one exact list value. It
    deliberately does NOT encode a fixed runtime consumption policy and is
    NOT a list of evaluated results. (`Algorithm.mk`'s `output` field, the
    `capture`/`listLiteral` constructor payloads, and the `call`/`dotCall`
    argument payloads are this type; the constructors inside the mutual block
    above spell it `List Expr` because the abbreviation cannot be declared
    before `Expr` exists.)
    C#: `OutputBundle`. -/
abbrev OutputBundle := List Expr

/-- Whether an argumentless reference path is rooted at a PARAMETER: the parameter itself, or an
    argumentless member edge over a parameter-rooted path (`b.G`, `b.H.G`). -/
def Expr.isParamHeaded : Expr -> Bool
  | .param _ => true
  | .dotMember receiver _ _ none => receiver.isParamHeaded
  | _ => false

/-- The RUNTIME ROWS of a callable alias (FWD-02 runtime-target aliases, META-S3-2): the argumentless
    reference shapes whose CALLABLE is a supplied cell's runtime projection — a parameter reference,
    an argumentless edge spelled `Algorithm` (a link; whether it takes the intrinsic route is decided
    member-first at run time, `aliasStepIsRuntime`), and an argumentless member path whose head is a
    parameter. C#: `AliasTargetRows.IsRuntimeRow`. -/
def Expr.isRuntimeAliasRow : Expr -> Bool
  | .param _ => true
  | e@(.dotMember _ member _ none) => member == "Algorithm" || e.isParamHeaded
  | _ => false

/-- Ordinary/lexical dot-call smart constructor: `a.f` / `a.f(args)` with the
    unelaborated fallback identity `.resolve f`. Hand-built ASTs keep plain
    lexical-fallback semantics through this form; elaborated trees carry the
    front-end's Param-vs-Resolve decision in the full `Expr.dotMember`
    constructor. C#: an `Expr.DotCall` with null `LexicalFallback`. -/
def Expr.dotCall (target : Expr) (name : Ident) (args : Option OutputBundle) : Expr :=
  .dotMember target name (.resolve name) args

/-- Smart constructor for a ONE-LINK comparison chain `left op right` — the
    hand-built spelling of an ordinary comparison (`a < b` is the chain with
    first operand `a` and the single link `< b`). C#: `new Expr.Comparison(a, [new ComparisonLink(op, b)])`. -/
def Expr.compare (op : ComparisonOp) (left right : Expr) : Expr :=
  .comparison left [{ op := op, operand := right }]

/-- Surface same-name clause-group classification.
  Front-ends must decide ordinary-vs-conditional elaboration only after
  collecting the entire same-name clause family, not while looking at the
  first clause in isolation.

  A same-name clause group elaborates as ordinary only when:
  - the group contains exactly one clause, and
  - that sole clause head is a recursive capture/structural (sequence or list)
    parameter pattern

  This is intentional. Later clauses may force the whole family to remain
  conditional, for example:

      F(0) = 0
      F(x) = 1

  Even though `F(x) = 1` alone would qualify for ordinary elaboration, the
  full family must stay conditional because branch selection is defined at the
  whole-group level. -/
inductive ClauseGroupDefinitionKind where
  | ordinary : List ParameterPattern -> ClauseGroupDefinitionKind
  | conditional : ClauseGroupDefinitionKind
  deriving Repr

--------------------------------------------------------------------------------
-- Result (structured evaluation artifact)
--------------------------------------------------------------------------------

inductive Result where
  | atom  : Int -> Result
  | str   : String -> Result     -- first-class string value (exact equality, no ordering/coercion)
  -- Boolean value `true` / `false`: a first-class scalar value kind that is
  -- NOT a number (no implicit conversion in either direction). Produced by
  -- the Boolean literals, every comparison operator, the logical operators,
  -- and `contains`; consumed wherever a condition or predicate is required
  -- (`if`, `filter`, the `while` continuation flag, `not`/`and`/`or`/`xor`).
  -- Equality is total across kinds (`bool true == atom 1` is false); there
  -- is no ordering on Booleans. C#: `Result.Bool`.
  | bool  : Bool -> Result
  | sequenceValue : List Result -> Result
  -- List value `[a, b, c]`. Unlike sequence values, list
  -- structure is never singleton-normalized: `listValue [r]` and `r` are
  -- distinct values, `listValue []` is distinct from the empty sequence
  -- value, and nesting is preserved exactly. C#: `Result.ListValue`.
  | listValue : List Result -> Result
  -- CALL REFERENCE (CallReference S1, October 2026): the opaque, run-scoped reference
  -- a `meta` parameter binds — the INVOCATION PLAN of one supplied call computation,
  -- identified by that call's need address (`NeedPlan.reify`). It is an ordinary
  -- transportable value (bindings, properties, `if`, selection, lists and sequences
  -- carry it unchanged) but no callable algorithm: it has no CALLABLE identity, no
  -- structural members, no number, Boolean or text view, and no ordering. Two
  -- references are equal iff they denote the same plan (`Result.beq` on the address).
  -- Its one operation is the dot intrinsic `R.Invoke()` (`NeedPlan.invoke`). It never
  -- leaves its run: the run result boundary (`runResultM`) and text conversion
  -- reject any value containing one (`Result.containsCallRef`). C#: `Result.CallReference`.
  | callRef : Nat -> Result
  -- ARGUMENT VIEW (CallReference S2, October 2026): the lazy, read-only view `R.Arguments`
  -- of the ORIGINAL effective argument supply of the call reference `callRef a` — the same
  -- plan address, a different object (`argView a ≠ callRef a`). Obtaining it runs nothing:
  -- no target, no supply preparation, no argument VALUE. Its operations are `count`
  -- (prepares the plan's ONE sticky supply, demands no argument), selection / `first` /
  -- `last` (prepare, then demand ONLY the selected cells) and the supply spread `F(V*)`,
  -- which TRANSPORTS the plan's original cells (`NeedSupply.slot`, `SpreadSupply.cells`).
  -- Like a call reference it is opaque (no CALLABLE, members, number, Boolean, text,
  -- ordering), equal only to itself (`Result.beq`), and never leaves its run
  -- (`containsCallRef`). C#: `Result.CallReference` with `IsArgumentView`.
  | argView : Nat -> Result
  deriving Repr

/- VALUE EQUALITY of results (`==`): structural equality — the same constructor with equal
    payloads, sequence and list items compared in order. Written out (S5, October 2026) instead
    of `deriving BEq`, whose handler compiles a nested inductive to an OPAQUE `partial`
    function, so that its laws are kernel theorems (`KatLangArityLaws/RepeatedNameLaws.lean`:
    `==` is `=`, `LawfulBEq`). It computes exactly the derived comparison: every constructor
    compares its fields with their own `==` and a list field with `List`'s elementwise `==`.
    The repeated-name binder's counted-value comparison (NEED-04) is this `==` on
    `CountedResult`, value and emitted count together. -/
mutual
  /-- Structural VALUE EQUALITY of two results: the `BEq Result` instance below. -/
  def Result.beq : Result -> Result -> Bool
    | .atom a, .atom b => a == b
    | .str a, .str b => a == b
    | .bool a, .bool b => a == b
    | .sequenceValue xs, .sequenceValue ys => Result.beqList xs ys
    | .listValue xs, .listValue ys => Result.beqList xs ys
    | .callRef a, .callRef b => a == b
    | .argView a, .argView b => a == b
    | _, _ => false

  /-- `List`'s elementwise `==` over `Result.beq` (the derived comparison's list fields). -/
  def Result.beqList : List Result -> List Result -> Bool
    | [], [] => true
    | x :: xs, y :: ys => Result.beq x y && Result.beqList xs ys
    | _, _ => false
end

instance : BEq Result := ⟨Result.beq⟩

namespace Result
  def normalize : Result -> Result
    | atom n => atom n
    | str s  => str s
    | bool b => bool b
    | sequenceValue rs =>
        let rs' := rs.map normalize
        match rs' with
        | [r] => r
        | _   => sequenceValue rs'
    -- Lists are exact: normalize their elements (redundant SEQUENCE structure
    -- inside a list still normalizes) but never collapse the list boundary
    -- itself — `[7]` stays `[7]`, never `7`.
    | listValue rs => listValue (rs.map normalize)
    | callRef a => callRef a
    | argView a => argView a

  /-- Language-level atom collection for the `atoms` builtin: recursively
      collect numeric atoms depth-first, left-to-right, through BOTH sequence
      and exact list boundaries. Strings and other non-numeric leaves
      contribute no atoms. The builtin materializes this collection as ONE
      list value (`makeCollectionListResult`).
      Deliberately separate from `Result.hostAtoms` (host projection), so the
      two contracts cannot drift through shared code. Boolean values are not
      numeric atoms and contribute nothing, like strings.
      C#: `Result.LanguageAtoms`. -/
  def languageAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | bool _    => []
    | sequenceValue rs => rs.flatMap languageAtoms
    | listValue rs => rs.flatMap languageAtoms
    | callRef _ => []
    | argView _ => []

  /-- Host-boundary numeric flattening used by `runFlat`: the numeric atoms
      reachable through sequence AND exact list boundaries, so collection-
      builtin results surface their numeric contents at the embedding
      boundary. This is a host projection, not language semantics: the
      `atoms` builtin collects through its own separate collector
      (`Result.languageAtoms`) and returns one exact list value rather than a
      host atom list, and no in-language conversion between lists and
      sequences is implied. Strings and Boolean values have no numeric
      projection and are omitted.
      C#: `Result.ToHostAtoms`. -/
  def hostAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | bool _    => []
    | sequenceValue rs => rs.flatMap hostAtoms
    | listValue rs => rs.flatMap hostAtoms
    | callRef _ => []
    | argView _ => []

  /-- Canonical text of a Boolean value: lowercase `true` / `false`, the same
      spelling as the literals. C#: `ValueTextRenderer.FormatBool`. -/
  def boolText : Bool -> String
    | true => "true"
    | false => "false"

  /-- Boolean view of a value, for every consumer that REQUIRES a condition or
      predicate (`if`, `filter`, the `while` continuation flag, `not`, `and`,
      `or`, `xor`). Only a Boolean value qualifies; a redundant singleton
      sequence boundary normalizes away exactly as `asInt?` does for numbers
      (`(true)` is `true`). Numbers have NO truth value — there is no
      `0`/nonzero convention — and neither do strings, multi-item sequence
      values, the empty sequence value, or lists.
      C#: `Result.AsBool`. -/
  def asBool? : Result -> Option Bool
    | bool b => some b
    | sequenceValue rs =>
        match normalize (sequenceValue rs) with
        | bool b => some b
        | _      => none
    | _ => none

    /-- Strict numeric extraction for numeric collection builtins such as `min`,
      `max`, `sum`, and `avg`.
      Accepts exactly one atomic numeric value.

      Sequence values are not flattened or recursively inspected, and strings
      are rejected. -/
  def singleAtomicNumber? : Result -> Option Int
    | atom n => some n
    | _      => none

  def asInt? : Result -> Option Int
    | atom n => some n
    | str _  => none
    | bool _ => none   -- Booleans are not numbers: no implicit conversion
    | sequenceValue rs =>
        match normalize (sequenceValue rs) with
        | atom n => some n
        | _      => none
    | listValue _ => none   -- lists never coerce to numbers, not even `[5]`
    | callRef _ => none     -- a call reference is no number
    | argView _ => none     -- nor is an argument view

  /-- Top-level items of a MULTI-ITEM counted result: a sequence value's items;
      any other value is itself. This is not an opening operation — call
      binding never uses it (every non-spread argument is ONE item) — it only
      recovers the rows a multi-output body emitted (`countedTopLevelValues`)
      and serves as the non-list branch of the one-level views below. The
      explicit openers are the spread marker (`spreadItems`, which assignment
      deconstruction's elaboration also uses), the kind-specific structural
      patterns (`sequencePatternItems?` for `(…)`, `listPatternItems?` for
      `[…]`), the selection RECEIVER position view (`projectionItems` — the
      receiver's positions, never the selected element), and the post-binding
      builtin collection view (`builtinCollectionItems`, applied to the bound
      `collection` argument). Every opener except the structural patterns opens
      a sequence and a list alike; a structural pattern opens only its own
      kind. -/
  def toItems : Result -> List Result
    | atom n   => [atom n]
    | str s    => [str s]
    | bool b   => [bool b]
    | sequenceValue rs => rs
    | listValue rs => [listValue rs]
    | callRef a => [callRef a]
    | argView a => [argView a]

  /-- Item view used by the spread expression (`expr*`): spread opens exactly ONE
      structure boundary. Sequence values and exact list values open to their
      immediate items; atoms and strings supply themselves as one item.
      C#: `Result.SpreadItems`. -/
  def spreadItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- The openable-structure view: a sequence value or exact list value opens
      to its immediate items; atoms, strings, and Booleans are not structures.
      Its total extension is the spread view (`(structureItems? v).getD [v] =
      spreadItems v`, `spreadItems_extends_structureItems`), which is what
      assignment deconstruction's unpacking receiver (`ParameterPattern.unpacking`)
      opens its lone right-hand side with; the structural patterns open only
      their own kind (`sequencePatternItems?`, `listPatternItems?`), and
      call-argument binding never opens an argument. It anchors the arity
      algebra's `structureItems?` (`CoreArityAlgebra.lean`); no evaluator path
      reads it, so it has no C# counterpart. -/
  def structureItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | listValue rs => some rs
    | _ => none

  /-- STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE
      (September 2026): the elements a SEQUENCE pattern `(p1, …, pn)` binds
      against, given the ONE value its slot supplies — a sequence value's
      elements, and nothing for any other value. A list value is NOT opened
      (`[x, y]` is the list pattern) and a scalar is NOT a one-item supply: the
      only pattern that takes a value whole is a bare binder. This is the ONE
      rule shared by the one Model-C binder (`bindNeedOne`, for direct calls,
      callbacks, loop steps and clause families alike) and the pattern matcher
      (`matchPatternInto`), so a callback that
      supplies one value `V` to a pattern `P` binds exactly as the ordinary call
      `P(V)` does. A
      sequence value has 0 or at least 2 elements (there is no one-item
      sequence), which is why a one-item sequence pattern is invalid.
      C#: `Result.SequencePatternItems`. -/
  def sequencePatternItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | _ => none

  /-- The elements a LIST pattern `[p1, …, pn]` binds against: a list value's
      elements, and nothing for any other value — never a sequence value and
      never a scalar. Lists keep every cardinality, so `[]`, `[x]` and
      `[x, *rest]` match lists of zero, one and at least one element.
      C#: `Result.ListPatternItems`. -/
  def listPatternItems? : Result -> Option (List Result)
    | listValue rs => some rs
    | _ => none

  /-- Count emitted top-level values when a result is already in hand.
      Empty results emit 0. Any non-empty atomic, string, or sequence value
      counts as one value. List values ALWAYS count as one visible value,
      including the empty list `[]` — only the empty SEQUENCE value `()` is
      the invisible-able empty result.

      It is the emitted count of every value boundary (VAL-06): property reads,
      call results — `map`/`reduce` callback results included (HO-03) —, builtin
      results, selection and callback items. -/
  def valueCount : Result -> Nat
    | sequenceValue [] => 0
    | _ => 1

  /-- The IMMEDIATE POSITIONAL VIEW of a selection receiver: a sequence value or
      exact list value offers its immediate elements as positions; every other
      value follows `toItems` (a number, a Boolean or a string offers ITSELF as
      the single position — a string, the empty string included, is never
      decomposed into characters). It is the ONE view `count`, `first`, `last`
      and postfix selection share (`positional_view_is_shared`: it equals the
      post-binding collection view `builtinCollectionItems`); an empty list or
      sequence has no positions. This view decides WHICH positions exist and
      never opens the selected element, which `select?` returns exactly as
      stored (a nested list element stays one opaque list, a nested sequence
      element one sequence value). C#: `Result.ProjectionItems`. -/
  def projectionItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- SELECTION IS A VALUE BOUNDARY (September 2026): one supplied selector of
      a postfix selection `receiver[i]` selects one immediate position of the
      receiver and returns the stored element as ONE value — it never opens
      it. A selected sequence value stays one sequence value, a selected list
      stays one exact list, and the selected value's origin is forgotten: the
      `.index` arm of `evalCounted` applies this once per supplied selector
      (`selectPosition`) and captures the selected values canonically
      (`selectionResult`), so a single selection of `()` emits zero values and
      everything else emits one. Only the spread marker (`spreadItems`) opens a
      selected value. `first`/`last` (`evalFirstCounted`/`evalLastCounted`) and
      higher-order callback items (`countedSequenceCallbackItem`) select through
      the same rule. Laws: `select_is_a_value_boundary`,
      `first_is_selection_at_zero`, `last_is_selection_at_count_minus_one` in
      `KatLangArityLaws.lean`. C#: `Result.Index`. -/
  def select? (r : Result) (i : Nat) : Option Result :=
    r.projectionItems[i]?

  /-- THE structural text of a value (VAL-12): what an interpolation hole writes.
      A number is its canonical text (the text the `.string` intrinsic writes,
      `resultToString`; on this integer tier `toString`), a Boolean its keyword
      (`boolText`), a string ITSELF — verbatim and never quoted, at every nesting
      level — and a sequence or list its elements' texts separated by `, ` inside
      parentheses or brackets, so `()` and `[]` stay distinct and nesting is kept.
      It is TOTAL: every value has a text, so converting a hole never fails.
      Human-readable text, not a serialization (`[str "a, b"]` and
      `[str "a", str "b"]` write the same text). Display settings never reach it.
      C#: `ValueTextRenderer.AppendCanonicalValue` (whose numbers are Decimal128
      canonical text, a C#-only tier). -/
  def canonicalText : Result -> String
    | atom n => toString n
    | str s => s
    | bool b => boolText b
    | sequenceValue rs => "(" ++ ", ".intercalate (rs.map canonicalText) ++ ")"
    | listValue rs => "[" ++ ", ".intercalate (rs.map canonicalText) ++ "]"
    -- A call reference has NO text (CallReference S1): the evaluator's interpolation
    -- arm rejects a hole whose value contains one BEFORE this function sees it
    -- (`requireCallRefFree`), so this arm is unreachable from evaluation; it exists only
    -- to keep the function total and is not a display syntax.
    | callRef _ => ""
    | argView _ => ""

  mutual
    /-- Whether a value CONTAINS a call reference at any depth (CallReference S1). The run
        result boundary (`runResultM`) and interpolation reject such a value; ordinary
        language operations transport it. C#: `Evaluator.ContainsCallReference`. -/
    def containsCallRef : Result -> Bool
      | callRef _ => true
      | argView _ => true
      | sequenceValue rs => anyContainsCallRef rs
      | listValue rs => anyContainsCallRef rs
      | _ => false

    /-- Whether some value of a list contains a call reference. -/
    def anyContainsCallRef : List Result -> Bool
      | [] => false
      | r :: rs => containsCallRef r || anyContainsCallRef rs
  end
end Result

/-- INTERPOLATION (VAL-12), the TOTAL combinator the evaluator's
    `.interpolatedString` arm instantiates with the ordinary value read of each
    hole (`fun hole => eval hole ctx env`, the read a comparison operand uses).
    Starting from the accumulated text `acc`, each link's hole is evaluated
    through `value` — LEFT TO RIGHT, EXACTLY ONCE — its value's structural text
    (`Result.canonicalText`) is appended at once, then the link's literal text.
    Because the holes are sequenced by the monad's bind, the first failing hole
    ends the whole run and no later hole is ever evaluated. Defined above the
    evaluator core (the FORMAL-07 pattern), so its laws are theorems for every
    channel (`KatLangArityLaws.lean` § Interpolation); the evaluator arm
    (`EvalBody.evalCounted`) passes the ordinary value read — since R7 a kernel
    term of the total core, still pinned by `#guard`s. C#: the `InterpolatedString` case of `Evaluator.EvalExpressionSpineCounted`
    and its async twin (an iterative frame machine — an implementation strategy with
    the same order — which additionally checks the C#-only string limits before each
    append). -/
def interpolateWith {m : Type → Type} [Monad m] (value : Expr → m Result) :
    String → List InterpolationLink → m String
  | acc, [] => pure acc
  | acc, link :: rest => do
      let holeValue ← value link.hole
      interpolateWith value (acc ++ Result.canonicalText holeValue ++ link.text) rest

/-- Counted evaluation result: the normalized value paired with the number of
  top-level values emitted at the current algorithm boundary.

  Helpers whose names end in `Counted` preserve this pair instead of
  collapsing the result to just the normalized value. -/
abbrev CountedResult := Prod Result Nat

/-- One algorithm-output evaluation prepared for consumers that need both the
    ordinary counted value and the evaluated written output slots. `outputSlots`
    contains the same evaluated `Result` values used to construct `counted`; it
    is not a second semantic sequence and does not perform another evaluation.
    C#: `PreparedAlgorithmOutput`. -/
structure PreparedAlgorithmOutput where
  counted : CountedResult
  outputSlots : List Result
  deriving Repr

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

def lookupAssoc {A} (k : Ident) : Assoc Ident A -> Option A
  | [] => none
  | (k',v)::xs => if k = k' then some v else lookupAssoc k xs

abbrev ValEnv := Assoc Ident Result

/- A parameter's CALLABLE identity is its supplied need cell's projection
   (`projectNeedCallable`), and its VALUE is that cell's one demand (`demandNeedRecursive`):
   since Model C (October 2026) there is no separate algorithm-channel tier and no
   counted callback-parameter tier — they were retired on 2026-10-13, with their C#
   counterparts, after a dependency analysis showed that no production binding site
   still wrote either. -/

inductive ZeroArgPropertyAccessKind where
  | lexical
  | structural
  deriving Repr, BEq

/-- Key of the per-run zero-parameter property cache — and with it the cache's
    semantic LAW (C#: `ZeroArgPropertyCacheKey`).

    THE RULE: a zero-parameter property is evaluated once per run for each
    resolved property binding; repeated VALUE access to that same binding reuses
    the result, a shadowing property is a different binding with its own entry,
    and an explicit call `A()` evaluates afresh, neither reading nor replacing
    the entry. CACHE IDENTITY FOLLOWS SEMANTIC BINDING IDENTITY, never the
    spelling of the name: the key is the resolved binding (its declaring scope
    and declaration), so two properties that happen to share a name never share
    an entry. HOW A PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING: the
    decision to reuse or evaluate belongs to the property ACCESS, and every
    consumer — an operator, a comparison, a list element, a selection, a user
    call argument, a builtin VALUE slot (`sum(A)`, `A.sum`, `if(c, A, B)`, a
    loop's initial state, `reduce`'s initial accumulator), the `.string`
    intrinsic's receiver, a callback body — receives the value that access
    produced (`supplyNeed`, `evalDotStringReceiverValue`). The scope of a
    stored value follows the binding's exposure classification:

    * an EXPORTED binding is self-contained — its value depends on no input that
      an enclosing owner's call binds — so the binding context at the access is
      not a determinant of the value: ONE entry per run per declaring scope
      serves every property-style access, from any call, callback, loop
      iteration, or explicit outer call. Its environment components are `none`.
    * a LOCAL-ONLY binding reads an input an enclosing owner's call binds
      through the dynamically threaded environments, so its value is a
      function of its DECLARING owner's binding context, retained by the existing
      lexical activation. Nested consumers never split that entry, and distinct
      owner calls never share it even with equal values. Scopes without retained
      activations keep the host environment fallback.

    Lean keys use structural representations (`reprStr`) because the model has
    immutable AST values rather than C# object identities. Run preparation
    assigns declaration identities before wiring, so separate declarations with
    equal bodies never alias; explicit `shared` identities preserve declaration
    sharing in host ASTs, but they do not represent C#'s by-reference host-scope
    identity for arbitrary host DAGs (O-6, deferred: see `PropertyIdentity`).
    The owner is its `asScopeCtx` (including parent chain), and exported
    lexical/structural spellings have one key. Explicit calls never read nor
    replace their own cache entry; a qualifying zero-supply invocation computes
    the SAME key and may establish an empty entry (CACHE-PUB-1, the `invoke`
    request). Only successful results are stored, and an enclosing failure never
    rolls back another key's successful nested store. WHICH completion is stored
    is the publication law of `evalZeroArgPropertyAccessCounted` (Q-37, extended
    by CACHE-PUB-1): the OUTERMOST successful qualifying evaluation of the key —
    a property-style read or an explicit zero-supply invocation; a re-entrant
    request of a key whose owner is still active evaluates but never publishes. -/
structure ZeroArgPropertyCacheKey where
  accessKind : ZeroArgPropertyAccessKind
  owner      : String
  propertyName : Ident
  propertyAlgorithm : String
  valEnv : Option String
  bindingContext : Option Nat
  deriving Repr, BEq

abbrev ZeroArgPropertyCache := List (Prod ZeroArgPropertyCacheKey CountedResult)

namespace ZeroArgPropertyCache
  def lookup (cache : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
      : Option CountedResult :=
    match cache with
    | [] => none
    | (existingKey, value) :: rest =>
        if existingKey == key then some value else lookup rest key

  def insert (cache : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
      (value : CountedResult) : ZeroArgPropertyCache :=
    match cache with
    | [] => [(key, value)]
    | (existingKey, existingValue) :: rest =>
        if existingKey == key then
          (existingKey, existingValue) :: rest
        else
          (existingKey, existingValue) :: insert rest key value
end ZeroArgPropertyCache

/-- Invocation-local supply bindings refer to stable addresses in the run heap. -/
abbrev NeedEnv := Assoc Ident Nat

structure EvalCtx where
  callStack : List Algorithm
  needEnv : Assoc Ident Nat := []
  bindingContext : Nat := 0
  headScope : Option ScopeCtx := none
  deriving Repr


/-- VALUE state is separate from callable projection. Completed failures are sticky. -/
inductive NeedState where
  | suspended
  | evaluating
  | completed (outcome : Except Error CountedResult)
  deriving Repr

inductive NeedSuspension where
  | expression (source : Expr) (caller : EvalCtx) (values : ValEnv)
  | collector (slice : List Nat)
  -- Produced data is a calculation value and carries no callable identity.
  | ready (value : CountedResult)
  deriving Repr

/-- The invocation-plan supply of ONE supplied call computation (CallReference M1.5,
    October 2026; `NeedPlan`). A cell whose suspension is a supported written call
    (`NeedPlan.callShape?`) IS an invocation plan, identified by its need address: VALUE
    demand executes the plan, and the internal META projection (`NeedPlan.reify`) reifies the
    same address. The plan forms its effective argument supply at most once, through the ONE
    former `NeedSupply.form`; the outcome — the ordered sourced cells or an ordinary failure —
    is sticky (D3, provisional) and every later execution of the plan runs over exactly it.
    `preparing` marks a formation in progress (a reentrant preparation is a `demandCycle`, which
    no ordinary program reaches: VALUE re-entry is already a cycle of the cell itself).
    It is semantic run state, never an observation field, and it never holds a VALUE result:
    the cell's VALUE stays in `NeedState`. Every other cell stays `unprepared`. -/
inductive NeedPlanSupply where
  | unprepared
  | preparing
  | prepared (outcome : Except Error (List (Nat × Option Expr)))
  deriving Repr

/-- CALLABLE state, separate from the VALUE state (META-S3-0a, NEED-06/NEED-09). A
    completed projection keeps its outcome: a callable identity (`.ok (some _)`), the
    SUCCESSFUL absence of one (`.ok none`), or an ordinary failure (`.error _`). `projecting`
    marks a projection in progress, so re-entering it is a `demandCycle` exactly as
    re-entering an `evaluating` VALUE is (`NeedProjection.step`). An identity-only projection
    never observes the marker (`KatLangArityLaws/NeedControl.lean` § Projection). -/
inductive NeedCallableState where
  | unprojected
  | projecting
  | projected (outcome : Except Error (Option Algorithm))
  deriving Repr

/-- META-S3-4 (CR-2/CR-13): which invocation a plan's written form performs, decided ONCE by the
    first route-dependent operation (`NeedPlan.routeOf`) through identity resolution only
    (`classifyPlanRouteWith`, the ordinary dot decision `selectDotEdge`): an ordinary call
    (`f(args)`, or `t.N(args)` selecting a declared member — callee the argumentless path, DOT-09),
    the `.Algorithm` intrinsic (`t.Algorithm(args)` / `(t.Algorithm)(args)` on a structural miss —
    callee the link `t.Algorithm`, CR-15), an extension call (`t.F(args)` on any other structural
    miss is `F(t, args)`, DOT-03), or a non-callable intrinsic (`.string`, `.Invoke`, `.Arguments`):
    the plan's VALUE is the ordinary evaluation and every route-dependent reference operation is
    `NeedPlan.invocationRefusal` (D-1A). -/
inductive PlanRoute where
  | call
  | algorithm
  | extension
  | intrinsic
  deriving Repr, BEq, DecidableEq

structure NeedCell where
  suspension : NeedSuspension
  state : NeedState := .suspended
  callable : NeedCallableState := .unprojected
  plan : NeedPlanSupply := .unprepared
  /-- META-S3-4: the plan's recorded route (`NeedPlan.routeOf`), written once and never changed. -/
  route : Option PlanRoute := none
  /-- META-S3-1, CR-13: an invocation plan's canonical CALLEE CELL, established lazily by the
      first observation that needs it (`NeedPlan.calleeCell`) and never changed again. -/
  callee : Option Nat := none
  /-- META-S3-1, CR-15: a supplied `X.Algorithm` link's canonical RECEIVER CELL, established
      lazily by the first channel that needs it (`NeedLink.receiverCell`) and shared by the
      link's VALUE and CALLABLE. -/
  receiver : Option Nat := none
  deriving Repr

/-- The parameter bindings saved by one lexical owner activation: its value
    bindings and its supplied cells (a cell carries both the VALUE and the
    CALLABLE channel of its parameter). -/
structure ParameterActivation where
  values : ValEnv
  needs : NeedEnv := []
  bindingContext : Nat := 0
  deriving Repr

/-- Per-run evaluator state. The zero-parameter property cache is part of the
    Lean semantics because property-style `A` and explicit `A()` now have
    distinct observable call shapes. The state is created fresh for each
    top-level `runResult`; it is not general memoization and does not cache
    arbitrary calls or expression results (an explicit zero-supply invocation may
    establish a property's empty entry — CACHE-PUB-1 — but never reads one).
    `activeZeroArgProperties` holds the cache keys whose OWNING qualifying
    evaluation — a property-style read or an explicit zero-supply invocation, in
    ONE ownership domain — is still running (Q-37, CACHE-PUB-1,
    `evalZeroArgPropertyAccessCounted`); it is empty between accesses. -/
structure EvalState where
  needs : Array NeedCell := #[]
  zeroArgPropertyCache : ZeroArgPropertyCache := []
  activeZeroArgProperties : List ZeroArgPropertyCacheKey := []
  nextBindingContext : Nat := 1
  lexicalActivations : Array ParameterActivation := #[]
  nextRuntimeDeclaration : Nat := 0
  /-- META-S3-2: the BINDING CELL of each runtime-target alias per declaring activation
      (`aliasCellKey`), established on first use by `aliasBindingCell` and never changed. -/
  aliasCells : List (String × Nat) := []
  deriving Repr

namespace EvalState
  def empty : EvalState := {}
end EvalState

/-- Errors retain completed evaluator state. A failed value probe may be
    accepted through its algorithm channel; nested properties whose own owning
    evaluation completed keep their published result even when that enclosing
    probe fails. The wrapper's `run` projection preserves the public
    Except-shaped result API. -/
structure EvalM (α : Type) where
  runState : ExceptT Error (StateM EvalState) α

instance : Monad EvalM where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.runState >>= fun a => (f a).runState⟩

instance : MonadStateOf EvalState EvalM where
  get := ⟨get⟩
  set s := ⟨set s⟩
  modifyGet f := ⟨modifyGet f⟩

/-- Whether an outcome is the R7 INCOMPLETE outcome (`Error.fuelExhausted`), which no ordinary
    probe observes. -/
def _root_.Except.isIncomplete {α : Type} : Except Error α → Bool
  | .error .fuelExhausted => true
  | _ => false

instance : MonadExceptOf Error EvalM where
  throw err := ⟨throw err⟩
  -- R7: an incomplete outcome passes through every handler unobserved.
  tryCatch m handler := ⟨fun state =>
    match m.runState state with
    | (.error err, next) =>
        if (Except.error err : Except Error Unit).isIncomplete then (.error err, next)
        else (handler err).runState next
    | (.ok a, next) => (.ok a, next)⟩

instance : MonadLift (Except Error) EvalM where
  monadLift e := ⟨match e with | .ok a => pure a | .error err => throw err⟩

namespace EvalM
  def error {A : Type} (err : Error) : EvalM A := ⟨throw err⟩
  def ok {A : Type} (value : A) : EvalM A := pure value

  @[simp] theorem pure_bind {A B : Type} (value : A) (next : A -> EvalM B) :
      (pure value >>= next : EvalM B) = next value := rfl

  /-- Bind is associative (`EvalM` is the lawful `ExceptT Error (StateM EvalState)` in a wrapper,
      without a global `LawfulMonad` instance). -/
  theorem bind_assoc {A B C : Type} (x : EvalM A) (f : A -> EvalM B) (g : B -> EvalM C) :
      ((x >>= f) >>= g : EvalM C) = (x >>= fun a => f a >>= g) := by
    cases x with
    | mk run =>
      show EvalM.mk _ = EvalM.mk _
      congr 1
      funext s
      show ((run >>= fun a => (f a).runState) >>= fun b => (g b).runState) s
        = (run >>= fun a => (f a).runState >>= fun b => (g b).runState) s
      rw [LawfulMonad.bind_assoc]

  def run {A : Type} (m : EvalM A) (state : EvalState) : Except Error (A × EvalState) :=
    let (result, nextState) := m.runState state
    result.map (fun value => (value, nextState))
end EvalM

instance {A : Type} : Nonempty (EvalM A) := Nonempty.intro (.error Error.badArity)

/-- Capture a probe's error without rolling back successful nested cache
    stores or binding identities. The failed property itself is never stored. -/
def evalAttempt {A : Type} (m : EvalM A) : EvalM (Except Error A) :=
  ⟨fun state =>
    let (result, nextState) := m.runState state
    -- R7: an incomplete outcome is not a failure the probe can capture; it propagates.
    if result.isIncomplete then (.error .fuelExhausted, nextState) else (.ok result, nextState)⟩

theorem EvalM.modify_runState (f : EvalState → EvalState) (s : EvalState) :
    (modify f : EvalM Unit).runState s = (.ok (), f s) := rfl

theorem _root_.Except.isIncomplete_eq_true {α : Type} {o : Except Error α} (h : o.isIncomplete = true) :
    o = .error .fuelExhausted := by
  cases o with
  | ok _ => cases h
  | error e => cases e <;> first | rfl | cases h

/-- `evalAttempt` captures every COMPLETED outcome of its probe, success or ordinary failure. -/
theorem evalAttempt_runState_of_complete {A : Type} (m : EvalM A) (s t : EvalState)
    (o : Except Error A) (h : m.runState s = (o, t)) (hc : o.isIncomplete = false) :
    (evalAttempt m).runState s = (.ok o, t) := by
  unfold evalAttempt
  show (match m.runState s with
        | (result, nextState) =>
          if result.isIncomplete then ((Except.error Error.fuelExhausted : Except Error (Except Error A)), nextState)
          else (Except.ok result, nextState)) = _
  rw [h]; simp [hc]

/-- R7: `evalAttempt` never captures the incomplete outcome; it propagates unchanged. -/
theorem evalAttempt_runState_of_incomplete {A : Type} (m : EvalM A) (s t : EvalState)
    (h : m.runState s = (.error .fuelExhausted, t)) :
    (evalAttempt m).runState s = (.error .fuelExhausted, t) := by
  unfold evalAttempt
  show (match m.runState s with
        | (result, nextState) =>
          if result.isIncomplete then ((Except.error Error.fuelExhausted : Except Error (Except Error A)), nextState)
          else (Except.ok result, nextState)) = _
  rw [h]; rfl

def runEvalM (m : EvalM A) : Except Error A :=
  match m.run EvalState.empty with
  | .ok (value, _) => .ok value
  | .error err => .error err

namespace EvalCtx
  def empty : EvalCtx := { callStack := [] }
  def push (a : Algorithm) (ctx : EvalCtx) : EvalCtx :=
    { ctx with callStack := a :: ctx.callStack, headScope := none }
  def head? (ctx : EvalCtx) : Option Algorithm := ctx.callStack.head?

  /-- The callee-side context of a parameter binding: a fresh binding context
      with the bound parameter names removed from the inherited need-cell tier
      (`needEnv`; the value tier is shadowed beside it with `ValEnv.shadow`); the
      binding site then prepends the callee's own cells (`needBindingContext`).

      A bound parameter owns its name on every channel: its supplied cell
      carries both its VALUE and its CALLABLE channel, so neither a
      value-position read nor a call-position read of it can reach a same-named
      caller binding. Names the callee does not bind stay visible, which is what
      lets a nested call still reach an ancestor-owned parameter. Every
      user-call, conditional-call, callback, and loop-step binding site builds
      its context through this one definition.
      C#: `ShadowInheritedParameterEnvironments` plus the site's own prepend. -/
  def bindParameters (names : List Ident) (ctx : EvalCtx) : EvalM EvalCtx := do
    -- Equal values in separate calls are still distinct bindings. Allocate at
    -- every binding boundary, including an explicit zero-argument call, just
    -- as C# creates fresh environment lists there. A property read only pushes
    -- its algorithm and preserves this identity.
    let state <- get
    set { state with nextBindingContext := state.nextBindingContext + 1 }
    pure { ctx with
      bindingContext := state.nextBindingContext,
      needEnv := ctx.needEnv.filter (fun entry => !names.contains entry.fst) }
end EvalCtx

/-- Allocate a fresh cell; transporting a parameter never calls this function. -/
def allocateNeed (suspension : NeedSuspension) : EvalM Nat := do
  let state <- get
  let address := state.needs.size
  set { state with needs := state.needs.push { suspension := suspension } }
  pure address

def readyNeed (value : CountedResult) : EvalM Nat :=
  allocateNeed (.ready value)


abbrev ValEnv.lookup (env : ValEnv) (x : Ident) : Option Result :=
  lookupAssoc x env

/-- Remove the named bindings from an INHERITED value environment.

    A callee's value environment is its own bindings prepended to the CALLER's
    (`argEnv ++ env`), which is what lets a nested property body still read an
    ancestor-owned parameter. A parameter the call bound through its supplied
    need cell (every Model-C binding) contributes no entry to `argEnv`, so
    without this filter a same-named binding inherited from the caller would
    stay in the callee's value tier: a read that reaches that tier would observe
    an unrelated caller value instead of the argument bound at THIS invocation,
    and which caller parameter names happen to collide with a callee's parameter
    names would become observable. Shadowing the callee's whole parameter list
    is exactly the rule `EvalCtx.bindParameters` applies to the inherited
    need-cell tier; names that DO carry a value binding are shadowed by
    `argEnv` anyway, so filtering the tail changes nothing for them.
    C#: `ShadowValEnv`. -/
def ValEnv.shadow (env : ValEnv) (names : List Ident) : ValEnv :=
  env.filter (fun entry => !names.contains entry.fst)

def dedupList [BEq A] (xs : List A) : List A :=
  let rec go (seen : List A) : List A -> List A
    | []      => []
    | x :: rest => if seen.elem x then go seen rest else x :: go (x :: seen) rest
  go [] xs

--------------------------------------------------------------------------------
-- Algorithm helpers
--------------------------------------------------------------------------------

/-- Primary helper: Lookup PropDef by name (any visibility). -/
def lookupPropDefAny? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k)

/-- Primary helper: Lookup PropDef by name (public only — the member an `open` provides,
    selected by visibility alone; accessibility is checked after selection). -/
def lookupPropDefPublic? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.isPublic)

/-- Lookup Algorithm from PropDef list (any visibility). -/
def lookupPropAny (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefAny? ps k).map (fun propDef => propDef.alg)

/-- Lookup Algorithm from PropDef list (public only). -/
def lookupPropPublic (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefPublic? ps k).map (fun propDef => propDef.alg)

/-- Check if PropDef list contains a property (any visibility). -/
def hasPropAny (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefAny? ps k).isSome

/-- The root level of a scope chain — the prelude level every evaluation chain is rooted at.
    A loaded module is wired there (`Algorithm.withParent`). C#: `Evaluator.ChainRoot`. -/
def ScopeCtx.chainRoot : ScopeCtx -> ScopeCtx
  | .mk none params opens props output branches activation id =>
      .mk none params opens props output branches activation id
  | .mk (some parent) _ _ _ _ _ _ _ => parent.chainRoot

namespace Algorithm
  def normalCallableParameters (ps : List Ident) : List CallableParameter :=
    ps.map (fun p => { name := p })

  def normalParameters (ps : List Ident) : List ParameterPattern :=
    ParameterPattern.normalPatterns ps

  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ _ => p
    | .builtin _ => none
    | .conditional p _ _ _ => p
    | .alias p _ _ _ _ _ => p
  /-- An alias declares no parameter list of its own: its callable's is its target's. -/
  def parameterPatterns : Algorithm -> List ParameterPattern
    | .mk _ parameterPatterns _ _ _ _ => parameterPatterns
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ _ _ _ _ => []

  def parameters : Algorithm -> List CallableParameter
    | a => (parameterPatterns a).flatMap ParameterPattern.captures

  def params : Algorithm -> List Ident
    | a => (parameters a).map (fun parameter => parameter.name)
  def paramKinds : Algorithm -> List ParameterKind
    | a => (parameters a).map (fun parameter => parameter.kind)
  def callableSignature (name : Ident) (a : Algorithm) : CallableSignature :=
    { name := name, parameters := parameters a }
  def opens : Algorithm -> List Expr
    | .mk _ _ op _ _ _ => op
    | .builtin _ => []
    | .conditional _ op _ _ => op
    | .alias _ op _ _ _ _ => op
  /-- An alias's are what its own body declares — a carrier's own members, never its target's; a
      transparent reference declares none (M4★: its members are its target's, read through its
      structure). -/
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ _ => pr
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ pr _ _ _ => pr
  /-- The algorithm's output as an `OutputBundle` — ordered original written
      expression rows. The algorithm is the scope-owning DEFINITION of this
      bundle; the bundle itself owns no scope. An alias's is its ONE written row,
      the target reference (what the static walks see it read); the evaluator never
      evaluates an alias's output as rows — it normalizes the alias first. -/
  def output : Algorithm -> OutputBundle
    | .mk _ _ _ _ out _ => out
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ _ target _ _ => [target]

  /-- Access branches for conditional algorithms. Returns [] for other forms. -/
  def branches : Algorithm -> List CondBranch
    | .conditional _ _ bs _ => bs
    | _ => []

  def declarationId : Algorithm -> Option PropertyIdentity
    | .mk _ _ _ _ _ id => id
    | .conditional _ _ _ id => id
    | .alias _ _ _ _ id _ => id
    | .builtin _ => none

  def withDeclarationId (id : Option PropertyIdentity) : Algorithm -> Algorithm
    | .mk p ps op pr out _ => .mk p ps op pr out id
    | .conditional p op bs _ => .conditional p op bs id
    | .alias p op pr target _ r => .alias p op pr target id r
    | .builtin b => .builtin b

  /-- Whether this is a loaded module's own declaration (`PropertyIdentity.module`). -/
  def isModuleRoot (a : Algorithm) : Bool :=
    match a.declarationId with
    | some (.module _) => true
    | _ => false

  /-- Wire under the scope `p`. A loaded module (Q-31 H-P) is wired under the chain's root
      level instead, wherever it is reached: its names never see its holder's, and every reach
      is the one declaration in the one declaring scope (Q-32 I-U). C#: `Evaluator.WithParent`. -/
  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ parameterPatterns op pr out (some (.module n)) =>
        .mk (p.map ScopeCtx.chainRoot) parameterPatterns op pr out (some (.module n))
    | .mk _ parameterPatterns op pr out id => .mk p parameterPatterns op pr out id
    | .builtin b => .builtin b
    | .conditional _ op bs id => .conditional p op bs id
    | .alias _ op pr target (some (.module n)) r => .alias (p.map ScopeCtx.chainRoot) op pr target (some (.module n)) r
    | .alias _ op pr target id r => .alias p op pr target id r

  def parameterForName? (x : Ident) : List CallableParameter -> Option CallableParameter
    | [] => none
    | parameter :: parameters =>
        if x = parameter.name then some parameter else parameterForName? x parameters

  def mergeParameters (oldParameters : List CallableParameter) (newParams : List Ident)
      : List CallableParameter :=
    newParams.map (fun p => (parameterForName? p oldParameters).getD { name := p })

  def mergeParameterPatterns (oldPatterns : List ParameterPattern) (newParams : List Ident)
      : List ParameterPattern :=
    let oldCaptures := oldPatterns.flatMap ParameterPattern.captures
    if newParams.take oldCaptures.length == oldCaptures.map (fun parameter => parameter.name) then
      oldPatterns ++ (newParams.drop oldCaptures.length).map (fun p => ParameterPattern.capture { name := p })
    else
      (mergeParameters oldCaptures newParams).map ParameterPattern.capture

  /-- Replace the explicit parameter list of a user-defined algorithm.
      This is used by clause elaboration to preserve ignored binders such as
      `K(a, b) = a`, where `b` must remain part of the ordinary call interface
      even though it is not referenced in the body. -/
  def withParams (ps : List Ident) : Algorithm -> Algorithm
    | .mk p oldPatterns op pr out id => .mk p (mergeParameterPatterns oldPatterns ps) op pr out id
    | .builtin b => .builtin b
    | .conditional p op bs id => .conditional p op bs id
    | .alias p op pr target id r => .alias p op pr target id r

  def withParameterPatterns (patterns : List ParameterPattern) : Algorithm -> Algorithm
    | .mk p _ op pr out id => .mk p patterns op pr out id
    | .builtin b => .builtin b
    | .conditional p op bs id => .conditional p op bs id
    | .alias p op pr target id r => .alias p op pr target id r

  def hasStructuredParameterPattern (a : Algorithm) : Bool :=
    ParameterPattern.hasStructured (parameterPatterns a)

  def topLevelParameterKind? (a : Algorithm) (name : Ident) : Option ParameterKind :=
    ParameterPattern.topLevelCaptureKind? name (parameterPatterns a)

  def collectingParam? (a : Algorithm) : Option (Nat × Ident) :=
    if hasStructuredParameterPattern a then
      none
    else
      let rec go : Nat -> List CallableParameter -> Option (Nat × Ident)
        | _, [] => none
        | index, parameter :: parameters =>
            match parameter.kind with
            | .collecting => some (index, parameter.name)
            | .normal | .metaRef => go (index + 1) parameters
      go 0 (parameters a)

  /-- A callable whose top-level parameter list consumes the supplied call
      argument supply: any top-level collecting capture, whether a lone collecting binding
      `*name` or a comma shape such as `x, *y, z`. A plain sequence-valued
      argument stays one supplied argument; only explicit spread opens it first. -/
  def usesItemSupplyBinding (a : Algorithm) : Bool :=
    (collectingParam? a).isSome

  /-- Classify a same-name clause family after all of its clauses are known.
      This is the real ordinary-vs-conditional decision boundary.

      A same-name clause group is ordinary only when it contains exactly one
      clause and that sole head is a recursive capture/structural parameter pattern.
      Otherwise the whole group remains conditional. This prevents regressions
      where an early ordinary-looking clause is committed as ordinary before
      later clauses reveal true pattern semantics, such as:

          F(0) = 0
          F(x) = 1 -/
  def clauseGroupDefinitionKind : List CondBranch -> ClauseGroupDefinitionKind
    | [branch] =>
        match Pattern.plainClauseParameterPatterns? branch.pattern with
        | some patterns => .ordinary patterns
        | none => .conditional
    | _ => .conditional

  /-- Elaborate a whole same-name clause family.
      Front-ends should collect all clauses of a same-name family first, then
      call this helper exactly once. A family elaborates as ordinary only when
      it has exactly one clause and that sole head is a recursive capture/structural
      parameter pattern; otherwise the whole family elaborates as
      `Algorithm.conditional`.

      This preserves higher-order ordinary call semantics for single-clause
      families such as `Apply(f) = f(4)` and
      `Choose(x, predicate) = if(predicate(x), x, 0)`, and preserves structural
      ordinary parameter shapes such as `PairSum((x, y)) = x + y` and
      `Only([x]) = x`, while keeping
      multi-clause and literal/mixed families conditional.

      Opens are BRANCH-OWNED: every branch body keeps its own opens, and the
      family itself owns none (`opens := []` in both conditional arms). An
      `open` written in one clause provides its names to that branch body and
      its nested scopes only (MOD-05): the family scope is the parent level of
      EVERY selected branch (`wireSelectedBranchBody` installs `callee.opens`
      there), so copying one branch's opens onto the family would leak them
      into every sibling branch — and re-resolve a copied named target such as
      a branch-local `open L` from the family's scope, where `L` is not
      visible. Clause bodies are brace blocks and may each declare their own
      opens, so branch opens routinely differ. C#: `Algorithm.ElaborateClauseGroup`
      (`Opens: []`). -/
  def elaborateClauseGroup : List CondBranch -> Algorithm
    | [branch] =>
        match clauseGroupDefinitionKind [branch] with
        | .ordinary patterns => branch.body.withParameterPatterns patterns
        | .conditional =>
            .conditional (parent branch.body) [] [{
              pattern := branch.pattern
              body := branch.body.withParams []
            }]
    | branches =>
        .conditional
          (branches.head?.map (fun branch => parent branch.body) |>.join)
          []
          (branches.map (fun branch => {
            pattern := branch.pattern
            body := branch.body.withParams []
          }))

  /-- Convenience wrapper for an already-known single-clause group.
      Front-ends must not use this while parsing a clause family incrementally;
      they should first collect the full same-name group and then call
      `elaborateClauseGroup`. -/
  def elaborateClauseDefinition (pattern : Pattern) (body : Algorithm) : Algorithm :=
    elaborateClauseGroup [{ pattern := pattern, body := body }]

  def asScopeCtx (a : Algorithm) : ScopeCtx :=
    ScopeCtx.mk (parent a) (params a) (opens a) (props a) (output a) (branches a) none (declarationId a)

  def isBuiltin : Algorithm -> Bool
    | .builtin _ => true
    | _          => false

  /-- Algorithm-level explicit parameters define a closed direct-call interface
      and therefore require the algorithm to define output.  Surface front-ends
      must not append inferred implicit parameters to this interface; free names
      in explicitly parameterized bodies must resolve lexically or be reported as
      undeclared. -/
  def declaresExplicitParamsWithoutOutput : Algorithm -> Bool
    | .mk _ parameterPatterns _ _ out _ => !parameterPatterns.isEmpty && out.isEmpty
    | .builtin _ => false
    | .conditional _ _ _ _ => false
    | .alias _ _ _ _ _ _ => false

  /-- Unfiltered property lookup (sees private properties). -/
  def lookupProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropAny (props a) k

  /-- Public-only property lookup (for open resolution). -/
  def lookupPublicProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropPublic (props a) k

  /-- Lookup PropDef by name (any visibility). -/
  def lookupPropDefAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefAny? (props a) k

  /-- Lookup PropDef by name (public only). -/
  def lookupPropDefPublic? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefPublic? (props a) k

  /-- True when a conditional algorithm has a branch body defining the given property. -/
  def conditionalBranchesDefineProperty : Algorithm -> Ident -> Bool
    | .conditional _ _ bs _, k => bs.any (fun br => hasPropAny (props br.body) k)
    | _, _ => false

  /-- Wire a child algorithm to its parent's scope context. -/
  def childOf (a : Algorithm) (child : Algorithm) : Algorithm :=
    child.withParent (some (a.asScopeCtx))

  /-- Validate that all branches of a conditional algorithm have the same
      top-level pattern arity.  Returns `none` if valid (or non-conditional),
      `some (expected, actual)` for the first mismatching branch.
      This enforces the uniform top-level arity invariant:
      conditional algorithms are "one algorithm, one outer interface, many branches".

      Enforced in two places: front-ends report it during clause elaboration,
      and the core pre-evaluation validation pass (`runResultM` via
      `validateConditionalBranchArities`) rejects violating ASTs with
      `Error.branchArityMismatch` before any evaluation. -/
  def validateBranchArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs _ =>
        match bs with
        | [] => none
        | b :: rest =>
            let expected := b.pattern.topLevelArity
            if rest.any (fun br => br.pattern.topLevelArity != expected)
            then
              match rest.find? (fun br => br.pattern.topLevelArity != expected) with
              | some bad => some (expected, bad.pattern.topLevelArity)
              | none     => none  -- unreachable
            else none
    | _ => none

  /-- Compute the top-level output arity of an algorithm.
      For user-defined algorithms (Algorithm.mk), this is the number of
      top-level output expressions.  For other forms, returns 0. -/
  def topLevelOutputArity (a : Algorithm) : Nat := a.output.length

  /-- Validate that all branches of a conditional algorithm have the same
      top-level output arity.  Returns `none` if valid (or non-conditional),
      `some (expected, actual)` for the first mismatching branch.
      This enforces the uniform top-level output arity invariant:
      all branches of a conditional algorithm share one output interface.
      Nested internal output structure may vary, but the outer number of
      outputs must remain consistent.

      Enforced in two places: front-ends report it during clause elaboration,
      and the core pre-evaluation validation pass (`runResultM` via
      `validateConditionalBranchArities`) rejects violating ASTs with
      `Error.branchOutputArityMismatch` before any evaluation. -/
  def validateBranchOutputArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs _ =>
        match bs with
        | [] => none
        | b :: rest =>
            let expected := topLevelOutputArity b.body
            if rest.any (fun br => topLevelOutputArity br.body != expected)
            then
              match rest.find? (fun br => topLevelOutputArity br.body != expected) with
              | some bad => some (expected, topLevelOutputArity bad.body)
              | none     => none  -- unreachable
            else none
    | _ => none

  /-- Check whether the property list of an Algorithm.mk contains duplicate
      property names.  Returns the first duplicate name found, or `none`
      if all names are unique.  This enforces the unique property name invariant. -/
  def findDuplicatePropName : Algorithm -> Option Ident
    | .mk _ _ _ ps _ _ => firstDuplicateName (ps.map (·.name))
    | .alias _ _ ps _ _ _ => firstDuplicateName (ps.map (·.name))
    | _ => none
  where
    firstDuplicateName (names : List Ident) : Option Ident :=
      let rec go : List Ident -> List Ident -> Option Ident
        | [],        _    => none
        | n :: rest, seen =>
            if seen.elem n then some n
            else go rest (n :: seen)
      go names []

  /-- Check whether the branch list of an Algorithm.conditional contains
      match-equivalent patterns.  Returns `true` if a duplicate is found.
      This enforces the unique branch pattern invariant. -/
  def hasDuplicateBranchPatterns : Algorithm -> Bool
    | .conditional _ _ bs _ =>
        let rec go : List CondBranch -> Bool
          | [] => false
          | b :: rest =>
              if rest.any (fun br => b.pattern.isMatchEquivalent br.pattern)
              then true
              else go rest
        go bs
    | _ => false
end Algorithm

/-- Enforce the uniform branch arity invariants of one conditional algorithm:
    all branches must share the same top-level pattern arity and the same
    top-level output arity. Mirrors the C# parser's clause-elaboration checks;
    in the Lean model the check runs in the pre-evaluation validation pass. -/
def validateConditionalBranchArities (name : Ident) (a : Algorithm) : EvalM Unit :=
  match Algorithm.validateBranchArities a with
  | some (expected, actual) => .error (Error.branchArityMismatch name expected actual)
  | none =>
      match Algorithm.validateBranchOutputArities a with
      | some (expected, actual) => .error (Error.branchOutputArityMismatch name expected actual)
      | none => pure ()

/-- The one message of an invalid singleton sequence pattern (the singleton rule,
    `ParameterPattern.isSingletonSequenceItems`). C#: the parser's
    `SingletonSequencePattern` diagnostic and the pre-evaluation violation
    `PreEvaluationAstViolation.SingletonSequencePattern` share its wording. -/
def singletonSequencePatternMessage : String :=
  "A sequence pattern with exactly one non-collecting item is invalid: KatLang has no one-item sequence value. Bind the whole value with a plain name, or use the list pattern `[x]` for a one-element list."

/-- The singleton rule over an algorithm's OWN patterns: its explicit parameter
    patterns, or every branch head of a clause family. -/
def Algorithm.hasSingletonSequencePattern : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => ParameterPattern.anyHasSingletonSequenceGroup parameters
  | .builtin _ => false
  | .conditional _ _ branches _ => branches.any (fun branch => branch.pattern.headHasSingletonSequenceGroup)
  | .alias _ _ _ _ _ _ => false

/-- The one message of a parameter-pattern level with more than one collecting
    capture — the parser's wording for a written head. C#:
    `Parser.MultipleCollectingBindingsPerLevelDiagnostic`, shared by the
    pre-evaluation violation `PreEvaluationAstViolation.MultipleCollectingCaptures`. -/
def multipleCollectingBindingsPerLevelMessage : String :=
  "Only one collecting binding is allowed per pattern level."

/-- The third X-02 rule, shared by written/inferred signatures and host-built preflight. -/
def repeatedNameIncludesCollectingMessage : String :=
  "Repeated parameter names cannot include collecting bindings."

/-- The META placement rule's message (CallReference S1, `ParameterPattern.metaViolation?`),
    shared by the parser's `InvalidMetaParameter` report and the pre-evaluation violation
    `PreEvaluationAstViolation.InvalidMetaParameter`. -/
def invalidMetaParameterMessage : String :=
  "`meta` may modify only a plain, fixed parameter name written once at the top level of an ordinary parameter list."

/-- The collector rule over an algorithm's OWN parameter patterns (X-02): some
    pattern level holds more than one collecting capture. -/
def Algorithm.hasMultipleCollectingCaptures : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel parameters
  | .builtin _ => false
  | .conditional _ _ _ _ => false
  | .alias _ _ _ _ _ _ => false

/-- Human-readable constructor kind for diagnostics. -/
def Expr.kind : Expr -> String
  | .param _      => "param"
  | .num _        => "num"
  | .stringLiteral _ => "stringLiteral"
  | .interpolatedString _ _ => "interpolatedString"
  | .boolLiteral _ => "boolLiteral"
  | .unary _ _    => "unary"
  | .binary _ _ _ => "binary"
  | .comparison _ _ => "comparison"
  | .index _ _    => "index"
  | .sequenceConstruct _ _ => "sequenceConstruct"
  | .emptySequence _ => "emptySequence"
  | .sequenceSpread _    => "spread"
  | .listLiteral _ => "listLiteral"
  | .resolve _    => "resolve"
  | .algorithmExpr _ => "algorithmExpr"
  | .capture _    => "capture"
  | .call _ _     => "call"
  | .dotMember _ _ _ _ => "dotCall"

/-- Render an empty-sequence core node by depth for diagnostics. Evaluation
  normalizes repeated ordinary parentheses back to `()`. -/
def emptySequenceText (depth : Nat) : String :=
  String.ofList (List.replicate (depth + 1) '(' ++ List.replicate (depth + 1) ')')

/-- Extract a descriptive name from an open expression for error messages.
  This MINIMAL renderer models only reference forms — a name, a parameter, and the
  structural forms below; every other kind (`.num`, `.binary`, ...) renders as the
  `(kind)` fallback, so C#'s merged `OpenExprName` prints more detail for them. That
  gap is pre-existing and uniform across `.dotCall`, `.sequenceConstruct`,
  `.sequenceSpread`, and `.index` alike — it is a property of this renderer's
  coverage, not of selection.
  A PARAMETER is a reference: it renders as the name written, like a property name
  (C# `ExprNameRenderer` renders `Expr.Param` the same way). Every call frame, branch
  failure and member-access report therefore names the written callee or receiver —
  `Apply(f, x) = f(x)` with a clause family reports `noMatchingBranch "f"` under
  "while evaluating call to f", and `Get(obj) = obj.Q` names `obj` in its
  `localOnlyProperty` report — never a `(param)` placeholder (aligned with C# on
  2026-10-13; until then a parameter fell to the `(kind)` fallback). -/
def openExprName (e : Expr) : String :=
  match e with
  | .resolve n => n
  | .param x => x
  | .dotMember o n _ _ =>
      openExprName o ++ "." ++ n
  -- Selection is source-faithful postfix `target[s1, …, sn]`, never the `(index)`
  -- kind fallback. Every selector sits inside the brackets' own expression list,
  -- so none needs parentheses; a spread TARGET does (`(A*)[0]`), since `A*[0]`
  -- reads back as multiplication. Every unmodelled kind is already
  -- self-delimiting as `(kind)`.
  | .index target selectors =>
      let targetName := openExprName target
      (match target with
       | .sequenceSpread _ => "(" ++ targetName ++ ")"
       | _ => targetName)
        ++ "[" ++ String.intercalate ", " (selectors.map openExprName) ++ "]"
  | .algorithmExpr _ => "(inline library)"
  | .capture _ => "(inline library)"
  -- SequenceConstruct is an internal value node; ';' is not surface syntax,
  -- so render it as one sequence value, never with ';'.
  | .sequenceConstruct a b => "(" ++ openExprName a ++ ", " ++ openExprName b ++ ")"
  -- A spread expression renders in the canonical postfix-marker form.
  | .sequenceSpread a => openExprName a ++ "*"
  -- Empty sequence core nodes render by depth for diagnostics.
  | .emptySequence depth => emptySequenceText depth
  | _ => s!"({Expr.kind e})"            -- * informative fallback using constructor kind

/-- A STATIC PATH (FWD-02): a name, or an argumentless dot edge whose receiver is itself
    a static path or a block — an edge spelled `string` included, since a declared member
    named `string` is selected like any member (Q-17 S-C). Every callable alias target is
    one; the surface pass forms an alias over nothing else. Returns the path's head (a name
    or a block) and its member steps, outermost receiver first.
    C#: `StaticAliasTargets.IsStaticPath`. -/
def Expr.staticAliasPath? : Expr -> Option (Expr × List Ident)
  | .resolve name => some (.resolve name, [])
  | .dotMember receiver member _ none =>
      match receiver with
      | .algorithmExpr block => some (.algorithmExpr block, [member])
      | other => (Expr.staticAliasPath? other).map (fun (head, steps) => (head, steps ++ [member]))
  | _ => none

def Expr.isStaticAliasPath (e : Expr) : Bool := (Expr.staticAliasPath? e).isSome

/-- The message of a callable alias whose target is not a static path (only a host-built
    tree has one). C#: `Evaluator.AliasTargetNotStaticPathMessage`. -/
def aliasTargetNotStaticPathMessage (target : String) : String :=
  s!"callable alias target {target} is not a name or a declared member path"

/-- The message of a callable alias cycle (only a host-built tree has one).
    C#: `Evaluator.AliasCycleMessage`. -/
def aliasCycleMessage : String :=
  "callable alias cycle: an alias target leads back to an alias already on its chain"

/-- The property `name` STATIC lexical lookup selects in `scope` (outermost scope first):
    the innermost scope that declares it, with the scope chain of the selected property's
    value (the scopes up to and including its owner). -/
def staticLexicalLookup? (scope : List Algorithm) (name : Ident) : Option (Algorithm × List Algorithm) :=
  let rec go : List Algorithm -> Option (Algorithm × List Algorithm)
    | [] => none
    | owner :: outerReversed =>
        match Algorithm.lookupPropDefAny? owner name with
        | some prop => some (prop.alg, (owner :: outerReversed).reverse)
        | none => go outerReversed
  go scope.reverse

/-- One STATIC step of a callable alias declared inside `chain` (outermost scope first): the
    callable its target selects by the ownership-first PROPERTY lookup over the alias's own
    declarations and its enclosing scopes, then structural navigation of declared members, with
    that callable's own scope chain. No `open` and no prelude is consulted: a target leaving the
    static chain has no static step. C#: `StaticAliasTargets.TryResolve`. -/
def staticAliasStep? (chain : List Algorithm) (alias : Algorithm) (target : Expr)
    : Option (Algorithm × List Algorithm) :=
  match Expr.staticAliasPath? target with
  | none => none
  | some (head, steps) =>
      let scope := chain ++ [alias]
      let start : Option (Algorithm × List Algorithm) :=
        match head with
        | .resolve name => staticLexicalLookup? scope name
        | .algorithmExpr block => some (block, scope)
        | _ => none
      -- A loaded module is rooted at the prelude (Q-31 H-P): what it declares resolves in a
      -- chain that starts at the module, and the module itself has no enclosing chain.
      (steps.foldl
        (fun acc step => acc.bind fun (value, valueChain) =>
          (Algorithm.lookupPropDefAny? value step).map fun prop =>
            (prop.alg, (if value.isModuleRoot then [] else valueChain) ++ [value]))
        start).map fun (value, valueChain) => (value, if value.isModuleRoot then [] else valueChain)

/-- The STATIC alias chase from the alias `start` declared inside `chain`: whether it leads back
    to an alias already on it (a cycle, only possible in a host-built tree). The chase runs at most
    `fuel` hops — `Algorithm.aliasCount` of the tree, the number of distinct aliases the static
    chase can land on — so a chase still landing on an alias after that many hops has revisited
    one: it is a cycle. C#: `StaticAliasTargets.FindCycle`. -/
def staticAliasCycle (fuel : Nat) (chain : List Algorithm) (start : Algorithm) : Bool :=
  match fuel, start with
  | 0, .alias _ _ _ _ _ _ => true
  | fuel + 1, .alias _ _ _ target _ _ =>
      match staticAliasStep? chain start target with
      | some (next@(.alias _ _ _ _ _ _), nextChain) => staticAliasCycle fuel nextChain next
      | _ => false
  | _, _ => false

/-- The STATIC normalization of the callable `a` declared inside `chain` (outermost scope first):
    `a` itself when it is not an alias, else the callable its chain of static steps
    (`staticAliasStep?`) ends at within `fuel` hops — none when a step leaves the static chain
    (an `open`, the prelude) or the fuel runs out. The surface pass's identity resolution through
    aliases (C#: the recorded `Algorithm.Alias.ResolvedTarget`), here over the static chain only;
    the evaluator's is `resolveAliasTarget`. -/
def staticAliasTarget? : Nat -> List Algorithm -> Algorithm -> Option Algorithm
  | _, _, .mk p ps op pr out id => some (.mk p ps op pr out id)
  | _, _, .builtin b => some (.builtin b)
  | _, _, .conditional p op bs id => some (.conditional p op bs id)
  | 0, _, .alias _ _ _ _ _ _ => none
  | fuel + 1, chain, .alias p op pr target id r =>
      match staticAliasStep? chain (.alias p op pr target id r) target with
      | some (next, nextChain) => staticAliasTarget? fuel nextChain next
      | none => none

mutual
  /-- The number of callable aliases in an algorithm tree — the fuel of the static alias chase
      (`staticAliasCycle`): a chase landing on more aliases than the tree holds has revisited one.
      A host-built parent scope is part of the tree the pre-evaluation pass validates
      (`validateScopeTree`), so its aliases are counted too. -/
  partial def Algorithm.aliasCount : Algorithm -> Nat
    | .mk p _ op pr out _ =>
        ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
          + (pr.map (fun prop => prop.alg.aliasCount)).sum + (out.map Expr.aliasCount).sum
    | .builtin _ => 0
    | .conditional p op branches _ =>
        ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
          + (branches.map (fun branch => branch.body.aliasCount)).sum
    | .alias p op pr target _ _ =>
        1 + ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
          + (pr.map (fun prop => prop.alg.aliasCount)).sum + target.aliasCount

  /-- The callable aliases in a parent scope chain: in each scope's opens and properties, the
      parts the pre-evaluation pass validates (`validateScopeTree`). -/
  partial def ScopeCtx.parentAliasCount : Option ScopeCtx -> Nat
    | none => 0
    | some (.mk parent? _ op pr _ _ _ _) =>
        ScopeCtx.parentAliasCount parent? + (op.map Expr.aliasCount).sum
          + (pr.map (fun prop => prop.alg.aliasCount)).sum

  /-- The callable aliases inside an expression (in its blocks). -/
  partial def Expr.aliasCount : Expr -> Nat
    | .algorithmExpr alg => alg.aliasCount
    | .unary _ operand => operand.aliasCount
    | .binary _ left right => left.aliasCount + right.aliasCount
    | .comparison first links => first.aliasCount + (links.map (fun link => link.operand.aliasCount)).sum
    | .index target selectors => target.aliasCount + (selectors.map Expr.aliasCount).sum
    | .sequenceConstruct left right => left.aliasCount + right.aliasCount
    | .sequenceSpread operand => operand.aliasCount
    | .listLiteral items => (items.map Expr.aliasCount).sum
    | .interpolatedString _ links => (links.map (fun link => link.hole.aliasCount)).sum
    | .capture rows => (rows.map Expr.aliasCount).sum
    | .call fn args => fn.aliasCount + (args.map Expr.aliasCount).sum
    | .dotMember target _ fallback args? =>
        target.aliasCount + fallback.aliasCount + ((args?.getD []).map Expr.aliasCount).sum
    | _ => 0
end

/-- A host-built parent scope chain as the STATIC chain its members are declared in, outermost
    first: each scope a plain algorithm holding its opens and properties. A member of a parent
    scope resolves names through that scope chain, never through the algorithm the scope parents,
    so the alias check (`staticAliasCycle`) chases a member's target through this chain exactly as
    through enclosing algorithms. -/
partial def ScopeCtx.staticChain : ScopeCtx -> List Algorithm
  | .mk parent? _ op pr _ _ _ _ =>
      ((parent?.map ScopeCtx.staticChain).getD []) ++ [Algorithm.mk none [] op pr [] none]

mutual
  /-- Pre-evaluation structural validation over a whole algorithm tree:
      - explicit algorithm parameters only appear on algorithms that define
        output (`explicitParamsRequireOutput`)
      - no parameter pattern or branch pattern contains a one-item sequence
        pattern (the singleton rule; `illegalInEval`
        `singletonSequencePatternMessage`) — a host-built tree cannot give such
        a pattern a meaning the surface language refuses it
      - no parameter-pattern level holds more than one collecting capture (X-02;
        `illegalInEval` `multipleCollectingBindingsPerLevelMessage`): the
        binders allocate a level around ONE movable collector, so a host-built
        tree cannot reach them with a second one
      - conditional algorithms have uniform top-level branch pattern arity and
        uniform top-level branch output arity (`branchArityMismatch`,
        `branchOutputArityMismatch`)
      - every callable alias has a STATIC-PATH target (`Expr.isStaticAliasPath`;
        `illegalInEval` `aliasTargetNotStaticPathMessage`), and the static chase of
        its target never leads back to an alias already on its chain
        (`staticAliasCycle`; `illegalInEval` `aliasCycleMessage`) — only a host-built
        tree can violate either, the surface pass never forms one

      The walk covers the WHOLE tree, including every host-built parent scope an
      algorithm carries (`validateScopeTree`, after the algorithm's own content). The
      evaluator keeps such a scope for an `open` block target
      (`wireOpenBlockToGlobalScope`), so its members are reachable at run time. Owner
      decision, 2026-10-12: they are held to these rules like every other algorithm.
      Formerly the walk never entered a parent scope.

      `name` labels conditional arity diagnostics with the nearest enclosing
      property name; anonymous algorithms report the placeholder
      `conditional`. `chain` is the static scope chain around `a` (outermost
      first) and `aliases` the whole tree's alias count, which the alias check
      reads. C#: `AlgorithmValidation.PreEvaluationValidationWalker`. -/
  partial def validateAlgorithmTree (a : Algorithm) (name : Ident)
      (chain : List Algorithm) (aliases : Nat) : EvalM Unit := do
    -- A loaded module is rooted at the prelude (Q-31 H-P): the static chain its aliases
    -- resolve in restarts at the module, whatever holds it.
    let chain := if a.isModuleRoot then [] else chain
    if a.hasSingletonSequencePattern then
      .error (Error.illegalInEval singletonSequencePatternMessage)
    if a.hasMultipleCollectingCaptures then
      .error (Error.illegalInEval multipleCollectingBindingsPerLevelMessage)
    let inner := chain ++ [a]
    match a with
    | .mk parent? parameters op pr out _ =>
        if let some .repeatedNameIncludesCollecting := ParameterPattern.signatureViolation? parameters then
          .error (Error.illegalInEval repeatedNameIncludesCollectingMessage)
        if (ParameterPattern.metaViolation? parameters).isSome then
          .error (Error.illegalInEval invalidMetaParameterMessage)
        if !parameters.isEmpty && out.isEmpty then
          .error Error.explicitParamsRequireOutput
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for prop in pr do
          validateAlgorithmTree prop.alg prop.name inner aliases
        for expr in out do
          validateExprTree expr inner aliases
        if let some scope := parent? then
          validateScopeTree scope aliases
    | .builtin _ => pure ()
    | .conditional parent? op branches _ =>
        validateConditionalBranchArities name a
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for branch in branches do
          validateAlgorithmTree branch.body name inner aliases
        if let some scope := parent? then
          validateScopeTree scope aliases
    | .alias parent? op pr target _ _ =>
        if !(target.isStaticAliasPath || target.isRuntimeAliasRow) then
          .error (Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target)))
        if staticAliasCycle aliases chain a then
          .error (Error.illegalInEval aliasCycleMessage)
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for prop in pr do
          validateAlgorithmTree prop.alg prop.name inner aliases
        validateExprTree target inner aliases
        if let some scope := parent? then
          validateScopeTree scope aliases

  /-- The pre-evaluation validation of a host-built PARENT scope, and of its own parent:
      its `open` targets and its property algorithms, the parts lexical lookup and `open`
      resolution read at run time. The scope's `output` and `branches` are identity data
      that nothing evaluates, so they are not walked. The members are validated against the
      scope chain (`ScopeCtx.staticChain`), the chain they resolve names in. No front end
      builds such a scope; a host may. C#: `PreEvaluationValidationWalker.VisitParentScopes`. -/
  partial def validateScopeTree (s : ScopeCtx) (aliases : Nat) : EvalM Unit := do
    let chain := s.staticChain
    match s with
    | .mk parent? _ op pr _ _ _ _ =>
        for openExpr in op do
          validateExprTree openExpr chain aliases
        for prop in pr do
          validateAlgorithmTree prop.alg prop.name chain aliases
        if let some outer := parent? then
          validateScopeTree outer aliases

  /-- Traverse expressions so nested block literals and call-argument
      algorithms also satisfy the same pre-evaluation invariants. -/
  partial def validateExprTree (e : Expr) (chain : List Algorithm) (aliases : Nat) : EvalM Unit :=
    match e with
    | .param _ => pure ()
    | .num _ => pure ()
    | .stringLiteral _ => pure ()
    | .interpolatedString _ links =>
        links.forM (fun link => validateExprTree link.hole chain aliases)
    | .boolLiteral _ => pure ()
    | .resolve _ => pure ()
    | .unary _ operand =>
        validateExprTree operand chain aliases
    | .binary _ left right => do
        validateExprTree left chain aliases
        validateExprTree right chain aliases
    | .comparison first links => do
        validateExprTree first chain aliases
        links.forM (fun link => validateExprTree link.operand chain aliases)
    | .index target selectors => do
        validateExprTree target chain aliases
        selectors.forM (fun selector => validateExprTree selector chain aliases)
    | .sequenceConstruct left right => do
      validateExprTree left chain aliases
      validateExprTree right chain aliases
    | .emptySequence _ => pure ()
    | .sequenceSpread operand => do
        validateExprTree operand chain aliases
    | .listLiteral items =>
        items.forM (fun item => validateExprTree item chain aliases)
    | .algorithmExpr alg =>
        validateAlgorithmTree alg "conditional" chain aliases
    | .capture rows =>
        rows.forM (fun row => validateExprTree row chain aliases)
    | .call fn args => do
        validateExprTree fn chain aliases
        args.forM (fun arg => validateExprTree arg chain aliases)
    | .dotMember target _ fallback args? => do
        validateExprTree target chain aliases
        -- The stored lexical fallback is a real child (Resolve/Param for
        -- front-end trees, but hand-built trees could hide algorithms in it),
        -- so the validation walk covers it like every other reference.
        validateExprTree fallback chain aliases
        match args? with
        | some args => args.forM (fun arg => validateExprTree arg chain aliases)
        | none => pure ()
end

/-- The pre-evaluation validation of one algorithm tree (`validateAlgorithmTree` over the
    whole tree, its alias count read once). -/
def validateExplicitParamOutputInvariant (a : Algorithm) (name : Ident := "conditional") : EvalM Unit :=
  validateAlgorithmTree a name [] a.aliasCount

/-- The pre-evaluation validation of a program expression (`validateExprTree`). -/
def validateExplicitParamOutputInvariantExpr (e : Expr) : EvalM Unit :=
  validateExprTree e [] e.aliasCount

namespace ScopeCtx
  def parent : ScopeCtx -> Option ScopeCtx
    | .mk p _ _ _ _ _ _ _ => p
  def params : ScopeCtx -> List Ident
    | .mk _ ps _ _ _ _ _ _ => ps
  def opens : ScopeCtx -> List Expr
    | .mk _ _ op _ _ _ _ _ => op
  def props : ScopeCtx -> List PropDef
    | .mk _ _ _ ps _ _ _ _ => ps
  /-- The owning output rows, retained for scope reconstruction. Runtime declaration IDs
      distinguish owners even when these rows (or clause binders) have the same shape. -/
  def output : ScopeCtx -> List Expr
    | .mk _ _ _ _ out _ _ _ => out
  def activation : ScopeCtx -> Option Nat
    | .mk _ _ _ _ _ _ value _ => value
  def withActivation (value : Nat) : ScopeCtx -> ScopeCtx
    | .mk p ps op props out branches _ id => .mk p ps op props out branches (some value) id
  partial def declaration : ScopeCtx -> ScopeCtx
    | .mk p ps op props out branches _ id =>
        .mk (p.map declaration) ps op props out branches none id
  def ancestor? (scope : ScopeCtx) : Nat -> Option ScopeCtx
    | 0 => some scope
    | n + 1 => scope.parent >>= fun p => ancestor? p n
  def declarationId : ScopeCtx -> Option PropertyIdentity
    | .mk _ _ _ _ _ _ _ id => id
end ScopeCtx

namespace Algorithm
  /-- Create a temporary algorithm from a ScopeCtx for open resolution. -/
  def forOpens (sc : ScopeCtx) : Algorithm :=
    .mk (some sc) [] (ScopeCtx.opens sc) [] []

  /-- Whether an algorithm is ineligible as an open provider: a parameterized algorithm
      (explicit or inferred parameters) or a clause family (even with a zero-arity branch). Such an
      algorithm is not an `open` provider under MOD-04 — `open` imports a namespace and never creates
      an activation. An alias reaching this test is a structural CARRIER or a RUNTIME reference
      (OD-C, M4★: `openStructure` normalized every static reference to its target first): its own
      namespace — a carrier's own public declarations, a runtime reference's own (empty) one —
      never its output's. (C#: `Evaluator.RequiresArguments`). -/
  def requiresArguments : Algorithm -> Bool
    | .conditional _ _ _ _ => true
    | .alias _ _ _ _ _ _ => false
    | a => !(params a).isEmpty

  /-- Lift a single expression into an algorithm whose output is that expression. -/
  def ofExpr (e : Expr) : Algorithm :=
    Algorithm.mk none [] [] [] [e]  -- no params, no opens, no properties
end Algorithm

--------------------------------------------------------------------------------
-- Lexical lookup (direct parents only)
--------------------------------------------------------------------------------

partial def lookupInParentsDirect (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropAny (ScopeCtx.props sc) name with
  | some child => some (Algorithm.withParent (some sc) child)
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirect sc' name
      | none     => none

/-- Direct lexical lookup: local + parent chain only (no opens).
    Used to resolve open expressions safely (avoids cycles). -/
partial def lookupLexicalDirect (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupProp a name with
  | some child => some (Algorithm.childOf a child)
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirect sc name
    | none    => none

--------------------------------------------------------------------------------
-- Member accessibility (the local-only law)
--------------------------------------------------------------------------------

/-- The scope owning parameter `name` as seen from `scope`: the nearest level, that scope
    itself first, whose parameters bind the name — the same nearest-owner walk that
    elaborated the captured reference (C#: `Evaluator.RequiredParameterOwner`). -/
partial def requiredParameterOwner? (scope : ScopeCtx) (name : Ident) : Option ScopeCtx :=
  if (ScopeCtx.params scope).contains name then some scope
  else
    match ScopeCtx.parent scope with
    | some parent => requiredParameterOwner? parent name
    | none => none

/- Runtime declaration/activation identity is not an exported-property cache determinant.
    Preserve the established structural cache law (C#: StructuralOwnerIdentity). -/
mutual
  partial def cacheExprShape : Expr -> Expr
    | .param n => .param n
    | .resolve n => .resolve n
    | .num n => .num n
    | .stringLiteral text => .stringLiteral text
    -- The key keeps the head and every text: two strings with the same holes but different
    -- literal text are different shapes.
    | .interpolatedString head links =>
        .interpolatedString head (links.map (fun link => { link with hole := cacheExprShape link.hole }))
    | .boolLiteral b => .boolLiteral b
    | .emptySequence depth => .emptySequence depth
    | .unary op e => .unary op (cacheExprShape e)
    | .binary op a b => .binary op (cacheExprShape a) (cacheExprShape b)
    | .comparison first links =>
        .comparison (cacheExprShape first)
          (links.map (fun link => { link with operand := cacheExprShape link.operand }))
    | .index a bs => .index (cacheExprShape a) (bs.map cacheExprShape)
    | .sequenceConstruct a b => .sequenceConstruct (cacheExprShape a) (cacheExprShape b)
    | .sequenceSpread e => .sequenceSpread (cacheExprShape e)
    | .listLiteral es => .listLiteral (es.map cacheExprShape)
    | .capture es => .capture (es.map cacheExprShape)
    | .algorithmExpr a => .algorithmExpr (cacheAlgorithmShape a)
    | .call f args => .call (cacheExprShape f) (args.map cacheExprShape)
    | .dotMember target name fallback args => .dotMember (cacheExprShape target) name
        (cacheExprShape fallback) (args.map (List.map cacheExprShape))

  partial def cacheAlgorithmShape : Algorithm -> Algorithm
    | .builtin b => .builtin b
    | .mk parent parameters opens props output _ =>
        .mk (parent.map cacheScopeShape) parameters (opens.map cacheExprShape)
          (props.map cachePropertyShape) (output.map cacheExprShape)
    | .conditional parent opens branches _ =>
        .conditional (parent.map cacheScopeShape) (opens.map cacheExprShape)
          (branches.map fun b => { b with body := cacheAlgorithmShape b.body })
    | .alias parent opens props target _ reference =>
        .alias (parent.map cacheScopeShape) (opens.map cacheExprShape)
          (props.map cachePropertyShape) (cacheExprShape target) none reference

  partial def cacheScopeShape : ScopeCtx -> ScopeCtx
    | .mk parent _ opens props _ _ _ _ =>
        .mk (parent.map cacheScopeShape) [] (opens.map cacheExprShape)
          (props.map cachePropertyShape) [] [] none none

  partial def cachePropertyShape (p : PropDef) : PropDef :=
    { p with alg := cacheAlgorithmShape p.alg }
end

/-- Known declaration identities compare only the binder view and parent chain. Walking
    or printing their complete property/output graphs at every lookup is unnecessary.
    TOTAL (S5, October 2026; formerly `partial`): structural recursion over the finite parent
    chain, matching the constructor so that the parent is visibly a subterm. Its equation is
    the former body's, field accessor for field accessor
    (`same_declaring_scope_equation`, `KatLangArityLaws/RepeatedNameLaws.lean`), so the
    function is unchanged. -/
def sameDeclaringScope (left right : ScopeCtx) : Bool :=
  match left, right with
  | .mk leftParent leftParams _ _ _ _ _ (some a), .mk rightParent rightParams _ _ _ _ _ (some b) =>
      a == b && leftParams == rightParams &&
      match leftParent, rightParent with
      | none, none => true
      | some p, some q => sameDeclaringScope p q
      | _, _ => false
  | _, _ => reprStr left.declaration == reprStr right.declaration

/-- Whether the `actual` activation chain satisfies the `required` one, level by level: an
    unactivated required level accepts any activation. TOTAL (S5, October 2026; formerly
    `partial`): structural over the finite parent chains, with the former body as its
    equation (`compatible_activations_equation`). -/
def compatibleActivations (required actual : Option ScopeCtx) : Bool :=
  match required, actual with
  | none, none => true
  | some (.mk requiredParent _ _ _ _ _ requiredActivation _),
    some (.mk actualParent _ _ _ _ _ actualActivation _) =>
      (requiredActivation.isNone || requiredActivation == actualActivation) &&
        compatibleActivations requiredParent actualParent
  | _, _ => false

def siteScope? (ctx : EvalCtx) : Option ScopeCtx :=
  ctx.headScope.orElse (fun _ => ctx.head?.map Algorithm.asScopeCtx)

partial def activeDeclaration? (required : ScopeCtx) (level : Option ScopeCtx) : Option ScopeCtx :=
  match level with
  | none => none
  | some scope =>
      if sameDeclaringScope required scope && compatibleActivations (some required) (some scope)
      then some scope else activeDeclaration? required scope.parent

def scopeInContext (a : Algorithm) (ctx : EvalCtx) : ScopeCtx :=
  let scope := a.asScopeCtx
  if scope.activation.isSome then scope
  else (activeDeclaration? scope (siteScope? ctx)).getD scope

def childOfInContext (parent child : Algorithm) (ctx : EvalCtx) : Algorithm :=
  child.withParent (some (scopeInContext parent ctx))

partial def scopeChainContains (level : Option ScopeCtx) (owner : ScopeCtx) : Bool :=
  match level with
  | none => false
  | some scope =>
      (sameDeclaringScope scope owner && scope.activation.isSome &&
        compatibleActivations (some owner) (some scope)) ||
      scopeChainContains scope.parent owner

def lexicalChainContains (ctx : EvalCtx) (owner : ScopeCtx) : Bool :=
  scopeChainContains (siteScope? ctx) owner

def recordParameterActivation (names : List Ident) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat := do
  let state <- get
  let id := state.lexicalActivations.size
  let activation : ParameterActivation := {
    values := env.filter (fun b => names.contains b.fst)
    needs := ctx.needEnv.filter (fun b => names.contains b.fst)
    bindingContext := ctx.bindingContext }
  set { state with
    lexicalActivations := state.lexicalActivations.push activation }
  pure id

def enterAlgorithmBody (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM EvalCtx := do
  if a.params.isEmpty && a.props.all (fun p => p.exposure.isExported) then pure (ctx.push a)
  else
    let id <- recordParameterActivation a.params ctx env
    pure { ctx.push a with headScope := some (a.asScopeCtx.withActivation id) }

/-- The body entry of a PROPERTY-STYLE demand (CACHE-OWNER-D1, owner decision October 23 2026):
    exactly `enterAlgorithmBody`, except that an activation it records retains `bindingContext` —
    the context of the declaring activation the read resolved (`EvalBody.evalPropertyDemandCounted`)
    — instead of the consumer's. The returned context keeps the consumer's own binding context,
    so nothing but the owner's recorded identity changes: its need tier, values, call stack and
    head scope are `enterAlgorithmBody`'s (`enterPropertyOwnerBody_own_context`). An explicit call
    never enters through here; it binds a fresh context (`EvalCtx.bindParameters`). C#:
    `Evaluator.EnterAlgorithmBody` with an inherited binding identity. -/
def enterPropertyOwnerBody (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (bindingContext : Nat) : EvalM EvalCtx := do
  let entered <- enterAlgorithmBody a { ctx with bindingContext := bindingContext } env
  pure { entered with bindingContext := ctx.bindingContext }

def capturedParameterActivation? (name : Ident) (ctx : EvalCtx) : EvalM (Option ParameterActivation) := do
  match ctx.head?, siteScope? ctx with
  | some site, some scope =>
      if site.params.contains name then pure none
      else
        let id := scope.parent >>= fun parent =>
          (requiredParameterOwner? parent name).bind ScopeCtx.activation
        match id with
        | none => pure none
        | some id => pure ((<- get).lexicalActivations[id]?)
  | _, _ => pure none

def parameterContext (name : Ident) (ctx : EvalCtx) (env : ValEnv) : EvalM (EvalCtx × ValEnv) := do
  match <- capturedParameterActivation? name ctx with
  | none => pure (ctx, env)
  | some activation =>
      let parameterCtx := { ctx with needEnv := activation.needs }
      pure (parameterCtx, activation.values)

/-- Whether `target` is a parameter bound to a SUPPLIED CELL (every parameter an ordinary
    call binds under Model C), looked up exactly as the value-position `param` arm of
    `evalCounted` finds it (through the captured activation, `parameterContext`). The
    ordinary-dot `string` intrinsic reads such a receiver through that cell instead of
    re-judging its callable by the zero-argument law (CALL-06; `evalDotCallCounted`).
    C#: the need-cell test that opens `Evaluator.EvalDotStringReceiverAlgOutput`. -/
def hasSuppliedParameterCell (target : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Bool := do
  match target with
  | .param x =>
      let (parameterCtx, _) <- parameterContext x ctx env
      pure (lookupAssoc x parameterCtx.needEnv).isSome
  | _ => pure false

/-- A parameter's CALLABLE as its supplied cell's TYPED projection outcome (META-S3-1, L2): the cell
    found exactly as `supplyNeed` finds it, projected by `project`; a parameter with no cell has no
    identity. The outcome is never re-classified: a projection FAILURE of any kind propagates
    (`parameter_projection_failure_propagates`) and only `none` is absence. Production:
    `projectParameterCallable` (`project = projectNeedCallable`). -/
def projectParameterWith (project : Nat → EvalM (Option Algorithm)) (x : Ident) (ctx : EvalCtx) :
    EvalM (Option Algorithm) := do
  let activation ← capturedParameterActivation? x ctx
  match lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) with
  | some address => project address
  | none => pure none

def supplyNeed (source : Expr) (caller : EvalCtx) (values : ValEnv) : EvalM Nat := do
  if let .param name := source then
    let activation <- capturedParameterActivation? name caller
    if let some address := lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) then
      return address
  allocateNeed (.expression source caller values)

/-- The KNOWN collector slice a spread operand transports (NEED-07/08): the slice of a
    parameter bound to a supplied collector cell, found exactly as `supplyNeed` finds a
    parameter's cell. It allocates nothing — any other operand is evaluated by the spread
    itself (`formNeedSupplySourced`). C#: the `Slice` test in `FormSpreadSupplySlot`. -/
def spreadCollectorSlice? (operand : Expr) (caller : EvalCtx) : EvalM (Option (List Nat)) := do
  if let .param name := operand then
    let activation <- capturedParameterActivation? name caller
    if let some address := lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) then
      let some cell := (<- get).needs[address]? | throw Error.badArity
      if let .collector slice := cell.suspension then return some slice
  pure none

/-- THE member-accessibility law, applied AFTER a member has been selected — by structural
    dot access (`evalDotCallCounted`, `resolveDotReceiver`), by a dotted `open` path step
    (`resolveAlgForOpen`), and by an `open`-provided name (`lookupOpenProperties`); direct
    lexical hits never consult it, because a name found on the site's own chain is by
    construction inside every owner of what it captures.

    An exported member is accessible everywhere. Captured requirements retain exact owner
    positions across shadowing; names alone use the legacy nearest-owner host convention.
    Each owner must be the same declaration and activation in the site's lexical chain,
    including captured ancestors of a static provider. Reads use that owner's snapshot
    rather than a shadowing dynamic binding. An absent owner refuses the access.
    `.localConditional` is never assigned to a `PropDef`; declared by a host, it is
    inaccessible. C#: `Evaluator.IsAccessibleFrom`. -/
def memberAccessible? (ctx : EvalCtx) (container : Algorithm) (p : PropDef) : Bool :=
  match p.exposure with
  | .exported => true
  | .localConditional => false
  | .localCapturedAncestorParams required =>
      match siteScope? ctx with
      | none => false
      | some _ =>
          let declaringScope := scopeInContext container ctx
          match p.requiredOwnerDepths with
          | some requirements => requirements.all fun (name, depth) =>
              match depth >>= declaringScope.ancestor? with
              | some owner => owner.params.contains name && lexicalChainContains ctx owner
              | none => false
          | none => required.all fun name =>
              match requiredParameterOwner? declaringScope name with
              | some owner => lexicalChainContains ctx owner
              | none => false


def wireToCaller (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match ctx.callStack.head? with
  | some caller => childOfInContext caller a ctx
  | none        => a

/-- Wires a selected branch body under its clause family for one call, publishing the
    matched pattern binders as the family scope's `params`: the body itself declares no
    parameters (binders bind by pattern matching), so this is the level at which
    `memberAccessible?` finds the owner of a binder-capturing member.
    C#: `Evaluator.ChildOfConditionalCall`. -/
def wireSelectedBranchBody (callee : Algorithm) (body : Algorithm) (binderNames : List Ident)
    (ctx : EvalCtx) (env : ValEnv) : EvalM Algorithm := do
  let id <- recordParameterActivation binderNames ctx env
  pure (body.withParent (some (.mk callee.parent binderNames callee.opens callee.props
    callee.output callee.branches (some id) callee.declarationId)))

def wireOpenBlockToGlobalScope (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match Algorithm.parent a, ctx.callStack.reverse.head? with
  | none, some globalScope => Algorithm.childOf globalScope a
  | _, _ => a

-- Dot-call helpers
--------------------------------------------------------------------------------

/-- Convert a numeric Result to its canonical string representation.
    Only atomic numeric values are supported; other forms raise typeMismatch.
    Canonical representation: Int.repr (e.g., 123 → "123", -5 → "-5", 0 → "0"). -/
def resultToString (r : Result) : EvalM Result :=
  match r with
  | .atom n => pure (Result.str (toString n))
  | _ => .error (Error.typeMismatch "builtin property `string` expects a numeric receiver")

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------

mutual
  /-- The diagnostic text of a value: a number in Lean's `Int` rendering, a string quoted
      with `'` (no escaping), a Boolean's spelling, a structure's items comma-separated in
      its delimiters, and the fixed descriptions of a call reference and an argument view
      (whose plan is never inspected). Structural recursion (R3′, October 2026). -/
  def resultDiagnosticString : Result -> String
    | .atom value => toString value
    | .str value => "'" ++ value ++ "'"
    | .bool value => Result.boolText value
    | .sequenceValue items => "(" ++ String.intercalate ", " (resultDiagnosticStrings items) ++ ")"
    | .listValue items => "[" ++ String.intercalate ", " (resultDiagnosticStrings items) ++ "]"
    | .callRef _ => "a call reference"
    | .argView _ => "an argument view"

  /-- `items.map resultDiagnosticString` (`PatternHelpers.resultDiagnosticStrings_eq_map`). -/
  def resultDiagnosticStrings : List Result -> List String
    | [] => []
    | item :: rest => resultDiagnosticString item :: resultDiagnosticStrings rest
end

/-- How a diagnostic names one value that failed an operand, condition, or
    predicate requirement: the value KIND first, then the value itself.
    C#: `Evaluator.DescribeOperand`. -/
def operandDescription : Result -> String
  | .sequenceValue items => s!"a sequence value with {items.length} sequence element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.sequenceValue items)}"
  | .str value => "a string: '" ++ value ++ "'"
  | .bool value => s!"a Boolean value: {Result.boolText value}"
  | .atom value => s!"numeric value {value}"
  | .listValue items => s!"a list value with {items.length} element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.listValue items)}"
  | .callRef _ => "a call reference"
  | .argView _ => "an argument view"

/-! CallReference S1 diagnostics (October 2026). C#: `CallReferenceMessages`. -/

/-- `R.Invoke` without an argument list: the intrinsic is never a property read. -/
def invokeRequiresArgumentListMessage : String :=
  "`Invoke` is a call-reference operation, not a property: write `R.Invoke()`."

/-- `x.Invoke()` whose receiver VALUE is not a call reference. -/
def invokeRequiresCallReferenceMessage (value : Result) : String :=
  s!"`Invoke` requires a call reference, got {operandDescription value}"

/-- Text conversion (interpolation) of a value that contains a call reference. -/
def callReferenceHasNoTextMessage : String :=
  "A call reference has no text: use a value computed from it, for example `R.Invoke()`."

/-- A run result (or another host-facing value) that contains a call reference. -/
def callReferenceLeavesRunMessage : String :=
  "A call reference cannot leave its run: return a value computed from it, for example `R.Invoke()`."

/-! META-S3-1 diagnostics (October 2026). C#: `Evaluator.AlgorithmProjection.cs`. -/

/-- `x.Algorithm` whose receiver VALUE is not a call reference. -/
def algorithmRequiresCallReferenceMessage (value : Result) : String :=
  s!"`Algorithm` requires a call reference, got {operandDescription value}"

/-- The absence report of a captured callee without CALLABLE identity (NEED-06). -/
def capturedCalleeDescription : String := "captured callee"

/-! CallReference S2 diagnostics (October 2026). C#: `Evaluator.CallPlans.cs`. -/

/-- `R.Arguments(…)`: the view is a property of the reference, never an operation. -/
def argumentsIsPropertyMessage : String :=
  "`Arguments` is a call-reference property, not an operation: write `R.Arguments`."

/-- `x.Arguments` whose receiver VALUE is not a call reference. -/
def argumentsRequiresCallReferenceMessage (value : Result) : String :=
  s!"`Arguments` requires a call reference, got {operandDescription value}"

/-- A spread that would open an argument view into VALUES (any spread outside an argument
    list, or an inner star of a stacked spread). -/
def argumentViewSpreadMessage : String :=
  "An argument view spreads only into an argument list, as `F(R.Arguments*)`; select its values with `R.Arguments[i]`."

/-- A collection builtin other than `count`, `first` and `last` over an argument view. -/
def argumentViewUnsupportedMessage (builtinName : String) : String :=
  s!"An argument view supports only `count`, `first`, `last`, selection and an argument spread, not `{builtinName}`."

/-- Refuse a value that contains a call reference with `message` (`typeMismatch`); every
    reference-free value passes unchanged. -/
def requireCallRefFree (message : String) (value : Result) : EvalM Unit :=
  if value.containsCallRef then .error (Error.typeMismatch message) else pure ()

/-- Coerce a Result to Int. Every present value that is not a number — a
    string, a Boolean, a sequence (`()` included) or a list — is the value-KIND
    failure `typeMismatch` (Q-27): a selector, a `range` bound, a `repeat`
    count and a Math argument of the wrong kind are never an arity error.
    C#: `Evaluator.ExpectInt`. -/
def expectInt (r : Result) : EvalM Int :=
  match r with
  | .str _ => .error (Error.typeMismatch "Expected a number, got a string")
  | .bool _ => .error (Error.typeMismatch "Expected a number, got a Boolean value")
  | _ => match Result.asInt? r with
    | some n => pure n
    | none   => .error (Error.typeMismatch s!"Expected a number, got {operandDescription r}")

/-- An ordinary structural pattern that received a value of another kind —
    a sequence pattern given a list or a scalar, a list pattern given a
    sequence or a scalar — fails its binding with this `typeMismatch`, naming
    the written pattern and the value received (STRUCTURAL PATTERN DELIMITERS
    SELECT THE VALUE KIND THEY DESTRUCTURE). A right-kind value with the wrong
    number of elements is the group's ordinary `arityMismatch` instead. In a
    clause family neither is raised: a mismatch only rejects the clause.
    C#: `Evaluator.StructuralPatternKindMismatch`. -/
def structuralPatternKindMismatch (pattern : ParameterPattern) (value : Result) : Error :=
  match pattern with
  | .listValue _ =>
      Error.typeMismatch
        s!"list pattern `{pattern.displayName}` expects a list value, but received {operandDescription value}"
  | _ =>
      Error.typeMismatch
        s!"sequence pattern `{pattern.displayName}` expects a sequence value, but received {operandDescription value}"

/-- The numeric-scalar operand rule of the arithmetic operators and the ordering
    comparisons, keyed by the operator's spelling. C#: `Evaluator.RequireNumericScalarOperand`. -/
def requireNumericScalarOperandOf (operatorSymbol : String) (side : String) (value : Result) : EvalM Int :=
  match Result.asInt? value with
  | some number => pure number
  | none => .error (Error.typeMismatch
      s!"operator `{operatorSymbol}` expects numeric scalar operands, but the {side} operand was {operandDescription value}")

def requireNumericScalarOperand (op : BinaryOp) (side : String) (value : Result) : EvalM Int :=
  requireNumericScalarOperandOf op.symbol side value

/-- The ordering comparisons share the arithmetic operators' numeric-scalar operand rule. -/
def requireNumericComparisonOperand (op : ComparisonOp) (side : String) (value : Result) : EvalM Int :=
  requireNumericScalarOperandOf op.symbol side value

/-- The logical operators `and` / `or` / `xor` require a Boolean value on
    BOTH sides: there is no numeric truthiness, so a number, string, sequence
    value, or list operand is a value-kind error naming the operand.
    C#: `Evaluator.RequireBooleanOperand`. -/
def requireBooleanOperand (op : BinaryOp) (side : String) (value : Result) : EvalM Bool :=
  match Result.asBool? value with
  | some b => pure b
  | none => .error (Error.typeMismatch
      s!"operator `{op.symbol}` expects Boolean operands, but the {side} operand was {operandDescription value}")

/-- The ONE message for every position that REQUIRES a Boolean value — an
    `if` condition, a `filter` predicate result, a `while` continuation flag:
    it names the role and the value kind actually supplied, so a number in a
    predicate position is reported as the value-kind mismatch it is, never as
    an arity or numeric error. C#: `Evaluator.BooleanRequiredMessage`. -/
def booleanRequiredMessage (role : String) (value : Result) : String :=
  s!"{role} must be a Boolean value (true or false), but was {operandDescription value}"

/-- Structural KatLang value equality used by `==` and `!=`.
    Numbers compare by value, strings by exact value, and sequence values by
    length plus recursive pairwise equality — exactly the derived structural
    `BEq` on `Result`. Different value kinds compare unequal rather than raising
    a type mismatch, so equality is total over all values and never type-errors.
    Ordering operators and arithmetic keep their numeric-scalar-only path via
    `requireNumericScalarOperand`. -/
def resultValueEq (a b : Result) : Bool := a == b

/-- Enumerate the inclusive integer span for `range(start, stop)`.
    The direction is inferred automatically:
    - ascending when `start <= stop`
    - descending when `start > stop`

    Because KatLang's Lean core represents numeric values as `Int`, the
    `range` builtin is integer-only by construction at the specification level. -/
def inclusiveRange (start stop : Int) : List Int :=
  if start <= stop then
    (List.range (Int.toNat (stop - start + 1))).map (fun i => start + Int.ofNat i)
  else
    (List.range (Int.toNat (start - stop + 1))).map (fun i => start - Int.ofNat i)

/-- Insert an integer into an ascending sorted list, preserving duplicates. -/
def insertIntAsc (value : Int) : List Int -> List Int
  | [] => [value]
  | head :: tail =>
      if value <= head then
        value :: head :: tail
      else
        head :: insertIntAsc value tail

/-- Ascending numeric sort used by `order` and `orderDesc`. -/
def sortIntsAsc : List Int -> List Int
  | [] => []
  | head :: tail => insertIntAsc head (sortIntsAsc tail)

/-- Descending numeric sort used by `orderDesc`. -/
def sortIntsDesc (xs : List Int) : List Int :=
  (sortIntsAsc xs).reverse

structure CallableCallItem where
  need? : Option Nat := none
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  source? : Option Expr := none
  /-- The callable the item NAMES, beside the value-side `algorithm?`: for a supplied
      cell whose VALUE demand failed, the cell's CALLABLE projection (unless the
      written slot is a parameter — `demandSequenceBuiltinCallItemValue`; C#
      `VariadicCallItem.Callable`, set by `FinishNeedCallItemDemand`). -/
  callable? : Option Algorithm := none
  deriving Repr

/-- The algorithm a call item NAMES: the identity the zero-argument value-demand law
    judges — the projected `callable?` when the item has one, otherwise the
    value-side `algorithm?`, which a VALUE demand evaluates. -/
def CallableCallItem.named? (item : CallableCallItem) : Option Algorithm :=
  item.callable?.or item.algorithm?

/-- The context of NEED-04's value verdict: the occurrences of one repeated
    parameter name received unequal VALUE contributions (the binder's
    `badArity`, unchanged by Q-27). C#: `Evaluator.RepeatedParameterContext`. -/
def repeatedParameterContext (name : Ident) : String :=
  s!"repeated parameter '{name}' requires equal arguments"

/-- Callable identity includes its declaration and the captured lexical activation chain.
    Comparing identities does not evaluate either algorithm or consult its value cache. -/
def sameRepeatedCallableIdentity (left right : Algorithm) : Bool :=
  match left, right with
  | .builtin a, .builtin b => a == b
  | .builtin _, _ | _, .builtin _ => false
  | _, _ =>
      left.declarationId == right.declarationId &&
      (match left.parent, right.parent with
       | none, none => true
       | some a, some b => sameDeclaringScope a b
       | _, _ => false) &&
      compatibleActivations left.parent right.parent &&
      compatibleActivations right.parent left.parent

/-- Builtin collection-item view of the bound collection argument: opens
  exactly one outer sequence or exact-list boundary to its immediate items;
  any other value supplies itself as one item (a scalar is a one-element
  collection). Never recursive — nested sequence values and nested list
  values stay intact as single items.
  Applied strictly AFTER ordinary fixed parameter binding, to the already
  bound `collection` parameter only — argument boundaries are never altered
  before binding. Call parameter binding never uses this view, assignment
  deconstruction opens its received value through the spread view
  (`Result.spreadItems`), and a structural pattern opens only its own kind.
  C#: `BuiltinCollectionItems`. -/
def builtinCollectionItems : Result -> List Result
  | .sequenceValue elems => elems
  | .listValue elems => elems
  | value => [value]

/-- Compatibility fallback for manually constructed core conditionals.
  Surface clause elaboration should already route eligible single-branch
  ordinary clause groups through `Algorithm.elaborateClauseGroup`, producing
  `Algorithm.mk` directly. This helper intentionally keeps only the stricter
  flat multi-binder `.conditional` core shape call-compatible with ordinary
  user algorithms, so evaluator fallback semantics do not silently broaden to
  bare single-binder conditionals. -/
def flatBinderUserEquivalent? (callee : Algorithm) : Option Algorithm :=
  match callee with
  | .conditional _ _ [branch] _ =>
      match Pattern.flatBinderParamNames? branch.pattern with
      | some ps =>
          let wiredBody := Algorithm.childOf callee branch.body
          some (Algorithm.mk
            (Algorithm.parent wiredBody)
            (Algorithm.normalParameters ps)
            (Algorithm.opens wiredBody)
            (Algorithm.props wiredBody)
            (Algorithm.output wiredBody))
      | none => none
  | _ => none

/-- ONE zero-supply acceptability rule: whether an ORDINARY call that supplies
    ZERO argument slots can bind this callable. It is derived from the very
    binder/dispatch semantics such a call uses, never from parameter-list
    emptiness:

    * a user algorithm accepts iff its top-level pattern list's
      `ParameterPattern.minimumSuppliedSlots` is zero — so `Only(*xs)` accepts
      (`Only()` binds `xs = []`) while `Head(x, *rest)`, `Tail(*rest, z)`,
      `P((x, *rest))`, `P([x])` and `Pair(x, y)` do not. A COLLECTING parameter
      contributes ZERO required slots; a nested pattern still consumes one, and
      binds ONE supplied value of its own kind, never none;
    * a clause family accepts iff some branch's top-level pattern has arity
      zero — exactly the branch the family dispatcher (`selectNeedFamilyBranch`)
      selects for an empty supply. A flat multi-binder core equivalent
      (`flatBinderUserEquivalent?`) always has at least two parameters, so it
      never accepts;
    * a BUILTIN never accepts (`sum()` is an arity error). Its rejection stays
      owned by `evalBuiltinValueCounted` / `builtinArityError b 0`, which is the
      very report `sum()` produces, so `zeroArgumentDemandError?` deliberately
      does not intercept builtins.

    C#: `Evaluator.AcceptsZeroSuppliedArguments`. -/
def Algorithm.acceptsZeroSuppliedArguments : Algorithm -> Bool
  | .builtin _ => false
  | .conditional _ _ branches _ =>
      branches.any (fun branch => Pattern.topLevelArity branch.pattern == 0)
  | a => ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns a) == 0

/-- Value-position access to a conditional algorithm cannot select a branch,
    so it must fail instead of silently forcing the conditional's empty output
    list. Mirrors the no-argument dot-call dispatch: a flat multi-binder core
    equivalent reports its ordinary call arity, and any other conditional
    reports `noMatchingBranch`. Returns `none` for non-conditional algorithms. -/
def conditionalValueAccessError? (name : String) (a : Algorithm) : Option Error :=
  match a with
  | .conditional _ _ _ _ =>
      match flatBinderUserEquivalent? a with
      | some simple => some (Error.arityMismatch (Algorithm.params simple).length 0)
      | none => some (Error.noMatchingBranch name)
  | _ => none

/-- Attach context to any error raised by `m`. -/
def withCtx (ctx : String) (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error err => .error (Error.withContext ctx err)

/-- Attach property context specifically to a missing-output failure.
    Other errors are preserved unchanged. -/
def withMissingOutputCtx (ctx : String) (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error (.missingOutput origin) => .error (.withContext ctx (.missingOutput origin))
    | .error err => .error err

/-- Any missing output, whatever its origin and context frames (the category test). -/
def isMissingOutputError : Error -> Bool
  | .missingOutput _ => true
  | .withContext _ inner => isMissingOutputError inner
  | _ => false

/-- The failure is the OWN missing output of the computation whose outcome it is (Q-36): raised
    by that computation's output check and carried through its context frames only. -/
def isOwnMissingOutputError : Error -> Bool
  | .missingOutput .own => true
  | .withContext _ inner => isOwnMissingOutputError inner
  | _ => false

/-- Convert an own missing output without discarding the demand's named context (Q-36). -/
def Error.asSpreadMissingOutput : Error -> Error
  | .missingOutput .own => .spreadMissingOutput
  | .withContext ctx inner => .withContext ctx inner.asSpreadMissingOutput
  | err => err

/-- The same failure as part of a CONSUMING computation's outcome (Q-36): a missing output in it
    is `nested`; its context frames, and every other error, are unchanged. -/
def Error.nestMissingOutput : Error -> Error
  | .missingOutput _ => .missingOutput .nested
  | .withContext ctx inner => .withContext ctx inner.nestMissingOutput
  | err => err

/-- Run `m` as a SUBORDINATE computation (Q-36): a missing output it fails with is `nested` in
    the outcome of the computation that ran it (`Error.nestMissingOutput`). Every other outcome,
    an incomplete one included, is unchanged. C#: `Evaluator.NestMissingOutput`. -/
def withNestedMissingOutput (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error err => .error err.nestMissingOutput

/-- `Error.nestMissingOutput` exactly when `nested` holds; the error itself otherwise. -/
def Error.nestMissingOutputWhen (nested : Bool) (err : Error) : Error :=
  if nested then err.nestMissingOutput else err

/-- Run `m` as a read that is SUBORDINATE exactly when `nested` holds (Q-36 with M4★: a VALUE read
    that crosses a structural carrier, `AliasTerminal.nested`): `withNestedMissingOutput` when it
    does, and otherwise `m`'s own outcome unchanged. One combinator, whatever the flag, so the read it
    wraps is written once. C#: the `CrossesCarrier ? NestMissingOutput(read) : read` terminal reads of
    `Evaluator.Aliases.cs`. -/
def withMissingOutputNesting (nested : Bool) (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error err => .error (err.nestMissingOutputWhen nested)

/-- The empty sequence value expression `()`. -/
def emptyResultExpr : Expr :=
  .emptySequence 0

/-- Recover the top-level values emitted at one algorithm boundary from a
    counted result.

    A sequence value emitted as a single top-level result stays intact, while a
    multi-output result is expanded back to its top-level items. -/
def countedTopLevelValues : CountedResult -> List Result
  | (_, 0) => []
  | (value, 1) => [value]
  | (value, _) => value.toItems

/-- Combine collected top-level output slots into one value. A single slot is
  returned as-is so useful sequence structure is preserved; multiple slots form
  one sequence value. Unlike `Result.normalize`, this does NOT singleton-collapse
  or recursively renormalize slot values -- slots are already evaluated values. -/
def combineOutputSlots : List Result -> Result
  | [r] => r
  | rs => Result.sequenceValue rs

/-- The receiver-independent half of `selectPosition` (CallReference S2): the selector VALUE must
    be a number (`typeMismatch`, `expectInt`) naming a non-negative position (`badIndex`). An
    argument view's selection runs it BEFORE the view's supply is prepared
    (`selectViewWith`); `selectPosition_eq_selectorIndex` relates the two. -/
def selectorIndex (selector : Result) : EvalM Nat := do
  let n <- expectInt selector
  if n < 0 then
    .error Error.badIndex
  else
    pure (Int.toNat n)

/-- VARIADIC POSTFIX SELECTION — ONE supplied selector (October 2026): validate the
    selector VALUE against the receiver and select that position. The checks are the
    retired colon form's, unchanged: a selector that is not a number is the kind failure
    `typeMismatch` (`expectInt`), a negative one names no position, and a position past
    the receiver's positional view (`Result.select?` over `Result.projectionItems`, the
    ONE immediate view `count`, `first` and `last` read) is `badIndex`. The stored
    element is returned whole — never opened. C#: `Evaluator.SelectPosition`. -/
def selectPosition (receiver : Result) (selector : Result) : EvalM Result := do
  let n <- expectInt selector
  if n < 0 then
    .error Error.badIndex
  else
    match Result.select? receiver (Int.toNat n) with
    | some selected => pure selected
    | none => .error Error.badIndex

/-- VARIADIC POSTFIX SELECTION — the supplied selectors (October 2026). Each supplied
    selector is DEMANDED, validated and selected LEFT TO RIGHT (`selectPosition`), and
    the first failure — of a demand or of a position — ends the selection: no later
    selector is demanded (`selectWith_stops_at_first_failure`). Repeated selectors
    repeat stored values, never a computation; the receiver is a value already in hand.
    TOTAL and parametrized by the demand, so its laws are theorems; the `.index` arm of
    `evalCounted` instantiates it with `fun cell => Prod.fst <$> demandNeedRecursive cell`
    over the supply formed by `NeedSupply.addresses evalSupplySpread`.
    C#: the Index case of `Evaluator.EvalExpressionSpineCounted` and its async twin. -/
def selectWith {α : Type} (demand : α -> EvalM Result) (receiver : Result) :
    List α -> EvalM (List Result)
  | [] => pure []
  | cell :: rest => do
      let selected <- selectPosition receiver (<- demand cell)
      let tail <- selectWith demand receiver rest
      pure (selected :: tail)

/-- The value of a completed selection: the selected values captured by ordinary
    sequence normalization of the RESULT GROUPING only (`combineOutputSlots`) — zero
    selections are `()`, one is the selected value itself, several are one sequence of
    the selected values kept whole (a selected `()` or `[]` stays an element). It
    crosses the ordinary value boundary (`Result.valueCount`) and keeps no record of how
    many selectors produced it. C#: `Evaluator.MakeCheckedSequenceCapture`. -/
def selectionResult (selected : List Result) : CountedResult :=
  let value := combineOutputSlots selected
  (value, Result.valueCount value)

/-- Materialize a collection-producing builtin's kept/projected items as ONE
    list value. Unlike canonical arity capture (ordinary
    construction via `Result.normalize`, `combineOutputSlots`), the list
    boundary is exact: zero items form `[]`, a
    single kept item forms `[item]` (the one-item collection boundary is NEVER
    erased, so `take(((1, 2), (3, 4)), 1)` yields `[(1, 2)]`), and item
    internals are never renormalized, dropped, or flattened -- nested sequence
    values and nested list values stay exact elements. The emitted count is
    always 1: a list value is one visible value (`Result.valueCount`),
    including the empty list `[]`.
    C#: `MakeCollectionListResult`. -/
def makeCollectionListResult (items : List Result) : CountedResult :=
  (Result.listValue items, 1)

/-- Collect the item segment assigned to a collecting binding as ONE list value.

    KatLang distinguishes three item-supply operations by receiver purpose:

    - `capture : Supply -> Value` — ordinary value/output capture, the
      normalizing boundary `Result.normalize (Result.sequenceValue xs)`
      (singleton erasure applies: `x = 1, 2, 3` is `(1, 2, 3)`, one supplied
      item is itself);
    - `collect : Supply -> ListValue` — THIS operation: a collecting binding (collecting parameter)
      materializes exactly the assigned items as one list
      (`collectSegment [] = []`, `collectSegment [v] = [v]`, never erased);
    - `spread : Value -> Supply` — the spread marker (`Result.spreadItems`), which
      opens one sequence OR list boundary.

    THE EXACT COLLECTOR LAW (September 2026): every collecting binding —
    single collecting parameters, mixed prefix/collecting/suffix parameter
    lists, nested pattern collectors, and deconstruction collecting bindings —
    binds exactly the items allocated to it and never inspects their values —
    since Model C (2026-10-02) as a lazy collector cell over the allocated supply
    cells (`bindNeedLevel`), whose VALUE demand materializes exactly this list
    through `makeCollectionListResult` (`demandNeedRecursive` through the total
    `NeedDemand.materialize` helper); this helper remains the
    value-level definition the laws state. A collector opens nothing: one written
    argument is one item whatever its value, so `Coll((1, 2))` is
    `[(1, 2)]`, `Coll([1, 2])` is `[[1, 2]]`, `Coll(())` is `[()]`, and
    `Coll([])` is `[[]]` — only the caller's explicit spread turns a value into
    several items (`Coll((1, 2)*)` and `Coll([1, 2]*)` are `[1, 2]`).
    Deconstruction (through the spread view) and nested structural patterns
    (a sequence pattern a sequence value, a list pattern a list value) open
    their one value BEFORE allocation, as explicit structural syntax, and the
    collector then collects the opened items exactly. The round trip
    `Result.spreadItems (collectSegment xs) = xs` is the value-level face of
    collecting-parameter forwarding: `Forward(*items) = Target(items*)`
    re-supplies exactly the collected items — since Model C by transferring the
    collector's own cells, unforced (FWD-01, NEED-07/08) — with no hidden
    raw-supply metadata. A collecting value is one visible value, so its emitted count is
    always 1 (including `[]`). C#: the collector cell `Evaluator.CollectorCell`,
    materializing through `MakeCollectionListResult` (`CollectSegment` and
    `CreateCollectingCapture` were deleted by Model C). -/
def collectSegment (items : List Result) : Result :=
  Result.listValue items

/-- Re-count a counted result at a public property/call/builtin RESULT boundary.

    A property/call boundary always returns ONE value: the body may internally
    produce an item supply of count 0, 1, or many, but the caller observes the
    same structural value with emitted count `Result.valueCount value` (0 for the
    empty sequence value, otherwise 1). A multi-output body therefore becomes one
    sequence value at the boundary; only an explicit caller-site spread `value*`
    re-spreads it (via `Result.spreadItems`, which reads the value, not this count).

    This re-counts without normalizing or rebuilding the value; ordinary value
    construction has already normalized redundant unary empty structure. It is
    applied only to public result boundaries — `map`/`reduce` callback results
    (HO-03, Q-25) and the completed `while`/`repeat` result
    (`loopResultCounted`, Q-26) included — never to internal
    body/root output accumulation (`evalAlgOutputCountedCore`) or a loop step's
    own row supply (`evalAlgOutputSlots`), which must keep their multi-item
    counts. (Collecting parameter storage needs no re-count:
    collecting binding collects one exact list value, so its stored count is already
    1.) Lexical zero-arg property access (`evalCounted .resolve`) and the `if`
    builtin already perform this same re-count inline; this helper generalizes
    it. -/
def reCountValueBoundary (r : CountedResult) : CountedResult :=
  (r.fst, Result.valueCount r.fst)

/-- Build the canonical empty sequence value for an `emptySequence` node.
    Repeated ordinary parentheses around `()` do not create higher-order empty
    sequence values. -/
def buildEmptySequenceValue (_ : Nat) : Result :=
  Result.sequenceValue []

-- No builtin is valid as a bare zero-argument value; every builtin requires a
-- call. (The empty sequence value is written `()`, not a builtin.)
def evalBuiltinValueCounted : Builtin -> EvalM CountedResult
  | b => .error (builtinArityError b 0)

/-- Flatten a `sequenceConstruct` subtree into its ordered leaves without changing
    sequence-value/block values inside those leaves. -/
partial def sequenceConstructLeavesLoop : List Expr -> List Expr -> List Expr
  | [], acc => acc.reverse
  | current :: rest, acc =>
      match current with
      | .sequenceConstruct left right => sequenceConstructLeavesLoop (left :: right :: rest) acc
      | leaf => sequenceConstructLeavesLoop rest (leaf :: acc)

def sequenceConstructLeaves (expr : Expr) : List Expr :=
  sequenceConstructLeavesLoop [expr] []

/-- Peel directly-nested unary sequence spreads down to the innermost operand.
    (Evaluation peels with `peelSequenceSpreadLayers`, which also counts the
    written layers, and applies them with the total checked opening `openSpreadItems`, which is
    `reopenSpreadLayers` wherever no opening exposes an argument view.)
    Stacked spread is COMPOSITIONAL (`A**` agrees with `(A*)*`) — each extra written
    layer re-captures the previous layer's item supply into one value
    (`Result.normalize ∘ Result.sequenceValue`, the ordinary expression
    capture) and spreads that captured value (`reopenSpreadItems`), applied iteratively
    (stack-safe for deep `A**` chains, matching the C# evaluator). A
    multi-item supply re-captures as a sequence whose spread restores the
    same items, so extra layers are fixed points there
    (`[[1, 2], [3, 4]]**` supplies the two inner lists unchanged); only a
    LONE structured item singleton-collapses at the capture and lets the
    next layer open one more boundary (`[[7]]**` is `7`, like
    `([[7]]*)*`). This is NOT binary spine flattening: there is no right
    operand, it only unwraps the single-operand chain. -/
partial def peelSequenceSpread : Expr -> Expr
  | .sequenceSpread operand => peelSequenceSpread operand
  | e => e

/-- Peel directly-nested spreads while counting the written layers.
    Returns the innermost non-spread operand and the number of `.sequenceSpread` layers
    (at least 1 when called on a spread node). -/
partial def peelSequenceSpreadLayers : Expr -> Nat -> Expr × Nat
  | .sequenceSpread operand, n => peelSequenceSpreadLayers operand (n + 1)
  | e, n => (e, n)

/-- ONE further written spread layer over an item supply (October 2026): the
    previous layer's supply is captured by ORDINARY capture (`Result.normalize ∘
    Result.sequenceValue`) and the captured value is spread (`Result.spreadItems`) —
    `spread(capture(items))`. TOTAL, so its laws are theorems (`KatLangArityLaws.lean`
    § Repeated spread over the real model): a zero- or multi-item canonical supply is a fixed
    point whose members are never opened, and only a LONE item lets the next layer open that
    item's own boundary (`reopen_spread_opens_only_a_lone_item`); the grouped spelling's
    capture boundary — the `.capture` arm's shallow `combineOutputSlots` over the inner
    spread's slots — computes exactly this step (`grouped_spread_layer_is_reopen`), so once the
    operand is evaluated `A**` and `(A*)*` perform the same value operation (the total evaluator
    core routes both spellings so — a kernel term of `EvalBody.evalSequenceSpreadOperandValue` /
    `EvalBody.evalCounted` since R7, guard-checked by CoreTests `RepeatedSpread`; no theorem states
    the two production routes equal, and their C# RESOURCE charges differ). `evalSequenceSpreadCounted` applies it through the checked
    `openSpreadItems`, which is `reopenSpreadLayers` wherever no opening exposes an argument view
    (`openSpreadItems_eq_reopen`).
    C#: the layer loop `Evaluator.OpenSpreadLayers` (of `EvalSequenceSpreadCounted` and its async
    twin), which
    re-captures with the SHALLOW `MakeCheckedSequenceCapture` (`CombineOutputSlots` after a
    resource reservation); that shallow rule, modelled LOCALLY by `shallowSpreadLayersForLaw`,
    computes the same supply on canonical supplies
    (`shallow_spread_layers_agree_on_canonical_supply`) — a proof about the rule, not the C#
    code, whose correspondence rests on inspection and tests. -/
def reopenSpreadItems (items : List Result) : List Result :=
  (Result.normalize (Result.sequenceValue items)).spreadItems

/-- `layers` further written spread layers over an item supply: `reopenSpreadItems` applied
    `layers` times, one boundary per written star — never all boundaries at once. This is the
    former local `reopen` of `evalSequenceSpreadCounted`, extracted unchanged so its laws are
    theorems; it is tail-recursive, so deep `A***…` chains stay stack-safe. -/
def reopenSpreadLayers : Nat -> List Result -> List Result
  | 0, items => items
  | n + 1, items => reopenSpreadLayers n (reopenSpreadItems items)

/-- The VALUE openings of a spread (CallReference S2): the operand VALUE `v` opened by the first
    written star and every further star's re-capture opened by the next — exactly
    `reopenSpreadLayers n v.spreadItems` (`openSpreadItems_eq_reopen`) — except that an
    ARGUMENT VIEW is never opened into values: any star that would open one is the
    `typeMismatch` `argumentViewSpreadMessage`. Only an argument supply's LAST star transports a
    view (`openSupplySpread`). TOTAL. C#: the layer loop `Evaluator.OpenSpreadLayers`. -/
def openSpreadItems : Nat -> Result -> Except Error (List Result)
  | _, .argView _ => .error (Error.typeMismatch argumentViewSpreadMessage)
  | 0, v => .ok v.spreadItems
  | n + 1, v => openSpreadItems n (Result.normalize (Result.sequenceValue v.spreadItems))

/-- What one written spread contributes to an ARGUMENT SUPPLY (CallReference S2): its opened
    items, or — when the value its LAST star opens is an argument view — that view's plan, whose
    original cells the supply transports (`NeedSupply.slot`, `SpreadSupply.cells`). -/
inductive SpreadOpening where
  | items (values : List Result)
  | view (plan : Nat)
  deriving Repr

/-- The supply openings of a spread: `openSpreadItems`, except that the LAST star's view is
    `view` (`openSupplySpread_eq_items` when nothing opened is a view). TOTAL. -/
def openSupplySpread : Nat -> Result -> Except Error SpreadOpening
  | 0, .argView a => .ok (.view a)
  | 0, v => .items <$> openSpreadItems 0 v
  | _ + 1, .argView _ => .error (Error.typeMismatch argumentViewSpreadMessage)
  | n + 1, v => openSupplySpread n (Result.normalize (Result.sequenceValue v.spreadItems))

/-- The counted result of a spread expression over its final item supply: the supply's
    ordinary capture, emitting the supply's item count (the expression-level face of
    `spread : Value -> Supply`; consumers that read the expression as one value re-count at
    their value boundary, and a spread ROW — or a spread leaf of the internal join — recovers the
    supply's NORMALIZED items, the items themselves on a canonical supply, through
    `countedTopLevelValues`, `countedTopLevelValues_spreadSupplyResult`).
    `evalSequenceSpreadCounted` returns it. C#: the final layer of
    `Evaluator.OpenSpreadLayers` (`CountedResult(capture, items.Count)`). -/
def spreadSupplyResult (items : List Result) : CountedResult :=
  (Result.normalize (Result.sequenceValue items), items.length)

def describeSequenceItem : Result -> String
  | .atom n => s!"numeric value {n}"
  | .str s => s!"string value {repr s}"
  | .bool b => s!"Boolean value {Result.boolText b}"
  | .sequenceValue [] => "empty sequence value"
  | .sequenceValue _ => "sequence value"
  | .listValue [] => "empty list value"
  | .listValue _ => "list value"
  | .callRef _ => "call reference"
  | .argView _ => "argument view"

def numericSequenceItemErrorContext (b : Builtin) (index : Nat) (item : Result) : String :=
  s!"{builtinDisplayName b} expects each collection element to be a single numeric value; item {index} was {describeSequenceItem item}"

/-- Shared collected view for current collection-builtin evaluation.
    This is the bound collection argument's post-binding one-level item view;
    nested sequence values stay intact and recursive flattening remains the
    job of `atoms`. -/
structure CollectedSequenceBuiltinInput where
  items : List Result
  deriving Repr

def CollectedSequenceBuiltinInput.totalItemCount
    (input : CollectedSequenceBuiltinInput) : Nat :=
  input.items.length

structure PreparedSequenceBuiltinInput where
  items : List Result
  numericItems? : Option (List Int) := none
  deriving Repr

/-- One bound control argument of a collection builtin. A CALLBACK control carries
    no value — it was never value-evaluated — only its callable: a supplied cell's
    address (`.needAlgorithm`, projected when the builtin invokes it), or, for an
    argument without a cell (the hand-built fixture seam), the algorithm it invokes
    (`.algorithm`). A VALUE control carries the value its one demand established. -/
inductive PreparedSequenceBuiltinSuffixArg where
  | algorithm (value : Algorithm)
  | needAlgorithm (address : Nat)
  | value (value : Result)
  | wholeNumber (value : Int)
  deriving Repr

structure BoundSequenceBuiltinArguments where
  preparedInput : PreparedSequenceBuiltinInput
  iterationItems : List CountedResult
  suffixArgs : List PreparedSequenceBuiltinSuffixArg
  /-- The plan of an ARGUMENT VIEW bound as the whole collection of `count`, `first` or `last`
      (CallReference S2): the builtin then reads the view's cells, not a collection value. -/
  view? : Option Nat := none
  deriving Repr

/-- The collection builtins an argument view supports as its WHOLE collection (CallReference
    S2): `count` reads the cardinality of the plan's supply, `first`/`last` select a cell. Every
    other collection builtin refuses a view (`argumentViewUnsupportedMessage`) instead of
    reading it as a one-element collection or materializing it. -/
def Builtin.readsArgumentView : Builtin -> Bool
  | .countBuiltin | .firstBuiltin | .lastBuiltin => true
  | _ => false

/-- One argument a builtin receives. Every argument the evaluator builds is a SUPPLIED
    CELL (`need?`): the builtin arm of `evalResolvedCallCounted` passes the call's
    supply (`formNeedSupplySourced`, explicit spreads already opened), a builtin loop
    step its state cells and a builtin callback its element cells; a VALUE slot
    demands the cell (`demandNeedRecursive`) and an invoking slot projects it
    (`projectNeedCallable`), while `algorithm` is an inert placeholder. An argument
    WITHOUT a cell is the direct-invocation seam that hand-built fixtures use
    (`CoreTests/ParityGuards.lean`, the slot-role laws): a VALUE slot then demands
    `algorithm` through the zero-argument law, and an invoking slot calls it.
    C#: `Evaluator.ResolvedArgumentAlgorithm`. -/
structure ResolvedArgumentAlgorithm where
  need? : Option Nat := none
  algorithm : Algorithm
  /-- The argument's WRITTEN slot at this call: the builtin arm of
      `evalResolvedCallCounted` records it from the supply formation
      (`formNeedSupplySourced` — the slot as written; for a transported collector
      slice, each cell's own original source; none for a spread's ready items), and a
      builtin VALUE slot's rejection report reads it: a written parameter reports its
      established failure (CALL-06), and any other written source keys the
      zero-argument law's report (`sequenceBuiltinValueDemandErrorWith?`). For an
      argument WITHOUT a cell it is the demand-site identity `zeroArgumentDemandError?`
      reports through. C#: `ResolvedArgumentAlgorithm.Source`. -/
  source? : Option Expr := none
  deriving Repr

/-- Collection-builtin call items: each argument the builtin receives, wrapped for
    binding, evaluating NOTHING (CALL-02, CALL-03, NEED-01..05). Every argument is
    already a supplied cell (`need?`): a builtin loop step's state cells, a builtin
    callback's element cells, or a call's supply, formed before this, left to right
    (`formNeedSupplySourced`, the builtin arm of `evalResolvedCallCounted`) — where a
    SPREAD slot's operand was evaluated and supplied exactly its spread items, which
    take the roles of the positions they land on, its failure, of any kind, the CALL's
    failure, raised before any later slot and before the arity check, never one
    phantom supplied item (SUP-01, SUP-02, CALL-04), so `take(Bad*)` is `Bad`'s
    failure, not an arity error, and `map([], Bad*)` fails although `map` would never
    invoke a callback — and every other slot stayed its suspended cell. Each item's ROLE
    (`SequenceBuiltinMetadata.slotRole`) decides what the builtin later does with it:
    a CALLBACK is projected on the CALLABLE channel only when the builtin invokes it
    per element (CALL-03, HO-04), so an unused callback runs no body, has no effect,
    cannot fail and cannot recurse (`map([], A)` never reads `A`, exactly as
    `Run(f) = repeat(f(5), 0)` / `Run(A)` never runs `A`); a VALUE slot is demanded only when the builtin
    executes it, after the arity check, through its cell and at most once, so no later
    read retries it (`reduce`'s `initial` included, HO-04;
    `demandSequenceBuiltinCallItemValue`); a SURPLUS slot is never demanded: the call
    reports its arity error first (NEED-05). An argument without a cell (the
    hand-built fixture seam) is never evaluated standalone either: a VALUE slot judges
    its algorithm by the ONE zero-argument law first. *(Until Model C, 2026-10-02, a
    value slot was demanded here, before the arity check, its ordinary failure retained
    on the item, and a surplus slot was prepared like a value slot's eager attempt.)*
    C#: `BuildCallableCallItems`. -/
def collectSequenceCallableCallItems (args : List ResolvedArgumentAlgorithm) : List CallableCallItem :=
  args.map fun arg => { algorithm? := some arg.algorithm, source? := arg.source?, need? := arg.need? }

def intPow (b : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => b * intPow b n

/-- Negative integer exponents follow the C# reference semantics:
    - `0 ^ negative` is a domain error — the runtime's rule is "a zero base
      rejects ANY exponent below zero, integral or not" (`0 ^ -0.5` and
      `Math.Pow(0, -2.5)` fail exactly like `0 ^ -1`); the Int core can only
      reach the integer instance of that rule and shares its message,
    - bases `1` and `-1` have exact integer reciprocals,
    - any other base yields a fractional reciprocal (for example `2 ^ -1 = 0.5`
      in the decimal runtime), which the Int-valued Lean core cannot represent.

    Instead of silently truncating fractional reciprocals to `0`, the core
    raises an explicit error. This is a documented limitation of the integer
    numeric model, not a behavior the runtime should copy. -/
def negativeIntPow (base exponent : Int) : EvalM Result :=
  if base == 0 then
    .error (Error.illegalInEval "zero cannot be raised to a negative exponent")
  else if base == 1 then
    pure (Result.atom 1)
  else if base == -1 then
    pure (Result.atom (if exponent % 2 == 0 then 1 else -1))
  else
    .error (Error.illegalInEval
      s!"`{base} ^ {exponent}` produces a fractional result, which the integer-valued Lean core cannot represent")

/-- Predicate defining which expression forms are allowed in open position
    **after elaboration**.  Only structural references to libraries are permitted.

    OpenForm is the *post-elaboration* set of permitted open expressions.
    Surface-level `load('url')` calls (represented as `Call(Resolve("load"), ...)`)
    may appear in source open lists, but the load elaboration pass MUST rewrite
    every such call into `Expr.algorithmExpr` before open resolution or validation runs.

    Note: the C# parser produces DotCall for all dot syntax (e.g. `Lib.Sub`).
    `DotCall(obj, name, none)` is the canonical form for open dot paths.
    `DotCall(obj, name, some args)` is rejected as an invalid open form.
    After normalization and load elaboration, opens contain only the forms
    listed below.

    Additionally, the exact-syntax sugar `open 'url'` is desugared to
    `open load('url')` at parse time, so raw string literals never appear
    in the canonical open list.  The load elaboration pass then rewrites
    `Call(Resolve("load"), ...)` into `Block(parsed module)` as usual.

    Open target semantics here accept INDIVIDUAL targets only: block,
    resolve, and argumentless dot-call.  The C# parser parses the
    source-level open declaration as one comma-separated target list
    (`open A, B, C`) and validates each target as an individual
    Lean-compatible form before evaluation; `;`/adjacency are not open
    separators.  Spread is not a valid open target: a spread-marked
    target (`open A*`) parses to a spread expression and is rejected by
    open-form validation, so no accepted SequenceSpread ever reaches open
    resolution. -/
inductive OpenForm where
  | algorithmExpr : Algorithm -> OpenForm
  | resolve : Ident -> OpenForm
  | dotCall : Expr -> Ident -> OpenForm     -- a.f (no-arg dotCall)

def Expr.openForm? : Expr -> Option OpenForm
  | .algorithmExpr a => some (.algorithmExpr a)
  -- A capture is a value boundary, not algorithm/namespace identity, so a
  -- surviving capture (`open (M, N)`, `open (M*)`) is NOT an open form: it is
  -- rejected by open-form validation with badOpenForm, exactly like a
  -- spread-marked target. (A redundant group is no capture: the C# parser
  -- erases it, so `open (M)` IS `open M`.)
  | .resolve n       => some (.resolve n)
  -- Only argumentless dot paths are open forms. The C# front end rejects a
  -- Grace-marked open target such as `open A~.B` before Lean encoding; valid
  -- graced dot sources otherwise encode as the same dotMember as ordinary dot.
  -- This classifies the OUTER node; `resolveAlgForOpen` recurses through the
  -- receiver, so a path whose head is no open form (`open 5.N`) is rejected
  -- there. The C# front end refuses such a head statically (`BadOpenForm`).
  | .dotMember o n _ none => some (.dotCall o n)
  | _                => none          -- capture, argument-bearing dot forms, call, and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

/-- Diagnostic expression names use KatLang source syntax; `.index` renders as
  postfix selection `target[s1, …, sn]`. Selection is postfix and binds tighter
  than unary and every binary operator, so those operands need parentheses in
  target position: `-A[0]` reads as `-(A[0])`, so the target of a selection over
  a unary must render `(-A)[0]`. A spread target renders `(A*)[0]`, because
  `A*[0]` reads back as the multiplication `A * [0]`. Postfix targets are
  left-associative and render faithfully bare (`A[0][1]`, `F(x)[0]`, `A.B[0]`).
  The selectors sit inside the brackets' own expression list and never need
  parentheses. C#: `ExprNameRenderer` (the Index arm). -/
def indexTargetNeedsParens : Expr -> Bool
  | .unary _ _    => true
  | .binary _ _ _ => true
  | .comparison _ _ => true
  | .sequenceSpread _ => true
  | .num v       => decide (v < 0)
  | _             => false

/-- Precedence tiers of the diagnostic-name renderer — the ONE parenthesization
  rule: a rendered name must read back as the AST it was rendered from, so an
  operand is parenthesized exactly when it binds LOOSER than the position it is
  written in. The tiers mirror the surface parser's ladder (loosest to
  tightest): `or` < `xor` < `and` < prefix `not` < the one comparison tier
  (`< > <= >= == !=`) < additive < multiplicative < prefix `-` < `^` < postfix.
  C#: `ExprNameRenderer.BindingTier` and the slot tiers below. -/
def orTier : Nat := 1
def xorTier : Nat := 2
def andTier : Nat := 3
def notTier : Nat := 4
def comparisonTier : Nat := 5
def additiveTier : Nat := 6
def multiplicativeTier : Nat := 7
def unaryMinusTier : Nat := 8
def powerTier : Nat := 9
def postfixTier : Nat := 10
def atomTier : Nat := 11

def binaryOperatorTier : BinaryOp -> Nat
  | .or => orTier
  | .xor => xorTier
  | .and => andTier
  | .add | .sub => additiveTier
  | .mul | .div | .idiv | .mod => multiplicativeTier
  | .pow => powerTier

/-- How tightly an expression binds when rendered bare. Prefix forms take their
  operator's tier (a negative literal renders with a leading minus, so it reads
  back as a prefix minus); postfix forms and the self-delimiting spellings
  (leaves, captures, lists, blocks, the parenthesized internal join) never
  rebind. C#: `ExprNameRenderer.BindingTier`. -/
def bindingTier : Expr -> Nat
  | .binary op _ _ => binaryOperatorTier op
  | .comparison _ [] => atomTier
  | .comparison _ _ => comparisonTier
  | .unary .not _ => notTier
  | .unary .minus _ => unaryMinusTier
  | .num v => if v < 0 then unaryMinusTier else atomTier
  | .index _ _ | .dotMember _ _ _ _ | .call _ _ | .sequenceSpread _ => postfixTier
  | _ => atomTier

/-- The tier a binary operator's LEFT operand is written at: the operator's own
  tier for the left-associative operators (an equal-tier left operand reads back
  unchanged), the postfix tier for `^`, whose base is postfix-level — a unary
  base or a negative literal must keep its parentheses, or `-a ^ b` would read
  back as `-(a ^ b)`, and `(a ^ b) ^ c` would read back right-associated.
  C#: `ExprNameRenderer.LeftOperandTier`. -/
def leftOperandTier (op : BinaryOp) : Nat :=
  match op with
  | .pow => postfixTier
  | _ => binaryOperatorTier op

/-- The tier a binary operator's RIGHT operand is written at: one above the
  operator for the left-associative operators (`a - (b - c)` keeps its
  parentheses), the unary tier for `^`, whose exponent re-enters the unary
  level (`a ^ -b` and `a ^ b ^ c` read back with the same AST).
  C#: `ExprNameRenderer.RightOperandTier`. -/
def rightOperandTier (op : BinaryOp) : Nat :=
  match op with
  | .pow => unaryMinusTier
  | _ => binaryOperatorTier op + 1

/-- A chain operand is written at the additive tier: a nested chain (`(a < b) == c`
  is not the chain `a < b == c`), a `not`, and the logical operators keep their
  parentheses; arithmetic, powers, prefix minus, and postfix forms read back bare.
  C#: `ExprNameRenderer.PushComparisonOperand`. -/
def comparisonOperandTier : Nat := additiveTier

/-- The tier a prefix operator's operand is written at: a `not` operand keeps its
  parentheses only when it binds looser than `not` (`not (a and b)`; a comparison
  chain reads back bare — `not a < b` IS `not (a < b)`), a minus operand when it
  binds no tighter than the prefix tier itself (`-(a + b)`, `-(a < b)`, `-(not a)`,
  `-(-a)`; a power reads back bare — `-a ^ b` IS `-(a ^ b)`).
  C#: `ExprNameRenderer.PushDiagnosticUnaryOperand`. -/
def unaryOperandTier : UnaryOp -> Nat
  | .not => notTier
  | .minus => unaryMinusTier + 1

def parenthesizeWhenLooser (slotTier : Nat) (operand : Expr) (name : String) : String :=
  if bindingTier operand < slotTier then "(" ++ name ++ ")" else name

/-- Whether a string's text can be written as a single-quoted literal (no quote and no line
    break). C#: `ExprNameRenderer.CanWriteSingleQuoted`. -/
def canWriteSingleQuoted (text : String) : Bool :=
  !(text.any fun c => c == '\'' || c == '\n' || c == '\r')

/-- The text of a double-quoted string as KatLang source spells it: `\`, `"`, a line feed and
    a tab escaped and braces doubled; a carriage return, which no KatLang string can spell, is
    shown as `\r`. C#: `ExprNameRenderer.EscapeDoubleQuotedText`. -/
def escapeDoubleQuotedText (text : String) : String :=
  String.join (text.toList.map fun c =>
    match c with
    | '\\' => "\\\\"
    | '"' => "\\\""
    | '\n' => "\\n"
    | '\t' => "\\t"
    | '\r' => "\\r"
    | '{' => "{{"
    | '}' => "}}"
    | other => other.toString)

/-- Whether an interpolation hole's operand-shape name could BEGIN with a brace: a block at the
    left end of the operator and postfix spine (`{...}.X`, `{...} + 2`, the block itself). Such a
    hole is written with spaces, `"{ {...}.X }"`, so `{{` never reads back as a literal brace.
    Conservative — a space inside a hole never changes it. C#:
    `ExprNameRenderer.MayRenderLeadingBrace`. -/
partial def holeMayRenderLeadingBrace : Expr -> Bool
  | .algorithmExpr _ => true
  | .binary _ left _ => holeMayRenderLeadingBrace left
  | .comparison first _ => holeMayRenderLeadingBrace first
  | .index target _ => holeMayRenderLeadingBrace target
  | .dotMember target _ _ _ => holeMayRenderLeadingBrace target
  | .call fn _ => holeMayRenderLeadingBrace fn
  | .sequenceSpread operand => holeMayRenderLeadingBrace operand
  | _ => false

/-- The diagnostic expression name (C#: `ExprNameMode.DiagnosticName`). Operators
  render bare, and every operand keeps parentheses exactly where the precedence
  ladder needs them (`bindingTier` against the slot tiers above), so the text
  reads back as the AST it was rendered from — nested binaries, comparison
  chains, and prefix operators included. -/
partial def exprDiagnosticName : Expr -> String
  | .param name => name
  | .num value => toString value
  -- A string renders as source: single-quoted when its text can be written that way,
  -- otherwise double-quoted with its escapes (C#: `ExprNameRenderer`).
  | .stringLiteral value =>
      if canWriteSingleQuoted value then "'" ++ value ++ "'"
      else "\"" ++ escapeDoubleQuotedText value ++ "\""
  -- An interpolated string renders as written: each text run re-escaped, each hole in
  -- operand shape, spaced when its name could begin with a brace. No rendered expression
  -- writes a hole-level `:` (selection renders brackets), so a hole never needs grouping.
  -- C#: `PushInterpolationLink`.
  | .interpolatedString head links =>
      "\"" ++ escapeDoubleQuotedText head
        ++ String.join (links.map (fun link =>
            let holeName := exprDiagnosticName link.hole
            let hole :=
              if holeMayRenderLeadingBrace link.hole then "{ " ++ holeName ++ " }"
              else "{" ++ holeName ++ "}"
            hole ++ escapeDoubleQuotedText link.text))
        ++ "\""
  | .boolLiteral value => Result.boolText value
  -- A prefix operator's operand is parenthesized when it binds looser than the
  -- operator's slot (`unaryOperandTier`): `-(a + b)`, `-(not a)`, `-(-a)`,
  -- `not (a and b)`; `-a ^ b` and `not a < b` read back bare with the same AST.
  | .unary op operand =>
      let operandName := parenthesizeWhenLooser (unaryOperandTier op) operand (exprDiagnosticName operand)
      (match op with
       | .minus => "-"
       | .not => "not ") ++ operandName
  -- A binary node's operands are written at `leftOperandTier` / `rightOperandTier`:
  -- a rebinding power base (`(-a) ^ b`, `(a + b) ^ b`), a `not` under a tighter
  -- operator (`(not a) + b`, `a * (not b)`), a looser binary (`(a + b) * c`),
  -- a right operand of equal tier (`a - (b - c)`), and a comparison chain under
  -- an arithmetic operator (`(a < b) + c`) keep their parentheses; `a + b + c`,
  -- `-a + b`, `a ^ -b`, and `a ^ b ^ c` read back bare.
  -- C#: `PushBinaryLeftOperand` / `PushBinaryRightOperand`.
  | .binary op left right =>
      let leftName := parenthesizeWhenLooser (leftOperandTier op) left (exprDiagnosticName left)
      let rightName := parenthesizeWhenLooser (rightOperandTier op) right (exprDiagnosticName right)
      leftName ++ " " ++ op.symbol ++ " " ++ rightName
  -- A comparison chain renders as the flat chain it is — `a < b <= c == d` —
  -- never as nested binary comparisons. Each operand is written at
  -- `comparisonOperandTier`, so a nested (parenthesized) chain, a `not`, and a
  -- logical operator keep their parentheses: `(a < b) == c` is not `a < b == c`.
  -- C#: `PushComparisonChain`.
  | .comparison _ [] => "<comparison with no links>"
  | .comparison first links =>
      comparisonOperandName first
        ++ String.join (links.map (fun link => " " ++ link.op.symbol ++ " " ++ comparisonOperandName link.operand))
  -- Source-faithful postfix selection `target[s1, …, sn]`; a target that would
  -- rebind under the real precedence is parenthesized (`indexTargetNeedsParens`),
  -- and every selector is written whole inside the brackets' expression list.
  | .index target selectors =>
      let targetName := exprDiagnosticName target
      (if indexTargetNeedsParens target then "(" ++ targetName ++ ")" else targetName)
        ++ "[" ++ String.intercalate ", " (selectors.map exprDiagnosticName) ++ "]"
  -- Internal SequenceConstruct renders as one sequence value; ';' is not surface syntax.
  | .sequenceConstruct left right => "(" ++ exprDiagnosticName left ++ ", " ++ exprDiagnosticName right ++ ")"
  -- Empty sequence value `()` and its nested forms.
  | .emptySequence depth => emptySequenceText depth
  -- Postfix spread binds to the completed operand. Unary and binary operands
  -- need parentheses so the diagnostic text reads back with the same AST.
  | .sequenceSpread operand =>
      parenthesizeWhenLooser postfixTier operand (exprDiagnosticName operand) ++ "*"
  -- Exact list literal `[a, b, c]`.
  | .listLiteral items => "[" ++ String.intercalate ", " (items.map exprDiagnosticName) ++ "]"
  | .resolve name => name
  | .algorithmExpr algorithm => "(" ++ String.intercalate ", " ((Algorithm.output algorithm).map exprDiagnosticName) ++ ")"
  | .capture rows => "(" ++ String.intercalate ", " (rows.map exprDiagnosticName) ++ ")"
  -- Postfix targets keep every grouping boundary that would rebind: binary and
  -- comparison nodes, unary operators, and negative numeric literals alike.
  -- C#: PushOperand at PostfixTier (Open already groups binary/comparison nodes).
  | .call fn _ => postfixTargetName fn ++ "(...)"
  | .dotMember target name _ none =>
      postfixTargetName target ++ "." ++ name
  | .dotMember target name _ (some _) =>
      postfixTargetName target ++ "." ++ name ++ "(...)"
where
  /-- One operand of a comparison chain, parenthesized when it binds looser than
      `comparisonOperandTier`. -/
  comparisonOperandName (operand : Expr) : String :=
    parenthesizeWhenLooser comparisonOperandTier operand (exprDiagnosticName operand)
  /-- The target of a call or dot edge is written at the postfix tier. -/
  postfixTargetName (target : Expr) : String :=
    parenthesizeWhenLooser postfixTier target (exprDiagnosticName target)

/-- The binary operand-shape name `left op right` — delegates to the `.binary`
  arm of `exprDiagnosticName` so the two can never disagree (in particular on
  power-base parenthesization). C#: `ExprNameRenderer.RenderBinaryDiagnosticName`. -/
def binaryExprDiagnosticName (op : BinaryOp) (left right : Expr) : String :=
  exprDiagnosticName (.binary op left right)

/-- The operand-shape name of ONE link of a comparison chain — `left op right`,
  the two ADJACENT operands the link compares — so the failing link of
  `1 < 2 < true` reads `2 < true`, never a nested spelling of the whole chain.
  Delegates to the `.comparison` arm so the two can never disagree.
  C#: `ExprNameRenderer.RenderComparisonLinkDiagnosticName`. -/
def comparisonLinkDiagnosticName (op : ComparisonOp) (left right : Expr) : String :=
  exprDiagnosticName (.comparison left [{ op := op, operand := right }])

/-- Apply ONE LINK of a comparison chain — `leftValue op rightValue`, the two
    ADJACENT operands the link compares — the single comparison semantics shared
    by every chain evaluation. `eq`/`ne` compare KatLang values structurally
    across all value kinds (`resultValueEq`): different kinds compare unequal
    rather than raising a type mismatch (`true == 1` is `false`), so equality is
    total and never fails. The ordering comparisons reject strings and then
    require numeric scalar operands (a Boolean operand is rejected — Booleans
    are NOT ordered; the empty sequence value `()` is an ordinary non-scalar
    operand, SYN-01), each rejection carrying the operand-shape context of THIS
    link (`while evaluating `2 < true``), never a spelling of the whole chain.
    C#: `Evaluator.ApplyComparison`. -/
def applyComparison (op : ComparisonOp) (leftExpr rightExpr : Expr) (lr rr : Result) : EvalM Bool :=
  match op with
  | .eq => pure (resultValueEq lr rr)
  | .ne => pure (!(resultValueEq lr rr))
  | _ =>
    match lr, rr with
    -- Non-equality operators are not defined on strings (they fail here rather
    -- than via expectInt so the diagnostic names the string operands).
    | .str _, .str _ => .error (Error.typeMismatch "Strings only support == and != operators")
    -- Mixed string/number or string/sequence value: fail for any ordering operator.
    | .str _, _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
    | _, .str _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
    | _, _ => do
      let linkContext := s!"while evaluating `{comparisonLinkDiagnosticName op leftExpr rightExpr}`"
      let x <- withCtx linkContext (requireNumericComparisonOperand op "left" lr)
      let y <- withCtx linkContext (requireNumericComparisonOperand op "right" rr)
      pure (match op with
            | .lt => decide (x < y)
            | .gt => decide (x > y)
            | .le => decide (x <= y)
            | .ge => decide (x >= y)
            | .eq => decide (x = y)
            | .ne => x != y)

namespace CtxMsg
  def openMsg (k : String)              := s!"while resolving open: {k}"
  def call   (f : Expr)               := s!"while evaluating call to {openExprName f}"
  def property (n : Ident)            := s!"while evaluating property {n}"
  def dotCall (obj : Expr) (n : Ident) := s!"while evaluating dotCall .{n} of {openExprName obj}"
  def spread (operand : Expr)         := s!"while evaluating spread operand {openExprName operand}"
end CtxMsg

/-- What a spread reports when evaluating its (peeled) operand failed (Q-36, decided
    2026-10-24): the operand's OWN missing output — the computation it directly denotes has no
    written output — is `spreadMissingOutput`; a NESTED missing output — one originating in a
    dependency, argument, output row or other subordinate computation of the operand — keeps its
    category, cause and blame, with the spread operand as added context; every other failure is
    the operand's own, unchanged. C#: `Evaluator.SpreadOperandFailure`. -/
def spreadOperandFailure (operand : Expr) (err : Error) : Error :=
  if isOwnMissingOutputError err then err.asSpreadMissingOutput
  else if isMissingOutputError err then .withContext (CtxMsg.spread operand) err
  else err

/-- The ONE zero-argument value-demand law (its rejection half), keyed by the
    written shape that names the demanded algorithm. It is consulted BEFORE an
    algorithm's body is entered wherever a resolved algorithm is demanded for its
    VALUE with zero explicit arguments: the value-position `resolve` /
    `algorithmExpr` arms of `evalCounted`, every lazy builtin VALUE slot (the `if`
    condition and branches, the `repeat` count,
    `atoms`, `range` — `evalArgumentValueCounted`), and the ordinary-dot `string`
    intrinsic's receiver. A read of a parameter bound to a supplied cell does NOT
    consult it — neither the value-position `param` arm nor a `string` receiver
    that is such a parameter (`hasSuppliedParameterCell`): the parameter's value
    outcome is established by the first VALUE demand of its cell, which evaluates
    the written argument — through this law, keyed by the argument's own shape —
    and every read reuses that outcome (AT-MOST-ONCE ARGUMENT VALUE EVALUATION,
    `demandNeedRecursive` through `NeedDemand.step`).

    ELIGIBILITY IS ARITY, NOT PARAMETER-LIST EMPTINESS (September 2026): a
    callable may satisfy a zero-argument value demand exactly when an ordinary
    call supplying zero arguments can bind it
    (`Algorithm.acceptsZeroSuppliedArguments` — the binder's own
    `ParameterPattern.minimumSuppliedSlots` rule, the family's zero-arity branch
    rule). So `Only(*xs) = xs` is demandable (a collecting parameter requires no
    supplied slot: `Only` and `Only()` both accept zero) while `Head(x, *rest)`
    still requires one supplied value and is rejected. The REPORT names the true
    minimum supply — `minimumSuppliedSlots`, never the flattened declared capture
    count — so `Head` reports 1 and `P((x, y))` reports 1, exactly the counts
    `Head()` / `P()` report.

    Only the report's shape depends on the source:
    - a lexical property reference `X` (`.resolve`): a conditional cannot be
      accessed as a value (`conditionalValueAccessError?`), and a parameterized
      property is `withContext (property X) (arityMismatch k 0)`;
    - an algorithm-channel parameter `x` (`.param`) and a structurally navigated
      member `A.M` (an argumentless `.dotMember` receiver): the same conditional
      rule, then the bare `arityMismatch k 0`;
    - a written brace block (`.algorithmExpr`): `unresolvedImplicitParams` — the
      block's OWN inferred parameters;
    - an inline CALLABLE ALIAS block (`.algorithmExpr` of an `Algorithm.alias`,
      `{ F }`): binding indirection with no signature and no report of its own, so
      the demand is reported exactly as its written target reference `F` reports it
      — the target's own contract (`{ Inc }` with `Inc(x)` is Inc's property-context
      `arityMismatch 1 0`, a family `noMatchingBranch`), never the written block's
      `unresolvedImplicitParams` over the target's parameters (FA-OQ-1, owner
      decision Option B, 2026-10-10). A builtin target stays `none` here, as above;
    - an anonymous or value-reified argument (`none`): the bare `arityMismatch`.
    `none` means the demand may proceed to the algorithm's zero-argument value
    (`evalZeroArgumentDemandOutputCounted`, which binds the accepted EMPTY supply
    first). A builtin CALLBACK slot (`map`/`filter`/`reduce` steps, loop steps)
    supplies arguments and never consults this law. C#:
    `ZeroArgumentValueDemandError`. -/
def zeroArgumentDemandError? (source? : Option Expr) (a : Algorithm) : Option Error :=
  match a with
  | .builtin _ =>
      -- A builtin is deliberately NOT decided here: its zero-argument rejection
      -- is owned by `evalBuiltinValueCounted` (`builtinArityError b 0` — the very
      -- error `sum()` reports), and intercepting it would replace that report
      -- with a parameter-list one.
      none
  | _ =>
    if Algorithm.acceptsZeroSuppliedArguments a then none
    else
      let arity :=
        Error.arityMismatch
          (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns a)) 0
      let named (name : Ident) (reject : Error) : Error :=
        (conditionalValueAccessError? name a).getD reject
      -- An inline callable alias is reported as its written target reference (FA-OQ-1).
      let source? := match source? with
        | some (.algorithmExpr (.alias _ _ _ target _ _)) => some target
        | other => other
      match source? with
      | some (.resolve n) => some (named n (Error.withContext (CtxMsg.property n) arity))
      | some (.param x) => some (named x arity)
      | some (.dotMember _ n _ _) => some (named n arity)
      | some (.algorithmExpr _) =>
          some (named "conditional" (Error.unresolvedImplicitParams (Algorithm.params a)))
      | _ => some (named "conditional" arity)

/-- The ACCEPTANCE half of the ONE zero-argument value-demand law, read off the
    law itself so the two halves can never disagree: `true` exactly when
    `zeroArgumentDemandError?` lets the demand proceed. It differs from
    `Algorithm.acceptsZeroSuppliedArguments` only for a BUILTIN, which the law
    deliberately passes through to its own arity rejection
    (`evalBuiltinValueCounted`) — the law
    `zero_argument_value_demand_accepts_exactly_zero_supply_callables` in
    `KatLangArityLaws.lean` proves the two agree everywhere else. Used by the
    demand sites that decide the same question without building a report: the
    structurally navigated member arm of `evalDotCallCounted` and the collection
    builtins' value slots. C#: `AcceptsZeroArgumentValueDemand`. -/
def acceptsZeroArgumentValueDemand (a : Algorithm) : Bool :=
  (zeroArgumentDemandError? none a).isNone

--------------------------------------------------------------------------------
-- Open resolution structures
--------------------------------------------------------------------------------

/-- A resolved open: its canonical dedup key, original expression, and resolved algorithm. -/
structure ResolvedOpen where
  key  : String
  expr : Expr
  lib  : Algorithm
  deriving Repr

/-- A resolved property-style access with the owner and binding retained for
    zero-argument property cache keys. -/
structure ResolvedProperty where
  owner   : Algorithm
  binding : PropDef
  alg     : Algorithm
  deriving Repr

/-- Where a STRUCTURE or INVOCATION alias chase ends (M4★, `EvalBody.resolveAliasChase`):
    * `identity alg last` — a non-alias algorithm, or a structural CARRIER when the chase does not
      follow carriers, with `last` the binding (owner and declaration) of the chase's final STATIC
      hop, if it took one;
    * `valueView alias` — a runtime reference whose binding cell projected NO callable identity;
    * `runtime alias` — the first runtime-target alias a chase that projects no runtime step of its own
      reaches (the VALUE chase and the static-structure chase). -/
inductive AliasChaseEnd where
  | identity (alg : Algorithm) (last : Option (Algorithm × PropDef))
  | valueView (alias : Algorithm)
  | runtime (alias : Algorithm)
  deriving Repr

/-- Whether a chase ENDED at a structural carrier — the end of the reference-only static chase that
    stops at the first carrier (`EvalBody.resolveAliasValueTarget`'s `nested`, Q-36 with M4★). -/
def AliasChaseEnd.isCarrier : AliasChaseEnd → Bool
  | .identity (.alias _ _ _ _ _ false) _ => true
  | _ => false

/-- Where a bare VALUE read of a binding goes (OD-E, M4★; `EvalBody.resolveAliasValueTarget`):
    * `plain alg` — not an alias: its own read;
    * `binding owner binding alg` — the TERMINAL property binding of a static alias chain (`alg`
      wired and not an alias): the read is THAT binding's bare read, under its own cache key, owner
      and activation — an alias owns no zero-argument cache entry of its own;
    * `runtime alias` — a runtime-target alias: its binding cell's VALUE (`EvalBody.aliasValue`).
    Each carries `nested` (Q-36 with M4★): the read CROSSES a structural carrier, whose bare VALUE is
    the subordinate computation of its written row, so a missing output escaping the read is nested in
    the carrier's outcome (a transparent reference is its target: its read is the target's own). -/
inductive AliasTerminal where
  | plain (alg : Algorithm) (nested : Bool)
  | binding (owner : Algorithm) (binding : PropDef) (alg : Algorithm) (nested : Bool)
  | runtime (alias : Algorithm) (nested : Bool)
  deriving Repr

/-- The algorithm a VALUE terminal reads. -/
def AliasTerminal.alg : AliasTerminal → Algorithm
  | .plain a _ => a
  | .binding _ _ a _ => a
  | .runtime a _ => a

/-- Whether a VALUE terminal's read crosses a structural carrier (Q-36 with M4★). -/
def AliasTerminal.nested : AliasTerminal → Bool
  | .plain _ n => n
  | .binding _ _ _ n => n
  | .runtime _ n => n

/-- The owner a VALUE terminal's read is keyed by: a terminal binding's own, else `owner`. -/
def AliasTerminal.ownerOr : AliasTerminal → Algorithm → Algorithm
  | .binding o _ _ _, _ => o
  | _, o => o

/-- The binding a VALUE terminal's read is keyed by: a terminal binding itself, else `binding`. -/
def AliasTerminal.bindingOr : AliasTerminal → PropDef → PropDef
  | .binding _ b _ _, _ => b
  | _, b => b

/-- The property name a VALUE terminal's read reports a missing output under: the TERMINAL binding's
    (M4★: a transparent reference is its target), else the written name `n`. -/
def AliasTerminal.readNameOr : AliasTerminal → Ident → Ident
  | .binding _ b _ _, _ => b.name
  | _, n => n

/-- The zero-argument value-demand rejection of a VALUE terminal read at the written `source`
    (`zeroArgumentDemandError?`, FA-OQ-1): none for a runtime-target alias, whose binding cell's VALUE
    is read, else the law over the terminal's algorithm. -/
def AliasTerminal.demandError? : AliasTerminal → Expr → Option Error
  | .runtime _ _, _ => none
  | t, source => zeroArgumentDemandError? (some source) t.alg

/-- WHICH zero-argument property calculation a request of the property cache performs
    (CACHE-PUB-1, owner decision October 22 2026). Both requests share ONE publication law
    (`evalZeroArgPropertyAccessCounted`, Q-37):
    * `read` — a property-style read `A`: an established entry is reused; on an empty entry the
      read evaluates the property's zero-argument demand under publication ownership.
    * `invoke calleeName` — a qualifying explicit zero-supply invocation `A()`: it ALWAYS performs
      its own fresh invocation (it never obtains its result from an established entry), and on an
      empty, inactive entry it owns publication, so its success establishes the entry a later bare
      read reuses. An established entry is never replaced. -/
inductive ZeroArgPropertyRequest where
  | read
  | invoke (calleeName : String)
  deriving Repr

/-- Where the callee of an ordinary call came from (CACHE-PUB-1): the authoritative provenance a
    zero-supply invocation needs to name the property BINDING it invokes, decided only after the
    supply is formed (`EvalBody.evalSuppliedCallCounted`) and read without evaluating anything
    (`EvalBody.originBinding?`).
    * `none` — no property binding (a computed callee, a callback, a host-built dispatch).
    * `written callee caller` — the written callee expression and the context it is resolved in
      (a lexical name, an argumentless structural path, a parameter).
    * `cell address` — a supplied callee cell (a parameter's transported cell, a captured plan's
      canonical callee cell): the binding its written source names in its own caller context.
    * `bound owner binding` — an already selected member binding (a structural member call).
    C#: `Evaluator.CalleeOrigin`. -/
inductive CalleeOrigin where
  | none
  | written (callee : Expr) (caller : EvalCtx)
  | cell (address : Nat)
  | bound (owner : Algorithm) (binding : PropDef)
  deriving Repr

structure OpenPropertyHit where
  provider : String
  property : ResolvedProperty
  deriving Repr

--------------------------------------------------------------------------------
-- Pattern matching (for conditional algorithms)
--------------------------------------------------------------------------------

/-- The elements a structural pattern of `patternCount` items matches
    against: a value of the pattern's OWN kind (`Result.sequencePatternItems?`
    for `(…)`, `Result.listPatternItems?` for `[…]`) with exactly that many
    elements, and nothing otherwise — never a value of the other kind and never
    a scalar (STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY
    DESTRUCTURE, September 2026; the former singleton fallback, under which a
    one-item `(b)` took any non-sequence value whole, is gone with the
    one-item sequence pattern itself). Read by the structural arms of
    `matchPatternInto`; the one Model-C binder binds structural patterns itself
    (`bindNeedOne`) and hands the matcher literal patterns only. -/
def patternStructureMembers? (elements? : Option (List Result)) (patternCount : Nat)
    : Option (List Result) :=
  match elements? with
  | some rs => if rs.length == patternCount then some rs else none
  | none => none

mutual
/-- Match a pattern against a Result, returning accumulated bindings on success.
    - `bind x` matches any Result, binding x → r
    - `litInt n` matches only `Result.atom n`; `litBool b` only `Result.bool b`
    - `sequenceValue ps` matches only `Result.sequenceValue rs` with the same length,
      recursively; `listValue ps` matches only `Result.listValue rs` with the same
      length, recursively (`patternStructureMembers?`)

    Bindings accumulate left-to-right. Repeated names compare against the
    first bound value and do not add another environment entry.

    Structural recursion over the pattern (R3′, October 2026): a structural arm reads its
    members once (`patternStructureMembers?`) and walks them with `matchItemsInto`, so
    `matchPatternInto (.sequenceValue ps) r env` IS `matchStructureInto ps
    (patternStructureMembers? (Result.sequencePatternItems? r) ps.length) env` by definition
    (`PatternHelpers.matchPatternInto_sequenceValue`; the list arm likewise). -/
def matchPatternInto (p : Pattern) (r : Result) (env : ValEnv)
    : Option ValEnv :=
  match p with
  | .bind x =>
      match env.lookup x with
      | some existing => if existing == r then some env else none
      | none => some (env ++ [(x, r)])
  | .litInt n  =>
      match r with
      | .atom v => if v = n then some env else none
      | _       => none
  | .litString s =>
      match r with
      | .str v => if v = s then some env else none
      | _      => none
  | .litBool b =>
      match r with
      | .bool v => if v = b then some env else none
      | _       => none
  | .sequenceValue ps  =>
      match patternStructureMembers? (Result.sequencePatternItems? r) ps.length with
      | none => none
      | some rs => matchItemsInto ps rs env
  | .listValue ps  =>
      match patternStructureMembers? (Result.listPatternItems? r) ps.length with
      | none => none
      | some rs => matchItemsInto ps rs env

/-- A structural pattern's items against the elements its value supplied, in lockstep and
    left to right, carrying the accumulated environment; the first non-match, or a length
    difference, ends the walk with `none` (structural recursion over the items; the former
    local `go` of `matchStructureInto`). -/
def matchItemsInto : List Pattern -> List Result -> ValEnv -> Option ValEnv
  | [], [], current => some current
  | p::ps', r::rs', current => do
      let next <- matchPatternInto p r current
      matchItemsInto ps' rs' next
  | _, _, _ => none
end

/-- Match a structural pattern's items against the elements its value supplied
    (`none` when the value is not of the pattern's kind or length). The structural arms of
    `matchPatternInto` are this helper over `patternStructureMembers?`. -/
def matchStructureInto (ps : List Pattern) (members? : Option (List Result)) (env : ValEnv)
    : Option ValEnv :=
  match members? with
  | none => none
  | some rs => matchItemsInto ps rs env

def matchPattern (p : Pattern) (r : Result) : Option ValEnv :=
  matchPatternInto p r []

--------------------------------------------------------------------------------
-- Pure evaluator helpers (no evaluator recursion)
--------------------------------------------------------------------------------
-- Helpers used by the evaluator that are not part of its recursion cycle:
-- they never call back into eval/evalCounted/applyBuiltin and friends, so
-- Lean checks them as ordinary total definitions.

/-- True when an argument expression supplies ONLY a value in argument
    position. A capture is a value boundary: it suppresses the algorithm
    identity of anything inside it, so higher-order probing never sees the
    enclosed content as callable.

    `algorithmExpr` is deliberately NOT value-only: an algorithm block
    explicitly exposes its contained Algorithm on the algorithm channel
    regardless of parameter/declaration/output count — `{42}` is as much an
    Algorithm as `{a + 1}` — while the value channel reifies the written slot
    independently. -/
def shouldWrapArgExprAsValue : Expr -> Bool
  | .capture _ => true
  | _ => false

def isLiftableArgResolutionError : Error → Bool
  | .notAnAlgorithm _ => true
  | .illegalInEval _  => true
  | .withContext _ e   => isLiftableArgResolutionError e
  | _                  => false

def loopStateResult (stateSlots : List Result) : Result :=
  Result.normalize (.sequenceValue stateSlots)

/-- The ROW SUPPLY a builtin loop step contributes (LOOP-03, LOOP-08, Q-23 decided
    October 2026): a builtin has no written rows, so the ONE result value of its
    ordinary invocation is ONE non-spread row — exactly the row its one-row user
    wrapper `W(p…) = builtin(p…)` writes. The emitted count is never consulted: a
    `()` result is one visible slot (never zero slots, as `countedTopLevelValues`
    would read it) and a collection result is one slot holding the collection.
    Laws: `loop_step_builtin_result_is_one_row`, `loop_step_builtin_rows_ignore_emitted_count`.
    C#: the builtin arm of `Evaluator.InvokeLoopStepSupply`. -/
def loopStepBuiltinRows (out : CountedResult) : List Result := [out.fst]

/-- The written expression a supply cell retains: the argument as written, or, for a
    cell transported through a parameter, the argument originally written for it
    (`supplyNeed`). A ready cell (a spread item, a callback element, loop state) and a
    collector have none. C#: `NeedCell.Source`. -/
def needWrittenSource? (address : Nat) : EvalM (Option Expr) := do
  match (<- get).needs[address]? with
  | some { suspension := .expression source _ _, .. } => pure (some source)
  | _ => pure none

/-- The name a loop step's own call frame and a family step's `noMatchingBranch`
    report (LOOP-08, Q-23): the written expression its SUPPLY CELL retains
    (`needWrittenSource?`) — the step argument as written, or, for a cell transported
    through a parameter, the argument originally written for it — named exactly as
    the ordinary call names its callee (`openExprName`); a cell with no written source
    (a spread item) is the loop's step. C#: `Evaluator.StepDiagnosticName`. -/
def loopStepName (loopName : String) (step : ResolvedArgumentAlgorithm) : EvalM String := do
  let written? : Option Expr <- match step.need? with
    | some address => needWrittenSource? address
    | none => pure step.source?
  pure (match written? with
    | some e => openExprName e
    | none => loopName ++ " step")

/-- The completed `while`/`repeat` result (LOOP-07, Q-26 decided October 2026):
    ONE value — the canonical capture of the final state's slots (`()` for zero
    slots, the slot itself for one, a sequence for several) — crossing the
    ordinary RESULT value boundary like every other builtin and call result:
    its emitted count is `Result.valueCount` of that value
    (`reCountValueBoundary`), never the slot count. The slot count is the
    loop's own protocol and is not observable outside the loop: a one-slot
    state holding `(20, 30)` and a two-slot state `20, 30` complete to the same
    counted result, and only an explicit spread `L*` opens it into items.
    Laws: `loop_result_is_a_value_boundary`, `loop_result_count_le_one`.
    C#: `Evaluator.MakeCheckedLoopStateResult`. -/
def loopResultCounted (finalSlots : List Result) : CountedResult :=
  reCountValueBoundary (loopStateResult finalSlots, finalSlots.length)

/-- The context of a `while` step that emitted no slot at all: its output has
    no continuation flag, an emitted-slot cardinality failure (`badArity`,
    Q-27). C#: `Evaluator.WhileStepWithoutFlagContext`. -/
def whileStepWithoutFlagContext : String :=
  "a while step must output at least its continuation flag"

/-! ### Output rows and the condition-first `while` round (LOOP-03, LOOP-06; LOOP-CF1, October 2026)

An algorithm's output is a list of ROWS. Forming a row is ONE ordinary counted evaluation of its
expression (the evaluator installs `formOutputRow`, which re-enters `evalCounted` through the
evaluator core's recursive answer);
what the formed row contributes to the row supply is the ONE row rule `OutputRows.items`. The
two receivers of a step's rows differ only in the ORDER in which they request rows:

* the supply reader (`OutputRows.formLeftToRight`; `evalAlgOutputSlots`, so `repeat`) forms every
  row once, left to right;
* the `while` round (`WhileRound.conditionFirst`; `whileVerdictSlots`) discovers its continuation
  flag first — rows from the LAST backwards until one supplies an item, whose last item is the
  flag — and forms the remaining earlier rows, left to right, only after a `true` verdict.

Both are TOTAL definitions parameterized by the row-forming capability, so the kernel checks
theorems about the very definitions the evaluator calls (`KatLangArityLaws/WhileRound.lean`).
Both receivers set the body up through the ONE activated-body boundary `ActivatedBody.readRows`
(below), passing `formOutputRow`; the production connection — one body entry, one context for
every row, the production row formation and the production `whileVerdictSlots` — is proved in
`KatLangArityLaws/WhileRoundProduction.lean` (CF-4, S6c). -/

namespace OutputRows

/-- What ONE formed output row contributes to its algorithm's row supply (LOOP-03): a spread row
    uses `countedTopLevelValues`; a non-spread row with count zero keeps its value as one visible
    slot (`()` included), otherwise it also uses `countedTopLevelValues`. Ordinary value-boundary
    results have count zero or one. The rule also preserves multi-item counted results, including
    host-built Ready cells; no single-slot premise is imposed on arbitrary `CountedResult`s.
    C#: `Evaluator.AddOutputRowItems`. -/
def items (e : Expr) (out : CountedResult) : List Result :=
  match e with
  | .sequenceSpread _ => countedTopLevelValues out
  | _ => if out.snd = 0 then [out.fst] else countedTopLevelValues out

/-- The supply reader: every row formed once, LEFT TO RIGHT, the supply in written order. -/
def formLeftToRight (form : Expr → EvalM (List Result)) : List Expr → EvalM (List Result)
  | [] => pure []
  | e :: rest => do
      let xs ← form e
      let ys ← formLeftToRight form rest
      pure (xs ++ ys)

end OutputRows

namespace WhileRound

/-- The `while` continuation flag rule (LOOP-06): a Boolean value (`true` continues, `false`
    stops); a number, string, sequence, or list there is a value-kind error, never a truth test.
    C#: `Evaluator.ContinuationFlag`. -/
def flag (item : Result) : EvalM Bool :=
  match Result.asBool? item with
  | some c => pure c
  | none => throw (Error.typeMismatch
      (booleanRequiredMessage "while continuation flag (the step's last output)" item))

/-- The next state of an accepted round from its complete supply: the supply without its last
    item, the flag — except that a one-item supply is both the next state and the flag. -/
def nextSlots (supply : List Result) : List Result :=
  match supply with
  | [slot] => [slot]
  | _ => supply.dropLast

/-- FLAG DISCOVERY over the rows in REVERSE written order: form each row until one supplies at
    least one item. Returns the still-unformed earlier rows (in written order) and that row's
    items; `none` when no row supplies an item. Rows passed over supplied nothing, so the
    discovered row's items are the whole supply formed so far. -/
def discover (form : Expr → EvalM (List Result)) : List Expr → EvalM (Option (List Expr × List Result))
  | [] => pure none
  | e :: rest => do
      let xs ← form e
      match xs with
      | [] => discover form rest
      | _ :: _ => pure (some (rest.reverse, xs))

/-- The missing-flag failure: no row supplied an item (an emitted-slot cardinality failure,
    `badArity`, Q-27). -/
def noFlag {α : Type} : EvalM α :=
  throw (Error.withContext whileStepWithoutFlagContext Error.badArity)

/-- ONE `while` round over a step body's rows (LOOP-06, condition first): discover the flag
    (`discover`), check it (`flag`); `false` ends the loop (`none`) without forming the remaining
    earlier rows; `true` forms them LEFT TO RIGHT and the next state is the supply in written
    order without its last item (`nextSlots`). Every row is formed at most once.
    C#: `Evaluator.EvalWhileVerdictSlots` and its async mirror. -/
def conditionFirst (form : Expr → EvalM (List Result)) (rows : List Expr) :
    EvalM (Option (List Result)) := do
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

end WhileRound

/-- Split a COMPLETE loop step supply into next state slots and the continuation flag: the
    supply's LAST item is the flag (`WhileRound.flag`), and a single-item supply keeps the
    established shape — its one slot is both the next state and the flag
    (`WhileRound.nextSlots`). A `while` round reads a step BODY's rows condition first
    (`WhileRound.conditionFirst`); this split is the round over a supply that is ONE atomic row,
    a builtin step's result (`WhileRound.ofSupply`). C#: `Evaluator.SplitContSlots`. -/
def splitContSlots (outputSlots : List Result) : EvalM (List Result × Bool) := do
  match outputSlots.getLast? with
  | none => WhileRound.noFlag
  | some last => pure (WhileRound.nextSlots outputSlots, ← WhileRound.flag last)

/-- A `while` round over a supply that is ONE atomic row (a builtin step, a builtin clause body):
    there are no earlier rows to skip, so the round is the ordinary split. C#:
    `Evaluator.WhileVerdictOfSupply`. -/
def WhileRound.ofSupply (supply : List Result) : EvalM (Option (List Result)) := do
  let (next, cont) ← splitContSlots supply
  pure (if cont then some next else none)

/-- ONE iteration of the `while` loop over its state cells (`.whileBuiltin`): run the round; a
    `false` verdict FINISHES the loop (`.inl`) with exactly the cells that entered the round — on
    the first round the original initial cells (R1: zero accepted transitions), still lazy, whose
    VALUE materialization is the loop's separate final boundary (LOOP-07) — and a `true` verdict's
    next slots become Ready cells (`.inr`). Law: `cf3_false_round_keeps_entering_cells`. -/
def WhileRound.advance (round : List Nat → EvalM (Option (List Result))) (cells : List Nat) :
    EvalM (Sum (List Nat) (List Nat)) := do
  match ← round cells with
  | none => pure (.inl cells)
  | some next => pure (.inr (← next.mapM (fun value => readyNeed (value, Result.valueCount value))))

/-! ### The activated-body boundary of a row reader (CF-4, S6c, October 2026)

Both receivers of a step body's rows — the supply reader (`evalAlgOutputSlots`, so `repeat`) and
the `while` round (`whileVerdictSlots`) — set the body up the SAME way and differ only in the
ORDER in which they request rows. `ActivatedBody.readRows` is that one setup, TOTAL and
parameterized by the row-forming capability `form` (the evaluator passes `formOutputRow`), the
row reader `read` (`OutputRows.formLeftToRight` or `WhileRound.conditionFirst`) and the reading of
a builtin body's ONE atomic row: a builtin body is one counted value; any other body passes the
body checks (`check`), is ENTERED ONCE (`enterAlgorithmBody`), and `read` receives the ONE
`form pushedCtx env` closure over that entered context — so every row the reader requests,
discovery and transitions alike, is formed in the same context, environment and parameter cells,
from the state the previous row left. Laws: `KatLangArityLaws/WhileRoundProduction.lean`. -/

namespace ActivatedBody

/-- The body checks of a row reader, in order: a duplicate property name (`duplicateProperty`),
    a clause family read as a value (`conditionalValueAccessError?`), a user body without written
    output (`missingOutput`). Reads no state and writes none. C#: `Evaluator.OutputRowsAccessError`. -/
def check (a : Algorithm) : EvalM Unit := do
  match a.findDuplicatePropName with
  | some n => .error (Error.duplicateProperty n)
  | none =>
    match conditionalValueAccessError? "conditional" a with
    | some err => .error err
    | none => pure ()
    match a with
    | .mk _ _ _ _ [] _ => .error (Error.missingOutput .own)
    | _ => pure ()

/-- Read a body's rows in ONE activation: a builtin body is one atomic counted value (`atomic`);
    any other body is checked (`check`), entered once (`enterAlgorithmBody`), and its written rows
    are read by `read` over the one `form pushedCtx env` closure. C#: the shared prelude of
    `Evaluator.EvalAlgOutputSlots` / `Evaluator.EvalWhileVerdictSlots` and their async mirrors. -/
def readRows {α : Type} (form : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α)
    (atomic : CountedResult → EvalM α) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM α :=
  match a with
  | .builtin b => do
      let out <- evalBuiltinValueCounted b
      atomic out
  | _ => do
      check a
      let pushedCtx <- enterAlgorithmBody a ctx env
      read (form pushedCtx env) (Algorithm.output a)

end ActivatedBody

/-- The counted view of one iterated collection item as the callback receives
    it. A callback item is a SELECTED value, so it crosses the same ordinary
    value boundary as `S[i]` / `first` / `last` (`reCountValueBoundary`): the
    item keeps its stored shape (a nested sequence or list stays one value for
    pattern matching and for every count-sensitive reader inside the body — a
    bare `x` output row, `x.Coll` on a collecting receiver), a `()` item emits
    zero values, and only an explicit
    spread `x*` opens it. Law: `callback_item_is_a_value_boundary`.
    C#: `CountedSequenceCallbackItem`. -/
def countedSequenceCallbackItem (item : CountedResult) : CountedResult :=
  reCountValueBoundary item

/-- A property-style access reuses the per-run cache exactly when the demanded
    callable is one the ONE zero-argument value-demand law ACCEPTS
    (`Algorithm.acceptsZeroSuppliedArguments`), so a newly eligible
    collecting-only property (`Only(*xs) = xs`) takes the very same demand/cache
    path an ordinary zero-parameter property takes — eligibility is what the
    September 2026 rule widened, cache POLICY is unchanged, and `Only()` remains
    an ordinary call that never reads the entry (since CACHE-PUB-1 it may
    establish an empty one, as the `invoke` request of
    `evalZeroArgPropertyAccessCounted`). A builtin never accepts, so it
    keeps flowing to its own arity rejection uncached, exactly as before.
    Since Q-03 (2026-09-28) the surface pass reads the SAME rule when it decides
    whether to lift a bare reference (`liftsBareValueReference`): it never
    rewrites a reference to a callable this accepts into a fresh forwarding
    call, so such a reference reaches this cache in EVERY position — an
    operand, a list element, a selection target, a Math argument — and
    not only in the neutral ones.
    C#: the zero-argument property access path
    (`GetOrEvaluateZeroArgPropertyResult`), entered by callers only after the
    law accepted. -/
def isCacheableZeroArgPropertyAlgorithm (a : Algorithm) : Bool :=
  Algorithm.acceptsZeroSuppliedArguments a

/-- The cache key of one property-style access (see `ZeroArgPropertyCacheKey`
    for the law it encodes): an exported binding's key carries no environment
    components; a local-only binding uses its declaring owner's retained binding
    context, falling back to the access environments only for unactivated host scopes. -/
def zeroArgPropertyCacheKey (_accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (ctx : EvalCtx) (env : ValEnv)
    (ownerBindingContext : Option Nat := none)
    : ZeroArgPropertyCacheKey :=
  let bindingContextFree := binding.exposure.isExported
  {
    accessKind := .lexical,
    owner := reprStr owner.declarationId ++ reprStr (cacheScopeShape owner.asScopeCtx),
    propertyName := binding.name,
    propertyAlgorithm := reprStr (cacheAlgorithmShape binding.alg),
    valEnv := if bindingContextFree || ownerBindingContext.isSome then none else some (reprStr env),
    bindingContext := if bindingContextFree then none else some (ownerBindingContext.getD ctx.bindingContext)
  }

/-- The binding context of the nearest ACTIVATED level of a declaring chain: the context its
    owner was entered in, independent of the consumer. A property-style read of a parameterless or
    collecting-only owner enters its body in this context (CACHE-OWNER-D1, COLLECT-CACHE-1,
    `EvalBody.evalPropertyDemandCounted`);
    an explicit call binds a fresh one. TOTAL (CACHE-OWNER-D1, October 2026; formerly `partial`):
    structural over the finite parent chain, with the former body as its equation. -/
def propertyOwnerBindingContext : Option ScopeCtx → EvalState → Option Nat
  | none, _ => none
  | some (.mk parent _ _ _ _ _ activation _), state =>
      match activation.bind (fun id => state.lexicalActivations[id]?) with
      | some found => some found.bindingContext
      | none => propertyOwnerBindingContext parent state

def applySequenceBuiltinEmptyPolicy (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput) : EvalM CollectedSequenceBuiltinInput :=
  match metadata.emptyPolicy with
  | .allowEmpty =>
      pure collected
  -- The empty collection is a DOMAIN failure of an aggregate and a missing
  -- POSITION of a selection (Q-27): never an arity error, because the argument
  -- count is correct.
  | .requireAnyItem =>
      if collected.totalItemCount = 0 then
        .error (Error.illegalInEval s!"{builtinDisplayName b} requires a non-empty collection")
      else
        pure collected
  | .requireSelectablePosition =>
      if collected.totalItemCount = 0 then
        .error (Error.withContext
          s!"{builtinDisplayName b} selects from an empty collection, which has no position to select"
          Error.badIndex)
      else
        pure collected

/-- Collect top-level collection elements as single atomic numeric values.
    Used by numeric ordering and aggregation builtins, which reject strings
    and sequence values instead of inventing mixed-type or structural
    interpretation.

    Diagnostics identify the 0-based collection item index so numeric shape
    failures remain debuggable after counted top-level extraction. An element
    that is not one number is a present value of the wrong KIND —
    `typeMismatch` (Q-27), never an arity error.
    C#: `Evaluator.CollectSingleAtomicNumbers`. -/
def collectSingleAtomicNumbers (b : Builtin)
    : Nat -> List Result -> EvalM (List Int)
  | _, [] => pure []
  | index, item :: rest =>
      match Result.singleAtomicNumber? item with
      | some n => do
          let tail <- collectSingleAtomicNumbers b (index + 1) rest
          pure (n :: tail)
      | none =>
          .error (Error.typeMismatch (numericSequenceItemErrorContext b index item))

def prepareSequenceBuiltinInput (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput)
    : EvalM PreparedSequenceBuiltinInput := do
  let collected <- applySequenceBuiltinEmptyPolicy b metadata collected
  let numericItems <-
    match metadata.itemShapeConstraint with
    | .any =>
        pure none
    | .singleNumeric => do
      let numbers <- collectSingleAtomicNumbers b 0 collected.items
      pure (some numbers)
  pure { items := collected.items, numericItems? := numericItems }

def sequenceBuiltinSuffixArgRequirementDesc
    (kind : SequenceBuiltinSuffixArgKind) : String :=
  match kind with
  | .algorithm => "an algorithm"
  | .value => "exactly one value"
  | .wholeNumber => "exactly one whole-number value"

def sequenceBuiltinSuffixArgKindDesc
    (kind : SequenceBuiltinSuffixArgKind) : String :=
  match kind with
  | .algorithm => "algorithm"
  | .value => "value"
  | .wholeNumber => "whole-number value"

def sequenceBuiltinSuffixArgErrorContext
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) : String :=
  s!"{builtinDisplayName b} {descriptor.name} must be {sequenceBuiltinSuffixArgRequirementDesc descriptor.kind}"

def internalSequenceBuiltinSuffixArgMetadataError
    (b : Builtin) (detail : String) : EvalM α :=
  .error (Error.withContext
    s!"internal sequence metadata for {builtinDisplayName b} {detail}"
    Error.badArity)

/-- After binding chooses a VALUE position, apply the shared demand rejection to
    an unevaluated callable using its written source — judging the callable the
    item NAMES (`CallableCallItem.named?`: a failed cell's CALLABLE projection, or a
    fixture item's algorithm). Preserve a
    valid value's body error; callback positions never consult this helper. A
    parameter's established failure precedes callable classification. `refine`
    rewrites only the zero-argument law's REJECTION of the named callable (every
    value slot keeps it unchanged except `reduce`'s `initial`,
    `reduceInitialRejection`). -/
def sequenceBuiltinValueDemandErrorWith? (refine : Algorithm -> Error -> Error)
    (item : CallableCallItem) : Option Error :=
  match item.source?, item.error? with
  | some (.param _), some err => some err
  | _, _ => match item.named? with
    | some alg => ((zeroArgumentDemandError? item.source? alg).map (refine alg)).or item.error?
    | none => item.error?

def sequenceBuiltinValueDemandError? (item : CallableCallItem) : Option Error :=
  sequenceBuiltinValueDemandErrorWith? (fun _ err => err) item

def reduceInitialAccumulatorRequiresValueError : Error :=
  Error.withContext "while preparing reduce initial accumulator" Error.badArity

/-- `reduce`'s `initial` is an ordinary VALUE slot (HO-04), demanded once like
    every other value slot; only the REPORT of a zero-argument demand rejection is
    reduce's own. A rejected callable that declares parameters is the reducer
    written where the initial accumulator belongs (`reduce(xs, Add, Inc)`), so it
    gets reduce's dedicated accumulator report; any other rejection (a clause
    family's `noMatchingBranch`) keeps the law's report. -/
def reduceInitialRejection (alg : Algorithm) (err : Error) : Error :=
  if (Algorithm.params alg).isEmpty then err else reduceInitialAccumulatorRequiresValueError

def prepareSequenceBuiltinSuffixArgItem
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor)
    (item : CallableCallItem) : EvalM PreparedSequenceBuiltinSuffixArg := do
  match descriptor.kind with
  | .algorithm =>
    if let some address := item.need? then return .needAlgorithm address
    -- A CALLBACK slot: call-item assembly never evaluated the item (CALL-03), so
    -- it carries its algorithm channel only; the builtin invokes it later.
    match item.algorithm? with
    | some alg => pure (.algorithm alg)
    | none =>
        match item.error? with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .value =>
    match item.value? with
    | some value => pure (.value value)
    | none =>
        let refine : Algorithm -> Error -> Error := match b with
          | .reduceBuiltin => reduceInitialRejection
          | _ => fun _ err => err
        match sequenceBuiltinValueDemandErrorWith? refine item with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .wholeNumber =>
    match item.value? with
    | some value =>
      -- The one numeric-control rule (Q-27): a present value of the wrong KIND
      -- is `typeMismatch`. (A non-whole number is the C# runtime's
      -- `illegalInEval`; the integer core has none.)
      match Result.singleAtomicNumber? value with
      | some number => pure (.wholeNumber number)
      | none =>
          .error (Error.typeMismatch
            s!"{sequenceBuiltinSuffixArgErrorContext b descriptor}, but was {operandDescription value}")
    | none =>
        match sequenceBuiltinValueDemandError? item with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)

def expectPreparedSequenceBuiltinSuffixArgAt
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat)
    (expectedKind : SequenceBuiltinSuffixArgKind)
    (projector : SequenceBuiltinSuffixArgDescriptor -> PreparedSequenceBuiltinSuffixArg -> EvalM α)
    : EvalM α := do
  if descriptors.length != args.length then
    internalSequenceBuiltinSuffixArgMetadataError b "mismatched suffix arguments"
  else
    match List.drop index descriptors, List.drop index args with
    | descriptor :: _, arg :: _ =>
        if descriptor.kind = expectedKind then
          projector descriptor arg
        else
          internalSequenceBuiltinSuffixArgMetadataError b
            s!"expected suffix argument {index + 1} ({descriptor.name}) to have metadata kind {sequenceBuiltinSuffixArgKindDesc expectedKind}, but found {sequenceBuiltinSuffixArgKindDesc descriptor.kind}"
    | _, _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"expected suffix argument {index + 1} to have metadata kind {sequenceBuiltinSuffixArgKindDesc expectedKind}"

def expectPreparedSequenceBuiltinWholeNumberSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Int :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .wholeNumber fun descriptor arg =>
    match arg with
    | .wholeNumber number => pure number
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .wholeNumber}"

def expectPreparedSequenceBuiltinValueSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Result :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .value fun descriptor arg =>
    match arg with
    | .value value => pure value
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .value}"

def expectPreparedNumericItems (b : Builtin)
    (prepared : PreparedSequenceBuiltinInput) : EvalM (List Int) :=
  match prepared.numericItems? with
  | some numbers => pure numbers
  | none =>
      .error (Error.withContext
        s!"internal sequence metadata for {builtinDisplayName b} did not produce numeric items"
        Error.badArity)

/-- Evaluate `order(collection)`.
    `order` eagerly evaluates the full top-level collection, sorts its numeric
    items ascending, preserves duplicates, and materializes the sorted items
    as one list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsAsc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `orderDesc(collection)`.
    `orderDesc` eagerly evaluates the full top-level collection, sorts its
    numeric items descending, preserves duplicates, and materializes the
    sorted items as one list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderDescCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsDesc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `count(collection)`.
    `count` processes top-level collection elements from left to right and
    increments once per element.

    Each atom, string, Boolean, sequence value, or list value counts as one
    top-level element. Sequence and list values are not flattened or recursively inspected, and empty
    collections return `0`. -/
def evalCountCounted (items : List Result) : EvalM CountedResult := do
  pure (Result.atom (Int.ofNat items.length), 1)

/-- Evaluate `contains(collection, item)`.
    `contains` checks whether any extracted top-level item equals the searched
    suffix item using ordinary KatLang value equality.

    Search is top-level only: sequence values compare as sequence values and are
    not recursively flattened or inspected. The result is a Boolean value:
    `true` when some item equals `item`, otherwise `false` (so an empty
    collection yields `false`). -/
def evalContainsCounted (items : List Result) (searched : Result) : EvalM CountedResult := do
  let found := items.any (fun item => item == searched)
  pure (Result.bool found, 1)

/-- Evaluate `distinct(collection)`.
    `distinct` removes later duplicate top-level items while preserving the
    first occurrence of each item and the original left-to-right order.

    Equality follows ordinary KatLang value semantics on extracted top-level
    items: atoms compare by numeric value, strings by exact string value, and
    sequence/list values structurally by their elements. Sequence and list
    values stay intact and are not flattened. The kept items are materialized
    as one list value: empty collections yield `[]`, and a
    single kept item forms `[item]` (so `distinct(((), ()))` yields `[()]`). -/
def evalDistinctCounted (items : List Result) : EvalM CountedResult := do
  let distinctItems := dedupList items
  pure (makeCollectionListResult distinctItems)

/-- Evaluate `first(collection)`: SELECT the first top-level collection
    element. The element is returned exactly as stored and re-counted through
    the ordinary value boundary (`Result.valueCount`), exactly like
    `collection[0]` — a selected sequence or list stays one value, a selected
    `()` emits zero values, and only an explicit spread opens the selection.
    An empty collection has no position to select: `badIndex`, the outcome of
    `collection[0]` (SEQ-04, Q-27; the empty policy reports it first).
    Laws: `first_is_select_zero`, `first_empty_is_badIndex`, `first_is_selection_at_zero`.
    C#: `EvalFirstCounted`. -/
def evalFirstCounted (items : List Result) : EvalM CountedResult := do
  match items with
  | first :: _ => pure (first, Result.valueCount first)
  | [] => .error Error.badIndex

/-- Evaluate `last(collection)`: SELECT the last top-level collection element
    through the same value boundary as `evalFirstCounted` and
    `collection[count - 1]`. An empty collection has no position to select:
    `badIndex`. Laws: `last_is_select_last`, `last_empty_is_badIndex`,
    `last_is_selection_at_count_minus_one`.
    C#: `EvalLastCounted`. -/
def evalLastCounted (items : List Result) : EvalM CountedResult := do
  match items.getLast? with
  | some last => pure (last, Result.valueCount last)
  | none => .error Error.badIndex

/-- Evaluate `take(collection, count)`.
    `take` returns the first `count` extracted top-level items unchanged,
    materialized as one list value.
    `count` is a fixed control argument after the `collection` argument.

    Non-positive counts return the empty list `[]`. Counts larger than the
    item count return all items. Nested sequence and list values stay intact
    as exact elements (so `take(((1, 2), (3, 4)), 1)` yields `[(1, 2)]`), and
    the original top-level order is preserved. -/
def evalTakeCounted (items : List Result) (count : Int) : EvalM CountedResult := do
  let taken :=
    if count <= 0 then
      []
    else
      items.take (Int.toNat count)
  pure (makeCollectionListResult taken)

/-- Evaluate `skip(collection, count)`.
    `skip` returns the extracted top-level items after the first `count`
    items, preserving item identity and original order, materialized as one
    list value.
    `count` is a fixed control argument after the `collection` argument.

    Non-positive counts keep all items. Counts larger than the item count
    return the empty list `[]`. Nested sequence and list values stay intact
    as exact elements. -/
def evalSkipCounted (items : List Result) (count : Int) : EvalM CountedResult := do
  let remaining :=
    if count <= 0 then
      items
    else
      items.drop (Int.toNat count)
  pure (makeCollectionListResult remaining)

/-- Evaluate `min(collection)`.
    `min` compares top-level sequence items from left to right and
    returns the smallest numeric element.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalMinCounted (numbers : List Int) : EvalM CountedResult := do
  let rec minLoop : List Int -> Int -> EvalM Int
    | [], currentMin => pure currentMin
    | n :: rest, currentMin =>
        minLoop rest (if n < currentMin then n else currentMin)
  match numbers with
  | [] => .error (Error.illegalInEval "min requires a non-empty collection")
  | first :: rest => do
      let minimum <- minLoop rest first
      pure (Result.atom minimum, 1)

/-- Evaluate `max(collection)`.
    `max` compares top-level sequence items from left to right and
    returns the largest numeric element.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalMaxCounted (numbers : List Int) : EvalM CountedResult := do
  let rec maxLoop : List Int -> Int -> EvalM Int
    | [], currentMax => pure currentMax
    | n :: rest, currentMax =>
        maxLoop rest (if n > currentMax then n else currentMax)
  match numbers with
  | [] => .error (Error.illegalInEval "max requires a non-empty collection")
  | first :: rest => do
      let maximum <- maxLoop rest first
      pure (Result.atom maximum, 1)

/-- Evaluate `sum(collection)`.
    `sum` processes top-level sequence items from left to right and adds them
    into one numeric total.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively summed, strings
    are rejected, and empty collections return `0`. -/
def evalSumCounted (numbers : List Int) : EvalM CountedResult := do
  let total := numbers.foldl (fun acc n => acc + n) 0
  pure (Result.atom total, 1)

/-- Evaluate `avg(collection)`.
    `avg` processes top-level sequence items from left to right,
    accumulates their numeric total, and divides by the element count.
    The integer core truncates the quotient toward zero (Int.tdiv), matching
    the truncating division convention of `div`/`mod`; the decimal runtime
    rounds the exact fractional average once to Decimal128.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalAvgCounted (numbers : List Int) : EvalM CountedResult := do
  match numbers with
  | [] => .error (Error.illegalInEval "avg requires a non-empty collection")
  | values =>
      let total := values.foldl (fun acc n => acc + n) 0
      pure (Result.atom (total.tdiv (Int.ofNat values.length)), 1)

/-- Assemble the argument bundle for extension dot-call fallback: DOT-CALL
    PASSES A VALUE — `receiver.F(C, D)` is exactly the bundle of the written
    call `F(receiver, C, D)`, the ORIGINAL receiver expression as the ordinary
    first argument slot followed by the written extra arguments. Assembly is
    independent of the resolved callee: the receiver is never pre-expanded,
    never unwrapped, never given a supply of its own, and no parameter shape
    is inspected; a spread receiver is the ordinary spread slot `F(R*, …)`.
    Laws (argument PREPARATION only; that the bundle then reaches the ordinary funnel
    `evalResolvedCallCounted` is the body `EvalBody.callLexicalWithReceiverCounted`, a kernel term
    since R7, but no end-to-end dot-funnel theorem is stated):
    `dot_receiver_is_ordinary_leading_argument`,
    `spread_dot_receiver_is_ordinary_spread_argument` (`KatLangArityLaws.lean`).
    C#: `BuildLexicalReceiverCallArgs`. -/
def prepareLexicalDotCallArgs (receiver : Expr) (extraArgs : Option OutputBundle)
    : OutputBundle :=
  [receiver] ++ extraArgs.getD []


--------------------------------------------------------------------------
-- Open resolution
--------------------------------------------------------------------------

/-- The fuel of `openStructure`: the surface pass never forms a reference cycle (OD-D) and a
    host-built static cycle is refused before evaluation (`staticAliasCycle`), so a chase still
    landing on a reference after this many hops is reported as the alias cycle it is. -/
def openStructureFuel : Nat := 4096

/-- The member steps of an open target reference's static path (`openStructure`): each receiver
    read through `structureOf`, each DECLARED member wired to it and checked for accessibility from the
    open's site; `none` when the path ends in the `.Algorithm` intrinsic on a structural miss (a runtime
    link, its own namespace). An inaccessible or branch-only member names the step's RECEIVER as written
    (`receiverName`, the path's head extended by each step), as every navigation does: `open A` with
    `A = G.Sub` reports what `open G.Sub` reports. C#: the navigation loop of `Evaluator.OpenStructure`. (A block
    head is spelled by each engine's renderer — `(inline library)` here, `{...}` in C# — at every navigation site;
    the object description is a rendered description, `docs/design/differential-observations.md`.) -/
def openNavigateWith (structureOf : Algorithm → EvalM Algorithm) (ctx : EvalCtx)
    (notStatic : Error) : Algorithm → String → List Ident → EvalM (Option Algorithm)
  | value, _, [] => pure (some value)
  | value, receiverName, member :: rest => do
      let receiver <- structureOf value
      match Algorithm.lookupPropDefAny? receiver member with
      | some prop =>
          if !(memberAccessible? ctx receiver prop) then
            .error (Error.localOnlyProperty receiverName member prop.exposure)
          else
            openNavigateWith structureOf ctx notStatic (childOfInContext receiver prop.alg ctx)
              (receiverName ++ "." ++ member) rest
      | none =>
          -- `X.Algorithm` on a structural miss is the intrinsic: a runtime link.
          if member == "Algorithm" then pure none
          else if Algorithm.conditionalBranchesDefineProperty receiver member then
            .error (Error.localOnlyProperty receiverName member .localConditional)
          else .error notStatic

/-- THE STRATIFIED STRUCTURE OF AN OPEN TARGET (OD-C, M4★): a TRANSPARENT REFERENCE opens its target's
    namespace, resolved WITHOUT any `open` — the reference's static target is looked up DIRECTLY in
    the reference's own declarations and its declaring chain (`lookupLexicalDirect`, never an open,
    never the evaluation of anything), and its member steps navigate DECLARED members, each receiver
    read through this same structure — so resolving an open target never depends on an open: a target
    only an open provides is unresolved (`unknownName`). A structural CARRIER is its own namespace
    (its own public declarations; its output is never evaluated), and so is a RUNTIME reference — a
    parameter row, a parameter-rooted path, an `.Algorithm` link on the intrinsic route: its own,
    empty, namespace, so nothing is opened dynamically. Every non-alias is itself.
    C#: `Evaluator.OpenStructure`. -/
def openStructure : Nat → EvalCtx → Algorithm → EvalM Algorithm
  | 0, _, a =>
      match a with
      | .alias _ _ _ _ _ true => .error (Error.illegalInEval aliasCycleMessage)
      | _ => pure a
  | fuel + 1, ctx, a =>
      match a with
      | .alias _ _ _ target _ true =>
          match Expr.staticAliasPath? target with
          | none => pure a
          | some (head, steps) => do
              let notStatic : Error := Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target))
              let start <- match head with
                | .resolve name =>
                    match lookupLexicalDirect a name with
                    | some found => pure found
                    | none => .error (Error.unknownName name)
                | .algorithmExpr block => pure (childOfInContext a block ctx)
                | _ => .error notStatic
              match <- openNavigateWith (fun value => openStructure fuel ctx value) ctx notStatic start (openExprName head) steps with
              | none => pure a
              | some value => openStructure fuel ctx value
      | _ => pure a

/-- Algorithm resolution using only direct lexical lookup (no opens).
    Used for resolving open expressions to avoid circularity.

    Open resolution wires the resolved head to the scope where direct
    lexical lookup found it — its lexical definition site — and never to
    arbitrary caller context.  This enforces open isolation: a library's
    internal lexical structure is self-contained and never smuggles caller
    context.

    Open restrictions:
    - Only `Expr.openForm?` forms are permitted (structural references to libraries only).
    - Direct lexical heads (`open Name`) use ordinary direct lexical lookup
      (`lookupLexicalDirect`, local properties plus the parent chain, no opens).
      The head may be private if it is lexically visible. This includes the
      common surface form where `open Lib` appears before a later
      `Lib = { ... }` definition in the same algorithm body.
    - A head that a PARAMETER owns never arrives here as `.resolve`: the
      surface layer classifies every open head by the ordinary owner walk
      (`elaborateOpenHead`) and elaborates a parameter-owned head to `.param`,
      which `Expr.openForm?` rejects — so a static open can never bypass an
      established parameter and reach a farther same-named property, and
      nothing is opened dynamically.
    - Builtins are still rejected: even if lexical lookup finds one, it is
      not a valid open target.
    - **Public-path policy**: Qualified property access in open paths
      (e.g., `open Lib.Sub`) still requires each dotted member after the
      direct lexical head to be public. `Algorithm.lookupPublicProp`
      enforces this unchanged rule.
    - Inline/load-elaborated block opens keep isolation from the opener while
      retaining the global call-stack base, which is the builtin prelude in
      normal runs.
    - `open` exposes only public properties of the resolved algorithm.
      Opening an algorithm never makes its private properties visible.

    Examples:
    - `open Lib` where private `Lib` is defined later in the same algorithm body → OK
    - `open Lib.PrivateSub` where `PrivateSub` has `isPublic = false` → Error (notPublicProperty)
    - Structural access `Lib.PrivateSub.X` in code → OK (uses Algorithm.lookupProp, sees private)
    - `open Lib` does NOT expose private properties of Lib (filtered by lookupOpenProperties) -/
def resolveAlgForOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  -- This match mirrors `Expr.openForm?` case-for-case (algorithmExpr /
  -- resolve / no-arg dotCall / reject-the-rest) but matches the
  -- expression directly so the dotted-path recursion is visibly structural.
  -- Keep the two in sync.
  match e with
  | .algorithmExpr a => pure (wireOpenBlockToGlobalScope ctx a)
  -- A capture is a value boundary, never algorithm/namespace identity:
  -- `open` consumes algorithm identity, so a captured target such as
  -- `open (M, N)` is not openable. Top-level capture targets are already
  -- rejected by resolveAllOpens' open-form validation; this arm is reached
  -- through dotted-path recursion (`open (X, Y).B`) and prebuilt ASTs — the
  -- C# front end refuses such a head statically (`BadOpenForm`).
  | .capture _ => throw (Error.badOpenForm "captured value groups cannot be opened")
  | .resolve n =>
    match ctx.callStack with
    | a::_ =>
      match lookupInParentsDirect (scopeInContext a ctx) n with
      | some r =>
          if r.isBuiltin then .error (Error.illegalInOpen s!"builtin '{n}'")
          else pure r
      | none => .error (Error.unknownName n)
    | [] => .error (Error.unknownName n)
  -- Only argumentless dot paths resolve as open targets. Grace-marked open
  -- targets are rejected by the C# front end before Lean encoding.
  | .dotMember o n _ none => do
    -- A transparent reference receiver is navigated as its target (OD-C), resolved without opens.
    let a <- openStructure openStructureFuel ctx (<- resolveAlgForOpen o ctx)
    -- First check if property exists at all so ownership still wins over opens.
    match Algorithm.lookupPropDefAny? a n with
    | some p =>
        if p.alg.isBuiltin then
          .error (Error.illegalInOpen s!"builtin not allowed in open: {openExprName o}.{n}")
        else if !p.isPublic then
          .error (Error.notPublicProperty (openExprName o) n)
        -- Open paths select public members before checking contextual accessibility.
        else if !(memberAccessible? ctx a p) then
          .error (Error.localOnlyProperty (openExprName o) n p.exposure)
        else
          -- Property exists; check if it's public
          match Algorithm.lookupPublicProp a n with
          | some publicAlg => pure (childOfInContext a publicAlg ctx)
          | none   => .error (Error.notPublicProperty (openExprName o) n)
    | none =>
        if Algorithm.conditionalBranchesDefineProperty a n then
          .error (Error.localOnlyProperty (openExprName o) n .localConditional)
        else
          .error (Error.unknownProperty (openExprName o) n)
  -- load('url') is not a core Expr constructor; it is represented as
  -- Call(Resolve("load"), ...) at parse time and elaborated to Block before
  -- open resolution.  If it reaches here un-elaborated, it falls through to
  -- the call/default case below (exactly as `Expr.openForm?` maps it to none).
  | _ =>
      throw (Error.badOpenForm s!"{Expr.kind e}: {openExprName e}")

/-- Resolve an open expression to a library algorithm and apply the PROVIDER rule: the
    resolved provider — the whole target, never an intermediate of a dotted path — must
    need no call (`Algorithm.requiresArguments`). A parameterized algorithm or a clause
    family has no members outside an activation, and `open` never creates one (there is
    no `open Lib(5)`), so it is refused with `illegalInOpen`; a parameterized HEAD of a
    dotted target is navigated by identity like any structural receiver (`open Lib.Sub`
    with `Lib(p)` opens a self-contained `Sub`), and a member of it that captures `p` is
    refused at the access by `memberAccessible?`. C#: `Evaluator.ResolveOpen`. -/
def openTargetRequiresArgumentsMessage (target : String) : Algorithm -> String
  | .conditional _ _ _ _ =>
      s!"'{target}' cannot be opened because it is a clause family, not a namespace."
  -- The failed rule is MOD-04's EMPTY EFFECTIVE PARAMETER LIST, not a need for supplied
  -- arguments: a collector-only `Only(*xs)` binds an empty supply, yet is no provider (X-27).
  | a =>
      s!"'{target}' cannot be opened because open providers must have an empty effective " ++
        s!"parameter list (found: {String.intercalate ", " (Algorithm.params a)})."

def resolveOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  -- OD-C (M4★): a transparent reference opens its TARGET's namespace, under the target's own
  -- provider identity (so `open A, Lib` with `A = Lib` is ONE provider).
  let provider <- openStructure openStructureFuel ctx (<- resolveAlgForOpen e ctx)
  if provider.isBuiltin then
    .error (Error.illegalInOpen s!"builtin '{openExprName e}'")
  else if provider.requiresArguments then
    .error (Error.illegalInOpen (openTargetRequiresArgumentsMessage (openExprName e) provider))
  else
    pure provider

/-- The head of an argumentless open path. An argument-bearing edge stops the walk,
    just as it stops open resolution. C#: `AstHelpers.OpenTargetHead`. -/
def Expr.openTargetHead : Expr → Expr
  | .dotMember receiver _ _ none => receiver.openTargetHead
  | e => e

/-- Resolve all opens of an algorithm upfront: the level's PROVIDERS, each counted once.
    Q-19 D-I (decided 2026-10-06): written targets that resolve to the same semantic
    provider count once, whatever their spelling or position — the provider identity is
    the language's one callable identity (`sameRepeatedCallableIdentity`, NEED-04's
    relation: declaration, declaring scope, compatible activations). So `open M, M`,
    `open Sub, Lib.Sub` for one declaration `Sub` of `Lib`, and two loads of one module
    are one provider, while two written blocks or two declarations stay two, however
    equal their members or values. The first occurrence names the provider; which
    providers the level has never depends on order. A repeated written-target key
    (`openExprName`; inline block heads, dotted paths from them included, are keyed by
    position) is skipped before resolution as a pure optimization — it resolves the same
    target. Validates all open expressions first for fail-fast diagnostics.
    C#: `Evaluator.ResolveAllOpens`. -/
def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
  let rawOpens := Algorithm.opens a
  -- Skip a repeated written-target key (it resolves the same target); inline blocks use
  -- positional keys, so this never merges two written blocks.
  let tagged := rawOpens.mapIdx (fun idx e =>
    let key := match e.openTargetHead with
      | .algorithmExpr _ => s!"(inline#{idx})"   -- * unique per original position
      | .capture _        => s!"(inline#{idx})"
      | _                 => openExprName e
    (key, e))
  let mut seen : List String := []
  let mut acc : List (Prod String Expr) := []
  for (k, e) in tagged do
    if !seen.elem k then
      seen := k :: seen
      acc := (k, e) :: acc
  acc := acc.reverse
  -- Validate all open expressions first (fail-fast with clear errors)
  acc.forM fun (k, e) =>
    if !Expr.isOpenForm e then
      throw (Error.badOpenForm s!"{Expr.kind e}: {k}")
    else
      pure ()
  -- Then resolve (each open wrapped with context using its key), counting each semantic
  -- provider once: a target resolving to the callable identity of an earlier one is that
  -- provider. A provider whose declaration is not identified (a hand-built tree that never
  -- passed the run's identification) is its own provider — C# compares declarations by
  -- reference, so an unidentified declaration is never another's.
  let resolved <- acc.mapM (fun (key, e) => do
    let lib <- withCtx (CtxMsg.openMsg key) (resolveOpen e ctx)
    pure { key := key, expr := e, lib := lib : ResolvedOpen })
  pure (resolved.foldl (fun (providers : List ResolvedOpen) r =>
    if r.lib.declarationId.isSome
        && providers.any (fun p => sameRepeatedCallableIdentity p.lib r.lib) then providers
    else providers ++ [r]) [])

/-- Lookup in opened namespaces with ambiguity error — the ONE open-lookup
    implementation in the ownership-first chain. It returns the full
    `ResolvedProperty` (owner + binding + wired algorithm) because the cached
    property-style path needs the binding; algorithm-only consumers project
    `ResolvedProperty.alg` instead of running a second lookup.
    Ordering rule: opens are searched in declaration order (first wins for
    single-provider lookups; multiple providers trigger ambiguousOpen).
    Only public properties are visible through opens.
    Returns:
      * ok none              if no open provides `name` publicly
      * ok (some prop)       if exactly one open provides it publicly (alg wired to library parent)
      * error ambiguousOpen if multiple opens provide it publicly -/
def lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM (Option ResolvedProperty) := do
  let ctx' := { ctx.push a with headScope := some (scopeInContext a ctx) }
  let resolvedOpens <- resolveAllOpens a ctx'
  let mut hits : List OpenPropertyHit := []
  for ri in resolvedOpens do
    match Algorithm.lookupPropDefPublic? ri.lib name with
    | some prop =>
        hits := {
          provider := ri.key,
          property := {
            owner := ri.lib,
            binding := prop,
            alg := childOfInContext ri.lib prop.alg ctx
          }
        } :: hits
    | none => pure ()
  hits := hits.reverse

  -- SELECTION IS BY VISIBILITY ONLY: a public member is provided by its open whatever its
  -- exposure (it takes part in precedence and ambiguity like any provided name), and
  -- accessibility is checked on the selected member afterwards, from the site — the
  -- algorithm whose body reads the name (the original context's head), not the level
  -- whose opens are consulted. Which declaration a name selects therefore never depends
  -- on exposure, which is what lets the surface layer reproduce the selection before
  -- exposure is classified.
  match hits with
  | [] => pure none
  | [h] =>
      if memberAccessible? ctx h.property.owner h.property.binding then
        pure (some h.property)
      else
        .error (Error.localOnlyProperty h.provider name h.property.binding.exposure)
  | hs => .error (Error.ambiguousOpen name (hs.map (fun hit => hit.provider)))

--------------------------------------------------------------------------
-- Lexical resolution
--------------------------------------------------------------------------

/-- Structural-only lookup in parent chain (no opens anywhere).
    Ownership-first model: structural properties take precedence.
    Example: If parent defines Pi and opens Math also exports Pi,
    the parent's Pi wins. To get Math.Pi, use Math.Pi syntax.
    This is the ONE structural parent-chain lookup; algorithm-only consumers
    project `ResolvedProperty.alg`. -/
def lookupInParentsStructuralProperty (sc : ScopeCtx) (name : Ident)
    : Option ResolvedProperty :=
  match lookupPropDefAny? (ScopeCtx.props sc) name with
  | some prop =>
      -- The binding belongs to sc itself. `forOpens sc` is a lookup wrapper
      -- whose PARENT is sc; using it as owner adds a spurious scope level to
      -- the property key, splitting an ancestor read from a direct read.
      -- The owner rebuilt from the level carries the level's own parameters, so its
      -- `asScopeCtx` — the cache key's owner identity — equals the declaring
      -- algorithm's own.
      let owner := match sc with
        | .mk parent params opens props output _ _ id =>
            Algorithm.mk parent (Algorithm.normalParameters params) opens props output id
      some {
        owner := owner,
        binding := prop,
        alg := Algorithm.withParent (some sc) prop.alg
      }
  | none =>
      match sc with
      | .mk (some sc') _ _ _ _ _ _ _ => lookupInParentsStructuralProperty sc' name
      | .mk none _ _ _ _ _ _ _       => none

/-- Open-based lookup in parent chain (helper for lookupOpenPropertiesInChain). -/
def lookupOpenPropertiesInParentChain (sc : ScopeCtx) (name : Ident)
    (ctx : EvalCtx) : EvalM (Option ResolvedProperty) := do
  let tempAlg := Algorithm.forOpens sc
  match (<- lookupOpenProperties tempAlg name ctx) with
  | some r => pure (some r)
  | none =>
      match sc with
      | .mk (some sc') _ _ _ _ _ _ _ => lookupOpenPropertiesInParentChain sc' name ctx
      | .mk none _ _ _ _ _ _ _       => pure none

/-- Open-based lookup across the algorithm chain (current first, then parents).
    Checks opens at each level of the parent chain as fallback. -/
def lookupOpenPropertiesInChain (a : Algorithm) (name : Ident)
    (ctx : EvalCtx) : EvalM (Option ResolvedProperty) := do
  match (<- lookupOpenProperties a name ctx) with
  | some r => pure (some r)
  | none =>
      match Algorithm.parent a with
      | some sc => lookupOpenPropertiesInParentChain sc name ctx
      | none    => pure none

/-- Full lexical lookup with ownership-first model — the CANONICAL chain:
    1. Local properties (owned by this algorithm)
    2. Parent chain structural properties (owned by ancestors)
    3. Opens as fallback (foreign namespaces)

    This ensures structural ownership always takes precedence over opens.
    It keeps the resolved owner and binding for the zero-argument property
    cache; `lookupLexical` is its algorithm projection, so the
    ownership-first / dedup / ambiguity rules exist exactly once. The selected
    binding is returned RAW — an alias as the alias — for the consumers that
    normalize it themselves: a written dot receiver's head (`resolveDotReceiver`,
    which reads it through its STRUCTURE, so a transparent reference navigates
    its target's declarations, M4★), the supplied-cell projection, and alias
    resolution itself (`resolveAliasStepWith`); every other consumer reads it
    through `lookupLexicalProperty`, which makes it callable.
    C#: `Evaluator.LookupLexicalRaw`. -/
def lookupLexicalPropertyRaw (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM ResolvedProperty := do
  match Algorithm.lookupPropDefAny? a name with
  | some prop =>
      pure {
        owner := a,
        binding := prop,
        alg := childOfInContext a prop.alg ctx
      }
  | none =>
      match Algorithm.parent a with
      | some sc =>
          match lookupInParentsStructuralProperty sc name with
          | some r => pure r
          | none =>
              match (<- lookupOpenPropertiesInChain a name ctx) with
              | some r => pure r
              | none   => .error (Error.unknownName name)
      | none =>
          match (<- lookupOpenPropertiesInChain a name ctx) with
          | some r => pure r
          | none   => .error (Error.unknownName name)

/-- The member steps of a static alias path (`resolveAliasStepWith`): each receiver read through
    `structureOf`, each declared member wired to it and checked for accessibility, the binding of
    the last member selected (`last`). C#: the navigation loop of `Evaluator.ResolveAliasStep`. -/
def aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (stepCtx : EvalCtx) (notStatic : Error) :
    Algorithm → Option ResolvedProperty → String → List Ident → EvalM (Option ResolvedProperty)
  | _, last, _, [] => pure last
  | value, _, receiverName, member :: rest => do
      let some receiver <- structureOf value stepCtx | .error notStatic
      match Algorithm.lookupPropDefAny? receiver member with
      | some p =>
          if !(memberAccessible? stepCtx receiver p) then
            .error (Error.localOnlyProperty receiverName member p.exposure)
          else
            let wired := childOfInContext receiver p.alg stepCtx
            aliasStepNavigateWith structureOf stepCtx notStatic wired
              (some { owner := receiver, binding := p, alg := wired }) (receiverName ++ "." ++ member) rest
      | none =>
          if Algorithm.conditionalBranchesDefineProperty receiver member then
            .error (Error.localOnlyProperty receiverName member .localConditional)
          else
            .error notStatic

/-- One STATIC STEP of an alias chase (M4★): the BINDING the alias `step`'s written `target` selects
    in the alias's OWN scope — the alias pushed as the head, exactly where its body would be
    evaluated — with its owner and declaration (the terminal binding a bare read and a publication
    origin of the chain use, OD-E): a name by the ownership-first lexical lookup, RAW, so a target
    that is itself an alias continues the chase; a member path by structural navigation of DECLARED
    members, each RECEIVER read through its STATIC STRUCTURE (`structureOf`: a transparent reference is
    its target's, a carrier its own — production: the static-only structure chase, which never
    projects a cell), each member wired to its receiver and checked for accessibility from the alias's
    site exactly like `resolveDotReceiver` navigates (a member declared only in branches is the same
    `localOnlyProperty` error). A target that is not a static path, or a path step whose receiver has
    no static structure or declares no such member, has no callable: `illegalInEval` — only a
    host-built tree has either, since the surface pass forms an alias over a statically known member
    only. C#: `Evaluator.ResolveAliasStep`. -/
def resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (step : Algorithm) (target : Expr) (ctx : EvalCtx) : EvalM ResolvedProperty := do
  let stepCtx := ctx.push step
  let notStatic : Error := Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target))
  match Expr.staticAliasPath? target with
  | none => .error notStatic
  | some (.resolve name, steps) =>
      let resolved <- lookupLexicalPropertyRaw step name stepCtx
      match <- aliasStepNavigateWith structureOf stepCtx notStatic resolved.alg (some resolved) name steps with
      | some found => pure found
      | none => .error notStatic
  | some (.algorithmExpr block, steps) =>
      match <- aliasStepNavigateWith structureOf stepCtx notStatic (wireToCaller stepCtx block) none
          (openExprName (.algorithmExpr block)) steps with
      | some found => pure found
      | none => .error notStatic
  | some (_, _) => .error notStatic

/-- THE VALUE VIEW of a runtime-target alias whose binding cell projected NO callable identity
    (L-RUN, M4★): the same written declaration, wired where the alias is, with the alias's own opens
    and declarations and its one row as its output, invoked as a zero-parameter algorithm — so a
    non-empty supply is the binder's ordinary cardinality failure, and a zero-supply invocation
    returns the binding cell's VALUE (`valueViewCell?`), never a rerun of the row. It has no members
    of interest and no CALLABLE: a value-only reference projects none. C#:
    `Algorithm.User(Algorithm.Alias)`. -/
def Algorithm.aliasPropertyView : Algorithm -> Algorithm
  | .alias parent opens props target id _ => .mk parent [] opens props [target] id
  | other => other

/-- The activation identities along a scope chain, innermost first. -/
def ScopeCtx.activationChain : Option ScopeCtx -> List (Option Nat)
  | none => []
  | some (.mk parent _ _ _ _ _ activation _) => activation :: ScopeCtx.activationChain parent

/-- The memo key of a runtime-target alias's BINDING CELL (META-S3-2): the alias's declaration,
    resolving scope shape and the activations of its declaring scope chain — ONE cell per declaring
    scope and activation, the run-level case (no activation) included. A shared declaration wired
    under different namespaces must not share its cell merely because both scopes are unactivated.
    C#: `Evaluator.AliasTargetKey` over the alias's declaration and structural owner identity, on the
    nearest activation's memo (or the run's). -/
def aliasCellKey (wired : Algorithm) : String :=
  reprStr wired.declarationId ++ "@" ++ reprStr (wired.parent.map cacheScopeShape)
    ++ "@" ++ reprStr (ScopeCtx.activationChain wired.parent)

/-- The VISITED KEY of an alias chase (`resolveAliasChase`, ALIAS-UNIFY-1 review): the alias's BINDING
    identity — its declaration, resolving scope shape and the activations of its declaring scope chain
    (`aliasCellKey`) — so two distinct declarations of one shape, and one declaration under two
    activations (a carrier passed from one call into the next), are two steps, never a cycle; an alias
    without a declaration identity (host-built) is keyed by its shape as well. C#:
    `Evaluator.AliasChaseVisit`. -/
def aliasChaseKey (a : Algorithm) : String :=
  aliasCellKey a ++ (match a.declarationId with
    | some _ => ""
    | none => "#" ++ reprStr (cacheAlgorithmShape a))

/-- The RECORDED binding cell of a non-parameter row (`aliasBindingCell`): the recorded address, or
    the row supplied in the alias's entered body context and recorded under `aliasCellKey`. -/
def aliasBindingCellRecorded (wired : Algorithm) (target : Expr) (ctx : EvalCtx) : EvalM Nat := do
  let key := aliasCellKey wired
  match lookupAssoc key (← get).aliasCells with
  | some address => pure address
  | none =>
    let declaringCtx ← enterAlgorithmBody wired ctx []
    let address ← supplyNeed target declaringCtx []
    modify fun s => { s with aliasCells := (key, address) :: s.aliasCells }
    pure address

/-- THE BINDING CELL of the runtime-target alias `wired` with row `target` (FWD-02, META-S3-2): the
    row supplied in the alias's OWN declaring context — the alias entered as the head, exactly where
    its body is evaluated — through the ONE supplier (`supplyNeed`, the construction META-S3-1's
    callee cell uses). A parameter row IS that parameter's own cell (NEED-01 transport, nothing
    allocated, `aliasBindingCell_parameter_transport`); every other row is established ONCE per
    declaration and declaring activation (`aliasCellKey`) and recorded in `EvalState.aliasCells`, so
    every later use reads the record (`aliasBindingCell_canonical`). Establishing it evaluates
    nothing: it may enter the alias's body scope, allocate one suspended cell and record its address
    (`aliasBindingCell_inert`). It is established lazily ONCE per declaring binding activation (L-RUN,
    M4★): its VALUE is the alias's bare read (`aliasValue`) and a value view's zero-supply invocation
    (`valueViewCell?`), its CALLABLE the alias's runtime identity, so every observation shares its
    receiver work and the supplied computation never reruns. C#: `Evaluator.AliasBindingCell`. -/
def aliasBindingCell (wired : Algorithm) (target : Expr) (ctx : EvalCtx) : EvalM Nat :=
  match target with
  | .param _ => supplyNeed target (ctx.push wired) []
  | _ => aliasBindingCellRecorded wired target ctx

/-- THE VALUE VIEW'S CELL (L-RUN, M4★, superseding D4's first-observation claim): the recorded binding
    cell of the runtime-target alias whose value view `a` is (`Algorithm.aliasPropertyView` keeps the
    alias's declaration and scope, so `aliasCellKey` finds it), read AFTER the ordinary binder's
    cardinality gate — a zero-supply invocation of a value-only reference returns that cell's VALUE
    every time, so the supplied computation never reruns. A parameter row records no cell: its view
    reads the parameter, whose own cell it is. Reads only. C#: `Evaluator.ValueViewCell`. -/
def valueViewCell? (a : Algorithm) : EvalM (Option Nat) := do
  match a with
  | .mk _ [] _ _ [_] _ => pure (lookupAssoc (aliasCellKey a) (← get).aliasCells)
  | _ => pure none

/-- The outcome of ONE runtime step of an alias chase (META-S3-2, M4★): `terminal` — the binding cell
    supplied no callable identity (the alias is a value view); or the projected identity the chase
    continues with (`continue`). -/
inductive RuntimeAliasStep where
  | terminal
  | continue (identity : Algorithm)

/-- ONE RUNTIME STEP of an alias chase over its CALLABLE capability `project` (META-S3-2): the
    runtime-target alias `owner`'s binding cell (`aliasBindingCell`), projected. Absence of an
    identity is `terminal` (`runtimeAliasStep_absence_is_terminal`); a supplied identity continues
    the chase — at ANY arity (L-RUN, M4★: no eligibility gate); a projection FAILURE propagates
    unchanged — it is never absence (`runtimeAliasStep_failure_propagates`). Production:
    `resolveAliasChase` installs `projectNeedCallable`. C#: the runtime arm of
    `Evaluator.ResolveAliasTarget`. -/
def runtimeAliasStepWith (project : Nat → EvalM (Option Algorithm)) (owner : Algorithm) (target : Expr)
    (ctx : EvalCtx) : EvalM RuntimeAliasStep := do
  match ← project (← aliasBindingCell owner target ctx) with
  | none => pure .terminal
  | some identity => pure (.continue identity)

/-- Runtime-created callable wrappers have identities too. C# mints a DeclarationIdentity
    on every new Algorithm.User; retaining this token through parameter forwarding makes
    one wrapper forwarded twice different from two separately resolved dot results. -/
def identifyRuntimeAlgorithm (algorithm : Algorithm) : EvalM Algorithm := do
  let state <- get
  set { state with nextRuntimeDeclaration := state.nextRuntimeDeclaration + 1 }
  pure (algorithm.withDeclarationId (some (.runtime state.nextRuntimeDeclaration)))

/- Total CALLABLE projection control (META-S3-0a), the CALLABLE twin of `NeedDemand`.
    Written-expression resolution stays an explicit callback; this is not a second
    resolver. C#: `NeedCell.ProjectCallable` / `ProjectCallableAsync`. -/
namespace NeedProjection

/-- The CALLABLE computation of a cell's suspension. Produced data and a collector slice
    carry no identity, nor does a capture (`shouldWrapArgExprAsValue`); every other written
    expression is resolved by `written` in its captured caller context. -/
def suspended (written : Expr → EvalCtx → EvalM (Option Algorithm)) :
    NeedSuspension → EvalM (Option Algorithm)
  | .ready _ => pure none
  | .collector _ => pure none
  | .expression source caller _ =>
    if shouldWrapArgExprAsValue source then pure none else written source caller

/-- THE one CALLABLE completion shell (NEED-06/NEED-09): a completed projection is reused
    and changes nothing; re-entering an active projection is `demandCycle` and leaves its
    `projecting` state in place; otherwise the cell is marked `projecting`, `project` runs
    over its suspension, and the outcome — identity, absence or failure, a propagated
    `demandCycle` included — is published as the cell's sticky CALLABLE outcome. The
    VALUE state is never read or written here. -/
def step (project : NeedSuspension → EvalM (Option Algorithm)) (a : Nat) :
    EvalM (Option Algorithm) := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.callable with
  | .projected outcome => return ← outcome
  | .projecting => throw Error.demandCycle
  | .unprojected =>
    modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with callable := .projecting }) }
    let outcome ← evalAttempt (project cell.suspension)
    modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with callable := .projected outcome }) }
    return ← outcome

end NeedProjection


/-- The structured `notAnAlgorithm` description of a dot expression in CALLEE position
    that carries no callable identity — a computed VALUE (an extension call's or the
    `.string` intrinsic's result, a call result). C#: `Evaluator.ComputedDotCalleeDescription`. -/
def computedDotCalleeDescription : String := "dot result"

/-- The CALLABLE a call's CALLEE carries (DOT-09; Q-18 C-B3). A dot expression carries ONE
    callable identity in every algorithm-capable position, so a dot callee is read through
    the SAME projection a supplied argument is (`projectNeedStructuralMember`, then alias
    normalization — exactly `projectNeedCallable`'s dot arm): an argumentless structural
    path is its member's own callable — `(Box.G)(2)` is the member call `Box.G(2)` and
    `(Box.V)()` the explicit fresh call `Box.V()`, grouping never changing identity — and
    every other dot expression is a computed value with no callable identity. Every other
    callee shape resolves through canonical `resolveAlg`. C#: `Evaluator.ResolveCallee`.
    Written over its two resolvers so the law is a kernel term; the production `resolveCalleeAlg`
    (in the evaluator recursion core, since META-S3-1) installs `projectNeedStructuralMember` and
    `resolveAlg`. -/
def resolveCalleeAlgWith (project : Expr → EvalCtx → EvalM (Option Algorithm))
    (normalize : Algorithm → EvalCtx → EvalM Algorithm)
    (resolve : Expr → EvalCtx → EvalM Algorithm) (f : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  match f with
  | .dotMember _ _ _ _ =>
      match <- project f ctx with
      | some algorithm => normalize algorithm ctx
      | none => .error (Error.notAnAlgorithm computedDotCalleeDescription)
  | _ => resolve f ctx

/-- The ROLE of a builtin's invoking (CALLABLE) slot — its callback, or a
    loop's step: the description of the slot's missing-callability verdict
    (Q-06), a structured semantic description and never a fake zero-parameter
    callable. The per-item invocation frames keep their own names ("filter
    predicate", "map transform", "reduce step").
    C#: `Evaluator.InvokingSlotRoles.Of`. -/
def invokingSlotRole : Builtin -> String
  | .mapBuiltin => "map transform"
  | .filterBuiltin => "filter predicate"
  | .reduceBuiltin => "reduce reducer"
  | .repeatBuiltin => "repeat step"
  | .whileBuiltin => "while step"
  | b => s!"{builtinDisplayName b} callback"

/-- CALLABLE projection of ONE invoking builtin slot — a collection builtin's
    callback (the `filter` predicate, the `map` transform, the `reduce`
    reducer) or a `while`/`repeat` step — made only when the builtin is about
    to invoke it, so an unused invoking slot is never projected or validated
    (CALL-03, LOOP-05). It reads the slot's callable identity alone and never
    demands its VALUE (NEED-06): a slot with no CALLABLE identity is
    `notAnAlgorithm` described by the slot's role (Q-06), the verdict a user
    higher-order parameter reports, raised before any invocation. A slot that
    HAS callable identity keeps every ordinary binder verdict when it is
    invoked. C#: `Evaluator.ProjectInvokingSlot`. -/
def projectInvokingSlot (role : String) : Option Algorithm -> EvalM Algorithm
  | some algorithm => pure algorithm
  | none => .error (Error.notAnAlgorithm role)

/-
Evaluator recursion core.

Everything above the `mutual` block below is helper logic that never re-enters
evaluation by itself: validation, name/open/lexical resolution, parameter-pattern
binding (the Model-C binder core, which reaches evaluation only through the
`NeedChannels` the block passes it),
argument-shape preparation, cache-key construction, and pure builtin
computations — checked as ordinary total definitions wherever Lean can see
termination.

The core (§ The fuel-indexed evaluator core below) intentionally contains only operations that
participate in runtime evaluation recursion, plus thin wrappers used by those operations. Since
R7 (October 2026) it is TOTAL: every operation is one `EvalCall`, its body an ordinary
definition over the recursive answer `rec`, and the recursion is the fuel-indexed iteration of
`evalStep` (KatLang programs may be recursively defined, so evaluation is not structurally
recursive over syntax; the fuel index bounds the depth of active calls instead).

Do not add non-evaluating helpers here — define them above the core so
Lean checks them as total definitions with their own laws. A new recursive operation is a new
`EvalCall` constructor, `EvalCall.Ret` arm, `EvalRec` helper, body and `evalStep` arm (and its
production wrapper below the core); `KatLangArityLaws/EvaluatorCore.lean` then needs its
monotonicity lemma and `KatLangArityLaws/EvaluatorDiscipline.lean` its discipline lemma.

PLAIN/COUNTED OWNERSHIP: for every plain/counted evaluator pair the COUNTED
implementation is canonical and the plain implementation is its value
projection (`.fst` of the counted result) — `eval` projects `evalCounted`,
`evalUserCall`/`evalConditionalCall`/`evalResolvedCall`/`evalCallExpr`/
`evalDotCall`/`applyBuiltin`/`evalAlgOutputCore`/
`evalCaptureValue`/`evalZeroArgPropertyAccess`/`evalResolvedCallbackCall`
project their counted twins. `evalCounted` therefore matches EVERY `Expr`
variant explicitly, with no default arm delegating back to `eval`: the
exhaustive match is the structural guard that a new variant cannot silently
reintroduce reverse (plain-owned) semantics. Plain projections may still be
CALLED from counted code wherever only the value of a subexpression or an
algorithm output is needed — that is a value-boundary read through the
projection, not an ownership reversal, and it recurses only into strictly
smaller work. The one intentionally non-projected sibling family is the
slot-view group (`evalAlgOutputSlots`, `evalExplicitSequenceValue*`), which
returns item lists rather than one counted value.
-/
/-- One inspecting-pattern language shared by ordinary calls, families and callbacks.
    `meta name` (CallReference S1) is a META capture: it binds `name` to a fresh Ready cell
    holding the supplied cell's call reference (`NeedCapabilities.reference`), reified when
    written traversal reaches it; it never demands the supplied cell. -/
inductive NeedPattern where
  | bind (name : Ident) (collecting : Bool := false)
  | sequence (items : List NeedPattern)
  | list (items : List NeedPattern)
  | unpack (items : List NeedPattern)
  | literal (pattern : Pattern)
  | metaRef (name : Ident)
  deriving Repr

def NeedPattern.ofParameter : ParameterPattern -> NeedPattern
  | .capture p => if p.kind == .metaRef then .metaRef p.name else .bind p.name (p.kind == .collecting)
  | .sequenceValue ps => .sequence (ps.map ofParameter)
  | .listValue ps => .list (ps.map ofParameter)
  | .unpacking ps => .unpack (ps.map ofParameter)

def NeedPattern.ofClause : Pattern -> NeedPattern
  | .bind name => .bind name
  | .sequenceValue ps => .sequence (ps.map ofClause)
  | .listValue ps => .list (ps.map ofClause)
  | pattern => .literal pattern

def NeedPattern.toParameter : NeedPattern -> ParameterPattern
  | .bind name collecting => .capture { name := name, kind := if collecting then .collecting else .normal }
  | .sequence ps => .sequenceValue (ps.map toParameter)
  | .list ps => .listValue (ps.map toParameter)
  | .unpack ps => .unpacking (ps.map toParameter)
  | .literal _ => .capture { name := "_" }
  | .metaRef name => .capture { name := name, kind := .metaRef }

def NeedPattern.names : NeedPattern -> List Ident
  | .bind name _ => [name]
  | .metaRef name => [name]
  | .sequence ps | .list ps | .unpack ps => ps.flatMap names
  | .literal _ => []

def NeedPattern.isCollecting : NeedPattern -> Bool
  | .bind _ collecting => collecting
  | _ => false

def needMinimumSuppliedSlots (patterns : List NeedPattern) : Nat :=
  patterns.length - (patterns.filter NeedPattern.isCollecting).length

def needAcceptsCardinality (patterns : List NeedPattern) (count : Nat) : Bool :=
  count >= needMinimumSuppliedSlots patterns &&
    (patterns.any NeedPattern.isCollecting || count == patterns.length)

def needClauseHead : Pattern -> List NeedPattern
  | .sequenceValue ps => ps.map NeedPattern.ofClause
  | pattern => [NeedPattern.ofClause pattern]

/- The invocation-plan IDENTITY layer (CallReference M1.5/S1): which cells are plans and
    META's pure read of one. It stands before the binder core because the production binder's
    META capability (`NeedPlan.reference`) reifies through it; the plan's preparation,
    execution and invocation follow `NeedSupply` below (§ Total invocation-plan control). -/
namespace NeedPlan

/-- META-S3-4: the written invocation FORM of a plan: a call `f(args)`, or an argument-bearing dot
    edge `receiver.name(args)` (an explicitly empty list included), whose route decides what it
    invokes. -/
inductive CallForm where
  | call
  | dot (receiver : Expr) (name : Ident) (fallback : Expr)
  deriving Repr

/-- A written invocation (META-S3-4, CR-2): a written call `f(args)` whose callee is a name, a
    parameter or an argumentless dot path — every call the parser produces — or an argument-bearing
    dot edge `t.N(args)`, whose `callee` is its argumentless edge `t.N` (the route's `effective`
    shape says what is actually called). The decision is syntactic, total and evaluation-free:
    argumentless dot edges (`5.Inc`, `Box.G`), names (`Start`), values and computed callees are no
    invocation (D-2A). -/
structure CallShape where
  callee : Expr
  args : OutputBundle
  caller : EvalCtx
  values : ValEnv
  form : CallForm := .call
  deriving Repr

def callShape? (source : Expr) (caller : EvalCtx) (values : ValEnv) : Option CallShape :=
  match source with
  | .call f args =>
    match f with
    | .resolve _ | .param _ | .dotMember _ _ _ none => some ⟨f, args, caller, values, .call⟩
    | _ => none
  | .dotMember receiver name fallback (some args) =>
    some ⟨.dotMember receiver name fallback none, args, caller, values, .dot receiver name fallback⟩
  | _ => none

/-- The shape a route invokes (D-5): an extension route calls the fallback with the receiver as the
    ordinary first argument (DOT-03, `prepareLexicalDotCallArgs`) — `5.Add(1)` is `Add(5, 1)`;
    every other route keeps the shape (a member's callee is its argumentless path, the `.Algorithm`
    route's the link edge). -/
def effective (shape : CallShape) : PlanRoute → CallShape
  | .extension =>
    match shape.form with
    | .dot receiver _ fallback =>
      { shape with callee := fallback, args := prepareLexicalDotCallArgs receiver (some shape.args) }
    | .call => shape
  | _ => shape

/-- The error context of a plan's written form, exactly the one its ordinary evaluation attaches:
    `evalCallCountedExpr`'s `CtxMsg.call f` for a call, `evalCounted`'s `CtxMsg.dotCall t N` for a
    dot edge. -/
def CallShape.ctxMsg (shape : CallShape) : String :=
  match shape.form with
  | .call => CtxMsg.call shape.callee
  | .dot receiver name _ => CtxMsg.dotCall receiver name

/-- The plan a cell is, if it is one. Ready data, collectors, non-call computations and
    unsupported callees are no plan. -/
def ofSuspension? : NeedSuspension → Option CallShape
  | .expression source caller values => callShape? source caller values
  | _ => none

def shapeAt? (needs : Array NeedCell) (a : Nat) : Option CallShape :=
  match needs[a]? with
  | some cell => ofSuspension? cell.suspension
  | none => none

/-- The stable handle META returns. Its identity IS the plan's need address. -/
structure CallReference where
  plan : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The description of META's capture refusal. C#: `Evaluator.MetaRefusalDescription`. -/
def metaRefusalDescription : String := "meta: not a supplied call computation"

/-- META's refusal of anything that is not a supplied call computation. -/
def metaRefusal : Error := Error.notAnAlgorithm metaRefusalDescription

/-- META-DIAG-1: the binder frame naming the META parameter whose capture refused.
    C#: `Evaluator.MetaParameterContext`. -/
def metaParameterContext (name : Ident) : String := s!"while binding meta parameter '{name}'"

/-- META-DIAG-1: the binder-level capture refusal of the META parameter `name` — the canonical
    `metaRefusal`, unchanged, inside the frame naming the parameter. -/
def metaBindingRefusal (name : Ident) : Error := .withContext (metaParameterContext name) metaRefusal

/-- META-DIAG-1: the binder's report of a failed capture of the META parameter `name`. ONLY the
    canonical capture refusal (`metaRefusal`) is framed with the parameter's name, the refusal
    itself kept as the inner error; every other error — the incomplete outcome, a later
    `invocationRefusal`, any other failure — passes unchanged. A direct `reify`/`reference` has
    no binding site and keeps the unframed refusal. C#: `Evaluator.AnnotateMetaBindingRefusal`. -/
def bindingRefusal (name : Ident) : Error → Error
  | .notAnAlgorithm description =>
      if description = metaRefusalDescription then metaBindingRefusal name
      else .notAnAlgorithm description
  | error => error

/-- META-DIAG-1: the canonical refusal, at a binding site, is exactly the named binder frame over it. -/
@[simp] theorem bindingRefusal_metaRefusal (name : Ident) :
    bindingRefusal name metaRefusal = metaBindingRefusal name := by
  simp [bindingRefusal, metaRefusal]

/-- META-S3-4 (D-1A): the refusal of a route-dependent reference operation (invocation, callable
    projection, argument-supply observation, loop setup) over a captured invocation whose route is a
    non-callable intrinsic (`5.string()`, `R.Invoke()`, `R.Arguments(…)`). Capture itself, reference
    identity and obtaining the argument view stay inert. -/
def invocationRefusal : Error := Error.notAnAlgorithm "meta: not a callable invocation"

def reifyResult (needs : Array NeedCell) (a : Nat) : Except Error CallReference :=
  match shapeAt? needs a with
  | some _ => .ok ⟨a⟩
  | none => .error metaRefusal

/-- META: a pure read. The state is returned unchanged on success and on refusal. -/
def reify (a : Nat) : EvalM CallReference := do
  return ← reifyResult (← get).needs a

/-- THE META CAPABILITY of the production binder (CallReference S1): reify the supplied
    cell at `a` (a pure read, `reify`; a non-plan cell is the structured `metaRefusal`, raised
    with the state unchanged) and allocate ONE fresh Ready cell holding its call reference
    `Result.callRef a`. The original cell — its suspension, VALUE state, CALLABLE memo and plan
    supply — is never read beyond its suspension and never written. The adapter has no
    CALLABLE identity (Ready data). -/
def reference (a : Nat) : EvalM Nat := do
  let r ← reify a
  readyNeed (.callRef r.plan, 1)

end NeedPlan

/-! ### The Model-C binder core (FORMAL-07, October 2026)

The ONE inspecting binder (NEED-04, PAT-10) and the clause-family dispatcher are
TOTAL definitions over the runtime capabilities of a supplied cell — its VALUE demand and its
CALLABLE projection, passed in as `NeedChannels` (with cell allocation, the generic core's
`NeedCapabilities`; see ONE GENERIC CORE below). Their own recursion is
structural over the written patterns (never over runtime values), so they live here,
above the evaluator recursion core, and the kernel checks their termination; the evaluator
recursion core instantiates them at every binding site (`evalNeedUserSupply`,
`evalNeedFamilySupply`, `runNeedStepWith` — twice —, `evalZeroArgumentDemandOutputCounted`) with
the TOTAL channel record `rec.bindingChannels` = `NeedChannels.shell rec.evalSuppliedAt
rec.planRoute rec.demandNeedRecursive rec.projectNeedWrittenAt` over the core's recursive answer
(`bindingChannels` is it at the production answer; S6a, October 2026; R7) — the VALUE shell
`NeedDemand.step` and the CALLABLE shell `NeedProjection.step`, i.e. exactly one unfolding of
`demandNeedRecursive` / `projectNeedCallable`, whose bodies they are. Every theorem stated for ALL channels
(`KatLangArityLaws.lean` § Model-C production binder laws) therefore holds for the
definitions the evaluator calls, and what the shells do on completed and Ready cells is a kernel
fact at that boundary (`KatLangArityLaws/NestedRepeatedNames.lean`, `shell_model_caps`). Since R7
the call sites are bodies of the total core, so that they pass this record is a kernel fact too
(`evalStep rec (.evalNeedUserSupply …)` unfolds to it by definition), and every completed
production run of a site is its body over the production operations
(`KatLangArityLaws/EvaluatorCore.lean`, `production_unfolds`). The total
public `demandNeed` is the same `NeedDemand.step` unfolding (`bindingChannels.value = demandNeed`
by definition); its specialization is kernel-checked in `KatLangArityLaws/NeedControl.lean`.
Until October 2026 these binder functions were `partial` members of the evaluator block
because they participated in recursive VALUE demand, so no theorem could say anything about
their behaviour (a `partial def` is an opaque constant). Until R3′ (October 2026) they also
called three helper families that reached `partial` definitions — literal matching
`matchPattern` (via `matchPatternInto`/`matchStructureInto`), the kind-mismatch payload
`structuralPatternKindMismatch` (via `ParameterPattern.displayName` and
`resultDiagnosticString`) and the duplicate-clause check `Algorithm.hasDuplicateBranchPatterns`
(via `Pattern.matchEquivalentWithRenaming`). All of them, with the adjacent
`ParameterPattern.captures` and `Pattern.parameterPattern?`, are now structural recursion over
finite pattern/value syntax, so those outcomes are kernel terms
(`KatLangArityLaws/PatternHelpers.lean`: literal success iff the same constructor and payload,
the payload as an explicit string, and duplicate clauses characterized as structural equality
up to an injective binder renaming). Repeated callable
identity `sameRepeatedCallableIdentity` is no longer opaque either (S5, October 2026): its helpers
`sameDeclaringScope` / `compatibleActivations` are total, so its outcome is a kernel term; only
the anonymous-declaration fallback of `sameDeclaringScope` compares two `reprStr` strings of
`ScopeCtx.declaration`, opaque values whose string equality is still lawful
(`KatLangArityLaws/RepeatedNameLaws.lean` proves the identity laws it needs;
`KatLangArityLaws/CallableIdentityDomain.lean` proves transitivity whenever no compared level
decides an identified/anonymous pair through that fallback).

ONE GENERIC CORE (R3, October 2026). The binder and the dispatcher's search are written ONCE,
in the `NeedBinder` namespace, over any monad with `Error` exceptions and the three
capabilities of `NeedCapabilities`: VALUE demand, CALLABLE projection and cell ALLOCATION
(the binder allocates `.collector` and `.ready` suspensions only). The production names —
`needSourceAddress`, `needCardinalityGate`, `bindNeedName`, `bindNeedOne`, `bindNeedSources`,
`bindNeedLevel`, `bindNeedPatterns`, `selectNeedFamilyBranch` — are, BY DEFINITION, that core
at `EvalM` with `NeedChannels.capabilities` (the two channels plus `allocateNeed`); a selected
clause is activated by the one monomorphic `needActivateBranch`. There is no second
production binder, and the generic form changes no operation and no effect order: the
effects are the same operations in the same order (the compiled code calls the generic
definitions; paired R3 measurements found no difference beyond run-to-run noise). It exists so
that proofs can run THE SAME binder in another interpretation — the external boundary trace of
`KatLangArityLaws.BinderTrace`, which observes every VALUE and CALLABLE invocation and every
successful allocation without adding anything to `EvalState`.

ALLOCATION is a separate pure function, `needLevelSources`, generic in what a supplied
cell is: it gives each top-level pattern of one level its ONE supplied cell, or, for the
collecting binding, the exact ordered slice allocated to it (VAR-02); `.missing` marks a
position no supplied cell reaches, which the cardinality gate excludes on every validated
signature (at most one collector per level, X-02 / `validateAlgorithmTree`). C# keeps the
same arithmetic in `Evaluator.NeedSourceRange`, behind a gate that reads the signature rule
`minimumSuppliedSlots` (C# `PatternLevelArity`); on every validated level that gate decides
exactly as `needAcceptsCardinality` (`binder_minimum_is_the_signature_minimum`). -/

/-- The capabilities of the generic binder core in a monad `m`: a supplied cell's VALUE
    demand, its CALLABLE projection, and the allocation of a fresh cell. The core allocates
    only `.collector` (a collecting binding's slice) and `.ready` (an opened structural
    item) suspensions. Production: `NeedChannels.capabilities`. -/
structure NeedCapabilities (m : Type → Type) where
  value : Nat → m CountedResult
  callable : Nat → m (Option Algorithm)
  allocate : NeedSuspension → m Nat
  /-- META reification (CallReference S1): validate that the cell is a supplied call and
      allocate the Ready adapter cell holding its reference. Only a `.metaRef` pattern invokes
      it. Production: `NeedPlan.reference`. -/
  reference : Nat → m Nat

/-- The two capabilities the binder may use on a supplied cell: its VALUE demand
    and its CALLABLE projection (which never forces this cell's VALUE, NEED-06). The evaluator passes
    `NeedChannels.shell` over `demandNeedRecursive` / `projectNeedWrittenAt` (`bindingChannels`);
    public guards may pass `demandNeed` and `projectNeedCallable`. Plain binding uses neither
    (NEED-01, NEED-03). -/
structure NeedChannels where
  value : Nat -> EvalM CountedResult
  callable : Nat -> EvalM (Option Algorithm)

/-- The production capabilities of the binder core: the evaluator's two channels and the
    one allocator `allocateNeed`. -/
def NeedChannels.capabilities (channels : NeedChannels) : NeedCapabilities EvalM :=
  ⟨channels.value, channels.callable, allocateNeed, NeedPlan.reference⟩

/-- What one top-level pattern of a level is bound from: one supplied cell, the exact slice
    a collecting binding collects, or nothing (an unreachable position, `badArity`). -/
inductive NeedSource (α : Type) where
  | cell (value : α)
  | collector (slice : List α)
  | missing
  deriving Repr, BEq

/-- The supplied cells a source covers, in order. -/
def NeedSource.items {α : Type} : NeedSource α -> List α
  | .cell value => [value]
  | .collector slice => slice
  | .missing => []

/-- The source of the pattern at `index`, around the level's FIRST collector `collector?`;
    `extra` is the number of supplied cells the collector collects. -/
def needSourceAt {α : Type} (collector? : Option Nat) (extra : Nat) (cells : List α)
    (index : Nat) : NeedSource α :=
  if collector? == some index then .collector ((cells.drop index).take extra)
  else
    match cells[if (collector?.map (fun i => decide (index > i))).getD false then index + extra - 1 else index]? with
    | some cell => .cell cell
    | none => .missing

/-- ALLOCATION of one level's supply to its top-level patterns, position by position: the
    patterns before the collector take the leading cells, the patterns after it the
    trailing cells, and the collector the exact slice between them (VAR-02); without a
    collector pattern `i` takes cell `i`. Pure and generic in the cell type, so the same
    function serves need addresses in the evaluator and values in the laws. -/
def needLevelSources {α : Type} (patterns : List NeedPattern) (cells : List α) : List (NeedSource α) :=
  let collector? := patterns.findIdx? NeedPattern.isCollecting
  let extra := cells.length + 1 - patterns.length
  (List.range patterns.length).map (needSourceAt collector? extra cells)

/-- The names a head binds more than once, at any depth: every occurrence of one of them
    is an inspecting occurrence (NEED-04). -/
def needRepeatedNames (patterns : List NeedPattern) : List Ident :=
  let names := patterns.flatMap NeedPattern.names
  names.eraseDups.filter (fun name => (names.filter (· == name)).length > 1)

/-- NEED-04 (group-aware, ALIAS-UNIFY-1, October 2026): the binder-local AGREEMENT STATE of one
    repeated name during ONE binding — never a parameter, a `Result`, an `EvalState` field or a
    second cell. `identity` is the normalized structural identity of the group's FIRST
    callable-bearing contribution, `anchor` the counted VALUE of its FIRST value-only contribution,
    and `pending` the earlier callable-bearing contributions whose own counted VALUE no anchor has
    checked yet, in occurrence order (empty once an anchor exists). C#: `Evaluator.RepeatedGroup`. -/
structure RepeatedGroup where
  identity : Option Algorithm := none
  anchor : Option CountedResult := none
  pending : List Nat := []
  deriving Repr

/-- Whether a callable-bearing contribution conflicts with the group's first identity. -/
def RepeatedGroup.conflictsWith (group : RepeatedGroup) (identity : Algorithm) : Bool :=
  match group.identity with
  | some earlier => !sameRepeatedCallableIdentity earlier identity
  | none => false

/-- What the binder threads through one head: the bound REPRESENTATIVES (original addresses — the
    production `NeedEnv` a binding returns) and the agreement state of the head's repeated names.
    The groups are discarded when the head is bound (`NeedBinder.bindPatterns`). -/
structure NeedBindState where
  bound : NeedEnv := []
  groups : Assoc Ident RepeatedGroup := []
  deriving Repr

/-- The re-binding of one name in a binding environment (the representative replaced). -/
def NeedEnv.rebind (bound : NeedEnv) (name : Ident) (address : Nat) : NeedEnv :=
  bound.filter (fun entry => entry.fst != name) ++ [(name, address)]

/-- The agreement state of `name` so far (empty before its first occurrence). -/
def NeedBindState.groupOf (state : NeedBindState) (name : Ident) : RepeatedGroup :=
  (lookupAssoc name state.groups).getD {}

/-- The state with `name`'s group replaced. -/
def NeedBindState.setGroup (state : NeedBindState) (name : Ident) (group : RepeatedGroup) : NeedBindState :=
  { state with groups := state.groups.filter (fun entry => entry.fst != name) ++ [(name, group)] }

/-- A non-repeated name: its one cell is its binding. -/
def NeedBindState.withPlain (state : NeedBindState) (name : Ident) (address : Nat) : NeedBindState :=
  { state with bound := state.bound.rebind name address }

/-- An agreed callable-bearing contribution at `address` with identity `identity`: the group's
    first callable contribution becomes the representative (it outranks a value-only one) and
    records the identity; without an anchor the cell waits as a pending VALUE obligation. -/
def NeedBindState.withCallable (state : NeedBindState) (name : Ident) (address : Nat)
    (identity : Algorithm) : NeedBindState :=
  let group := state.groupOf name
  let bound := if group.identity.isSome then state.bound else state.bound.rebind name address
  let pending := if group.anchor.isSome then group.pending else group.pending ++ [address]
  { state with bound := bound }.setGroup name
    { group with identity := group.identity <|> some identity, pending := pending }

/-- The group's FIRST value-only contribution at `address`, of counted VALUE `anchor`, after every
    pending callable contribution agreed with it: it anchors the group, the pending obligations are
    released, and it is the representative unless an earlier callable contribution is. -/
def NeedBindState.withAnchor (state : NeedBindState) (name : Ident) (address : Nat)
    (anchor : CountedResult) : NeedBindState :=
  let group := state.groupOf name
  let bound := if group.identity.isSome then state.bound else state.bound.rebind name address
  { state with bound := bound }.setGroup name { group with anchor := some anchor, pending := [] }

/-! The generic Model-C binder core (R3). Every definition here is the ONE implementation of
    its production namesake below (`chooseBranch`, the clause search, has none: it is reached
    through `selectFamily`), which instantiates it at `EvalM` with
    `NeedChannels.capabilities`; see § The Model-C binder core. -/
namespace NeedBinder

variable {m : Type → Type} [Monad m] [MonadExceptOf Error m]

/-- META-DIAG-1: the META capture of the parameter `name`, its refusal reported through
    `NeedPlan.bindingRefusal` (the canonical refusal framed with the name; any other error
    re-raised unchanged). Success is the capture's own outcome. -/
def captureMeta (name : Ident) (capture : m Nat) : m Nat :=
  tryCatchThe Error capture (fun error => throwThe Error (NeedPlan.bindingRefusal name error))

/-- The address one pattern binds: a supplied cell is TRANSPORTED (no new cell, nothing
    evaluated), a collecting binding gets ONE fresh suspended collector cell over its slice.
    Production: `needSourceAddress`. -/
def sourceAddress (allocate : NeedSuspension → m Nat) (source : NeedSource Nat) : m Nat :=
  match source with
  | .cell address => pure address
  | .collector slice => allocate (.collector slice)
  | .missing => throw Error.badArity

/-- THE CARDINALITY GATE of one pattern level (NEED-05, CALL-04, PAT-10(1)): an unaccepted
    supply count is rejected — a family's non-match, otherwise the arity error whose payload
    is the level's minimum and the COMPLETE supply count — before `accepted` runs.
    Production: `needCardinalityGate`. -/
def cardinalityGate {β : Type} (patterns : List NeedPattern) (count : Nat) (family : Bool)
    (accepted : m (Option β)) : m (Option β) :=
  if !needAcceptsCardinality patterns count then
    if family then pure none
    else throw (Error.arityMismatch (needMinimumSuppliedSlots patterns) count)
  else accepted

/-- A repeated-name incompatibility (NEED-04): a clause attempt's non-match, otherwise the
    agreement's own error. -/
def repeatedMismatch (family : Bool) (error : Error) : m (Option NeedBindState) :=
  if family then pure none else throw error

/-- NEED-04's DATA-ANCHOR CHECK: the own counted VALUE of each cell of `cells`, demanded in
    order, against the group's anchor `anchor` (value AND emitted count). `true` when every one
    agrees; the first disagreement is the agreement's `badArity` under the repeated-parameter
    context (a family attempt's `false`, its non-match); the first demand failure propagates and
    nothing after it is demanded. -/
def checkAnchor (capabilities : NeedCapabilities m) (name : Ident) (anchor : CountedResult)
    (family : Bool) : List Nat → m Bool
  | [] => pure true
  | cell :: rest => do
      let own <- capabilities.value cell
      if own == anchor then checkAnchor capabilities name anchor family rest
      else if family then pure false
      else throw (Error.withContext (repeatedParameterContext name) Error.badArity)

/-- One occurrence of a binder name (NEED-04, group-aware: ALIAS-UNIFY-1, October 2026). A
    non-repeated name transports its cell and invokes nothing. At EVERY occurrence of a REPEATED
    name, the first included, the binder projects that cell's CALLABLE first (a projection
    failure propagates — it is never absence):
    * a CALLABLE-BEARING contribution is compared by its normalized structural identity with the
      group's first one (a conflict is the `typeMismatch` before any VALUE demand); while the group
      has no value-only contribution its own VALUE is NOT demanded — it waits as a pending
      obligation — and once the group has a data anchor its own counted VALUE is demanded and
      compared with the anchor at once;
    * a VALUE-ONLY contribution demands its own counted VALUE: the first one is the group's ANCHOR
      and then checks every pending callable contribution's own counted VALUE in occurrence order
      (`checkAnchor`), a later one is compared with the anchor.
    The binding is the FIRST callable-bearing original cell when there is one, otherwise the first
    value-only one — an original supplied or allocated cell, never a synthesized pairing.
    Successful incompatibility is a family's non-match; every failure propagates. Production:
    `bindNeedName`. C#: `Evaluator.BindAcceptedNeedPatterns`. -/
def bindName (capabilities : NeedCapabilities m) (name : Ident) (address : Nat)
    (repeated : List Ident) (state : NeedBindState) (family : Bool) : m (Option NeedBindState) :=
  if repeated.contains name then do
    let group := state.groupOf name
    match <- capabilities.callable address with
    | some identity =>
        if group.conflictsWith identity then
          repeatedMismatch family (Error.typeMismatch "Repeated bind equality requires the same callable identity")
        else do
          let agreed <- match group.anchor with
            | some anchor => checkAnchor capabilities name anchor family [address]
            | none => pure true
          if agreed then pure (some (state.withCallable name address identity)) else pure none
    | none => do
        let own <- capabilities.value address
        match group.anchor with
        | some anchor =>
            if own == anchor then pure (some state)
            else repeatedMismatch family (Error.withContext (repeatedParameterContext name) Error.badArity)
        | none => do
            let agreed <- checkAnchor capabilities name own family group.pending
            if agreed then pure (some (state.withAnchor name address own)) else pure none
  else pure (some (state.withPlain name address))

mutual
  /-- One pattern against one supplied cell: a name is `bindName`; a literal, a
      structural pattern and the unpacking receiver demand the cell's VALUE first, then a
      structural pattern opens ONLY its own kind, allocates one fresh ready cell per opened
      item, in order, and binds them as a nested level through the same gate and allocation
      — written out here because `bindLevel` is defined after this block, and identified
      with it at the production instance by the theorems `nested_*_level_is_bind_need_level`
      (`KatLangArityLaws.lean`); change both together. Production: `bindNeedOne`. -/
  def bindOne (capabilities : NeedCapabilities m) (pattern : NeedPattern) (address : Nat)
      (repeated : List Ident) (bound : NeedBindState) (family : Bool) : m (Option NeedBindState) := do
    match pattern with
    | .bind name _ => bindName capabilities name address repeated bound family
    -- A META capture (CallReference S1) is reached in WRITTEN order like every pattern
    -- (NEED-04): it reifies the supplied cell into a fresh Ready adapter — demanding
    -- nothing, a non-plan cell refusing — and binds the name to that adapter. A refusal names
    -- the parameter (META-DIAG-1, `NeedPlan.bindingRefusal`); any other error passes unchanged.
    | .metaRef name => do
        let adapter <- captureMeta name (capabilities.reference address)
        bindName capabilities name adapter repeated bound family
    | .literal literal => do
        let (value, _) <- capabilities.value address
        pure (if (matchPattern literal value).isSome then some bound else none)
    | .sequence ps | .list ps | .unpack ps => do
        let (value, _) <- capabilities.value address
        let items? := match pattern with
          | .list _ => Result.listPatternItems? value
          | .sequence _ => Result.sequencePatternItems? value
          | _ => some (Result.spreadItems value)
        match items? with
        | none => if family then pure none else throw (structuralPatternKindMismatch pattern.toParameter value)
        | some items => do
            let cells <- items.mapM (fun item => capabilities.allocate (.ready (item, Result.valueCount item)))
            cardinalityGate ps cells.length family
              (bindSources capabilities ps (needLevelSources ps cells) repeated bound family)

  /-- The patterns of one level, left to right, each from its allocated source; the first
      failure or non-match ends binding. Production: `bindNeedSources`. -/
  def bindSources (capabilities : NeedCapabilities m) (patterns : List NeedPattern)
      (sources : List (NeedSource Nat)) (repeated : List Ident) (current : NeedBindState)
      (family : Bool) : m (Option NeedBindState) :=
    match patterns with
    | [] => pure (some current)
    | pattern :: rest => do
        let address <- sourceAddress capabilities.allocate (sources.headD .missing)
        match <- bindOne capabilities pattern address repeated current family with
        | none => pure none
        | some next => bindSources capabilities rest sources.tail repeated next family
end

/-- One pattern level over its supplied cells: the cardinality gate, then the patterns
    left to right over their allocated sources. Production: `bindNeedLevel`. -/
def bindLevel (capabilities : NeedCapabilities m) (patterns : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedBindState) (family : Bool) : m (Option NeedBindState) :=
  cardinalityGate patterns cells.length family
    (bindSources capabilities patterns (needLevelSources patterns cells) repeated bound family)

/-- THE ONE INSPECTING BINDER of Model C (NEED-04, PAT-10) over a whole head: the head's level
    from the empty binding state; the representatives it bound are the binding, and the repeated
    names' agreement state is discarded with the binder activation. Production: `bindNeedPatterns`. -/
def bindPatterns (capabilities : NeedCapabilities m) (patterns : List NeedPattern) (cells : List Nat)
    (family : Bool := false) : m (Option NeedEnv) := do
  let state <- bindLevel capabilities patterns cells (needRepeatedNames patterns) {} family
  pure (state.map NeedBindState.bound)

/-- The clause search of a family dispatch: the clauses in WRITTEN order, each attempt
    inspecting the SAME supplied cells through the one binder in family mode; a non-match
    tries the next clause from the state the attempt left (nothing is rolled back), a raised
    failure aborts the search, the first match is handed to `activate`, and exhaustion is
    `noMatchingBranch`. -/
def chooseBranch {β : Type} (capabilities : NeedCapabilities m) (cells : List Nat)
    (calleeName : String) (activate : CondBranch → NeedEnv → m β) : List CondBranch → m β
  | [] => throw (Error.noMatchingBranch calleeName)
  | branch :: rest => do
      match <- bindPatterns capabilities (needClauseHead branch.pattern) cells true with
      | none => chooseBranch capabilities cells calleeName activate rest
      | some bindings => activate branch bindings

/-- The clause-family dispatcher over an already formed cell supply: the duplicate-pattern
    check, the family's cardinality, then the clause search (`chooseBranch`), whose match is
    activated by `activate`. Production: `selectNeedFamilyBranch`. -/
def selectFamily {β : Type} (capabilities : NeedCapabilities m) (callee : Algorithm)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → m β) : m β := do
  if callee.hasDuplicateBranchPatterns then throw Error.duplicateBranchPattern
  let branches := Algorithm.branches callee
  if !branches.any (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) then
    throw (Error.arityMismatch ((branches.head?.map (fun branch => needMinimumSuppliedSlots (needClauseHead branch.pattern))).getD 0) cells.length)
  chooseBranch capabilities cells calleeName activate branches

end NeedBinder

/-- The address one pattern binds (`NeedBinder.sourceAddress` with `allocateNeed`): a
    supplied cell is TRANSPORTED (no new cell, nothing evaluated), a collecting binding gets
    ONE fresh suspended collector cell over its slice. -/
def needSourceAddress (source : NeedSource Nat) : EvalM Nat :=
  NeedBinder.sourceAddress allocateNeed source

/-- THE CARDINALITY GATE of one pattern level (`NeedBinder.cardinalityGate` at `EvalM`;
    NEED-05, CALL-04, PAT-10(1)). -/
def needCardinalityGate {β : Type} (patterns : List NeedPattern) (count : Nat) (family : Bool)
    (accepted : EvalM (Option β)) : EvalM (Option β) :=
  NeedBinder.cardinalityGate patterns count family accepted

/-- One occurrence of a binder name (`NeedBinder.bindName` at the production capabilities;
    NEED-04 group-aware, Q-28). C#: `Evaluator.BindAcceptedNeedPatterns`. -/
def bindNeedName (channels : NeedChannels) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedBindState) (family : Bool) : EvalM (Option NeedBindState) :=
  NeedBinder.bindName channels.capabilities name address repeated bound family

/-- One pattern against one supplied cell (`NeedBinder.bindOne` at the production
    capabilities). -/
def bindNeedOne (channels : NeedChannels) (pattern : NeedPattern) (address : Nat)
    (repeated : List Ident) (bound : NeedBindState) (family : Bool) : EvalM (Option NeedBindState) :=
  NeedBinder.bindOne channels.capabilities pattern address repeated bound family

/-- The patterns of one level, left to right (`NeedBinder.bindSources` at the production
    capabilities). -/
def bindNeedSources (channels : NeedChannels) (patterns : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (current : NeedBindState)
    (family : Bool) : EvalM (Option NeedBindState) :=
  NeedBinder.bindSources channels.capabilities patterns sources repeated current family

/-- One pattern level over its supplied cells (`NeedBinder.bindLevel` at the production
    capabilities). -/
def bindNeedLevel (channels : NeedChannels) (patterns : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedBindState) (family : Bool) : EvalM (Option NeedBindState) :=
  NeedBinder.bindLevel channels.capabilities patterns cells repeated bound family

/-- THE ONE INSPECTING BINDER of Model C (NEED-04, PAT-10): ordinary calls (`family =
    false`), clause attempts (`family = true`: an incompatibility is a non-match, a runtime
    failure is not), callbacks and loop steps alike — `NeedBinder.bindPatterns` at the
    production capabilities. C#: `Evaluator.BindNeedPatterns`. -/
def bindNeedPatterns (channels : NeedChannels) (patterns : List NeedPattern) (cells : List Nat)
    (family : Bool := false) : EvalM (Option NeedEnv) :=
  NeedBinder.bindPatterns channels.capabilities patterns cells family

/-- The callee-side context of a completed need binding. -/
def needBindingContext (ctx : EvalCtx) (bindings : NeedEnv) : EvalM EvalCtx := do
  let names := bindings.map Prod.fst
  let next <- ctx.bindParameters names
  pure { next with needEnv := bindings ++ next.needEnv }

/-- The ACTIVATION of a selected clause, after its successful binding: a fresh binding
    context under the family (`needBindingContext`, which shadows the inherited cells of
    the bound names), the inherited values shadowed for those names, and the selected body
    wired under the family with its binders' lexical activation (`wireSelectedBranchBody`).
    It returns the activated body, its context and its values WITHOUT evaluating it. -/
def needActivateBranch (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) : EvalM (Algorithm × EvalCtx × ValEnv) := do
  let names := bindings.map Prod.fst
  let next <- needBindingContext (ctx.push callee) bindings
  let values := ValEnv.shadow env names
  let body <- wireSelectedBranchBody callee branch.body names next values
  pure (body, next, values)

/-- The ordinary clause-family dispatcher over an already formed cell supply: the
    duplicate-pattern check, the family's cardinality, then the clauses in WRITTEN
    order, each attempt inspecting the SAME cells through the one binder in family
    mode (a successful mismatch tries the next clause; a runtime failure during
    inspection aborts dispatch; no clause is `noMatchingBranch`), and finally the
    selected branch's activation (`needActivateBranch`) — `NeedBinder.selectFamily` at the
    production capabilities. It returns the activated body, its context and
    its values WITHOUT evaluating it, so each receiver reads the body its own way:
    the ordinary call as one value (`evalNeedFamilySupply`), a loop step as its
    row supply (`runNeedStepSlots`, LOOP-08). C#: `BindNeedFamilySupply`. -/
def selectNeedFamilyBranch (channels : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM (Algorithm × EvalCtx × ValEnv) :=
  NeedBinder.selectFamily channels.capabilities callee cells calleeName
    (needActivateBranch callee ctx env)

/-- What ONE computed explicit spread slot contributes to a supply (CallReference S2): the
    spread's opened ITEMS — each becomes one fresh Ready cell — or ORIGINAL CELLS transported
    with their written sources: an argument view's plan supply (`SpreadOpening.view`), never
    copied, re-evaluated or wrapped. -/
inductive SpreadSupply where
  | items (values : List Result)
  | cells (cells : List (Nat × Option Expr))
  deriving Repr

/- Total Model-C supply formation (R5/A2). Only evaluation of a computed spread
    re-enters the evaluator core (its `SpreadEval` callback). Ordinary acquisition and known-slice
    reopening have no VALUE-demand callback. -/
namespace NeedSupply
abbrev Sourced := Nat × Option Expr

/-- The evaluator's capability for one COMPUTED spread slot (a spread that is not a collecting
    parameter's known slice): its supply contribution (`SpreadSupply`). Production:
    `evalSupplySpread` — the spread expression's top-level items, or an argument view's
    transported plan cells (CallReference S2). -/
abbrev SpreadEval := Expr → EvalCtx → ValEnv → EvalM SpreadSupply

def slot (spread : SpreadEval)
    (ctx : EvalCtx) (env : ValEnv) (e : Expr) : EvalM (List Sourced) :=
  match e with
  | .sequenceSpread operand => do
    match ← spreadCollectorSlice? operand ctx with
    | some slice => slice.mapM (fun a => do pure (a, ← needWrittenSource? a))
    | none => do
      match ← spread e ctx env with
      | .items values =>
        values.mapM (fun v => do pure (← readyNeed (v, Result.valueCount v), none))
      | .cells cells => pure cells
  | _ => do pure [(← supplyNeed e ctx env, some e)]

def form (spread : SpreadEval)
    (ctx : EvalCtx) (env : ValEnv) : OutputBundle → EvalM (List Sourced)
  | [] => pure []
  | e :: rest => do
    let head ← slot spread ctx env e
    let tail ← form spread ctx env rest
    pure (head ++ tail)

/-- The address-only route projects THE sourced formation, in order. -/
def addresses (spread : SpreadEval)
    (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) : EvalM (List Nat) := do
  pure ((← form spread ctx env args).map Prod.fst)
end NeedSupply

/- Total invocation-plan control (CallReference M1.5, October 2026). ONE supplied call
    computation — a cell whose suspension is a written call `F(args)` with a lexical-name or
    parameter callee — is ONE invocation plan, identified by its need address and nothing else
    (no AST key: two dynamic occurrences of one written call are two cells, two plans).
    * VALUE: `NeedDemand.step`, the one completion shell, runs `execute` for such a cell
      (`NeedDemand.suspendedValue`), so EVERY production VALUE demand of the cell — the public
      `demandNeed`, and the recursive `demandNeedRecursive` behind parameter reads, binder
      inspection, collectors, selection and builtin roles, at any nesting depth — executes the
      plan. The original VALUE stays at-most-once in `NeedState`.
    * META: `reify` is a pure read of the cell's suspension. It runs no target, demands no
      argument, forms no supply and opens no spread; a completed cell keeps its suspension,
      so META after VALUE (success or ordinary failure) reifies the same plan.
    * Invocation: `invoke` is `execute` without the completion shell — a fresh target
      execution over the plan's one prepared supply that never reads or writes the cell's VALUE.
    * Forwarding: a parameter supplied onward transports the cell itself (`supplyNeed`), so the
      plan, its callee and its caller context travel unchanged; no forwarding scope re-resolves.
    `execute` has the phase order of the ordinary call (`evalCallCountedExpr` →
    `evalResolvedCallCounted`): the callee in the CALLER's context under the call frame, then,
    under the frame, alias normalization, the supply, and the ONE dispatch
    (`evalSuppliedCallCounted`) — the plan only replaces the per-execution `NeedSupply.form` by
    the plan's single memoized `prepare` over the same former. The target is resolved per
    execution (D2, provisional). Since S1 (October 2026) source reaches them: a `meta` parameter
    binds through `reference` (`reify` + one Ready adapter), and the `Invoke` dot intrinsic runs
    `invoke` (`invokeCallReferenceValue`). -/
namespace NeedPlan

/-- The target and dispatch phases a plan execution installs. Production: `productionPlanRoute`
    (`resolveCalleeAlg`, `normalizeCallee`, `evalSuppliedCallCounted`). -/
structure Route where
  target : Expr → EvalCtx → EvalM Algorithm
  normalize : Algorithm → EvalCtx → EvalM Algorithm
  /-- The ONE dispatch over the callee's ORIGIN (CACHE-PUB-1: the provenance a zero-supply invocation
      publishes under, `CalleeOrigin`), the normalized callee and the formed supply. -/
  dispatch : CalleeOrigin → Algorithm → List NeedSupply.Sourced → EvalCtx → ValEnv → String → EvalM CountedResult
  /-- The spread capability the plan's supply formation runs (production `evalSupplySpread`). -/
  spread : NeedSupply.SpreadEval
  /-- META-S3-4: the route classifier (production `classifyPlanRouteWith` over
      `resolveDotReceiver?` and `algorithmIntrinsicRoute`: identity resolution only; a runtime
      projection receiver is demanded through its own single-flight cell). -/
  classify : CallShape → EvalM PlanRoute
  /-- META-S3-4: a cell's CALLABLE (production `projectNeedCallable`), used for the `.Algorithm`
      route's callee cell — the link, whose receiver is demanded once per plan (D-3). -/
  project : Nat → EvalM (Option Algorithm)

def setSupply (a : Nat) (supply : NeedPlanSupply) : EvalM Unit :=
  modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with plan := supply }) }

def setRoute (a : Nat) (r : PlanRoute) : EvalM Unit :=
  modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with route := some r }) }

/-- META-S3-4: plan `a`'s route, classified once by the first route-dependent operation and
    recorded in the plan cell (`NeedCell.route`); every later operation reads the record, and the
    record is never rewritten: a classification that finds the route recorded meanwhile (a nested
    observation of the same plan) returns that record — the first writer wins, as C#'s CAS does. A
    classification failure records nothing and propagates (it is the plan's failure, never
    absence; C# retains it). -/
def routeOf (classify : CallShape → EvalM PlanRoute) (a : Nat) (shape : CallShape) : EvalM PlanRoute := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.route with
  | some r => pure r
  | none =>
    let r ← classify shape
    match ((← get).needs[a]?).bind NeedCell.route with
    | some recorded => pure recorded
    | none =>
      setRoute a r
      pure r

/-- The plan's ONE supply preparation through `NeedSupply.form`, memoized in the cell. -/
def prepare (spread : NeedSupply.SpreadEval)
    (a : Nat) (shape : CallShape) : EvalM (List NeedSupply.Sourced) := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.plan with
  | .prepared outcome => return ← outcome
  | .preparing => throw Error.demandCycle
  | .unprepared =>
    setSupply a .preparing
    let outcome ← evalAttempt (NeedSupply.form spread shape.caller shape.values shape.args)
    setSupply a (.prepared outcome)
    return ← outcome

/-- Records plan `a`'s canonical callee cell (CR-13). -/
def setCallee (a c : Nat) : EvalM Unit :=
  modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with callee := some c }) }

/-- THE CANONICAL CALLEE CELL of plan `a` (META-S3-1, CR-13; META-S3-4: the callee of its ROUTE —
    the written callee, the argumentless member path, the link `t.Algorithm`, or an extension's
    fallback): supplied in the plan's captured caller context through the ONE supplier
    (`supplyNeed`) — so a parameter callee is that parameter's existing cell (NEED-01) — and
    recorded in the plan cell (`NeedCell.callee`); every later observation reads the record. Once
    the route is recorded, establishing it evaluates, prepares and demands nothing; establishing
    the ROUTE may demand a runtime-projection receiver (D-4). An intrinsic route is
    `invocationRefusal`, a non-plan address META's refusal. C#: `InvocationPlan.CalleeCell`. -/
def calleeCell (classify : CallShape → EvalM PlanRoute) (a : Nat) : EvalM Nat := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.callee with
  | some c => pure c
  | none =>
    match ofSuspension? cell.suspension with
    | none => throw metaRefusal
    | some shape =>
      let r ← routeOf classify a shape
      if r == .intrinsic then throw invocationRefusal
      let eff := effective shape r
      let c ← supplyNeed eff.callee eff.caller eff.values
      setCallee a c
      pure c

/-- The callee plan `a` invokes along route `r` over its effective shape `eff`: the ordinary callee
    law of the written callee (a call, a member path, an extension fallback), or — for the
    `.Algorithm` route — the CALLABLE of the plan's canonical callee cell, the link (CR-14 c), so the
    link's receiver is demanded once per plan (D-3). -/
def calleeAlong (route : Route) (a : Nat) (eff : CallShape) : PlanRoute → EvalM Algorithm
  | .algorithm => do
    match ← route.project (← calleeCell route.classify a) with
    | some algorithm => pure algorithm
    | none => throw (Error.notAnAlgorithm capturedCalleeDescription)
  | .intrinsic => throw invocationRefusal
  | _ => route.target eff.callee eff.caller

/-- The written name of plan `a`'s callee in heap `needs`, total (`calleeName`'s law): its route's
    effective callee once the route is recorded (an extension names its fallback), otherwise the
    written callee; `none` for a non-plan address. -/
def calleeNameIn? (needs : Array NeedCell) (a : Nat) : Option String :=
  match shapeAt? needs a with
  | some shape =>
    match needs[a]? with
    | some { route := some r, .. } => some (openExprName (effective shape r).callee)
    | _ => some (openExprName shape.callee)
  | none => none

/-- The plan a supplied `X.Algorithm` LINK at `link` decoded, read from heap `needs` alone: the
    link's recorded receiver cell (`NeedLink.receiverCell`) completed with a call reference. It
    demands, projects and records nothing; once the link's CALLABLE has been obtained
    (`NeedLink.callable`) it is exactly the plan that CALLABLE was decoded from, because a completed
    VALUE and a recorded receiver are never rewritten. -/
def linkedPlanIn? (needs : Array NeedCell) (link : Nat) : Option Nat :=
  match needs[link]? with
  | some { receiver := some r, .. } =>
    match needs[r]? with
    | some { state := .completed (.ok (.callRef p, _)), .. } => some p
    | _ => none
  | _ => none

/-- CACHE-PUB-1: follow only the ALREADY RECORDED callee edges of supplied `.Algorithm` links.
    CALLABLE resolution has completed before publication eligibility is read, so every traversed
    receiver and callee is already retained. This heap read demands, projects and allocates nothing;
    nested links preserve the ultimate binding. The heap size bounds even a malformed cyclic heap.
    C#: `CellCalleeBinding` follows `LinkSuspension.ProjectedCallee`. -/
def originCalleeIn (needs : Array NeedCell) (address : Nat) : Nat :=
  go needs.size address
where
  go : Nat → Nat → Nat
    | 0, a => a
    | fuel + 1, a =>
        match (linkedPlanIn? needs a).bind (fun p => (needs[p]?).bind NeedCell.callee) with
        | some callee => go fuel callee
        | none => a

/-- META-S3-4-DIAG (October 20 2026): the callee name plan `a`'s execution along route `r` passes
    to its dispatch, read from heap `needs` alone (total; no demand, projection or preparation).
    Every route names its effective written callee (`openExprName eff.callee`) — the call's callee,
    the argumentless member path, an extension's fallback — except the `.Algorithm` route: its
    callee is the CAPTURED plan's callee, so it is named exactly as the ordinary intrinsic names a
    fresh call of it (`algorithmOfValue` / `algorithmCalleeOf`: `calleeName` of the decoded plan),
    and `R.Algorithm(1)` with `R = Capture(F(0))` reports `noMatchingBranch "F"`, never
    `"R.Algorithm"`. The decoded plan is the one the link's CALLABLE came from (`linkedPlanIn?`);
    were it unreadable, the written link names the dispatch. C#: `ProjectPlannedAlgorithmCallee`'s
    `PlanCalleeName(captured)`. -/
def dispatchNameIn (needs : Array NeedCell) (a : Nat) (eff : CallShape) : PlanRoute → String
  | .algorithm =>
    match ((needs[a]?).bind NeedCell.callee).bind (linkedPlanIn? needs) |>.bind (calleeNameIn? needs) with
    | some name => name
    | none => openExprName eff.callee
  | _ => openExprName eff.callee

/-- `dispatchNameIn` over the current heap: a pure state read. -/
def dispatchName (a : Nat) (eff : CallShape) (r : PlanRoute) : EvalM String := do
  pure (dispatchNameIn (← get).needs a eff r)

/-- CACHE-PUB-1: the ORIGIN of the callee plan `a`'s execution along route `r` invokes, read from heap
    `needs` alone (total; no demand, projection or preparation) — the provenance its dispatch names a
    zero-supply invocation's property binding by. Every route's callee is its effective WRITTEN
    callee in the plan's caller context, except the `.Algorithm` route, whose callee is the CAPTURED
    plan's canonical callee cell (the one the link's CALLABLE projected, `linkedPlanIn?`); were it
    unreadable, the dispatch has no origin. C#: `Evaluator.PlanCalleeOrigin`. -/
def dispatchOriginIn (needs : Array NeedCell) (a : Nat) (eff : CallShape) : PlanRoute → CalleeOrigin
  | .algorithm =>
    match ((needs[a]?).bind NeedCell.callee).bind (linkedPlanIn? needs)
        |>.bind (fun p => (needs[p]?).bind NeedCell.callee) with
    | some c => .cell c
    | none => .none
  | _ => .written eff.callee eff.caller

/-- `dispatchOriginIn` over the current heap: a pure state read. -/
def dispatchOrigin (a : Nat) (eff : CallShape) (r : PlanRoute) : EvalM CalleeOrigin := do
  pure (dispatchOriginIn (← get).needs a eff r)

/-- One execution of plan `a` along its recorded route `r`: the ordinary call's phases (callee,
    normalization, the plan's ONE supply over the route's effective bundle, the one dispatch) under
    the written form's own error context. The dispatch is named by `dispatchName`, read right after
    the callee phase established the callee. -/
def executeAlong (route : Route) (a : Nat) (shape : CallShape) (r : PlanRoute) : EvalM CountedResult := do
  let eff := effective shape r
  let callee ← withCtx shape.ctxMsg (calleeAlong route a eff r)
  let name ← dispatchName a eff r
  let origin ← dispatchOrigin a eff r
  let result ← withCtx shape.ctxMsg (do
    let normal ← route.normalize callee eff.caller
    let cells ← prepare route.spread a eff
    route.dispatch origin normal cells eff.caller eff.values name)
  pure (reCountValueBoundary result)

/-- One execution of plan `a` (META-S3-4): its route — recorded, or established now — then
    `executeAlong`. An intrinsic route is no callable invocation (D-1A). -/
def execute (route : Route) (a : Nat) (shape : CallShape) : EvalM CountedResult := do
  match ← withCtx shape.ctxMsg (routeOf route.classify a shape) with
  | .intrinsic => throw invocationRefusal
  | r => executeAlong route a shape r

/-- Explicit invocation through a reference: `execute` with no completion shell. -/
def invoke (route : Route) (r : CallReference) : EvalM CountedResult := do
  match shapeAt? (← get).needs r.plan with
  | some shape => execute route r.plan shape
  | none => throw metaRefusal

/-- THE ARGUMENT VIEW's supply (CallReference S2): the effective argument cells of plan `a` — its
    ONE sticky preparation (`prepare`: a prepared plan returns its recorded outcome and runs
    nothing) over its ROUTE's bundle (META-S3-4, D-4/D-5: reading the supply first establishes the
    route; an extension's receiver is its first argument) — WITHOUT dispatching the target and
    without demanding any argument VALUE. `count` reads its length, selection demands only the
    selected cells, and the supply spread transports them. An intrinsic route is
    `invocationRefusal`, a non-plan address META's refusal. -/
def viewCells (spread : NeedSupply.SpreadEval) (classify : CallShape → EvalM PlanRoute) (a : Nat) :
    EvalM (List NeedSupply.Sourced) := do
  match shapeAt? (← get).needs a with
  | some shape =>
    let r ← routeOf classify a shape
    if r == .intrinsic then throw invocationRefusal
    prepare spread a (effective shape r)
  | none => throw metaRefusal

/-- What an argument view's supply spread contributes (CallReference S2): plan `a`'s ORIGINAL
    cells (`viewCells`), in order, each with its own written source (`needWrittenSource?`, as a
    collecting parameter's transported slice reports it) — no cell is allocated, copied or
    demanded. `evalSupplySpread` returns it for a spread whose last star opens `argView a`. -/
def viewSupply (spread : NeedSupply.SpreadEval) (classify : CallShape → EvalM PlanRoute) (a : Nat) :
    EvalM SpreadSupply := do
  let cells ← viewCells spread classify a
  let transported ← cells.mapM (fun (b, _) => do pure (b, ← needWrittenSource? b))
  pure (.cells transported)

/-- The written name of plan `a`'s callee — its route's effective callee once the route is recorded
    (an extension names its fallback). This names a fresh invocation of the projected callee; a plan
    on the `.Algorithm` route has its own written link as that name, while executing that plan uses
    the immediately captured plan's name (`dispatchName`). -/
def calleeName (a : Nat) : EvalM String := do
  match calleeNameIn? (← get).needs a with
  | some name => pure name
  | none => throw metaRefusal

end NeedPlan

/-- The written shape of a `.Algorithm` LINK (META-S3-1, CR-14/CR-15): an argumentless dot edge
    spelled `Algorithm`, as its receiver and fallback. Whether the edge is the intrinsic or a declared
    member is decided at run time, member-first (`algorithmIntrinsicRoute`). -/
def linkEdge? : Expr → Option (Expr × Expr)
  | .dotMember receiver name fallback none =>
    if name = "Algorithm" then some (receiver, fallback) else none
  | _ => none

/-- Decodes the receiver VALUE of `.Algorithm` into the plan address of its call reference; any
    other value (an argument view included) is the intrinsic's kind rejection. Serial Lean has one
    run, so the C# ownership check has no counterpart. C#: `Evaluator.DecodeAlgorithmReceiver`. -/
def decodeCallRef (val : Result) : EvalM Nat :=
  match val with
  | .callRef a => pure a
  | other => .error (Error.typeMismatch (algorithmRequiresCallReferenceMessage other))

/-- THE CAPTURED STEP'S LOOP SETUP (META-S3-3, D1/CR-9/CR-13), the one definition the `while` and
    `repeat` arms run after the builtin META binding: the Ready adapter cell bound to `meta step`
    read through `read` (production: the recursive VALUE driver; an adapter holds its reference, so
    reading it runs nothing) and decoded into its plan (`decodeCallRef`); then the plan's ONE sticky
    supply through `view` (production: `argumentViewCells` = `NeedPlan.viewCells`: its recorded
    preparation or exactly one formation, opening only the explicit spreads written inside the
    captured call and demanding no argument VALUE) — the loop's initial state, the ORIGINAL argument
    cells, never re-formed (an empty supply is the ordinary zero-slot state, OD-1); then the plan's
    canonical callee cell (`NeedPlan.calleeCell`, CR-13, inert) — the step, projected only when an
    iteration runs. The captured call itself is never dispatched. Laws: `KatLangArityLaws.MetaLoop`. -/
def metaLoopCapture (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (read : Nat → EvalM CountedResult) (view : Nat → EvalM (List NeedSupply.Sourced))
    (adapter : Nat) : EvalM (Nat × List Nat) := do
  let (reference, _) ← read adapter
  let plan ← decodeCallRef reference
  let initialCells := (← view plan).map Prod.fst
  let stepCell ← NeedPlan.calleeCell classify plan
  pure (stepCell, initialCells)

/-- THE `repeat` SETUP ORDER (META-S3-3, RP-1): the captured step's setup (`metaLoopCapture`,
    which prepares the captured supply) runs BEFORE the count — the outer call's own VALUE
    argument, demanded and validated once by `count` — so a captured spread's failure or effect
    precedes the count's, exactly as LOOP-01/05 ordered the retired surface; a failing setup never
    demands the count. Laws: `repeat_setup_order`, `repeat_setup_failure_skips_count`. -/
def metaRepeatSetup {α : Type} (setup : EvalM α) (count : EvalM Int) : EvalM (α × Int) := do
  let captured ← setup
  let n ← count
  pure (captured, n)

/- THE LINK of a supplied `X.Algorithm` (META-S3-1, CR-15): one link cell whose receiver `X` is ONE
    receiver cell, established lazily and recorded in the link cell (`NeedCell.receiver`), so the
    link's VALUE (`linkValue`) and its CALLABLE (`linkCallable`) demand the SAME receiver VALUE. -/
namespace NeedLink

/-- Records link `a`'s canonical receiver cell. -/
def setReceiver (a r : Nat) : EvalM Unit :=
  modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with receiver := some r }) }

/-- The canonical RECEIVER CELL of link `a`: the link's written receiver supplied in the link's
    caller context through `supplyNeed` (a parameter receiver is its existing cell), established
    by the first channel that needs it and recorded; evaluates nothing (`receiverCell_canonical`).
    C#: `Evaluator.LinkSuspension.Receiver`. -/
def receiverCell (a : Nat) : EvalM Nat := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.receiver with
  | some r => pure r
  | none =>
    match cell.suspension with
    | .expression source caller values =>
      match linkEdge? source with
      | some (receiver, _) =>
        let r ← supplyNeed receiver caller values
        setReceiver a r
        pure r
      | none => throw (Error.illegalInEval "not a link")
    | _ => throw (Error.illegalInEval "not a link")

/-- The callee cell BOTH channels of link `a` reach (CR-15): the link's ONE receiver cell, its VALUE
    through `demand`, decoded into its plan, then the plan's canonical callee cell. Production:
    `demand = demandNeedRecursive`. -/
def decodeCallee (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (demand : Nat → EvalM CountedResult) (a : Nat) : EvalM Nat := do
  let receiver ← receiverCell a
  let (value, _) ← demand receiver
  let plan ← decodeCallRef value
  NeedPlan.calleeCell classify plan

/-- The link's VALUE (CR-14 b): the callee cell's VALUE. Production: `linkValue`. -/
def value (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (demand : Nat → EvalM CountedResult) (a : Nat) : EvalM CountedResult := do
  demand (← decodeCallee classify demand a)

/-- The link's CALLABLE (CR-14 a): the callee cell's CALLABLE — `demand` is used only for the
    receiver (`callable_value_only_at_receiver`). Production: `linkCallable`. -/
def callable (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (demand : Nat → EvalM CountedResult) (project : Nat → EvalM (Option Algorithm))
    (a : Nat) : EvalM (Option Algorithm) := do
  project (← decodeCallee classify demand a)

end NeedLink

/-! ### Argument views (CallReference S2, October 2026)

`R.Arguments` is the lazy, read-only view `Result.argView a` of plan `a`'s ORIGINAL effective
argument supply. Its operations are TOTAL here, parametrized by the view's cells (`cellsOf`,
production `NeedPlan.viewCells evalSupplySpread a`: the plan's ONE sticky preparation) and by
cell VALUE demand (production `demandNeedRecursive`), so their demand laws are theorems
(`KatLangArityLaws/ArgumentView.lean`). The supply spread, the third operation, is
`NeedSupply.slot`'s `SpreadSupply.cells` arm. -/

/-- VARIADIC POSTFIX SELECTION over an ARGUMENT VIEW (CallReference S2): `selectWith`'s order with
    the view's cells as the positions. Each supplied selector is demanded and validated
    (`selectorIndex`) BEFORE the view's supply is read — `R.Arguments[]` reads nothing and
    `R.Arguments[true]` fails before any preparation; then the supply decides the position
    (`badIndex` past its end) and ONLY the selected cell is demanded, its VALUE kept whole.
    The first failure ends the selection. C#: the view arm of `Evaluator.AdvanceSelection`. -/
def selectViewWith {α : Type} (demand : α -> EvalM Result) (cellsOf : EvalM (List NeedSupply.Sourced))
    (demandCell : Nat -> EvalM Result) : List α -> EvalM (List Result)
  | [] => pure []
  | selector :: rest => do
      let n <- selectorIndex (<- demand selector)
      let cells <- cellsOf
      let selected <-
        match cells[n]? with
        | some (cell, _) => demandCell cell
        | none => .error Error.badIndex
      let tail <- selectViewWith demand cellsOf demandCell rest
      pure (selected :: tail)

/-- `first`/`last` over an empty argument view: the ordinary empty-collection selection failure
    (`applySequenceBuiltinEmptyPolicy`'s `requireSelectablePosition`). -/
def argumentViewEmptySelection (b : Builtin) : Error :=
  Error.withContext
    s!"{builtinDisplayName b} selects from an empty collection, which has no position to select"
    Error.badIndex

/-- `count`, `first` and `last` over an ARGUMENT VIEW bound as their whole collection
    (CallReference S2). `count` is the number of EFFECTIVE supplied cells — explicit spreads
    included — read from the plan's supply: no argument VALUE is demanded. `first` / `last`
    demand exactly the first / last cell and select its VALUE through the ordinary selection
    boundary (`evalFirstCounted` / `evalLastCounted`); an empty supply is the ordinary empty-collection selection failure (`badIndex`), as for
    `first([])`. C#: `Evaluator.EvalArgumentViewBuiltin`. -/
def argumentViewBuiltin (cellsOf : EvalM (List NeedSupply.Sourced)) (demandCell : Nat -> EvalM Result)
    (b : Builtin) : EvalM CountedResult := do
  let cells <- cellsOf
  match b with
  | .countBuiltin => pure (Result.atom (Int.ofNat cells.length), 1)
  | .firstBuiltin =>
      match cells.head? with
      | some (cell, _) => evalFirstCounted [← demandCell cell]
      | none => .error (argumentViewEmptySelection b)
  | .lastBuiltin =>
      match cells.getLast? with
      | some (cell, _) => evalLastCounted [← demandCell cell]
      | none => .error (argumentViewEmptySelection b)
  | _ => .error (Error.typeMismatch (argumentViewUnsupportedMessage (builtinDisplayName b)))

/-- `R.Arguments` over the receiver's VALUE (CallReference S2): a call reference yields its
    ARGUMENT VIEW — the same plan address; nothing is run, read, prepared or allocated
    (`arguments_inert`). Any other value (an argument view included) is the intrinsic's kind
    rejection. C#: `Evaluator.ArgumentsOfCallReferenceValue`. -/
def argumentsOfValue (val : Result) : EvalM CountedResult :=
  match val with
  | .callRef a => pure (.argView a, 1)
  | other => .error (Error.typeMismatch (argumentsRequiresCallReferenceMessage other))

/-- The route fact of the `Arguments` intrinsic (CallReference S2): the argument view is a
    PROPERTY of a call reference, so any written argument list — `R.Arguments()` included — is
    refused (`argumentsIsPropertyMessage`) before anything is formed or demanded; the view is
    never executed. C#: `Evaluator.RejectDotArgumentsIntrinsicArguments`. -/
def rejectArgumentsIntrinsicArguments (argsOpt : Option OutputBundle) : EvalM Unit := do
  match argsOpt with
  | none => pure ()
  | some _ => .error (Error.illegalInEval argumentsIsPropertyMessage)

/- Total collector VALUE sequencing and completion control (R5/B2).
    Recursive expression evaluation and element VALUE demand remain explicit callbacks;
    this is not a second evaluator or a CALLABLE projection operation. -/
namespace NeedDemand
def materialize
    (demand : Nat → EvalM CountedResult) (slice : List Nat) : EvalM CountedResult := do
  let values ← slice.mapM (fun a => Prod.fst <$> demand a)
  pure (makeCollectionListResult values)

/-- The computation of a suspended cell `a`. A supported supplied call is its invocation
    plan (`NeedPlan.execute`, M1.5); every other expression is evaluated by `ev`. -/
def suspendedValue (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat) :
    NeedSuspension → EvalM CountedResult
  | .ready value => pure value
  | .expression e ctx env =>
    match NeedPlan.callShape? e ctx env with
    | some shape => do
      -- META-S3-4 (D-1A): a non-callable intrinsic route is the ordinary evaluation; every other
      -- route executes the plan over its one supply.
      match ← withCtx shape.ctxMsg (NeedPlan.routeOf route.classify a shape) with
      | .intrinsic => reCountValueBoundary <$> ev e ctx env
      | r => NeedPlan.executeAlong route a shape r
    | none => reCountValueBoundary <$> ev e ctx env
  -- Materializing a collector constructs a list; its elements are subordinate computations.
  -- Store their failures as nested in this cell, without changing the original element cells.
  | .collector slice => withNestedMissingOutput (materialize demand slice)

def step (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) : EvalM CountedResult := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.state with
  | .completed outcome => return ← outcome
  | .evaluating => throw Error.demandCycle
  | .suspended =>
    modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with state := .evaluating }) }
    let outcome ← evalAttempt (suspendedValue ev route demand a cell.suspension)
    modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with state := .completed outcome }) }
    return ← outcome

end NeedDemand

/-- THE BINDER'S CHANNELS AS THE TWO TOTAL SHELLS (S6a, October 2026): VALUE is `NeedDemand.step`
    over the cell's written-expression evaluator `ev a`, the plan route and the recursive VALUE
    driver `demand`; CALLABLE is `NeedProjection.step` over the cell's written resolver
    `written a`. Every binder call site of the evaluator recursion core passes this record with
    `evalSuppliedAt`, the production route, `demandNeedRecursive` and `projectNeedWrittenAt` —
    exactly ONE unfolding of `demandNeedRecursive` and `projectNeedCallable`, whose bodies are
    these two shells, so evaluation and effect order are unchanged. Because the record is total,
    what the shells do on completed and Ready cells (memo reuse, Ready completion, identityless
    projection) is a kernel fact at the binder boundary
    (`KatLangArityLaws/NestedRepeatedNames.lean`, `shell_model_caps`); since R7 the recursive drivers
    are the total core's own operations (`EvalRec.bindingChannels`). -/
def NeedChannels.shell (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)) : NeedChannels :=
  ⟨fun a => NeedDemand.step (ev a) route demand a,
   fun a => NeedProjection.step (NeedProjection.suspended (written a)) a⟩

/-! ### The fuel-indexed evaluator core (R7, October 2026)

THE RECURSIVE EVALUATOR IS A TOTAL, FUEL-INDEXED DEFINITION. Every recursive evaluator
operation — expression evaluation, need-cell VALUE demand and CALLABLE projection, alias and
lexical resolution, invocation plans, builtins, callbacks and loop rounds — is one constructor
of `EvalCall`, whose result type is `EvalCall.Ret`. An `EvalRec` answers every call. Each
operation's body (`EvalBody.*`) is an ordinary, non-recursive definition that reaches every
other operation ONLY through the `EvalRec` it is given (`rec.evalCounted …`,
`rec.demandNeedRecursive …`), and `evalStep` dispatches a call to its body. So the evaluator is
the functional `evalStep`, and the kernel sees every body.

FUEL. `evalFuel n` iterates `evalStep` `n` times from the everywhere-incomplete answer: every
recursive `EvalCall` edge costs one unit, so `n` bounds the nesting of those calls (one `while`
round is one call, `EvalBody.whileLoop`). Finite structural helpers, including `repeatLoop`,
can make many sibling calls at one index; fuel is not a bound on all work or all helper recursion.
Fuel is a proof index only: it is not a KatLang
argument, not a C# budget, not a language error and not a bound on terminating programs. Running
out is the INCOMPLETE outcome `(.error .fuelExhausted, {})` (`EvalM.incomplete`), which retains
nothing and supports no resumption; `evalAttempt`/`tryCatch` never capture it, so it is never
memoized as a VALUE, CALLABLE or plan failure, never published to the property cache and never
caught by an ordinary language probe — it aborts the whole fueled computation. More fuel never
changes a COMPLETED outcome, failure included (`KatLangArityLaws/EvaluatorCore.lean`): the
answers are ordered by `EvalM.Approx` (incomplete below everything, a completed outcome only
below itself), `evalStep` is monotone, so the iterates form a chain.

PRODUCTION. The production operations (`evalCounted`, `demandNeedRecursive`, …, defined after the
core) are `evalUnbounded` at their call: it runs the SAME total core with `initialFuel` and, should
that be incomplete, with ever more fuel from the same entry state (`searchFuel`, a
`partial_fixpoint`, so its unfolding equation is a kernel theorem). A completed production outcome
is therefore exactly the outcome of the total core at some fuel; a divergent program still
diverges (the search never ends at run time; the kernel-level fallback of `evalUnbounded` is
never reached by compiled code). No `partial` definition remains between a public run and the
evaluator bodies. -/

namespace EvalM

/-- R7: the INCOMPLETE outcome (`Error.fuelExhausted`) with no retained state. -/
def incomplete {α : Type} : EvalM α := ⟨fun _ => (.error .fuelExhausted, {})⟩

/-- One run of `m` ends in the incomplete outcome. -/
def IsIncompleteAt {α : Type} (m : EvalM α) (s : EvalState) : Prop :=
  m.runState s = (.error .fuelExhausted, {})

/-- R7 approximation order: at every entry state, `a` is incomplete or agrees with `b`
    exactly (outcome AND final state). -/
def Approx {α : Type} (a b : EvalM α) : Prop :=
  ∀ s, a.IsIncompleteAt s ∨ a.runState s = b.runState s

theorem ext {α : Type} {a b : EvalM α} (h : ∀ s, a.runState s = b.runState s) : a = b := by
  cases a; cases b; congr; funext s; exact h s

/-- The incomplete outcome as an `EvalM` result, normalized: any incomplete outcome forgets the
    state it was reached in, so every incomplete answer is THE incomplete answer. -/
def normalizeIncomplete {α : Type} (m : EvalM α) : EvalM α :=
  ⟨fun s =>
    match m.runState s with
    | (.error .fuelExhausted, _) => (.error .fuelExhausted, {})
    | r => r⟩

theorem bind_runState {α β : Type} (m : EvalM α) (f : α → EvalM β) (s : EvalState) :
    (m >>= f).runState s =
      (match m.runState s with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) := by
  show (ExceptT.bind m.runState (fun a => (f a).runState)).run s = _
  simp only [ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.run, bind, StateT.bind]
  rcases m.runState s with ⟨r, next⟩
  cases r <;> rfl

end EvalM

/-- META-DIAG-1 at `EvalM`: a META capture keeps the capture's outcome and state, its error
    mapped through `NeedPlan.bindingRefusal` (which leaves the incomplete outcome, the one error
    `EvalM`'s handler does not observe, unchanged). -/
theorem NeedBinder.captureMeta_runState (name : Ident) (capture : EvalM Nat) (s : EvalState) :
    (NeedBinder.captureMeta name capture).runState s =
      (match capture.runState s with
       | (.ok a, next) => (.ok a, next)
       | (.error e, next) => (.error (NeedPlan.bindingRefusal name e), next)) := by
  unfold NeedBinder.captureMeta tryCatchThe
  rcases h : capture.runState s with ⟨_ | a, next⟩
  · rename_i err
    by_cases hi : (Except.error err : Except Error Unit).isIncomplete = true
    · cases Except.isIncomplete_eq_true hi
      simp [MonadExceptOf.tryCatch, h, NeedPlan.bindingRefusal, Except.isIncomplete]
    · simp [MonadExceptOf.tryCatch, h, hi, throwThe, MonadExceptOf.throw]
      rfl
  · simp [MonadExceptOf.tryCatch, h]

instance instPartialOrderEvalM {α : Type} : Lean.Order.PartialOrder (EvalM α) where
  rel := EvalM.Approx
  rel_refl := fun _ => .inr rfl
  rel_trans := by
    intro a b c hab hbc s
    rcases hab s with h | h
    · exact .inl h
    · rcases hbc s with h' | h'
      · exact .inl (h.trans h')
      · exact .inr (h.trans h')
  rel_antisymm := by
    intro a b hab hba
    apply EvalM.ext; intro s
    rcases hab s with h | h
    · rcases hba s with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

theorem EvalM.incomplete_approx {α : Type} (m : EvalM α) : EvalM.Approx EvalM.incomplete m :=
  fun _ => .inl rfl

instance : Lean.Order.MonoBind EvalM where
  bind_mono_left := by
    intro α β a₁ a₂ f h s
    show EvalM.IsIncompleteAt _ s ∨ _
    unfold EvalM.IsIncompleteAt
    rw [EvalM.bind_runState, EvalM.bind_runState]
    rcases h s with h | h
    · left; unfold EvalM.IsIncompleteAt at h; rw [h]
    · right; rw [h]
  bind_mono_right := by
    intro α β a f₁ f₂ h s
    show EvalM.IsIncompleteAt _ s ∨ _
    unfold EvalM.IsIncompleteAt
    rw [EvalM.bind_runState, EvalM.bind_runState]
    rcases a.runState s with ⟨r, next⟩
    cases r with
    | error e => right; rfl
    | ok v => exact h v next

@[partial_fixpoint_monotone] theorem monotone_evalAttempt {α γ : Type} [Lean.Order.PartialOrder γ]
    (f : γ → EvalM α) (h : Lean.Order.monotone f) :
    Lean.Order.monotone (fun x => evalAttempt (f x)) := by
  intro x y hxy s
  show EvalM.IsIncompleteAt _ s ∨ _
  rcases h x y hxy s with h' | h'
  · left; unfold EvalM.IsIncompleteAt at h' ⊢; simp [evalAttempt, h', Except.isIncomplete]
  · right; simp [evalAttempt, h']

@[partial_fixpoint_monotone] theorem monotone_normalizeIncomplete {α γ : Type} [Lean.Order.PartialOrder γ]
    (f : γ → EvalM α) (h : Lean.Order.monotone f) :
    Lean.Order.monotone (fun x => (f x).normalizeIncomplete) := by
  intro x y hxy s
  show EvalM.IsIncompleteAt _ s ∨ _
  rcases h x y hxy s with h' | h'
  · left; unfold EvalM.IsIncompleteAt at h' ⊢; simp [EvalM.normalizeIncomplete, h']
  · right; simp [EvalM.normalizeIncomplete, h']

/-! The fuel-indexed evaluator core: the call universe, its answers and the bodies. -/

inductive EvalCall : Type where
  | whileLoop (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat)
  | aliasStepIsRuntime (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String)
  | aliasValue (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | resolveAliasChase (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef))
  | resolveAliasTarget (a : Algorithm) (ctx : EvalCtx)
  | resolveAliasStructure (a : Algorithm) (ctx : EvalCtx)
  | resolveAliasValueTarget (a : Algorithm) (ctx : EvalCtx)
  | aliasOriginBinding? (a : Algorithm) (ctx : EvalCtx)
  | lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx)
  | lookupLexicalValueProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx)
  | lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx)
  | needPlanNormalizeCallee (callee : Algorithm) (ctx : EvalCtx)
  | resolveAlg (e : Expr) (ctx : EvalCtx)
  | projectNeedCallable (address : Nat)
  | projectNeedWrittenAt (address : Nat) (source : Expr) (caller : EvalCtx)
  | linkCallable (address : Nat)
  | projectParameterCallable (x : Ident) (ctx : EvalCtx)
  | projectNeedWritten (source : Expr) (caller : EvalCtx)
  | projectNeedStructuralMember (source : Expr) (ctx : EvalCtx)
  | resolveCalleeAlg (f : Expr) (ctx : EvalCtx)
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat)
  | resolveDotReceiver? (e : Expr) (ctx : EvalCtx)
  | resolveDotReceiver (e : Expr) (ctx : EvalCtx)
  | algorithmIntrinsicRoute (receiver : Expr) (ctx : EvalCtx)
  | demandNeedRecursive (address : Nat)
  | evalSuppliedAt (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | linkValue (address : Nat)
  | algorithmOfValue (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | capturedCallee (callee : Nat)
  | referenceReceiverValue (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | algorithmCalleeOf (receiver : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalSuppliedCallCounted (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalNeedUserSupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv)
  | evalNeedFamilySupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | invokeNeed (arg : ResolvedArgumentAlgorithm)
  | argumentNeed (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | runNeedStepSlots (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String)
  | runNeedWhileRound (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String)
  | evalAlgOutputCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalProgramOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | formOutputRow (ctx : EvalCtx) (env : ValEnv) (e : Expr)
  | whileVerdictSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalSequenceCallbackCall (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalSequenceCallbackCallCounted (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalAlgOutputPreparedCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalOutputRowsPreparedCore (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
  | evalCapturePreparedCore (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalCaptureCountedCore (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalCaptureValue (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalAlgOutputCountedCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalAlgOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalZeroArgumentDemandOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalZeroArgumentDemandOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalArgumentValueCounted (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalArgumentValue (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalZeroArgPropertyAccessCounted (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest)
  | evalZeroArgPropertyAccess (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalConditionalCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalUserCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv)
  | evalResolvedCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalResolvedCallbackCall (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalSequenceReduceStepCounted (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | demandSequenceBuiltinCallItemValue (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv)
  | bindSequenceBuiltinArguments (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalReduceCounted (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv)
  | evalFilterCounted (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalMapCounted (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | applyBuiltinCountedSequence (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | applyBuiltinCounted (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | applyBuiltin (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | applyBuiltinCountedResolved (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalExplicitSequenceValueItems (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalExplicitSequenceValueRowSlots (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
  | evalExplicitSequenceValueExprSlots (expr : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalUserCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalConditionalCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalResolvedCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalResolvedCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin)
  | evalCallCountedExpr (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | callLexicalWithReceiverCounted (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | rejectDotStringIntrinsicArguments (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalDotStringReceiverValue (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
  | evalDotCallCounted (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | rejectInvokeIntrinsicArguments (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | invokeCallReferenceValue (val : Result)
  | argumentViewCells (a : Nat)
  | evalArgumentViewBuiltin (b : Builtin) (a : Nat)
  | evalSequenceSpreadOperandValue (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalSequenceSpreadCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalSupplySpread (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalListLiteralCounted (elements : List Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalSequenceConstructCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalUnaryCounted (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalBinaryCounted (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalComparisonCounted (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv)
  | evalComparisonLinksCounted (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv)
  | evalCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
  | evalUserCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalConditionalCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String)
  | evalCallExpr (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | evalDotCall (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv)
  | eval (e : Expr) (ctx : EvalCtx) (env : ValEnv)

@[reducible] def EvalCall.Ret : EvalCall → Type
  | .whileLoop .. => List Nat
  | .aliasStepIsRuntime .. => Bool
  | .aliasValue .. => CountedResult
  | .resolveAliasChase .. => AliasChaseEnd
  | .resolveAliasTarget .. => Algorithm
  | .resolveAliasStructure .. => (Option Algorithm)
  | .resolveAliasValueTarget .. => AliasTerminal
  | .aliasOriginBinding? .. => (Option (Algorithm × PropDef))
  | .lookupLexicalProperty .. => ResolvedProperty
  | .lookupLexicalValueProperty .. => AliasTerminal
  | .lookupLexical .. => Algorithm
  | .needPlanNormalizeCallee .. => Algorithm
  | .resolveAlg .. => Algorithm
  | .projectNeedCallable .. => (Option Algorithm)
  | .projectNeedWrittenAt .. => (Option Algorithm)
  | .linkCallable .. => (Option Algorithm)
  | .projectParameterCallable .. => (Option Algorithm)
  | .projectNeedWritten .. => (Option Algorithm)
  | .projectNeedStructuralMember .. => (Option Algorithm)
  | .resolveCalleeAlg .. => Algorithm
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg .. => Algorithm
  | .resolveDotReceiver? .. => (Option Algorithm)
  | .resolveDotReceiver .. => Algorithm
  | .algorithmIntrinsicRoute .. => Bool
  | .demandNeedRecursive .. => CountedResult
  | .evalSuppliedAt .. => CountedResult
  | .linkValue .. => CountedResult
  | .algorithmOfValue .. => CountedResult
  | .capturedCallee .. => Algorithm
  | .referenceReceiverValue .. => Result
  | .algorithmCalleeOf .. => (Algorithm × String × Nat)
  | .evalSuppliedCallCounted .. => CountedResult
  | .evalNeedUserSupply .. => CountedResult
  | .evalNeedFamilySupply .. => CountedResult
  | .invokeNeed .. => (Option Algorithm)
  | .argumentNeed .. => Nat
  | .runNeedStepSlots .. => (List Result)
  | .runNeedWhileRound .. => (Option (List Result))
  | .evalAlgOutputCore .. => Result
  | .evalAlgOutput .. => Result
  | .evalProgramOutput .. => Result
  | .evalAlgOutputSlots .. => (List Result)
  | .formOutputRow .. => (List Result)
  | .whileVerdictSlots .. => (Option (List Result))
  | .evalSequenceCallbackCall .. => Result
  | .evalSequenceCallbackCallCounted .. => CountedResult
  | .evalAlgOutputPreparedCore .. => PreparedAlgorithmOutput
  | .evalOutputRowsPreparedCore .. => PreparedAlgorithmOutput
  | .evalCapturePreparedCore .. => PreparedAlgorithmOutput
  | .evalCaptureCountedCore .. => CountedResult
  | .evalCaptureValue .. => Result
  | .evalAlgOutputCountedCore .. => CountedResult
  | .evalAlgOutputCounted .. => CountedResult
  | .evalZeroArgumentDemandOutputCounted .. => CountedResult
  | .evalZeroArgumentDemandOutput .. => Result
  | .evalArgumentValueCounted .. => CountedResult
  | .evalArgumentValue .. => Result
  | .evalZeroArgPropertyAccessCounted .. => CountedResult
  | .evalZeroArgPropertyAccess .. => Result
  | .evalConditionalCallbackCallCounted .. => CountedResult
  | .evalUserCallbackCallCounted .. => CountedResult
  | .evalResolvedCallbackCallCounted .. => CountedResult
  | .evalResolvedCallbackCall .. => Result
  | .evalSequenceReduceStepCounted .. => CountedResult
  | .demandSequenceBuiltinCallItemValue .. => CallableCallItem
  | .bindSequenceBuiltinArguments .. => BoundSequenceBuiltinArguments
  | .evalReduceCounted .. => CountedResult
  | .evalFilterCounted .. => CountedResult
  | .evalMapCounted .. => CountedResult
  | .applyBuiltinCountedSequence .. => CountedResult
  | .applyBuiltinCounted .. => CountedResult
  | .applyBuiltin .. => Result
  | .applyBuiltinCountedResolved .. => CountedResult
  | .evalExplicitSequenceValueItems .. => (List Result)
  | .evalExplicitSequenceValueRowSlots .. => (List Result)
  | .evalExplicitSequenceValueExprSlots .. => (List Result)
  | .evalUserCallCounted .. => CountedResult
  | .evalConditionalCallCounted .. => CountedResult
  | .evalResolvedCall .. => Result
  | .evalResolvedCallCounted .. => CountedResult
  | .evalCallCountedExpr .. => CountedResult
  | .callLexicalWithReceiverCounted .. => CountedResult
  | .rejectDotStringIntrinsicArguments .. => Unit
  | .evalDotStringReceiverValue .. => Result
  | .evalDotCallCounted .. => CountedResult
  | .rejectInvokeIntrinsicArguments .. => Unit
  | .invokeCallReferenceValue .. => CountedResult
  | .argumentViewCells .. => (List NeedSupply.Sourced)
  | .evalArgumentViewBuiltin .. => CountedResult
  | .evalSequenceSpreadOperandValue .. => Result
  | .evalSequenceSpreadCounted .. => CountedResult
  | .evalSupplySpread .. => SpreadSupply
  | .evalListLiteralCounted .. => CountedResult
  | .evalSequenceConstructCounted .. => CountedResult
  | .evalUnaryCounted .. => CountedResult
  | .evalBinaryCounted .. => CountedResult
  | .evalComparisonCounted .. => CountedResult
  | .evalComparisonLinksCounted .. => CountedResult
  | .evalCounted .. => CountedResult
  | .evalUserCall .. => Result
  | .evalConditionalCall .. => Result
  | .evalCallExpr .. => Result
  | .evalDotCall .. => Result
  | .eval .. => Result

abbrev EvalRec : Type := (c : EvalCall) → EvalM c.Ret

@[inline] def EvalRec.whileLoop (rec : EvalRec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) : EvalM (List Nat) :=
  rec (.whileLoop step ctx env stepName cells)
@[inline] def EvalRec.aliasStepIsRuntime (rec : EvalRec) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) : EvalM Bool :=
  rec (.aliasStepIsRuntime step target ctx visited)
@[inline] def EvalRec.aliasValue (rec : EvalRec) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.aliasValue wired ctx env)
@[inline] def EvalRec.resolveAliasChase (rec : EvalRec) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) : EvalM AliasChaseEnd :=
  rec (.resolveAliasChase followCarriers projectRuntime a ctx visited last)
@[inline] def EvalRec.resolveAliasTarget (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.resolveAliasTarget a ctx)
@[inline] def EvalRec.resolveAliasStructure (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.resolveAliasStructure a ctx)
@[inline] def EvalRec.resolveAliasValueTarget (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM AliasTerminal :=
  rec (.resolveAliasValueTarget a ctx)
@[inline] def EvalRec.aliasOriginBinding? (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM (Option (Algorithm × PropDef)) :=
  rec (.aliasOriginBinding? a ctx)
@[inline] def EvalRec.lookupLexicalProperty (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM ResolvedProperty :=
  rec (.lookupLexicalProperty a name ctx)
@[inline] def EvalRec.lookupLexicalValueProperty (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM AliasTerminal :=
  rec (.lookupLexicalValueProperty a name ctx)
@[inline] def EvalRec.lookupLexical (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.lookupLexical a name ctx)
@[inline] def EvalRec.needPlanNormalizeCallee (rec : EvalRec) (callee : Algorithm) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.needPlanNormalizeCallee callee ctx)
@[inline] def EvalRec.resolveAlg (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.resolveAlg e ctx)
@[inline] def EvalRec.projectNeedCallable (rec : EvalRec) (address : Nat) : EvalM (Option Algorithm) :=
  rec (.projectNeedCallable address)
@[inline] def EvalRec.projectNeedWrittenAt (rec : EvalRec) (address : Nat) (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.projectNeedWrittenAt address source caller)
@[inline] def EvalRec.linkCallable (rec : EvalRec) (address : Nat) : EvalM (Option Algorithm) :=
  rec (.linkCallable address)
@[inline] def EvalRec.projectParameterCallable (rec : EvalRec) (x : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.projectParameterCallable x ctx)
@[inline] def EvalRec.projectNeedWritten (rec : EvalRec) (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.projectNeedWritten source caller)
@[inline] def EvalRec.projectNeedStructuralMember (rec : EvalRec) (source : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.projectNeedStructuralMember source ctx)
@[inline] def EvalRec.resolveCalleeAlg (rec : EvalRec) (f : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.resolveCalleeAlg f ctx)
@[inline] def EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg (rec : EvalRec) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm :=
  rec (.expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index)
@[inline] def EvalRec.resolveDotReceiver? (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  rec (.resolveDotReceiver? e ctx)
@[inline] def EvalRec.resolveDotReceiver (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  rec (.resolveDotReceiver e ctx)
@[inline] def EvalRec.algorithmIntrinsicRoute (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx) : EvalM Bool :=
  rec (.algorithmIntrinsicRoute receiver ctx)
@[inline] def EvalRec.demandNeedRecursive (rec : EvalRec) (address : Nat) : EvalM CountedResult :=
  rec (.demandNeedRecursive address)
@[inline] def EvalRec.evalSuppliedAt (rec : EvalRec) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalSuppliedAt address e ctx env)
@[inline] def EvalRec.linkValue (rec : EvalRec) (address : Nat) : EvalM CountedResult :=
  rec (.linkValue address)
@[inline] def EvalRec.algorithmOfValue (rec : EvalRec) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.algorithmOfValue val argsOpt ctx env)
@[inline] def EvalRec.capturedCallee (rec : EvalRec) (callee : Nat) : EvalM Algorithm :=
  rec (.capturedCallee callee)
@[inline] def EvalRec.referenceReceiverValue (rec : EvalRec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.referenceReceiverValue target targetAlg ctx env)
@[inline] def EvalRec.algorithmCalleeOf (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (Algorithm × String × Nat) :=
  rec (.algorithmCalleeOf receiver ctx env)
@[inline] def EvalRec.evalSuppliedCallCounted (rec : EvalRec) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult :=
  rec (.evalSuppliedCallCounted origin callee cells ctx env calleeName)
@[inline] def EvalRec.evalNeedUserSupply (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalNeedUserSupply callee cells ctx env)
@[inline] def EvalRec.evalNeedFamilySupply (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult :=
  rec (.evalNeedFamilySupply callee cells ctx env calleeName)
@[inline] def EvalRec.invokeNeed (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) : EvalM (Option Algorithm) :=
  rec (.invokeNeed arg)
@[inline] def EvalRec.argumentNeed (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat :=
  rec (.argumentNeed arg ctx env)
@[inline] def EvalRec.runNeedStepSlots (rec : EvalRec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (List Result) :=
  rec (.runNeedStepSlots step ctx env cells stepName)
@[inline] def EvalRec.runNeedWhileRound (rec : EvalRec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (Option (List Result)) :=
  rec (.runNeedWhileRound step ctx env cells stepName)
@[inline] def EvalRec.evalAlgOutputCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalAlgOutputCore a ctx env)
@[inline] def EvalRec.evalAlgOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalAlgOutput a ctx env)
@[inline] def EvalRec.evalProgramOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalProgramOutput a ctx env)
@[inline] def EvalRec.evalAlgOutputSlots (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  rec (.evalAlgOutputSlots a ctx env)
@[inline] def EvalRec.formOutputRow (rec : EvalRec) (ctx : EvalCtx) (env : ValEnv) (e : Expr) : EvalM (List Result) :=
  rec (.formOutputRow ctx env e)
@[inline] def EvalRec.whileVerdictSlots (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (Option (List Result)) :=
  rec (.whileVerdictSlots a ctx env)
@[inline] def EvalRec.evalSequenceCallbackCall (rec : EvalRec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  rec (.evalSequenceCallbackCall callee item ctx env calleeName)
@[inline] def EvalRec.evalSequenceCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  rec (.evalSequenceCallbackCallCounted callee item ctx env calleeName)
@[inline] def EvalRec.evalAlgOutputPreparedCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  rec (.evalAlgOutputPreparedCore a ctx env)
@[inline] def EvalRec.evalOutputRowsPreparedCore (rec : EvalRec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  rec (.evalOutputRowsPreparedCore rows rowCtx env)
@[inline] def EvalRec.evalCapturePreparedCore (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  rec (.evalCapturePreparedCore rows ctx env)
@[inline] def EvalRec.evalCaptureCountedCore (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalCaptureCountedCore rows ctx env)
@[inline] def EvalRec.evalCaptureValue (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalCaptureValue rows ctx env)
@[inline] def EvalRec.evalAlgOutputCountedCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalAlgOutputCountedCore a ctx env)
@[inline] def EvalRec.evalAlgOutputCounted (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalAlgOutputCounted a ctx env)
@[inline] def EvalRec.evalZeroArgumentDemandOutputCounted (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalZeroArgumentDemandOutputCounted a ctx env)
@[inline] def EvalRec.evalZeroArgumentDemandOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalZeroArgumentDemandOutput a ctx env)
@[inline] def EvalRec.evalArgumentValueCounted (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalArgumentValueCounted arg ctx env)
@[inline] def EvalRec.evalArgumentValue (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalArgumentValue arg ctx env)
@[inline] def EvalRec.evalZeroArgPropertyAccessCounted (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest := .read) : EvalM CountedResult :=
  rec (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request)
@[inline] def EvalRec.evalZeroArgPropertyAccess (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env)
@[inline] def EvalRec.evalConditionalCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  rec (.evalConditionalCallbackCallCounted callee args ctx env calleeName)
@[inline] def EvalRec.evalUserCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalUserCallbackCallCounted callee args ctx env)
@[inline] def EvalRec.evalResolvedCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  rec (.evalResolvedCallbackCallCounted callee args ctx env calleeName)
@[inline] def EvalRec.evalResolvedCallbackCall (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  rec (.evalResolvedCallbackCall callee args ctx env calleeName)
@[inline] def EvalRec.evalSequenceReduceStepCounted (rec : EvalRec) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  rec (.evalSequenceReduceStepCounted callee element accumulator ctx env calleeName)
@[inline] def EvalRec.demandSequenceBuiltinCallItemValue (rec : EvalRec) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) : EvalM CallableCallItem :=
  rec (.demandSequenceBuiltinCallItemValue item ctx env)
@[inline] def EvalRec.bindSequenceBuiltinArguments (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM BoundSequenceBuiltinArguments :=
  rec (.bindSequenceBuiltinArguments b metadata args ctx env)
@[inline] def EvalRec.evalReduceCounted (rec : EvalRec) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalReduceCounted collection stepAlg initial ctx env)
@[inline] def EvalRec.evalFilterCounted (rec : EvalRec) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalFilterCounted items predicateAlg ctx env)
@[inline] def EvalRec.evalMapCounted (rec : EvalRec) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalMapCounted collection transformAlg ctx env)
@[inline] def EvalRec.applyBuiltinCountedSequence (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.applyBuiltinCountedSequence b metadata args ctx env)
@[inline] def EvalRec.applyBuiltinCounted (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.applyBuiltinCounted b args ctx env)
@[inline] def EvalRec.applyBuiltin (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.applyBuiltin b args ctx env)
@[inline] def EvalRec.applyBuiltinCountedResolved (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.applyBuiltinCountedResolved b args ctx env)
@[inline] def EvalRec.evalExplicitSequenceValueItems (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  rec (.evalExplicitSequenceValueItems a ctx env)
@[inline] def EvalRec.evalExplicitSequenceValueRowSlots (rec : EvalRec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  rec (.evalExplicitSequenceValueRowSlots rows rowCtx env)
@[inline] def EvalRec.evalExplicitSequenceValueExprSlots (rec : EvalRec) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  rec (.evalExplicitSequenceValueExprSlots expr ctx env)
@[inline] def EvalRec.evalUserCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalUserCallCounted callee args ctx env)
@[inline] def EvalRec.evalConditionalCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  rec (.evalConditionalCallCounted callee args ctx env calleeName)
@[inline] def EvalRec.evalResolvedCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  rec (.evalResolvedCall callee args ctx env calleeName)
@[inline] def EvalRec.evalResolvedCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") (origin : CalleeOrigin := .none) : EvalM CountedResult :=
  rec (.evalResolvedCallCounted callee args ctx env calleeName origin)
@[inline] def EvalRec.evalCallCountedExpr (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalCallCountedExpr f args ctx env)
@[inline] def EvalRec.callLexicalWithReceiverCounted (rec : EvalRec) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env)
@[inline] def EvalRec.rejectDotStringIntrinsicArguments (rec : EvalRec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit :=
  rec (.rejectDotStringIntrinsicArguments argsOpt ctx env)
@[inline] def EvalRec.evalDotStringReceiverValue (rec : EvalRec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalDotStringReceiverValue target targetAlg ctx env)
@[inline] def EvalRec.evalDotCallCounted (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalDotCallCounted target name fallback argsOpt ctx env)
@[inline] def EvalRec.rejectInvokeIntrinsicArguments (rec : EvalRec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit :=
  rec (.rejectInvokeIntrinsicArguments argsOpt ctx env)
@[inline] def EvalRec.invokeCallReferenceValue (rec : EvalRec) (val : Result) : EvalM CountedResult :=
  rec (.invokeCallReferenceValue val)
@[inline] def EvalRec.argumentViewCells (rec : EvalRec) (a : Nat) : EvalM (List NeedSupply.Sourced) :=
  rec (.argumentViewCells a)
@[inline] def EvalRec.evalArgumentViewBuiltin (rec : EvalRec) (b : Builtin) (a : Nat) : EvalM CountedResult :=
  rec (.evalArgumentViewBuiltin b a)
@[inline] def EvalRec.evalSequenceSpreadOperandValue (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalSequenceSpreadOperandValue e ctx env)
@[inline] def EvalRec.evalSequenceSpreadCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalSequenceSpreadCounted e ctx env)
@[inline] def EvalRec.evalSupplySpread (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM SpreadSupply :=
  rec (.evalSupplySpread e ctx env)
@[inline] def EvalRec.evalListLiteralCounted (rec : EvalRec) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalListLiteralCounted elements ctx env)
@[inline] def EvalRec.evalSequenceConstructCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalSequenceConstructCounted e ctx env)
@[inline] def EvalRec.evalUnaryCounted (rec : EvalRec) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalUnaryCounted op operand ctx env)
@[inline] def EvalRec.evalBinaryCounted (rec : EvalRec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalBinaryCounted op a b ctx env)
@[inline] def EvalRec.evalComparisonCounted (rec : EvalRec) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalComparisonCounted first links ctx env)
@[inline] def EvalRec.evalComparisonLinksCounted (rec : EvalRec) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalComparisonLinksCounted previousExpr previous holds links ctx env)
@[inline] def EvalRec.evalCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  rec (.evalCounted e ctx env)
@[inline] def EvalRec.evalUserCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalUserCall callee args ctx env)
@[inline] def EvalRec.evalConditionalCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  rec (.evalConditionalCall callee args ctx env calleeName)
@[inline] def EvalRec.evalCallExpr (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalCallExpr f args ctx env)
@[inline] def EvalRec.evalDotCall (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.evalDotCall target name fallback argsOpt ctx env)
@[inline] def EvalRec.eval (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  rec (.eval e ctx env)

/-- META-S3-4: what a dot edge `target.name` selects on a structural MISS: one of the receiver
    intrinsics (`string`, DOT-08; `Invoke`, CallReference S1; `Arguments`, S2; `Algorithm`, CR-14)
    or the extension call through the edge's lexical fallback (DOT-03). Decided by spelling only. -/
inductive DotMiss where
  | string
  | invoke
  | arguments
  | algorithm
  | extension
  deriving Repr, BEq, DecidableEq

def DotMiss.ofName (name : Ident) : DotMiss :=
  if name = "string" then .string
  else if name = "Invoke" then .invoke
  else if name = "Arguments" then .arguments
  else if name = "Algorithm" then .algorithm
  else .extension

/-- META-S3-4: THE dot-edge route decision over the receiver's typed identity (`none` = a value
    receiver): ONE structural lookup, member-first whatever the member's spelling (Q-17 S-C); the
    member's accessibility from the site is judged after selection; a branch-only member is the
    local-only error (never a miss); only a structural miss takes the miss route. Pure: it reads
    the already resolved identity and evaluates nothing. Ordinary dot evaluation
    (`evalDotCallCounted`), the `.Algorithm` route fact (`algorithmIntrinsicRoute`) and the
    invocation-plan route (`classifyPlanRouteWith`) all decide through it.
    C#: `Evaluator.SelectDotEdge`. -/
inductive DotSelection where
  | member (targetAlg : Algorithm) (p : PropDef)
  | miss (kind : DotMiss)

def selectDotEdge (ctx : EvalCtx) (target : Expr) (name : Ident) : Option Algorithm → Except Error DotSelection
  | none => .ok (.miss (DotMiss.ofName name))
  | some targetAlg =>
    match Algorithm.lookupPropDefAny? targetAlg name with
    | some p =>
      if !(memberAccessible? ctx targetAlg p) then
        .error (Error.localOnlyProperty (openExprName target) name p.exposure)
      else .ok (.member targetAlg p)
    | none =>
      if Algorithm.conditionalBranchesDefineProperty targetAlg name then
        .error (Error.localOnlyProperty (openExprName target) name .localConditional)
      else .ok (.miss (DotMiss.ofName name))

/-- The plan route a structural miss takes: the three non-callable intrinsics are `intrinsic`. -/
def DotMiss.planRoute : DotMiss → PlanRoute
  | .string | .invoke | .arguments => .intrinsic
  | .algorithm => .algorithm
  | .extension => .extension

/-- THE ROUTE of an alias step's `.Algorithm` row over a STATIC receiver path (ALIAS-UNIFY-1, M4★):
    `algorithmIntrinsicRoute`'s member-first decision — the intrinsic exactly on a structural miss —
    with every receiver STRUCTURE read through `structureOf`, which production instantiates with the
    asking chase's STRUCTURE context (`aliasStepIsRuntime`, `aliasStructureContext`: a structure chase's
    own keys, none for an invocation or VALUE chase), so a receiver path that leads back into a structure
    computation in progress is a cycle, a failure of this decision, never an unbounded re-entry of it,
    while one that leads back into an invocation or VALUE chase is no cycle. The head is
    the ownership-first lexical lookup, RAW (or a block wired to the caller), each step a DECLARED
    member wired to its receiver (`aliasStepNavigateWith`); a receiver without static structure or a
    missing member is a failure too, which the caller reads as the runtime route exactly as it reads
    any route failure (the ordinary route reaches the same verdict through a dot-result carrier). C#:
    `Evaluator.IsRuntimeAliasStep` over `ChaseAlias`'s `structureContext`. -/
def aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (receiver : Expr) (ctx : EvalCtx) : EvalM Bool := do
  let notStatic : Error := Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName receiver))
  let found <-
    match Expr.staticAliasPath? receiver with
    | some (.resolve name, steps) =>
        match ctx.callStack with
        | owner :: _ => do
            let resolved <- lookupLexicalPropertyRaw owner name ctx
            aliasStepNavigateWith structureOf ctx notStatic resolved.alg (some resolved) name steps
        | [] => .error (Error.unknownName name)
    | some (.algorithmExpr block, steps) =>
        aliasStepNavigateWith structureOf ctx notStatic (wireToCaller ctx block) none
          (openExprName (.algorithmExpr block)) steps
    | _ => .error notStatic
  let navigated <-
    match found with
    | some p => structureOf p.alg ctx
    | none => .error notStatic
  match selectDotEdge ctx receiver "Algorithm" navigated with
  | .ok (.miss .algorithm) => pure true
  | _ => pure false

/-- META-S3-4: a plan's ROUTE (CR-2/CR-13), over identity resolution only: a written call keeps the
    ordinary callee law, except that `(t.Algorithm)(args)` on a structural miss is the `.Algorithm`
    intrinsic (`algorithmRoute`, the same route fact `evalCallCountedExpr` consults); an
    argument-bearing dot edge takes `selectDotEdge` — a declared member is an ordinary call of the
    argumentless member path (DOT-09), a miss its `DotMiss.planRoute`. A selection failure is the
    route's failure. C#: `Evaluator.ComputePlanRoute`. -/
def classifyPlanRouteWith (resolveReceiver? : Expr → EvalCtx → EvalM (Option Algorithm))
    (algorithmRoute : Expr → EvalCtx → EvalM Bool) (shape : NeedPlan.CallShape) : EvalM PlanRoute := do
  match shape.form with
  | .call =>
    match linkEdge? shape.callee with
    | some (receiver, _) => if ← algorithmRoute receiver shape.caller then pure .algorithm else pure .call
    | none => pure .call
  | .dot receiver name _ =>
    match selectDotEdge shape.caller receiver name (← resolveReceiver? receiver shape.caller) with
    | .error err => throw err
    | .ok (.member _ _) => pure .call
    | .ok (.miss kind) => pure kind.planRoute

/-- The production invocation-plan route over an evaluator answer `rec`: the one route every
    recursive VALUE edge installs (`productionPlanRoute` is it at the production answer). -/
def EvalRec.planRoute (rec : EvalRec) : NeedPlan.Route :=
  ⟨rec.resolveCalleeAlg, rec.needPlanNormalizeCallee, rec.evalSuppliedCallCounted, rec.evalSupplySpread,
   classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute, rec.projectNeedCallable⟩

/-- The binder channels every binding site of the core passes (`bindingChannels` is it at the
    production answer): the two total shells over `rec`'s written-expression evaluator, plan route,
    recursive VALUE driver and written resolver. -/
def EvalRec.bindingChannels (rec : EvalRec) : NeedChannels :=
  NeedChannels.shell rec.evalSuppliedAt rec.planRoute rec.demandNeedRecursive rec.projectNeedWrittenAt

@[partial_fixpoint_monotone] theorem EvalRec.whileLoop_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).whileLoop step ctx env stepName cells) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.aliasStepIsRuntime_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).aliasStepIsRuntime step target ctx visited) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.aliasValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).aliasValue wired ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveAliasChase_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveAliasChase followCarriers projectRuntime a ctx visited last) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveAliasTarget_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveAliasTarget a ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveAliasStructure_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveAliasStructure a ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveAliasValueTarget_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveAliasValueTarget a ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.aliasOriginBinding?_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).aliasOriginBinding? a ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.lookupLexicalProperty_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).lookupLexicalProperty a name ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.lookupLexicalValueProperty_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).lookupLexicalValueProperty a name ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.lookupLexical_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).lookupLexical a name ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.needPlanNormalizeCallee_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).needPlanNormalizeCallee callee ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveAlg_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveAlg e ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.projectNeedCallable_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).projectNeedCallable address) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.projectNeedWrittenAt_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) (source : Expr) (caller : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).projectNeedWrittenAt address source caller) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.linkCallable_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).linkCallable address) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.projectParameterCallable_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (x : Ident) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).projectParameterCallable x ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.projectNeedWritten_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (source : Expr) (caller : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).projectNeedWritten source caller) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.projectNeedStructuralMember_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (source : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).projectNeedStructuralMember source ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveCalleeAlg_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (f : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveCalleeAlg f ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveDotReceiver?_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveDotReceiver? e ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.resolveDotReceiver_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).resolveDotReceiver e ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.algorithmIntrinsicRoute_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (receiver : Expr) (ctx : EvalCtx) :
    Lean.Order.monotone (fun ρ => (recOf ρ).algorithmIntrinsicRoute receiver ctx) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.demandNeedRecursive_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).demandNeedRecursive address) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSuppliedAt_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSuppliedAt address e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.linkValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (address : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).linkValue address) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.algorithmOfValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).algorithmOfValue val argsOpt ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.capturedCallee_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).capturedCallee callee) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.referenceReceiverValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).referenceReceiverValue target targetAlg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.algorithmCalleeOf_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).algorithmCalleeOf receiver ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSuppliedCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSuppliedCallCounted origin callee cells ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalNeedUserSupply_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalNeedUserSupply callee cells ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalNeedFamilySupply_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalNeedFamilySupply callee cells ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.invokeNeed_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (arg : ResolvedArgumentAlgorithm) :
    Lean.Order.monotone (fun ρ => (recOf ρ).invokeNeed arg) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.argumentNeed_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).argumentNeed arg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.runNeedStepSlots_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).runNeedStepSlots step ctx env cells stepName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.runNeedWhileRound_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).runNeedWhileRound step ctx env cells stepName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutputCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutputCore a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutput_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutput a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalProgramOutput_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalProgramOutput a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutputSlots_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutputSlots a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.formOutputRow_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Lean.Order.monotone (fun ρ => (recOf ρ).formOutputRow ctx env e) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.whileVerdictSlots_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).whileVerdictSlots a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceCallbackCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceCallbackCall callee item ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceCallbackCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceCallbackCallCounted callee item ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutputPreparedCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutputPreparedCore a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalOutputRowsPreparedCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalOutputRowsPreparedCore rows rowCtx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCapturePreparedCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCapturePreparedCore rows ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCaptureCountedCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCaptureCountedCore rows ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCaptureValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCaptureValue rows ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutputCountedCore_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutputCountedCore a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalAlgOutputCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalAlgOutputCounted a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalZeroArgumentDemandOutputCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalZeroArgumentDemandOutputCounted a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalZeroArgumentDemandOutput_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalZeroArgumentDemandOutput a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalArgumentValueCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalArgumentValueCounted arg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalArgumentValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalArgumentValue arg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalZeroArgPropertyAccessCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalZeroArgPropertyAccess_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalConditionalCallbackCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalConditionalCallbackCallCounted callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalUserCallbackCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalUserCallbackCallCounted callee args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalResolvedCallbackCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalResolvedCallbackCallCounted callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalResolvedCallbackCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalResolvedCallbackCall callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceReduceStepCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceReduceStepCounted callee element accumulator ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.demandSequenceBuiltinCallItemValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).demandSequenceBuiltinCallItemValue item ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.bindSequenceBuiltinArguments_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).bindSequenceBuiltinArguments b metadata args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalReduceCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalReduceCounted collection stepAlg initial ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalFilterCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalFilterCounted items predicateAlg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalMapCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalMapCounted collection transformAlg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.applyBuiltinCountedSequence_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).applyBuiltinCountedSequence b metadata args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.applyBuiltinCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).applyBuiltinCounted b args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.applyBuiltin_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).applyBuiltin b args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.applyBuiltinCountedResolved_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).applyBuiltinCountedResolved b args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalExplicitSequenceValueItems_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalExplicitSequenceValueItems a ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalExplicitSequenceValueRowSlots_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalExplicitSequenceValueRowSlots rows rowCtx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalExplicitSequenceValueExprSlots_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalExplicitSequenceValueExprSlots expr ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalUserCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalUserCallCounted callee args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalConditionalCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalConditionalCallCounted callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalResolvedCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalResolvedCall callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalResolvedCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalResolvedCallCounted callee args ctx env calleeName origin) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCallCountedExpr_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCallCountedExpr f args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.callLexicalWithReceiverCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.rejectDotStringIntrinsicArguments_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).rejectDotStringIntrinsicArguments argsOpt ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalDotStringReceiverValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalDotStringReceiverValue target targetAlg ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalDotCallCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalDotCallCounted target name fallback argsOpt ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.rejectInvokeIntrinsicArguments_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).rejectInvokeIntrinsicArguments argsOpt ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.invokeCallReferenceValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (val : Result) :
    Lean.Order.monotone (fun ρ => (recOf ρ).invokeCallReferenceValue val) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.argumentViewCells_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (a : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).argumentViewCells a) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalArgumentViewBuiltin_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (b : Builtin) (a : Nat) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalArgumentViewBuiltin b a) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceSpreadOperandValue_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceSpreadOperandValue e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceSpreadCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceSpreadCounted e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSupplySpread_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSupplySpread e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalListLiteralCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalListLiteralCounted elements ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalSequenceConstructCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalSequenceConstructCounted e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalUnaryCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalUnaryCounted op operand ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalBinaryCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalBinaryCounted op a b ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalComparisonCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalComparisonCounted first links ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalComparisonLinksCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalComparisonLinksCounted previousExpr previous holds links ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCounted_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCounted e ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalUserCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalUserCall callee args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalConditionalCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalConditionalCall callee args ctx env calleeName) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalCallExpr_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalCallExpr f args ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.evalDotCall_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).evalDotCall target name fallback argsOpt ctx env) :=
  fun _ _ h => hrec _ _ h _
@[partial_fixpoint_monotone] theorem EvalRec.eval_mono {γ : Type} [Lean.Order.PartialOrder γ]
    (recOf : γ → EvalRec) (hrec : Lean.Order.monotone recOf) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Lean.Order.monotone (fun ρ => (recOf ρ).eval e ctx env) :=
  fun _ _ h => hrec _ _ h _

-- META-S3-1: the identity resolvers live in the evaluator recursion core, so a RUNTIME
-- projection (a `.Algorithm` link) can demand VALUE (`demandNeedRecursive`).
-- META-S3-2: callable-alias normalization lives here too — a runtime-target alias's step projects
-- its binding cell's CALLABLE (`projectNeedCallable`) and decides an `.Algorithm` row's route
-- member-first (`algorithmIntrinsicRoute`), and every lexical lookup normalizes through it.

/-- Whether the alias `step` with row `target` takes a RUNTIME step (FWD-02, META-S3-2): its row is a
    runtime row (`Expr.isRuntimeAliasRow`) and — for an `.Algorithm` link whose receiver is not
    parameter-rooted — the edge takes the intrinsic route in the alias's own scope, decided
    member-first exactly as the dot route decides it (`algorithmIntrinsicRoute`); a receiver that
    declares a member `Algorithm` is an ordinary static step. A route failure is the runtime cell's
    own failure, reported by its projection or VALUE. Identity navigation only.
    C#: `Evaluator.IsRuntimeAliasStep`. -/
def EvalBody.aliasStepIsRuntime (rec : EvalRec) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) : EvalM Bool := do
  if !target.isRuntimeAliasRow then return false
  match target with
  | .dotMember receiver _ _ none =>
      if receiver.isParamHeaded then return true
      -- A static receiver path's STRUCTURE is read within the ASKING chase's STRUCTURE context
      -- `visited` (ALIAS-UNIFY-1; `resolveAliasChase`): a path leading back into a structure computation
      -- in progress (`A = A.Algorithm`; `A = B.Algorithm` with `B = A`) is a cycle inside this
      -- decision, hence a route failure and a runtime step — whose projection then re-enters its own
      -- flight (`demandCycle`, NEED-09) — never an unbounded re-entry of the decision. Every other
      -- receiver reads no alias structure.
      let structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm) := fun a c => do
        match <- rec.resolveAliasChase false true a c visited none with
        | .identity found _ => pure (some found)
        | _ => pure none
      match <- evalAttempt (if receiver.isStaticAliasPath then aliasRouteIsIntrinsicWith structureOf receiver (ctx.push step)
          else rec.algorithmIntrinsicRoute receiver (ctx.push step)) with
      | .ok intrinsic => pure intrinsic
      | .error _ => pure true
  | _ => pure true

/-- THE BARE READ of a runtime-target alias `wired` (FWD-02, META-S3-2; L-RUN, M4★): its binding cell's
    VALUE (`aliasBindingCell`) — the very cell its CALLABLE projects, established once per declaring
    binding activation, so a computed receiver (`A = Mk(5).Algorithm`) is evaluated once whatever
    observes it first, and no alias owns a cache entry of its own. A parameter row is its property
    body's ordinary parameter read, which demands that parameter's own cell. Never a CALLABLE
    projection. C#: `Evaluator.EvalRuntimeAliasValueCounted`. -/
def EvalBody.aliasValue (rec : EvalRec) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
  match wired with
  | .alias _ _ _ target _ _ =>
      match target with
      | .param _ => rec.evalCounted target (ctx.push wired) env
      | _ => rec.demandNeedRecursive (<- aliasBindingCell wired target ctx)
  | other => rec.evalZeroArgumentDemandOutputCounted other ctx env

/-- The STRUCTURE context the structure computations nested in one step of `resolveAliasChase` inherit
    (ALIAS-UNIFY-1 review): a structure chase's own steps, this one included (`followCarriers = false`);
    none for an invocation or VALUE chase, which is never itself nested in a structure computation. C#:
    the `structureContext` of `Evaluator.ChaseAlias`. -/
def aliasStructureContext (followCarriers : Bool) (key : String) (visited : List String) : List String :=
  if followCarriers then [] else key :: visited

/-- THE ALIAS CHASE (FWD-02, binding indirection; runtime targets META-S3-2; M4★ whole-algorithm
    transport, ALIAS-UNIFY-1). Three operations read an alias, each by its own chase over the one
    definition, so none can substitute for another:
    * STRUCTURE (`followCarriers = false`, `projectRuntime = true`; `resolveAliasStructure`): a
      TRANSPARENT REFERENCE is followed to its target, a structural CARRIER is the end — its own
      identity, members and namespace;
    * INVOCATION (`true`, `true`; `resolveAliasTarget`): both kinds are followed to the algorithm an
      explicit call invokes, at ANY arity;
    * VALUE (`true`, `false`; `resolveAliasValueTarget`): static steps through both kinds, ending at
      the TERMINAL binding (`last`, the binding of the final static hop) or AT the first
      runtime-target alias, whose bare read is its binding cell's VALUE (`aliasValue`) — a VALUE read
      never initiates the alias's CALLABLE projection.
    A static step resolves the written target in the alias's own scope, each receiver of a member path
    read through its STATIC structure (`resolveAliasStepWith` over the static-only structure chase,
    `false`, `false`, which projects no runtime step of its own — an `.Algorithm` route decision inside
    it still reads its receiver through the projecting structure chase, `aliasStepIsRuntime`). A RUNTIME
    step (`aliasStepIsRuntime`) projects the alias's binding cell (`aliasBindingCell`,
    `projectNeedCallable`): an identity continues the chase,
    absence ends it as a VALUE VIEW (`valueView`, never the unresolved alias again), and a projection
    FAILURE propagates with its kind (never absence). An alias is never an invocation: resolving it
    binds nothing and charges nothing.

    A chase that reaches an alias BINDING it already passed (`aliasChaseKey`: the same declaration,
    resolving scope and activations) is a CYCLE: `illegalInEval aliasCycleMessage`, never a
    non-terminating chase — statically only possible in a host-built tree past the pre-evaluation
    check (`staticAliasCycle`), at run time a completed projection that leads back into its own chain;
    an ACTIVE projection re-entered is `demandCycle` (`NeedProjection.step`, NEED-09). The STRUCTURE
    computations a step nests — a member path's receiver, an `.Algorithm` row's route decision —
    inherit only the enclosing STRUCTURE context: a structure chase's own steps (a receiver leading back
    into it is a cycle: `A = A.F`, `A = A.Algorithm`), never an invocation or VALUE chase's, whose steps
    are no structure computation (`A = B` / `B = { public F(x) = x * x ⏎ A.F }`: `A(3)` is `F(3)`).
    C#: `Evaluator.ResolveAliasTarget`. -/
def EvalBody.resolveAliasChase (rec : EvalRec) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) : EvalM AliasChaseEnd :=
  match a with
  | .alias _ _ _ target _ reference =>
      if !followCarriers && !reference then pure (.identity a last)
      else do
        let key := aliasChaseKey a
        if visited.contains key then
          .error (Error.illegalInEval aliasCycleMessage)
        else if (<- rec.aliasStepIsRuntime a target ctx (aliasStructureContext followCarriers key visited)) then
          if !projectRuntime then pure (.runtime a)
          else
            match <- runtimeAliasStepWith rec.projectNeedCallable a target ctx with
            | .terminal => pure (.valueView a)
            | .continue identity => rec.resolveAliasChase followCarriers projectRuntime identity ctx (key :: visited) none
        else do
          let staticStructure : Algorithm → EvalCtx → EvalM (Option Algorithm) := fun receiver stepCtx => do
            match <- rec.resolveAliasChase false false receiver stepCtx (aliasStructureContext followCarriers key visited) none with
            | .identity found _ => pure (some found)
            | _ => pure none
          let next <- resolveAliasStepWith staticStructure a target ctx
          rec.resolveAliasChase followCarriers projectRuntime next.alg ctx (key :: visited) (some (next.owner, next.binding))
  | other => pure (.identity other last)

/-- The INVOCATION chase (`resolveAliasChase`, M4★): the algorithm an explicit call through `a`
    invokes — references and carriers alike are followed, at any arity; a value-only runtime target
    is its VALUE VIEW (`Algorithm.aliasPropertyView`). -/
def EvalBody.resolveAliasTarget (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM Algorithm := do
  match <- rec.resolveAliasChase true true a ctx [] none with
  | .identity target _ => pure target
  | .valueView alias => pure alias.aliasPropertyView
  | .runtime alias => pure alias.aliasPropertyView

/-- The STRUCTURE chase (`resolveAliasChase`, M4★): the full algorithm `a` denotes — a transparent
    reference's target, a structural carrier itself — or `none` for a value-only runtime reference,
    which has no structure. C#: `Evaluator.ResolveAliasStructure`. -/
def EvalBody.resolveAliasStructure (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
  match <- rec.resolveAliasChase false true a ctx [] none with
  | .identity target _ => pure (some target)
  | .valueView _ => pure none
  | .runtime _ => pure none

/-- The VALUE chase (`resolveAliasChase`, OD-E, M4★): where a bare read of `a` goes — the terminal
    binding of a static chain, the first runtime-target alias, or `a` itself when it is no alias.
    C#: `Evaluator.ResolveAliasValueTerminal`. -/
def EvalBody.resolveAliasValueTarget (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM AliasTerminal := do
  let chased <- rec.resolveAliasChase true false a ctx [] none
  -- A read that CROSSES a structural carrier is the subordinate computation of the carrier's written
  -- row (Q-36 with M4★): the reference-only static chase — a prefix of the VALUE chase, projecting no
  -- runtime step of its own — stops exactly at the first carrier.
  let static <- rec.resolveAliasChase false false a ctx [] none
  match chased with
  | .identity target (some (owner, binding)) => pure (.binding owner binding target static.isCarrier)
  | .identity target none => pure (.plain target static.isCarrier)
  | .valueView alias => pure (.runtime alias static.isCarrier)
  | .runtime alias => pure (.runtime alias static.isCarrier)

/-- The canonical lexical lookup with the selected binding made CALLABLE: a binding that is an alias
    keeps its own property as the binding (its exposure and accessibility) while its resolved algorithm
    is the alias's INVOCATION target (`resolveAliasTarget`). C#: `Evaluator.LookupLexical` (over
    `NormalizeAliasBinding`). -/
def EvalBody.lookupLexicalProperty (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM ResolvedProperty := do
  let resolved <- lookupLexicalPropertyRaw a name ctx
  match resolved.alg with
  | .alias _ _ _ _ _ _ => pure { resolved with alg := (<- rec.resolveAliasTarget resolved.alg ctx) }
  | _ => pure resolved

/-- The lexical lookup of a VALUE read (a property read `A`, a `.string` receiver; OD-E, M4★): the
    selected binding's VALUE terminal — the binding itself when it is no alias, else its VALUE chase
    (`resolveAliasValueTarget`): the TERMINAL binding of a static chain (whose key, owner and
    activation the read uses) or the first runtime-target alias. C#: `Evaluator.LookupLexicalForValue`. -/
def EvalBody.lookupLexicalValueProperty (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM AliasTerminal := do
  let resolved <- lookupLexicalPropertyRaw a name ctx
  match resolved.alg with
  | .alias _ _ _ _ _ _ => rec.resolveAliasValueTarget resolved.alg ctx
  | _ => pure (.binding resolved.owner resolved.binding resolved.alg false)

/-- Algorithm-position lexical lookup (call callees, dot-call targets).
    This is the algorithm PROJECTION of `lookupLexicalProperty`: the canonical
    property-carrying chain owns ownership-first ordering, open dedup,
    ambiguity, and precedence, and this projection only discards the
    owner/binding metadata that algorithm-position consumers never read. -/
def EvalBody.lookupLexical (rec : EvalRec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm := do
  let resolved <- rec.lookupLexicalProperty a name ctx
  pure resolved.alg

/-- The ordinary call's alias normalization before dispatch (`evalResolvedCallCounted`'s
    alias arm). -/
def EvalBody.needPlanNormalizeCallee (rec : EvalRec) (callee : Algorithm) (ctx : EvalCtx) : EvalM Algorithm :=
  match callee with
  | .alias _ _ _ _ _ _ => rec.resolveAliasTarget callee ctx
  | other => pure other

def EvalBody.resolveAlg (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .sequenceConstruct _ _ =>
    .error (Error.notAnAlgorithm "sequence construct expression")
  | .sequenceSpread _ =>
    .error (Error.notAnAlgorithm "spread expression")
  -- An inline block whose one row names a parameterized callable is a callable alias
  -- (`{ F }`): its callable is its target's.
  | .algorithmExpr a => rec.resolveAliasTarget (wireToCaller ctx a) ctx
  -- Capture is not algorithm identity: the algorithm channel sees only a
  -- zero-parameter value thunk over the bundle, exactly as the pre-split
  -- transparent wrapper behaved. `Apply((Inc, Dec))` therefore never receives
  -- either callable identity: a capture ARGUMENT has no CALLABLE channel at all
  -- (`projectNeedCallable` declines it through `shouldWrapArgExprAsValue`), so
  -- `f(9)` is `notAnAlgorithm` (Q-06, NEED-06), while
  -- the redundant group `Apply((Increment))` IS `Apply(Increment)` — the
  -- parser erases it before this node exists (parentheses group syntax).
  -- C#: `CaptureValueThunk`.
  | .capture rows => identifyRuntimeAlgorithm (wireToCaller ctx (Algorithm.mk none [] [] [] rows))
  | .resolve n =>
      match ctx.callStack with
      | a::_ => rec.lookupLexical a n ctx
      | []   => .error (Error.unknownName n)
  | .dotMember o n fallback args =>
      -- The internal CARRIER of a dot RESULT used as a RECEIVER: a memberless
      -- wrapper whose evaluation (evalDotCall) owns every dot semantic
      -- (structural member, `.string` intrinsic, extension call). The whole
      -- node — including its elaborated fallback identity — rides along
      -- unchanged. Its only consumer is `resolveDotReceiver` below, where a
      -- structural miss or an argument-bearing edge is a VALUE (DOT-02); it is
      -- never a program-visible callable — every algorithm-capable position,
      -- the callee included, reads a dot expression's identity through
      -- `projectNeedStructuralMember` (DOT-09; `projectNeedCallable`,
      -- `resolveCalleeAlg`).
      identifyRuntimeAlgorithm (wireToCaller ctx (Algorithm.ofExpr (.dotMember o n fallback args)))
  -- Explicit errors for syntactic forms that cannot resolve to algorithms
  | .param x =>
      -- Higher-order parameter: its supplied cell projects its CALLABLE identity
      -- (`projectNeedCallable`, never a VALUE demand). A cell without one — a
      -- computed value — and a name with no cell are not callable. The
      -- environment reaching here was shadowed by every enclosing binding's
      -- parameter names (`EvalCtx.bindParameters`), so a parameter never reaches
      -- a same-named caller binding.
      do
      match <- rec.projectParameterCallable x ctx with
      | some algorithm => pure algorithm
      | none => .error (Error.notAnAlgorithm s!"param({x})")
  | .num n   => .error (Error.notAnAlgorithm s!"num({n})")
  | .emptySequence _ => .error (Error.notAnAlgorithm "empty sequence value")
  | .listLiteral _ => .error (Error.notAnAlgorithm "list literal")
  | .unary _ _ => .error (Error.notAnAlgorithm "unary expression")
  | .binary _ _ _ => .error (Error.notAnAlgorithm "binary expression")
  | .comparison _ _ => .error (Error.notAnAlgorithm "comparison expression")
  | .index _ _ => .error (Error.notAnAlgorithm "index expression")
  | .call _ _ => .error (Error.notAnAlgorithm "call expression")
  | .stringLiteral _ => .error (Error.notAnAlgorithm "string literal")
  | .interpolatedString _ _ => .error (Error.notAnAlgorithm "interpolated string")
  | .boolLiteral _ => .error (Error.notAnAlgorithm "Boolean literal")

/-- Project identity without demanding the projected cell's VALUE or invoking anything: the ONE
    CALLABLE completion shell (`NeedProjection.step`) over the cell's suspension, written at the
    cell's own address (`projectNeedWrittenAt`). An identity-only projection never re-enters its own
    cell and never observes `projecting`; a RUNTIME projection — a supplied `X.Algorithm` link
    (`linkCallable`, META-S3-1) or a parameter-rooted path over one — demands other cells' VALUE on
    its callee route, and re-entering it is `demandCycle` (NEED-09). -/
def EvalBody.projectNeedCallable (rec : EvalRec) (address : Nat) : EvalM (Option Algorithm) :=
  NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt address)) address

/-- The CALLABLE of the written expression supplied at `address`: a supplied `X.Algorithm` LINK on the
    intrinsic route is `linkCallable` (CR-15; a declared member `Algorithm` keeps the structural
    projection), every other expression `projectNeedWritten`. C#: `ProjectSuspendedCallable`. -/
def EvalBody.projectNeedWrittenAt (rec : EvalRec) (address : Nat) (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) := do
  match linkEdge? source with
  | some (receiver, _) =>
      if <- rec.algorithmIntrinsicRoute receiver caller then rec.linkCallable address
      else rec.projectNeedWritten source caller
  | none => rec.projectNeedWritten source caller

/-- The CALLABLE of a supplied `X.Algorithm` LINK at `address` (META-S3-1, CR-15/CR-16): the link's ONE
    receiver cell's VALUE (`NeedLink.receiverCell`, shared with `linkValue`), decoded into its plan,
    then the plan's canonical callee cell's CALLABLE — never the link's own VALUE and never the callee
    cell's VALUE (`callable_value_only_at_receiver`). A receiver, decode or callee-route failure is the
    projection's failure, published by `NeedProjection.step` with its kind. C#: `ProjectLinkCallable`. -/
def EvalBody.linkCallable (rec : EvalRec) (address : Nat) : EvalM (Option Algorithm) :=
  NeedLink.callable rec.planRoute.classify rec.demandNeedRecursive rec.projectNeedCallable address

/-- A parameter's CALLABLE as its supplied cell's TYPED projection outcome (META-S3-1, L2): `some`
    identity, `none` the successful absence of one (a computed value, or no cell), and every
    projection FAILURE — whatever its kind, `notAnAlgorithm` and `illegalInEval` included —
    propagates instead of being read as absence. C#: `ResolveNeedParameterAlgorithm` with
    `IsProjectionFailure`. -/
def EvalBody.projectParameterCallable (rec : EvalRec) (x : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  projectParameterWith rec.projectNeedCallable x ctx

/-- The identity of a written supplied expression (NEED-06; M4★ whole-algorithm transport): the FULL
    algorithm it denotes — a structural dot path's member, a name's or an inline block's algorithm,
    each read through its STRUCTURE (`resolveAliasStructure`: a transparent reference is its target, a
    structural carrier itself, never its forwarding target) — or the expression's resolved algorithm,
    where a resolution that only reports absence (`isLiftableArgResolutionError`) is the successful
    outcome "no identity". -/
def EvalBody.projectNeedWritten (rec : EvalRec) (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) := do
  if let .dotMember _ _ _ _ := source then
    let selected <- rec.projectNeedStructuralMember source caller
    match selected with
    | some algorithm => rec.resolveAliasStructure algorithm caller
    | none => pure none
  else
    -- META-S3-2: a name or inline block whose static REFERENCE chain reaches a runtime-target alias is
    -- a RUNTIME projection — every failure of its structure propagates (NEED-06); any other keeps the
    -- static rule that a resolution reporting only absence is "no identity". The decision walks
    -- references statically and stops at a carrier, so it never resolves a carrier's target.
    -- C#: `ReferenceReachesRuntimeAlias` makes exactly those supplied cells runtime projections.
    let lifted : EvalM Algorithm → EvalM (Option Algorithm) := fun resolution => do
      match <- evalAttempt resolution with
      | .ok algorithm => pure (some algorithm)
      | .error err => if isLiftableArgResolutionError err then pure none else throw err
    let throughAlias : Algorithm → EvalM (Option Algorithm) := fun alias => do
      match <- evalAttempt (rec.resolveAliasChase false false alias caller [] none) with
      | .ok (.runtime _) => rec.resolveAliasStructure alias caller
      | _ =>
          match <- evalAttempt (rec.resolveAliasStructure alias caller) with
          | .ok identity => pure identity
          | .error err => if isLiftableArgResolutionError err then pure none else throw err
    match source with
    | .resolve n =>
        match caller.callStack with
        | owner :: _ =>
            match <- evalAttempt (lookupLexicalPropertyRaw owner n caller) with
            | .ok resolved =>
                match resolved.alg with
                | .alias _ _ _ _ _ _ => throughAlias resolved.alg
                | other => pure (some other)
            | .error err => if isLiftableArgResolutionError err then pure none else throw err
        | [] => .error (Error.unknownName n)
    | .algorithmExpr a =>
        match wireToCaller caller a with
        | wired@(.alias _ _ _ _ _ _) => throughAlias wired
        | wired => pure (some wired)
    | _ => lifted (rec.resolveAlg source caller)

/-- Identity-only structural navigation: THE ONE CALLABLE PROJECTION of a dot
    expression (DOT-09), shared by a supplied argument (`projectNeedCallable`, NEED-06)
    and a callee (`resolveCalleeAlg`, Q-18 C-B3). An argumentless path whose every edge
    selects a DECLARED member — a member named `string` included (Q-17 S-C) — is that
    member (accessibility checked after selection); a computed dot result (an
    argument-bearing edge, a structural miss) has no callable channel, and resolving a
    receiver must not mint a value-thunk identity. C#: `ProjectDotPathCallable`. -/
def EvalBody.projectNeedStructuralMember (rec : EvalRec) (source : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
  match source with
  | .dotMember receiver name _ none =>
      let container <- rec.projectNeedStructuralMember receiver ctx
      let some selected := container | return none
      -- M4★: the receiver's members are its STRUCTURE's — a transparent reference navigates its
      -- target's, a carrier only its own (no inheritance).
      let some algorithm <- rec.resolveAliasStructure selected ctx | return none
      match Algorithm.lookupPropDefAny? algorithm name with
      | some property =>
          if !(memberAccessible? ctx algorithm property) then
            throw (Error.localOnlyProperty (openExprName receiver) name property.exposure)
          pure (some (childOfInContext algorithm property.alg ctx))
      | none =>
          if Algorithm.conditionalBranchesDefineProperty algorithm name then
            throw (Error.localOnlyProperty (openExprName receiver) name .localConditional)
          return none
  | .resolve name =>
      match ctx.callStack with
      | owner :: _ => pure (some (<- lookupLexicalPropertyRaw owner name ctx).alg)
      | [] => throw (Error.unknownName name)
  | .algorithmExpr algorithm => pure (some (wireToCaller ctx algorithm))
  -- L2 (META-S3-1): a parameter head is its supplied cell's TYPED CALLABLE outcome — absence is
  -- `none`, and a runtime projection failure propagates whatever its kind (never read as absence).
  | .param x => rec.projectParameterCallable x ctx
  | _ => pure none

/-- The production callee law: `resolveCalleeAlgWith` at the evaluator's structural projection and
    canonical resolution. C#: `Evaluator.ResolveCallee`. -/
def EvalBody.resolveCalleeAlg (rec : EvalRec) (f : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  resolveCalleeAlgWith rec.projectNeedStructuralMember rec.resolveAliasTarget rec.resolveAlg f ctx

/-- The CALLBACK a sequence builtin invokes from an algorithm suffix slot (the
    `filter` predicate, the `map` mapper, the `reduce` reducer), through the ONE
    invoking-slot rule (`projectInvokingSlot`): a supplied cell's CALLABLE projection
    (`projectNeedCallable`), or, for an argument without a cell, its algorithm. -/
def EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg (rec : EvalRec) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .algorithm fun descriptor arg =>
    match arg with
    | .needAlgorithm address => do
        projectInvokingSlot (invokingSlotRole b) (<- rec.projectNeedCallable address)
    | .algorithm algorithm =>
        projectInvokingSlot (invokingSlotRole b) (some algorithm)
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .algorithm}"

/-- Resolve a dot edge's RECEIVER in algorithm position — the structural half
    of the ordinary DotCall law applied at EVERY level of a chain.

    Every receiver shape resolves through canonical `resolveAlg` except an
    argumentless dot edge `X.M`, which NAVIGATES: when `X` (resolved the same
    way, recursively) is an algorithm that declares `M` (any visibility;
    selection never depends on exposure), the receiver IS that member algorithm
    wired to `X` (`childOfInContext`), so `Lib.Sub.Q` reads `Sub`'s own `Q`
    before any lexical `Q(x)` is considered, exactly as `Lib.Q` reads `Lib`'s.
    A member named `string` is navigated like any member (Q-17 S-C:
    `Obj.string.Q` reads the declared `string`'s own `Q`). A declared `M` that
    is inaccessible from the site (`memberAccessible?`), or one defined only
    inside conditional branches, is the same structural error that evaluating
    `X.M` itself reports — never a fallback. When `X` does not declare `M` (or
    is not an algorithm at all), the edge is an ordinary dot RESULT — its
    lexical fallback's value, or, for `string`, the intrinsic's text — and
    resolves to `resolveAlg`'s memberless wrapper, the internal carrier of that
    VALUE, so the chain continues by value (`3.A.B` stays `B(A(3))`). An
    argument-bearing edge is a call, hence a value, and never navigates; a
    capture receiver keeps suppressing structural identity (`(A, B).V` and
    `(A*).V` fall back — a redundant group never reaches this node, so the
    sources `(Obj).V` and `(Lib.Sub).Q` are simply `Obj.V` and `Lib.Sub.Q`:
    parentheses group syntax and never change which receiver is navigated).

    The resolution is identity navigation only: no intermediate edge is
    evaluated, so a parameterized or output-less container navigates exactly
    as it does at the first level (`F.Q` works while `F` alone is an arity or
    missing-output error). A dot expression's CALLABLE identity is read by
    `projectNeedStructuralMember` alone (DOT-09). C#: `ResolveDotReceiver`.

    The outcome is TYPED (META-S3-1, L2): `some` the navigated receiver (or the carrier of a dot
    result), `none` no identity — a written value head or a parameter whose cell projects none — and
    every failure, a parameter cell's runtime projection failure of any kind included, propagates. -/
def EvalBody.resolveDotReceiver? (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  match e with
  | .dotMember o n _ none =>
      do
        match <- rec.resolveDotReceiver? o ctx with
        | some a =>
            match Algorithm.lookupPropDefAny? a n with
            | some p =>
                if !(memberAccessible? ctx a p) then
                  .error (Error.localOnlyProperty (openExprName o) n p.exposure)
                else
                  -- The navigated member is read through its STRUCTURE (M4★): a member that is a
                  -- transparent reference navigates its target, a carrier itself, and a value-only
                  -- runtime reference makes the next edge an ordinary dot result.
                  match <- rec.resolveAliasStructure (childOfInContext a p.alg ctx) ctx with
                  | some member => pure (some member)
                  | none => some <$> rec.resolveAlg e ctx
            | none =>
                if Algorithm.conditionalBranchesDefineProperty a n then
                  .error (Error.localOnlyProperty (openExprName o) n .localConditional)
                else
                  -- Structural miss: the edge is an ordinary dot result.
                  some <$> rec.resolveAlg e ctx
        -- A value receiver makes the edge an ordinary dot result too.
        | none => some <$> rec.resolveAlg e ctx
  -- A written receiver HEAD is navigated through its STRUCTURE (M4★ whole-algorithm transport): a
  -- transparent reference is its target — its members, its context, its accessibility — and a
  -- structural carrier its OWN declarations only (never its forwarding target's members). A
  -- value-only runtime reference has no structure: the edge is an ordinary dot result.
  -- C#: `Evaluator.ResolveReceiverHead`.
  | .resolve n =>
      match ctx.callStack with
      | a :: _ => do
          let resolved <- lookupLexicalPropertyRaw a n ctx
          rec.resolveAliasStructure resolved.alg ctx
      | [] => .error (Error.unknownName n)
  | .algorithmExpr a => rec.resolveAliasStructure (wireToCaller ctx a) ctx
  -- L2 (META-S3-1): a parameter head is its cell's TYPED CALLABLE outcome.
  | .param x => rec.projectParameterCallable x ctx
  -- Every other head is a written value shape: no identity is the absence report.
  | _ => do
      match <- evalAttempt (rec.resolveAlg e ctx) with
      | .ok a => pure (some a)
      | .error (.notAnAlgorithm _) => pure none
      | .error err => .error err

/-- `resolveDotReceiver?` with the absence report raised (`notAnAlgorithm`), for the consumers that
    treat every resolution failure alike. -/
def EvalBody.resolveDotReceiver (rec : EvalRec) (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  match <- rec.resolveDotReceiver? e ctx with
  | some a => pure a
  | none => rec.resolveAlg e ctx

/-- The route fact of an argumentless edge spelled `Algorithm` (META-S3-1, CR-14), decided
    member-first exactly as `evalDotCallCounted` decides it: `true` on a structural miss (a value
    receiver included) — the intrinsic — and `false` when the receiver declares `Algorithm` (a member,
    or a branch-only member whose error the ordinary route reports). Identity navigation only.
    C#: `Evaluator.IsAlgorithmIntrinsicRoute`. -/
def EvalBody.algorithmIntrinsicRoute (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx) : EvalM Bool := do
  match selectDotEdge ctx receiver "Algorithm" (<- rec.resolveDotReceiver? receiver ctx) with
  | .ok (.miss .algorithm) => pure true
  | _ => pure false


  /-- The recursive VALUE edge installs the evaluator callbacks in the ONE total
      demand shell. Since R7 this body is a kernel term of the total core; a completed production
      demand IS this body over the production operations (`production_demand_unfolds`). -/
  def EvalBody.demandNeedRecursive (rec : EvalRec) (address : Nat) : EvalM CountedResult :=
    NeedDemand.step (rec.evalSuppliedAt address)
      rec.planRoute
      rec.demandNeedRecursive address

  /-- The VALUE computation of the written expression supplied at `address` (the `ev` the production
      VALUE shell installs): a supplied `X.Algorithm` LINK on the intrinsic route is `linkValue`
      (CR-15; a declared member `Algorithm` keeps the ordinary evaluation), every other expression
      `evalCounted`. C#: `Evaluator.EvalSuspendedValue` / `TryEvalLinkValue`. -/
  def EvalBody.evalSuppliedAt (rec : EvalRec) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match linkEdge? e with
    | some (receiver, _) =>
        if <- rec.algorithmIntrinsicRoute receiver ctx then rec.linkValue address
        else rec.evalCounted e ctx env
    | none => rec.evalCounted e ctx env

  /-- The VALUE of a supplied `X.Algorithm` LINK at `address` (META-S3-1, CR-14 b / CR-15): the link's
      ONE receiver cell's VALUE — the very demand `linkCallable` makes — decoded into its plan, then
      the plan's canonical callee cell's VALUE: the captured callee read as an ordinary value in its
      captured context, with its property cache, computation or arity rejection. C#:
      `Evaluator.TryEvalLinkValue`. -/
  def EvalBody.linkValue (rec : EvalRec) (address : Nat) : EvalM CountedResult :=
    NeedLink.value rec.planRoute.classify rec.demandNeedRecursive address

  /-- The `.Algorithm` intrinsic over its receiver's VALUE (META-S3-1, CR-14): the decoded plan's
      canonical callee cell — its VALUE when the edge is bare (b), otherwise a FRESH ordinary call of
      its CALLABLE with exactly the written arguments (c), named by the plan's written callee. The
      plan's captured invocation, original supply and VALUE are never touched (CR-16).
      C#: `Evaluator.ApplyAlgorithmIntrinsic`. -/
  def EvalBody.algorithmOfValue (rec : EvalRec) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let plan <- decodeCallRef val
    let callee <- NeedPlan.calleeCell rec.planRoute.classify plan
    match argsOpt with
    | none => reCountValueBoundary <$> rec.demandNeedRecursive callee
    | some args =>
        let algorithm <- rec.capturedCallee callee
        rec.evalResolvedCallCounted algorithm args ctx env (<- NeedPlan.calleeName plan) (.cell callee)

  /-- The CALLABLE of a decoded callee cell, or the captured callee's absence report (NEED-06). -/
  def EvalBody.capturedCallee (rec : EvalRec) (callee : Nat) : EvalM Algorithm := do
    match <- rec.projectNeedCallable callee with
    | some algorithm => pure algorithm
    | none => .error (Error.notAnAlgorithm capturedCalleeDescription)

  /-- The receiver VALUE of a call-reference intrinsic on a structural miss of an algorithm receiver,
      read exactly as the `string` intrinsic reads it (alias target, the zero-argument demand law, the
      ordinary value read). C#: `Evaluator.EvalDotReferenceIntrinsicReceiver`. -/
  def EvalBody.referenceReceiverValue (rec : EvalRec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let valueAlg := (<- rec.resolveAliasValueTarget targetAlg ctx).alg
    if !(<- hasSuppliedParameterCell target ctx env) then
      match zeroArgumentDemandError? (some target) valueAlg with
      | some err => .error err
      | none => pure ()
    rec.evalDotStringReceiverValue target targetAlg ctx env

  /-- A callee written `X.Algorithm` on the intrinsic route (META-S3-1, CR-14 a/c): `X`'s VALUE read as
      the dot route reads it, decoded, and the callee cell's CALLABLE, with the plan's callee name —
      so `(R.Algorithm)(args)` is the fresh call `R.Algorithm(args)`. C#:
      `Evaluator.EvalAlgorithmCalleeCallCounted`. The third component is the decoded plan's canonical
      callee cell, the ORIGIN of the fresh call (CACHE-PUB-1). -/
  def EvalBody.algorithmCalleeOf (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (Algorithm × String × Nat) := do
    let value <-
      match <- rec.resolveDotReceiver? receiver ctx with
      | none => withNestedMissingOutput (rec.eval receiver ctx env)
      | some targetAlg => rec.referenceReceiverValue receiver targetAlg ctx env
    let plan <- decodeCallRef value
    let cell <- NeedPlan.calleeCell rec.planRoute.classify plan
    let callee <- rec.capturedCallee cell
    pure (callee, <- NeedPlan.calleeName plan, cell)

  /-- CACHE-PUB-1: a selected binding as a publication identity. An ALIAS owns no zero-argument entry
      (OD-E, M4★): its publication origin is its TARGET's (`aliasOriginBinding?`) — a static chain's
      terminal binding, a runtime reference's binding cell origin (R-6). `wired` is the binding's
      algorithm wired to its owner; no new projection or demand occurs. -/
  def EvalBody.publicationBinding? (rec : EvalRec) (owner : Algorithm) (binding : PropDef) (wired : Algorithm) (ctx : EvalCtx) :
      EvalM (Option (Algorithm × PropDef)) := do
    match wired with
    | .alias _ _ _ _ _ _ => rec.aliasOriginBinding? wired ctx
    | _ => pure (some (owner, binding))

  /-- CACHE-PUB-1: the property binding a WRITTEN callee names in its caller context — the very
      identity resolution the callee law performed (`lookupLexicalPropertyRaw` for a name, the
      structural navigation of `projectNeedStructuralMember` for an argumentless member path), read
      again without evaluating anything. Every other written form names no property binding. -/
  def EvalBody.writtenCalleeBinding? (rec : EvalRec) (callee : Expr) (caller : EvalCtx) :
      EvalM (Option (Algorithm × PropDef)) := do
    match callee with
    | .resolve n =>
        match caller.callStack with
        | owner :: _ =>
            match <- evalAttempt (lookupLexicalPropertyRaw owner n caller) with
            | .ok resolved => EvalBody.publicationBinding? rec resolved.owner resolved.binding resolved.alg caller
            | .error _ => pure none
        | [] => pure none
    | .dotMember receiver name _ none =>
        match <- evalAttempt (rec.projectNeedStructuralMember receiver caller) with
        | .ok (some selected) =>
            -- The container is the receiver's STRUCTURE, exactly as the callee law navigated it.
            match <- evalAttempt (rec.resolveAliasStructure selected caller) with
            | .ok (some container) =>
                match Algorithm.lookupPropDefAny? container name with
                | some property =>
                    EvalBody.publicationBinding? rec container property (childOfInContext container property.alg caller) caller
                | none => pure none
            | _ => pure none
        | _ => pure none
    | _ => pure none

  /-- CACHE-PUB-1: the property binding a supplied callee CELL names: its written source in its own
      caller context (a transported parameter cell keeps the argument originally written for it). -/
  def EvalBody.cellCalleeBinding? (rec : EvalRec) (address : Nat) : EvalM (Option (Algorithm × PropDef)) := do
    let needs := (← get).needs
    let callee := NeedPlan.originCalleeIn needs address
    match (needs[callee]?).map NeedCell.suspension with
    | some (.expression source caller _) => EvalBody.writtenCalleeBinding? rec source caller
    | _ => pure none

  /-- THE PUBLICATION ORIGIN OF AN ALIAS (OD-E, R-6; M4★): the property binding an explicit zero-supply
      invocation through the alias `a` may publish under — never the alias's own, since an alias owns no
      zero-argument entry. A static chain's TERMINAL binding (`resolveAliasValueTarget`); a runtime-target
      alias's binding cell's own written origin — for a supplied `X.Algorithm` link on the intrinsic
      route, its plan's canonical callee cell (CR-13), read through the link's recorded receiver and the
      plan's recorded callee cell, which the invocation's own projection already established; otherwise
      the cell's written source in its own caller context (`cellCalleeBinding?`). A failed chase and a
      value-only origin name no binding. Nothing is evaluated. C#: `Evaluator.AliasOriginBinding`. -/
  def EvalBody.aliasOriginBinding? (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) : EvalM (Option (Algorithm × PropDef)) := do
    match <- evalAttempt (rec.resolveAliasValueTarget a ctx) with
    | .ok (.binding owner binding _ _) => pure (some (owner, binding))
    | .ok (.runtime alias _) =>
        match alias with
        | .alias _ _ _ target _ _ =>
            let cell <- aliasBindingCell alias target ctx
            match ((← get).needs[cell]?).map NeedCell.suspension with
            | some (.expression source caller _) =>
                match linkEdge? source with
                | some (receiver, _) =>
                    if <- rec.algorithmIntrinsicRoute receiver caller then
                      match <- evalAttempt (NeedLink.decodeCallee rec.planRoute.classify rec.demandNeedRecursive cell) with
                      | .ok callee => EvalBody.cellCalleeBinding? rec callee
                      | .error _ => pure none
                    else EvalBody.cellCalleeBinding? rec cell
                | none => EvalBody.cellCalleeBinding? rec cell
            | _ => EvalBody.cellCalleeBinding? rec cell
        | _ => pure none
    | _ => pure none

  /-- CACHE-PUB-1: THE PROVENANCE of a zero-supply invocation — the property binding (owner and
      binding) its callee ORIGIN names (`CalleeOrigin`), or `none`. A written parameter callee is its
      supplied cell's binding; an argumentless member path is the declared member; a captured callee
      is its canonical callee cell's binding; a selected member is itself — and a binding that is an
      ALIAS is its target's origin (`aliasOriginBinding?`, OD-E/R-6, M4★), since no alias owns a
      zero-argument entry. Nothing is evaluated, invoked or demanded. C#: `Evaluator.OriginBinding`. -/
  def EvalBody.originBinding? (rec : EvalRec) (origin : CalleeOrigin) (ctx : EvalCtx) :
      EvalM (Option (Algorithm × PropDef)) := do
    match origin with
    | .none => pure none
    | .written (.param x) caller =>
        let activation ← capturedParameterActivation? x caller
        match lookupAssoc x (activation.map ParameterActivation.needs |>.getD caller.needEnv) with
        | some address => EvalBody.cellCalleeBinding? rec address
        | none => pure none
    | .written callee caller => EvalBody.writtenCalleeBinding? rec callee caller
    | .cell address => EvalBody.cellCalleeBinding? rec address
    | .bound owner binding => EvalBody.publicationBinding? rec owner binding (childOfInContext owner binding.alg ctx) ctx

  /-- THE dispatch of a normalized callee over an already formed sourced supply: the
      builtin, flat-binder, clause-family and user arms of the ordinary call. The ordinary
      call (`evalResolvedCallCounted`) forms its supply and calls it; an invocation plan
      (`NeedPlan.execute`, at `productionPlanRoute`) calls it over the plan's one prepared
      supply. The alias arm is the dispatch safety net (a normalized callee is never an
      alias). A zero-supply invocation whose ORIGIN names a property binding is that
      property's qualifying invocation (CACHE-PUB-1). C#: the arms of
      `EvalResolvedCallCounted` / `DispatchPlanned` and `EvalPublishedZeroSupplyInvocation`. -/
  def EvalBody.evalSuppliedCallCounted (rec : EvalRec) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult := do
    match callee with
    | .builtin b =>
      let supplied := cells.map fun (address, source?) =>
        ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address, source? := source? } : ResolvedArgumentAlgorithm)
      rec.applyBuiltinCountedResolved b supplied ctx env
    | .alias _ _ _ _ _ _ => do
      let target <- rec.resolveAliasTarget callee ctx
      rec.evalSuppliedCallCounted origin target cells ctx env calleeName
    | _ =>
      -- CACHE-PUB-1: a ZERO-SUPPLY invocation of an identifiable property binding is the same
      -- calculation a property-style read of that binding requests, so it participates in the ONE
      -- publication law (`evalZeroArgPropertyAccessCounted` with an `invoke` request): it executes
      -- freshly and, owning an empty entry, establishes it. Decided only now, after the supply is
      -- formed (an explicit spread may contribute no slot), and the origin's binding is read
      -- without evaluating anything. The result is the ordinary call's value boundary.
      if cells.isEmpty then
        if let some (owner, binding) <- EvalBody.originBinding? rec origin ctx then
          return reCountValueBoundary
            (<- rec.evalZeroArgPropertyAccessCounted .lexical owner binding callee ctx env (.invoke calleeName))
      match callee with
      | .conditional _ _ _ _ =>
        match flatBinderUserEquivalent? callee with
        | some simple => rec.evalNeedUserSupply simple (cells.map Prod.fst) ctx env
        | none => rec.evalNeedFamilySupply callee (cells.map Prod.fst) ctx env calleeName
      | _ => rec.evalNeedUserSupply callee (cells.map Prod.fst) ctx env

  /-- The user invocation BEFORE its value boundary: the binder, the output check, the fresh binding
      context and the body's own counted output (or a value view's binding-cell demand). The
      ordinary call re-counts it (`evalNeedUserSupply`); a qualifying zero-supply invocation
      publishes exactly this property-level counted result (CACHE-PUB-1, the `invoke` calculation
      of `zeroArgPropertyCalculation`). C#: `EvalNeedUserSupplyOutputCounted`. -/
  def EvalBody.evalNeedUserSupplyOutput (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let patterns := (Algorithm.parameterPatterns callee).map NeedPattern.ofParameter
    -- An argument the binder inspects is a SUBORDINATE computation of the call (Q-36).
    let some bindings <- withNestedMissingOutput (bindNeedPatterns (rec.bindingChannels) patterns cells) | throw Error.badArity
    if (Algorithm.output callee).isEmpty then throw (Error.missingOutput .own)
    let next <- needBindingContext ctx bindings
    if let some address ← valueViewCell? callee then
      return (← rec.demandNeedRecursive address)
    rec.evalAlgOutputCounted callee next (ValEnv.shadow env (Algorithm.params callee))

  /-- A user algorithm invoked over an already formed cell supply. Its result is the
      call's value boundary (VAL-06): ONE value, re-counted — for an ordinary call and a
      `map`/`filter`/`reduce` callback invocation alike (HO-03, Q-25 resolved October
      2026: a callback invocation IS the ordinary call). C#: `EvalNeedUserSupply`. -/
  def EvalBody.evalNeedUserSupply (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let result <- EvalBody.evalNeedUserSupplyOutput rec callee cells ctx env
    pure (reCountValueBoundary result)

  /-- A clause family invoked over an already formed cell supply: ordinary dispatch, then
      the selected body's output at the call's value boundary — for an ordinary call and a
      callback invocation alike (HO-03, PAT-11). C#: `EvalNeedFamilySupply`. -/
  def EvalBody.evalNeedFamilySupply (rec : EvalRec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult := do
    -- An argument a clause pattern inspects is a SUBORDINATE computation of the call (Q-36).
    let (body, next, values) <- withNestedMissingOutput (selectNeedFamilyBranch (rec.bindingChannels) callee cells ctx env calleeName)
    let result <- rec.evalAlgOutputCounted body next values
    pure (reCountValueBoundary result)

  def EvalBody.invokeNeed (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) : EvalM (Option Algorithm) := do
    if let some address := arg.need? then return (<- rec.projectNeedCallable address)
    pure (some arg.algorithm)

  def EvalBody.argumentNeed (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat :=
    match arg.need? with
    | some address => pure address
    | none => do readyNeed (<- rec.evalArgumentValueCounted arg ctx env)

  /-- One loop iteration's step invocation. A LOOP STEP IS AN ORDINARY CALLABLE
      INVOKED OVER THE CURRENT STATE SUPPLY (LOOP-08, Q-23 decided October 2026):
      the state cells are an already formed supply, and the step is invoked on them
      by its own ordinary machinery — a user algorithm through the one inspecting
      binder over its parameter patterns, a clause family through the ordinary
      family dispatcher (`selectNeedFamilyBranch`), a builtin through its ordinary
      argument roles (`applyBuiltinCountedResolved` over need-backed arguments, the
      callback route), an alias as its target. Only the RECEIVER is the loop's: the
      invocation's ROW SUPPLY is the next state (LOOP-03, Q-24) — a user body's or
      the selected clause's rows, and for a builtin, which has no written rows, its
      ONE result value as ONE non-spread row (`()` and collections included; never
      the result's emitted count). Patterns bind the incoming cells only: no
      pattern category is consulted when the rows form the next state
      (`Dup(x, x) = { x + 1, x + 1 }` and `Dup(x, x) = { (x + 1, x + 1)* }` both
      supply two slots). A family's or builtin's failure is its ordinary
      invocation failure under the step's own call frame (`stepName`, the written
      step as the ordinary call names its callee — `loopStepName`); a user step's
      supplied-cardinality failure is the binder's own `arityMismatch` (C# wraps it
      in its loop-state report, the same innermost kind, FORMAL-06), and pattern
      inspection retains the ordinary binder's error.

      The receiver also fixes the ORDER in which an activated body's rows are formed: it passes
      its row reader `read` (and `atomic`, its reading of a builtin's one result row). `repeat`
      reads the supply left to right (`runNeedStepSlots`); a `while` round reads condition first
      (`runNeedWhileRound`, LOOP-06). There is ONE dispatch: the binder, family dispatch,
      builtin roles and alias resolution are this definition's for both receivers.
      C#: `Evaluator.InvokeLoopStepSupply`. -/
  def EvalBody.runNeedStepWith (rec : EvalRec) {α : Type} (read : Algorithm → EvalCtx → ValEnv → EvalM α) (atomic : CountedResult → EvalM α) (again : Algorithm → EvalM α) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM α := do
    match step with
    | .builtin b =>
        withCtx s!"while evaluating call to {stepName}" do
          let supplied := cells.map fun address =>
            ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)
          let out <- rec.applyBuiltinCountedResolved b supplied ctx env
          atomic out
    | .conditional _ _ _ _ =>
        withCtx s!"while evaluating call to {stepName}" do
          let (body, next, values) <- selectNeedFamilyBranch (rec.bindingChannels) step cells ctx env stepName
          read body next values
    | .alias _ _ _ _ _ _ => do
        let target <- rec.resolveAliasTarget step ctx
        again target
    | .mk _ _ _ _ _ _ => do
        let some bindings <- bindNeedPatterns (rec.bindingChannels)
            ((Algorithm.parameterPatterns step).map NeedPattern.ofParameter) cells
          | throw Error.badArity
        let next <- needBindingContext ctx bindings
        read step next (ValEnv.shadow env (Algorithm.params step))

  /-- A `repeat` round: the step's row supply, left to right (`evalAlgOutputSlots`); a builtin's
      one result is one row (`loopStepBuiltinRows`). -/
  def EvalBody.runNeedStepSlots (rec : EvalRec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (List Result) :=
    EvalBody.runNeedStepWith rec rec.evalAlgOutputSlots (fun out => pure (loopStepBuiltinRows out))
      (fun target => rec.runNeedStepSlots target ctx env cells stepName) step ctx env cells stepName

  /-- A `while` round (LOOP-06, condition first): the step's rows read by `whileVerdictSlots`; a
      builtin's one result row is both the flag and the candidate state (`WhileRound.ofSupply`).
      `none` is a false verdict. C#: `Evaluator.InvokeLoopStepSupply` with `conditionFirst`. -/
  def EvalBody.runNeedWhileRound (rec : EvalRec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (Option (List Result)) :=
    EvalBody.runNeedStepWith rec rec.whileVerdictSlots (fun out => WhileRound.ofSupply (loopStepBuiltinRows out))
      (fun target => rec.runNeedWhileRound target ctx env cells stepName) step ctx env cells stepName


  --------------------------------------------------------------------------
  -- Evaluation
  --------------------------------------------------------------------------

  /-- Evaluate an algorithm's output expressions and collect into a single Result:
      the value projection of `evalAlgOutputPreparedCore`, so the plain and counted
      evaluators can never disagree on an output value. Each NON-spread output
      expression contributes exactly one visible slot, even when it evaluates to
      the empty sequence value `()` (counted output `0`); an explicit spread
      `expr*` contributes its expanded items, so a spread of `()` contributes
      zero items and `(A*, 99)` splices `A`'s items before `99`. The slots are
      combined with `combineOutputSlots`, which preserves singleton slot
      structure and deliberately does NOT apply the general `Result.normalize`,
      which would recursively erase useful one-item sequence structure.
      (Loop-step state reads the same rows as a SUPPLY through
      `evalAlgOutputSlots`, not as this one combined value.)

      A user-defined algorithm value may exist structurally without output, but
      forcing it in value position raises `missingOutput`. A root program is
      also forced in value position when a result is requested; explicit empty
      output is written as `()`, the empty sequence value.

      Forcing a conditional algorithm in value position fails through
      `conditionalValueAccessError?`: branch selection requires call arguments,
      so a conditional must never silently force its empty output list.
      C#: `EvalAlgOutputCore`. -/
  def EvalBody.evalAlgOutputCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalAlgOutputCountedCore a ctx env
    pure out.fst

  /-- Force a user-defined algorithm value to produce output. -/
  def EvalBody.evalAlgOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    rec.evalAlgOutputCore a ctx env

  /-- Evaluate a root program algorithm when a result is requested. The root is
      demanded for its value with NOTHING supplied, so it goes through the ONE
      zero-argument demand funnel: a root declaring no parameter pattern is its
      output exactly as before, and a root whose parameter list accepts an EMPTY
      supply (a collecting-only host-built root) binds that supply first. -/
  def EvalBody.evalProgramOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    rec.evalZeroArgumentDemandOutput a ctx env

  /-- The ROW SUPPLY of an algorithm's output (LOOP-03, VAL-07 applied to a loop
      step; the `repeat` receiver's reading — a `while` round reads the same rows condition
      first, `whileVerdictSlots`): every output row is formed once, left to right
      (`OutputRows.formLeftToRight` over `formOutputRow`); a NON-spread row
      supplies exactly one item — its value, `()` included (a row's emitted
      count is at most one since every result, loop results included, is a value
      boundary: Q-26, October 2026) — and a spread row `e*` supplies its spread
      items, possibly none. The supply depends on the rows alone: there is no
      pattern-derived flag (the former LOOP-04 packing of a pattern-bound step's
      spread row was retired by Q-24), so `(a, b)` is one item and `(a, b)*` two
      in every step. The internal `sequenceConstruct` join (never
      parser-produced) is a non-spread row like any other: it supplies exactly ONE slot (it
      emits at most one value, `Result.valueCount` of its constructed sequence; a constructed
      `()` is kept as its one slot by the `out.snd = 0` arm). A builtin has no written rows, so its value is ONE
      row (LOOP-03, Q-23) — never a re-counted supply that would read a `()` result
      as zero slots; a builtin loop step never reaches this arm (`runNeedStepSlots`
      invokes it over the state supply), only a host-built clause body that IS a
      builtin does, read with nothing supplied as the ordinary family call reads it.
      The body checks, the ONE body entry and the builtin route are the shared activated-body
      boundary `ActivatedBody.readRows` (CF-4). C#: `Evaluator.EvalAlgOutputSlots`. -/
  def EvalBody.evalAlgOutputSlots (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
    ActivatedBody.readRows rec.formOutputRow OutputRows.formLeftToRight (fun out => pure [out.fst]) a ctx env

  /-- Form ONE output row in an activated body: one ordinary counted evaluation of the row's
      expression, contributing `OutputRows.items` (LOOP-03). The one row formation of both row
      readers (`evalAlgOutputSlots`, `whileVerdictSlots`). C#: `EvalCounted` +
      `Evaluator.AddOutputRowItems`. -/
  def EvalBody.formOutputRow (rec : EvalRec) (ctx : EvalCtx) (env : ValEnv) (e : Expr) : EvalM (List Result) := do
    let out <- rec.evalCounted e ctx env
    pure (OutputRows.items e out)

  /-- ONE `while` round's reading of a step body's rows (LOOP-06, condition first — LOOP-CF1,
      October 2026): the activated-body boundary `ActivatedBody.readRows` it shares with
      `evalAlgOutputSlots` (the same body checks, ONE body entry), then
      `WhileRound.conditionFirst` over the one `formOutputRow pushedCtx env` closure, so the flag
      row and the transition rows share the entered context, its parameter cells and the evolving
      state (CF-4; laws `KatLangArityLaws/WhileRoundProduction.lean`). `none` is a `false` verdict
      (no earlier row formed); `some next` the next state. A builtin body is one atomic row
      (`WhileRound.ofSupply`). C#: `Evaluator.EvalWhileVerdictSlots`. -/
  def EvalBody.whileVerdictSlots (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (Option (List Result)) :=
    ActivatedBody.readRows rec.formOutputRow WhileRound.conditionFirst
      (fun out => WhileRound.ofSupply [out.fst]) a ctx env

  /-- Evaluate a higher-order sequence callback on one collected iteration
      item (the `filter` predicate). C#: `EvalSequenceCallbackCall`. -/
  def EvalBody.evalSequenceCallbackCall (rec : EvalRec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
    rec.evalResolvedCallbackCall callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Counted variant of `evalSequenceCallbackCall` used by `map`: the transform's
      ordinary call result (HO-03). C#: `EvalSequenceCallbackCallCounted`. -/
  def EvalBody.evalSequenceCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
    rec.evalResolvedCallbackCallCounted callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Evaluate an algorithm's output expressions once, retaining both the combined counted
      value and the explicit evaluated output-slot view. The slot list is the accumulator
      from the same left-to-right pass that constructs the combined value; it never reopens
      or decomposes that value after singleton erasure and never evaluates an expression twice.

      A parenthesized sequence-value expression such as `(a, b)` counts as one emitted value,
      while multiple top-level output expressions `a, b` count as two. Body/root output
      accumulation and the loop-step row protocol retain this distinction. A map/reduce
      callback instead returns its ordinary call result at the value boundary (Q-25). -/
  def EvalBody.evalAlgOutputPreparedCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput := do
    match a with
    | .builtin b => do
        let counted <- evalBuiltinValueCounted b
        pure { counted := counted, outputSlots := countedTopLevelValues counted }
    | _ =>
      match a.findDuplicatePropName with
      | some n => .error (Error.duplicateProperty n)
      | none =>
        match conditionalValueAccessError? "conditional" a with
        | some err => .error err
        | none => pure ()
        match a with
        | .mk _ _ _ _ [] _ => .error (Error.missingOutput .own)
        | _ => pure ()
        let pushedCtx <- enterAlgorithmBody a ctx env
        rec.evalOutputRowsPreparedCore (Algorithm.output a) pushedCtx env

  /-- The ONE shared output-row supply loop: evaluates ordered `OutputBundle`
      rows left to right (a spread row contributes its supplied items, a
      non-spread row contributes exactly one slot) and combines the collected
      slots into one canonical value (`combineOutputSlots`). Algorithm output
      evaluation reaches it after pushing the algorithm's own scope;
      `Expr.capture` evaluation reaches it directly with the surrounding
      context, because a capture owns no scope. Both receivers therefore share
      exactly the same supply semantics rather than duplicating them.
      C#: `EvalOutputRowsPreparedCore`. -/
  def EvalBody.evalOutputRowsPreparedCore (rec : EvalRec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput := do
    let rec collect : List Expr -> List Result -> Nat -> EvalM PreparedAlgorithmOutput
      | [], acc, emitted =>
          let outputSlots := acc.reverse
          pure {
            counted := (combineOutputSlots outputSlots, emitted),
            outputSlots := outputSlots
          }
      | expr :: rest, acc, emitted => do
          -- A row is a SUBORDINATE computation of the body or capture (Q-36).
          let out <- withNestedMissingOutput (rec.evalCounted expr rowCtx env)
          match expr with
          | .sequenceSpread _ =>
              collect rest ((countedTopLevelValues out).reverse ++ acc) (emitted + out.snd)
          | _ =>
              -- A non-spread output is always one visible slot, even when it is
              -- the empty sequence value (). Only an explicit spread can
              -- contribute zero items.
              let slotCount := if out.snd = 0 then 1 else out.snd
              collect rest (out.fst :: acc) (emitted + slotCount)
    collect rows [] 0

  /-- Evaluates a `Expr.capture` body's rows in the surrounding context (a
      capture owns no scope, so nothing is pushed) through the shared
      output-row supply loop. The multi-item emitted count is preserved here;
      value-position consumers re-count at the capture's value boundary
      (`Result.valueCount`). An empty bundle captures the empty sequence value.
      C#: `EvalCapturePreparedCore`. -/
  def EvalBody.evalCapturePreparedCore (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
    rec.evalOutputRowsPreparedCore rows ctx env

  def EvalBody.evalCaptureCountedCore (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let out <- rec.evalCapturePreparedCore rows ctx env
    pure out.counted

  /-- Evaluates a capture body to its single canonical captured value. -/
  def EvalBody.evalCaptureValue (rec : EvalRec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalCaptureCountedCore rows ctx env
    pure out.fst

  /-- Counted projection of the shared prepared algorithm-output evaluation. -/
  def EvalBody.evalAlgOutputCountedCore (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let out <- rec.evalAlgOutputPreparedCore a ctx env
    pure out.counted

  /-- Counted forcing variant of `evalAlgOutput`. -/
  def EvalBody.evalAlgOutputCounted (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    rec.evalAlgOutputCountedCore a ctx env

  /-- THE BARE READ AT A VALUE TERMINAL (OD-E, M4★): a runtime-target alias is its binding cell's VALUE
      (`aliasValue`); the TERMINAL binding of a static alias chain is that binding's own bare read — the
      property access under its key, owner and activation, so no alias owns a zero-argument entry and a
      reference, a carrier and the target share ONE entry; a plain algorithm is its own zero-argument
      demand. A caller applies the zero-argument value-demand law to `t.alg` first, reporting as its
      written reference. C#: `Evaluator.ReadAliasTerminal`. -/
  def EvalBody.terminalAccess (rec : EvalRec) (t : AliasTerminal) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    -- A read that crosses a structural carrier is nested (Q-36 with M4★): one wrapper, one read.
    -- A terminal binding's missing output is reported as THAT property's (M4★: the alias is its target).
    withMissingOutputNesting t.nested <|
      match t with
      | .runtime alias _ => rec.aliasValue alias ctx env
      | .binding owner binding alg _ =>
          withMissingOutputCtx (CtxMsg.property binding.name) (rec.evalZeroArgPropertyAccessCounted .lexical owner binding alg ctx env)
      | .plain alg _ => rec.evalZeroArgumentDemandOutputCounted alg ctx env

  /-- Evaluate a callable that the ONE zero-argument value-demand law
      (`zeroArgumentDemandError?`) has ACCEPTED, as the zero-argument value it
      denotes. This is the demand's evaluation half, the counterpart of that
      law's rejection half, and the ONE funnel every demand site evaluates
      through:

      * a callable that declares no top-level pattern is its output, exactly as
        before — the overwhelmingly common path, untouched;
      * a callable whose pattern list accepts an EMPTY supply (a collecting-only
        signature such as `Only(*xs) = xs`) is bound by the ORDINARY binder
        against the empty supply first, so its collecting parameter holds the
        exact empty list `[]` while the body runs, and the callee's names shadow
        every inherited tier (need cells, algorithm, counted, value) exactly as a
        written call's do;
      * a clause family that accepts zero supplied arguments dispatches its
        zero-argument branch through ordinary conditional dispatch, so branch
        selection, duplicate-pattern rejection and the value boundary are the
        call's own.

      ELIGIBILITY is what this rule changes; the CACHE is untouched: a
      property-style demand still reaches this funnel through
      `evalZeroArgPropertyAccessCounted` (the run cache), while `Only()` stays an
      ordinary call that never reads it (CACHE-PUB-1: it may establish an empty entry). C#:
      `EvalZeroArgumentDemandOutputCounted`. -/
  def EvalBody.evalZeroArgumentDemandOutputCounted (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match a with
    | .conditional _ _ _ _ => rec.evalConditionalCallCounted a [] ctx env
    -- An alias demanded with zero arguments is its VALUE terminal's bare read (OD-E, M4★): the
    -- terminal binding's read under ITS key, owner and activation, or — when its chain reaches a
    -- runtime-target alias — that alias's binding cell's VALUE (the VALUE chase never initiates a
    -- CALLABLE projection).
    | .alias _ _ _ _ _ _ => do
        EvalBody.terminalAccess rec (<- rec.resolveAliasValueTarget a ctx) ctx env
    | _ =>
      if (Algorithm.parameterPatterns a).isEmpty then
        rec.evalAlgOutputCounted a ctx env
      else do
        let some bindings <- bindNeedPatterns (rec.bindingChannels)
            ((Algorithm.parameterPatterns a).map NeedPattern.ofParameter) []
          | throw Error.badArity
        let newCtx <- needBindingContext ctx bindings
        rec.evalAlgOutputCounted a newCtx (ValEnv.shadow env (Algorithm.params a))

  /-- Value projection of `evalZeroArgumentDemandOutputCounted`.
      C#: `EvalZeroArgumentDemandOutput`. -/
  def EvalBody.evalZeroArgumentDemandOutput (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let counted <- rec.evalZeroArgumentDemandOutputCounted a ctx env
    pure counted.fst

  /-- Demand a builtin argument slot for its VALUE. A supplied cell is its one VALUE
      demand (`demandNeedRecursive`) — every argument the evaluator builds. An argument WITHOUT
      a cell (the hand-built fixture seam) is judged by the ONE zero-argument
      value-demand law (`zeroArgumentDemandError?`) from its algorithm's effective
      signature BEFORE any body is entered — a selected `if` branch, a loop's initial
      state, the `repeat` count, and the `atoms`/`range` arguments reject a callable
      that cannot accept zero supplied arguments exactly like value-position access
      does (`if(true, Inc, 0)` with `Inc(x)` is the property arity error, never
      `unknownName x` from inside `Inc`), while a callable that CAN (a property, a
      written value, a collecting-only signature) evaluates through the shared demand
      funnel. Laziness is untouched: a slot is demanded only when the builtin selects
      it. C#: `EvalResolvedArgumentCounted`. -/
  def EvalBody.evalArgumentValueCounted (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    if let some address := arg.need? then return <- rec.demandNeedRecursive address
    match zeroArgumentDemandError? arg.source? arg.algorithm with
    | some err => .error err
    | none => rec.evalZeroArgumentDemandOutputCounted arg.algorithm ctx env

  /-- Value projection of `evalArgumentValueCounted`. C#: `EvalResolvedArgument`. -/
  def EvalBody.evalArgumentValue (rec : EvalRec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let counted <- rec.evalArgumentValueCounted arg ctx env
    pure counted.fst

  /-- A property-style READ's zero-argument demand (CACHE-OWNER-D1, owner decision October 23
      2026): DECLARING-CONTEXT INHERITANCE. A parameterless user owner is checked and entered
      exactly as `evalAlgOutputPreparedCore` enters it (`ActivatedBody.check`, then its rows over
      the one entered context), except that its body entry (`enterPropertyOwnerBody`) records the
      binding context of the nearest activation on its IN-CONTEXT declaring chain
      (`propertyOwnerBindingContext a.parent`) — the very context its own cache key carries —
      and the consumer's only when there is none. So the owner's local-only properties are keyed
      on its declaring activation whichever consumer (callback, helper, loop step, branch,
      `R.Invoke()`) first reads it, and a lexical read inside the body, a structural `B.V` and an
      opened `V` select ONE entry.

      A user owner whose pattern list accepts the EMPTY supply (a collecting-only signature such as
      `Only(*xs)`; COLLECT-CACHE-1, October 23 2026) is READ the same way: the ordinary binder binds
      the empty supply first, exactly as the demand funnel binds it (`bindNeedPatterns` over no
      cells, `needBindingContext`, the shadowed values) — so `xs` is the exact empty list and the
      callee's names shadow every inherited tier — and the body is then checked and entered over
      the BOUND context with the same inherited declaring context. Only the recorded activation's
      binding context changes; the bound need tier, values and fresh binding context of the entered
      body are the binder's. A pattern list that rejects the empty supply fails as the funnel fails.

      Every other callable — a family, an alias, a builtin — is the ordinary demand
      (`evalZeroArgumentDemandOutputCounted`), whose binding boundaries mint fresh contexts as
      before; an explicit `Only()` is the `.invoke` calculation and never comes here.
      C#: `Evaluator.EvaluateZeroArgPropertyResult`. -/
  def EvalBody.evalPropertyDemandCounted (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match a with
    | .mk _ [] _ _ _ _ => do
        ActivatedBody.check a
        let inherited := (propertyOwnerBindingContext a.parent (<- get)).getD ctx.bindingContext
        let pushedCtx <- enterPropertyOwnerBody a ctx env inherited
        let out <- rec.evalOutputRowsPreparedCore (Algorithm.output a) pushedCtx env
        pure out.counted
    | .mk _ (_ :: _) _ _ _ _ => do
        let some bindings <- bindNeedPatterns (rec.bindingChannels)
            ((Algorithm.parameterPatterns a).map NeedPattern.ofParameter) []
          | throw Error.badArity
        let boundCtx <- needBindingContext ctx bindings
        let boundEnv := ValEnv.shadow env (Algorithm.params a)
        ActivatedBody.check a
        let inherited := (propertyOwnerBindingContext a.parent (<- get)).getD ctx.bindingContext
        let pushedCtx <- enterPropertyOwnerBody a boundCtx boundEnv inherited
        let out <- rec.evalOutputRowsPreparedCore (Algorithm.output a) pushedCtx boundEnv
        pure out.counted
    | _ => rec.evalZeroArgumentDemandOutputCounted a ctx env

  /-- The property-level calculation one request of the property cache performs (CACHE-PUB-1):
      a READ is the property's zero-argument demand (`evalPropertyDemandCounted`, CACHE-OWNER-D1); an
      INVOCATION is the ordinary call's own FRESH zero-supply invocation of the normalized callee —
      exactly the user / flat-binder / family arms of `evalSuppliedCallCounted` over the empty supply
      (a fresh binding context, the binder, the output check) — taken BEFORE the user arm's value
      boundary, so what an owning invocation publishes is the property-level counted result a read
      would publish (a family's own dispatch result is already its value boundary, as its read's
      is). C#: the `evaluate` callbacks of `EvalPublishedZeroSupplyInvocation`. -/
  def EvalBody.zeroArgPropertyCalculation (rec : EvalRec) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match request with
    | .read => EvalBody.evalPropertyDemandCounted rec resolvedAlgorithm ctx env
    | .invoke calleeName =>
        match resolvedAlgorithm with
        | .conditional _ _ _ _ =>
            match flatBinderUserEquivalent? resolvedAlgorithm with
            | some simple => rec.evalNeedUserSupply simple [] ctx env
            | none => rec.evalNeedFamilySupply resolvedAlgorithm [] ctx env calleeName
        | _ => EvalBody.evalNeedUserSupplyOutput rec resolvedAlgorithm [] ctx env

  /-- Property-style zero-parameter access may reuse the per-run cache; a qualifying explicit
      zero-supply invocation shares the same publication law (CACHE-PUB-1, owner decision
      October 22 2026, superseding "an explicit call neither reads nor populates the entry").

      THE PUBLICATION LAW (Q-37, owner decision October 11 2026, superseding the
      first-successful-completion rule; extended to invocations by CACHE-PUB-1): the OUTERMOST
      successful qualifying evaluation of a key owns its entry, whether it is a property-style
      read or an explicit zero-supply invocation. A request on an empty key that is not active
      makes it the key's OWNER: the key is active while its calculation runs and is released on
      success and failure alike, and only a successful owner publishes. A request on an ACTIVE
      key — the same binding reached again, directly or through other properties and calls,
      before its owner finished — is RE-ENTRANT: it performs its calculation and returns its own
      (possibly intermediate) result but publishes nothing. A failed owner publishes nothing for
      its key; entries other keys' owners published meanwhile stay (`EvalM` retains state).
      `insert` never replaces an entry, and under this law no completion can reach an active
      key's entry. Reads and invocations differ only in their calculation
      (`zeroArgPropertyCalculation`) and in what an ESTABLISHED entry means: a read returns it,
      an invocation never does — it always executes freshly and leaves the entry unchanged. The
      result is the property-level counted result; an invocation's caller applies the call's
      value boundary. C#: `ZeroArgPropertyPublications` (`EvaluateMiss` / `Invoke`). -/
  def EvalBody.evalZeroArgPropertyAccessCounted (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) : EvalM CountedResult := do
    if isCacheableZeroArgPropertyAlgorithm resolvedAlgorithm then
      let state <- get
      let key := zeroArgPropertyCacheKey accessKind owner binding ctx env
        (propertyOwnerBindingContext resolvedAlgorithm.parent state)
      match ZeroArgPropertyCache.lookup state.zeroArgPropertyCache key with
      | some cached =>
          match request with
          | .read => pure cached
          -- An explicit invocation is FRESH: it never obtains its result from the entry, and it
          -- cannot replace it.
          | .invoke _ => EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env
      | none =>
          if state.activeZeroArgProperties.contains key then
            -- Re-entrant: an enclosing evaluation of this key owns publication.
            EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env
          else
            let active := state.activeZeroArgProperties
            set { state with activeZeroArgProperties := key :: active }
            let outcome <- evalAttempt (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)
            let nextState <- get
            match outcome with
            | .ok counted =>
                set { nextState with
                  activeZeroArgProperties := active,
                  zeroArgPropertyCache :=
                    ZeroArgPropertyCache.insert nextState.zeroArgPropertyCache key counted }
                pure counted
            | .error err =>
                set { nextState with activeZeroArgProperties := active }
                throw err
    else
      EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env

  def EvalBody.evalZeroArgPropertyAccess (rec : EvalRec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let counted <- rec.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env
    pure counted.fst

  /-- A clause-family callback invocation: the ordinary family dispatch over Ready
      cells, whose result is the ordinary call result (HO-03, PAT-11). -/
  def EvalBody.evalConditionalCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult := do
    let cells <- args.mapM readyNeed
    rec.evalNeedFamilySupply callee cells ctx env calleeName

  /-- Bind pre-evaluated callback arguments to a user algorithm through the ONE
      ordinary counted binder and evaluate its output. THE CALLBACK LAW
      (September 2026): every value a callback operation supplies is ONE
      ordinary argument, bound exactly as the ordinary call with the same
      supply — `map(xs, F)` calls `F(E)` for each element `E`, `reduce` calls
      `R(E, Acc)` — so fixed parameters take their values unchanged, a
      collector collects the supplied values exactly, and only the callee's
      explicit structural patterns open a value (a sequence pattern a sequence
      element, a list pattern a list element). There is no callback row
      convention: `map([(1, 2)], Add)` with `Add(x, y)` is the ordinary arity
      error of `Add((1, 2))`, while `AddPair((x, y))` opens the element
      explicitly. The RESULT is the ordinary call result too (HO-03, Q-25
      resolved October 2026): one value at the call's value boundary, several
      rows arriving as one sequence value. -/
  def EvalBody.evalUserCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let cells <- args.mapM readyNeed
    rec.evalNeedUserSupply callee cells ctx env

  /-- Evaluate a resolved algorithm against pre-evaluated callback arguments
      that preserve their emitted top-level counts.

      This is the shared callback-binding path for higher-order sequence
      builtins. Each callback item is a selected value, so inside the callback
      body it behaves exactly like `S[i]` — one value, never opened — and it is
      bound as one ordinary argument (`evalUserCallbackCallCounted`). -/
  def EvalBody.evalResolvedCallbackCallCounted (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult := do
    match callee with
    | .builtin b => do
        let cells <- args.mapM readyNeed
        let supplied := cells.map fun address => ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)
        rec.applyBuiltinCounted b supplied ctx env
    | .conditional _ _ _ _ =>
        match flatBinderUserEquivalent? callee with
        | some simple => rec.evalUserCallbackCallCounted simple args ctx env
        | none =>
            rec.evalConditionalCallbackCallCounted callee args ctx env calleeName
    -- An alias callback is its target, normalized BEFORE any invocation, so the alias charges
    -- nothing. C#: `EvalAliasCallbackCallCounted`.
    | .alias _ _ _ _ _ _ => do
        let target <- rec.resolveAliasTarget callee ctx
        rec.evalResolvedCallbackCallCounted target args ctx env calleeName
    | _ => rec.evalUserCallbackCallCounted callee args ctx env

  /-- Non-counted wrapper for callback calls (the value projection of
      `evalResolvedCallbackCallCounted`). -/
  def EvalBody.evalResolvedCallbackCall (rec : EvalRec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result := do
    let out <- rec.evalResolvedCallbackCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Evaluate a `reduce` step on one collected iteration item. The reducer is
      an ordinary two-argument callback (THE CALLBACK LAW): it receives the
      element and the accumulator as exactly two arguments, each ONE value —
      `reduce(xs, R, init)` calls `R(E, Acc)` — so a collecting parameter on
      either side collects those argument values exactly and a structured
      accumulator is opened only by the reducer's own explicit pattern
      (`R(x, (a, b))`). The accumulator is always one value: the initial
      accumulator is reified at the value boundary, and each step's result is
      its ordinary call result, passed whole as the next accumulator (HO-03).
      C#: `EvalSequenceReduceStepCounted`. -/
  def EvalBody.evalSequenceReduceStepCounted (rec : EvalRec) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
    rec.evalResolvedCallbackCallCounted callee
      [ countedSequenceCallbackItem element
      , (accumulator, Result.valueCount accumulator)
      ]
      ctx env calleeName

  /-- Demand ONE collection-builtin call item that binding has placed in a VALUE
      position: the demand happens HERE, once the descriptor has decided the slot is
      a value (a CALLBACK item is never demanded — a CALLBACK slot receives the
      callable, never a value). An item that was already evaluated, or whose
      evaluation already failed, is never re-entered.

      A supplied cell — every item the evaluator builds — is demanded through its one
      VALUE demand. When that demand FAILS, the item keeps the failure and — unless
      its WRITTEN slot is a parameter, whose established failure is reported as the
      written argument's own (CALL-06) — records the cell's CALLABLE projection, never
      a VALUE demand (NEED-06), as the callable the slot NAMES
      (`CallableCallItem.callable?`), so the slot's rejection report judges it
      (`sequenceBuiltinValueDemandErrorWith?`: the zero-argument law's report keyed by
      the written source, and `reduce`'s dedicated initial-accumulator report,
      `reduceInitialRejection`). A projection that fails names no callable.

      An item WITHOUT a cell (the hand-built fixture seam) is evaluated through the
      shared demand funnel only when the ONE law accepts its callable
      (`acceptsZeroArgumentValueDemand` — a collecting-only signature such as `Only`
      alongside every zero-parameter property); every other such item is returned
      untouched for `sequenceBuiltinValueDemandError?` to report.
      C#: `DemandSequenceBuiltinCallItemValue` → `FinishNeedCallItemDemand`. -/
  def EvalBody.demandSequenceBuiltinCallItemValue (rec : EvalRec) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) : EvalM CallableCallItem := do
    if let some address := item.need? then
      if item.value?.isSome || item.error?.isSome then return item
      match <- evalAttempt (rec.demandNeedRecursive address) with
      | .ok value => return { item with value? := some value.fst }
      | .error err =>
          match item.source? with
          | some (.param _) => return { item with error? := some err }
          | _ =>
              let named? <- match <- evalAttempt (rec.projectNeedCallable address) with
                | .ok (some carrier@(.alias _ _ _ _ _ false)) =>
                    -- FA-OQ-1 under M4★: a projected structural CARRIER names its VALUE terminal, whose
                    -- bare view its VALUE read delegated to, so the slot reports as its written target
                    -- reference does (the static VALUE chase, which projects no runtime step of its own;
                    -- any `.Algorithm` route decision it reads was taken by the failed demand, and those
                    -- projections are sticky); a runtime terminal or a failed chase keeps the carrier.
                    -- C#: `NameCarrierValueTerminal`, which observes this chase without initiating it
                    -- (META-S3-0b); see SEMANTIC-ALIGNMENT.md, ALIAS-UNIFY-1 corrections (5) and (11).
                    match <- evalAttempt (rec.resolveAliasValueTarget carrier ctx) with
                    | .ok (.runtime _ _) => pure (some carrier)
                    | .ok terminal => pure (some terminal.alg)
                    | .error _ => pure (some carrier)
                | .ok projected => pure projected
                | .error _ => pure none
              return { item with error? := some err, callable? := named? }
    match item.value?, item.error?, item.algorithm? with
    | none, none, some alg =>
        if acceptsZeroArgumentValueDemand (item.callable?.getD alg) then
          match <- evalAttempt (rec.evalZeroArgumentDemandOutputCounted alg ctx env) with
          | .ok counted => pure { item with value? := some counted.fst }
          | .error err => pure { item with error? := some err }
        else
          pure item
    | _, _, _ => pure item

    def EvalBody.bindSequenceBuiltinArguments (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM BoundSequenceBuiltinArguments := do
    let items := collectSequenceCallableCallItems args
    -- A collection builtin is an ordinary fixed-arity callable: exactly one
    -- collection argument followed by its fixed control arguments
    -- (`count(collection)`, `take(collection, count)`,
    -- `map(collection, mapper)`). An unspread sequence or list value is ONE
    -- argument at this call boundary, exactly like at every other call
    -- boundary; only explicit caller-site spread alters argument boundaries,
    -- and the spread items obey the same fixed arity
    -- (`count([1, 2, 3]*)` supplies three arguments and is an arity error).
    -- Nothing is opened before binding.
    let expectedArgCount := 1 + metadata.suffixArgs.length
    if items.length != expectedArgCount then
      .error (Error.arityMismatch expectedArgCount items.length)
    match items with
    | [] => .error (Error.arityMismatch expectedArgCount 0)
    | collectionItem :: controlItems => do
        -- The `collection` parameter is a VALUE position, so demand the bound item
        -- through the ONE zero-argument value-demand law before reading its value.
        let collectionItem <- rec.demandSequenceBuiltinCallItemValue collectionItem ctx env
        let collectionValue <-
          match collectionItem.value? with
          | some value => pure value
          | none =>
              match sequenceBuiltinValueDemandError? collectionItem with
              | some err => .error err
              | none => .error Error.badArity
        -- An ARGUMENT VIEW bound as the whole collection (CallReference S2) is no collection
        -- value: `count`/`first`/`last` read its cells (`view?`); every other builtin refuses it
        -- before any control argument is demanded.
        if let .argView a := collectionValue then
          if b.readsArgumentView then
            return { preparedInput := { items := [] }, iterationItems := [], suffixArgs := [], view? := some a }
          else
            .error (Error.typeMismatch (argumentViewUnsupportedMessage (builtinDisplayName b)))
        -- The one-level builtin collection view applies AFTER binding, to the
        -- bound collection value only: a lone sequence or exact list value
        -- opens to its immediate items, and any other value is a one-element
        -- collection (`count(7)` is 1). Opening is never recursive — nested
        -- sequence/list elements stay intact as single items.
        let collectionValues := builtinCollectionItems collectionValue
        let collected : CollectedSequenceBuiltinInput := { items := collectionValues }
        let preparedInput <- prepareSequenceBuiltinInput b metadata collected
        let rec prepareControls :
            List SequenceBuiltinSuffixArgDescriptor ->
            List CallableCallItem ->
            EvalM (List PreparedSequenceBuiltinSuffixArg)
          | [], [] => pure []
          | descriptor :: descriptors, item :: rest => do
              -- A `.value` / `.wholeNumber` control is a VALUE position, so it is
              -- demanded through the ONE law; an `.algorithm` control is a
              -- CALLBACK slot and is never demanded.
              let item <-
                match descriptor.kind with
                | .algorithm => pure item
                | _ => rec.demandSequenceBuiltinCallItemValue item ctx env
              let prepared <- prepareSequenceBuiltinSuffixArgItem b descriptor item
              let tail <- prepareControls descriptors rest
              pure (prepared :: tail)
          | _, _ =>
              internalSequenceBuiltinSuffixArgMetadataError b "mismatched control arguments"
        let suffixArgs <- prepareControls metadata.suffixArgs controlItems
        pure {
          preparedInput := preparedInput
          iterationItems := collectionValues.map (fun value => (value, 1))
          suffixArgs := suffixArgs
        }

    /-- Evaluate `reduce` over the bound collection argument's viewed items.
      `reduce(collection, reducer, initial)` processes top-level
      collection elements from left to right.
      `step(element, accumulator)` receives each item exactly as collected
      from the post-binding collection view and the accumulator as ONE value —
      two ordinary callback arguments (THE CALLBACK LAW); nested sequence
      values stay intact, and only the reducer's own explicit pattern opens a
      structured element or accumulator. Each step's result is its ORDINARY
      call result (HO-03, Q-25 resolved October 2026) — the one value the call
      boundary delivers: several rows arrive as one sequence value, `()` and
      `[]` are ordinary values — passed whole, never spread, as the next
      accumulator with its value-boundary count (`reCountValueBoundary`), so
      `reduce([a, b], R, i)` is `R(b, R(a, i))`.

      The initial accumulator is an ordinary VALUE slot (HO-04): binding has
      already demanded it ONCE — a failure there is the call's failure and is
      never retried — so this function receives its value, never an algorithm
      to evaluate again. A callable that cannot supply a zero-argument value was
      rejected at binding (`reduceInitialRejection`). The value occupies one
      written accumulator slot, reified at the ordinary value boundary before
      reduction, so empty collections return the initial accumulator as ONE
      value. -/
  def EvalBody.evalReduceCounted (rec : EvalRec) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec reduceLoop : List CountedResult -> CountedResult -> EvalM CountedResult
      | [], acc => pure acc
      | item :: rest, (accValue, _) => do
          let stepOut <- withCtx
            "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            rec.evalSequenceReduceStepCounted stepAlg item accValue ctx env "reduce step"
          reduceLoop rest (reCountValueBoundary stepOut)
    -- The initial accumulator occupies ONE written accumulator slot: its value
    -- is reified as one persistent value at the ordinary value boundary
    -- (`Result.valueCount`, what `reCountValueBoundary` computes) BEFORE
    -- reduction begins, so an initial expression that emitted multiple items
    -- cannot leak that supply through the empty-collection return.
    reduceLoop collection (initial, Result.valueCount initial)

    /-- Evaluate `filter(collection, predicate)`.
      The fixed `collection` argument supplies the items through the
      post-binding collection view, and `predicate` is a fixed control
      argument. Each iterated item is passed to the predicate exactly as
      collected; nested sequence values and nested
      list values stay intact. The kept items remain the original collection
      items and are materialized as one list value, so keeping
      exactly `(1, 2)` yields `[(1, 2)]`. -/
  def EvalBody.evalFilterCounted (rec : EvalRec) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec filterLoop : Nat -> List CountedResult -> EvalM (List Result)
      | _, [] => pure []
      | index, item :: rest => do
        match <- evalAttempt (withCtx (s!"while evaluating filter predicate for item {index}: {resultDiagnosticString item.fst} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)") <|
          rec.evalSequenceCallbackCall predicateAlg item ctx env "filter predicate") with
          | .error err =>
              .error err
          | .ok pr =>
              -- The predicate must return a Boolean value; a numeric result
              -- (`filter{x}` over numbers) is a value-kind error, never a
              -- nonzero truth test.
              match Result.asBool? pr with
              | some true => do
                  let kept <- filterLoop (index + 1) rest
                  pure (item.fst :: kept)
              | some false =>
                  filterLoop (index + 1) rest
              | none =>
                  .error (Error.typeMismatch
                    (booleanRequiredMessage "filter predicate result" pr))
    let kept <- filterLoop 0 items
    pure (makeCollectionListResult kept)

  /-- Evaluate `map(collection, mapper)`.
      `map` processes top-level collection elements from left to right.
      `transform(element)` receives each item exactly as collected from the
      post-binding collection view; nested sequence values stay intact.
      Each transform result is its ORDINARY call result (HO-03, Q-25 resolved
      October 2026) — the one value the call boundary delivers: several rows
      arrive as one sequence value, `()` and `[]` are ordinary values — and
      becomes ONE element of the list result, never flattened into it, so
      `map(L, F)` is `[F(L[0]), …, F(L[n - 1])]`. Empty collections yield `[]`, and
      the output preserves the original element order and element count. -/
  def EvalBody.evalMapCounted (rec : EvalRec) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec mapLoop : List CountedResult -> EvalM (List Result)
      | [] => pure []
      | item :: rest => do
          let mappedOut <- withCtx
            "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            rec.evalSequenceCallbackCallCounted transformAlg item ctx env "map transform"
          let restMapped <- mapLoop rest
          pure (mappedOut.fst :: restMapped)
    let mapped <- mapLoop collection
    pure (makeCollectionListResult mapped)

    def EvalBody.applyBuiltinCountedSequence (rec : EvalRec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    do
      let bound <- rec.bindSequenceBuiltinArguments b metadata args ctx env
      if let some a := bound.view? then
        return <- rec.evalArgumentViewBuiltin b a
      let withPreparedItems
          (k : List Result -> EvalM CountedResult) : EvalM CountedResult :=
        k bound.preparedInput.items
      let withPreparedNumericItems
          (k : List Int -> EvalM CountedResult) : EvalM CountedResult := do
        k (<- expectPreparedNumericItems b bound.preparedInput)
      let withPreparedSuffixArgs
          (k : List PreparedSequenceBuiltinSuffixArg -> EvalM CountedResult) : EvalM CountedResult :=
        k bound.suffixArgs
        match b with
        | .filterBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              if bound.iterationItems.isEmpty then return makeCollectionListResult []
              let predicateAlg <-
                rec.expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              rec.evalFilterCounted bound.iterationItems predicateAlg ctx env
        | .mapBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              if bound.iterationItems.isEmpty then return makeCollectionListResult []
              let transformAlg <-
                rec.expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              rec.evalMapCounted bound.iterationItems transformAlg ctx env
        | .orderBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalOrderCounted numbers
        | .orderDescBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalOrderDescCounted numbers
        | .countBuiltin =>
            withPreparedItems fun items =>
              evalCountCounted items
        | .containsBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let searched <-
                expectPreparedSequenceBuiltinValueSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalContainsCounted items searched
        | .distinctBuiltin =>
            withPreparedItems fun items =>
              evalDistinctCounted items
        | .firstBuiltin =>
            withPreparedItems fun items =>
              evalFirstCounted items
        | .lastBuiltin =>
            withPreparedItems fun items =>
              evalLastCounted items
        | .takeBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let count <-
                expectPreparedSequenceBuiltinWholeNumberSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalTakeCounted items count
        | .skipBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let count <-
                expectPreparedSequenceBuiltinWholeNumberSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalSkipCounted items count
        | .minBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalMinCounted numbers
        | .maxBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalMaxCounted numbers
        | .sumBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalSumCounted numbers
        | .avgBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalAvgCounted numbers
        | .reduceBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let initial <-
                expectPreparedSequenceBuiltinValueSuffixArg b metadata.suffixArgs preparedSuffixArgs 1
              if bound.iterationItems.isEmpty then return (initial, Result.valueCount initial)
              let stepAlg <-
                rec.expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              rec.evalReduceCounted bound.iterationItems stepAlg initial ctx env
        | _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with counted output shape (a builtin callback's one
      result is already a value, counted by `Result.valueCount`).
      Every VALUE slot (the `if` condition and branches, the
      `repeat` count, `atoms`, `range`) is demanded through
      `evalArgumentValueCounted`, so a parameterized algorithm in a selected slot
      is the ordinary zero-argument arity rejection and never enters its body;
      ALGORITHM slots (loop steps) invoke the argument's CALLABLE projection
      (`invokeNeed`), so a step forwarded through a parameter is the callable
      itself, never its demanded value. A builtin declaring a META parameter (the
      loops) binds through the ONE binder first (META-S3-3); a loop's initial state is
      its captured call's supply, demanded by the step and the final materialization. A missing
      output escaping the application is NESTED (Q-36): a builtin always has output, so it is an
      argument's, a callback's or a step's. -/
  def EvalBody.applyBuiltinCounted (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    withNestedMissingOutput <| match sequenceBuiltinMetadata? b with
    | some metadata =>
      rec.applyBuiltinCountedSequence b metadata args ctx env
    | none =>
      if builtinDeclaresMeta b then do
        -- THE META BINDING OF A BUILTIN (META-S3-3, October 2026): a builtin whose signature
        -- declares a META parameter (`builtinDeclaresMeta`) is an ordinary fixed-arity callable:
        -- its arity gate (before any demand), then its supplied cells bound through THE ONE
        -- inspecting binder over its signature (`bindNeedPatterns`), whose `.metaRef` arm
        -- captures the supplied call exactly as for a user algorithm (`NeedPlan.reference`:
        -- inert; a non-call cell is `metaRefusal`), then its native arm over the bound
        -- environment. Every evaluator route supplies cells; an argument WITHOUT a cell (the
        -- fixture seam) is a VALUE, which META refuses. C#: `Evaluator.ApplyMetaBuiltinCounted`.
        if !builtinAcceptsArity b args.length then throw (builtinArityError b args.length)
        let cells <- args.mapM (fun arg => rec.argumentNeed arg ctx env)
        let some bindings <- bindNeedPatterns (rec.bindingChannels) ((builtinSignature b).map NeedPattern.ofParameter) cells
          | throw Error.badArity
        let bound (name : Ident) : EvalM Nat :=
          match lookupAssoc name bindings with
          | some address => pure address
          | none => throw (Error.illegalInEval s!"unbound builtin parameter {name}")
        -- The captured step's loop (D1, CR-9, CR-13): the reference bound to `meta step` (its
        -- Ready adapter, read without running anything) decoded into its plan; the plan's ONE
        -- sticky supply (`argumentViewCells`: its recorded preparation or exactly one formation,
        -- opening only the explicit spreads written inside the captured call and demanding no
        -- argument VALUE) is the initial state -- the ORIGINAL argument cells, never re-formed;
        -- an empty supply is the ordinary zero-slot state (OD-1) -- and the plan's canonical
        -- callee cell (`NeedPlan.calleeCell`, inert) is the step, projected only when an
        -- iteration runs. The captured call itself is never dispatched.
        let capture : EvalM (ResolvedArgumentAlgorithm × List Nat) := do
          let (stepCell, initialCells) <- metaLoopCapture rec.planRoute.classify rec.demandNeedRecursive rec.argumentViewCells (<- bound "step")
          pure ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some stepCell }, initialCells)
        match b, args with
        | .whileBuiltin, _ => do
            let (step, initialCells) <- capture
            let stepName <- loopStepName "while" step
            -- One condition-first round per iteration (LOOP-06, `WhileRound.advance`): a false
            -- verdict finishes with the cells that entered the round (R1: zero accepted
            -- transitions return the initial cells), materialized below (LOOP-07).
            let finalCells <- rec.whileLoop step ctx env stepName initialCells
            let finalSlots <- finalCells.mapM (fun address => Prod.fst <$> rec.demandNeedRecursive address)
            pure (loopResultCounted finalSlots)
        | .repeatBuiltin, [_, countAlg] => do
            -- RP-1: capture, then the captured supply, THEN the count -- the outer call's own
            -- VALUE argument, demanded and validated once -- so a captured spread's failure or
            -- effect precedes the count's, as LOOP-01/05 ordered it before META-S3-3.
            let ((step, initialCells), n) <- metaRepeatSetup capture (do
              expectInt (<- rec.evalArgumentValue { countAlg with need? := some (<- bound "count") } ctx env))
            if n < 0 then
              .error (Error.illegalInEval "Repeat count must be >= 0")
            else
              let stepName <- loopStepName "repeat" step
              let rec repeatLoop : Nat → List Nat → EvalM (List Nat)
                | 0, cells => pure cells
                | remaining + 1, cells => do
                  let algorithm <- projectInvokingSlot (invokingSlotRole .repeatBuiltin) (<- rec.invokeNeed step)
                  let outputSlots <- rec.runNeedStepSlots algorithm ctx env cells stepName
                  let next <- outputSlots.mapM (fun value => readyNeed (value, Result.valueCount value))
                  repeatLoop remaining next
              let finalCells <- repeatLoop n.toNat initialCells
              let finalSlots <- finalCells.mapM (fun address => Prod.fst <$> rec.demandNeedRecursive address)
              pure (loopResultCounted finalSlots)
        | _, _ => .error (builtinArityError b args.length)
      else
        match b, args with
        | .ifBuiltin, [c,t,e] => do
            let cr <- rec.evalArgumentValue c ctx env
            -- The selected branch is one argument expression, so `if` observes it
            -- as a single value boundary -- exactly like value-position property
            -- access. A multi-output branch property such as `X = 1, 2, 3`
            -- therefore yields the grouped sequence value `(1, 2, 3)` with emitted
            -- count 1, not three separate outputs; explicit spread opens it.
            -- `if` re-counts the chosen branch value via `Result.valueCount`,
            -- exactly as a completed `while`/`repeat` re-counts its final state
            -- (`loopResultCounted`).
            -- The condition must be a Boolean value: `if(1, a, b)` is a
            -- value-kind error, not a truth test.
            match Result.asBool? cr with
            | some false => do
                let r <- rec.evalArgumentValueCounted e ctx env
                pure (r.fst, Result.valueCount r.fst)
            | some true => do
                let r <- rec.evalArgumentValueCounted t ctx env
                pure (r.fst, Result.valueCount r.fst)
            | none => .error (Error.typeMismatch (booleanRequiredMessage "if condition" cr))

        | .atomsBuiltin, [a] => do
            let r <- rec.evalArgumentValue a ctx env
            -- An argument view has no atoms to collect without materializing it (S2).
            if let .argView _ := r then
              .error (Error.typeMismatch (argumentViewUnsupportedMessage "atoms"))
            -- `atoms` materializes a collection: one list of
            -- the recursively collected numeric atoms (sequence AND list
            -- boundaries open; strings and Boolean values contribute none).
            pure (makeCollectionListResult ((Result.languageAtoms r).map Result.atom))

        | .rangeBuiltin, [startAlg, stopAlg] => do
            let start <- expectInt (<- rec.evalArgumentValue startAlg ctx env)
            let stop <- expectInt (<- rec.evalArgumentValue stopAlg ctx env)
            let xs := inclusiveRange start stop
            -- `range` materializes a collection: one list value.
            pure (makeCollectionListResult (xs.map Result.atom))

        | _, _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with plain Result output.
      This is the Result projection of `applyBuiltinCounted`: the counted twin
      owns the builtin dispatch and semantics, and the non-counted path only
      discards the emitted-count metadata. The CoreTests builtin projection
      parity guards pin this equivalence (values, error diagnostics, and
      evaluator state) case by case. -/
  def EvalBody.applyBuiltin (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.applyBuiltinCounted b args ctx env
    pure out.fst

  /-- The builtin application of a resolved call and of a builtin loop step (C#:
      `ApplyBuiltinCountedResolved`, the ONE builtin dispatch switch, which a builtin
      callback reaches too; Lean's callback route calls `applyBuiltinCounted`
      directly): `applyBuiltinCounted` over the arguments as received — supplied
      cells, a call's explicit spreads already opened at supply formation
      (`formNeedSupplySourced`). *(Until 2026-10-13 it first expanded spread-marked
      arguments, which no evaluator-built argument had been since Model C; only
      CoreTests fixtures wrote them.)* -/
  def EvalBody.applyBuiltinCountedResolved (rec : EvalRec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    rec.applyBuiltinCounted b args ctx env

  def EvalBody.evalExplicitSequenceValueItems (rec : EvalRec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) := do
    match a with
    | .builtin b => do
        let out <- evalBuiltinValueCounted b
        pure (countedTopLevelValues out)
    | _ =>
      match a.findDuplicatePropName with
      | some n => .error (Error.duplicateProperty n)
      | none =>
        match conditionalValueAccessError? "conditional" a with
        | some err => .error err
        | none => pure ()
        match a with
        | .mk _ _ _ _ [] _ => .error (Error.missingOutput .own)
        | _ => pure ()
        let pushedCtx <- enterAlgorithmBody a ctx env
        rec.evalExplicitSequenceValueRowSlots (Algorithm.output a) pushedCtx env

  /-- The shared written-slot loop over ordered bundle rows: each row
      contributes its explicit written slots. Algorithm-shaped groupings reach
      it after pushing their own scope; a `Expr.capture` body reaches it
      directly (captures own no scope).
      C#: `EvalExplicitSequenceValueRowSlots`. -/
  def EvalBody.evalExplicitSequenceValueRowSlots (rec : EvalRec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM (List Result) := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          -- A row is a SUBORDINATE computation of the body or capture (Q-36).
          let values <- withNestedMissingOutput (rec.evalExplicitSequenceValueExprSlots e rowCtx env)
          collect rest (values.reverse ++ acc)
    collect rows []

  def EvalBody.evalExplicitSequenceValueExprSlots (rec : EvalRec) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) := do
    match expr with
    -- A nested capture or zero-parameter block materializes exactly one item, combined
    -- with the same shallow singleton-erasing rule as ordinary capture
    -- evaluation (`combineOutputSlots`). A host-built single-row capture IS
    -- its already-evaluated item (source `(A)` is erased to `A` by the parser),
    -- and an all-spread-empty capture is `()`, never an orphan such as `(5)`.
    -- This is list-element reification, not an extra pattern-argument view.
    | .capture rows => do
        let items <- rec.evalExplicitSequenceValueRowSlots rows ctx env
        pure [combineOutputSlots items]
    | .algorithmExpr algorithm => do
        let wired := wireToCaller ctx algorithm
        -- Only a plain-output algorithm can take the written-slot fast path. A
        -- captureless pattern still consumes a slot; a family must dispatch.
        let plainOutput := match wired with
          | .conditional _ _ _ _ => false
          -- A callable alias is no output to unfold: it is demanded as its target.
          | .alias _ _ _ _ _ _ => false
          | _ => (Algorithm.parameterPatterns wired).isEmpty
        if plainOutput then
          let items <- rec.evalExplicitSequenceValueItems wired ctx env
          pure [combineOutputSlots items]
        else
          let out <- rec.evalCounted expr ctx env
          pure [out.fst]
    | .sequenceSpread _ =>
        let out <- rec.evalCounted expr ctx env
        pure (countedTopLevelValues out)
    | _ =>
        let out <- rec.evalCounted expr ctx env
        -- WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        -- written slot contributes exactly ONE persistent value — the value
        -- its counted supply denotes — regardless of how many items the
        -- expression emitted (zero, one, or many). Only an explicit spread
        -- supplies the value's items into the surrounding item slots.
        pure [out.fst]

  /-- Ordinary calls form a demandable supply in the caller's context, check its
      cardinality, bind through the common inspecting-pattern engine and then
      execute the body. Plain binders transport cells without forcing VALUE.
      The public result remains the ordinary recounted value boundary. -/
  def EvalBody.evalUserCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env args
    rec.evalNeedUserSupply callee cells ctx env

  /-- Counted conditional call evaluation — the CANONICAL conditional-call
      implementation (`evalConditionalCall` is its value projection).
      1. Assemble the argument supply through the shared call argument
         pipeline (explicit spread expands into ordinary argument slots
         BEFORE clause matching, so a multi-clause callee sees the same
         supply as every other callable shape).
      2. Try branches in order; first match wins.
      3. Evaluate the selected branch body with pattern bindings prepended.
      4. If no branch matches, raise noMatchingBranch.

      **Full-input-specification rule**: the branch body receives its input
      bindings ONLY from the matched pattern. No extra implicit parameters are
      inferred from free identifiers in the body; they must resolve through
      ordinary lexical / property / open / builtin lookup or fail with
      unknownName.

      **Assumes uniform output arity**: after validation
      (validateBranchOutputArities), all branches produce the same top-level
      output arity; the evaluator does not re-check this at runtime.

      The selected branch is a value boundary, so its public result re-counts
      the emitted arity to `Result.valueCount` (via `reCountValueBoundary`) --
      a multi-output branch becomes one sequence value (count 1), matching
      `if` and plain calls. -/
  def EvalBody.evalConditionalCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult := do
    let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env args
    rec.evalNeedFamilySupply callee cells ctx env calleeName

  /-- Dispatch an already-resolved callee with plain Result output.
      This is the Result projection of `evalResolvedCallCounted`: the counted
      twin owns the builtin/flat-binder/conditional/user dispatch, and each of
      its arms already ends in a projected family, so the projection is
      compositional. -/
  def EvalBody.evalResolvedCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result := do
    let out <- rec.evalResolvedCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Dispatch an already-resolved callee in counted evaluation — the
      CANONICAL resolved-callee dispatch (`evalResolvedCall` is its value
      projection). -/
  def EvalBody.evalResolvedCallCounted (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") (origin : CalleeOrigin := .none) : EvalM CountedResult := do
    match callee with
    -- The dispatch safety net: a callee that reached dispatch as an unnormalized alias (a
    -- host-built tree) calls its target with the same written arguments. Every binding lookup
    -- normalizes first. C#: `EvalAliasCallCounted`.
    | .alias _ _ _ _ _ _ => do
      let target <- rec.resolveAliasTarget callee ctx
      rec.evalResolvedCallCounted target args ctx env calleeName origin
    | _ => do
      -- Every callee receives the ordinary supply cells, each with its WRITTEN source (C#:
      -- `ResolveArgAlgsWithSequenceSpread` → `ResolveNeedSupply`), then the ONE dispatch.
      -- (The user and family arms formerly formed the address projection of the same supply
      -- inside `evalUserCallCounted` / `evalConditionalCallCounted`: the same operations.)
      let cells <- NeedSupply.form rec.evalSupplySpread ctx env args
      rec.evalSuppliedCallCounted origin callee cells ctx env calleeName

  /-- Context-aware counted call evaluation for expression position — the
      CANONICAL expression-position call dispatch (`evalCallExpr` is its value
      projection); attaches `CtxMsg.call` to resolution and dispatch errors.
      The callee is resolved by `resolveCalleeAlg` (DOT-09). -/
  def EvalBody.evalCallCountedExpr (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    -- META-S3-1: a callee written `X.Algorithm` is the call-reference intrinsic on a structural miss
    -- (`algorithmCalleeOf`); a declared member `Algorithm` keeps the ONE callee law.
    if let some (receiver, _) := linkEdge? f then
      if <- withCtx (CtxMsg.call f) (rec.algorithmIntrinsicRoute receiver ctx) then
        let (callee, calleeName, calleeCell) <- withCtx (CtxMsg.call f) (rec.algorithmCalleeOf receiver ctx env)
        return <- withCtx (CtxMsg.call f) <| rec.evalResolvedCallCounted callee args ctx env calleeName (.cell calleeCell)
    let callee <- withCtx (CtxMsg.call f) <| rec.resolveCalleeAlg f ctx
    withCtx (CtxMsg.call f) <| rec.evalResolvedCallCounted callee args ctx env (openExprName f) (.written f ctx)

  /-- Counted extension-call fallback: DOT-CALL PASSES A VALUE (September
      2026). `R.F(args)` resolves the callee and dispatches exactly
      `F(R, args)` — the receiver expression becomes the ordinary FIRST
      written argument slot of the ONE shared call assembly
      (`prepareLexicalDotCallArgs` + `evalResolvedCallCounted`), so every
      callable shape (builtin, flat, collecting, patterned, clause family)
      binds, demands, caches, orders, charges, and rejects the receiver
      exactly as it would that written argument: a builtin's `collection`
      slot demands a named receiver through the zero-argument value-demand law
      like `count(A)` does, a collecting parameter collects the receiver as
      one item (`(1, 2).Coll` is `[(1, 2)]`, `().Coll` is `[()]`), and only a
      spread receiver — the fluent `R*.F` form, which the parser lowers to
      `F(R*)` — opens a boundary. There is no dotted receiver view, no raw
      receiver supply, and no builtin-specific receiver placement.

      The STORED lexical-fallback identity decides the callee channel — the
      front-end's Param-vs-Resolve decision is CONSUMED here, never
      reconstructed from runtime environments: a `.resolve` fallback takes the
      ordinary name-based path, and any other fallback (normally `.param`)
      resolves through canonical `resolveAlg`, so a parameter shadows a
      same-name builtin exactly as in plain-call position. Non-name hand-built
      fallbacks are outside the post-elaboration contract and follow their
      ordinary `resolveAlg` behavior defensively.
      C#: `CallLexicalWithReceiverCounted`. -/
  def EvalBody.callLexicalWithReceiverCounted (rec : EvalRec) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let combinedArgs := prepareLexicalDotCallArgs receiver extraArgs
    match fallback with
    | .resolve fallbackName =>
      let callee <- rec.resolveAlg (.resolve fallbackName) ctx
      rec.evalResolvedCallCounted callee combinedArgs ctx env fallbackName
    | other =>
      let callee <- rec.resolveAlg other ctx
      rec.evalResolvedCallCounted callee combinedArgs ctx env name

  /-- The `.string` intrinsic is a ZERO-parameter member. A written argument
      list is formed exactly like every call's supply (`formNeedSupply`:
      explicit spreads are opened, every other slot stays a suspended need)
      and then rejected by its cardinality before any argument, or the
      receiver, is demanded — the same outcome as `Obj.V(1)` for a declared
      zero-parameter member — so a written bundle is never silently dropped;
      an EMPTY written list (`x.string()`), or one whose spreads supply no
      item, stays the intrinsic, as `A()` stays a call of `A`.
      C#: `RejectDotStringIntrinsicArguments`. -/
  def EvalBody.rejectDotStringIntrinsicArguments (rec : EvalRec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit := do
    match argsOpt with
    | none => pure ()
    | some args =>
      let items <- NeedSupply.addresses rec.evalSupplySpread ctx env args
      if items.length = 0 then pure ()
      else .error (Error.arityMismatch 0 items.length)

  /-- The VALUE the ordinary-dot `string` intrinsic converts, demanded after the
      zero-argument value-demand law accepted the resolved receiver — or, for a
      parameter bound to a supplied cell, without consulting the law
      (`hasSuppliedParameterCell`), since that cell's demand reports exactly what
      the written argument raises (CALL-06). HOW A
      PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING, so the intrinsic reads
      its receiver exactly as a value position reads it:
      * a lexical property reference `A` is read through the zero-argument
        property access of its resolved binding (the run cache), so `A.string`
        converts the very value `A` reads;
      * a structurally navigated member `Obj.A` is read through the structural
        property access of the member it selects, so `Obj.A.string` converts the
        very value `Obj.A` reads;
      * a parameter is the ordinary value-position parameter read — its bound
        value, or the failure its argument slot established — so a forwarded
        property value is never re-run through the parameter's algorithm channel
        (`F(v) = v.string` converts the value `F(A)` passed);
      * every other receiver shape (a written block, a capture, a dot result) is
        its resolved algorithm's zero-argument demand, as before.
      The receiver is a SUBORDINATE computation of the intrinsic, so a missing output it fails
      with is nested (Q-36); every intrinsic's value-receiver read (`eval target`) is too.
      C#: `EvalDotStringReceiverAlgOutput`. -/
  def EvalBody.evalDotStringReceiverValue (rec : EvalRec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    withNestedMissingOutput do
      match target with
      | .resolve n =>
          match ctx.callStack with
          | owner :: _ => do
              -- A receiver reached THROUGH an alias reads its VALUE terminal, a missing output named as
              -- that terminal binding's (exactly what its former row read reported); a direct binding is
              -- its own cached access, framed by the dot edge alone.
              let resolved <- lookupLexicalPropertyRaw owner n ctx
              match resolved.alg with
              | .alias _ _ _ _ _ _ =>
                  let counted <- EvalBody.terminalAccess rec (<- rec.resolveAliasValueTarget resolved.alg ctx) ctx env
                  pure counted.fst
              | _ =>
                  let counted <- rec.evalZeroArgPropertyAccessCounted .lexical resolved.owner resolved.binding resolved.alg ctx env
                  pure counted.fst
          | [] => rec.evalZeroArgumentDemandOutput targetAlg ctx env
      | .param _ => rec.eval target ctx env
      | .dotMember receiver member _ none =>
          -- The same navigation `resolveDotReceiver` just performed (a `string` step
          -- included, Q-17 S-C): a member the container DECLARES is the selected
          -- structural binding (its accessibility was already enforced there);
          -- anything else is a dot result.
          match <- evalAttempt (rec.resolveDotReceiver receiver ctx) with
          | .ok container =>
              match Algorithm.lookupPropDefAny? container member with
              | some p =>
                  match childOfInContext container p.alg ctx with
                  -- A member that is an alias reads its VALUE terminal (OD-E, M4★).
                  | wired@(.alias _ _ _ _ _ _) =>
                      let counted <- EvalBody.terminalAccess rec (<- rec.resolveAliasValueTarget wired ctx) ctx env
                      pure counted.fst
                  | _ =>
                      let accessed := (flatBinderUserEquivalent? targetAlg).getD targetAlg
                      let counted <- rec.evalZeroArgPropertyAccessCounted .structural container p accessed ctx env
                      pure counted.fst
              | none => rec.evalZeroArgumentDemandOutput targetAlg ctx env
          | .error _ => rec.evalZeroArgumentDemandOutput targetAlg ctx env
      | _ => rec.evalZeroArgumentDemandOutput targetAlg ctx env

  /-- Evaluate dotCall: a.f or a.f(args). The member result is a value boundary:
      structural zero-arg property access and collection builtins re-count to
      `Result.valueCount`, and user/lexical member calls re-count via
      `evalUserCallCounted`, so a multi-output member becomes one sequence value
      (count 1) and only a caller-site spread `value*` re-spreads
      it. This is the single owner
      of dot-call dispatch; `evalDotCall` is its Result projection.
      The ROUTE is decided first, member-first at every edge (DOT-01; Q-17 S-C):
      - Receiver resolution through `resolveDotReceiver`: a chained receiver
        navigates its declared structural members, so the property-first
        rule below holds at every level of `A.B.C.D`
      - ONE structural lookup of the member (a member named `string` included):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - A branch-only member → `localOnlyProperty`
      - A structural MISS takes the edge's miss route:
        - "string" → the value intrinsic: evaluate the receiver, convert its
          numeric value to text (a lexical `string` is never consulted)
        - otherwise → extension fallback (`callLexicalWithReceiverCounted`):
          DOT-CALL PASSES A VALUE — `a.f(args)` is exactly the call
          `f(a, args)`, the receiver being the ordinary first argument slot
          (never a supply of its own; only the spread receiver `a*.f`, lowered
          to `f(a*)`, opens a boundary).
        Dot resolution therefore has three classes — structural member access,
        the intrinsic `.string`, and extension fallback — and only the
        extension call injects the receiver.

      When receiver resolution returns notAnAlgorithm (a value receiver, e.g. a
      numeric literal), there is no member to select: the miss route applies
      directly.

      (The C# front end consumes the Grace annotation in `a~.f` / `a.~f`, so
      Lean receives the same dotMember and the same structural-first dispatch
      as for ordinary `a.f`.)

      A structurally navigated zero-argument member read goes through the
      zero-argument property access of the member's binding (the run cache,
      `evalZeroArgPropertyAccessCounted`), exactly like the lexical read of the
      same binding; an explicit member call `Obj.A()` does not. -/
  def EvalBody.evalDotCallCounted (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    -- The receiver's TYPED identity (META-S3-1, L2): `none` is a value receiver; a failure — a
    -- parameter cell's runtime projection failure of any kind included — propagates.
    let targetAlg? <- rec.resolveDotReceiver? target ctx
    -- ONE structural lookup decides the route, whatever the member's spelling (`selectDotEdge`,
    -- META-S3-4: the same decision an invocation plan's route takes): a declared member wins (a
    -- member named `string` included — Q-17 S-C), its accessibility from THIS site is decided
    -- afterwards, a branch-only member is the local-only error, and only a structural MISS (a
    -- value receiver declares no member) takes the miss route.
    match selectDotEdge ctx target name targetAlg? with
    | .error err => throw err
    | .ok (.member targetAlg p) => do
        -- A member that is an alias is read through its VALUE terminal and called through its
        -- INVOCATION target (OD-E, M4★; C#: `EvalAliasMemberCounted`): a read uses the TERMINAL
        -- binding's zero-argument entry (or a runtime alias's binding cell), never one of its own; a
        -- call publishes under the target's origin (`.bound` → `aliasOriginBinding?`).
        match argsOpt with
        | none =>
            match <- rec.resolveAliasValueTarget (childOfInContext targetAlg p.alg ctx) ctx with
            | terminal@(.runtime _ _) => reCountValueBoundary <$> EvalBody.terminalAccess rec terminal ctx env
            | terminal =>
              let wired := terminal.alg
              -- A structurally navigated member read with NO argument list is an
              -- ordinary zero-argument value demand, so the ONE law decides
              -- (`acceptsZeroArgumentValueDemand`) and the rejection names the
              -- member's true minimum supply (`minimumSuppliedSlots`), never its
              -- flattened declared capture count. The read is the TERMINAL binding's (the
              -- member's own when it is no alias), and a read crossing a carrier is nested (Q-36).
              match flatBinderUserEquivalent? wired with
              | some simple =>
                  if acceptsZeroArgumentValueDemand simple then
                    reCountValueBoundary <$> withMissingOutputNesting terminal.nested
                      (rec.evalZeroArgPropertyAccessCounted .structural (terminal.ownerOr targetAlg) (terminal.bindingOr p) simple ctx env)
                  else
                    .error (Error.arityMismatch
                      (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns simple)) 0)
              | none =>
                  if acceptsZeroArgumentValueDemand wired then
                    reCountValueBoundary <$> withMissingOutputNesting terminal.nested
                      (rec.evalZeroArgPropertyAccessCounted .structural (terminal.ownerOr targetAlg) (terminal.bindingOr p) wired ctx env)
                  else
                    match wired with
                    | .conditional _ _ _ _ => .error (Error.noMatchingBranch name)
                    | _ =>
                        .error (Error.arityMismatch
                          (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns wired)) 0)
        | some args =>
            rec.evalResolvedCallCounted (<- rec.resolveAliasTarget (childOfInContext targetAlg p.alg ctx) ctx) args ctx env name (.bound targetAlg p)
    | .ok (.miss .string) =>
        -- `string` is the number-to-text intrinsic (DOT-08) — it takes the extension call's
        -- place, so a lexical `string` is never consulted.
        -- The intrinsic is a ZERO-parameter member: a written argument list is
        -- formed like every call's supply (explicit spreads opened, every other
        -- slot a suspended need) and rejected by its cardinality before any
        -- argument or the receiver is demanded, exactly as `Obj.V(1)` is for a
        -- declared zero-parameter member; `x.string()` (an empty list) stays the
        -- intrinsic.
        -- C#: `RejectDotStringIntrinsicArguments`.
        match targetAlg? with
        | some targetAlg => do
          rec.rejectDotStringIntrinsicArguments argsOpt ctx env
          -- A receiver that is an alias is demanded as its VALUE terminal (OD-E, M4★; C#:
          -- `EvalAliasDotStringCounted`; the VALUE chase): the law below is judged on the terminal's
          -- algorithm, while the read keeps the alias, so every shape reads the TERMINAL binding's
          -- cached entry (an inline carrier through the demand funnel's alias arm).
          let valueAlg := (<- rec.resolveAliasValueTarget targetAlg ctx).alg
          -- The receiver is demanded for its VALUE with zero arguments. A PARAMETER
          -- bound to a supplied cell is a VALUE demand of that cell (CALL-06): the
          -- first demand evaluates the written argument once, and its outcome is
          -- reported exactly as that argument reports it, as every other read of the
          -- parameter reports it — `Show(v) = v.string` / `Show(Inc)` is Inc's
          -- property-context arity error, `Show({ x + 1 })` the block's
          -- `unresolvedImplicitParams`, a clause family its own `noMatchingBranch` —
          -- never a report re-judged against the parameter's callable. Every other
          -- receiver is judged by the ONE zero-argument demand law from the resolved
          -- receiver's signature before its body is entered: `Inc.string` with
          -- `Inc(x)` is the property arity error, a navigated parameterized member the
          -- bare one, and a written parameterized block `unresolvedImplicitParams`.
          -- The receiver is then READ like a value position reads it
          -- (`evalDotStringReceiverValue`): a named property through its cached
          -- property access, a parameter through its bound value.
          -- C#: `EvalDotStringReceiverAlgOutput`.
          if !(<- hasSuppliedParameterCell target ctx env) then
            match zeroArgumentDemandError? (some target) valueAlg with
            | some err => .error err
            | none => pure ()
          let val <- rec.evalDotStringReceiverValue target targetAlg ctx env
          let out <- resultToString val
          pure (out, Result.valueCount out)
        | none => do
          rec.rejectDotStringIntrinsicArguments argsOpt ctx env
          let val <- withNestedMissingOutput (rec.eval target ctx env)
          let out <- resultToString val
          pure (out, Result.valueCount out)
    | .ok (.miss .invoke) =>
        -- `Invoke` is the call-reference intrinsic (CallReference S1, J1) — it takes the
        -- extension call's place, so a lexical `Invoke` is never consulted. The argument list
        -- is a route fact checked BEFORE the receiver is demanded: a bare `R.Invoke` is
        -- refused, a non-empty list is the zero-parameter cardinality rejection. The receiver
        -- is then read exactly as the `string` intrinsic reads it (alias target, the
        -- zero-argument demand law, the ordinary value read) and must be a call reference.
        match targetAlg? with
        | some targetAlg => do
          rec.rejectInvokeIntrinsicArguments argsOpt ctx env
          let valueAlg := (<- rec.resolveAliasValueTarget targetAlg ctx).alg
          if !(<- hasSuppliedParameterCell target ctx env) then
            match zeroArgumentDemandError? (some target) valueAlg with
            | some err => .error err
            | none => pure ()
          let val <- rec.evalDotStringReceiverValue target targetAlg ctx env
          rec.invokeCallReferenceValue val
        | none => do
          rec.rejectInvokeIntrinsicArguments argsOpt ctx env
          let val <- withNestedMissingOutput (rec.eval target ctx env)
          rec.invokeCallReferenceValue val
    | .ok (.miss .arguments) =>
        -- `Arguments` is the call-reference ARGUMENT VIEW intrinsic (CallReference S2) — it
        -- takes the extension call's place, so a lexical `Arguments` is never consulted. A
        -- written argument list is refused as a route fact before the receiver is demanded;
        -- the receiver is read exactly as the `Invoke` intrinsic reads it and must be a call
        -- reference. Nothing else runs.
        match targetAlg? with
        | some targetAlg => do
          rejectArgumentsIntrinsicArguments argsOpt
          let valueAlg := (<- rec.resolveAliasValueTarget targetAlg ctx).alg
          if !(<- hasSuppliedParameterCell target ctx env) then
            match zeroArgumentDemandError? (some target) valueAlg with
            | some err => .error err
            | none => pure ()
          let val <- rec.evalDotStringReceiverValue target targetAlg ctx env
          argumentsOfValue val
        | none => do
          rejectArgumentsIntrinsicArguments argsOpt
          let val <- withNestedMissingOutput (rec.eval target ctx env)
          argumentsOfValue val
    | .ok (.miss .algorithm) =>
        -- `Algorithm` is the callable-projection intrinsic (META-S3-1, CR-14) — it takes the
        -- extension call's place, so a lexical `Algorithm` is never consulted. The receiver is
        -- read exactly as the `Invoke` intrinsic reads it; bare, the edge is the captured
        -- callee's VALUE, with arguments a fresh call of it.
        match targetAlg? with
        | some targetAlg => do
          let val <- rec.referenceReceiverValue target targetAlg ctx env
          rec.algorithmOfValue val argsOpt ctx env
        | none => do
          let val <- withNestedMissingOutput (rec.eval target ctx env)
          rec.algorithmOfValue val argsOpt ctx env
    | .ok (.miss .extension) =>
        rec.callLexicalWithReceiverCounted name target fallback argsOpt ctx env

  /-- The argument-list route fact of the `Invoke` intrinsic (CallReference S1): `R.Invoke`
      without a list is refused (`invokeRequiresArgumentListMessage`) — the intrinsic is never
      a property read and never executes implicitly — and a written list must supply nothing,
      formed and rejected exactly as for the `string` intrinsic (`R.Invoke(8)` is
      `arityMismatch 0 1`: S1 has no replacement arguments). Nothing is demanded.
      C#: `RejectDotInvokeIntrinsicArguments`. -/
  def EvalBody.rejectInvokeIntrinsicArguments (rec : EvalRec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit := do
    match argsOpt with
    | none => .error (Error.illegalInEval invokeRequiresArgumentListMessage)
    | some _ => rec.rejectDotStringIntrinsicArguments argsOpt ctx env

  /-- `R.Invoke()` over the receiver's VALUE (CallReference S1): a call reference executes
      its plan afresh through the production plan route (`NeedPlan.invoke` with the route
      `demandNeedRecursive` installs — exactly `invokeNeedCall`), over the plan's one prepared
      supply, never reading or writing the original cell's VALUE; any other value is the
      intrinsic's kind rejection. C#: `InvokeCallReferenceValue`. -/
  def EvalBody.invokeCallReferenceValue (rec : EvalRec) (val : Result) : EvalM CountedResult :=
    match val with
    | .callRef a =>
        NeedPlan.invoke
          rec.planRoute ⟨a⟩
    | other => .error (Error.typeMismatch (invokeRequiresCallReferenceMessage other))

  /-- The cells of argument view `a` (CallReference S2): the plan's ONE sticky supply
      (`NeedPlan.viewCells` over the production spread capability). C#: `PrepareArgumentView`. -/
  def EvalBody.argumentViewCells (rec : EvalRec) (a : Nat) : EvalM (List NeedSupply.Sourced) :=
    NeedPlan.viewCells rec.evalSupplySpread rec.planRoute.classify a

  /-- `count`/`first`/`last` over argument view `a` at the production capabilities
      (`argumentViewBuiltin`). -/
  def EvalBody.evalArgumentViewBuiltin (rec : EvalRec) (b : Builtin) (a : Nat) : EvalM CountedResult :=
    argumentViewBuiltin (rec.argumentViewCells a) (fun cell => Prod.fst <$> rec.demandNeedRecursive cell) b

  /-- Evaluate a spread operand and supply its immediate items. A failed operand
      is reported by `spreadOperandFailure` (Q-36, decided 2026-10-24) on EVERY
      operand shape — the direct `.algorithmExpr`/`.capture` specializations
      decide exactly like the generic arm: the operand's OWN missing output is
      `spreadMissingOutput`, so `{A = 1}*` and `X = {A = 1}` / `X*` agree, while a
      missing output NESTED in the operand's evaluation (`H = G + 1` / `H*`,
      `F({})*`, `{ G }*`, `[G]*`) keeps its category, cause and blame. The
      decision reads the completed failure's origin only: it evaluates nothing.
      Its argument is the spread's PEELED operand
      (`evalSequenceSpreadCounted` is its one caller): a consumer holding a whole
      spread EXPRESSION reads its items through `evalCounted` +
      `countedTopLevelValues` (the output-row loop, written-slot reification, supply
      formation, the internal join), since handing it the spread node itself would
      spread the spread's captured value again — one boundary too many.
      C#: `EvalSequenceSpreadOperandValue`. -/
  def EvalBody.evalSequenceSpreadOperandValue (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    match e with
    | .capture rows =>
        match <- evalAttempt (rec.evalCaptureValue rows ctx env) with
        | .ok value =>
            pure value
        | .error err =>
            .error (spreadOperandFailure e err)
    | .algorithmExpr a => do
        -- An inline alias block is demanded as its VALUE terminal (OD-E, M4★), a rejection reported
        -- as its written target reference (FA-OQ-1; C#: `EvalAliasSpreadOperandValue`); a chain
        -- reaching a runtime-target alias reads that alias's binding cell (META-S3-2).
        let terminal <- rec.resolveAliasValueTarget (wireToCaller ctx a) ctx
        -- A spread operand is demanded for its VALUE with zero arguments, so the
        -- ONE law decides and shapes its report here too: a block whose parameter
        -- list accepts an empty supply is demanded through the shared funnel.
        match terminal.demandError? e with
        | some err => .error err
        | none =>
          match <- evalAttempt (EvalBody.terminalAccess rec terminal ctx env) with
          | .ok value =>
              pure value.fst
          | .error err =>
              .error (spreadOperandFailure e err)
    | _ =>
        match <- evalAttempt (rec.eval e ctx env) with
        | .ok value =>
            pure value
        | .error err =>
            .error (spreadOperandFailure e err)

    /-- Evaluate a unary `sequenceSpread` node by evaluating its single operand
      once and spreading immediate top-level items. Nested sequence-value
      members are not recursively flattened. Directly-nested spreads (`A**`)
      are unwrapped iteratively (`peelSequenceSpreadLayers`, stack-safe for deep
      nesting), the operand is evaluated ONCE, and then each further written
      layer is applied COMPOSITIONALLY by the total checked opening `openSpreadItems`
      (`reopenSpreadLayers` wherever no opening exposes an argument view): every
      written `sequenceSpread` layer opens exactly one boundary of the value
      the previous layer's supply re-captures (`reopenSpreadItems`), so `A**`
      agrees with `(A*)*`.
      For sequence values
      the extra layers are fixed points (value-equivalent to a single spread);
      a singleton-list chain opens one list boundary per layer
      (`[[7]]**` supplies `7`), while a multi-element list re-captures as
      a sequence after the first layer and then stays fixed
      (`[[1, 2], [3, 4]]**` supplies the two inner lists unchanged). The
      post-evaluation operation is total and its laws are theorems
      (`KatLangArityLaws.lean` § Repeated spread over the real model); that this
      body evaluates the operand once and applies it is a kernel term of the total core
      (R7), pinned by CoreTests `RepeatedSpread`. -/
  def EvalBody.evalSequenceSpreadCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let (operand, layers) := peelSequenceSpreadLayers e 0
    let value <- rec.evalSequenceSpreadOperandValue operand ctx env
    -- The written stars open the operand VALUE one boundary each (`reopenSpreadLayers`); a
    -- star that would open an argument view into values is refused (`openSpreadItems`, S2).
    let supplied <- openSpreadItems (layers - 1) value
    pure (spreadSupplyResult supplied)

  /-- THE SPREAD CAPABILITY OF SUPPLY FORMATION (CallReference S2; `NeedSupply.SpreadEval`): what
      a COMPUTED explicit spread slot `e` of an argument or selector supply contributes. The
      operand is evaluated ONCE, exactly as `evalSequenceSpreadCounted` evaluates it, and its
      stars open it exactly as there (`openSupplySpread`): the spread's top-level items, as the
      supply read them before S2 (`countedTopLevelValues` of the spread's counted result), each
      of which becomes one Ready cell — except that when its LAST star opens an ARGUMENT VIEW,
      the slot contributes that view's ORIGINAL cells (`argumentViewCells`: the plan's one
      sticky preparation), each with its own written source (`needWrittenSource?`, as a
      collecting parameter's transported slice), and demands none of them.
      C#: `Evaluator.FormSpreadSupplySlot`. -/
  def EvalBody.evalSupplySpread (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM SpreadSupply := do
    let (operand, layers) := peelSequenceSpreadLayers e 0
    let value <- rec.evalSequenceSpreadOperandValue operand ctx env
    match <- openSupplySpread (layers - 1) value with
    | .items supplied => pure (.items (countedTopLevelValues (spreadSupplyResult supplied)))
    | .view a => NeedPlan.viewSupply rec.evalSupplySpread rec.planRoute.classify a

  /-- Evaluate a surface list literal `[e1, ..., en]` as exactly ONE exact
      immutable list value. Element slots reuse the written-parentheses
      expression-list slot rules (`evalExplicitSequenceValueExprSlots`): an
      explicit spread slot opens its operand's immediate items into the list
      being constructed (an empty spread contributes no elements), a non-spread
      slot is one element even when it evaluates to the empty sequence value
      `()`, and a nested multi-slot capture or zero-parameter `algorithmExpr` is one element
      (its own rows combined to one value).
      Unlike sequence construction the collected elements are stored EXACTLY:
      no singleton erasure and no empty-nesting collapse, so `[7]`, `[[7]]`,
      `[]`, and `[()]` are all distinct list values. A list literal always
      emits one value. C#: `EvalListLiteralCounted`; plain `eval` is this
      function's value projection on both sides. -/
  def EvalBody.evalListLiteralCounted (rec : EvalRec) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          let values <- rec.evalExplicitSequenceValueExprSlots e ctx env
          collect rest (values.reverse ++ acc)
    let items <- collect elements []
    pure (Result.listValue items, 1)

  /-- Evaluate the INTERNAL `sequenceConstruct` join node as one sequence
      value. Join semantics, not written-parentheses semantics: a non-spread
      leaf whose value is `()` contributes NO item (an empty join
      contribution), an explicit spread leaf contributes exactly the items the
      spread expression supplies — read back like a spread output row
      (`evalCounted` + `countedTopLevelValues`), one boundary per written star,
      never reopened, a spread-produced `()` item included — and the result is
      normalized. (Until October 2026 the leaf itself was handed to
      `evalSequenceSpreadOperandItems` (since S2 `evalSequenceSpreadOperandValue`), which re-spread the spread's captured value:
      a k-star leaf acted as k+1 layers whenever it supplied one structured item.)
      Written parentheses parse to `capture` nodes and always keep a
      non-spread `()` item visible — surface syntax must never route through
      this node (see the constructor note on `Expr.sequenceConstruct`).
      C#: `EvalSequenceConstructCounted`; plain `eval` is this function's
      value projection on both sides. -/
  def EvalBody.evalSequenceConstructCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec loop : List Expr -> List Result -> EvalM CountedResult
      | [], items =>
          let value := Result.normalize (Result.sequenceValue items.reverse)
          pure (value, Result.valueCount value)
      | leaf :: rest, items => do
          match leaf with
          | .sequenceSpread _ => do
              -- A spread leaf supplies exactly the spread EXPRESSION's items, read back
              -- like a spread output row (`countedTopLevelValues`): one boundary per
              -- written star, never reopened (`countedTopLevelValues_spreadSupplyResult`).
              let out <- rec.evalCounted leaf ctx env
              loop rest ((countedTopLevelValues out).reverse ++ items)
          | _ => do
              let value <- rec.eval leaf ctx env
              if Result.valueCount value = 0 then
                loop rest items
              else
                loop rest (value :: items)
    loop (sequenceConstructLeaves e) []

  /-- Evaluate a unary operator expression as one counted value. The operand is
      read at its value boundary. `not` is the Boolean negation and REQUIRES a
      Boolean operand (a number has no truth value); `-` is numeric negation:
      every non-numeric operand — a string, a Boolean, a sequence (the empty
      sequence value like any other, SYN-01) or a list — is the one value-kind
      error naming the operator and the operand (Q-27), never an arity error.
      Owned here so
      `eval` (the value projection) never carries independent operator
      semantics. C#: `Evaluator.ApplyUnaryOperator`, reached from the unary
      case of `EvalExpressionSpineCounted`. -/
  def EvalBody.evalUnaryCounted (rec : EvalRec) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let r <- rec.eval operand ctx env
    match op with
    | .not =>
        match Result.asBool? r with
        | some b => pure (Result.bool (!b), 1)
        | none => .error (Error.typeMismatch
            s!"operator `not` expects a Boolean operand, but the operand was {operandDescription r}")
    | .minus =>
        match Result.asInt? r with
        | some v => pure (Result.atom (-v), 1)
        | none => .error (Error.typeMismatch
            s!"operator `-` expects a numeric scalar operand, but the operand was {operandDescription r}")

  /-- Evaluate a binary (arithmetic or logical) operator expression as one
      counted value. Both operands are read at their value boundaries; strings
      reject every binary operator; everything else follows the numeric-scalar
      core or the Boolean-only logical rule. Comparisons are NOT binary
      operators — every comparison is a link of a comparison chain
      (`evalComparisonCounted`). The empty sequence value `()` is an ORDINARY
      operand here — it has no numeric scalar value, so it is rejected by the
      same operand validation as any other non-scalar value (SYN-01). Empty
      NEUTRALITY belongs to the arity algebra's supply operations
      (capture/collect/spread), never to scalar operators. Owned here so `eval`
      (the value projection) never carries independent operator semantics.
      C#: the binary case of `EvalExpressionSpineCounted` / `ApplyBinaryOperator`. -/
  def EvalBody.evalBinaryCounted (rec : EvalRec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let lr <- rec.eval a ctx env
    let rr <- rec.eval b ctx env
    match op with
    -- The logical operators are Boolean-only: both operands are evaluated
    -- left to right before the operator applies (the established evaluation
    -- order — no short circuit), and each must be a Boolean value. There is
    -- no numeric truthiness, so `1 and 2` is a value-kind error.
    | .and | .or | .xor => do
        let binaryContext := s!"while evaluating `{binaryExprDiagnosticName op a b}`"
        let x <- withCtx binaryContext (requireBooleanOperand op "left" lr)
        let y <- withCtx binaryContext (requireBooleanOperand op "right" rr)
        let value : Bool :=
          match op with
          | .and => x && y
          | .or  => x || y
          | _    => x != y
        pure (Result.bool value, 1)
    | _ =>
      -- SYN-01: the empty sequence value is NOT an identity for scalar
      -- operators. `()` carries no numeric scalar value, so it falls through to
      -- the ordinary operand validation below exactly like `(1, 2)` or `[]` —
      -- `10 / ()`, `() > 10`, `() and 7`, and `() + 'text'` are operand errors,
      -- never a passthrough of the other operand.
      match lr, rr with
      -- Non-equality operators are not defined on strings (they fail here rather
      -- than via expectInt so the diagnostic names the string operands).
      | .str _, .str _ => .error (Error.typeMismatch "Strings only support == and != operators")
      -- Mixed string/number or string/sequence value: fail for any operator
      | .str _, _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
      | _, .str _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
      | _, _ => do
        let binaryContext := s!"while evaluating `{binaryExprDiagnosticName op a b}`"
        let x <- withCtx binaryContext (requireNumericScalarOperand op "left" lr)
        let y <- withCtx binaryContext (requireNumericScalarOperand op "right" rr)
        -- Check for division by zero
        if (op == BinaryOp.div || op == BinaryOp.idiv || op == BinaryOp.mod) && y == 0 then
          .error Error.divByZero
        else if op == BinaryOp.pow && y < 0 then do
          let value <- negativeIntPow x y
          pure (value, Result.valueCount value)
        else
          let value : Result :=
            -- The logical operators are handled above; their arm below keeps
            -- the match exhaustive over BinaryOp and is unreachable here.
            match op with
            | .add  => .atom (x + y)
            | .sub  => .atom (x - y)
            | .mul  => .atom (x * y)
            -- Division and modulo truncate toward zero (Int.tdiv / Int.tmod),
            -- matching the C# reference: `-7 div 2 = -3` and `-7 mod 2 = -1`.
            -- `/` on non-divisible operands additionally truncates the exact
            -- decimal quotient as part of the integer-core limitation.
            | .div  => .atom (x.tdiv y)
            | .idiv => .atom (x.tdiv y)
            | .mod  => .atom (x.tmod y)
            | .pow  => .atom (intPow x y.toNat)
            | .and | .or | .xor => .bool false
          pure (value, 1)

  /-- Evaluate a COMPARISON CHAIN `first op1 x1 op2 x2 …` as one counted Boolean
      value — incrementally, left to right: the first operand, then link by
      link, evaluating the link's operand and comparing the PREVIOUS operand's
      value with it (`applyComparison`). Every operand is evaluated EXACTLY ONCE
      (the previous VALUE is carried forward, never its expression), a `false`
      link never stops the chain (KatLang's eager Boolean composition: a later
      invalid comparison is still reported), and an error terminates it before
      any later operand is evaluated. The chain is `true` iff every link held; a
      chain with no links evaluates its first operand and is `true`.
      C#: the Comparison case of `EvalExpressionSpineCounted` /
      `EvalExpressionSpineCountedAsync` and `LoopOptimizer.EvalLoopComparisonPlan`. -/
  def EvalBody.evalComparisonCounted (rec : EvalRec) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let firstValue <- rec.eval first ctx env
    rec.evalComparisonLinksCounted first firstValue true links ctx env

  /-- The link loop of `evalComparisonCounted`: `previous` is the value of
      `previousExpr` (the left side of the next link) and `holds` the verdict of
      the links compared so far. -/
  def EvalBody.evalComparisonLinksCounted (rec : EvalRec) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match links with
    | [] => pure (Result.bool holds, 1)
    | link :: rest => do
        let next <- rec.eval link.operand ctx env
        let linkHolds <- applyComparison link.op previousExpr link.operand previous next
        rec.evalComparisonLinksCounted link.operand next (holds && linkHolds) rest ctx env

  /-- Evaluate an expression together with the number of top-level values it
      emits at the current algorithm boundary — the CANONICAL expression
      dispatch: it matches EVERY `Expr` variant explicitly (no default arm),
      and plain `eval` is its total value projection. A new `Expr` variant
      therefore fails compilation here until it is given a counted arm — the
      structural guard against silently reintroducing plain-owned semantics.

      Calls, name resolution, collection builtins, and SELECTION (`.index`,
      like `first`/`last`) are value boundaries: they emit `Result.valueCount`
      of the result value (one value for a non-empty result), so a
      multi-output body/collection or a selected sequence/list is observed as
      one value and only a caller-site spread `value*` re-spreads it.
      Block expressions count as one sequence value when non-empty. `sequenceConstruct`
      emits one constructed sequence value. `sequenceSpread`
      emits the immediate spread items of its operand. All other value expressions emit either zero values (empty
      result) or one value.

      A constructor, selection, interpolation or operator expression demands no computation's
      output of its own: it forms a value from SUBORDINATE computations, so a missing output
      escaping it is NESTED (`withNestedMissingOutput`, Q-36). -/
  def EvalBody.evalCounted (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match e with
    | .param x => do
        let (ctx, env) <- parameterContext x ctx env
        -- AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01, September 2026): a Model-C
        -- parameter is read through its need cell (its first demand evaluates the
        -- supplied computation once; every later read reuses the completed outcome).
        if let some address := lookupAssoc x ctx.needEnv then
          return <- rec.demandNeedRecursive address
        match env.lookup x with
        | some v => pure (v, Result.valueCount v)
        | none => .error (Error.unknownName x)
    | .sequenceConstruct _ _ =>
      withNestedMissingOutput (rec.evalSequenceConstructCounted e ctx env)
    | .emptySequence depth =>
        let value := buildEmptySequenceValue depth
        pure (value, Result.valueCount value)
    | .sequenceSpread _ =>
        rec.evalSequenceSpreadCounted e ctx env
    | .listLiteral elements =>
        withNestedMissingOutput (rec.evalListLiteralCounted elements ctx env)
    | .algorithmExpr a => do
        -- An inline alias block (`{ F }`) is demanded as its VALUE terminal (OD-E, M4★: the
        -- terminal binding's cached bare read, no entry of its own), and a rejected demand is
        -- reported as its written target reference `F` reports it (`zeroArgumentDemandError?`,
        -- FA-OQ-1; C#: `EvalInlineAliasValue`); a chain reaching a runtime-target alias reads
        -- that alias's binding cell (META-S3-2).
        let terminal <- rec.resolveAliasValueTarget (wireToCaller ctx a) ctx
        match terminal.demandError? e with
        | some err => .error err
        | none =>
          let r <- EvalBody.terminalAccess rec terminal ctx env
          pure (r.fst, Result.valueCount r.fst)
    | .capture rows => do
        -- A capture in value position is a value boundary: the body's supply
        -- is captured to one canonical value and re-counted as that value's
        -- valueCount.
        let r <- rec.evalCaptureValue rows ctx env
        pure (r, Result.valueCount r)
    | .resolve n => do
        match ctx.callStack with
        | owner :: _ =>
            -- OD-E (M4★): an alias binding reads its VALUE terminal — the terminal binding's own
            -- entry, or a runtime-target alias's binding cell — never an entry of its own.
            let terminal <- rec.lookupLexicalValueProperty owner n ctx
            match terminal.demandError? e with
            | some err => .error err
            | none =>
                -- The property that lacks output is the TERMINAL binding a reference reads (M4★: a
                -- transparent reference is its target), so the report names it.
                withMissingOutputCtx (CtxMsg.property (terminal.readNameOr n)) <| do
                  let counted <- EvalBody.terminalAccess rec terminal ctx env
                  pure (counted.fst, Result.valueCount counted.fst)
        | [] => .error (Error.unknownName n)
    | .index receiver selectors => withNestedMissingOutput do
        -- VARIADIC POSTFIX SELECTION (October 2026). (1) The receiver is demanded
        -- ONCE through its ordinary value path (`Data` is the cached property
        -- read, `Data()` one fresh call), even when no selector is supplied.
        let value <- rec.eval receiver ctx env
        -- (2) The selector supply is formed exactly like a call's: explicit
        -- spreads run during formation, ordinary selectors stay suspended cells.
        let cells <- NeedSupply.addresses rec.evalSupplySpread ctx env selectors
        -- (3) Each supplied selector is demanded, validated and selected left to
        -- right; the first failure ends the selection.
        -- An ARGUMENT VIEW receiver (CallReference S2) selects among the plan's ORIGINAL cells,
        -- each selector validated before the view's supply is read and only the selected
        -- cells demanded (`selectViewWith`).
        let selected <-
          match value with
          | .argView a =>
              selectViewWith (fun cell => Prod.fst <$> rec.demandNeedRecursive cell)
                (rec.argumentViewCells a) (fun cell => Prod.fst <$> rec.demandNeedRecursive cell) cells
          | _ => selectWith (fun cell => Prod.fst <$> rec.demandNeedRecursive cell) value cells
        -- (4) SELECTION IS A VALUE BOUNDARY: the selected values are captured by
        -- ordinary normalization of the result grouping and re-counted.
        -- C#: the Index case of `EvalExpressionSpineCounted`.
        pure (selectionResult selected)
    | .dotMember o n fallback argsOpt => withCtx (CtxMsg.dotCall o n) do
        rec.evalDotCallCounted o n fallback argsOpt ctx env
    | .call f args =>
        rec.evalCallCountedExpr f args ctx env
    | .num n => pure (Result.atom n, 1)
    | .stringLiteral s => pure (Result.str s, 1)
    | .interpolatedString head links => withNestedMissingOutput do
        -- VAL-12: the holes left to right, each once through the ordinary value read
        -- (the read a comparison operand uses), each converted at once; the first failure
        -- ends the node; ONE string value.
        -- A hole whose value contains a call reference has no text (CallReference S1):
        -- it is refused when that hole is reached, so earlier holes have run and later
        -- ones never do — the ordinary first-failure order of interpolation.
        let text <- interpolateWith (fun hole => do
            let value <- rec.eval hole ctx env
            requireCallRefFree callReferenceHasNoTextMessage value
            pure value) head links
        pure (Result.str text, 1)
    | .boolLiteral b => pure (Result.bool b, 1)
    | .unary op operand =>
        withNestedMissingOutput (rec.evalUnaryCounted op operand ctx env)
    | .binary op a b =>
        withNestedMissingOutput (rec.evalBinaryCounted op a b ctx env)
    | .comparison first links =>
        withNestedMissingOutput (rec.evalComparisonCounted first links ctx env)

  /-- User-defined call evaluation with plain Result output.
      This is the Result projection of `evalUserCallCounted`: the counted twin
      owns argument binding (dual-view ABI, patterned/deconstruction/flat
      dispatch) and body evaluation, and the non-counted path only discards
      the emitted-count metadata (`reCountValueBoundary` is value-preserving).
      The CoreTests call projection parity guards pin this equivalence. -/
  def EvalBody.evalUserCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalUserCallCounted callee args ctx env
    pure out.fst

  /-- Conditional call evaluation with plain Result output.
      This is the Result projection of `evalConditionalCallCounted`: the
      counted twin owns argument assembly, clause matching, and branch body
      evaluation, and the non-counted path only discards the emitted-count
      metadata (`reCountValueBoundary` is value-preserving). The CoreTests
      call projection parity guards pin this equivalence. -/
  def EvalBody.evalConditionalCall (rec : EvalRec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result := do
    let out <- rec.evalConditionalCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Context-aware direct call evaluation for expression position with plain
      Result output. This is the Result projection of `evalCallCountedExpr`:
      the counted twin owns callee resolution and dispatch, including the
      `CtxMsg.call` error-context attachment, so contexts cannot drift between
      the plain and counted spellings. -/
  def EvalBody.evalCallExpr (rec : EvalRec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalCallCountedExpr f args ctx env
    pure out.fst

  /-- Dot-call evaluation with plain Result output.
      This is the Result projection of `evalDotCallCounted`: the counted twin
      owns the dot-call dispatch (receiver resolution, structural lookup,
      lexical fallback with receiver injection, zero-arg property access,
      conditional dispatch, and receiver-spread rules), and the non-counted
      path only discards the emitted-count metadata. The CoreTests dot-call
      projection parity guards pin this equivalence (values, error
      diagnostics, and evaluator state) case by case. -/
  def EvalBody.evalDotCall (rec : EvalRec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalDotCallCounted target name fallback argsOpt ctx env
    pure out.fst

  /-- Expression evaluation with plain Result output.
      This is the TOTAL Result projection of `evalCounted`: the counted
      evaluator owns the per-variant dispatch for every `Expr` constructor
      (leaves included), and this projection only discards the emitted-count
      metadata. Counted code calls it wherever a subexpression is read at a
      value boundary; that recursion is into strictly smaller work, never a
      same-node ownership cycle, because `evalCounted` has no arm that
      delegates back here. -/
  def EvalBody.eval (rec : EvalRec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- rec.evalCounted e ctx env
    pure out.fst


/-- One condition-first `while` round and, on a true verdict, the next round (LOOP-06,
    `WhileRound.advance`): a false verdict finishes with the cells that entered the round (R1: zero
    accepted transitions return the initial cells). The round loop is not structurally bounded, so
    it is its own evaluator call: every round costs one fuel unit (R7). Reached only from the
    `while` arm of `applyBuiltinCounted`'s META branch. C#: the `while` loop of `Evaluator.EvalNeedLoop`. -/
def EvalBody.whileLoop (rec : EvalRec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (stepName : String) (cells : List Nat) : EvalM (List Nat) := do
  let algorithm <- projectInvokingSlot (invokingSlotRole .whileBuiltin) (<- rec.invokeNeed step)
  match <- WhileRound.advance (fun cells => rec.runNeedWhileRound algorithm ctx env cells stepName) cells with
  | .inl final => pure final
  | .inr next => rec.whileLoop step ctx env stepName next

def evalStep (rec : EvalRec) : EvalRec := fun c =>
  match c with
  | .whileLoop step ctx env stepName cells => EvalBody.whileLoop rec step ctx env stepName cells
  | .aliasStepIsRuntime step target ctx visited => EvalBody.aliasStepIsRuntime rec step target ctx visited
  | .aliasValue wired ctx env => EvalBody.aliasValue rec wired ctx env
  | .resolveAliasChase followCarriers projectRuntime a ctx visited last => EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last
  | .resolveAliasTarget a ctx => EvalBody.resolveAliasTarget rec a ctx
  | .resolveAliasStructure a ctx => EvalBody.resolveAliasStructure rec a ctx
  | .resolveAliasValueTarget a ctx => EvalBody.resolveAliasValueTarget rec a ctx
  | .aliasOriginBinding? a ctx => EvalBody.aliasOriginBinding? rec a ctx
  | .lookupLexicalProperty a name ctx => EvalBody.lookupLexicalProperty rec a name ctx
  | .lookupLexicalValueProperty a name ctx => EvalBody.lookupLexicalValueProperty rec a name ctx
  | .lookupLexical a name ctx => EvalBody.lookupLexical rec a name ctx
  | .needPlanNormalizeCallee callee ctx => EvalBody.needPlanNormalizeCallee rec callee ctx
  | .resolveAlg e ctx => EvalBody.resolveAlg rec e ctx
  | .projectNeedCallable address => EvalBody.projectNeedCallable rec address
  | .projectNeedWrittenAt address source caller => EvalBody.projectNeedWrittenAt rec address source caller
  | .linkCallable address => EvalBody.linkCallable rec address
  | .projectParameterCallable x ctx => EvalBody.projectParameterCallable rec x ctx
  | .projectNeedWritten source caller => EvalBody.projectNeedWritten rec source caller
  | .projectNeedStructuralMember source ctx => EvalBody.projectNeedStructuralMember rec source ctx
  | .resolveCalleeAlg f ctx => EvalBody.resolveCalleeAlg rec f ctx
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index
  | .resolveDotReceiver? e ctx => EvalBody.resolveDotReceiver? rec e ctx
  | .resolveDotReceiver e ctx => EvalBody.resolveDotReceiver rec e ctx
  | .algorithmIntrinsicRoute receiver ctx => EvalBody.algorithmIntrinsicRoute rec receiver ctx
  | .demandNeedRecursive address => EvalBody.demandNeedRecursive rec address
  | .evalSuppliedAt address e ctx env => EvalBody.evalSuppliedAt rec address e ctx env
  | .linkValue address => EvalBody.linkValue rec address
  | .algorithmOfValue val argsOpt ctx env => EvalBody.algorithmOfValue rec val argsOpt ctx env
  | .capturedCallee callee => EvalBody.capturedCallee rec callee
  | .referenceReceiverValue target targetAlg ctx env => EvalBody.referenceReceiverValue rec target targetAlg ctx env
  | .algorithmCalleeOf receiver ctx env => EvalBody.algorithmCalleeOf rec receiver ctx env
  | .evalSuppliedCallCounted origin callee cells ctx env calleeName => EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName
  | .evalNeedUserSupply callee cells ctx env => EvalBody.evalNeedUserSupply rec callee cells ctx env
  | .evalNeedFamilySupply callee cells ctx env calleeName => EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName
  | .invokeNeed arg => EvalBody.invokeNeed rec arg
  | .argumentNeed arg ctx env => EvalBody.argumentNeed rec arg ctx env
  | .runNeedStepSlots step ctx env cells stepName => EvalBody.runNeedStepSlots rec step ctx env cells stepName
  | .runNeedWhileRound step ctx env cells stepName => EvalBody.runNeedWhileRound rec step ctx env cells stepName
  | .evalAlgOutputCore a ctx env => EvalBody.evalAlgOutputCore rec a ctx env
  | .evalAlgOutput a ctx env => EvalBody.evalAlgOutput rec a ctx env
  | .evalProgramOutput a ctx env => EvalBody.evalProgramOutput rec a ctx env
  | .evalAlgOutputSlots a ctx env => EvalBody.evalAlgOutputSlots rec a ctx env
  | .formOutputRow ctx env e => EvalBody.formOutputRow rec ctx env e
  | .whileVerdictSlots a ctx env => EvalBody.whileVerdictSlots rec a ctx env
  | .evalSequenceCallbackCall callee item ctx env calleeName => EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName
  | .evalSequenceCallbackCallCounted callee item ctx env calleeName => EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName
  | .evalAlgOutputPreparedCore a ctx env => EvalBody.evalAlgOutputPreparedCore rec a ctx env
  | .evalOutputRowsPreparedCore rows rowCtx env => EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env
  | .evalCapturePreparedCore rows ctx env => EvalBody.evalCapturePreparedCore rec rows ctx env
  | .evalCaptureCountedCore rows ctx env => EvalBody.evalCaptureCountedCore rec rows ctx env
  | .evalCaptureValue rows ctx env => EvalBody.evalCaptureValue rec rows ctx env
  | .evalAlgOutputCountedCore a ctx env => EvalBody.evalAlgOutputCountedCore rec a ctx env
  | .evalAlgOutputCounted a ctx env => EvalBody.evalAlgOutputCounted rec a ctx env
  | .evalZeroArgumentDemandOutputCounted a ctx env => EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env
  | .evalZeroArgumentDemandOutput a ctx env => EvalBody.evalZeroArgumentDemandOutput rec a ctx env
  | .evalArgumentValueCounted arg ctx env => EvalBody.evalArgumentValueCounted rec arg ctx env
  | .evalArgumentValue arg ctx env => EvalBody.evalArgumentValue rec arg ctx env
  | .evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request
  | .evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env
  | .evalConditionalCallbackCallCounted callee args ctx env calleeName => EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName
  | .evalUserCallbackCallCounted callee args ctx env => EvalBody.evalUserCallbackCallCounted rec callee args ctx env
  | .evalResolvedCallbackCallCounted callee args ctx env calleeName => EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName
  | .evalResolvedCallbackCall callee args ctx env calleeName => EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName
  | .evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName
  | .demandSequenceBuiltinCallItemValue item ctx env => EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env
  | .bindSequenceBuiltinArguments b metadata args ctx env => EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env
  | .evalReduceCounted collection stepAlg initial ctx env => EvalBody.evalReduceCounted rec collection stepAlg initial ctx env
  | .evalFilterCounted items predicateAlg ctx env => EvalBody.evalFilterCounted rec items predicateAlg ctx env
  | .evalMapCounted collection transformAlg ctx env => EvalBody.evalMapCounted rec collection transformAlg ctx env
  | .applyBuiltinCountedSequence b metadata args ctx env => EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env
  | .applyBuiltinCounted b args ctx env => EvalBody.applyBuiltinCounted rec b args ctx env
  | .applyBuiltin b args ctx env => EvalBody.applyBuiltin rec b args ctx env
  | .applyBuiltinCountedResolved b args ctx env => EvalBody.applyBuiltinCountedResolved rec b args ctx env
  | .evalExplicitSequenceValueItems a ctx env => EvalBody.evalExplicitSequenceValueItems rec a ctx env
  | .evalExplicitSequenceValueRowSlots rows rowCtx env => EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env
  | .evalExplicitSequenceValueExprSlots expr ctx env => EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env
  | .evalUserCallCounted callee args ctx env => EvalBody.evalUserCallCounted rec callee args ctx env
  | .evalConditionalCallCounted callee args ctx env calleeName => EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName
  | .evalResolvedCall callee args ctx env calleeName => EvalBody.evalResolvedCall rec callee args ctx env calleeName
  | .evalResolvedCallCounted callee args ctx env calleeName origin => EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin
  | .evalCallCountedExpr f args ctx env => EvalBody.evalCallCountedExpr rec f args ctx env
  | .callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env
  | .rejectDotStringIntrinsicArguments argsOpt ctx env => EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env
  | .evalDotStringReceiverValue target targetAlg ctx env => EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env
  | .evalDotCallCounted target name fallback argsOpt ctx env => EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env
  | .rejectInvokeIntrinsicArguments argsOpt ctx env => EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env
  | .invokeCallReferenceValue val => EvalBody.invokeCallReferenceValue rec val
  | .argumentViewCells a => EvalBody.argumentViewCells rec a
  | .evalArgumentViewBuiltin b a => EvalBody.evalArgumentViewBuiltin rec b a
  | .evalSequenceSpreadOperandValue e ctx env => EvalBody.evalSequenceSpreadOperandValue rec e ctx env
  | .evalSequenceSpreadCounted e ctx env => EvalBody.evalSequenceSpreadCounted rec e ctx env
  | .evalSupplySpread e ctx env => EvalBody.evalSupplySpread rec e ctx env
  | .evalListLiteralCounted elements ctx env => EvalBody.evalListLiteralCounted rec elements ctx env
  | .evalSequenceConstructCounted e ctx env => EvalBody.evalSequenceConstructCounted rec e ctx env
  | .evalUnaryCounted op operand ctx env => EvalBody.evalUnaryCounted rec op operand ctx env
  | .evalBinaryCounted op a b ctx env => EvalBody.evalBinaryCounted rec op a b ctx env
  | .evalComparisonCounted first links ctx env => EvalBody.evalComparisonCounted rec first links ctx env
  | .evalComparisonLinksCounted previousExpr previous holds links ctx env => EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env
  | .evalCounted e ctx env => EvalBody.evalCounted rec e ctx env
  | .evalUserCall callee args ctx env => EvalBody.evalUserCall rec callee args ctx env
  | .evalConditionalCall callee args ctx env calleeName => EvalBody.evalConditionalCall rec callee args ctx env calleeName
  | .evalCallExpr f args ctx env => EvalBody.evalCallExpr rec f args ctx env
  | .evalDotCall target name fallback argsOpt ctx env => EvalBody.evalDotCall rec target name fallback argsOpt ctx env
  | .eval e ctx env => EvalBody.eval rec e ctx env

/-- R7: the evaluator at fuel `n`: `n` iterations of `evalStep` from the everywhere-incomplete
    answer. Every incomplete outcome is normalized to THE incomplete outcome. -/
def evalFuel : Nat → EvalRec
  | 0 => fun _ => EvalM.incomplete
  | n + 1 => fun c => (evalStep (evalFuel n) c).normalizeIncomplete

/-- The fuel the production driver tries first. Any value is correct (a completed outcome does
    not depend on the fuel that completes it); this one is large enough that no run reaching
    completion on a real stack needs a second attempt. -/
def initialFuel : Nat := 2 ^ 24

/-- R7: the production fuel search from one entry state: the core at `fuel`, and — only when that
    is incomplete — again from the SAME entry state with more fuel. A `partial_fixpoint`: its
    unfolding equation `searchFuel.eq_1` and its fixpoint induction are kernel theorems; it returns
    `none` exactly when every attempt is incomplete, which compiled code never observes (it keeps
    searching, i.e. the program diverges). -/
def searchFuel (c : EvalCall) (s : EvalState) (fuel : Nat) : Option (Except Error c.Ret × EvalState) :=
  match (evalFuel fuel c).runState s with
  | (.error .fuelExhausted, _) => searchFuel c s (2 * fuel + 1)
  | r => some r
partial_fixpoint

/-- R7: THE PRODUCTION EVALUATOR at one call: the total core under the fuel search
    (`searchFuel`). Every production operation below is this at its call. -/
def evalUnbounded (c : EvalCall) : EvalM c.Ret :=
  ⟨fun s => (searchFuel c s initialFuel).getD (.error .fuelExhausted, s)⟩

/-! The production operations: each is `evalUnbounded` at its own call. -/

def aliasStepIsRuntime (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) : EvalM Bool :=
  evalUnbounded (.aliasStepIsRuntime step target ctx visited)

def aliasValue (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.aliasValue wired ctx env)

def resolveAliasChase (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) : EvalM AliasChaseEnd :=
  evalUnbounded (.resolveAliasChase followCarriers projectRuntime a ctx visited last)

def resolveAliasTarget (a : Algorithm) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.resolveAliasTarget a ctx)

def resolveAliasStructure (a : Algorithm) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.resolveAliasStructure a ctx)

def resolveAliasValueTarget (a : Algorithm) (ctx : EvalCtx) : EvalM AliasTerminal :=
  evalUnbounded (.resolveAliasValueTarget a ctx)

def aliasOriginBinding? (a : Algorithm) (ctx : EvalCtx) : EvalM (Option (Algorithm × PropDef)) :=
  evalUnbounded (.aliasOriginBinding? a ctx)

def lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM ResolvedProperty :=
  evalUnbounded (.lookupLexicalProperty a name ctx)

def lookupLexicalValueProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM AliasTerminal :=
  evalUnbounded (.lookupLexicalValueProperty a name ctx)

def lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.lookupLexical a name ctx)

def NeedPlan.normalizeCallee (callee : Algorithm) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.needPlanNormalizeCallee callee ctx)

def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.resolveAlg e ctx)

def projectNeedCallable (address : Nat) : EvalM (Option Algorithm) :=
  evalUnbounded (.projectNeedCallable address)

def projectNeedWrittenAt (address : Nat) (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.projectNeedWrittenAt address source caller)

def linkCallable (address : Nat) : EvalM (Option Algorithm) :=
  evalUnbounded (.linkCallable address)

def projectParameterCallable (x : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.projectParameterCallable x ctx)

def projectNeedWritten (source : Expr) (caller : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.projectNeedWritten source caller)

def projectNeedStructuralMember (source : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.projectNeedStructuralMember source ctx)

def resolveCalleeAlg (f : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.resolveCalleeAlg f ctx)

def expectPreparedSequenceBuiltinAlgorithmSuffixArg (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm :=
  evalUnbounded (.expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index)

def resolveDotReceiver? (e : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) :=
  evalUnbounded (.resolveDotReceiver? e ctx)

def resolveDotReceiver (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  evalUnbounded (.resolveDotReceiver e ctx)

def algorithmIntrinsicRoute (receiver : Expr) (ctx : EvalCtx) : EvalM Bool :=
  evalUnbounded (.algorithmIntrinsicRoute receiver ctx)

def demandNeedRecursive (address : Nat) : EvalM CountedResult :=
  evalUnbounded (.demandNeedRecursive address)

def evalSuppliedAt (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalSuppliedAt address e ctx env)

def linkValue (address : Nat) : EvalM CountedResult :=
  evalUnbounded (.linkValue address)

def algorithmOfValue (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.algorithmOfValue val argsOpt ctx env)

def capturedCallee (callee : Nat) : EvalM Algorithm :=
  evalUnbounded (.capturedCallee callee)

def referenceReceiverValue (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.referenceReceiverValue target targetAlg ctx env)

def algorithmCalleeOf (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (Algorithm × String × Nat) :=
  evalUnbounded (.algorithmCalleeOf receiver ctx env)

def evalSuppliedCallCounted (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult :=
  evalUnbounded (.evalSuppliedCallCounted origin callee cells ctx env calleeName)

def evalNeedUserSupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalNeedUserSupply callee cells ctx env)

def evalNeedFamilySupply (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult :=
  evalUnbounded (.evalNeedFamilySupply callee cells ctx env calleeName)

def invokeNeed (arg : ResolvedArgumentAlgorithm) : EvalM (Option Algorithm) :=
  evalUnbounded (.invokeNeed arg)

def argumentNeed (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat :=
  evalUnbounded (.argumentNeed arg ctx env)

def runNeedStepSlots (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (List Result) :=
  evalUnbounded (.runNeedStepSlots step ctx env cells stepName)

def runNeedWhileRound (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) : EvalM (Option (List Result)) :=
  evalUnbounded (.runNeedWhileRound step ctx env cells stepName)

def evalAlgOutputCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalAlgOutputCore a ctx env)

def evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalAlgOutput a ctx env)

def evalProgramOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalProgramOutput a ctx env)

def evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  evalUnbounded (.evalAlgOutputSlots a ctx env)

def formOutputRow (ctx : EvalCtx) (env : ValEnv) (e : Expr) : EvalM (List Result) :=
  evalUnbounded (.formOutputRow ctx env e)

def whileVerdictSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (Option (List Result)) :=
  evalUnbounded (.whileVerdictSlots a ctx env)

def evalSequenceCallbackCall (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  evalUnbounded (.evalSequenceCallbackCall callee item ctx env calleeName)

def evalSequenceCallbackCallCounted (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  evalUnbounded (.evalSequenceCallbackCallCounted callee item ctx env calleeName)

def evalAlgOutputPreparedCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  evalUnbounded (.evalAlgOutputPreparedCore a ctx env)

def evalOutputRowsPreparedCore (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  evalUnbounded (.evalOutputRowsPreparedCore rows rowCtx env)

def evalCapturePreparedCore (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM PreparedAlgorithmOutput :=
  evalUnbounded (.evalCapturePreparedCore rows ctx env)

def evalCaptureCountedCore (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalCaptureCountedCore rows ctx env)

def evalCaptureValue (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalCaptureValue rows ctx env)

def evalAlgOutputCountedCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalAlgOutputCountedCore a ctx env)

def evalAlgOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalAlgOutputCounted a ctx env)

def evalZeroArgumentDemandOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalZeroArgumentDemandOutputCounted a ctx env)

def evalZeroArgumentDemandOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalZeroArgumentDemandOutput a ctx env)

def evalArgumentValueCounted (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalArgumentValueCounted arg ctx env)

def evalArgumentValue (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalArgumentValue arg ctx env)

def evalZeroArgPropertyAccessCounted (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest := .read) : EvalM CountedResult :=
  evalUnbounded (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request)

def evalZeroArgPropertyAccess (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env)

def evalConditionalCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  evalUnbounded (.evalConditionalCallbackCallCounted callee args ctx env calleeName)

def evalUserCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalUserCallbackCallCounted callee args ctx env)

def evalResolvedCallbackCallCounted (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  evalUnbounded (.evalResolvedCallbackCallCounted callee args ctx env calleeName)

def evalResolvedCallbackCall (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  evalUnbounded (.evalResolvedCallbackCall callee args ctx env calleeName)

def evalSequenceReduceStepCounted (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  evalUnbounded (.evalSequenceReduceStepCounted callee element accumulator ctx env calleeName)

def demandSequenceBuiltinCallItemValue (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) : EvalM CallableCallItem :=
  evalUnbounded (.demandSequenceBuiltinCallItemValue item ctx env)

def bindSequenceBuiltinArguments (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM BoundSequenceBuiltinArguments :=
  evalUnbounded (.bindSequenceBuiltinArguments b metadata args ctx env)

def evalReduceCounted (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalReduceCounted collection stepAlg initial ctx env)

def evalFilterCounted (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalFilterCounted items predicateAlg ctx env)

def evalMapCounted (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalMapCounted collection transformAlg ctx env)

def applyBuiltinCountedSequence (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.applyBuiltinCountedSequence b metadata args ctx env)

def applyBuiltinCounted (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.applyBuiltinCounted b args ctx env)

def applyBuiltin (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.applyBuiltin b args ctx env)

def applyBuiltinCountedResolved (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.applyBuiltinCountedResolved b args ctx env)

def evalExplicitSequenceValueItems (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  evalUnbounded (.evalExplicitSequenceValueItems a ctx env)

def evalExplicitSequenceValueRowSlots (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  evalUnbounded (.evalExplicitSequenceValueRowSlots rows rowCtx env)

def evalExplicitSequenceValueExprSlots (expr : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
  evalUnbounded (.evalExplicitSequenceValueExprSlots expr ctx env)

def evalUserCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalUserCallCounted callee args ctx env)

def evalConditionalCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM CountedResult :=
  evalUnbounded (.evalConditionalCallCounted callee args ctx env calleeName)

def evalResolvedCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  evalUnbounded (.evalResolvedCall callee args ctx env calleeName)

def evalResolvedCallCounted (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") (origin : CalleeOrigin := .none) : EvalM CountedResult :=
  evalUnbounded (.evalResolvedCallCounted callee args ctx env calleeName origin)

def evalCallCountedExpr (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalCallCountedExpr f args ctx env)

def callLexicalWithReceiverCounted (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env)

def rejectDotStringIntrinsicArguments (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit :=
  evalUnbounded (.rejectDotStringIntrinsicArguments argsOpt ctx env)

def evalDotStringReceiverValue (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalDotStringReceiverValue target targetAlg ctx env)

def evalDotCallCounted (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalDotCallCounted target name fallback argsOpt ctx env)

def rejectInvokeIntrinsicArguments (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Unit :=
  evalUnbounded (.rejectInvokeIntrinsicArguments argsOpt ctx env)

def invokeCallReferenceValue (val : Result) : EvalM CountedResult :=
  evalUnbounded (.invokeCallReferenceValue val)

def argumentViewCells (a : Nat) : EvalM (List NeedSupply.Sourced) :=
  evalUnbounded (.argumentViewCells a)

def evalArgumentViewBuiltin (b : Builtin) (a : Nat) : EvalM CountedResult :=
  evalUnbounded (.evalArgumentViewBuiltin b a)

def evalSequenceSpreadOperandValue (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalSequenceSpreadOperandValue e ctx env)

def evalSequenceSpreadCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalSequenceSpreadCounted e ctx env)

def evalSupplySpread (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM SpreadSupply :=
  evalUnbounded (.evalSupplySpread e ctx env)

def evalListLiteralCounted (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalListLiteralCounted elements ctx env)

def evalSequenceConstructCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalSequenceConstructCounted e ctx env)

def evalUnaryCounted (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalUnaryCounted op operand ctx env)

def evalBinaryCounted (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalBinaryCounted op a b ctx env)

def evalComparisonCounted (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalComparisonCounted first links ctx env)

def evalComparisonLinksCounted (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalComparisonLinksCounted previousExpr previous holds links ctx env)

def evalCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  evalUnbounded (.evalCounted e ctx env)

def evalUserCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalUserCall callee args ctx env)

def evalConditionalCall (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result :=
  evalUnbounded (.evalConditionalCall callee args ctx env calleeName)

def evalCallExpr (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalCallExpr f args ctx env)

def evalDotCall (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.evalDotCall target name fallback argsOpt ctx env)

def eval (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
  evalUnbounded (.eval e ctx env)


/-- First VALUE demand through the total completion shell, over the production operations (the
    total core under its fuel search, R7). -/
def demandNeed (address : Nat) : EvalM CountedResult :=
  NeedDemand.step (evalSuppliedAt address)
    ⟨resolveCalleeAlg, NeedPlan.normalizeCallee, evalSuppliedCallCounted, evalSupplySpread,
     classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute, projectNeedCallable⟩
    demandNeedRecursive address

/-- The production invocation-plan route: the one the recursive VALUE edge installs. -/
def productionPlanRoute : NeedPlan.Route :=
  ⟨resolveCalleeAlg, NeedPlan.normalizeCallee, evalSuppliedCallCounted, evalSupplySpread,
   classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute, projectNeedCallable⟩

/-- The channels every binder call site of the evaluator recursion core passes, at the production
    answer: `EvalRec.bindingChannels evalUnbounded` (`bindingChannels_is_core`, by `rfl`; the
    sites are `evalNeedUserSupply`, `evalNeedFamilySupply`, `runNeedStepWith` — twice — and
    `evalZeroArgumentDemandOutputCounted`). Its VALUE channel is the public `demandNeed` by
    definition. -/
def bindingChannels : NeedChannels :=
  NeedChannels.shell evalSuppliedAt productionPlanRoute demandNeedRecursive projectNeedWrittenAt

/-- META projection of a supplied cell (CallReference M1.5); since S1 the binder's `meta`
    capture reaches it through `NeedPlan.reference`. -/
def reifyNeedCall (address : Nat) : EvalM NeedPlan.CallReference :=
  NeedPlan.reify address

/-- Explicit invocation of a reified plan over its one supply; since S1 it is exactly what the
    `Invoke` dot intrinsic runs for a `Result.callRef` receiver (`invokeCallReferenceValue`). -/
def invokeNeedCall (reference : NeedPlan.CallReference) : EvalM CountedResult :=
  NeedPlan.invoke productionPlanRoute reference

/-- THE sourced supply: ordinary slots retain the current written argument, known
    collector slices retain each transported cell's source, computed spreads none.
    The evaluator core installs this same total former over its own `evalSupplySpread`. -/
def formNeedSupplySourced (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    : EvalM (List (Nat × Option Expr)) :=
  NeedSupply.form evalSupplySpread ctx env args

/-- The supply's cells, projected from THE sourced supply without another assembler. -/
def formNeedSupply (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Nat) := do
  pure ((← formNeedSupplySourced args ctx env).map Prod.fst)

--------------------------------------------------------------------------------
-- Surface syntax support: implicit parameter detection
--------------------------------------------------------------------------------

/-- Probe whether a bare name should be treated as an implicit parameter.
    Used by surface syntax parsers to distinguish:
    - `Expr.param name` (implicit parameter) if name does not resolve lexically
    - `Expr.resolve name` (lexical reference) if name resolves in scope

    This uses the ownership-first lexical lookup order already encoded in `lookupLexical`:
    1. Local properties of the current algorithm
    2. Structural properties in parent chain
    3. Opens as fallback

    Returns:
    - `ok true`: name does not resolve → treat as implicit parameter
    - `ok false`: name resolves lexically → emit resolve, not param
    - `error`: propagates resolution errors (e.g., ambiguousOpen for diagnostics)

    Example usage in surface layer:
    ```
    -- Build initial algorithm with known properties/opens
    let alg := Algorithm.mk parent (Algorithm.normalParameters params) opens knownProps []
    let ctx := EvalCtx.push alg parentCtx

    -- For each free identifier token:
    match shouldTreatAsImplicitParam alg name ctx with
    | ok true  => emit (Expr.param name), add name to Algorithm.params
    | ok false => emit (Expr.resolve name)
    | error e  => report diagnostic (e.g., ambiguous open)
    ```

    SCOPE: this is the PROMOTION question only — whether a name that NOTHING
    binds becomes a new implicit parameter of the algorithm being elaborated.
    It is not the ownership question. Once a name IS bound, which binding the
    occurrence selects — an enclosing scope's parameter or a property — is
    `selectOwnedDeclaration` below, and the two are independent: promotion
    still stops at any visible property or opened name, while ownership
    decides between an already-established parameter and a property by owning
    scope. The caller must exclude already-established parameter bindings BEFORE
    invoking this probe. The probe itself only calls `lookupLexical`, the
    projection of `lookupLexicalProperty`: it does not inspect the owner's
    parameter declarations or the value/algorithm binding environments.
    A captured parameter therefore bypasses this probe; ownership selection
    below keeps it from losing to a farther property.

    OPEN TARGETS: `lookupLexical` resolves the level's opens lazily, and a target
    that resolves to nothing fails that resolution. The surface layer never lets
    such a failure reach promotion: it refuses every `open` target that resolves
    to nothing — an unknown head, a missing member, a non-public path step, from
    a name head or an inline block or module head alike — as a static diagnostic
    (C# `DiagnosticCode.UnresolvedOpenTarget`), and a dotted path whose head is
    not itself an open form (`open 5.N`, which `resolveAlgForOpen` rejects through
    its receiver recursion) as C# `DiagnosticCode.BadOpenForm`, so in an accepted
    program this probe only ever sees resolvable targets. Its `.error` arm reports
    genuine lookup failures; an ambiguous open is no longer one of them for a
    WRITTEN name: Q-29 A-U (decided 2026-10-06) makes a written name whose lookup
    reaches two different providers at one open level the surface layer's static
    rejection (C# `DiagnosticCode.AmbiguousOpen`), whether or not evaluation
    demands it, while `ambiguousOpen` stays the evaluator's verdict for a lookup
    only evaluation decides (a dot fallback the receiver decides) and for a
    host-built tree.

    NOTE: This function is used only for ordinary algorithms without an explicit
    parameter-pattern list.  Explicit ordinary algorithms and conditional branch
    bodies do NOT use implicit parameter inference.  Their written pattern in
    `Name(...)` is the complete input specification; free identifiers in the
    body must resolve lexically or produce an error.  Pattern-bound names are
    rewritten to `Expr.param` by the surface layer directly, without using this
    function. -/
def shouldTreatAsImplicitParam (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Bool := do
  match <- evalAttempt (lookupLexical a name ctx) with
  | .ok _ => .ok false                      -- Name resolves → NOT a param
  | .error (Error.unknownName _) => .ok true  -- Name doesn't resolve → IS a param
  | .error e => .error e                    -- Propagate other errors (ambiguousOpen, etc.)


--------------------------------------------------------------------------------
-- Surface syntax support: owner-aware binding selection
--------------------------------------------------------------------------------

/-- One level of the surface layer's ordered OWNER CHAIN for a bare-name
    occurrence: the scopes enclosing that occurrence, innermost first.

    `parameters` are the parameter BINDINGS the level owns by NAME RESOLUTION —
    an algorithm's written and inferred parameters, or a conditional branch
    body's pattern binders. `properties` are the property names the level
    declares. Both are OWNED declarations; `opens` are deliberately absent,
    because they are not owned by the level and keep the separate later fallback
    policy of `lookupLexicalProperty`.

    `forwarded` are the parameters AUTOMATIC PARAMETER FORWARDING added to the
    level (Q-04, decided 2026-09-28): parameters the level receives only so that
    it can hand them on to a referenced callee that needs them, because no
    parameter binding of that name was available (`forwardingSource` below).
    They complete the level's signature for its callers — and a property of the
    same name still conflicts with them (`conflictingOwnedNames`) — but they are
    NEVER what a written name denotes: the owner walk does not consult them, so
    automatic forwarding cannot change what an existing name refers to. (Before
    the decision the surface layer re-selected every binding against the
    completed signatures, so a lifted parameter captured same-named written
    references — PV-01.)

    A CALLABLE ALIAS (FWD-02, binding indirection, decided 2026-10-01;
    `Algorithm.alias`) contributes no parameters at all: its callable is its
    target's, and it declares no signature of its own, so its level lists only the
    properties its own body declares — renaming the target's binders can never make
    the alias a declaration error.

    A `ScopeCtx` cannot serve as this chain: it carries `props` but no
    parameters, since by the time an `Algorithm` exists every ancestor-parameter
    reference in it is already an `Expr.param` and the binding lives in
    `ValEnv`. The chain is therefore surface-layer information, supplied to the
    walk while the front end is still deciding `param` vs `resolve`.

    The CHAIN, not a separately counted depth, is what says which owner is
    nearer: level `i` is nearer than level `j` exactly when `i < j`. -/
structure OwnerLevel where
  parameters : List Ident
  properties : List Ident
  forwarded : List Ident := []
  deriving Repr, DecidableEq

/-- Every parameter the level's callers bind: its name-resolution parameters and the
    ones automatic forwarding added (the completed signature). -/
def OwnerLevel.signature (level : OwnerLevel) : List Ident :=
  level.parameters ++ level.forwarded

/-- Surface declaration validity, checked after parameter-signature completion and
    before evaluation. Each property whose name is bound by this or an enclosing owner's
    completed signature — forwarded parameters included; a callable alias declares no
    parameters (see `OwnerLevel`) — is a declaration error,
    regardless of visibility or reference order. Pattern binders belong to their branch
    body. Open targets are not declarations and never conflict, but their HEAD name obeys
    the same owner chain (`elaborateOpenHead`). The surface layer reports each written
    conflicting declaration at its source name.
    C#: ParameterPropertyCollisionValidator. This is a front-end validity boundary;
    raw/recovery AST evaluation and lookup do not substitute for this check. -/
def conflictingOwnedNames (owner : OwnerLevel) (ancestors : List OwnerLevel := []) : List Ident :=
  owner.properties.filter fun name =>
    owner.signature.contains name || ancestors.any (fun outer => outer.signature.contains name)

def validOwnedDeclarations : List OwnerLevel -> Bool
  | [] => true
  | owner :: ancestors =>
      (conflictingOwnedNames owner ancestors).isEmpty && validOwnedDeclarations ancestors

/-- What the owner walk selects for a bare name, with the position of the
    DECIDING level in the supplied chain (0 = the occurrence's own body). -/
inductive OwnedDeclaration where
  | none
  | parameter (level : Nat)
  | property  (level : Nat)
  deriving Repr, DecidableEq

/-- THE owner walk, and the specification the surface layer's
    parameter/receiver classification and the editor's visible-name view all
    implement (C#: `ElaboratedScopeLookup.SelectOwnedDeclaration`).

    Search outward by owning scope: the first level that DECLARES `name` wins,
    and within that level an established PARAMETER takes precedence over a
    property. Consequences, in the order they matter:

    * a captured ancestor parameter beats a property owned by any FARTHER scope
      (the root's, and the prelude's — the prelude is simply the outermost
      property level, so `F(pi) = { pi + 1 }` binds the parameter);
    * a nearer property beats an outer parameter in an invalid recovery tree;
    * a level owning BOTH is invalid source (`validOwnedDeclarations`), but its
      recovery tree still selects the parameter consistently for direct and nested
      references, so editor behavior stays deterministic;
    * with several enclosing parameters of one name, the nearest wins, because
      it is reached first.

    `.none` means no owner declares the name; the caller then applies the
    unchanged lookup/promotion policy — `shouldTreatAsImplicitParam`
    above for a body that infers implicit parameters, and an ordinary
    `Expr.resolve` otherwise. -/
def selectOwnedDeclarationFrom : Nat -> List OwnerLevel -> Ident -> OwnedDeclaration
  | _, [],             _    => .none
  | i, level :: outer, name =>
      if level.parameters.contains name then .parameter i
      else if level.properties.contains name then .property i
      else selectOwnedDeclarationFrom (i + 1) outer name

def selectOwnedDeclaration (chain : List OwnerLevel) (name : Ident) : OwnedDeclaration :=
  selectOwnedDeclarationFrom 0 chain name

/-- Whether a bare-name occurrence elaborates to `Expr.param name` (a runtime
    parameter read, resolved through the inherited supplied cells and `ValEnv`) rather
    than to `Expr.resolve name` (ordinary lexical property lookup). The value
    and the callable view of one occurrence share this single decision: the
    elaborated node is the same in both positions. -/
def elaboratesToParameter (chain : List OwnerLevel) (name : Ident) : Bool :=
  match selectOwnedDeclaration chain name with
  | .parameter _ => true
  | _            => false

/-- Static-open ownership (SYN-03 / F2). `open` is STATIC — it never opens a
    runtime value — but lexical ownership still applies to the target name:
    the HEAD of a static open target (`Lib` in `open Lib` or `open Lib.Sub`)
    is a bare-name occurrence like any other, so the surface layer classifies
    it with the SAME owner walk. When the nearest established binding is a
    parameter — written, inferred, collecting, grouped, a branch binder, or any
    of these captured from an enclosing owner (never one automatic forwarding
    added: `OwnerLevel.forwarded` owns no name) — that parameter owns the name
    and the head elaborates to `.param`, exactly as every other
    parameter-owned occurrence does. A `.param` head is NOT an open form
    (`Expr.openForm?` maps it to `none`), so open resolution rejects the
    target with `badOpenForm` and can never reach a farther same-named
    property: whether such a declaration exists changes nothing. The surface
    layer reports the parameter-owned head before evaluation (C#:
    `ParameterDetector.ClassifyOpenTargetHeads`,
    `DiagnosticCode.OpenTargetIsParameter`); `resolveAlgForOpen` therefore
    receives `.resolve` heads only for names no callable parameter owns, and
    its direct lexical lookup (`lookupLexicalDirect`) is sound for them.
    The chain carries CALLABLE bindings: the never-called program root's
    phantom signature is omitted from it by the surface layer (its names are
    unresolved root inputs, reported as such by evaluation, not parameters
    that could own an open target). -/
def elaborateOpenHead (chain : List OwnerLevel) (name : Ident) : Expr :=
  if elaboratesToParameter chain name then .param name else .resolve name

--------------------------------------------------------------------------------
-- Surface syntax support: implicit argument resolution
--------------------------------------------------------------------------------

/- **Implicit argument resolution** (surface syntax pass — runs after parameter
   detection):

   When a property body contains a bare value-position reference to a sibling
   property that REQUIRES supplied arguments — one an ordinary call supplying
   zero arguments could not bind (`liftsBareValueReference` below) — the
   surface layer rewrites that reference into an explicit call, passing the
   sibling's parameter-pattern captures as arguments. Each argument is the
   PARAMETER binding the referencing body can already reach under that name —
   its own, or an enclosing owner's captured parameter or branch binder — and
   only a name no parameter binding supplies is lifted into the referencing
   property's own parameter-pattern list, as a FORWARDED parameter that no
   written name denotes (`forwardingSource` below; Q-04, decided 2026-09-28:
   automatic parameter forwarding must not change what an existing name refers
   to). Properties, opened names and builtins are never forwarded as
   parameters.

   A reference to a sibling that ACCEPTS zero supplied arguments — no
   parameters, or only a top-level collecting parameter such as `Roll(*xs)` —
   is never rewritten, in any position (Q-03, decided 2026-09-28): declaring a
   parameter does not by itself make a bare reference a call. It stays
   `.resolve`, the zero-argument value demand that `zeroArgumentDemandError?`
   accepts and `isCacheableZeroArgPropertyAlgorithm` sends through the property
   cache, so `Roll == Roll` reads ONE value; only a written call (`Roll()`,
   `Roll(args)`) evaluates afresh. Before the decision the surface pass lifted
   every sibling that DECLARED a parameter, so a collecting-only sibling in an
   operator, list, index, spread, strict-Math or alias position became the
   fresh call `Roll(xs*)` and bypassed the cache that its neutral positions
   read. The evaluator was never involved: it evaluates whichever tree the
   surface pass produces, and the specification identity
   `lifts_bare_value_reference_iff_not_cacheable` (`KatLangArityLaws.lean`, definitional) states
   that a signature the specification leaves unlifted is one the cache eligibility predicate
   admits (the C# resolver's agreement rests on tests).

   Formula lifting is by BINDING NAME, regardless of how many times a name
   occurs in the sibling's parameter patterns (decided 2026-09-29, reversing
   the same day's Q-72 refusal): the referencing body receives ONE parameter
   per name (first occurrence first, skipping names already bound, inside a
   group too), and the rewritten call supplies that one binding to every
   occurrence — `P(x, x) = x` / `D = [P][0]` becomes `D(x) = [P(x, x)][0]`,
   exactly as `H = F + G` with `F(x)` and `G(x)` becomes
   `H(x) = F(x) + G(x)`. The evaluator binds `P`'s two slots as it binds any
   call: both read the same caller binding, so nothing is merged — the
   repeated-name constraint (Q-05; the binder's `bindNeedName`) concerns
   independently supplied arguments.

   THE ALIAS AND BARE-FORWARDING RULES (FWD-02, decided 2026-09-29–30; binding
   indirection 2026-10-01) come first: a body whose ONE written row is a bare
   reference to a callable that DECLARES parameterized structure
   (`Algorithm.declaresParameterizedStructure`) is not a formula. An open body is
   a CALLABLE ALIAS (`Algorithm.alias`) — `A = P` names `P`'s callable itself,
   with no wrapper and no copied signature, so a call through it is `P`'s own
   call with `P`'s two independent arguments. A written parameter list or a
   clause branch is BARE
   FORWARDING (`bareForwardingRow`): each of the callee's parameters is supplied
   from an EXISTING compatible binding of the SAME NAME — `Q(x) = P` is
   `Q(x) = P(x, x)`, `G(x, y) = F` with `F(y, x)` is `F(y, x)` — never renamed,
   never matched by position, never added to the closed list, and never
   reshaped from same-named leaves (`G(x) = Single` with `Single([x])` is
   rejected). The explicit call `A(p) = F(p)` is deliberately different: an
   ordinary written call, whose arguments need not match the callee's names. A
   written call `G = F(exprs)` is an ordinary formula whose parameters are the
   free names written in `exprs`.

   Example:
     Surface:   `{ A = x + 1  B = A * 2 }`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

     Surface:   `{ A = x + 1  F(x) = { B = A * 2  B } }`
     After resolution: B.params = [], B.output = [Call(A, [Param(x)]) * 2]
       (the `x` is F's: B reuses the captured parameter instead of lifting its own)

     Surface:   `{ A(*xs) = xs.count  B = A * 2 }`
     After resolution: B.params = [], B.output = [Resolve(A) * 2]

   Recursive parameter patterns are preserved by this surface pass: lifting
   `x, *items`, `(*items)`, or `((*history), previous)` keeps that shape
   instead of reconstructing ordinary capture parameters from flattened names.
   A narrow forwarding rule also permits a bare helper reference with one
   forwardable variadic supply — a lone collector inside the helper's one
   group, `H((*xs))` (a helper whose only parameter is a top-level collector
   accepts zero supplied arguments and is never rewritten) — to use a
   containing algorithm's single top-level variadic supply by shape rather
   than by capture-name equality. This is not a general positional
   parameter-matching rule.

   **Transitive ordering invariant**: Properties must be processed in dependency
   order. If property B references property A (even if A currently has zero
   parameters), then A must be resolved before B, so that A's final parameter
   list (which may itself have been augmented by transitive dependencies) is
   visible when resolving B's implicit arguments.

   This ordering is computed by topological sort over ALL bare sibling property
   references — not just those with parameters at detection time — because a
   property with initially zero parameters may acquire parameters through its
   own transitive dependencies during resolution.

   Formally:
     Let G = (properties, edges) where edge (B, A) exists iff B's output
     expressions contain a bare Resolve(A) and A is a sibling property.
     Process properties in topological order of G.
     At each step, the parameter map is updated with the processed property's
     final parameter-pattern signature before processing subsequent dependents.

   Cycles (mutually recursive siblings) are not excluded from lifting: each
   cycle — a strongly connected component of G — is ordered as ONE unit,
   processed once every sibling its members reference outside it has been,
   its members in DECLARATION order, each seeing the signatures completed so
   far (the C# `PropertyDependencyGraph.TopologicalOrder`). That fallback is
   confined to the cycle's members: a property that references a cycle is
   not part of it, so it is processed after all of the cycle's members and
   sees their final signatures, whatever the declaration order. C# also
   anticipates reads through soft preferences: when those close a cycle
   around hard units, the combined component settles before outside
   consumers, retaining the hard scheduler's order inside it (no fixed
   point or call recomputation). This is the
   one documented way two reaches of a node can observe different sibling
   signatures (the "sibling CYCLE" exception of the shared-DAG guarantee in
   `docs/design/language-rules/evaluator-and-hosting.md`). -/

/-- **Implicit-lifting eligibility** (Q-03, decided 2026-09-28; surface syntax
    support — the specification of the surface pass's one lifting decision).
    A bare value-position reference is rewritten into an implicit forwarding
    call exactly when its callee's lifting signature REQUIRES supplied
    arguments: when `ParameterPattern.minimumSuppliedSlots` — the binder's own
    arity rule, the very count `Algorithm.acceptsZeroSuppliedArguments` reads —
    is nonzero. A signature that accepts zero supplied arguments (no pattern, or
    only a top-level collecting capture) is never lifted: its reference stays
    the cached zero-argument value demand. One predicate therefore decides both
    halves, and they cannot disagree about a callable (see the definitional identity
    `lifts_bare_value_reference_iff_not_cacheable`).

    The argument is the callee's LIFTING signature (`Algorithm.liftingSignature?`,
    one contract for every kind since the unified formula-lifting law of
    2026-09-30): a user algorithm's `parameterPatterns`, a builtin's callable
    interface, a clause family's derived whole-slot signature. C#:
    `ImplicitArgumentResolver.RequiresSuppliedArguments` over
    `CallableSignature.AcceptsZeroSuppliedArguments` /
    `ParameterPattern.AcceptsZeroSuppliedSlots`. -/
def liftsBareValueReference (signature : List ParameterPattern) : Bool :=
  ParameterPattern.minimumSuppliedSlots signature != 0

/-!
### The unified formula-lifting law (decided 2026-09-30)

In an inferring formula, a resolved callable reference is lifted when that occurrence is used as
a VALUE, and its lifting signature is derived from the resolved callable's contract, independent
of the callable's category or the route that resolved it. Two operations, both specified here and
implemented by the C# front end (Lean has no front end):

- `LiftingRole` / `liftingSlotRole` — the role a slot gives the reference that fills it, decided
  by the slot's IMMEDIATE consumer (C# `FormulaLiftingRoles`). Every operator operand, index part,
  spread operand, list and capture element and output row is a VALUE slot; a call's callee is
  CALLABLE; a call's arguments take the roles `liftingSlotRole` gives them. A compound expression
  in a callable slot is still examined: its own children take the roles of THEIR consumers
  (`Twice(A)` keeps `A`, `Twice(A + 0)` lifts it). Laziness does not change a role: an `if` branch
  is a value slot whether or not a run selects it, exactly as a free name written there is a
  parameter (PAR-03).
- `Algorithm.liftingSignature?` — the one lifting signature of every kind.

A lone bare row is not a formula (FWD-02 completes it — a callable alias or bare forwarding,
`Algorithm.declaresParameterizedStructure`), and the never-called root keeps a bare row as the
callable's own rejection. A reference to a callable alias takes the roles and the lifting
signature of the alias's NORMALIZED TARGET (the surface pass resolves the chain first), never of
the alias itself: no alias-specific role exists. -/

/-- The role a slot gives the reference that fills it (C#: `LiftingRole`). -/
inductive LiftingRole where
  | value
  | callable
  deriving Repr, BEq, DecidableEq

/-- What a consumer needs to know about the callable it calls: its KIND, which elaboration never
    changes (C#: `LiftingCalleeKind`). A `strictValue` callee is a Math member or a host
    operation (neither is modeled here beyond this kind). -/
inductive LiftingCalleeKind where
  | dynamic
  | user
  | family
  | builtin (b : Builtin)
  | strictValue
  deriving Repr, BEq

/-- The callee KIND of a resolved callable (C#: `FormulaLiftingRoles.OfAlgorithm`), which decides the
    roles of a call's argument positions (`liftingSlotRole`). A callable ALIAS has no kind of its own:
    a reference to it takes the kind — and so the roles — of its NORMALIZED TARGET (X-45: `A = abs` /
    `K = A(Inc)` gives `Inc` the value role `abs` gives it). Math members and host operations are
    `strictValue` callees, a kind the surface pass reads from their identity; Lean models them only
    as that kind, so they are not derived from an algorithm here. -/
def Algorithm.liftingCalleeKind? : Algorithm -> Option LiftingCalleeKind
  | .mk _ _ _ _ _ _ => some .user
  | .builtin b => some (.builtin b)
  | .conditional _ _ _ _ => some .family
  | .alias _ _ _ _ _ _ => none

/-- The role of supplied position `position` of a builtin: only a callback keeps its callable
    identity. The collection, the value controls and a SURPLUS position beyond the signature have
    the static VALUE role (at run time a surplus slot is never demanded: cardinality fails first),
    just as every argument of a Math member, a host operation and a clause family is a value
    whatever the call's arity, so no role depends on how many arguments a call supplies. A META
    position (`builtinMetaAt`: a loop's step) transports its supplied cell, the CALLABLE role
    every META parameter has, and every other position is a value; `if`, `atoms` and `range`
    take values only. -/
def builtinLiftingSlotRole (b : Builtin) (position : Nat) : LiftingRole :=
  match sequenceBuiltinMetadata? b with
  | some metadata => if metadata.slotRole position == .callback then .callable else .value
  | none => if builtinMetaAt b position then .callable else .value

/-- Whether every position of a builtin is a value slot (a position after a spread slot is known
    only at run time, so it is a value slot only then). -/
def builtinEverySlotIsValue (b : Builtin) : Bool :=
  match sequenceBuiltinMetadata? b with
  | some metadata => metadata.suffixArgs.all (fun suffix => suffix.kind != .algorithm)
  | none => !builtinDeclaresMeta b

/-- THE ROLE TABLE of a call's supplied positions (C#: `FormulaLiftingRoles.SlotRole`): every
    argument of a clause family, a Math member and a host operation has the static VALUE role (for
    a family a role retained by NEED-05: at run time it demands only what its patterns inspect or
    its selected body consumes, PAT-07/NEED-04); a builtin reads its registry role; a user callable's argument stays
    NEUTRAL — its binder decides at run time, a plain capture keeping both channels — and so does
    a callee known only at run time. `positionKnown` is false once a spread slot precedes it. -/
def liftingSlotRole (callee : LiftingCalleeKind) (position : Nat) (positionKnown : Bool) : LiftingRole :=
  match callee with
  | .family | .strictValue => .value
  | .builtin b =>
      if positionKnown then builtinLiftingSlotRole b position
      else if builtinEverySlotIsValue b then .value else .callable
  | .user | .dynamic => .callable

/-- The top-level argument positions of a clause head: the head's own argument list
    (`sequenceValue`), or its lone pattern (`Pattern.topLevelArity`). -/
def Pattern.topLevelPositions : Pattern -> List Pattern
  | .sequenceValue ps => ps
  | p => [p]

/-- The name one clause votes for a position: the plain binder it binds there. A literal, a
    structural pattern and a binderless group name nothing. -/
def Pattern.positionName? : Pattern -> Option Ident
  | .bind x => some x
  | _ => none

/-- The name the clauses agree on for position `position`: every vote equal, at least one vote. -/
def familyPositionName? (heads : List Pattern) (position : Nat) : Option Ident :=
  match heads.filterMap (fun head => (head.topLevelPositions[position]?).bind Pattern.positionName?) with
  | [] => none
  | first :: rest => if rest.all (· == first) then some first else none

/-- A CLAUSE FAMILY'S LIFTING SIGNATURE (decided 2026-09-30): one whole-value slot per top-level
    argument position (the family's common arity, PAT-03), each named by the plain parameter the
    clauses that bind it agree on, the names of different positions distinct. The lifted call hands
    the family the caller's arguments whole, so dispatch is exactly the explicit call's. A family
    whose clauses leave a position unnamed, name it differently, or give two positions one name has
    none (`none`): it stays explicitly callable, and a formula that would lift it is the C# front
    end's `UnliftableClauseFamily`. No name is ever invented.
    C#: `ImplicitArgumentResolver.DeriveFamilyLiftingSignature`. -/
def familyLiftingSignature? (branches : List CondBranch) : Option (List ParameterPattern) :=
  match branches with
  | [] => none
  | first :: _ =>
      let heads := branches.map (·.pattern)
      let arity := first.pattern.topLevelArity
      if heads.any (fun head => head.topLevelArity != arity) then none
      else
        let names := (List.range arity).map (familyPositionName? heads)
        let named := names.filterMap id
        if named.length == arity && named.eraseDups.length == named.length
        then some (named.map (fun name => ParameterPattern.capture { name := name }))
        else none

/-- A builtin's callable interface as formula lifting reads it: THE builtin signature
    (`builtinSignature`, META-S3-3; C#: `PlainSignature`), so `while(meta step)` and
    `repeat(meta step, count)` lift and forward exactly as their runtime binds. -/
def builtinLiftingSignature (b : Builtin) : List ParameterPattern :=
  builtinSignature b

/-- THE ONE LIFTING SIGNATURE of every algorithm kind (the unified formula-lifting law): a user
    algorithm's parameter patterns, a builtin's callable interface, a clause family's derived
    whole-slot signature (or none). It is also the callable's FORWARDING CONTRACT — the names
    bare forwarding supplies by (`bareForwardingRowOf`). A callable alias has none of its own:
    every callable question is asked of its NORMALIZED TARGET (the surface pass resolves the
    alias chain first, exactly as the evaluator does, `resolveAliasTarget`), so lifting and
    forwarding through an alias are the target's, never a copied signature.
    C#: `ImplicitArgumentResolver.TryResolveLiftable`. -/
def Algorithm.liftingSignature? : Algorithm -> Option (List ParameterPattern)
  | .mk _ parameters _ _ _ _ => some parameters
  | .builtin b => some (builtinLiftingSignature b)
  | .conditional _ _ branches _ => familyLiftingSignature? branches
  | .alias _ _ _ _ _ _ => none

/-- **Lone-row eligibility** (FWD-02, binding indirection — decided 2026-10-01; surface syntax
    support — the specification of the surface pass's decision for a body whose ONE written
    row is a bare reference). Such a row names the callable ITSELF, so the decision reads the
    DECLARED callable structure of the ONE identity name resolution selects (owner walk →
    prelude → opens → structural dot path, looking through aliases to the normalized target),
    never the lookup route and never zero-argument acceptance: a callable that DECLARES
    PARAMETERIZED STRUCTURE — every builtin (`if`, the callback builtins and the loops
    included), every clause family (nameable or not), a user algorithm with at least one
    parameter pattern (`Only(*xs)` included, although `Only()` is legal), a Math member or a
    host operation — makes an OPEN body a callable ALIAS (`Algorithm.alias`: binding
    indirection, no wrapper, no inherited signature) and a CLOSED body bare forwarding
    (`bareForwardingRowOf`). Since M4★ (ALIAS-UNIFY-1, October 2026) this gate decides only the
    CLOSED body: an OPEN body whose one row is a resolved algorithm reference is an alias whatever
    the target's arity — `A = Z` with a zero-parameter `Z` is a transparent reference whose bare read
    is `Z`'s own (OD-E) — while a closed body over a callee that declares nothing stays the bare
    name (`F = 10` / `A(p) = F` is simply 10). C#:
    `ImplicitArgumentResolver.DeclaresParameterizedStructure`. -/
def Algorithm.declaresParameterizedStructure : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => !parameters.isEmpty
  | .builtin _ => true
  | .conditional _ _ _ _ => true
  | .alias _ _ _ _ _ _ => true

/-- The tree of a WRITTEN sequence group `(e1, …, en)` (SYN-06): `()` for no
    items, the one item itself for a lone non-spread item (a one-slot group IS
    its content; there is no one-item sequence value), and otherwise a capture of
    the slots — a lone spread slot `(xs*)` included, which a group keeps.
    C#: `ImplicitArgumentResolver.BuildSequenceArgument`. -/
def sequenceArgument : List Expr -> Expr
  | [] => .emptySequence 0
  | [only] =>
      match only with
      | .sequenceSpread operand => .capture [.sequenceSpread operand]
      | _ => only
  | first :: second :: rest => .capture (first :: second :: rest)

mutual
  /-- **Pattern reconstruction** (FWD-02; surface syntax support — the ONE
      reconstruction the alias and bare-forwarding rules share). The argument that
      rebuilds one parameter pattern from its own bindings — exactly the argument a
      programmer would write:

      * a fixed capture is its binding, `x`;
      * a collecting capture re-spreads the items it collected, `xs*`, at any
        level — so a `[first, *middle, last]` pattern rebuilds
        `[first, middle*, last]`;
      * a sequence pattern rebuilds a sequence (`sequenceArgument`) and a list
        pattern a list, of the same shape, at every depth — never the other kind;
      * the unpacking receiver (never written in a signature) rebuilds the list of
        its items.

      BARE FORWARDING rebuilds a callee's structural parameter this way only when the
      forwarding body declares the SAME pattern (`bareForwardingArgument`). (A callable
      alias rebuilds nothing: it IS its target's callable, `Algorithm.alias`.)
      C#: `ImplicitArgumentResolver.BuildPatternArgument`; `CoreTests/AliasForwarding.lean`. -/
  def ParameterPattern.sourceArgument : ParameterPattern -> Expr
    | .capture parameter =>
        match parameter.kind with
        | .normal | .metaRef => .param parameter.name
        | .collecting => .sequenceSpread (.param parameter.name)
    | .sequenceValue items => sequenceArgument (ParameterPattern.sourceArguments items)
    | .listValue items => .listLiteral (ParameterPattern.sourceArguments items)
    | .unpacking items => .listLiteral (ParameterPattern.sourceArguments items)

  /-- The rebuilt arguments of a pattern list: one per pattern, in order. -/
  def ParameterPattern.sourceArguments : List ParameterPattern -> List Expr
    | [] => []
    | pattern :: rest => ParameterPattern.sourceArgument pattern :: ParameterPattern.sourceArguments rest
end

mutual
  /-- Whether two parameter patterns declare the same CONTRACT — the same kind and
      shape, the same names and the same collectors at every depth. Bare forwarding
      compares whole TOP-LEVEL patterns by this relation, never their leaf names alone
      (C#: `ParameterPattern.ContractComparer`, never display equality). -/
  def ParameterPattern.sameContract : ParameterPattern -> ParameterPattern -> Bool
    | .capture left, .capture right => left.name == right.name && left.kind == right.kind
    | .sequenceValue left, .sequenceValue right => ParameterPattern.sameContracts left right
    | .listValue left, .listValue right => ParameterPattern.sameContracts left right
    | .unpacking left, .unpacking right => ParameterPattern.sameContracts left right
    | _, _ => false

  /-- Pairwise `sameContract` over two pattern lists of equal length. -/
  def ParameterPattern.sameContracts : List ParameterPattern -> List ParameterPattern -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        ParameterPattern.sameContract left right && ParameterPattern.sameContracts lefts rights
    | _, _ => false
end

/-- BARE FORWARDING's verdict for one callee parameter pattern (`bareForwardingArgument`). -/
inductive BareForwardingVerdict where
  /-- An existing compatible binding supplies the parameter: this argument. -/
  | supplied (argument : Expr)
  /-- A collector that no binding of its name supplies: it receives no argument. -/
  | optional
  /-- No existing compatible binding supplies the parameter: the definition is a
      front-end error (C# `DiagnosticCode.UnforwardableParameter`). -/
  | unforwardable
  deriving Repr

/-- The argument that forwards an existing binding named like the capture
    `destination`: a collecting SOURCE binding re-spreads into a collecting destination
    (FWD-01, `spread (collect S) = S`); every other pair passes the binding as ONE
    argument, unchanged — a re-spread needs BOTH a collecting source and a collecting
    destination (FWD-02; `bare_forwarding_mixed_kind_pairs_pass_the_binding_whole`). -/
def bareForwardedBinding (destination : CallableParameter) (sourceKind : ParameterKind) : Expr :=
  if destination.kind == .collecting && sourceKind == .collecting then
    .sequenceSpread (.param destination.name)
  else
    .param destination.name

/-- **Bare forwarding** (FWD-02, decided 2026-09-30; surface syntax support — the
    specification of the surface pass's decision for a CLOSED body whose ONE written
    row is a bare reference to a callable that declares parameters: a written
    parameter list `A(p) = F` or a clause branch `A(head) = F`). Bare forwarding
    REUSES EXISTING COMPATIBLE BINDINGS BY NAME: it never renames a binding, never
    adds one to the closed list, never matches by position, and never converts an
    incompatible top-level parameter pattern because nested leaf names coincide. The
    inputs:

    * `own` — the closed body's own TOP-LEVEL parameter patterns (a branch: its
      literal-free top-level head items, `Pattern.bareForwardingOwn`);
    * `ownNames` — every name the body binds, at any depth;
    * `captured` — the ENCLOSING parameter bindings a written name would denote
      in the body when the body binds no such name itself (Q-04: the
      `.capturedParameter` results of `forwardingSource`), with their kinds.

    One callee parameter pattern is then:

    * a capture `n`: supplied by the body's own top-level capture `n`
      (`bareForwardedBinding` decides a re-spread from that SOURCE's kind); if the
      body binds `n` only INSIDE one of its structural patterns, that `n` is an
      element, not a whole-value parameter — unforwardable; otherwise supplied by
      the enclosing binding `n`, if any; otherwise a collector is OPTIONAL (it
      accepts no argument) and a fixed capture is unforwardable;
    * a structural pattern: supplied only by one of the body's own top-level
      patterns with the SAME contract (`ParameterPattern.sameContract`), rebuilt as
      itself (`ParameterPattern.sourceArgument`) — never assembled from same-named
      leaves, and never from enclosing bindings, which are plain named values.

    So `F(p) = p * 2` / `A(p) = F` forwards `A.p` to `F.p`, while `F(q) = q * 2` /
    `A(p) = F` is rejected (never `F(p)`), `F(p, q)` / `A(p) = F` is rejected (never
    an inferred `q`), `F(y, x)` / `G(x, y) = F` is `F(y, x)` BY NAME (never positional),
    `Single([x])` / `G(x) = Single` is rejected while `G([x]) = Single` forwards, and an
    unused parameter of the body (`A(p, unused) = F`) stays unused. The explicit call
    `A(p) = F(p)` is an ordinary written call and never reaches this rule; formula
    lifting (`forwardingSource`) is a separate mechanism, which infers into an OPEN
    body what bare forwarding refuses to add to a closed one.
    C#: `ImplicitArgumentResolver.BareForwardingArgument`;
    `KatLangArityLaws.lean`, `CoreTests/AliasForwarding.lean`. -/
def bareForwardingArgument (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) : ParameterPattern -> BareForwardingVerdict
  | .capture parameter =>
      match ParameterPattern.topLevelCaptureKind? parameter.name own with
      | some kind => .supplied (bareForwardedBinding parameter kind)
      | none =>
          if ownNames.contains parameter.name then
            .unforwardable
          else
            match captured.find? (fun binding => binding.name == parameter.name) with
            | some binding => .supplied (bareForwardedBinding parameter binding.kind)
            | none => if parameter.kind == .collecting then .optional else .unforwardable
  | pattern =>
      if own.any (ParameterPattern.sameContract pattern) then
        .supplied (ParameterPattern.sourceArgument pattern)
      else
        .unforwardable

/-- Bare forwarding of a whole callee signature: the supplied arguments in the
    callee's parameter order (an optional collector contributes none), or `none` when
    any parameter is unforwardable — the front-end rejection. -/
def bareForwardingArguments (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) : List ParameterPattern -> Option (List Expr)
  | [] => some []
  | parameter :: rest =>
      match bareForwardingArgument own ownNames captured parameter,
            bareForwardingArguments own ownNames captured rest with
      | .supplied argument, some arguments => some (argument :: arguments)
      | .optional, some arguments => some arguments
      | _, _ => none

/-- The row a bare-forwarding body elaborates to: the call of `callee` with the
    forwarded arguments; the BARE NAME when nothing is forwarded (every callee
    parameter an optional collector, so the callee works with no arguments and the
    row is Q-03's cached value read, never an invented call); or `none` when a
    parameter is unforwardable (C# `DiagnosticCode.UnforwardableParameter`, the row
    left as written). -/
def bareForwardingRow (callee : Ident) (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (signature : List ParameterPattern) : Option Expr :=
  match bareForwardingArguments own ownNames captured signature with
  | none => none
  | some [] => some (.resolve callee)
  | some arguments => some (.call (.resolve callee) arguments)

/-- Why a closed lone row cannot bare-forward its callee. -/
inductive BareForwardingRejection where
  /-- A callee parameter that no existing compatible binding of its name supplies
      (C# `DiagnosticCode.UnforwardableParameter`). -/
  | unforwardableParameter
  /-- The callee — through every alias, its NORMALIZED target — has NO forwarding contract
      at all: an unnameable clause family names no input to forward by (narrowed Q-77,
      decided 2026-10-01; C# `DiagnosticCode.UnforwardableCallable`). -/
  | noForwardingContract
  deriving Repr, DecidableEq

/-- **Bare forwarding of a callable** (FWD-02 with narrowed Q-77, decided 2026-10-01): the row a
    CLOSED body whose one row is the bare `callee` elaborates to, given the callee's NORMALIZED
    target. The forwarding contract is the target's lifting signature
    (`Algorithm.liftingSignature?`, identity-keyed, so an alias, an opened or dotted member, a
    builtin, a Math member, a host operation and a nameable family forward alike); a target
    without one — an unnameable clause family — is the front-end error
    `noForwardingContract`, never a silent zero-argument demand. A callable alias of such a
    family is still a valid ALIAS (`unnameable_family_can_be_aliased`): aliasing needs callable
    identity, forwarding needs names. C#: `ImplicitArgumentResolver.TryCompleteLoneCalleeRow`. -/
def bareForwardingRowOf (callee : Ident) (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (target : Algorithm) : Except BareForwardingRejection Expr :=
  match target.liftingSignature? with
  | none => .error .noForwardingContract
  | some signature =>
      match bareForwardingRow callee own ownNames captured signature with
      | some row => .ok row
      | none => .error .unforwardableParameter

/-- A clause branch's OWN inputs for bare forwarding: a top-level sequence pattern IS
    the branch's parameter list and any other head is its one parameter; an item that
    holds a literal at any depth declares no literal-free pattern, so it offers
    nothing (its binders still count as bound names, `Pattern.boundNames`). C#:
    `BareForwardingSources.OfBranchHead`. -/
def Pattern.bareForwardingOwn (head : Pattern) : List ParameterPattern :=
  let items := match head with
    | .sequenceValue items => items
    | other => [other]
  items.filterMap Pattern.parameterPattern?

/-- Where AUTOMATIC PARAMETER FORWARDING takes the argument for one callee parameter
    (Q-04, decided 2026-09-28): see `forwardingSource`. -/
inductive ForwardingSource where
  /-- The referencing body binds the name itself: a written or inferred parameter, or
      its branch binder. -/
  | ownParameter
  /-- An enclosing owner binds it (at chain level `level`, a clause-branch binder
      included): forwarding hands the callee THAT binding. -/
  | capturedParameter (level : Nat)
  /-- No parameter binding exists and the body infers its parameters: it receives a new
      FORWARDED parameter of that name (`OwnerLevel.forwarded`). -/
  | forwardedParameter
  /-- No parameter binding exists and the body's inputs are CLOSED (a written parameter
      list or a branch pattern): nothing is forwarded. -/
  | unavailable
  deriving Repr, DecidableEq

/-- **Automatic parameter forwarding** (Q-04, decided 2026-09-28; surface syntax
    support — the specification of the surface pass's one forwarding decision).
    THE LAW: automatic parameter forwarding must not change what an existing name
    refers to. Forwarding therefore reuses PARAMETER bindings only: when a lifted
    reference forwards a callee parameter `name` from the referencing body — level 0
    of `chain`, the body's name-resolution owner chain, innermost first — the argument
    is the binding the owner walk (`selectOwnedDeclaration`) gives a WRITTEN occurrence
    of `name` there, if that binding is a parameter: the body's own
    (`.ownParameter`), or an accessible captured parameter of an enclosing owner, a
    clause-branch binder included (`.capturedParameter`). Properties, opened names,
    module members and prelude builtins are never forwarded as parameters: when the
    walk finds a property, or nothing, an inferring body (`inferring = true`) receives a
    new forwarded parameter and a closed body gets nothing. So a body never acquires a
    parameter that would capture a name it already reads from an enclosing owner — the
    former rule, which lifted every callee parameter the body did not bind itself and
    then re-selected the written references against the completed signature, made
    `A = y + 1` / `F(y) = { G = y * 1000 + A ⏎ H(y) = G ⏎ H(100) }` / `F(3)` give 100101
    where the inlined helper gives 3004 (PV-01) — and a forwarded parameter is never
    what a written name denotes (`OwnerLevel.forwarded`; the owner walk does not read
    it). C#: `ImplicitArgumentResolver.ForwardableParameters` (the enclosing parameter
    bindings), `LiftSignature`, `MissingClosedListForwardingNames`,
    `BuildImplicitCallArguments`; laws in `KatLangArityLaws.lean`, guards in
    `CoreTests/ForwardingBindings.lean`.

    FORMULA LIFTING IS BY BINDING NAME, regardless of how many times the name
    occurs in the callee's parameter patterns: every capture occurrence of `name`
    receives the one source this function returns, so a callee that repeats a
    name (`P(x, x)`, `P((x, a), x)`) receives the caller's ONE binding at every
    occurrence — `D = [P][0]` is `D(x) = [P(x, x)][0]` — the rule by-name sharing
    ACROSS callees already follows (`H = F + G` is `H(x) = F(x) + G(x)`). Each
    occurrence is then an ordinary argument slot reading that binding; the
    binder's repeated-name constraint (Q-05) concerns independently supplied
    arguments and merges nothing. (Decided 2026-09-29, reversing the same day's
    Q-72 refusal of such callees; Lean models no signature construction.) This
    decision is FORMULA lifting's: a body whose one row is the bare callee is a
    callable alias (`Algorithm.alias`), which reuses no binding and gains no
    parameter, or bare forwarding (`bareForwardingArgument`), which reuses the same
    parameter bindings by name — the body's own, else the `.capturedParameter`
    this function selects — but never adds one: what a formula in an OPEN body
    infers (`.forwardedParameter`), a closed body's bare row rejects. -/
def forwardingSource (chain : List OwnerLevel) (inferring : Bool) (name : Ident) : ForwardingSource :=
  match selectOwnedDeclaration chain name with
  | .parameter 0 => .ownParameter
  | .parameter (level + 1) => .capturedParameter (level + 1)
  | _ => if inferring then .forwardedParameter else .unavailable

/-- The chain level whose parameter binding a forwarding reuses, if it reuses one. -/
def ForwardingSource.reusedLevel? : ForwardingSource -> Option Nat
  | .ownParameter => some 0
  | .capturedParameter level => some level
  | .forwardedParameter => none
  | .unavailable => none

/-- The chain level whose parameter the owner walk selected, if it selected one. -/
def OwnedDeclaration.parameterLevel? : OwnedDeclaration -> Option Nat
  | .parameter level => some level
  | .property _ => Option.none
  | .none => Option.none

/-- The chain once forwarding added a parameter `name` to the referencing body. -/
def forwardParameter : List OwnerLevel -> Ident -> List OwnerLevel
  | [], _ => []
  | level :: outer, name => { level with forwarded := level.forwarded ++ [name] } :: outer

-- Surface syntax support: while/repeat initial-state boundaries
--------------------------------------------------------------------------------

/- **Ordinary parentheses** construct sequence values.  There is no special
   "double-parens" syntax.  `((expr))` in any position is nested sequence-value
   construction.  `f((a + b) mod 2, c)` parses normally as two arguments.

   **while/repeat initial state** preserves explicit argument boundaries.
   The loops are ordinary fixed-arity builtins whose step is a META parameter
   (META-S3-3, `builtinSignature`):

     while(meta step)          -- step: a written call Step(s1, ..., sk), k ≥ 0
     repeat(meta step, count)

   Each argument of the captured step call is supplied independently (one
   demand cell, never evaluated by the loop itself) and becomes exactly one
   initial state slot (the plan's ONE sticky supply, `argumentViewCells`).
   Therefore `repeat(Step(a, b), 3)` starts with two slots, while
   `repeat(Step(Pair), 3)` starts with one slot even if `Pair` evaluates to
   multiple values.  Use explicit selections such as `Pair[0], Pair[1]` (or
   the spread `Pair*` inside the call) when the intended initial state is two
   slots.  Zero arguments are the empty state (`Z().while` is `()`).

   DotCall lexical fallback (`Step(x).repeat(n)` / `Step(x).while`) injects
   the receiver as the ordinary leading argument — the captured call — after
   structural property lookup.

   Any callable is a step (LOOP-08, Q-23, October 2026): each iteration
   invokes it as the ORDINARY call over the current state slots
   (`runNeedStepSlots`) — a clause family dispatches its clauses, a builtin
   binds them through its argument roles — so `repeat(F(s), 1)` is `F(s)` for
   every callable; a builtin's one result value is one next-state slot
   (`loopStepBuiltinRows`), and a value with no callable identity is no step.

   Step outputs define the state slots for the next iteration as a ROW SUPPLY
   (LOOP-03): each non-spread output row is one next-state slot and each spread
   row `e*` supplies its items.  The step's parameter patterns only bind the
   incoming state; they never repack its rows (Q-24, October 2026).  To keep
   one structured slot across iterations, write it as one value — a capture
   `(history*, next)` or a list `[history*, next]`; multi-output steps
   intentionally become many next-state slots.  A nested loop written as a
   step row is ONE slot like any other result (Q-26): `repeat(Inner(a, b), 2)*`
   supplies its final state's items.

   The completed loop is ONE value with emitted count `Result.valueCount`
   (`loopResultCounted`), so `Fibonacci(0, 1).repeat(10)` is one row `(55, 89)`
   and `Fibonacci(0, 1).repeat(10)*` two rows.

   Expr.capture semantics
   ----------------------
   No tuple constructor exists in the Lean core AST; written sequence-value
   construction is expressed via `Expr.capture` over an OutputBundle of row
   expressions.  Free identifiers inside a capture bubble up to the enclosing
   algorithm through ParameterDetector, because a capture owns no scope.

   Examples
   --------
     while(Step(5, 0))       -- initial state has two slots
     repeat(Step(0, 0), 3)   -- initial state has two slots
     Step(x, 0).while        -- initial state has two slots
     Step(x, 0).repeat(3)    -- initial state has two slots
     Step((x, 0)).while      -- initial state has one sequence-value slot
     while(Step(init))       -- initial state has one slot
     repeat(Step(init), n)   -- initial state has one slot
     Z().while               -- initial state has zero slots -/

/- **Collection builtin inputs** are evaluated at the builtin-dispatch
   layer, not by parser rewriting.

   Builtins such as `order`, `orderDesc`, `count`, `first`, `last`, `min`,
   `max`, `sum`, `avg`, `filter`, `map`, and `reduce` operate on one bound
   collection value's top-level items.

   - Collection builtins are ordinary fixed-arity callables: one fixed
     `collection` parameter followed by fixed control parameters such as
     `count`, `mapper`, or `predicate`. Nothing is opened before binding.
   - A plain call's first argument and a dot-call receiver both fill the
     `collection` parameter; the post-binding collection view then opens one
     outer boundary of a bound sequence or list value (any other value is a
     one-element collection).
   - Nested sequence values are never recursively flattened unless a builtin
     explicitly says so (for example `atoms`). -/

--------------------------------------------------------------------------------
-- Surface syntax support: trailing brace-block call sugar
--------------------------------------------------------------------------------

/- **Trailing brace-block call** is a parser-level desugaring that allows
   passing an inline anonymous algorithm to a call target using brace syntax
   immediately following an identifier or dotCall target.

   Triggering syntax
   -----------------
     Algo{e}              -- trailing block on resolve
     A.Apply{e}           -- trailing block on dotCall

   Desugaring
   ----------
   The parser constructs one algorithm and places it in the argument bundle:

   1. **Inline algorithm** (`inlineAlg`): the parametrized algorithm inferred
      from the brace body.  Free lowercase identifiers inside the body become
      implicit parameters via ParameterDetector, exactly as for `func`-style
      algorithms.  This is the algorithm that `{e}` denotes.

   2. **Argument bundle**: call/dotCall arguments are an OutputBundle
      (`List Expr`) of the original written argument expressions, consumed
      directly in the caller's context.  The trailing brace lowers to the
      single bundle slot `[Expr.algorithmExpr inlineAlg]` — there is no
      argument-wrapper Algorithm.

   The trailing brace is therefore equivalent to parenthesised call syntax:

     Algo{e}       ≡  Algo({e})
     A.Apply{e}    ≡  A.Apply({e})

   Lowered AST:

     Algo{e}
       =>  call (resolve "Algo") [Expr.algorithmExpr inlineAlg]

     A.Apply{e}
       =>  dotCall (resolve "A") "Apply" (some [Expr.algorithmExpr inlineAlg])

   Note: the parser does NOT place `inlineAlg` in the bundle as a bare
   Algorithm — a bundle slot is an Expr, and the brace algorithm always
   appears as an `Expr.algorithmExpr` slot. This allows per-slot argument
   resolution to see the `Expr.algorithmExpr` node and return the inner
   algorithm, which is essential for higher-order binding (the slot's need
   cell projects it as its CALLABLE identity, `projectNeedCallable`).
   (Per-expression Algorithm resolution remains separate from value
   evaluation, and the runtime may still construct one-expression
   Algorithm adapters — `Algorithm.ofExpr` and the capture value
   thunk — for deferred/lazy evaluation of individual slots; those
   adapters are runtime machinery, not the source AST.)

   Evaluation semantics of `Expr.algorithmExpr` in value position
   ---------------------------------------------------------------
   `Expr.algorithmExpr` represents an inline anonymous algorithm.  When
   evaluated directly (not resolved as an algorithm via resolveAlg):
   - 0-param block: auto-evaluates via evalAlgOutput (thunk semantics)
   - block with parameters: returns arityMismatch (needs explicit arguments)

   `resolveAlg(.algorithmExpr a)` always returns the algorithm (wired to
   caller scope), regardless of parameter count. `resolveAlg(.capture rows)`,
   by contrast, returns only a fresh zero-parameter output thunk over the
   bundle — capture is not algorithm identity.

   Higher-order flow
   -----------------
   When a block is passed as an argument to a user-defined call:

     Algo = func(9)
     Algo{a + 1}

   1. The parser emits `call (resolve "Algo") [Expr.algorithmExpr inlineAlg]`
      where `inlineAlg.params = ["a"]`.
   2. `evalCallExpr` resolves `Algo` and dispatches through
      `evalResolvedCall` into `evalUserCall`.
   3. Supply formation turns that bundle slot into a suspended need cell
      (`formNeedSupply` / `supplyNeed`), and the callee's `func` parameter is
      bound to it.
   4. When the callee evaluates `func(9)`, `resolveAlg (.param func)` projects
      the cell's CALLABLE identity (`projectNeedCallable`), which resolves the
      `Expr.algorithmExpr inlineAlg` slot to `inlineAlg` (wired to caller scope).
   5. The value `9` is bound to `a`, and the output `a + 1` evaluates to `10`.

   Examples
   --------
     Algo = func(9); Algo{a + 1}          -- => 10
     Apply = func(x); Apply({a + 1}, 5)   -- => 6
     Use = func; Use{42}                  -- => 42
     Use = func; Use{a + 1}              -- => arityMismatch (block has param a)

   The last example shows that `{a + 1}` in value position (not passed to a
   caller that binds it) triggers arityMismatch because the block has an
   unbound parameter. -/

--------------------------------------------------------------------------------
-- Entry points
--------------------------------------------------------------------------------

/-- Helper to create a private property (default visibility). -/
def privateProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := false, exposure := .exported }

/-- Helper to create a public property. -/
def publicProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true, exposure := .exported }

/-- Helper to create a private local-only property. -/
def privateLocalProp (name : Ident) (exposure : PropExposure) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := false, exposure := exposure }

/-- Helper to create a public local-only property. -/
def publicLocalProp (name : Ident) (exposure : PropExposure) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true, exposure := exposure }

/-- Migration helper: convert assoc list to private PropDefs. -/
def propsPrivate (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => privateProp n a)

/-- Prelude algorithm providing builtin operations in scope by default.
    Builtins are injected into the initial call stack by adding preludeAlg.
    All builtins are public for use in opened contexts. -/
def preludeAlg : Algorithm :=
  Algorithm.mk none [] []
    [ publicProp "if" (Algorithm.builtin .ifBuiltin)
    , publicProp "while" (Algorithm.builtin .whileBuiltin)
    , publicProp "repeat" (Algorithm.builtin .repeatBuiltin)
    , publicProp "atoms" (Algorithm.builtin .atomsBuiltin)
    , publicProp "range" (Algorithm.builtin .rangeBuiltin)
    , publicProp "filter" (Algorithm.builtin .filterBuiltin)
    , publicProp "map" (Algorithm.builtin .mapBuiltin)
    , publicProp "order" (Algorithm.builtin .orderBuiltin)
    , publicProp "orderDesc" (Algorithm.builtin .orderDescBuiltin)
    , publicProp "count" (Algorithm.builtin .countBuiltin)
    , publicProp "contains" (Algorithm.builtin .containsBuiltin)
    , publicProp "first" (Algorithm.builtin .firstBuiltin)
    , publicProp "last" (Algorithm.builtin .lastBuiltin)
    , publicProp "distinct" (Algorithm.builtin .distinctBuiltin)
    , publicProp "take" (Algorithm.builtin .takeBuiltin)
    , publicProp "skip" (Algorithm.builtin .skipBuiltin)
    , publicProp "min" (Algorithm.builtin .minBuiltin)
    , publicProp "max" (Algorithm.builtin .maxBuiltin)
    , publicProp "sum" (Algorithm.builtin .sumBuiltin)
    , publicProp "avg" (Algorithm.builtin .avgBuiltin)
    , publicProp "reduce" (Algorithm.builtin .reduceBuiltin)
    ]
    []

/- Allocate declaration identities once, before execution. Lean ASTs are
    immutable values: two different declarations can have identical bodies,
    so `reprStr` alone cannot identify them. These numbers identify written
    declarations, not activations. Host-supplied sharing identities survive.
    This pass changes no names, ownership, exposure, or executable expression. -/
mutual
  partial def identifyPropertyExpr : Expr -> StateM Nat Expr
    | .param n => pure (.param n)
    | .num n => pure (.num n)
    | .stringLiteral s => pure (.stringLiteral s)
    | .interpolatedString head links =>
        return .interpolatedString head
          (<- links.mapM (fun link => do
            return { link with hole := (<- identifyPropertyExpr link.hole) }))
    | .boolLiteral b => pure (.boolLiteral b)
    | .resolve n => pure (.resolve n)
    | .emptySequence n => pure (.emptySequence n)
    | .unary op e => return .unary op (<- identifyPropertyExpr e)
    | .binary op a b => return .binary op (<- identifyPropertyExpr a) (<- identifyPropertyExpr b)
    | .comparison first links =>
        return .comparison (<- identifyPropertyExpr first)
          (<- links.mapM (fun link => do
            return { link with operand := (<- identifyPropertyExpr link.operand) }))
    | .index a bs => return .index (<- identifyPropertyExpr a) (<- bs.mapM identifyPropertyExpr)
    | .sequenceConstruct a b => return .sequenceConstruct (<- identifyPropertyExpr a) (<- identifyPropertyExpr b)
    | .sequenceSpread e => return .sequenceSpread (<- identifyPropertyExpr e)
    | .listLiteral es => return .listLiteral (<- es.mapM identifyPropertyExpr)
    | .capture es => return .capture (<- es.mapM identifyPropertyExpr)
    | .algorithmExpr a => return .algorithmExpr (<- identifyPropertyAlgorithm a)
    | .call f args => return .call (<- identifyPropertyExpr f) (<- args.mapM identifyPropertyExpr)
    | .dotMember target name fallback args =>
        return .dotMember (<- identifyPropertyExpr target) name
          (<- identifyPropertyExpr fallback) (<- args.mapM (List.mapM identifyPropertyExpr))

  partial def identifyPropertyAlgorithm (algorithm : Algorithm) : StateM Nat Algorithm := do
    let identity <- match algorithm.declarationId with
      | some (.shared n) => pure (.shared n)
      | some (.module n) => pure (.module n)
      | _ => do
          let next <- get
          set (next + 1)
          pure (.syntax next)
    match algorithm with
    | .builtin b => pure (.builtin b)
    | .mk parent parameters opens props output _ =>
        return .mk (<- parent.mapM identifyPropertyScope) parameters
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- output.mapM identifyPropertyExpr) (some identity)
    | .conditional parent opens branches _ =>
        return .conditional (<- parent.mapM identifyPropertyScope)
          (<- opens.mapM identifyPropertyExpr)
          (<- branches.mapM fun b => return { b with body := (<- identifyPropertyAlgorithm b.body) }) (some identity)
    | .alias parent opens props target _ reference =>
        return .alias (<- parent.mapM identifyPropertyScope)
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- identifyPropertyExpr target) (some identity) reference

  partial def identifyPropertyScope : ScopeCtx -> StateM Nat ScopeCtx
    | .mk parent params opens props output branches _ id =>
        return .mk (<- parent.mapM identifyPropertyScope) params
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- output.mapM identifyPropertyExpr)
          (<- branches.mapM fun b => return { b with body := (<- identifyPropertyAlgorithm b.body) }) none id

  partial def identifyPropertyDefinition (p : PropDef) : StateM Nat PropDef := do
    let identity <- match p.identity with
      | some (.shared n) => pure (.shared n)
      | _ => do
          let next <- get
          set (next + 1)
          pure (.syntax next)
    return { p with identity := some identity, alg := (<- identifyPropertyAlgorithm p.alg) }
end

/-- THE RUN RESULT BOUNDARY (CallReference S1, J4): a call reference is run-scoped, so a
    run result that contains one — at any depth — is refused; every reference-free value
    leaves unchanged. C#: `Evaluator.ExportRunValue` (every public evaluator and engine
    result, host-operation arguments, formatting). -/
def exportRunValue (value : Result) : EvalM Result := do
  requireCallRefFree callReferenceLeavesRunMessage value
  pure value

def runResultM (e : Expr) : EvalM Result := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      -- The program root is demanded for its value with nothing supplied, so the
      -- ONE zero-supply rule decides: a root whose parameter list still REQUIRES
      -- a supplied argument has unresolved implicit parameters, while one that
      -- accepts an empty supply (a collecting-only host-built root) binds it
      -- through the shared demand funnel (`evalProgramOutput`).
      if Algorithm.acceptsZeroSuppliedArguments wired then
        exportRunValue (<- evalProgramOutput wired ctx [])
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => exportRunValue (<- eval e ctx [])

def runResultWithState (e : Expr) : Except Error (Result × EvalState) :=
  runResultM e |>.run EvalState.empty

def runResult (e : Expr) : Except Error Result :=
  match runResultWithState e with
  | .ok (result, _) => .ok result
  | .error err => .error err

def runFlat (e : Expr) : Except Error (List Int) := do
  pure (Result.hostAtoms (<- runResult e))

--------------------------------------------------------------------------------
-- Core sugar (surface syntax is external)
--------------------------------------------------------------------------------

open Expr

def param (s : Ident) : Expr := .param s
def num (n : Int) : Expr := .num n
def index (a : Expr) (selectors : List Expr) : Expr := .index a selectors
def resolve (n : Ident) : Expr := .resolve n
def algorithmExpr (a : Algorithm) : Expr := .algorithmExpr a
def capture (rows : OutputBundle) : Expr := .capture rows
def call (f : Expr) (args : List Expr) : Expr := .call f args
def dotCall (o : Expr) (n : Ident) : Expr := .dotCall o n none
def sequenceConstruct (a b : Expr) : Expr := .sequenceConstruct a b
def sequenceSpread (a : Expr) : Expr := .sequenceSpread a
def listLiteral (items : List Expr) : Expr := .listLiteral items

/-- Convenience constructor for algorithms with private properties by default.
    To make properties public, use `publicProp` when building the props list. -/
def alg (ps : List Ident) (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none (Algorithm.normalParameters ps) op props out

def algWithParameters (parameters : List CallableParameter)
    (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none (ParameterPattern.fromParameters parameters) op props out

def algWithParameterPatterns (patterns : List ParameterPattern)
    (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none patterns op props out

/-- Convenience constructor accepting (name, alg) pairs as private properties. -/
def algPrivate (ps : List Ident) (op : List Expr) (props : List (Prod Ident Algorithm)) (out : List Expr) : Algorithm :=
  Algorithm.mk none (Algorithm.normalParameters ps) op (propsPrivate props) out

infixl:65 " + " => fun a b => Expr.binary BinaryOp.add a b
infixl:65 " - " => fun a b => Expr.binary BinaryOp.sub a b
infixl:70 " * " => fun a b => Expr.binary BinaryOp.mul a b
infixl:70 " / " => fun a b => Expr.binary BinaryOp.div a b
infixr:75 " ^ " => fun a b => Expr.binary BinaryOp.pow a b

--------------------------------------------------------------------------------
-- load elaboration (compile-time module loading)
--------------------------------------------------------------------------------

/- Descriptive C# load boundary (Q-63, owner decision 2026-10-13).

  Source acquisition and load elaboration are implemented by the C# frontend and
  hosting infrastructure. The current Lean evaluator supplies no complete executable
  load-elaboration model; this text is descriptive, not a proof of C# loading.

  Property/clause definition bodies and open targets enter an allowed load context.
  Transparent nested blocks, capture/list items, spreads, Grace and argumentless dot
  receivers inherit it. Ordinary call arguments, operator operands, selection,
  interpolation holes and root output rows are runtime positions and reject load.
  C# ModuleLoader owns literal/URL admission, transport, canonical module identity,
  caching and cycles. Deferred regions retain directives until materialization;
  unavailable or refused directives remain in an unevaluable analysis tree.

  The executable structural predicates below check the post-elaboration core AST.
  They neither execute acquisition nor prove the C# loader, deferred-region schedule
  or refusal policy. Successful materialized regions contain no unresolved load.
-/
mutual
/-- Post-elaboration invariant: returns true iff the expression tree contains
    no unresolved load calls (`call (resolve "load") _`) and every dot edge
    satisfies the elaborated dot-edge contract. Runtime `Expr.stringLiteral`
    nodes are allowed as ordinary first-class values.
    This structural predicate is not a proof of C# load elaboration or hosting. -/
partial def postElabInvariant : Expr -> Bool
  | .stringLiteral _ => true
  -- Holes are ordinary expressions: a `load` call or an incoherent dot edge inside one
  -- violates the invariant like anywhere else (the wildcard below would hide them).
  | .interpolatedString _ links => links.all (fun link => postElabInvariant link.hole)
  | .boolLiteral _   => true
  | .unary _ e       => postElabInvariant e
  | .binary _ a b    => postElabInvariant a && postElabInvariant b
  | .comparison first links => postElabInvariant first && links.all (fun link => postElabInvariant link.operand)
  | .index a bs      => postElabInvariant a && bs.all postElabInvariant
  | .sequenceConstruct a b  => postElabInvariant a && postElabInvariant b
  | .sequenceSpread a       => postElabInvariant a
  | .listLiteral items      => items.all postElabInvariant
  | .call (.resolve "load") _ => false  -- unresolved load call
  | .call f args     => postElabInvariant f && args.all postElabInvariant
  -- Elaborated dot-edge contract (C#: DotCallElaborationInvariant): the
  -- stored lexical fallback is exactly `.resolve` or `.param` and its
  -- identifier equals the structural member name — the two identities name
  -- the same written member. Any other fallback expression is not a valid
  -- elaborated dot edge. Lean's representation has no nullable
  -- host-compatibility state: `Expr.dotCall` (the ordinary/lexical smart
  -- constructor) already builds a coherent edge, so this arm rejects only
  -- hand-built incoherence.
  | .dotMember a n fallback args =>
      (match fallback with
       | .resolve fn => fn == n
       | .param fn   => fn == n
       | _           => false) &&
      postElabInvariant a &&
      match args with
      | some slots => slots.all postElabInvariant
      | none => true
  | .algorithmExpr alg => postElabInvariantAlg alg
  | .capture rows    => rows.all postElabInvariant
  | _                => true  -- param, num, resolve

/-- Algorithm-level post-elaboration invariant: all contained expressions
  satisfy `postElabInvariant`. -/
partial def postElabInvariantAlg : Algorithm -> Bool
  | .builtin _ => true
  | .mk _ _ opens props output _ =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      output.all postElabInvariant
  | .conditional _ opens branches _ =>
      opens.all postElabInvariant &&
      branches.all (fun b => postElabInvariantAlg b.body)
  | .alias _ opens props target _ _ =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      postElabInvariant target
end

end KatLang
