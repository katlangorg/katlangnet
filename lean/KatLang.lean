-- KatLang v0.8.190 (core AST + semantics + while/repeat init boundaries + higher-order alg params + conditional algorithms + first-class strings)
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
--   rule: the runtime first performs `div`'s quotient in finite-precision
--   Decimal128, and large integral arithmetic can round or overflow. Fractional
--   results the decimal runtime can represent are another documented Int-core
--   limitation: `/`-style quotients and the `avg` builtin truncate here
--   (`7 / 2 = 3` and `avg(1, 2) = 1`) but yield decimals in the runtime
--   (`3.5` and `1.5`), and negative exponents with
--   |base| >= 2 raise an explicit error instead of silently truncating the
--   reciprocal to 0 (see `negativeIntPow`).
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
--       recursive parameter pattern made only of captures and structural sequence-value patterns
--       (for example `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, or
--       `CountSequenceValue((*values)) = values.count`)
--     - multi-clause families and clause heads that require literal or
--       whole-argument conditional matching elaborate to `Algorithm.conditional`
--
--   This split is intentional: ordinary elaboration preserves dual-view call
--   binding for higher-order arguments, while true conditional algorithms keep
--   their full-input-specification and whole-argument matching semantics.
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

namespace StateT
  def error {σ : Type u} {errT : Type v} {α : Type u} (err : errT)
      : StateT σ (Except errT) α :=
    throw err

  def ok {σ : Type u} {errT : Type v} {α : Type u} (value : α)
      : StateT σ (Except errT) α :=
    pure value
end StateT

namespace KatLang

--------------------------------------------------------------------------------
-- Typed identifiers (lightweight aliases for future-proofing)
--------------------------------------------------------------------------------

abbrev Ident := String    -- algorithm / property / parameter names
abbrev Assoc (K V : Type) := List (Prod K V)  -- association list

inductive ParameterKind where
  | normal
  | collecting
  deriving Repr, BEq, DecidableEq

structure CallableParameter where
  name : Ident
  kind : ParameterKind := .normal
  deriving Repr, BEq

inductive ParameterPattern where
  | capture : CallableParameter -> ParameterPattern
  | sequenceValue : List ParameterPattern -> ParameterPattern
  deriving Repr, BEq

structure CallableSignature where
  name : Ident
  parameters : List CallableParameter
  deriving Repr, BEq

def CallableParameter.displayName (parameter : CallableParameter) : String :=
  match parameter.kind with
  | .normal => parameter.name
  | .collecting => "*" ++ parameter.name

namespace ParameterPattern
  partial def captures : ParameterPattern -> List CallableParameter
    | .capture parameter => [parameter]
    | .sequenceValue items => items.flatMap captures

  def fromParameters (parameters : List CallableParameter) : List ParameterPattern :=
    parameters.map .capture

  def normalPatterns (ps : List Ident) : List ParameterPattern :=
    ps.map (fun p => .capture { name := p })

  def hasStructured (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .sequenceValue _ => true
      | _ => false)

  /-- True when the pattern list itself contains a collecting binding (nested
      captures inside sequence-value patterns do not count).
      C#: `ParameterPattern.HasCollectingCaptureAtCurrentLevel`. -/
  def hasCollectingCaptureAtCurrentLevel (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .capture parameter => parameter.kind == ParameterKind.collecting
      | _ => false)

  def hasRepeatedCaptureNames (patterns : List ParameterPattern) : Bool :=
    let names := (patterns.flatMap captures).map (fun parameter => parameter.name)
    names.length != names.eraseDups.length

  partial def containsCaptureName (name : Ident) : ParameterPattern -> Bool
    | .capture parameter => parameter.name = name
    | .sequenceValue items => items.any (containsCaptureName name)

  def topLevelCaptureKind? (name : Ident) : List ParameterPattern -> Option ParameterKind
    | [] => none
    | .capture parameter :: rest =>
        if parameter.name = name then some parameter.kind else topLevelCaptureKind? name rest
    | .sequenceValue _ :: rest => topLevelCaptureKind? name rest
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
        | .normal => go (index + 1) rest
  go 0 signature.parameters

def CallableSignature.requiredNormalParameterCount (signature : CallableSignature) : Nat :=
  (signature.parameters.filter (fun parameter => parameter.kind == ParameterKind.normal)).length

def CallableSignature.acceptsItemCount (signature : CallableSignature) (count : Nat) : Bool :=
  -- A collecting user signature consumes an item supply: it accepts at least
  -- the fixed (non-collecting) count. Fixed signatures, including collection
  -- builtins, stay exact.
  match signature.collectingIndex? with
  | some _ => count >= signature.requiredNormalParameterCount
  | none => count == signature.parameters.length

structure CallableArgumentBindings (α : Type) where
  normalBindings : List (Prod Ident α)
  collectingName? : Option Ident := none
  collectingItems : List α := []
  deriving Repr

/-- Exposure classification of a `PropDef`: an INPUT to lookup, computed by the C# front
    end and never derived here. `open` exposes public `.exported` members and structural
    dot access reaches `.exported` members. `.localCapturedAncestorParams`: the value
    requires an input only an enclosing owner's call binds (a parameter, or a conditional
    branch's pattern binder). `.localConditional` is the family-level reason a name access
    into a conditional's branch bodies is refused (`conditionalBranchesDefineProperty`);
    the front end never assigns it to a `PropDef` — a branch's own declarations classify
    exactly like declarations in any other body. -/
inductive PropExposure where
  | exported
  | localCapturedAncestorParams
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

inductive Error where
  | unknownName      : Ident -> Error
  | unknownProperty  : String -> Ident -> Error        -- object desc, property name
  | notPublicProperty : String -> Ident -> Error       -- object desc, property name (exists but private)
  | localOnlyProperty : String -> Ident -> PropExposure -> Error  -- object desc, property name, reason
  | notAnAlgorithm   : String -> Error
  | illegalInOpen    : String -> Error                -- semantic restriction (e.g., builtin not allowed)
  | badOpenForm      : String -> Error                -- syntactic form not allowed in open
  | illegalInEval    : String -> Error                -- not evaluable to a value
  | ambiguousOpen    : Ident -> List String -> Error   -- name, providers
  | arityMismatch    : Nat -> Nat -> Error     -- expected, actual
  | badArity         : Error                   -- shape / unpacking failure
  | typeMismatch     : String -> Error          -- type error (e.g. string where number expected)
  | badIndex         : Error
  | divByZero        : Error                   -- division or modulo by zero
  | noMatchingBranch : Ident -> Error          -- conditional algorithm: no branch matched
  | branchArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchArities)
  | branchOutputArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level output arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchOutputArities)
  | duplicateProperty : Ident -> Error         -- algorithm defines the same property name more than once
  | duplicateBranchPattern : Error             -- conditional algorithm has match-equivalent branch patterns
  | explicitParamsRequireOutput : Error        -- explicit algorithm params require an algorithm output
  | missingOutput    : Error                   -- forced user-defined algorithm does not define output
  | spreadMissingOutput : Error          -- spread operand produced no output
  | unresolvedImplicitParams : List Ident -> Error  -- top-level block has unresolved implicit parameters
  | withContext      : String -> Error -> Error -- contextual wrapper
  deriving Repr

-- * IMPORTANT: Needed for compiling `partial` definitions.
-- Lean requires `Nonempty` for the function types of partial defs.
instance : Nonempty Error := Nonempty.intro Error.badArity

def Error.referencesAnyName (names : List Ident) : Error -> Bool
  | .unknownName name => names.contains name
  | .unresolvedImplicitParams paramNames => paramNames.any (fun name => names.contains name)
  | .withContext _ inner => Error.referencesAnyName names inner
  | _ => false

def CallableSignature.validate (signature : CallableSignature) : Except Error Unit :=
  match signature.validationError? with
  | some message => .error (Error.illegalInEval message)
  | none => .ok ()

/-- Variable-middle collecting-parameter binding (mirrors C# `BindCallableArguments`). The fixed
    prefix binds from the front, the fixed suffix from the back, and the collecting
    captures the remaining middle items (zero or more). The minimum is the FIXED
    (non-collecting) parameter count: like every other collecting binding, the collecting parameter may
    collect ZERO items (an empty collected segment is the exact list `[]`) — the same rule the
    shared pattern binder applies (`bindParameterPatternList`: required =
    patterns - 1).
    (Collection builtins no longer bind here: they are ordinary fixed-arity
    callables bound in `bindSequenceBuiltinArguments`.) -/
def bindCallableArguments (signature : CallableSignature) (items : List α)
    (arityMismatch : Nat -> Nat -> Error)
    : Except Error (CallableArgumentBindings α) :=
  match signature.validate with
  | .error err => .error err
  | .ok () =>
      match signature.collectingIndex? with
      | none =>
          if items.length == signature.parameters.length then
            .ok {
              normalBindings := List.zip (signature.parameters.map (fun parameter => parameter.name)) items
            }
          else
            .error (arityMismatch signature.parameters.length items.length)
      | some collectingIndex =>
          -- Minimum = fixed (non-collecting) parameter count, so the collecting binding may
          -- collect zero items (empty collected segment = `[]`) at every receiver,
          -- including loop-state binding.
          let minimum := signature.parameters.length - 1
          if items.length < minimum then
            .error (arityMismatch minimum items.length)
          else
            let suffixParameters := signature.parameters.drop (collectingIndex + 1)
            let suffixCount := suffixParameters.length
            let suffixStart := items.length - suffixCount
            let prefixParameters := signature.parameters.take collectingIndex
            let prefixItems := items.take collectingIndex
            let suffixItems := items.drop suffixStart
            let middleItems := (items.drop collectingIndex).take (suffixStart - collectingIndex)
            .ok {
              normalBindings :=
                (List.zip (prefixParameters.map (fun parameter => parameter.name)) prefixItems) ++
                (List.zip (suffixParameters.map (fun parameter => parameter.name)) suffixItems)
              collectingName? := (signature.parameters.drop collectingIndex).head?.map (fun parameter => parameter.name)
              collectingItems := middleItems
            }

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

inductive BinaryOp where
  | add | sub | mul | div | idiv | mod | pow
  | lt | gt | le | ge | eq | ne
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
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .eq => "=="
  | .ne => "!="
  | .and => "and"
  | .or => "or"
  | .xor => "xor"

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

inductive SequenceBuiltinEmptyPolicy where
  | allowEmpty
  | requireAnyItem
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
      emptyPolicy := .requireAnyItem
    }
  | .lastBuiltin => some {
      emptyPolicy := .requireAnyItem
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
      suffixArgs := [
        { name := "reducer" },
        { name := "initial" }
      ]
    }
  | _ => none

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

/-- Normative arity-acceptance specification for builtins, mirrored by the C#
    `BuiltinRegistry.AcceptsArity` (which the C# evaluator consults directly).
    The Lean `applyBuiltinCounted` dispatch enforces the same arities
    structurally via pattern-match fall-through to `builtinArityError`, and
    `applyBuiltin` inherits them as its Result projection; the two encodings
    must stay in agreement (pinned by the CoreTests arity parity guards). -/
def builtinAcceptsArity : Builtin -> Nat -> Bool
  | b, n =>
      match sequenceBuiltinMetadata? b with
      | some metadata =>
          -- Collection builtins are ordinary fixed-arity callables:
          -- `count(collection)` is exactly 1 argument and
          -- `take(collection, count)` is exactly 2, the same rule as every
          -- other fixed builtin.
          n = 1 + metadata.suffixArgs.length
      | none =>
          match b, n with
          | .ifBuiltin, 3 => true
          | .whileBuiltin, n => n >= 2
          | .repeatBuiltin, n => n >= 3
          | .atomsBuiltin, 1 => true
          | .rangeBuiltin, 2 => true
          | _, _ => false

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
      | none =>
          match b with
          | .ifBuiltin => "3"
          | .whileBuiltin => "at least 2"
          | .repeatBuiltin => "at least 3"
          | .atomsBuiltin => "1"
          | .rangeBuiltin => "2"
          | _ => "?"

def builtinArityError (b : Builtin) (actual : Nat) : Error :=
  -- The numeric payload mirrors the C# `WrongBuiltinArity`: `if` is the one
  -- builtin whose expected count is populated (it requires exactly 3
  -- arguments); every other builtin still carries the placeholder 0 beside
  -- the descriptive `builtinArityDesc` context.
  let expected : Nat :=
    match b with
    | .ifBuiltin => 3
    | _ => 0
  Error.withContext s!"expected {builtinArityDesc b} arguments" (Error.arityMismatch expected actual)

--------------------------------------------------------------------------------
-- Patterns (for clause heads and conditional algorithms)
--------------------------------------------------------------------------------

/-- Pattern language for clause heads and conditional algorithm branch matching.
    Recursive capture/sequence-value patterns can elaborate to ordinary explicit
    parameter patterns. Conditional patterns match against Result values at
    call time.
    - `bind x`: matches any Result and binds it to name `x`
    - `litInt n`: matches only `Result.atom n`
    - `sequenceValue ps`: matches `Result.sequenceValue rs` with same arity, each sub-pattern
      matching; a singleton sequence-value pattern also matches a non-sequence-value
      result because normalization collapses singleton sequence values
      (see `patternSequenceValueMembers?`)

    Patterns are a separate semantic type, distinct from Expr.
    They do not appear in executable expression positions.

    **Full-input-specification rule**: In a conditional algorithm, the branch
    pattern in `Name(...)` is the COMPLETE INPUT SPECIFICATION of that branch.
    - All branch inputs must appear in the pattern.
    - Branch bodies do NOT infer additional implicit parameters from free
      identifiers.  Only names bound by the pattern (plus ordinary lexical /
      property / open / builtin resolution) are available in the body.
    - Unused pattern-bound names are allowed.
    - Grace `~` is NOT permitted in patterns or branch bodies.  Patterns
      contain only matching constructs (binders, integer literals, nested
      sequence-value patterns).  Branch bodies must not use Grace because conditional branches
      have no implicit parameter inference or reordering to apply it to.

    This keeps conditional algorithms self-contained: branch selection and
    branch binding are the same operation, with no hidden remaining parameters
    and no interaction with Grace-based parameter reordering. -/
inductive Pattern where
  | bind      : Ident -> Pattern
  | litInt    : Int -> Pattern
  | litString : String -> Pattern    -- matches only Result.str s (exact string equality)
  | sequenceValue     : List Pattern -> Pattern
  deriving Repr, BEq

namespace Pattern
  /-- Collect all binder names in a pattern (left-to-right). -/
  def boundNames : Pattern -> List Ident
    | .bind x      => [x]
    | .litInt _    => []
    | .litString _ => []
    | .sequenceValue ps    => ps.flatMap boundNames

  /-- Compute the top-level arity of a pattern.
      - `sequenceValue [p1, ..., pn] ⟹ n`
      - any non-sequence-value pattern  ⟹ 1

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

  /-- Return parameter names when a sole surface clause head consists only of
      recursive binder/sequence-value parameter patterns.

      This is only an eligibility helper for the whole same-name clause-group
      elaboration rule; it does not by itself decide ordinary-vs-conditional.

      Rejected on purpose:
      - literal or mixed non-binder pattern structure

      This is the ordinary clause-elaboration boundary: capture/sequence-value-only
      recursive parameter patterns elaborate as ordinary algorithms, while
      literal or mixed patterns stay conditional. -/
  partial def parameterPattern? : Pattern -> Option ParameterPattern
    | .bind x => some (.capture { name := x })
    | .sequenceValue ps => do
        let patterns <- ps.mapM parameterPattern?
        some (.sequenceValue patterns)
    | _ => none

  partial def plainClauseParameterPatterns? : Pattern -> Option (List ParameterPattern)
    | .bind x => some [.capture { name := x }]
    | .sequenceValue ps => ps.mapM parameterPattern?
    | _ => none

  def plainClauseParamNames? : Pattern -> Option (List Ident)
    | p => (plainClauseParameterPatterns? p).map (fun patterns => (patterns.flatMap ParameterPattern.captures).map (fun parameter => parameter.name))

  /-- Check whether two patterns are match-equivalent. Binder spelling is
      irrelevant, but repeated-name equality positions must agree:
      - `bind _` ≡ `bind _` (any binder matches everything)
      - `litInt m` ≡ `litInt n` iff `m = n`
      - `sequenceValue ps` ≡ `sequenceValue qs` iff same length and pairwise match-equivalent

      Used to detect duplicate branch patterns in conditional algorithms.

      Equivalence is structural, not extensional: because matching adapts
      singleton sequence-value patterns to non-sequence-value values (`patternSequenceValueMembers?`),
      `sequenceValue [bind _]` accepts the same runtime inputs as `bind _`, yet the
      two are not considered equivalent here.  Duplicate detection therefore
      flags only structurally identical match behavior. -/
  def binderRenaming? (name : Ident) : List (Ident × Ident) -> Option Ident
    | [] => none
    | (left, right) :: rest =>
        if left = name then some right else binderRenaming? name rest

  def binderTargetUsed (name : Ident) : List (Ident × Ident) -> Bool
    | [] => false
    | (_, right) :: rest => right = name || binderTargetUsed name rest

  partial def matchEquivalentWithRenaming : Pattern -> Pattern ->
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
    | .sequenceValue ps, .sequenceValue qs, pairs =>
        if ps.length != qs.length then
          none
        else
          let rec go : List (Pattern × Pattern) ->
              List (Ident × Ident) -> Option (List (Ident × Ident))
            | [], current => some current
            | (p, q) :: rest, current => do
                let next <- matchEquivalentWithRenaming p q current
                go rest next
          go (ps.zip qs) pairs
    | _, _, _ => none

  def isMatchEquivalent (left right : Pattern) : Bool :=
    (matchEquivalentWithRenaming left right []).isSome
end Pattern

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

mutual
  inductive Expr where
    | param   : Ident -> Expr
    | num     : Int -> Expr
    | stringLiteral : String -> Expr  -- * string literal: first-class value (evaluates to Result.str)
    | unary   : UnaryOp -> Expr -> Expr
    | binary  : BinaryOp -> Expr -> Expr -> Expr
    | index   : Expr -> Expr -> Expr
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
    --   visible-empty rule. Guarded by SequenceConstructContainmentTests
    --   (C#) and the internal-node cases in SemanticExplorerCases.lean.
    | sequenceConstruct : Expr -> Expr -> Expr
    -- * emptySequence: the empty sequence value `()`. Repeated ordinary
    --   parentheses around the empty sequence are useful-structure canonicalized
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
    --   ONE exact immutable list value (`Result.listValue`). Element slots follow
    --   the same expression-list rules as written parentheses (an explicit spread
    --   slot opens its operand's immediate items, a non-spread `()` slot stays one
    --   visible element), but the collected elements are stored EXACTLY: no
    --   singleton erasure and no empty canonicalization, so `[7]`, `[[7]]`, and
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
    --   algorithm identity of anything inside it. Redundant parentheses
    --   normalize away at parse time (C# parser); only meaningful boundaries
    --   survive as this node. C#: `Expr.Capture`.
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
    --   the fallback applying only on a structural miss. Runtime consumers
    --   CONSUME these facts (`resolveAlg fallback`) instead of reconstructing
    --   the Param-vs-Resolve decision from environments. The C# front end
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

  /-- Property definition with visibility metadata. -/
  structure PropDef where
    name     : Ident
    alg      : Algorithm
    isPublic : Bool
    exposure : PropExposure := .exported
    deriving Repr

  /-- A branch of a conditional algorithm: a pattern and a body algorithm.
      The pattern is the complete input specification of the branch.
      Branch bodies receive bindings ONLY from the matched pattern (plus
      ordinary lexical resolution).  No extra implicit parameters are inferred
      from free identifiers in the body.  Grace `~` is not allowed in patterns
      or branch bodies.
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
        Algorithm
    | builtin : Builtin -> Algorithm
    /-- Conditional algorithm: ordered pattern branches tried at call time.
        At call time, arguments are evaluated and matched against branch patterns
        in source order.  The first matching branch body is evaluated.
        If no branch matches, evaluation fails with noMatchingBranch.

        **Full-input-specification invariant**: each branch pattern `Name(...)`
        declares the complete input interface of that branch.  Branch bodies do
        NOT infer additional implicit parameters from free identifiers — only
        names bound by the pattern and names resolvable through ordinary lexical /
        property / open / builtin lookup are available.  Grace `~` is forbidden
        in both patterns and branch bodies.

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
        and that sole head is a recursive capture/sequence-value parameter pattern such
        as `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, or
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
        Algorithm
    deriving Repr

  inductive ScopeCtx where
    | mk :
        (parent  : Option ScopeCtx) ->
        (opens   : List Expr) ->
        (props   : List PropDef) ->
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

/-- Ordinary/lexical dot-call smart constructor: `a.f` / `a.f(args)` with the
    unelaborated fallback identity `.resolve f`. Hand-built ASTs keep plain
    lexical-fallback semantics through this form; elaborated trees carry the
    front-end's Param-vs-Resolve decision in the full `Expr.dotMember`
    constructor. C#: an `Expr.DotCall` with null `LexicalFallback`. -/
def Expr.dotCall (target : Expr) (name : Ident) (args : Option OutputBundle) : Expr :=
  .dotMember target name (.resolve name) args

/-- Surface same-name clause-group classification.
  Front-ends must decide ordinary-vs-conditional elaboration only after
  collecting the entire same-name clause family, not while looking at the
  first clause in isolation.

  A same-name clause group elaborates as ordinary only when:
  - the group contains exactly one clause, and
  - that sole clause head is a recursive capture/sequence-value parameter pattern

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
  | sequenceValue : List Result -> Result
  -- Exact immutable list value `[a, b, c]`. Unlike sequence values, list
  -- structure is never singleton-normalized: `listValue [r]` and `r` are
  -- distinct values, `listValue []` is distinct from the empty sequence
  -- value, and nesting is preserved exactly. C#: `Result.ListValue`.
  | listValue : List Result -> Result
  deriving Repr, BEq

namespace Result
  def normalize : Result -> Result
    | atom n => atom n
    | str s  => str s
    | sequenceValue rs =>
        let rs' := rs.map normalize
        match rs' with
        | [r] => r
        | _   => sequenceValue rs'
    -- Lists are exact: normalize their elements (redundant SEQUENCE structure
    -- inside a list still canonicalizes) but never collapse the list boundary
    -- itself — `[7]` stays `[7]`, never `7`.
    | listValue rs => listValue (rs.map normalize)

  /-- Truth-testing numeric flattening: the numeric atoms reachable through
      SEQUENCE boundaries only. This view backs `truthValue?` and is NOT the
      `atoms` builtin's collector — that is `languageAtoms`, which also opens
      list boundaries. Keeping the two separate means the builtin's traversal
      can never leak into truth testing: lists have no truth value.
      C#: `Result.ToAtoms`. -/
  def atoms : Result -> List Int
    | atom n    => [n]
    | str _     => []       -- strings are not numeric; silently omitted from atom lists
    | sequenceValue rs => rs.flatMap atoms
    | listValue _ => []     -- lists are opaque to truth testing, like strings

  /-- Language-level atom collection for the `atoms` builtin: recursively
      collect numeric atoms depth-first, left-to-right, through BOTH sequence
      and exact list boundaries. Strings and other non-numeric leaves
      contribute no atoms. The builtin materializes this collection as ONE
      exact immutable list value (`makeCollectionListResult`).
      Deliberately separate from `Result.atoms` (truth testing stays
      list-opaque) and `Result.hostAtoms` (host projection), so none of the
      three contracts can drift through shared code.
      C#: `Result.LanguageAtoms`. -/
  def languageAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | sequenceValue rs => rs.flatMap languageAtoms
    | listValue rs => rs.flatMap languageAtoms

  /-- Host-boundary numeric flattening used by `runFlat`: like `Result.atoms`,
      but also opens exact list boundaries so collection-builtin results
      surface their numeric contents at the embedding boundary. This is a host
      projection, not language semantics: truth testing keeps lists opaque
      (`Result.atoms`), the `atoms` builtin collects through its own separate
      collector (`Result.languageAtoms`) and returns one exact list value
      rather than a host atom list, and no in-language conversion between
      lists and sequences is implied.
      C#: `Result.ToHostAtoms`. -/
  def hostAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | sequenceValue rs => rs.flatMap hostAtoms
    | listValue rs => rs.flatMap hostAtoms

  /-- KatLang truth testing used by builtins like `if`.
      Zero is false, any other numeric atom is true.
      Results with no numeric atoms are invalid for truth testing.

      This intentionally follows the current builtin convention based on the
      first numeric atom of the flattened result. Builtins with stricter
      contracts, such as `filter`, should use a dedicated helper instead. -/
  def truthValue? (r : Result) : Option Bool :=
    match atoms r with
    | 0::_ => some false
    | _::_ => some true
    | _    => none

  /-- Strict truth testing for `filter` predicates.
      Accepts exactly one atomic numeric result: `0` is false and any other
      atom is true.

      Sequence values, multi-output results, empty results, and strings are all
      rejected. This is intentionally stricter than `truthValue?`, because
      `filter` must not derive truth from flattened atoms. -/
  def singleAtomicTruthValue? : Result -> Option Bool
    | atom 0 => some false
    | atom _ => some true
    | _      => none

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
    | sequenceValue rs =>
        match normalize (sequenceValue rs) with
        | atom n => some n
        | _      => none
    | listValue _ => none   -- lists never coerce to numbers, not even `[5]`

  /-- Extract top-level items from a result.
      Atom/string -> singleton list; sequence value -> its items.
      A list value stays OPAQUE here: it is one item, so non-spread consumers
      (boundary re-counting, call binding) treat a list as a single exact
      value. Only the spread marker (`spreadItems`), deconstruction binding
      (`structureItems?`), the indexing `:` projection target view
      (`projectionItems`), and the post-binding builtin collection view
      (`builtinCollectionItems`, applied to the bound `collection` argument)
      open a list boundary. -/
  def toItems : Result -> List Result
    | atom n   => [atom n]
    | str s    => [str s]
    | sequenceValue rs => rs
    | listValue rs => [listValue rs]

  /-- Item view used by the spread expression (`expr*`): spread opens exactly ONE
      structure boundary. Sequence values and exact list values open to their
      immediate items; atoms and strings supply themselves as one item.
      C#: `Result.SpreadItems`. -/
  def spreadItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- Deconstruction-openable structure view shared by the sequence-value
      parameter pattern binders: a received sequence value or exact list value
      opens to its immediate items; atoms and strings are not openable (the
      binders apply their own scalar one-item fallback). Function-call argument
      binding never uses this view — a list argument stays one argument.
      C#: `GetSequenceValuePatternItems` / `BindCountedParameterPattern`. -/
  def structureItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | listValue rs => some rs
    | _ => none

  /-- Construction preserves structure; selection projects content.
      Project one selected value to the top-level content it denotes at the
      current boundary, without recursively flattening nested sequence elements.

      Atoms and strings stay atomic. Sequence values project exactly one level
      to their immediate members, and the accompanying count records how many
      top-level values that projection emits. -/
  def projectSelectedContent (selected : Result) : Result × Nat :=
    let items := selected.toItems
    (normalize (sequenceValue items), items.length)

  /-- Count emitted top-level values when a result is already in hand.
      Empty results emit 0. Any non-empty atomic, string, or sequence value
      counts as one value. List values ALWAYS count as one visible value,
      including the empty list `[]` — only the empty SEQUENCE value `()` is
      the invisible-able empty result.

      This is used by `reduce` and `map`, where sequence-value accumulator / mapped
      values are valid as long as the step / transform returns exactly one
      top-level value. -/
  def valueCount : Result -> Nat
    | sequenceValue [] => 0
    | _ => 1

  /-- Projection target view for indexing `:`: a sequence value or exact list
      value opens to its immediate elements; every other value follows
      `toItems`. This opens the TARGET boundary only — the selected element
      itself is returned exactly as stored, so a nested list element stays one
      opaque list. C#: `Result.ProjectionItems`. -/
  def projectionItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- Construction preserves structure; selection projects content.
      `:` selects one top-level item from a sequence or exact list target and
      projects that item's content one level: atoms stay atomic, sequence
      values yield their immediate members, and nested sequence and list
      values remain intact. -/
  def select? (r : Result) (i : Nat) : Option (Result × Nat) :=
    match r.projectionItems[i]? with
    | some selected => some (projectSelectedContent selected)
    | none => none
end Result

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

structure PreparedCallArgumentEvaluation where
  counted : CountedResult
  explicitItems? : Option (List Result) := none
  deriving Repr

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

def lookupAssoc {A} (k : Ident) : Assoc Ident A -> Option A
  | [] => none
  | (k',v)::xs => if k = k' then some v else lookupAssoc k xs

abbrev ValEnv := Assoc Ident Result

/-- Algorithm environment: maps parameter names to algorithms.
    Used for higher-order algorithm parameters — when a caller passes an
    algorithm as an argument, the callee can invoke it by name.
    Parallel to ValEnv (which maps names to Results). -/
abbrev AlgEnv := Assoc Ident Algorithm

namespace AlgEnv
  def lookup (env : AlgEnv) (x : Ident) : Option Algorithm :=
    lookupAssoc x env
end AlgEnv

/-- Counted parameter environment for callback-bound values that must preserve
    expression-level emitted counts, for example higher-order sequence items
    projected through the same one-level rule as `:`. Collecting bindings
    also record their bound value here; since collecting binding collects ONE exact
    immutable list value, those entries always carry emitted count 1 and agree
    with ordinary value-environment lookup (there is no separate raw-supply
    forwarding environment). -/
abbrev CountedParamEnv := Assoc Ident (Prod Result Nat)

namespace CountedParamEnv
  def lookup (env : CountedParamEnv) (x : Ident) : Option (Prod Result Nat) :=
    lookupAssoc x env

  def shadow (env : CountedParamEnv) (names : List Ident) : CountedParamEnv :=
    env.filter (fun entry => !names.contains entry.fst)
end CountedParamEnv

inductive ZeroArgPropertyAccessKind where
  | lexical
  | structural
  deriving Repr, BEq

/-- Lean cache keys use structural representations because the model has
    immutable AST values rather than C# object identities.  The key still
    distinguishes access shape, resolved owner/property, and the current
    lexical/value binding context, so it is intentionally more specific than a
    simple property name. -/
structure ZeroArgPropertyCacheKey where
  accessKind : ZeroArgPropertyAccessKind
  owner      : String
  propertyName : Ident
  propertyAlgorithm : String
  valEnv : String
  algEnv : String
  countedParamEnv : String
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
          (key, value) :: rest
        else
          (existingKey, existingValue) :: insert rest key value
end ZeroArgPropertyCache

/-- Per-run evaluator state. The zero-parameter property cache is part of the
    Lean semantics because property-style `A` and explicit `A()` now have
    distinct observable call shapes. The state is created fresh for each
    top-level `runResult`; it is not general memoization and does not cache
    arbitrary calls or expression results. -/
structure EvalState where
  zeroArgPropertyCache : ZeroArgPropertyCache := []
  deriving Repr

namespace EvalState
  def empty : EvalState := {}
end EvalState

abbrev EvalM (α : Type) := StateT EvalState (Except Error) α

instance {A : Type} : Nonempty (EvalM A) := Nonempty.intro (.error Error.badArity)

/-- Run a sub-computation and capture its `Except` result without committing
    state changes from the failing path. This preserves the older Except-style
    probing behavior used by fallback resolution. -/
def evalAttempt {A : Type} (m : EvalM A) : EvalM (Except Error A) :=
  fun state =>
    match m.run state with
    | .ok (value, nextState) => .ok (.ok value, nextState)
    | .error err => .ok (.error err, state)

def runEvalM (m : EvalM A) : Except Error A :=
  match m.run EvalState.empty with
  | .ok (value, _) => .ok value
  | .error err => .error err

/-- Evaluation context threaded through resolution and evaluation.
    Wraps the algorithm chain (current algorithm + enclosing callers) used for
    both lexical resolution and runtime dispatch.
  algEnv carries algorithm-typed parameter bindings for higher-order dispatch.

  The evaluator state carries the per-run zero-parameter property cache. This
  cache is core KatLang semantics because `A` and `A()` are distinct: property-
  style `A` may read/write the cache, while explicit zero-parameter calls
  bypass only the directly called property's cache entry. The cache is scoped
  to one top-level `runResult`; it is not general memoization and does not
  apply to arbitrary calls. -/
structure EvalCtx where
  callStack : List Algorithm
  algEnv    : AlgEnv := []
  countedParamEnv : CountedParamEnv := []
  deriving Repr

namespace EvalCtx
  def empty : EvalCtx := { callStack := [], algEnv := [], countedParamEnv := [] }
  def push (a : Algorithm) (ctx : EvalCtx) : EvalCtx :=
    { callStack := a :: ctx.callStack, algEnv := ctx.algEnv, countedParamEnv := ctx.countedParamEnv }
  def head? (ctx : EvalCtx) : Option Algorithm := ctx.callStack.head?
  def withAlgEnv (env : AlgEnv) (ctx : EvalCtx) : EvalCtx :=
    { callStack := ctx.callStack, algEnv := env, countedParamEnv := ctx.countedParamEnv }
  def withCountedParamEnv (env : CountedParamEnv) (ctx : EvalCtx) : EvalCtx :=
    { callStack := ctx.callStack, algEnv := ctx.algEnv, countedParamEnv := env }
end EvalCtx

abbrev ValEnv.lookup (env : ValEnv) (x : Ident) : Option Result :=
  lookupAssoc x env

/-- Remove the named bindings from an INHERITED value environment.

    A callee's value environment is its own bindings prepended to the CALLER's
    (`argEnv ++ env`), which is what lets a nested property body still read an
    ancestor-owned parameter. A parameter the call bound only on the ALGORITHM
    channel — a higher-order argument, or any argument whose value evaluation
    failed — contributes no entry to `argEnv`, so without this filter a
    same-named binding inherited from the caller would answer every
    value-position read of that parameter: the callee would silently observe an
    unrelated caller value instead of the argument bound at THIS invocation, and
    which caller parameter names happen to collide with a callee's parameter
    names would become observable. Shadowing the callee's whole parameter list
    is exactly the rule `CountedParamEnv.shadow` already applies to the counted
    tier; names that DO carry a value binding are shadowed by `argEnv` anyway,
    so filtering the tail changes nothing for them.
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

/-- Primary helper: Lookup PropDef by name when the property is exported. -/
def lookupPropDefExportedAny? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.exposure.isExported)

/-- Primary helper: Lookup PropDef by name (public only). -/
def lookupPropDefPublic? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.isPublic && p.exposure.isExported)

/-- Lookup Algorithm from PropDef list (any visibility). -/
def lookupPropAny (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefAny? ps k).map (fun propDef => propDef.alg)

/-- Lookup Algorithm from PropDef list (public only). -/
def lookupPropPublic (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefPublic? ps k).map (fun propDef => propDef.alg)

/-- Check if PropDef list contains a property (any visibility). -/
def hasPropAny (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefAny? ps k).isSome

namespace Algorithm
  def normalCallableParameters (ps : List Ident) : List CallableParameter :=
    ps.map (fun p => { name := p })

  def normalParameters (ps : List Ident) : List ParameterPattern :=
    ParameterPattern.normalPatterns ps

  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ => p
    | .builtin _ => none
    | .conditional p _ _ => p
  def parameterPatterns : Algorithm -> List ParameterPattern
    | .mk _ parameterPatterns _ _ _ => parameterPatterns
    | .builtin _ => []
    | .conditional _ _ _ => []

  def parameters : Algorithm -> List CallableParameter
    | a => (parameterPatterns a).flatMap ParameterPattern.captures

  def params : Algorithm -> List Ident
    | a => (parameters a).map (fun parameter => parameter.name)
  def paramKinds : Algorithm -> List ParameterKind
    | a => (parameters a).map (fun parameter => parameter.kind)
  def callableSignature (name : Ident) (a : Algorithm) : CallableSignature :=
    { name := name, parameters := parameters a }
  def opens : Algorithm -> List Expr
    | .mk _ _ op _ _ => op
    | .builtin _ => []
    | .conditional _ op _ => op
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ => pr
    | .builtin _ => []
    | .conditional _ _ _ => []
  /-- The algorithm's output as an `OutputBundle` — ordered original written
      expression rows. The algorithm is the scope-owning DEFINITION of this
      bundle; the bundle itself owns no scope. -/
  def output : Algorithm -> OutputBundle
    | .mk _ _ _ _ out => out
    | .builtin _ => []
    | .conditional _ _ _ => []

  /-- Access branches for conditional algorithms. Returns [] for other forms. -/
  def branches : Algorithm -> List CondBranch
    | .conditional _ _ bs => bs
    | _ => []

  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ parameterPatterns op pr out => .mk p parameterPatterns op pr out
    | .builtin b => .builtin b
    | .conditional _ op bs => .conditional p op bs

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
    | .mk p oldPatterns op pr out => .mk p (mergeParameterPatterns oldPatterns ps) op pr out
    | .builtin b => .builtin b
    | .conditional p op bs => .conditional p op bs

  def withParameterPatterns (patterns : List ParameterPattern) : Algorithm -> Algorithm
    | .mk p _ op pr out => .mk p patterns op pr out
    | .builtin b => .builtin b
    | .conditional p op bs => .conditional p op bs

  def hasStructuredParameterPattern (a : Algorithm) : Bool :=
    ParameterPattern.hasStructured (parameterPatterns a)

  def hasRepeatedParameterNames (a : Algorithm) : Bool :=
    ParameterPattern.hasRepeatedCaptureNames (parameterPatterns a)

  def requiresPatternBinding (a : Algorithm) : Bool :=
    hasStructuredParameterPattern a || hasRepeatedParameterNames a

  def topLevelParameterKind? (a : Algorithm) (name : Ident) : Option ParameterKind :=
    ParameterPattern.topLevelCaptureKind? name (parameterPatterns a)

  def declaresParameterName (a : Algorithm) (name : Ident) : Bool :=
    (parameterPatterns a).any (ParameterPattern.containsCaptureName name)

  def collectingParam? (a : Algorithm) : Option (Nat × Ident) :=
    if hasStructuredParameterPattern a then
      none
    else
      let rec go : Nat -> List CallableParameter -> Option (Nat × Ident)
        | _, [] => none
        | index, parameter :: parameters =>
            match parameter.kind with
            | .collecting => some (index, parameter.name)
            | .normal => go (index + 1) parameters
      go 0 (parameters a)

  /-- A callable whose top-level parameter list consumes the supplied call
      argument stream: any top-level collecting capture, whether a lone collecting binding
      `*name` or a comma shape such as `x, *y, z`. A plain sequence-valued
      argument stays one supplied argument; only explicit spread opens it first. -/
  def usesItemSupplyBinding (a : Algorithm) : Bool :=
    (collectingParam? a).isSome

  /-- Classify a same-name clause family after all of its clauses are known.
      This is the real ordinary-vs-conditional decision boundary.

      A same-name clause group is ordinary only when it contains exactly one
      clause and that sole head is a recursive capture/sequence-value parameter pattern.
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
      it has exactly one clause and that sole head is a recursive capture/sequence-value
      parameter pattern; otherwise the whole family elaborates as
      `Algorithm.conditional`.

      This preserves higher-order ordinary call semantics for single-clause
      families such as `Apply(f) = f(4)` and
      `Choose(x, predicate) = if(predicate(x), x, 0)`, and preserves sequence-value
      ordinary parameter shapes such as `PairSum((x, y)) = x + y`, while keeping
      multi-clause and literal/mixed families conditional.

      Opens handling (descriptive, relied on by the front-end): the
      conditional's own opens list is taken from the FIRST branch's body, and
      every branch body also keeps its own opens.  Surface clause bodies are
      expressions, so in practice all clause bodies of a family carry the same
      (usually empty) opens; the front-end does not produce families whose
      branch bodies declare differing opens. -/
  def elaborateClauseGroup : List CondBranch -> Algorithm
    | [branch] =>
        match clauseGroupDefinitionKind [branch] with
        | .ordinary patterns => branch.body.withParameterPatterns patterns
        | .conditional =>
            .conditional (parent branch.body) (opens branch.body) [{
              pattern := branch.pattern
              body := branch.body.withParams []
            }]
    | branches =>
        .conditional
          (branches.head?.map (fun branch => parent branch.body) |>.join)
          (branches.head?.map (fun branch => opens branch.body) |>.getD [])
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
    ScopeCtx.mk (parent a) (opens a) (props a)

  def isBuiltin : Algorithm -> Bool
    | .builtin _ => true
    | _          => false

  /-- Algorithm-level explicit parameters define a closed direct-call interface
      and therefore require the algorithm to define output.  Surface front-ends
      must not append inferred implicit parameters to this interface; free names
      in explicitly parameterized bodies must resolve lexically or be reported as
      undeclared. -/
  def declaresExplicitParamsWithoutOutput : Algorithm -> Bool
    | .mk _ parameterPatterns _ _ out => !parameterPatterns.isEmpty && out.isEmpty
    | .builtin _ => false
    | .conditional _ _ _ => false

  /-- Unfiltered property lookup (sees private properties). -/
  def lookupProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropAny (props a) k

  /-- Public-only property lookup (for open resolution). -/
  def lookupPublicProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropPublic (props a) k

  /-- Lookup PropDef by name (any visibility). -/
  def lookupPropDefAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefAny? (props a) k

  /-- Lookup PropDef by name when the property is exported. -/
  def lookupPropDefExportedAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefExportedAny? (props a) k

  /-- Lookup PropDef by name (public only). -/
  def lookupPropDefPublic? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefPublic? (props a) k

  /-- True when a conditional algorithm has a branch body defining the given property. -/
  def conditionalBranchesDefineProperty : Algorithm -> Ident -> Bool
    | .conditional _ _ bs, k => bs.any (fun br => hasPropAny (props br.body) k)
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
    | .conditional _ _ bs =>
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
    | .conditional _ _ bs =>
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
    | .mk _ _ _ ps _ =>
        let names := ps.map (·.name)
        let rec go : List Ident -> List Ident -> Option Ident
          | [],        _    => none
          | n :: rest, seen =>
              if seen.elem n then some n
              else go rest (n :: seen)
        go names []
    | _ => none

  /-- Check whether the branch list of an Algorithm.conditional contains
      match-equivalent patterns.  Returns `true` if a duplicate is found.
      This enforces the unique branch pattern invariant. -/
  def hasDuplicateBranchPatterns : Algorithm -> Bool
    | .conditional _ _ bs =>
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

mutual
  /-- Pre-evaluation structural validation over a whole algorithm tree:
      - explicit algorithm parameters only appear on algorithms that define
        output (`explicitParamsRequireOutput`)
      - conditional algorithms have uniform top-level branch pattern arity and
        uniform top-level branch output arity (`branchArityMismatch`,
        `branchOutputArityMismatch`)

      `name` labels conditional arity diagnostics with the nearest enclosing
      property name; anonymous algorithms report the placeholder
      `conditional`. -/
  partial def validateExplicitParamOutputInvariant (a : Algorithm)
      (name : Ident := "conditional") : EvalM Unit := do
    match a with
    | .mk _ parameters op pr out =>
        if !parameters.isEmpty && out.isEmpty then
          .error Error.explicitParamsRequireOutput
        for openExpr in op do
          validateExplicitParamOutputInvariantExpr openExpr
        for prop in pr do
          validateExplicitParamOutputInvariant prop.alg prop.name
        for expr in out do
          validateExplicitParamOutputInvariantExpr expr
    | .builtin _ => pure ()
    | .conditional _ op branches =>
        validateConditionalBranchArities name a
        for openExpr in op do
          validateExplicitParamOutputInvariantExpr openExpr
        for branch in branches do
          validateExplicitParamOutputInvariant branch.body name

  /-- Traverse expressions so nested block literals and call-argument
      algorithms also satisfy the same pre-evaluation invariants. -/
  partial def validateExplicitParamOutputInvariantExpr : Expr -> EvalM Unit
    | .param _ => pure ()
    | .num _ => pure ()
    | .stringLiteral _ => pure ()
    | .resolve _ => pure ()
    | .unary _ operand =>
        validateExplicitParamOutputInvariantExpr operand
    | .binary _ left right => do
        validateExplicitParamOutputInvariantExpr left
        validateExplicitParamOutputInvariantExpr right
    | .index target selector => do
        validateExplicitParamOutputInvariantExpr target
        validateExplicitParamOutputInvariantExpr selector
    | .sequenceConstruct left right => do
      validateExplicitParamOutputInvariantExpr left
      validateExplicitParamOutputInvariantExpr right
    | .emptySequence _ => pure ()
    | .sequenceSpread operand => do
        validateExplicitParamOutputInvariantExpr operand
    | .listLiteral items =>
        items.forM validateExplicitParamOutputInvariantExpr
    | .algorithmExpr alg =>
        validateExplicitParamOutputInvariant alg
    | .capture rows =>
        rows.forM validateExplicitParamOutputInvariantExpr
    | .call fn args => do
        validateExplicitParamOutputInvariantExpr fn
        args.forM validateExplicitParamOutputInvariantExpr
    | .dotMember target _ fallback args? => do
        validateExplicitParamOutputInvariantExpr target
        -- The stored lexical fallback is a real child (Resolve/Param for
        -- front-end trees, but hand-built trees could hide algorithms in it),
        -- so the validation walk covers it like every other reference.
        validateExplicitParamOutputInvariantExpr fallback
        match args? with
        | some args => args.forM validateExplicitParamOutputInvariantExpr
        | none => pure ()
end

namespace ScopeCtx
  def parent : ScopeCtx -> Option ScopeCtx
    | .mk p _ _ => p
  def opens : ScopeCtx -> List Expr
    | .mk _ op _ => op
  def props : ScopeCtx -> List PropDef
    | .mk _ _ ps => ps
end ScopeCtx

namespace Algorithm
  /-- Create a temporary algorithm from a ScopeCtx for open resolution. -/
  def forOpens (sc : ScopeCtx) : Algorithm :=
    .mk (some sc) [] (ScopeCtx.opens sc) [] []

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

def wireToCaller (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match ctx.callStack.head? with
  | some caller => Algorithm.childOf caller a
  | none        => a

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

/-- Coerce a Result to Int, or raise typeMismatch for strings, badArity otherwise. -/
def expectInt (r : Result) : EvalM Int :=
  match r with
  | .str _ => .error (Error.typeMismatch "Expected a number, got a string")
  | _ => match Result.asInt? r with
    | some n => pure n
    | none   => .error Error.badArity

partial def resultDiagnosticString : Result -> String
  | .atom value => toString value
  | .str value => "'" ++ value ++ "'"
  | .sequenceValue items => "(" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ ")"
  | .listValue items => "[" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ "]"

def numericScalarOperandDescription : Result -> String
  | .sequenceValue items => s!"a sequence value with {items.length} sequence element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.sequenceValue items)}"
  | .str value => "a string: '" ++ value ++ "'"
  | .atom value => s!"numeric value {value}"
  | .listValue items => s!"a list value with {items.length} element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.listValue items)}"

def requireNumericScalarOperand (op : BinaryOp) (side : String) (value : Result) : EvalM Int :=
  match Result.asInt? value with
  | some number => pure number
  | none => .error (Error.typeMismatch
      s!"operator `{op.symbol}` expects numeric scalar operands, but the {side} operand was {numericScalarOperandDescription value}")

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

structure CountedParameterPatternBindings where
  countedParamEnv : CountedParamEnv := []
  deriving Repr

partial def bindParams (ps : List Ident) (vs : List Result) : EvalM ValEnv :=
  match ps, vs with
  | [], [] => .ok []
  | p::ps', v::vs' => do
      let rest <- bindParams ps' vs'
      pure ((p,v)::rest)
  | _, _ => .error (Error.arityMismatch ps.length vs.length)

/-- The three merge helpers below are transparent structural recursion used by
    pattern binding. They are intentionally `def`s (not `partial def`s) so bridge
    theorems can unfold the real binder path; each recursion consumes `incoming`,
    so the behavior is unchanged. -/
def mergeEqualValEnv (acc incoming : ValEnv) : EvalM ValEnv :=
  match incoming with
  | [] => pure acc
  | (name, value) :: rest =>
      match acc.lookup name with
      | some existing =>
          if existing == value then mergeEqualValEnv acc rest
          else .error Error.badArity
      | none => mergeEqualValEnv (acc ++ [(name, value)]) rest

def mergeEqualCountedParamEnv (acc incoming : CountedParamEnv)
    : EvalM CountedParamEnv :=
  match incoming with
  | [] => pure acc
  | (name, value) :: rest =>
      match acc.lookup name with
      | some existing =>
          if existing.fst == value.fst then mergeEqualCountedParamEnv acc rest
          else .error Error.badArity
      | none => mergeEqualCountedParamEnv (acc ++ [(name, value)]) rest

def mergePatternAlgEnv (leftValues rightValues : ValEnv)
    (acc incoming : AlgEnv) : EvalM AlgEnv :=
  match incoming with
  | [] => pure acc
  | (name, value) :: rest =>
      match AlgEnv.lookup acc name with
      | some _ =>
          if (leftValues.lookup name).isSome && (rightValues.lookup name).isSome then
            mergePatternAlgEnv leftValues rightValues acc rest
          else
            .error (Error.typeMismatch
              "Repeated bind equality is not supported for algorithm-only arguments")
      | none => mergePatternAlgEnv leftValues rightValues (acc ++ [(name, value)]) rest

/-- Argument passing rule: a single atom is wrapped in a one-element list;
    a sequence value is unpacked into its elements.  This is the canonical ABI for
    translating an evaluated Result into positional arguments for bindParams.
    Exact list values are NOT unpacked: call-argument binding preserves a list
    as one argument; only an explicit caller-site spread `value*` opens it. -/
def unpackArgs (r : Result) : List Result :=
  match r with
  | .atom _ => [r]
  | .str _  => [r]
  | .sequenceValue rs => rs
  | .listValue _ => [r]

/-- How a call's argument bundle was assembled: ordinary written argument
    slots, or a lexical dot-call bundle whose FIRST slot is the injected
    receiver segment. The injected receiver is always ONE leading segment for
    arity checking and prefix/suffix allocation (never pre-expanded), is
    evaluated through the raw counted receiver-segment path, and carries its
    evaluated top-level supply (`ParameterPatternInput.collectingSegmentCount?`)
    so only a flat top-level collecting parameter allocated the segment
    consumes the supply items. Receiver assembly never inspects the resolved
    callee. C#: `CallArgumentAssembly`. -/
inductive CallArgumentAssembly where
  | ordinaryArguments
  | injectedDotReceiverLeading
  deriving Repr, BEq

def CallArgumentAssembly.isInjectedDotReceiverLeading : CallArgumentAssembly -> Bool
  | .injectedDotReceiverLeading => true
  | .ordinaryArguments => false

/-- Bind algorithm-typed parameters: zip parameter names with algorithms.
    Only includes entries where the argument resolved to an algorithm.
    Result entries are skipped (they go through bindParams / ValEnv). -/
def bindAlgParams (ps : List Ident) (algs : List (Option Algorithm)) : AlgEnv :=
  match ps, algs with
  | [], _ => []
  | _, [] => []
  | p::ps', a::as' =>
    match a with
    | some alg => (p, alg) :: bindAlgParams ps' as'
    | none     => bindAlgParams ps' as'

/-- One call argument segment prepared for parameter binding. Every segment
    has a value view (`value?`); an injected dot-call receiver segment
    additionally carries `collectingSegmentCount?` — the raw emitted count of
    its counted evaluation — as an EPHEMERAL collecting supply view. A fixed
    parameter always binds the value view; only a flat top-level collecting
    parameter that is allocated the segment consumes the supply view
    (one level, never recursive). The field is data-only and never propagated
    into nested pattern inputs, parameter environments, or collected lists.
    C#: `ParameterPatternInput` (via `VariadicCallItem`). -/
structure VariadicItem where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  explicitItems? : Option (List Result) := none
  collectingSegmentCount? : Option Nat := none
  deriving Repr

structure FlatFixedCallSlot where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  deriving Repr

structure CallableCallItem where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  skipMissingValue : Bool := false
  deriving Repr

structure ParameterPatternInput where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  explicitSequenceValueItems? : Option (List Result) := none
  collectingSegmentCount? : Option Nat := none
  deriving Repr

structure ParameterPatternBindings where
  argEnv : ValEnv := []
  countedParamEnv : CountedParamEnv := []
  algEnv : AlgEnv := []
  deriving Repr

/-- Builtin collection-item view of the bound collection argument: opens
  exactly one outer sequence or exact-list boundary to its immediate items;
  any other value supplies itself as one item (a scalar is a one-element
  collection). Never recursive — nested sequence values and nested list
  values stay intact as single items.
  Applied strictly AFTER ordinary fixed parameter binding, to the already
  bound `collection` parameter only — argument boundaries are never altered
  before binding. Function-call parameter binding never uses this view, and
  assignment deconstruction opens its received value through the
  sequence-value parameter pattern instead. C#: `BuiltinCollectionItems`. -/
def builtinCollectionItems : Result -> List Result
  | .sequenceValue elems => elems
  | .listValue elems => elems
  | value => [value]

def variadicItemToPatternInput (item : VariadicItem) : ParameterPatternInput :=
  { value? := item.value?,
    algorithm? := item.algorithm?,
    error? := item.error?,
    explicitSequenceValueItems? := item.explicitItems?,
    collectingSegmentCount? := item.collectingSegmentCount? }

/-- Compatibility fallback for manually constructed core conditionals.
  Surface clause elaboration should already route eligible single-branch
  ordinary clause groups through `Algorithm.elaborateClauseGroup`, producing
  `Algorithm.mk` directly. This helper intentionally keeps only the stricter
  flat multi-binder `.conditional` core shape call-compatible with ordinary
  user algorithms, so evaluator fallback semantics do not silently broaden to
  bare single-binder conditionals. -/
def flatBinderUserEquivalent? (callee : Algorithm) : Option Algorithm :=
  match callee with
  | .conditional _ _ [branch] =>
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

/-- Value-position access to a conditional algorithm cannot select a branch,
    so it must fail instead of silently forcing the conditional's empty output
    list. Mirrors the no-argument dot-call dispatch: a flat multi-binder core
    equivalent reports its ordinary call arity, and any other conditional
    reports `noMatchingBranch`. Returns `none` for non-conditional algorithms. -/
def conditionalValueAccessError? (name : String) (a : Algorithm) : Option Error :=
  match a with
  | .conditional _ _ _ =>
      match flatBinderUserEquivalent? a with
      | some simple => some (Error.arityMismatch (Algorithm.params simple).length 0)
      | none => some (Error.noMatchingBranch name)
  | _ => none

/-- Attach context to any error raised by `m`. -/
def withCtx (ctx : String) (m : EvalM A) : EvalM A :=
  fun state =>
    match m.run state with
    | .ok result => .ok result
    | .error err => .error (Error.withContext ctx err)

/-- Attach property context specifically to a missing-output failure.
    Other errors are preserved unchanged. -/
def withMissingOutputCtx (ctx : String) (m : EvalM A) : EvalM A :=
  fun state =>
    match m.run state with
    | .ok result => .ok result
    | .error .missingOutput => .error (.withContext ctx .missingOutput)
    | .error err => .error err

def isMissingOutputError : Error -> Bool
  | .missingOutput => true
  | .withContext _ inner => isMissingOutputError inner
  | _ => false

/-- The empty sequence value expression `()`. -/
def emptyResultExpr : Expr :=
  .emptySequence 0

/-- True when a Result is the empty sequence value or a redundant chain of
    one-item sequences ending in it. -/
def isEmptySequenceChain : Result -> Bool
  | .sequenceValue [] => true
  | .sequenceValue [inner] => isEmptySequenceChain inner
  | _ => false

/-- Reify a normalized Result as an expression that evaluates back to the same
    value/shape. Redundant empty-sequence chains reify as canonical `()`; other
    sequence-value results become block expressions. -/
def resultToExpr : Result -> Expr
  | .atom n => .num n
  | .str s => .stringLiteral s
  | .sequenceValue rs =>
      if isEmptySequenceChain (.sequenceValue rs) then
        .emptySequence 0
      else
        -- A reified sequence value is a capture of its already-evaluated
        -- items — a value boundary, not an algorithm.
        .capture (rs.map resultToExpr)
  -- Exact list values reify as list literals so they round-trip losslessly
  -- (a reified `()` element stays one visible list element).
  | .listValue rs => .listLiteral (rs.map resultToExpr)

/-- Validate the output shape required by counted builtins that must emit
    exactly one top-level value.

    Non-empty sequence values are valid; the empty sequence value `()` and
    multiple top-level outputs are rejected. (An empty-sequence output is a visible
    slot at the output boundary, but these builtins require a substantive single
    element.) -/
def expectSingleValueWith (msg : String) (out : CountedResult) : EvalM Result :=
  match out with
  | (Result.sequenceValue [], 1) => .error (Error.withContext msg Error.badArity)
  | (value, 1) => pure value
  | _ => .error (Error.withContext
    msg
    Error.badArity)

/-- Validate the output shape required by `reduce`.
    The step must emit exactly one accumulator value. -/
def expectSingleAccumulator (out : CountedResult) : EvalM Result :=
  expectSingleValueWith
    "reduce step must return a single accumulator value"
    out

/-- Validate the output shape required by `map`.
    The transform must emit exactly one mapped element: one atom, one string,
    one sequence value, or one exact list value is valid (the empty list `[]`
    counts as one value), while empty-sequence and multi-output results are
    rejected. -/
def expectSingleMappedElement (out : CountedResult) : EvalM Result :=
  expectSingleValueWith
    "map transform must return a single element"
    out

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

/-- Materialize a collection-producing builtin's kept/projected items as ONE
    exact immutable list value. Unlike canonical arity capture (ordinary
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

/-- True when an argument's resolved algorithm meaning is genuinely
    FUNCTION-shaped — a builtin, a conditional clause family, or an algorithm
    declaring parameters/patterns — as opposed to a zero-parameter VALUE
    property that merely resolved through the dual algorithm channel. Used to
    decide whether a valueless argument bound by a collecting parameter gets the targeted
    "collects values, but ... is a function" diagnostic or surfaces its
    genuine value-evaluation error. C#: `IsFunctionShapedAlgorithm`. -/
def Algorithm.isFunctionShaped : Algorithm -> Bool
  | .builtin _ => true
  | .conditional _ _ _ => true
  | a => !(Algorithm.params a).isEmpty || !(Algorithm.parameterPatterns a).isEmpty

/-- Collect the item segment assigned to a collecting binding as ONE exact immutable list value.

    KatLang distinguishes three item-supply operations by receiver purpose:

    - `capture : Supply -> Value` — ordinary value/output capture, the
      canonicalizing boundary `Result.normalize (Result.sequenceValue xs)`
      (singleton erasure applies: `x = 1, 2, 3` is `(1, 2, 3)`, one supplied
      item is itself);
    - `collect : Supply -> ListValue` — THIS operation: a collecting binding (collecting parameter)
      materializes exactly the assigned items as one exact immutable list
      (`collectSegment [] = []`, `collectSegment [v] = [v]`, never erased);
    - `spread : Value -> Supply` — the spread marker (`Result.spreadItems`), which
      opens one sequence OR list boundary.

    Every collecting binding — deconstruction collecting bindings, single collecting parameters,
    and mixed prefix/collecting/suffix parameter lists — binds its assigned middle
    supply through this single helper, after the receiver-specific supply
    preparation (call binding preserves argument slots; deconstruction may
    open one lone sequence or list). The round trip
    `Result.spreadItems (collectSegment xs) = xs` makes collecting-parameter forwarding
    ordinary list spread: `Forward(*items) = Target(items*)` re-supplies
    exactly the collected items with no hidden raw-supply metadata. A collecting
    value is one visible value, so its emitted count is always 1 (including
    `[]`). C#: `CollectSegment` (inside `CreateCollectingCapture`). -/
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
    construction has already canonicalized redundant unary empty structure. It is
    applied only to public result boundaries, never to internal
    body/root output accumulation (`evalAlgOutputCountedCore`), which must keep
    its multi-item counts. (Collecting parameter storage needs no re-count:
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
    Used by evaluation together with `peelSequenceSpreadLayers`: stacked
    spread is COMPOSITIONAL (`A**` agrees with `(A*)*`) — each extra written
    layer re-captures the previous layer's item supply into one value
    (`Result.normalize ∘ Result.sequenceValue`, the ordinary expression
    capture) and spreads that captured value, applied iteratively
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

/-- Reify a counted argument shape as a zero-parameter algorithm that preserves
    the same value and emitted top-level count when evaluated. -/
def countedArgAlgorithm (arg : CountedResult) : Algorithm :=
  let output :=
    match arg with
    | (_, 0) => [emptyResultExpr]
    | _ => (countedTopLevelValues arg).map resultToExpr
  Algorithm.mk none [] [] [] output

/-- Ordinary call-style unpacking for a pre-evaluated explicit argument whose
    expression-level emitted count is already known.

    A final explicit argument may still unpack its value across the remaining
    parameters, matching `callee(S:i)` and preserving the one-level projected
    callback item rule without changing global call semantics. -/
def unpackCountedArg (arg : CountedResult) : List CountedResult :=
  unpackArgs arg.fst |>.map (fun value => (value, Result.valueCount value))

/-- Bind callback parameters through counted argument semantics.
    This preserves the difference between a projected callback item that emits
    several top-level values and an ordinary sequence value that still emits one.
    The bound parameter remains a parameter value, not a callable algorithm. -/
partial def bindCountedCallbackParams (ps : List Ident) (args : List CountedResult)
    : EvalM CountedParamEnv := do
  let rec collect
      (remainingParams : List Ident)
      (remainingArgs : List CountedResult)
      : EvalM (List Ident × List CountedResult) :=
    match remainingParams, remainingArgs with
    | [], _ => pure ([], [])
    | params, [] => pure (params, [])
    | p :: ps', [arg] =>
        match ps' with
        | [] => pure ([p], [arg])
        | _ => pure (p :: ps', unpackCountedArg arg)
    | p :: ps', arg :: args' => do
        let (boundParams, boundArgs) <- collect ps' args'
        pure (p :: boundParams, arg :: boundArgs)
  if args.length > ps.length then
    .error (Error.arityMismatch ps.length args.length)
  else do
    let (boundParams, boundArgs) <- collect ps args
    if boundParams.length != boundArgs.length then
      .error (Error.arityMismatch boundParams.length boundArgs.length)
    else
      pure (List.zip boundParams boundArgs)

mutual
partial def bindCountedParameterPattern (pattern : ParameterPattern) (input : CountedResult)
    : EvalM CountedParameterPatternBindings := do
  match pattern with
  | .capture parameter =>
      match parameter.kind with
      | .normal => pure { countedParamEnv := [(parameter.name, input)] }
      | .collecting => .error Error.badArity
  | .sequenceValue items =>
      let sequenceValueItems? :=
        -- A received sequence value or exact list value opens to its
        -- immediate items (`Result.structureItems?`): the deconstruction
        -- receiver opens ONE lone structure boundary of either kind.
        match Result.structureItems? input.fst with
        | some structureItems => some structureItems
        -- This counted matcher is the callback binding path. Callback
        -- deconstruction is intentionally deferred; counted callback binding
        -- remains strict to preserve existing callback semantics and Lean/C#
        -- parity, so its scalar fallback stays singleton-only to match the C#
        -- `BindCountedParameterPattern`. The scalar one-item normalization for
        -- assignment and function-parameter deconstruction lives in the
        -- non-counted `bindParameterPattern` instead.
        | none => if items.length == 1 then some [input.fst] else none
      match sequenceValueItems? with
      | none => .error Error.badArity
      | some sequenceValueItems =>
          let nestedInputs := sequenceValueItems.map (fun value => (value, Result.valueCount value))
          bindCountedParameterPatternList items nestedInputs

partial def bindCountedParameterPatternList (patterns : List ParameterPattern)
  (inputs : List CountedResult) : EvalM CountedParameterPatternBindings := do
  let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
    | [], _ => none
    | (.capture parameter) :: rest, index =>
        match parameter.kind with
        | .collecting => some (index, parameter)
        | .normal => findCollecting rest (index + 1)
    | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
  let merge (left right : CountedParameterPatternBindings)
      : EvalM CountedParameterPatternBindings := do
    let countedParamEnv <- mergeEqualCountedParamEnv left.countedParamEnv right.countedParamEnv
    pure { countedParamEnv := countedParamEnv }
  let rec bindPairs : List ParameterPattern -> List CountedResult -> EvalM CountedParameterPatternBindings
    | [], [] => pure {}
    | pattern :: patterns', input :: inputs' => do
        let current <- bindCountedParameterPattern pattern input
        let rest <- bindPairs patterns' inputs'
        merge current rest
    | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
  match findCollecting patterns 0 with
  | none =>
      if patterns.length != inputs.length then
        .error (Error.arityMismatch patterns.length inputs.length)
      else
        bindPairs patterns inputs
  | some (collectingIndex, collectingParameter) =>
      let required := patterns.length - 1
      if inputs.length < required then
        .error (Error.arityMismatch required inputs.length)
      else
        let prefixPatterns := patterns.take collectingIndex
        let prefixInputs := inputs.take collectingIndex
        let suffixCount := patterns.length - collectingIndex - 1
        let suffixPatterns := patterns.drop (collectingIndex + 1)
        let suffixInputs := inputs.drop (inputs.length - suffixCount)
        let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
        let prefixBindings <- bindPairs prefixPatterns prefixInputs
        let suffixBindings <- bindPairs suffixPatterns suffixInputs
        let capturedValues := capturedInputs.map Prod.fst
        -- Collecting binding COLLECTS: the assigned supply becomes one exact
        -- immutable list value, emitted count 1 (a list is one visible value).
        let captured := collectSegment capturedValues
        let capturedBinding := (collectingParameter.name, (captured, 1))
        let collectingBindings : CountedParameterPatternBindings :=
          { countedParamEnv := [capturedBinding] }
        let withCollecting <- merge prefixBindings collectingBindings
        merge withCollecting suffixBindings
      end

/-- Callback binding for a flat callee whose top-level parameters include a
    collecting parameter. The callback argument supply keeps the established
    flat-callback row convention: when fewer argument slots are supplied than
    top-level parameters, the final supplied argument opens into its items
    (matching `callee(S:i)`; exact lists stay opaque), exactly as
    `bindCountedCallbackParams` does for fixed-only flat callees. The resulting
    slots then bind through the shared prefix/collecting/suffix binder, so the collecting
    parameter COLLECTS its allocated slots as one exact immutable list.
    C#: `BindCountedCallbackParameterPatternList`. -/
def bindCountedCallbackParameterPatternList (patterns : List ParameterPattern)
    (args : List CountedResult) : EvalM CountedParameterPatternBindings :=
  let slots :=
    if args.length != 0 && args.length < patterns.length then
      match args.getLast? with
      | some last => args.dropLast ++ unpackCountedArg last
      | none => args
    else
      args
  bindCountedParameterPatternList patterns slots

def describeSequenceItem : Result -> String
  | .atom n => s!"numeric value {n}"
  | .str s => s!"string value {repr s}"
  | .sequenceValue [] => "empty sequence value"
  | .sequenceValue _ => "sequence value"
  | .listValue [] => "empty list value"
  | .listValue _ => "list value"

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

inductive PreparedSequenceBuiltinSuffixArg where
  | algorithm (value : Algorithm)
  | value (value : Result)
  | wholeNumber (value : Int)
  deriving Repr

structure BoundSequenceBuiltinArguments where
  preparedInput : PreparedSequenceBuiltinInput
  iterationItems : List CountedResult
  suffixArgs : List PreparedSequenceBuiltinSuffixArg
  deriving Repr

structure ResolvedArgumentAlgorithm where
  algorithm : Algorithm
  spreadsSequence : Bool := false
  deriving Repr

def intPow (b : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => b * intPow b n

/-- Negative integer exponents follow the C# reference semantics:
    - `0 ^ negative` is a domain error,
    - bases `1` and `-1` have exact integer reciprocals,
    - any other base yields a fractional reciprocal (for example `2 ^ -1 = 0.5`
      in the decimal runtime), which the Int-valued Lean core cannot represent.

    Instead of silently truncating fractional reciprocals to `0`, the core
    raises an explicit error. This is a documented limitation of the integer
    numeric model, not a behavior the runtime should copy. -/
def negativeIntPow (base exponent : Int) : EvalM Result :=
  if base == 0 then
    .error (Error.illegalInEval "zero cannot be raised to a negative integer exponent")
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
  -- A capture is a value boundary, not algorithm/namespace identity, so
  -- `open (M)` is NOT an open form: it is rejected by open-form validation
  -- with badOpenForm, exactly like a spread-marked target.
  | .resolve n       => some (.resolve n)
  -- Only argumentless dot paths are open forms. The C# front end rejects a
  -- Grace-marked open target such as `open A~.B` before Lean encoding; valid
  -- graced dot sources otherwise encode as the same dotMember as ordinary dot.
  | .dotMember o n _ none => some (.dotCall o n)
  | _                => none          -- capture, argument-bearing dot forms, call, and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

/-- Human-readable constructor kind for diagnostics. -/
def Expr.kind : Expr -> String
  | .param _      => "param"
  | .num _        => "num"
  | .stringLiteral _ => "stringLiteral"
  | .unary _ _    => "unary"
  | .binary _ _ _ => "binary"
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
  canonicalizes repeated ordinary parentheses back to `()`. -/
def emptySequenceText (depth : Nat) : String :=
  String.ofList (List.replicate (depth + 1) '(' ++ List.replicate (depth + 1) ')')

/-- Diagnostic expression names use KatLang source syntax; `.index` renders as
  `target:selector`, never `target[selector]` (`[...]` is exact list literal
  syntax). Indexing is postfix and binds tighter than unary and every binary
  operator, so those operands need parentheses in target position: `-A:0` reads
  as `-(A:0)`, so the target of an index over a unary must render `(-A):0`.
  Postfix targets are left-associative and render faithfully bare (`A:0:1`).
  C#: `Evaluator.OpenExprIndexTargetName`. -/
def indexTargetNeedsParens : Expr -> Bool
  | .unary _ _    => true
  | .binary _ _ _ => true
  | _             => false

/-- The index selector is a primary in source syntax, so any form that would
  continue the postfix chain rebinds to the target instead (`A:B.C` reads as
  `(A:B).C`, `A:B:C` as `(A:B):C`, `A:f(0)` as adjacency), and a bare negative
  literal (`A:-1`) is not selector syntax at all.
  C#: `Evaluator.OpenExprIndexSelectorName`. -/
def indexSelectorNeedsParens : Expr -> Bool
  | .unary _ _      => true
  | .binary _ _ _   => true
  | .call _ _       => true
  | .dotMember _ _ _ _ => true
  | .index _ _      => true
  | .sequenceSpread _ => true
  | .num v          => decide (v < 0)
  | _               => false

/-- `^` binds tighter than prefix unary on the LEFT (the base), so a unary
  base — and a literal that renders with a leading minus — must keep its
  parentheses: bare `-a ^ b` reads back as `-(a ^ b)`. The exponent side
  re-enters the unary level in source syntax, so this never applies to the
  right operand (`a ^ -b` renders bare and reads back with the same AST).
  C#: `ExprNameRenderer.PowerBaseNeedsParens`. -/
def powerBaseNeedsParens : Expr -> Bool
  | .unary _ _ => true
  | .num v     => decide (v < 0)
  | _          => false

/-- This MINIMAL renderer models only structural reference forms; every other
  kind (`.num`, `.param`, `.binary`, ...) renders as the `(kind)` fallback, so
  C#'s merged `OpenExprName` prints more detail for them. That gap is
  pre-existing and uniform across `.dotCall`, `.sequenceConstruct`,
  `.sequenceSpread`, and `.index` alike — it is a property of this renderer's
  coverage, not of indexing. -/
def openExprNameIndexSelectorNeedsParens : Expr -> Bool
  | .dotMember _ _ _ _ => true
  | .index _ _        => true
  | .sequenceSpread _ => true
  | _                 => false

/-- Extract a descriptive name from an open expression for error messages.
  See `openExprNameIndexSelectorNeedsParens` for this renderer's coverage gap. -/
def openExprName (e : Expr) : String :=
  match e with
  | .resolve n => n
  | .dotMember o n _ _ =>
      openExprName o ++ "." ++ n
  -- Indexing is source-faithful postfix `target:selector`, never the `(index)`
  -- kind fallback. Only the forms this renderer prints BARE can continue the
  -- postfix chain and rebind; every unmodelled kind is already self-delimiting
  -- as `(kind)`, so parenthesizing it again would only double the parentheses.
  | .index target selector =>
      let selectorName := openExprName selector
      openExprName target ++ ":" ++
        (if openExprNameIndexSelectorNeedsParens selector then "(" ++ selectorName ++ ")"
         else selectorName)
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

partial def exprDiagnosticName : Expr -> String
  | .param name => name
  | .num value => toString value
  | .stringLiteral value => "'" ++ value ++ "'"
  -- Under power-over-unary precedence, a bare unary operand reads back
  -- correctly even over a power (`-a ^ b` IS `-(a ^ b)`); binary operands of
  -- OTHER operators keep this renderer's established bare convention (see the
  -- index comment below for how it diverges from C# on nested operands).
  | .unary .minus operand => "-" ++ exprDiagnosticName operand
  | .unary .not operand => "not " ++ exprDiagnosticName operand
  -- The LEFT operand of `^` is postfix-level in source syntax, so a unary or
  -- negative-literal base must keep parentheses (`(-a) ^ b`), or the bare
  -- text would read back as `-(a ^ b)`. C#: `PushBinaryLeftOperand`.
  | .binary op left right =>
      let leftName := exprDiagnosticName left
      let baseName :=
        match op with
        | .pow => if powerBaseNeedsParens left then "(" ++ leftName ++ ")" else leftName
        | _ => leftName
      baseName ++ " " ++ op.symbol ++ " " ++ exprDiagnosticName right
  -- Source-faithful postfix indexing `target:selector`; operands that would
  -- rebind under the real precedence are parenthesized. This renderer prints
  -- binary bare, so a binary index operand is parenthesized here; C# reaches
  -- the same text via `OpenExprName`, which self-parenthesizes binary. The two
  -- agree on a simple operand (`(A + B):0`) but not on a NESTED one, where C#
  -- also parenthesizes the inner binary (`((A + B) + C):0` vs `(A + B + C):0`).
  -- That difference is inherited from each renderer's own binary convention,
  -- is independent of indexing, and is unambiguous either way.
  | .index target selector =>
      let targetName := exprDiagnosticName target
      let selectorName := exprDiagnosticName selector
      (if indexTargetNeedsParens target then "(" ++ targetName ++ ")" else targetName)
        ++ ":" ++
        (if indexSelectorNeedsParens selector then "(" ++ selectorName ++ ")" else selectorName)
  -- Internal SequenceConstruct renders as one sequence value; ';' is not surface syntax.
  | .sequenceConstruct left right => "(" ++ exprDiagnosticName left ++ ", " ++ exprDiagnosticName right ++ ")"
  -- Empty sequence value `()` and its nested forms.
  | .emptySequence depth => emptySequenceText depth
  -- Postfix spread binds to the completed operand. Unary and binary operands
  -- need parentheses so the diagnostic text reads back with the same AST.
  | .sequenceSpread operand =>
      let operandName := exprDiagnosticName operand
      (match operand with
       | .unary _ _ | .binary _ _ _ => "(" ++ operandName ++ ")"
       | _ => operandName) ++ "*"
  -- Exact list literal `[a, b, c]`.
  | .listLiteral items => "[" ++ String.intercalate ", " (items.map exprDiagnosticName) ++ "]"
  | .resolve name => name
  | .algorithmExpr algorithm => "(" ++ String.intercalate ", " ((Algorithm.output algorithm).map exprDiagnosticName) ++ ")"
  | .capture rows => "(" ++ String.intercalate ", " (rows.map exprDiagnosticName) ++ ")"
  | .call fn _ => exprDiagnosticName fn ++ "(...)"
  | .dotMember target name _ none =>
      exprDiagnosticName target ++ "." ++ name
  | .dotMember target name _ (some _) =>
      exprDiagnosticName target ++ "." ++ name ++ "(...)"

/-- The binary operand-shape name `left op right` — delegates to the `.binary`
  arm of `exprDiagnosticName` so the two can never disagree (in particular on
  power-base parenthesization). C#: `ExprNameRenderer.RenderBinaryDiagnosticName`. -/
def binaryExprDiagnosticName (op : BinaryOp) (left right : Expr) : String :=
  exprDiagnosticName (.binary op left right)

namespace CtxMsg
  def openMsg (k : String)              := s!"while resolving open: {k}"
  def call   (f : Expr)               := s!"while evaluating call to {openExprName f}"
  def property (n : Ident)            := s!"while evaluating property {n}"
  def dotCall (obj : Expr) (n : Ident) := s!"while evaluating dotCall .{n} of {openExprName obj}"
end CtxMsg

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

structure OpenPropertyHit where
  provider : String
  property : ResolvedProperty
  deriving Repr

--------------------------------------------------------------------------------
-- Pattern matching (for conditional algorithms)
--------------------------------------------------------------------------------

/-- Recover the member list a sequence-value pattern should match against.
    `Result.normalize` collapses `sequenceValue [x]` -> `x` at every algorithm boundary,
    so singleton sequence values never exist at runtime. A singleton sequence-value
    pattern such as `(b)` therefore must also match a non-sequence-value result by
    treating it as `sequenceValue [result]`.

    This rule is shared by `matchPattern` and `matchCountedPattern` so direct
    conditional calls and counted callback calls (map/filter/reduce) accept
    exactly the same input shapes. -/
def patternSequenceValueMembers? (patternCount : Nat) (r : Result) : Option (List Result) :=
  match r with
  | .sequenceValue rs => if rs.length == patternCount then some rs else none
  | _ => if patternCount == 1 then some [r] else none

/-- Match a pattern against a Result, returning accumulated bindings on success.
    - `bind x` matches any Result, binding x → r
    - `litInt n` matches only `Result.atom n`
    - `sequenceValue ps` matches `Result.sequenceValue rs` with same length, recursively;
      a singleton sequence-value pattern also matches a non-sequence-value result because
      normalization collapses singleton sequence values (`patternSequenceValueMembers?`)

    Bindings accumulate left-to-right. Repeated names compare against the
    first bound value and do not add another environment entry. -/
partial def matchPatternInto (p : Pattern) (r : Result) (env : ValEnv)
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
  | .sequenceValue ps  =>
      match patternSequenceValueMembers? ps.length r with
      | none => none
      | some rs =>
          let rec go : List Pattern -> List Result -> ValEnv -> Option ValEnv
            | [], [], current => some current
            | p::ps', r::rs', current => do
                let next <- matchPatternInto p r current
                go ps' rs' next
            | _, _, _ => none
          go ps rs env

def matchPattern (p : Pattern) (r : Result) : Option ValEnv :=
  matchPatternInto p r []

/-- Match a top-level conditional call head against the explicit argument list
    supplied at the call site.

    Ordinary direct conditional calls preserve explicit argument slots at the
    top level: a non-sequence-value head expects exactly one explicit argument, while a
    sequence-value head expects one explicit argument per sequence element. Nested sequence-value
    structure is still matched through `matchPattern`. -/
def matchCallPattern (p : Pattern) (args : List Result) : Option ValEnv :=
  match p with
  | .sequenceValue ps =>
      if ps.length != args.length then
        none
      else
        let rec go : List Pattern -> List Result -> ValEnv -> Option ValEnv
          | [], [], env => some env
          | p::ps', arg::args', env => do
              let next <- matchPatternInto p arg env
              go ps' args' next
          | _, _, _ => none
        go ps args []
  | _ =>
      match args with
      | [arg] => matchPattern p arg
      | _ => none

/-- Try to match branches in order against the explicit argument list of an
    ordinary direct conditional call. -/
def matchCallBranches (bs : List CondBranch) (args : List Result) : Option (CondBranch × ValEnv) :=
  match bs with
  | []     => none
  | b::bs' =>
      match matchCallPattern b.pattern args with
      | some env => some (b, env)
      | none     => matchCallBranches bs' args

partial def matchCountedPatternInto (p : Pattern) (arg : CountedResult)
    (env : CountedParamEnv) : Option CountedParamEnv :=
  match p with
  | .bind x =>
      match env.lookup x with
      | some existing => if existing.fst == arg.fst then some env else none
      | none => some (env ++ [(x, arg)])
  | .litInt n =>
      match arg.fst with
      | .atom v => if v = n then some env else none
      | _ => none
  | .litString s =>
      match arg.fst with
      | .str v => if v = s then some env else none
      | _ => none
  | .sequenceValue ps =>
      match patternSequenceValueMembers? ps.length arg.fst with
      | none => none
      | some rs =>
          let rec go : List Pattern -> List Result ->
              CountedParamEnv -> Option CountedParamEnv
            | [], [], current => some current
            | p'::ps', r::rs', current => do
                let next <- matchCountedPatternInto p' (r, Result.valueCount r) current
                go ps' rs' next
            | _, _, _ => none
          go ps rs env

def matchCountedPattern (p : Pattern) (arg : CountedResult) : Option CountedParamEnv :=
  matchCountedPatternInto p arg []

def matchCountedCallPattern (p : Pattern) (args : List CountedResult) : Option CountedParamEnv :=
  match p with
  | .sequenceValue ps =>
      if ps.length != args.length then
        none
      else
        let rec go : List Pattern -> List CountedResult ->
            CountedParamEnv -> Option CountedParamEnv
          | [], [], env => some env
          | p'::ps', arg::args', env => do
              let next <- matchCountedPatternInto p' arg env
              go ps' args' next
          | _, _, _ => none
        go ps args []
  | _ =>
      match args with
      | [arg] => matchCountedPattern p arg
      | _ => none

def matchCountedCallBranches (bs : List CondBranch) (args : List CountedResult)
    : Option (CondBranch × CountedParamEnv) :=
  match bs with
  | [] => none
  | b::bs' =>
      match matchCountedCallPattern b.pattern args with
      | some env => some (b, env)
      | none => matchCountedCallBranches bs' args

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

/-- Builtin argument adapters reify each written slot as one value-producing
    adapter. A zero-declaration algorithm block slot keeps its one-slot value
    boundary here (written-slot reification: `repeat(step, n, {1, 2})`
    supplies ONE initial state slot), exactly as before the block's algorithm
    identity became visible to user-call higher-order binding. Blocks with
    parameters, properties, or opens still resolve as algorithms for
    algorithm-consuming builtin arguments (callbacks). -/
def zeroDeclarationBlockValueSlot : Expr -> Bool
  | .algorithmExpr alg =>
      (Algorithm.params alg).isEmpty
        && (Algorithm.opens alg).isEmpty
        && (Algorithm.props alg).isEmpty
  | _ => false

def isLiftableArgResolutionError : Error → Bool
  | .notAnAlgorithm _ => true
  | .illegalInEval _  => true
  | .withContext _ e   => isLiftableArgResolutionError e
  | _                  => false

def bindLoopStepValueEnv (parameters : List CallableParameter)
    (normalBindings : List (Prod Ident Result))
    (collectingName : Ident) (captured : Result) : EvalM ValEnv :=
  match parameters with
  | [] =>
      match normalBindings with
      | [] => pure []
      | _ => .error Error.badArity
  | parameter :: rest =>
      match parameter.kind with
      | .collecting => do
          let vals <- bindLoopStepValueEnv rest normalBindings collectingName captured
          pure ((collectingName, captured) :: vals)
      | .normal =>
          match normalBindings with
          | [] => .error Error.badArity
          | binding :: bindings' => do
              let vals <- bindLoopStepValueEnv rest bindings' collectingName captured
              pure ((binding.fst, binding.snd) :: vals)

def loopStateResult (stateSlots : List Result) : Result :=
  Result.normalize (.sequenceValue stateSlots)

/-- Split a loop step output into next state slots and continuation flag. -/
def splitContSlots (outputSlots : List Result) : EvalM (List Result × Int) := do
  match outputSlots with
  | [] => .error Error.badArity
  | [slot] =>
    match slot with
    | .atom n => pure ([slot], n)
    | _ => .error Error.badArity
  | _ =>
    match outputSlots.getLast? with
    | some last =>
      let c <- expectInt last
      pure (outputSlots.dropLast, c)
    | none => .error Error.badArity

/-- Higher-order callbacks keep the collected item value shape for pattern
    matching, while the counted callback-param view still uses the same
    one-level projection rule as `S:i` for callback param operations like
    `x.count`. -/
def countedSequenceCallbackItem (item : CountedResult) : CountedResult :=
  Result.projectSelectedContent item.fst

def isCacheableZeroArgPropertyAlgorithm (a : Algorithm) : Bool :=
  (Algorithm.params a).isEmpty

def zeroArgPropertyCacheKey (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (ctx : EvalCtx) (env : ValEnv)
    : ZeroArgPropertyCacheKey :=
  {
    accessKind := accessKind,
    owner := reprStr owner,
    propertyName := binding.name,
    propertyAlgorithm := reprStr binding.alg,
    valEnv := reprStr env,
    algEnv := reprStr ctx.algEnv,
    countedParamEnv := reprStr ctx.countedParamEnv
  }

def reducerAccumulatorSideHasTopLevelCollecting : Algorithm -> Bool
  | .mk _ patterns _ _ _ =>
      match patterns with
      | [] => false
      | _ :: accumulatorPatterns =>
          accumulatorPatterns.any (fun
            | .capture parameter => parameter.kind == .collecting
            | _ => false)
  | _ => false

def requireCallableValues (items : List CallableCallItem)
    : EvalM (List Result) := do
  match items with
  | [] => pure []
  | item :: rest =>
      let tail <- requireCallableValues rest
      match item.value? with
      | some value => pure (value :: tail)
      | none =>
          if item.skipMissingValue then
            pure tail
          else
            match item.error? with
            | some err => .error err
            | none => .error Error.badArity

def applySequenceBuiltinEmptyPolicy (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput) : EvalM CollectedSequenceBuiltinInput :=
  match metadata.emptyPolicy with
  | .allowEmpty =>
      pure collected
  | .requireAnyItem =>
      if collected.totalItemCount = 0 then
        .error (Error.withContext
          s!"{builtinDisplayName b} requires a non-empty collection"
          Error.badArity)
      else
        pure collected

/-- Collect top-level collection elements as single atomic numeric values.
    Used by numeric ordering and aggregation builtins, which reject strings
    and sequence values instead of inventing mixed-type or structural
    interpretation.

    Diagnostics identify the 0-based collection item index so numeric shape
    failures remain debuggable after counted top-level extraction. -/
def collectSingleAtomicNumbers (b : Builtin)
    : Nat -> List Result -> EvalM (List Int)
  | _, [] => pure []
  | index, item :: rest =>
      match Result.singleAtomicNumber? item with
      | some n => do
          let tail <- collectSingleAtomicNumbers b (index + 1) rest
          pure (n :: tail)
      | none =>
          .error (Error.withContext
            (numericSequenceItemErrorContext b index item)
            Error.badArity)

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

def prepareSequenceBuiltinSuffixArgItem
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor)
    (item : CallableCallItem) : EvalM PreparedSequenceBuiltinSuffixArg := do
  match descriptor.kind with
  | .algorithm =>
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
        match item.error? with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .wholeNumber =>
    match item.value? with
    | some value =>
      match Result.singleAtomicNumber? value with
      | some number => pure (.wholeNumber number)
      | none =>
          .error (Error.withContext
            (sequenceBuiltinSuffixArgErrorContext b descriptor)
            Error.badArity)
    | none =>
        match item.error? with
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

def expectPreparedSequenceBuiltinAlgorithmSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .algorithm fun descriptor arg =>
    match arg with
    | .algorithm algorithm => pure algorithm
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .algorithm}"

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

def reduceInitialAccumulatorRequiresValueError : Error :=
  Error.withContext "while preparing reduce initial accumulator" Error.badArity

def isLikelyUnevaluatedParameterError (algorithm : Algorithm) (err : Error) : Bool :=
  match Algorithm.params algorithm with
  | [] => false
  | paramNames => Error.referencesAnyName paramNames err

/-- Evaluate `order(collection)`.
    `order` eagerly evaluates the full top-level collection, sorts its numeric
    items ascending, preserves duplicates, and materializes the sorted items
    as one exact immutable list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsAsc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `orderDesc(collection)`.
    `orderDesc` eagerly evaluates the full top-level collection, sorts its
    numeric items descending, preserves duplicates, and materializes the
    sorted items as one exact immutable list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderDescCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsDesc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `count(collection)`.
    `count` processes top-level collection elements from left to right and
    increments once per element.

    Each atom, string, or sequence value counts as one top-level element.
    Sequence values are not flattened or recursively inspected, and empty
    collections return `0`. -/
def evalCountCounted (items : List Result) : EvalM CountedResult := do
  pure (Result.atom (Int.ofNat items.length), 1)

/-- Evaluate `contains(collection, item)`.
    `contains` checks whether any extracted top-level item equals the searched
    suffix item using ordinary KatLang value equality.

    Search is top-level only: sequence values compare as sequence values and are
    not recursively flattened or inspected. Empty collections return `0`. -/
def evalContainsCounted (items : List Result) (searched : Result) : EvalM CountedResult := do
  let found := items.any (fun item => item == searched)
  pure (Result.atom (if found then 1 else 0), 1)

/-- Evaluate `distinct(collection)`.
    `distinct` removes later duplicate top-level items while preserving the
    first occurrence of each item and the original left-to-right order.

    Equality follows ordinary KatLang value semantics on extracted top-level
    items: atoms compare by numeric value, strings by exact string value, and
    sequence/list values structurally by their elements. Sequence and list
    values stay intact and are not flattened. The kept items are materialized
    as one exact immutable list value: empty collections yield `[]`, and a
    single kept item forms `[item]` (so `distinct((), ())` yields `[()]`). -/
def evalDistinctCounted (items : List Result) : EvalM CountedResult := do
  let distinctItems := dedupList items
  pure (makeCollectionListResult distinctItems)

/-- Evaluate `first(collection)`.
    `first` evaluates the full top-level sequence and
    returns its first top-level element unchanged.

    Atoms, strings, and sequence values each count as one top-level element.
    Sequence values are preserved whole rather than flattened. The collection
    must be non-empty. -/
def evalFirstCounted (items : List Result) : EvalM CountedResult := do
  match items with
  | first :: _ => pure (first, 1)
  | [] => .error Error.badArity

/-- Evaluate `last(collection)`.
    `last` evaluates the full top-level sequence and
    returns its last top-level element unchanged.

    Atoms, strings, and sequence values each count as one top-level element.
    Sequence values are preserved whole rather than flattened. The collection
    must be non-empty. -/
def evalLastCounted (items : List Result) : EvalM CountedResult := do
  match items.getLast? with
  | some last => pure (last, 1)
  | none => .error Error.badArity

/-- Evaluate `take(collection, count)`.
    `take` returns the first `count` extracted top-level items unchanged,
    materialized as one exact immutable list value.
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
    exact immutable list value.
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
  | [] => .error Error.badArity
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
  | [] => .error Error.badArity
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
    keeps the exact fractional average.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalAvgCounted (numbers : List Int) : EvalM CountedResult := do
  match numbers with
  | [] => .error Error.badArity
  | values =>
      let total := values.foldl (fun acc n => acc + n) 0
      pure (Result.atom (total.tdiv (Int.ofNat values.length)), 1)

/-- Assemble the argument bundle for ordinary lexical dot-call fallback:
    `receiver.F(C, D)` calls `F` with the ORIGINAL receiver expression as one
    injected leading segment followed by the written extra arguments.
    Assembly is independent of the resolved callee: the receiver is never
    pre-expanded, never unwrapped, and no parameter shape is inspected. The
    paired `CallArgumentAssembly.injectedDotReceiverLeading` marker makes the
    receiver one segment for allocation whose evaluated top-level supply only
    a flat top-level collecting parameter consumes.
    C#: `BuildLexicalReceiverCallArgs`. -/
def prepareLexicalDotCallArgs (receiver : Expr) (extraArgs : Option OutputBundle)
    : OutputBundle :=
  [receiver] ++ extraArgs.getD []


--------------------------------------------------------------------------
-- Open resolution
--------------------------------------------------------------------------

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
  -- `open (M)` is not openable. Top-level capture targets are already
  -- rejected by resolveAllOpens' open-form validation; this arm is reached
  -- through dotted-path recursion (`open (X).B`) and prebuilt ASTs.
  | .capture _ => throw (Error.badOpenForm "captured value groups cannot be opened")
  | .resolve n =>
    match ctx.callStack with
    | a::_ =>
      match lookupLexicalDirect a n with
      | some r =>
          if r.isBuiltin then .error (Error.illegalInOpen s!"builtin '{n}'")
          else pure r
      | none => .error (Error.unknownName n)
    | [] => .error (Error.unknownName n)
  -- Only argumentless dot paths resolve as open targets. Grace-marked open
  -- targets are rejected by the C# front end before Lean encoding.
  | .dotMember o n _ none => do
    let a <- resolveAlgForOpen o ctx
    -- First check if property exists at all so ownership still wins over opens.
    match Algorithm.lookupPropDefAny? a n with
    | some p =>
        if p.alg.isBuiltin then
          .error (Error.illegalInOpen s!"builtin not allowed in open: {openExprName o}.{n}")
        else if !p.exposure.isExported then
          .error (Error.localOnlyProperty (openExprName o) n p.exposure)
        else
          -- Property exists; check if it's public
          match Algorithm.lookupPublicProp a n with
          | some publicAlg => pure (Algorithm.childOf a publicAlg)
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

/-- Resolve an open expression to a library algorithm. -/
def resolveOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  resolveAlgForOpen e ctx

/-- Resolve all opens of an algorithm upfront.
    Deduplicates named opens by `openExprName` (first occurrence wins) to
    avoid repeated resolution and spurious ambiguity.  Inline blocks are never
    deduplicated (each gets a unique positional key).
    Validates all open expressions first for fail-fast diagnostics. -/
def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
  let rawOpens := Algorithm.opens a
  -- Deduplicate by key (first occurrence wins); inline blocks use positional keys
  let tagged := rawOpens.mapIdx (fun idx e =>
    let key := match e with
      | .algorithmExpr _ => s!"(inline#{idx})"   -- * unique per original position, never deduped
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
  -- Then resolve (each open wrapped with context using its dedup key)
  acc.mapM (fun (key, e) => do
    let lib <- withCtx (CtxMsg.openMsg key) (resolveOpen e ctx)
    pure { key := key, expr := e, lib := lib })

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
  let ctx' := EvalCtx.push a ctx
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
            alg := Algorithm.childOf ri.lib prop.alg
          }
        } :: hits
    | none => pure ()
  hits := hits.reverse

  match hits with
  | [] => pure none
  | [h] => pure (some h.property)
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
      let owner := Algorithm.forOpens sc
      some {
        owner := owner,
        binding := prop,
        alg := Algorithm.withParent (some sc) prop.alg
      }
  | none =>
      match sc with
      | .mk (some sc') _ _ => lookupInParentsStructuralProperty sc' name
      | .mk none _ _       => none

/-- Open-based lookup in parent chain (helper for lookupOpenPropertiesInChain). -/
def lookupOpenPropertiesInParentChain (sc : ScopeCtx) (name : Ident)
    (ctx : EvalCtx) : EvalM (Option ResolvedProperty) := do
  let tempAlg := Algorithm.forOpens sc
  match (<- lookupOpenProperties tempAlg name ctx) with
  | some r => pure (some r)
  | none =>
      match sc with
      | .mk (some sc') _ _ => lookupOpenPropertiesInParentChain sc' name ctx
      | .mk none _ _       => pure none

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
    ownership-first / dedup / ambiguity rules exist exactly once. -/
def lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM ResolvedProperty := do
  match Algorithm.lookupPropDefAny? a name with
  | some prop =>
      pure {
        owner := a,
        binding := prop,
        alg := Algorithm.childOf a prop.alg
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

/-- Algorithm-position lexical lookup (call callees, dot-call targets).
    This is the algorithm PROJECTION of `lookupLexicalProperty`: the canonical
    property-carrying chain owns ownership-first ordering, open dedup,
    ambiguity, and precedence, and this projection only discards the
    owner/binding metadata that algorithm-position consumers never read. -/
def lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm := do
  let resolved <- lookupLexicalProperty a name ctx
  pure resolved.alg

def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .sequenceConstruct _ _ =>
    .error (Error.notAnAlgorithm "sequence construct expression")
  | .sequenceSpread _ =>
    .error (Error.notAnAlgorithm "spread expression")
  | .algorithmExpr a => pure (wireToCaller ctx a)
  -- Capture is not algorithm identity: the algorithm channel sees only a
  -- zero-parameter value thunk over the bundle, exactly as the pre-split
  -- transparent wrapper behaved. `(F)(1)` therefore stays an arity error and
  -- `Apply((Increment))` never receives Increment's callable identity.
  -- C#: `CaptureValueThunk`.
  | .capture rows => pure (wireToCaller ctx (Algorithm.mk none [] [] [] rows))
  | .resolve n =>
      match ctx.callStack with
      | a::_ => lookupLexical a n ctx
      | []   => .error (Error.unknownName n)
  | .dotMember o n fallback args =>
      -- Lift a.f / a.f(args) to a wrapper algorithm; evalDotCall handles all
      -- semantics (builtin property special cases, structural property,
      -- receiver injection, lexical fallback). The whole node — including its
      -- elaborated fallback identity — rides along unchanged.
      pure (wireToCaller ctx (Algorithm.ofExpr (.dotMember o n fallback args)))
  -- Explicit errors for syntactic forms that cannot resolve to algorithms
  | .param x =>
      -- Higher-order parameter: if x is bound in AlgEnv, return the algorithm
      match ctx.algEnv.lookup x with
      | some alg => pure alg
      | none     => .error (Error.notAnAlgorithm s!"param({x})")
  | .num n   => .error (Error.notAnAlgorithm s!"num({n})")
  | .emptySequence _ => .error (Error.notAnAlgorithm "empty sequence value")
  | .listLiteral _ => .error (Error.notAnAlgorithm "list literal")
  | .unary _ _ => .error (Error.notAnAlgorithm "unary expression")
  | .binary _ _ _ => .error (Error.notAnAlgorithm "binary expression")
  | .index _ _ => .error (Error.notAnAlgorithm "index expression")
  | .call _ _ => .error (Error.notAnAlgorithm "call expression")
  | .stringLiteral _ => .error (Error.notAnAlgorithm "string literal")


def resolveArgAlgExpr (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Algorithm := do
  let shouldUseValueSide :=
    match e with
    | .param name => (ctx.countedParamEnv.lookup name).isSome || (env.lookup name).isSome
    | _ => false
  if shouldWrapArgExprAsValue e || zeroDeclarationBlockValueSlot e || shouldUseValueSide then
    pure (wireToCaller ctx (Algorithm.ofExpr e))
  else
    match <- evalAttempt (resolveAlg e ctx) with
    | .ok a    => pure a
    | .error err =>
      if isLiftableArgResolutionError err then
        pure (wireToCaller ctx (Algorithm.ofExpr e))
      else
        .error err

/-- Resolve argument expressions to algorithms for builtin dispatch, tagging
    each argument with whether it is a spread expression.
    Unlike a strict `mapM resolveAlg`, this wraps *liftable* non-resolvable
    expressions (`notAnAlgorithm`, `illegalInEval`) in trivial
    `Algorithm.ofExpr` wrappers wired to the caller scope (see
    `resolveArgAlgExpr`).  This enables ergonomic builtin syntax such as
    `If(X >= 5, 1, 0)` without requiring explicit `{…}` blocks around every
    argument.

    Wrapping is safe because builtins evaluate their algorithm arguments
    lazily via `evalAlgOutput`, so the expression is evaluated on demand
    within the correct scope rather than resolved structurally upfront.

    Errors that indicate genuine lookup or semantic failures (`unknownName`,
    `unknownProperty`, `ambiguousOpen`, etc.) are propagated immediately so
    diagnostics remain precise.

    Non-builtin call paths are unaffected — user-defined calls still evaluate
    arguments eagerly through the expression-position call path
    (`evalCallExpr` / `evalCallCountedExpr`). -/
def resolveArgAlgsWithSequenceSpread (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    : EvalM (List ResolvedArgumentAlgorithm) :=
  args.mapM (fun e => do
    let alg <- resolveArgAlgExpr e ctx env
    let spreadsSequence :=
      match e with
      | .sequenceSpread _ => true
      | _ => false
    pure { algorithm := alg, spreadsSequence := spreadsSequence })

/-- Try to resolve each argument expression to an algorithm.
    Returns `some alg` for expressions that resolve, `none` for those that don't
    (e.g., numeric literals, arithmetic). Every `algorithmExpr` contributes its
    contained algorithm regardless of declaration/output count. A `capture`
    contributes only its zero-parameter value thunk, never the algorithm
    identity of an expression it contains. Only liftable
    errors → none; genuine lookup failures propagate.
    Used by the shared call argument-slot assembly
    (`collectVariadicCallItems`, serving every callable shape) to build AlgEnv
    for higher-order algorithm parameters. -/
def tryResolveArgAlgs (args : OutputBundle) (ctx : EvalCtx) : EvalM (List (Option Algorithm)) :=
  args.mapM (fun e => do
    if shouldWrapArgExprAsValue e then
      pure none
    else
      match <- evalAttempt (resolveAlg e ctx) with
      | .ok a    => pure (some a)
      | .error err =>
        if isLiftableArgResolutionError err then
          pure none
        else
          .error err)

/-- `sizeOf` of a list prefix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_take_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.take n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.take]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.take]; omega
      | succ n =>
          simp only [List.take, List.cons.sizeOf_spec]
          have := ih n
          omega

/-- `sizeOf` of a list suffix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_drop_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.drop n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.drop]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.drop]
      | succ n =>
          simp only [List.drop, List.cons.sizeOf_spec]
          have := ih n
          omega

mutual
  def bindParameterPattern (pattern : ParameterPattern) (input : ParameterPatternInput)
      (allowAlgorithmBindings : Bool) : EvalM ParameterPatternBindings := do
    match pattern with
    | .capture parameter =>
        match parameter.kind with
        | .normal =>
            let argEnv := match input.value? with
              | some value => [(parameter.name, value)]
              | none => []
            let algEnv :=
              if allowAlgorithmBindings then
                match input.algorithm? with
                | some algorithm => [(parameter.name, algorithm)]
                | none => []
              else []
            if input.value?.isNone && (input.algorithm?.isNone || !allowAlgorithmBindings) then
              .error (input.error?.getD Error.badArity)
            else
              pure { argEnv := argEnv, countedParamEnv := [], algEnv := algEnv }
        | .collecting => .error Error.badArity
    | .sequenceValue items => do
        let sequenceValueItems? :=
          match input.explicitSequenceValueItems? with
          | some sequenceValueItems => some sequenceValueItems
          | none =>
            match input.value? with
            -- A received sequence value or exact list value opens to its
            -- immediate items (`Result.structureItems?`): the deconstruction
            -- receiver opens ONE lone structure boundary of either kind, so
            -- `x, y, z = [1, 2, 3]` binds like `x, y, z = [1, 2, 3]*`.
            -- A non-grouped scalar is a one-item supply for the
            -- prefix/collecting/suffix matcher (the same normalization the function
            -- deconstruction path applies).
            | some value => some ((Result.structureItems? value).getD [value])
            | none => none
        match sequenceValueItems? with
        | none => .error (input.error?.getD Error.badArity)
        | some sequenceValueItems =>
            let nestedInputs := sequenceValueItems.map (fun value => { value? := some value : ParameterPatternInput })
            bindParameterPatternList items nestedInputs false
  -- Termination: the pattern-side `sizeOf` shrinks around the recursion cycle;
  -- the +1 tag on the list function breaks the tie for same-list entry calls.
  termination_by 2 * sizeOf pattern
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def bindParameterPatternList (patterns : List ParameterPattern)
      (inputs : List ParameterPatternInput) (allowAlgorithmBindings : Bool)
      : EvalM ParameterPatternBindings := do
    let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
      | [], _ => none
      | (.capture parameter) :: rest, index =>
          match parameter.kind with
          | .collecting => some (index, parameter)
          | .normal => findCollecting rest (index + 1)
      | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
    let merge (left right : ParameterPatternBindings)
        : EvalM ParameterPatternBindings := do
      let argEnv <- mergeEqualValEnv left.argEnv right.argEnv
      let countedParamEnv <-
        mergeEqualCountedParamEnv left.countedParamEnv right.countedParamEnv
      let algEnv <- mergePatternAlgEnv left.argEnv right.argEnv left.algEnv right.algEnv
      pure {
        argEnv := argEnv,
        countedParamEnv := countedParamEnv,
        algEnv := algEnv
      }
    let rec bindPairs : List ParameterPattern -> List ParameterPatternInput -> EvalM ParameterPatternBindings
      | [], [] => pure {}
      | pattern :: patterns', input :: inputs' => do
          let current <- bindParameterPattern pattern input allowAlgorithmBindings
          let rest <- bindPairs patterns' inputs'
          merge current rest
      | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
      termination_by ps _ => 2 * sizeOf ps
      decreasing_by
        all_goals simp_wf
        all_goals omega
    match findCollecting patterns 0 with
    | none =>
        if patterns.length != inputs.length then
          .error (Error.arityMismatch patterns.length inputs.length)
        else
          bindPairs patterns inputs
    | some (collectingIndex, collectingParameter) =>
        let required := patterns.length - 1
        if inputs.length < required then
          .error (Error.arityMismatch required inputs.length)
        else
          let prefixPatterns := patterns.take collectingIndex
          let prefixInputs := inputs.take collectingIndex
          let suffixCount := patterns.length - collectingIndex - 1
          let suffixPatterns := patterns.drop (collectingIndex + 1)
          let suffixInputs := inputs.drop (inputs.length - suffixCount)
          let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
          let prefixBindings <- bindPairs prefixPatterns prefixInputs
          let suffixBindings <- bindPairs suffixPatterns suffixInputs
          let rec collectValues : List ParameterPatternInput -> EvalM (List Result)
            | [] => pure []
            | input :: rest =>
                match input.value? with
                | some value => do
                    let values <- collectValues rest
                    -- A segment allocated to the flat top-level collecting
                    -- position consumes its evaluated top-level supply (one
                    -- level, never recursive): an injected dot-call receiver
                    -- segment contributes its emitted items, while every
                    -- ordinary segment contributes its one reified value.
                    -- Fixed prefix/suffix and nested pattern positions ignore
                    -- the supply view (they bind the value view).
                    match input.collectingSegmentCount? with
                    | some segmentCount =>
                        pure (countedTopLevelValues (value, segmentCount) ++ values)
                    | none => pure (value :: values)
                | none =>
                    -- A collecting binding collects VALUES. A FUNCTION-shaped
                    -- argument (builtin, clause family, or parameterized
                    -- algorithm) has no value to collect — only fixed
                    -- parameters keep the dual algorithm channel — so name
                    -- the actual conflict instead of surfacing the argument's
                    -- incidental value-evaluation error. A zero-parameter
                    -- VALUE property whose body failed is NOT a function: its
                    -- genuine evaluation error surfaces.
                    -- C#: `BindParameterPatternList` (whose message also
                    -- names the collecting parameter).
                    match input.algorithm? with
                    | some alg =>
                        if alg.isFunctionShaped then
                          .error (Error.typeMismatch
                            "A collecting parameter collects values, but a supplied argument is a function. Pass a value, or call the function so its result is collected.")
                        else
                          .error (input.error?.getD Error.badArity)
                    | none => .error (input.error?.getD Error.badArity)
          let capturedValues <- collectValues capturedInputs
          -- Collecting binding COLLECTS: the assigned supply becomes one exact
          -- immutable list value, emitted count 1 (a list is one visible value).
          let captured := collectSegment capturedValues
          let collectingBindings : ParameterPatternBindings :=
            { argEnv := [(collectingParameter.name, captured)],
              countedParamEnv := [(collectingParameter.name, (captured, 1))],
              algEnv := [] }
          let withCollecting <- merge prefixBindings collectingBindings
          merge withCollecting suffixBindings
  termination_by 2 * sizeOf patterns + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have take_le := list_take_sizeOf_le collectingIndex patterns
         omega)
      | (have drop_le := list_drop_sizeOf_le (collectingIndex + 1) patterns
         omega)
end

def bindStructuredLoopState (step : Algorithm) (stateValues : List Result)
    : EvalM (ValEnv × CountedParamEnv) := do
  let inputs := stateValues.map (fun value => { value? := some value : ParameterPatternInput })
  let bindings <- bindParameterPatternList (Algorithm.parameterPatterns step) inputs false
  pure (bindings.argEnv, bindings.countedParamEnv)

def bindLoopStepState (step : Algorithm) (stateValues : List Result)
    : EvalM (ValEnv × CountedParamEnv) := do
  if Algorithm.requiresPatternBinding step then
    bindStructuredLoopState step stateValues
  else
    match Algorithm.collectingParam? step with
    | none => do
        let argEnv <- bindParams (Algorithm.params step) stateValues
        pure (argEnv, [])
    | some _ => do
        let signature := Algorithm.callableSignature "loop step" step
        let bindings <-
          match bindCallableArguments signature stateValues (fun required actual => Error.arityMismatch required actual) with
          | .ok value => pure value
          | .error err => .error err
        match bindings.collectingName? with
        | none => .error Error.badArity
        | some collectingName =>
            -- Collecting binding COLLECTS (same rule as the pattern binders): the
            -- assigned state slots become one exact immutable list value.
            let captured := collectSegment bindings.collectingItems
            let argEnv <- bindLoopStepValueEnv signature.parameters bindings.normalBindings collectingName captured
            let collectingBinding := (collectingName, (captured, 1))
            pure (argEnv, [collectingBinding])

/-
Evaluator recursion core.

Everything above this point is helper logic that never re-enters evaluation:
validation, name/open/lexical resolution, parameter-pattern binding,
argument-shape preparation, cache-key construction, and pure builtin
computations — checked as ordinary total definitions wherever Lean can see
termination.

This mutual block intentionally contains only functions that participate in
runtime evaluation recursion, plus thin wrappers used by those functions.
Its members are `partial` because KatLang programs may be recursively
defined, so evaluation is not structurally recursive over syntax alone; a
total version would require an explicit fuel/step-indexed evaluator.

Do not add non-evaluating helpers here — define them above this block so
Lean checks them as total definitions.

PLAIN/COUNTED OWNERSHIP: for every plain/counted evaluator pair the COUNTED
implementation is canonical and the plain implementation is its value
projection (`.fst` of the counted result) — `eval` projects `evalCounted`,
`evalUserCall`/`evalConditionalCall`/`evalResolvedCall`/`evalCallExpr`/
`evalDotCall`/`applyBuiltin`/`applyBuiltinResolved`/`evalAlgOutputCore`/
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
mutual

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
      (Loop-step state, which must keep a collecting `*history` structured, goes
      through `evalAlgOutputSlots` with its explicit preserve flag, not here.)

      A user-defined algorithm value may exist structurally without output, but
      forcing it in value position raises `missingOutput`. A root program is
      also forced in value position when a result is requested; explicit empty
      output is written as `()`, the empty sequence value.

      Forcing a conditional algorithm in value position fails through
      `conditionalValueAccessError?`: branch selection requires call arguments,
      so a conditional must never silently force its empty output list.
      C#: `EvalAlgOutputCore`. -/
  partial def evalAlgOutputCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalAlgOutputCountedCore a ctx env
    pure out.fst

  /-- Force a user-defined algorithm value to produce output. -/
  partial def evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    evalAlgOutputCore a ctx env

  /-- Evaluate a root program algorithm when a result is requested. -/
  partial def evalProgramOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    evalAlgOutputCore a ctx env

  partial def evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      (preserveSequenceSpreadExpressionBoundaries : Bool := false)
      : EvalM (List Result) := do
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
        | .mk _ _ _ _ [] => .error Error.missingOutput
        | _ => pure ()
        let pushedCtx := EvalCtx.push a ctx
        let rec collect : List Expr -> List Result -> EvalM (List Result)
          | [], acc => pure acc.reverse
          | e :: rest, acc => do
              let out <- evalCounted e pushedCtx env
              let values :=
                if preserveSequenceSpreadExpressionBoundaries then
                  match e with
                  | .sequenceSpread _ => if out.snd = 0 then [] else [out.fst]
                  | _ =>
                      if out.snd = 0 then [out.fst] else countedTopLevelValues out
                else
                  match e with
                  | .sequenceSpread _ => countedTopLevelValues out
                  | _ =>
                      if out.snd = 0 then [out.fst] else countedTopLevelValues out
              collect rest (values.reverse ++ acc)
        collect (Algorithm.output a) []

  partial def runStepSlots (step : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      (stateSlots : List Result) : EvalM (List Result) := do
    let (argEnv, countedParamEnv) <- bindLoopStepState step stateSlots
    let shadowedCountedParamEnv := CountedParamEnv.shadow ctx.countedParamEnv (Algorithm.params step)
    let stepCtx := ctx.withCountedParamEnv (countedParamEnv ++ shadowedCountedParamEnv)
    evalAlgOutputSlots step stepCtx (argEnv ++ env) (Algorithm.requiresPatternBinding step)

  /-- Run a step algorithm with the given state bound to its params. -/
  partial def runStep (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : Result) : EvalM Result := do
    let outputSlots <- runStepSlots step ctx env (unpackArgs s)
    pure (loopStateResult outputSlots)

  /-- Initial loop state preserves explicit argument boundaries: `repeat(Step, 3, a, b)`
      starts with two slots, while `repeat(Step, 3, Pair)` starts with one slot even when
      `Pair` evaluates to multiple values. Step outputs define later state slots; capture a
      step result to keep one structured slot across iterations. -/
  partial def evalInitialLoopStateSlots (inits : List Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
    inits.mapM (fun init => evalAlgOutput init ctx env)

  /-- Evaluate a higher-order sequence callback on one collected iteration
      item. -/
  partial def evalSequenceCallbackCall (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result :=
    evalResolvedCallbackCall callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Counted variant of `evalSequenceCallbackCall` used by `map`. -/
  partial def evalSequenceCallbackCallCounted (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult :=
    evalResolvedCallbackCallCounted callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Evaluate an algorithm's output expressions once, retaining both the combined counted
      value and the explicit evaluated output-slot view. The slot list is the accumulator
      from the same left-to-right pass that constructs the combined value; it never reopens
      or decomposes that value after singleton erasure and never evaluates an expression twice.

      A parenthesized sequence-value expression such as `(a, b)` counts as one emitted value,
      while multiple top-level output expressions `a, b` count as two. `reduce`
      uses this to distinguish sequence-value accumulator values from multi-output
      step results. -/
  partial def evalAlgOutputPreparedCore
      (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput := do
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
        | .mk _ _ _ _ [] => .error Error.missingOutput
        | _ => pure ()
        evalOutputRowsPreparedCore (Algorithm.output a) (EvalCtx.push a ctx) env

  /-- The ONE shared output-row supply loop: evaluates ordered `OutputBundle`
      rows left to right (a spread row contributes its supplied items, a
      non-spread row contributes exactly one slot) and combines the collected
      slots into one canonical value (`combineOutputSlots`). Algorithm output
      evaluation reaches it after pushing the algorithm's own scope;
      `Expr.capture` evaluation reaches it directly with the surrounding
      context, because a capture owns no scope. Both receivers therefore share
      exactly the same supply semantics rather than duplicating them.
      C#: `EvalOutputRowsPreparedCore`. -/
  partial def evalOutputRowsPreparedCore
      (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput := do
    let rec collect : List Expr -> List Result -> Nat -> EvalM PreparedAlgorithmOutput
      | [], acc, emitted =>
          let outputSlots := acc.reverse
          pure {
            counted := (combineOutputSlots outputSlots, emitted),
            outputSlots := outputSlots
          }
      | expr :: rest, acc, emitted => do
          let out <- evalCounted expr rowCtx env
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
  partial def evalCapturePreparedCore
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput :=
    evalOutputRowsPreparedCore rows ctx env

  partial def evalCaptureCountedCore
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let out <- evalCapturePreparedCore rows ctx env
    pure out.counted

  /-- Evaluates a capture body to its single canonical captured value. -/
  partial def evalCaptureValue
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- evalCaptureCountedCore rows ctx env
    pure out.fst

  /-- Counted projection of the shared prepared algorithm-output evaluation. -/
  partial def evalAlgOutputCountedCore
      (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let out <- evalAlgOutputPreparedCore a ctx env
    pure out.counted

  /-- Counted forcing variant of `evalAlgOutput`. -/
  partial def evalAlgOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    evalAlgOutputCountedCore a ctx env

  /-- Property-style zero-parameter access may reuse the per-run cache.
      Explicit calls do not use this helper, so `A()` bypasses only `A`'s
      direct cache entry and does not change nested property references. -/
  partial def evalZeroArgPropertyAccessCounted
      (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm)
      (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
      (env : ValEnv) : EvalM CountedResult := do
    if isCacheableZeroArgPropertyAlgorithm resolvedAlgorithm then
      let key := zeroArgPropertyCacheKey accessKind owner binding ctx env
      let state <- get
      match ZeroArgPropertyCache.lookup state.zeroArgPropertyCache key with
      | some cached => pure cached
      | none =>
          let counted <- evalAlgOutputCounted resolvedAlgorithm ctx env
          let nextState <- get
          set { nextState with
            zeroArgPropertyCache :=
              ZeroArgPropertyCache.insert nextState.zeroArgPropertyCache key counted }
          pure counted
    else
      evalAlgOutputCounted resolvedAlgorithm ctx env

  partial def evalZeroArgPropertyAccess
      (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm)
      (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
      (env : ValEnv) : EvalM Result := do
    let counted <- evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env
    pure counted.fst

  partial def evalConditionalCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    if callee.hasDuplicateBranchPatterns then
      .error Error.duplicateBranchPattern
    else
      match matchCountedCallBranches (Algorithm.branches callee) args with
      | some (branch, bindings) =>
          let wiredBody := Algorithm.childOf callee branch.body
          let names := bindings.map Prod.fst
          let newCtx := (EvalCtx.push callee ctx).withCountedParamEnv
            (bindings ++ CountedParamEnv.shadow ctx.countedParamEnv names)
          let newEnv := (bindings.map fun | (name, value) => (name, value.fst)) ++ env
          evalAlgOutputCounted wiredBody newCtx newEnv
      | none =>
          .error (Error.noMatchingBranch calleeName)

  /-- Evaluate a resolved algorithm against pre-evaluated callback arguments
      that preserve their emitted top-level counts.

      This is the shared callback-binding path for higher-order sequence
      builtins. It mirrors ordinary call semantics for final-argument
      unpacking while making the projected callback item behave like `S:i`
      inside the callback body. -/
  partial def evalResolvedCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    match callee with
    | .builtin b =>
        applyBuiltinCounted b (args.map countedArgAlgorithm) ctx env
    | .conditional _ _ _ =>
        match flatBinderUserEquivalent? callee with
        | some simple => do
            if (Algorithm.output simple).isEmpty then
              .error Error.missingOutput
            else do
              let countedParamEnv <- bindCountedCallbackParams (Algorithm.params simple) args
              let names := Algorithm.params simple
              let newCtx := ctx.withCountedParamEnv
                (countedParamEnv ++ CountedParamEnv.shadow ctx.countedParamEnv names)
              evalAlgOutputCounted simple newCtx env
        | none =>
            evalConditionalCallbackCallCounted callee args ctx env calleeName
    | _ =>
        if (Algorithm.output callee).isEmpty then
          .error Error.missingOutput
        else do
          if Algorithm.requiresPatternBinding callee then do
            let bindings <- bindCountedParameterPatternList (Algorithm.parameterPatterns callee) args
            let names := bindings.countedParamEnv.map Prod.fst
            let newCtx := ctx.withCountedParamEnv
              (bindings.countedParamEnv ++ CountedParamEnv.shadow ctx.countedParamEnv names)
            evalAlgOutputCounted callee newCtx env
          -- A flat callee with a top-level collecting parameter (`Rows.map(F)` with
          -- `F(x, *y, z)` or a single-collecting `Collect(*items)`) binds through
          -- the shared prefix/collecting/suffix binder so the collecting parameter
          -- COLLECTS an exact immutable list, after the same final-argument
          -- row expansion the fixed-only flat path uses below. Single-variadic
          -- callees keep the whole iterated element as one collected slot.
          else if ParameterPattern.hasCollectingCaptureAtCurrentLevel
              (Algorithm.parameterPatterns callee) then do
            let bindings <- bindCountedCallbackParameterPatternList
              (Algorithm.parameterPatterns callee) args
            let names := bindings.countedParamEnv.map Prod.fst
            let newCtx := ctx.withCountedParamEnv
              (bindings.countedParamEnv ++ CountedParamEnv.shadow ctx.countedParamEnv names)
            evalAlgOutputCounted callee newCtx env
          else do
            -- Fixed-only flat callback binding projects each callback item into
            -- slots and binds those slots to the algorithm's flat parameter
            -- names (the final item is unpacked across any remaining names);
            -- it does not apply item-supply singleton-boundary normalization.
            -- Scalar callback deconstruction stays deferred so the counted
            -- callback path keeps Lean/C# parity.
            let countedParamEnv <- bindCountedCallbackParams (Algorithm.params callee) args
            let names := Algorithm.params callee
            let newCtx := ctx.withCountedParamEnv
              (countedParamEnv ++ CountedParamEnv.shadow ctx.countedParamEnv names)
            evalAlgOutputCounted callee newCtx env

  /-- Non-counted wrapper for callback calls that still preserve projected item
      emitted counts internally where later operations depend on them. -/
  partial def evalResolvedCallbackCall (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    let out <- evalResolvedCallbackCallCounted callee args ctx env calleeName
    pure out.fst

  partial def evalReducerAccumulatorVariadicCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    match callee with
    | .mk _ patterns _ _ output =>
        if output.isEmpty then
          .error Error.missingOutput
        else do
          let bindings <- bindCountedParameterPatternList patterns args
          let names := bindings.countedParamEnv.map Prod.fst
          let newCtx := ctx.withCountedParamEnv
            (bindings.countedParamEnv ++ CountedParamEnv.shadow ctx.countedParamEnv names)
          evalAlgOutputCounted callee newCtx env
    | _ =>
        evalResolvedCallbackCallCounted callee args ctx env calleeName

  /-- Evaluate a `reduce` step on one collected iteration item. Reducers with
      a top-level variadic accumulator parameter bind accumulator state slots
      like loop state; other reducers keep ordinary structural accumulator
      binding. -/
  partial def evalSequenceReduceStepCounted (callee : Algorithm)
      (element : CountedResult) (accumulator : Result)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    let elementArg := countedSequenceCallbackItem element
    if reducerAccumulatorSideHasTopLevelCollecting callee then
      let accumulatorArgs :=
        (Result.toItems accumulator).map (fun value => (value, Result.valueCount value))
      evalReducerAccumulatorVariadicCallbackCallCounted callee
        (elementArg :: accumulatorArgs)
        ctx env calleeName
    else
      evalResolvedCallbackCallCounted callee
        [ elementArg
        , (accumulator, Result.valueCount accumulator)
        ]
        ctx env calleeName

    partial def collectSequenceCallableCallItems
      (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List CallableCallItem) := do
    let rec loop : List ResolvedArgumentAlgorithm -> EvalM (List CallableCallItem)
      | [] => pure []
      | arg :: rest => do
          let alg := arg.algorithm
          let tail <- loop rest
          -- A callback/function argument (one that declares parameters) is applied
          -- per element by the consuming sequence builtin, never used as a value here.
          -- Its parameters are unbound at this collection point, so evaluating its body
          -- standalone would resolve those parameter names against the surrounding scope;
          -- when a sibling argument shares a parameter name and was deferred as a
          -- self-referential thunk, that stray lookup re-enters the same builtin call and
          -- never settles. Keep the algorithm unevaluated so it is applied with bound
          -- parameters later; only value-shaped arguments are materialized eagerly.
          if !(Algorithm.params alg).isEmpty || !(Algorithm.parameterPatterns alg).isEmpty then
            pure ({ value? := none, algorithm? := some alg, error? := none, skipMissingValue := false } :: tail)
          else
          match <- evalAttempt (evalAlgOutputCounted alg ctx env) with
          | .ok counted =>
              if arg.spreadsSequence then
                match countedTopLevelValues counted with
                | [] => pure tail
                | values =>
                    let head := values.map (fun value =>
                      { value? := some value, algorithm? := some alg, error? := none, skipMissingValue := false })
                    pure (head ++ tail)
              else
                pure ({ value? := some counted.fst, algorithm? := some alg, error? := none, skipMissingValue := false } :: tail)
          | .error err =>
              pure ({ value? := none, algorithm? := some alg, error? := some err, skipMissingValue := false } :: tail)
    loop args


    partial def bindSequenceBuiltinArguments
      (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM BoundSequenceBuiltinArguments := do
    let items <- collectSequenceCallableCallItems args ctx env
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
        let collectionValue <-
          match collectionItem.value? with
          | some value => pure value
          | none =>
              match collectionItem.error? with
              | some err => .error err
              | none => .error Error.badArity
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
      from the post-binding collection view; nested sequence values stay
      intact. Normal accumulator parameters keep ordinary structural semantics,
      while top-level variadic accumulator parameters receive accumulator state
      slots. The step must
      return exactly one accumulator value: one atom, one string, one sequence
      value, or one exact list value is valid (the empty list `[]` counts as
      one value), while empty-sequence and multi-output results are rejected.

      The initial accumulator expression occupies one written accumulator
      slot (reified via `reCountValueBoundary` before reduction), so empty
      collections return the initial accumulator as ONE value. -/
  partial def evalReduceCounted (collection : List CountedResult)
      (stepAlg initialAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let initOut <-
      match <- evalAttempt (evalAlgOutputCounted initialAlg ctx env) with
      | .ok value => pure value
      | .error err =>
          if isLikelyUnevaluatedParameterError initialAlg err then
            .error reduceInitialAccumulatorRequiresValueError
          else
            .error err
    let rec reduceLoop : List CountedResult -> CountedResult -> EvalM CountedResult
      | [], acc => pure acc
      | item :: rest, (accValue, _) => do
          let stepOut <- withCtx
            "while evaluating reduce step (reduce passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list, nested sequence and list values stay intact, and top-level collecting accumulator parameters receive state slots)" <|
            evalSequenceReduceStepCounted stepAlg item accValue ctx env "reduce step"
          let next <- expectSingleAccumulator stepOut
          reduceLoop rest (next, 1)
    -- The initial accumulator expression occupies ONE written accumulator
    -- slot: its result is reified as one persistent value at the ordinary
    -- value boundary (`reCountValueBoundary`) BEFORE reduction begins, so an
    -- initial expression that emitted multiple items cannot leak that supply
    -- through the empty-collection return.
    reduceLoop collection (reCountValueBoundary initOut)

    /-- Evaluate `filter(collection, predicate)`.
      The fixed `collection` argument supplies the items through the
      post-binding collection view, and `predicate` is a fixed control
      argument. Each iterated item is passed to the predicate exactly as
      collected; nested sequence values and nested
      list values stay intact. The kept items remain the original collection
      items and are materialized as one exact immutable list value, so keeping
      exactly `(1, 2)` yields `[(1, 2)]`. -/
  partial def evalFilterCounted (items : List CountedResult) (predicateAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec filterLoop : Nat -> List CountedResult -> EvalM (List Result)
      | _, [] => pure []
      | index, item :: rest => do
        match <- evalAttempt (withCtx (s!"while evaluating filter predicate for item {index}: {resultDiagnosticString item.fst} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)") <|
          evalSequenceCallbackCall predicateAlg item ctx env "filter predicate") with
          | .error err =>
              .error err
          | .ok pr =>
              match Result.singleAtomicTruthValue? pr with
              | some true => do
                  let kept <- filterLoop (index + 1) rest
                  pure (item.fst :: kept)
              | some false =>
                  filterLoop (index + 1) rest
              | none =>
                  .error (Error.withContext
                    "filter predicate must return exactly one atomic numeric value"
                    Error.badArity)
    let kept <- filterLoop 0 items
    pure (makeCollectionListResult kept)

  /-- Evaluate `map(collection, mapper)`.
      `map` processes top-level collection elements from left to right.
      `transform(element)` receives each item exactly as collected from the
      post-binding collection view; nested sequence values stay intact.
      It must return exactly one mapped element:
      one atom, one sequence value, or one exact list value is valid, while
      empty and multi-output results are rejected.

      Sequence-value and list-value mapped elements are accepted as single
      output elements. Each captured callback result becomes one element of
      the exact immutable list result (mapped elements are never flattened
      into the outer list), empty collections yield `[]`, and the output
      preserves the original element order and element count. -/
  partial def evalMapCounted (collection : List CountedResult) (transformAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec mapLoop : List CountedResult -> EvalM (List Result)
      | [] => pure []
      | item :: rest => do
          let mappedOut <- withCtx
            "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            evalSequenceCallbackCallCounted transformAlg item ctx env "map transform"
          let mapped <- expectSingleMappedElement mappedOut
          let restMapped <- mapLoop rest
          pure (mapped :: restMapped)
    let mapped <- mapLoop collection
    pure (makeCollectionListResult mapped)

    partial def applyBuiltinCountedSequence
      (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    do
      let bound <- bindSequenceBuiltinArguments b metadata args ctx env
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
              let predicateAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalFilterCounted bound.iterationItems predicateAlg ctx env
        | .mapBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let transformAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalMapCounted bound.iterationItems transformAlg ctx env
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
              let stepAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              let initialAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 1
              evalReduceCounted bound.iterationItems stepAlg initialAlg ctx env
        | _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with counted output shape.
      Used by `reduce` to validate that the step emits exactly one accumulator
      value without flattening sequence values. -/
  partial def applyBuiltinCounted
      (b : Builtin) (args : List Algorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    match sequenceBuiltinMetadata? b with
    | some metadata =>
      applyBuiltinCountedSequence b metadata (args.map fun alg => { algorithm := alg }) ctx env
    | none =>
        match b, args with
        | .ifBuiltin, [c,t,e] => do
            let cr <- evalAlgOutput c ctx env
            -- The selected branch is one argument expression, so `if` observes it
            -- as a single value boundary -- exactly like value-position property
            -- access. A multi-output branch property such as `X = 1, 2, 3`
            -- therefore yields the grouped sequence value `(1, 2, 3)` with emitted
            -- count 1, not three separate outputs; explicit spread opens it.
            -- Unlike `while`/`repeat`, which preserve multi-slot loop state, `if`
            -- re-counts the chosen branch value via `Result.valueCount`.
            match Result.truthValue? cr with
            | some false => do
                let r <- evalAlgOutputCounted e ctx env
                pure (r.fst, Result.valueCount r.fst)
            | some true => do
                let r <- evalAlgOutputCounted t ctx env
                pure (r.fst, Result.valueCount r.fst)
            | none => .error Error.badArity

        | .whileBuiltin, step :: initAlgs => do
            if initAlgs.isEmpty then
              .error (builtinArityError b args.length)
            else
            let initialSlots <- evalInitialLoopStateSlots initAlgs ctx env
            let rec loop (stateSlots : List Result) : EvalM (List Result) := do
              let outputSlots <- runStepSlots step ctx env stateSlots
              let (nextSlots, cont) <- splitContSlots outputSlots
              if cont = 0 then pure stateSlots else loop nextSlots
            let finalSlots <- loop initialSlots
            let final := loopStateResult finalSlots
            pure (final, finalSlots.length)

        | .repeatBuiltin, step :: countAlg :: initAlgs => do
            if initAlgs.isEmpty then
              .error (builtinArityError b args.length)
            else
            let cr <- evalAlgOutput countAlg ctx env
            let n <- expectInt cr
            if n < 0 then
              .error (Error.illegalInEval "Repeat count must be >= 0")
            else
              let initialSlots <- evalInitialLoopStateSlots initAlgs ctx env
              let rec repeatLoop (k : Int) (stateSlots : List Result) : EvalM (List Result) :=
                if k = 0 then pure stateSlots else do
                  let outputSlots <- runStepSlots step ctx env stateSlots
                  repeatLoop (k-1) outputSlots
              let finalSlots <- repeatLoop n initialSlots
              let final := loopStateResult finalSlots
              pure (final, finalSlots.length)

        | .atomsBuiltin, [a] => do
            let r <- evalAlgOutput a ctx env
            -- `atoms` materializes a collection: one exact immutable list of
            -- the recursively collected numeric atoms (sequence AND list
            -- boundaries open; truth testing stays list-opaque).
            pure (makeCollectionListResult ((Result.languageAtoms r).map Result.atom))

        | .rangeBuiltin, [startAlg, stopAlg] => do
            let start <- expectInt (<- evalAlgOutput startAlg ctx env)
            let stop <- expectInt (<- evalAlgOutput stopAlg ctx env)
            let xs := inclusiveRange start stop
            -- `range` materializes a collection: one exact immutable list value.
            pure (makeCollectionListResult (xs.map Result.atom))

        | _, _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with plain Result output.
      This is the Result projection of `applyBuiltinCounted`: the counted twin
      owns the builtin dispatch and semantics, and the non-counted path only
      discards the emitted-count metadata. The CoreTests builtin projection
      parity guards pin this equivalence (values, error diagnostics, and
      evaluator state) case by case. -/
  partial def applyBuiltin
      (b : Builtin) (args : List Algorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- applyBuiltinCounted b args ctx env
    pure out.fst

  partial def expandSequenceSpreadBuiltinArguments
      (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Algorithm) := do
    -- Spread-marked argument slots are forced exactly once, in left-to-right written
    -- order, and expanding a spread slot is part of evaluating that slot: evaluate and
    -- expand the CURRENT spread slot before recursing into the remaining ones, then
    -- place its expansion before theirs. Non-spread slots pass through untouched as
    -- algorithms — they keep their written position and remain builtin-lazy, evaluated
    -- or skipped later by the builtin's own semantics (an unselected `if` branch never
    -- runs). Recursing first still produced the correct flattened argument order, but
    -- it ran the spread slots' effects and reported their failures right to left, so
    -- two failing spread slots reported the RIGHTMOST failure while the C# runtime
    -- reported the leftmost.
    let rec loop : List ResolvedArgumentAlgorithm -> EvalM (List Algorithm)
      | [] => pure []
      | arg :: rest => do
          if arg.spreadsSequence then
            let counted <- evalAlgOutputCounted arg.algorithm ctx env
            let expanded := (countedTopLevelValues counted).map (fun value => countedArgAlgorithm (value, 1))
            let tail <- loop rest
            pure (expanded ++ tail)
          else
            let tail <- loop rest
            pure (arg.algorithm :: tail)
    loop args

  partial def applyBuiltinCountedResolved
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    match sequenceBuiltinMetadata? b with
    | some metadata =>
        applyBuiltinCountedSequence b metadata args ctx env
    | none => do
        let expandedArgs <- expandSequenceSpreadBuiltinArguments args ctx env
        applyBuiltinCounted b expandedArgs ctx env

  partial def applyBuiltinResolved
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- applyBuiltinCountedResolved b args ctx env
    pure out.fst

  partial def evalVariadicCallItemCounted (e : Expr) (ctx : EvalCtx)
      (env : ValEnv) (exposeInlineBlockTopLevel : Bool)
      : EvalM CountedResult := do
    if exposeInlineBlockTopLevel then
      match e with
      -- A grouped receiver keeps its multi-item emitted count as the injected
      -- leading argument segment (no value-boundary re-count), for both the
      -- capture form and a zero-parameter scoped block.
      | .capture rows =>
          evalCaptureCountedCore rows ctx env
      | .algorithmExpr a =>
          let wired := wireToCaller ctx a
          if (Algorithm.params wired).length = 0 then
            evalAlgOutputCounted wired ctx env
          else
            evalCounted e ctx env
      | _ =>
          evalCounted e ctx env
    else
      evalCounted e ctx env

  /-- Evaluate one non-expanded call argument. Patterned calls additionally need the written
      output-slot view of a capture or zero-parameter `algorithmExpr`; obtain both products from
      the corresponding prepared-output evaluator in one pass. A multi-parameter algorithm
      remains on the ordinary dual algorithm/value fallback and is not forced to manufacture explicit items.
      Argument slots evaluate directly in the CALLER's context: the bundle owns
      no scope, so there is no argument-level lexical frame (the pre-Track-B
      transparent args wrapper was an empty caller-wired level, so lookup
      behavior is unchanged by its removal). -/
  partial def evalVariadicCallItemPrepared (e : Expr) (ctx : EvalCtx)
      (env : ValEnv) (exposeInlineBlockTopLevel : Bool)
      (includeExplicitItems : Bool) : EvalM PreparedCallArgumentEvaluation := do
    if includeExplicitItems then
      match e with
      | .capture rows => do
          let prepared <- evalCapturePreparedCore rows ctx env
          let counted :=
            if exposeInlineBlockTopLevel then prepared.counted
            else reCountValueBoundary prepared.counted
          pure { counted := counted, explicitItems? := some prepared.outputSlots }
      | .algorithmExpr a =>
          let wired := wireToCaller ctx a
          if (Algorithm.params wired).length = 0 then do
            let prepared <- evalAlgOutputPreparedCore wired ctx env
            let counted :=
              if exposeInlineBlockTopLevel then prepared.counted
              else reCountValueBoundary prepared.counted
            pure { counted := counted, explicitItems? := some prepared.outputSlots }
          else do
            let counted <- evalVariadicCallItemCounted e ctx env exposeInlineBlockTopLevel
            pure { counted := counted }
      | _ => do
          let counted <- evalVariadicCallItemCounted e ctx env exposeInlineBlockTopLevel
          pure { counted := counted }
    else do
      let counted <- evalVariadicCallItemCounted e ctx env exposeInlineBlockTopLevel
      pure { counted := counted }

  /-- Shared call argument-slot assembly used by EVERY callable shape (flat
      fixed, flat/mixed variadic, patterned, and multi-clause conditional):
      each written argument slot is evaluated exactly once, left to right; every non-spread slot is
      reified as exactly ONE argument value (with its dual algorithm view
      where resolvable), and every explicit spread slot is expanded by
      exactly one value boundary into ordinary argument slots. The final
      argument supply is formed BEFORE any arity checking, clause selection,
      conditional dispatch, or pattern binding — the callee's internal
      representation never influences the meaning of caller-side spread.
      An injected dot-call receiver segment
      (`CallArgumentAssembly.injectedDotReceiverLeading`) stays ONE segment
      for allocation — never pre-expanded — and retains its raw counted supply
      (`collectingSegmentCount?`) for the flat top-level collecting position.
      When `includeExplicitItems` is set (patterned callees), a non-spread
      capture or zero-parameter `algorithmExpr` also records its written item
      slots for sequence-value pattern binding. C#: `BuildCallArgumentInputs`. -/
  partial def collectVariadicCallItems (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      (assembly : CallArgumentAssembly := .ordinaryArguments)
      (includeExplicitItems : Bool := false)
      : EvalM (List VariadicItem) := do
    let maybeAlgs <- tryResolveArgAlgs args ctx
    let rec appendCounted (counted : CountedResult) (maybeAlg : Option Algorithm) (expand : Bool)
        (isReceiver : Bool) (explicitItems : Option (List Result)) (acc : List VariadicItem) : List VariadicItem :=
      if expand then
        let expanded := (countedTopLevelValues counted).map (fun value =>
          { value? := some value : VariadicItem })
        expanded.reverse ++ acc
      else
        { value? := some counted.fst,
          algorithm? := maybeAlg,
          explicitItems? := explicitItems,
          collectingSegmentCount? := if isReceiver then some counted.snd else none : VariadicItem } :: acc
    let shouldExpand (e : Expr) (isReceiver : Bool) : Bool :=
      match e with
      | .sequenceSpread _ => !isReceiver
      | _ => false
    let rec loop : List Expr -> List (Option Algorithm) -> Bool -> List VariadicItem -> EvalM (List VariadicItem)
      | [], _, _, acc => pure acc.reverse
      | e :: es, ma :: mas, isReceiver, acc => do
          let expand := shouldExpand e isReceiver
          match <- evalAttempt (evalVariadicCallItemPrepared e ctx env isReceiver
              (includeExplicitItems && !expand)) with
          | .ok prepared =>
            loop es mas false
              (appendCounted prepared.counted ma expand isReceiver prepared.explicitItems? acc)
          | .error err =>
            match ma with
            | some alg => loop es mas false ({ algorithm? := some alg, error? := some err : VariadicItem } :: acc)
            | none => .error err
      | e :: es, [], isReceiver, acc => do
          let expand := shouldExpand e isReceiver
          match <- evalAttempt (evalVariadicCallItemPrepared e ctx env isReceiver
              (includeExplicitItems && !expand)) with
          | .ok prepared =>
            loop es [] false
              (appendCounted prepared.counted none expand isReceiver prepared.explicitItems? acc)
          | .error err => .error err
    loop args maybeAlgs assembly.isInjectedDotReceiverLeading []

  /-- Bind a call to an item-supply parameter list (any top-level variadic).
      The call argument stream is already the receiver for parameter binding: a
      plain sequence-valued argument contributes one item, while explicit spread
      contributes the operand's items. -/
  partial def bindDeconstructionUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (assembly : CallArgumentAssembly := .ordinaryArguments)
      : EvalM (ValEnv × CountedParamEnv × AlgEnv) := do
    let items <- collectVariadicCallItems args ctx env assembly
    let inputs := items.map variadicItemToPatternInput
    let bindings <- bindParameterPatternList (Algorithm.parameterPatterns callee) inputs true
    pure (bindings.argEnv, bindings.countedParamEnv, bindings.algEnv)

  partial def evalExplicitSequenceValueItems (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
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
        | .mk _ _ _ _ [] => .error Error.missingOutput
        | _ => pure ()
        evalExplicitSequenceValueRowSlots (Algorithm.output a) (EvalCtx.push a ctx) env

  /-- The shared written-slot loop over ordered bundle rows: each row
      contributes its explicit written slots. Algorithm-shaped groupings reach
      it after pushing their own scope; a `Expr.capture` body reaches it
      directly (captures own no scope).
      C#: `EvalExplicitSequenceValueRowSlots`. -/
  partial def evalExplicitSequenceValueRowSlots (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          let values <- evalExplicitSequenceValueExprSlots e rowCtx env
          collect rest (values.reverse ++ acc)
    collect rows []

  partial def evalExplicitSequenceValueExprSlots (expr : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    match expr with
    -- A nested written grouping level materializes exactly one item, combined
    -- with the same shallow singleton-erasing rule as ordinary capture
    -- evaluation (`combineOutputSlots`). A singleton group such as `(A)` IS
    -- its single already-evaluated item and an all-spread-empty group is `()`
    -- -- never a literal-unwritable orphan such as `(5)`. Both node kinds keep
    -- this written-slot view: a capture body directly, and a zero-parameter
    -- scoped block through its algorithm.
    | .capture rows => do
        let items <- evalExplicitSequenceValueRowSlots rows ctx env
        pure [combineOutputSlots items]
    | .algorithmExpr algorithm => do
        let wired := wireToCaller ctx algorithm
        if (Algorithm.params wired).length = 0 then
          let items <- evalExplicitSequenceValueItems wired ctx env
          pure [combineOutputSlots items]
        else
          let out <- evalCounted expr ctx env
          pure [out.fst]
    | .sequenceSpread _ =>
        let out <- evalCounted expr ctx env
        pure (countedTopLevelValues out)
    | _ =>
        let out <- evalCounted expr ctx env
        -- WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        -- written slot contributes exactly ONE persistent value — the value
        -- its counted supply denotes — regardless of how many items the
        -- expression emitted (zero, one, or many). Only an explicit spread
        -- supplies the value's items into the surrounding item slots.
        pure [out.fst]

  partial def bindPatternedUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (assembly : CallArgumentAssembly := .ordinaryArguments)
      : EvalM (ValEnv × CountedParamEnv × AlgEnv) := do
    let items <- collectVariadicCallItems args ctx env assembly
      (includeExplicitItems := true)
    let inputs := items.map variadicItemToPatternInput
    let bindings <- bindParameterPatternList (Algorithm.parameterPatterns callee) inputs true
    pure (bindings.argEnv, bindings.countedParamEnv, bindings.algEnv)

  partial def bindFlatFixedUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM (ValEnv × AlgEnv) := do
    let params := Algorithm.params callee
    -- Shared argument-slot assembly (spread expansion happens there, before
    -- any arity checking).
    let items <- collectVariadicCallItems args ctx env
    let slots := items.map (fun item =>
      { value? := item.value?, algorithm? := item.algorithm?, error? := item.error? : FlatFixedCallSlot })
    if slots.length > params.length then
      .error (Error.arityMismatch params.length slots.length)
    else
      let rec collect : List Ident -> List FlatFixedCallSlot -> EvalM (List Ident × List Result × AlgEnv)
        | [], _ => pure ([], [], [])
        | p :: ps, [] => do
            let (valueParams, values, algBindings) <- collect ps []
            pure (p :: valueParams, values, algBindings)
        | p :: ps, slot :: rest => do
            let (valueParams, values, algBindings) <- collect ps rest
            let algBindings :=
              match slot.algorithm? with
              | some alg => (p, alg) :: algBindings
              | none => algBindings
            match slot.value? with
            | some value => pure (p :: valueParams, value :: values, algBindings)
            | none =>
                match slot.algorithm? with
                | some _ => pure (valueParams, values, algBindings)
                | none => .error (slot.error?.getD Error.badArity)
      let (valueParams, values, algBindings) <- collect params slots
      let argEnv <- bindParams valueParams values
      pure (argEnv, algBindings)

  /-- Counted user-defined call evaluation — the CANONICAL user-call
      implementation (`evalUserCall` is its value projection).

      Shared user-defined call binding logic. Preserves the eager value ABI
      while layering AlgEnv for higher-order arguments. Each original argument
      expression is interpreted independently in two ways:
      - structural algorithm resolution for AlgEnv
      - ordinary eager value evaluation for ValEnv

      If both succeed, the parameter gets both meanings. If only one succeeds,
      only that view is bound. A parameter bound only through `AlgEnv` still
      SHADOWS the caller's inherited value environment (`ValEnv.shadow`, the
      value-tier counterpart of `CountedParamEnv.shadow`), so a value-position
      read of that parameter reaches its algorithm binding — the ordinary
      zero-argument value demand or its arity error — instead of silently
      answering with a same-named caller value. If both fail, the ordinary
      eager-evaluation error is propagated. Every `algorithmExpr` contributes
      its contained algorithm to the `AlgEnv` side regardless of declaration/output count;
      a `capture` contributes only its fresh zero-parameter value thunk and
      never exposes contained algorithm identity.

      Flat fixed calls bind call-site structure: each comma argument is one
      argument expression, while a bare `sequenceSpread` expression explicitly
      contributes its spread top-level items. Multi-output values from ordinary
      expressions, including `.atoms`, remain one argument expression. Earlier
      explicit argument positions stay distinct on the eager value side even if
      some later arguments bind only through `AlgEnv`.

      A user/property call is a value boundary: the public result preserves the
      structural value while re-counting the emitted arity to
      `Result.valueCount` (via `reCountValueBoundary`). A multi-output body
      therefore becomes one sequence value (count 1); only a caller-site spread
      `value*` re-spreads it. -/
  partial def evalUserCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (assembly : CallArgumentAssembly := .ordinaryArguments)
      : EvalM CountedResult := do
    if (Algorithm.output callee).isEmpty then
      .error Error.missingOutput
    else if Algorithm.requiresPatternBinding callee then do
          let (argEnv, countedParamEnv, algBindings) <-
            bindPatternedUserCall callee args ctx env assembly
          let shadowedCountedParamEnv := CountedParamEnv.shadow ctx.countedParamEnv (Algorithm.params callee)
          let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
          let newCtx :=
            (ctx.withAlgEnv (algBindings ++ ctx.algEnv)).withCountedParamEnv
              (countedParamEnv ++ shadowedCountedParamEnv)
          reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)
    else match Algorithm.collectingParam? callee with
      | some _ =>
          -- Any top-level variadic binds the supplied call argument stream.
          let (argEnv, countedParamEnv, algBindings) <-
            bindDeconstructionUserCall callee args ctx env assembly
          let shadowedCountedParamEnv := CountedParamEnv.shadow ctx.countedParamEnv (Algorithm.params callee)
          let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
          let newCtx :=
            (ctx.withAlgEnv (algBindings ++ ctx.algEnv)).withCountedParamEnv
              (countedParamEnv ++ shadowedCountedParamEnv)
          reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)
      | none =>
      do
        let (argEnv, algBindings) <- bindFlatFixedUserCall callee args ctx env
        let newCtx := (ctx.withAlgEnv (algBindings ++ ctx.algEnv)).withCountedParamEnv
          (CountedParamEnv.shadow ctx.countedParamEnv (Algorithm.params callee))
        let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
        reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)

  /-- Assemble the evaluated argument values for a conditional (multi-clause)
      call through the shared call argument pipeline
      (`collectVariadicCallItems`): non-spread slots reify as one value each
      and explicit spread expands by one value boundary, exactly as for every
      other callable shape. Clause matching needs plain values, so an
      algorithm-only argument surfaces its value-evaluation error.
      C#: `EvalConditionalCallArguments`. -/
  partial def evalConditionalCallArguments (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (assembly : CallArgumentAssembly)
      : EvalM (List Result) := do
    let items <- collectVariadicCallItems args ctx env assembly
    items.mapM (fun item =>
      match item.value? with
      | some value => pure value
      | none => .error (item.error?.getD Error.badArity))

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
  partial def evalConditionalCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      (assembly : CallArgumentAssembly := .ordinaryArguments) : EvalM CountedResult := do
    let argResults <- evalConditionalCallArguments args ctx env assembly
    if callee.hasDuplicateBranchPatterns then
      .error Error.duplicateBranchPattern
    else
      match matchCallBranches (Algorithm.branches callee) argResults with
      | some (branch, bindings) =>
          let wiredBody := Algorithm.childOf callee branch.body
          let names := bindings.map Prod.fst
          let newCtx := (EvalCtx.push callee ctx).withCountedParamEnv
            (CountedParamEnv.shadow ctx.countedParamEnv names)
          reCountValueBoundary <$> evalAlgOutputCounted wiredBody newCtx (bindings ++ env)
      | none =>
          .error (Error.noMatchingBranch calleeName)

  /-- Dispatch an already-resolved callee with plain Result output.
      This is the Result projection of `evalResolvedCallCounted`: the counted
      twin owns the builtin/flat-binder/conditional/user dispatch, and each of
      its arms already ends in a projected family, so the projection is
      compositional. -/
  partial def evalResolvedCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      (assembly : CallArgumentAssembly := .ordinaryArguments) : EvalM Result := do
    let out <- evalResolvedCallCounted callee args ctx env calleeName assembly
    pure out.fst

  /-- Dispatch an already-resolved callee in counted evaluation — the
      CANONICAL resolved-callee dispatch (`evalResolvedCall` is its value
      projection). -/
  partial def evalResolvedCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      (assembly : CallArgumentAssembly := .ordinaryArguments) : EvalM CountedResult := do
    match callee with
    | .builtin b => do
      let argAlgs <- resolveArgAlgsWithSequenceSpread args ctx env
      applyBuiltinCountedResolved b argAlgs ctx env
    | .conditional _ _ _ =>
      match flatBinderUserEquivalent? callee with
      | some simple => evalUserCallCounted simple args ctx env assembly
      | none => evalConditionalCallCounted callee args ctx env calleeName assembly
    | _ => evalUserCallCounted callee args ctx env assembly

  /-- Context-aware counted call evaluation for expression position — the
      CANONICAL expression-position call dispatch (`evalCallExpr` is its value
      projection); attaches `CtxMsg.call` to resolution and dispatch errors. -/
  partial def evalCallCountedExpr (f : Expr) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let callee <- withCtx (CtxMsg.call f) <| resolveAlg f ctx
    withCtx (CtxMsg.call f) <| evalResolvedCallCounted callee args ctx env (openExprName f)

  /-- Sequence builtins in dot-call form evaluate the receiver to ONE value,
      re-counted to `Result.valueCount`, and pass it as the ordinary fixed
      `collection` argument (the post-binding collection view opens it,
      exactly as for the plain call form).

      A direct inline receiver block first exposes its inner algorithm output
      count, which strips exactly one receiver-scoping block layer for forms
      like `(1, 2, 3).take(2)` while still keeping `((1, 2, 3)).take(2)` and
      named sequence-valued helpers intact. Any extra dot-call arguments
      still follow the plain-call argument path.

      This keeps plain-call boundary preservation unchanged while making
      `receiver.builtin(...)` operate on the same top-level collection that
      `receiver:i` and higher-order callback projection observe. -/
  partial def evalSequenceBuiltinDotReceiverCounted (receiver : Expr) (ctx : EvalCtx)
      (env : ValEnv) : EvalM CountedResult := do
    let value <- eval receiver ctx env
    pure (value, Result.valueCount value)

  partial def sequenceBuiltinDotReceiverArgs (receiver : Expr) (ctx : EvalCtx)
      (env : ValEnv) : EvalM (List ResolvedArgumentAlgorithm) := do
    let receiverOut <- evalSequenceBuiltinDotReceiverCounted receiver ctx env
    pure [{ algorithm := countedArgAlgorithm receiverOut, spreadsSequence := false }]

  partial def trySequenceBuiltinDotCall
      (name : Ident) (receiver : Expr) (extraArgs : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM (Option (Builtin × List ResolvedArgumentAlgorithm)) := do
    match <- evalAttempt (resolveAlg (.resolve name) ctx) with
    | .ok (.builtin b) =>
        match sequenceBuiltinMetadata? b with
        | some _ =>
            let receiverArgAlgs <- sequenceBuiltinDotReceiverArgs receiver ctx env
            let extraArgAlgs <-
              match extraArgs with
              | some args => resolveArgAlgsWithSequenceSpread args ctx env
              | none => pure []
            match b, extraArgAlgs with
            | .reduceBuiltin, [missingInitialReducer] =>
                if (Algorithm.params missingInitialReducer.algorithm).isEmpty then
                  pure (some (b, receiverArgAlgs ++ extraArgAlgs))
                else
                  .error reduceInitialAccumulatorRequiresValueError
            | _, _ =>
                pure (some (b, receiverArgAlgs ++ extraArgAlgs))
        | none =>
            pure none
    | _ =>
        pure none

  /-- Counted lexical fallback with receiver injection.
      The injected receiver is one leading argument segment.

      The STORED lexical-fallback identity decides the callee channel — the
      front-end's Param-vs-Resolve decision is CONSUMED here, never
      reconstructed from runtime environments:
      - a `.resolve` fallback takes the ordinary name-based path, including
        the dotted sequence-builtin receiver view;
      - any other fallback (normally `.param`) resolves through canonical
        `resolveAlg`, so a parameter shadows a same-name builtin exactly as in
        plain-call position. Non-name hand-built fallbacks are outside the
        post-elaboration contract and follow their ordinary `resolveAlg`
        behavior defensively. -/
  partial def callLexicalWithReceiverCounted (name : Ident) (receiver : Expr)
      (fallback : Expr)
      (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match fallback with
    | .resolve fallbackName =>
      match <- trySequenceBuiltinDotCall fallbackName receiver extraArgs ctx env with
      | some (b, args) =>
        applyBuiltinCountedResolved b args ctx env
      | none =>
        let callee <- resolveAlg (.resolve fallbackName) ctx
        let combinedArgs := prepareLexicalDotCallArgs receiver extraArgs
        evalResolvedCallCounted callee combinedArgs ctx env fallbackName .injectedDotReceiverLeading
    | other =>
      let callee <- resolveAlg other ctx
      let combinedArgs := prepareLexicalDotCallArgs receiver extraArgs
      evalResolvedCallCounted callee combinedArgs ctx env name .injectedDotReceiverLeading

  /-- Evaluate dotCall: a.f or a.f(args). The member result is a value boundary:
      structural zero-arg property access and collection builtins re-count to
      `Result.valueCount`, and user/lexical member calls re-count via
      `evalUserCallCounted`, so a multi-output member becomes one sequence value
      (count 1) and only a caller-site spread `value*` re-spreads
      it. This is the single owner
      of dot-call dispatch; `evalDotCall` is its Result projection.
      Smart dispatch:
      - "string" value intrinsic → evaluate target, convert numeric result to string
      - Structural property found (navigation-only):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - No property → lexical fallback (receiver injection)

      When resolveAlg returns notAnAlgorithm (e.g. numeric literal target),
      value-based intrinsics are checked before lexical fallback.

      (The C# front end consumes the Grace annotation in `a~.f` / `a.~f`, so
      Lean receives the same dotMember and the same structural-first dispatch
      as for ordinary `a.f`.)

      Optimization note for executable evaluators: repeated references to the
      same eligible structural or lexical property may be reused within one
      top-level run when the property is fully wired and requires no further
      arguments in the current evaluation context. This is intentionally local
      to one run and must not be interpreted as memoizing arbitrary calls or as
      changing the semantic behavior of dotCall itself. -/
  partial def evalDotCallCounted (target : Expr) (name : Ident)
      (fallback : Expr) (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match <- evalAttempt (resolveAlg target ctx) with
    | .ok targetAlg =>
      if name = "string" then do
        let val <- evalAlgOutput targetAlg ctx env
        let out <- resultToString val
        pure (out, Result.valueCount out)
      else
        match Algorithm.lookupPropDefAny? targetAlg name with
        | some p =>
            if !p.exposure.isExported then
              .error (Error.localOnlyProperty (openExprName target) name p.exposure)
            else
            let wired := Algorithm.childOf targetAlg p.alg
            match argsOpt with
            | none =>
                match flatBinderUserEquivalent? wired with
                | some simple =>
                    if (Algorithm.params simple).length = 0 then
                      reCountValueBoundary <$> evalZeroArgPropertyAccessCounted .structural targetAlg p simple ctx env
                    else
                      .error (Error.arityMismatch (Algorithm.params simple).length 0)
                | none =>
                    match wired with
                    | .conditional _ _ _ => .error (Error.noMatchingBranch name)
                    | _ =>
                        if (Algorithm.params wired).length = 0 then
                          reCountValueBoundary <$> evalZeroArgPropertyAccessCounted .structural targetAlg p wired ctx env
                        else
                          .error (Error.arityMismatch (Algorithm.params wired).length 0)
            | some args =>
                evalResolvedCallCounted wired args ctx env name
        | none =>
            if Algorithm.conditionalBranchesDefineProperty targetAlg name then
              .error (Error.localOnlyProperty (openExprName target) name .localConditional)
            else
              callLexicalWithReceiverCounted name target fallback argsOpt ctx env
    | .error (.notAnAlgorithm _) =>
      if name = "string" then do
        let val <- eval target ctx env
        let out <- resultToString val
        pure (out, Result.valueCount out)
      else
        callLexicalWithReceiverCounted name target fallback argsOpt ctx env
    | .error e => .error e

  /-- Evaluate a spread operand and supply its immediate items. Spreading an
      operand that has no defined output is the spread-specific
      `spreadMissingOutput` error on EVERY operand shape — the direct
      `.algorithmExpr`/`.capture` specializations translate a missing-output
      failure exactly like the generic arm, so `{A = 1}*` and
      `X = {A = 1}` / `X*` agree.
      C#: `EvalSequenceSpreadOperandItems`. -/
  partial def evalSequenceSpreadOperandItems (e : Expr) (ctx : EvalCtx)
      (env : ValEnv) : EvalM (List Result) := do
    match e with
    | .capture rows =>
        match <- evalAttempt (evalCaptureValue rows ctx env) with
        | .ok value =>
            pure value.spreadItems
        | .error err =>
            if isMissingOutputError err then
              .error Error.spreadMissingOutput
            else
              .error err
    | .algorithmExpr a =>
        let wired := wireToCaller ctx a
        if (Algorithm.params wired).length = 0 then
          match <- evalAttempt (evalAlgOutput wired ctx env) with
          | .ok value =>
              pure value.spreadItems
          | .error err =>
              if isMissingOutputError err then
                .error Error.spreadMissingOutput
              else
                .error err
        else
          .error (Error.unresolvedImplicitParams (Algorithm.params wired))
    | _ =>
        match <- evalAttempt (eval e ctx env) with
        | .ok value =>
            pure value.spreadItems
        | .error err =>
            if isMissingOutputError err then
              .error Error.spreadMissingOutput
            else
              .error err

    /-- Evaluate a unary `sequenceSpread` node by evaluating its single operand
      once and spreading immediate top-level items. Nested sequence-value
      members are not recursively flattened. Directly-nested spreads (`A**`)
      are unwrapped iteratively (`peelSequenceSpreadLayers`, stack-safe for deep
      nesting) and then each written layer is applied COMPOSITIONALLY: every
      written `sequenceSpread` layer opens exactly one boundary of the value
      the previous layer's supply re-captures, so `A**` agrees with `(A*)*`.
      For sequence values
      the extra layers are fixed points (value-equivalent to a single spread);
      a singleton-list chain opens one list boundary per layer
      (`[[7]]**` supplies `7`), while a multi-element list re-captures as
      a sequence after the first layer and then stays fixed
      (`[[1, 2], [3, 4]]**` supplies the two inner lists unchanged). -/
  partial def evalSequenceSpreadCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let (operand, layers) := peelSequenceSpreadLayers e 0
    let supplied <- evalSequenceSpreadOperandItems operand ctx env
    let rec reopen : Nat -> List Result -> List Result
      | 0, items => items
      | n + 1, items =>
          reopen n (Result.spreadItems (Result.normalize (Result.sequenceValue items)))
    let items := reopen (layers - 1) supplied
    pure (Result.normalize (Result.sequenceValue items), items.length)

  /-- Evaluate a surface list literal `[e1, ..., en]` as exactly ONE exact
      immutable list value. Element slots reuse the written-parentheses
      expression-list slot rules (`evalExplicitSequenceValueExprSlots`): an
      explicit spread slot opens its operand's immediate items into the list
      being constructed (an empty spread contributes no elements), a non-spread
      slot is one element even when it evaluates to the empty sequence value
      `()`, and a nested capture or zero-parameter `algorithmExpr` is one written grouping level.
      Unlike sequence construction the collected elements are stored EXACTLY:
      no singleton erasure and no empty canonicalization, so `[7]`, `[[7]]`,
      `[]`, and `[()]` are all distinct list values. A list literal always
      emits one value. C#: `EvalListLiteralCounted`; plain `eval` is this
      function's value projection on both sides. -/
  partial def evalListLiteralCounted (elements : List Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          let values <- evalExplicitSequenceValueExprSlots e ctx env
          collect rest (values.reverse ++ acc)
    let items <- collect elements []
    pure (Result.listValue items, 1)

  /-- Evaluate the INTERNAL `sequenceConstruct` join node as one sequence
      value. Join semantics, not written-parentheses semantics: a non-spread
      leaf whose value is `()` contributes NO item (an empty join
      contribution), an explicit spread leaf opens its operand's immediate
      items into the constructed sequence, and the result is normalized.
      Written parentheses parse to `capture` nodes and always keep a
      non-spread `()` item visible — surface syntax must never route through
      this node (see the constructor note on `Expr.sequenceConstruct`).
      C#: `EvalSequenceConstructCounted`; plain `eval` is this function's
      value projection on both sides. -/
  partial def evalSequenceConstructCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let rec loop : List Expr -> List Result -> EvalM CountedResult
      | [], items =>
          let value := Result.normalize (Result.sequenceValue items.reverse)
          pure (value, Result.valueCount value)
      | leaf :: rest, items => do
          match leaf with
          | .sequenceSpread _ => do
              let supplied <- evalSequenceSpreadOperandItems leaf ctx env
              loop rest (supplied.reverse ++ items)
          | _ => do
              let value <- eval leaf ctx env
              if Result.valueCount value = 0 then
                loop rest items
              else
                loop rest (value :: items)
    loop (sequenceConstructLeaves e) []

  /-- Evaluate a unary operator expression as one counted value. The operand is
      read at its value boundary; the empty sequence value propagates through
      unary operators, strings are rejected, and any other operand must be a
      numeric scalar. Owned here so `eval` (the value projection) never carries
      independent operator semantics. C#: the unary case of
      `EvalExpressionSpineCounted`. -/
  partial def evalUnaryCounted (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let r <- eval operand ctx env
    match r with
    | .sequenceValue [] => pure (Result.sequenceValue [], 0)   -- empty propagates through unary
    | .str _ => .error (Error.typeMismatch "Unary operator is not supported for strings")
    | _ => do
      let v <- expectInt r
      pure (Result.atom <|
        match op with
        | .minus => -v
        | .not   => if v = 0 then 1 else 0, 1)

  /-- Evaluate a binary operator expression as one counted value. Both operands
      are read at their value boundaries. `==`/`!=` compare KatLang values
      structurally across all value kinds; empty results stay transparent for
      the non-comparison operators; strings reject the non-equality operators;
      everything else follows the numeric-scalar core. Owned here so `eval`
      (the value projection) never carries independent operator semantics.
      C#: the binary case of `EvalExpressionSpineCounted` / `ApplyBinaryOperator`. -/
  partial def evalBinaryCounted (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let lr <- eval a ctx env
    let rr <- eval b ctx env
    match op with
    -- `==` and `!=` compare KatLang values structurally across all value kinds
    -- (numbers, strings, and sequence values, recursively). Different value
    -- kinds compare unequal rather than raising a type mismatch. This dedicated
    -- path is separate from the numeric-scalar-only validation used by the
    -- arithmetic and ordering operators below.
    | .eq => pure (Result.atom (if resultValueEq lr rr then 1 else 0), 1)
    | .ne => pure (Result.atom (if resultValueEq lr rr then 0 else 1), 1)
    | _ =>
      -- Empty results remain transparent for the non-comparison operators.
      match lr, rr with
      | .sequenceValue [], .sequenceValue [] => pure (Result.sequenceValue [], 0)
      | .sequenceValue [], _ => pure (rr, Result.valueCount rr)
      | _, .sequenceValue [] => pure (lr, Result.valueCount lr)
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
          pure (Result.atom <|
            -- `.eq`/`.ne` are handled structurally above; the arms below keep the
            -- numeric match exhaustive over BinaryOp and are unreachable here.
            match op with
            | .add  => x + y
            | .sub  => x - y
            | .mul  => x * y
            -- Division and modulo truncate toward zero (Int.tdiv / Int.tmod),
            -- matching the C# reference: `-7 div 2 = -3` and `-7 mod 2 = -1`.
            -- `/` on non-divisible operands additionally truncates the exact
            -- decimal quotient as part of the integer-core limitation.
            | .div  => x.tdiv y
            | .idiv => x.tdiv y
            | .mod  => x.tmod y
            | .pow  => intPow x y.toNat
            | .lt   => if x < y then 1 else 0
            | .gt   => if x > y then 1 else 0
            | .le   => if x <= y then 1 else 0
            | .ge   => if x >= y then 1 else 0
            | .eq   => if x = y then 1 else 0
            | .ne   => if x != y then 1 else 0
            | .and  => if x != 0 then (if y != 0 then 1 else 0) else 0
            | .or   => if x != 0 then 1 else (if y != 0 then 1 else 0)
            | .xor  => if x != 0 then (if y = 0 then 1 else 0) else (if y != 0 then 1 else 0), 1)

  /-- Evaluate an expression together with the number of top-level values it
      emits at the current algorithm boundary — the CANONICAL expression
      dispatch: it matches EVERY `Expr` variant explicitly (no default arm),
      and plain `eval` is its total value projection. A new `Expr` variant
      therefore fails compilation here until it is given a counted arm — the
      structural guard against silently reintroducing plain-owned semantics.

      Calls, name resolution, and collection builtins are value boundaries: they
      emit `Result.valueCount` of the result value (one value for a non-empty
      result), so a multi-output body/collection is observed as one sequence
      value and only a caller-site spread `value*` re-spreads it.
      Block expressions count as one sequence value when non-empty. `sequenceConstruct`
      emits one constructed sequence value. `sequenceSpread`
      emits the immediate spread items of its operand. All other value expressions emit either zero values (empty
      result) or one value. -/
  partial def evalCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match e with
    | .param x =>
        match ctx.countedParamEnv.lookup x with
        | some counted => pure counted
        | none =>
            match env.lookup x with
            | some v => pure (v, Result.valueCount v)
            | none =>
                match ctx.algEnv.lookup x with
                | some alg =>
                    match conditionalValueAccessError? x alg with
                    | some err => .error err
                    | none =>
                        if (Algorithm.params alg).length = 0 then do
                          let value <- evalAlgOutput alg ctx env
                          pure (value, Result.valueCount value)
                        else
                          .error (Error.arityMismatch (Algorithm.params alg).length 0)
                | none => .error (Error.unknownName x)
    | .sequenceConstruct _ _ =>
      evalSequenceConstructCounted e ctx env
    | .emptySequence depth =>
        let value := buildEmptySequenceValue depth
        pure (value, Result.valueCount value)
    | .sequenceSpread _ =>
        evalSequenceSpreadCounted e ctx env
    | .listLiteral elements =>
        evalListLiteralCounted elements ctx env
    | .algorithmExpr a => do
        let wired := wireToCaller ctx a
        if (Algorithm.params wired).length = 0 then
          let r <- evalAlgOutput wired ctx env
          pure (r, Result.valueCount r)
        else
          .error (Error.unresolvedImplicitParams (Algorithm.params wired))
    | .capture rows => do
        -- A capture in value position is a value boundary: the body's supply
        -- is captured to one canonical value and re-counted as that value's
        -- valueCount.
        let r <- evalCaptureValue rows ctx env
        pure (r, Result.valueCount r)
    | .resolve n => do
        match ctx.callStack with
        | owner :: _ =>
            let resolved <- lookupLexicalProperty owner n ctx
            match conditionalValueAccessError? n resolved.alg with
            | some err => .error err
            | none =>
                if (Algorithm.params resolved.alg).length = 0 then
                  withMissingOutputCtx (CtxMsg.property n) <| do
                    let counted <- evalZeroArgPropertyAccessCounted .lexical resolved.owner resolved.binding resolved.alg ctx env
                    pure (counted.fst, Result.valueCount counted.fst)
                else
                  .error (Error.withContext (CtxMsg.property n) (Error.arityMismatch (Algorithm.params resolved.alg).length 0))
        | [] => .error (Error.unknownName n)
    | .index a i => do
        let ar <- eval a ctx env
        let ir <- eval i ctx env
        let n  <- expectInt ir
        if n < 0 then
          .error Error.badIndex
        else
          match Result.select? ar (Int.toNat n) with
          | some projected => pure projected
          | none => .error Error.badIndex
    | .dotMember o n fallback argsOpt => withCtx (CtxMsg.dotCall o n) do
        evalDotCallCounted o n fallback argsOpt ctx env
    | .call f args =>
        evalCallCountedExpr f args ctx env
    | .num n => pure (Result.atom n, 1)
    | .stringLiteral s => pure (Result.str s, 1)
    | .unary op operand =>
        evalUnaryCounted op operand ctx env
    | .binary op a b =>
        evalBinaryCounted op a b ctx env

  /-- User-defined call evaluation with plain Result output.
      This is the Result projection of `evalUserCallCounted`: the counted twin
      owns argument binding (dual-view ABI, patterned/deconstruction/flat
      dispatch) and body evaluation, and the non-counted path only discards
      the emitted-count metadata (`reCountValueBoundary` is value-preserving).
      The CoreTests call projection parity guards pin this equivalence. -/
  partial def evalUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (assembly : CallArgumentAssembly := .ordinaryArguments)
      : EvalM Result := do
    let out <- evalUserCallCounted callee args ctx env assembly
    pure out.fst

  /-- Conditional call evaluation with plain Result output.
      This is the Result projection of `evalConditionalCallCounted`: the
      counted twin owns argument assembly, clause matching, and branch body
      evaluation, and the non-counted path only discards the emitted-count
      metadata (`reCountValueBoundary` is value-preserving). The CoreTests
      call projection parity guards pin this equivalence. -/
  partial def evalConditionalCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      (assembly : CallArgumentAssembly := .ordinaryArguments) : EvalM Result := do
    let out <- evalConditionalCallCounted callee args ctx env calleeName assembly
    pure out.fst

  /-- Context-aware direct call evaluation for expression position with plain
      Result output. This is the Result projection of `evalCallCountedExpr`:
      the counted twin owns callee resolution and dispatch, including the
      `CtxMsg.call` error-context attachment, so contexts cannot drift between
      the plain and counted spellings. -/
  partial def evalCallExpr (f : Expr) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalCallCountedExpr f args ctx env
    pure out.fst

  /-- Dot-call evaluation with plain Result output.
      This is the Result projection of `evalDotCallCounted`: the counted twin
      owns the dot-call dispatch (receiver resolution, structural lookup,
      lexical fallback with receiver injection, zero-arg property access,
      conditional dispatch, and receiver-spread rules), and the non-counted
      path only discards the emitted-count metadata. The CoreTests dot-call
      projection parity guards pin this equivalence (values, error
      diagnostics, and evaluator state) case by case. -/
  partial def evalDotCall (target : Expr) (name : Ident)
      (fallback : Expr) (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalDotCallCounted target name fallback argsOpt ctx env
    pure out.fst

  /-- Expression evaluation with plain Result output.
      This is the TOTAL Result projection of `evalCounted`: the counted
      evaluator owns the per-variant dispatch for every `Expr` constructor
      (leaves included), and this projection only discards the emitted-count
      metadata. Counted code calls it wherever a subexpression is read at a
      value boundary; that recursion is into strictly smaller work, never a
      same-node ownership cycle, because `evalCounted` has no arm that
      delegates back here. -/
  partial def eval (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalCounted e ctx env
    pure out.fst

end

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

    IMPORTANT: Opens CAN suppress implicit parameters. If an opened library
    provides `name`, the surface layer emits `Expr.resolve name`, not a param.
    This is intentional: opens have lexical precedence in the ownership-first model.
    The trade-off is accepted: shadowing via opens is rare and explicit (listed in `opens:`).

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
-- Surface syntax support: implicit argument resolution
--------------------------------------------------------------------------------

/- **Implicit argument resolution** (surface syntax pass — runs after parameter
   detection):

   When a property body contains a bare reference to a sibling property that has
   parameters, the surface layer rewrites that reference into an explicit call,
   passing the sibling's parameter-pattern captures as arguments (lifted into
   the referencing property's own parameter-pattern list when they are not
   already provided by the caller).

   Example:
     Surface:   `{ A = x + 1  B = A * 2 }`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

   Recursive parameter patterns are preserved by this surface pass: lifting
   `*items`, `(*items)`, or `((*history), previous)` keeps that shape
   instead of reconstructing ordinary capture parameters from flattened names.
   A narrow forwarding rule also permits a bare helper reference with one
   forwardable variadic supply to use a containing algorithm's single
   top-level variadic supply by shape rather than by capture-name equality.
   This is not a general positional parameter-matching rule.

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

   Cycles are handled by leaving cyclic properties unmodified (no implicit
   argument lifting for properties involved in mutual recursion). -/

-- Surface syntax support: while/repeat initial-state boundaries
--------------------------------------------------------------------------------

/- **Ordinary parentheses** construct sequence values.  There is no special
   "double-parens" syntax.  `((expr))` in any position is nested sequence-value
   construction.  `f((a + b) mod 2, c)` parses normally as two arguments.

   **while/repeat initial state** preserves explicit argument boundaries.
   The evaluator accepts variable arity for these builtins:

     while(step, s1, s2, ..., sk)         -- k ≥ 1
     repeat(step, count, s1, s2, ..., sk) -- k ≥ 1

   Each explicit init argument is evaluated independently and becomes exactly
   one initial state slot.  Therefore `repeat(Step, 3, a, b)` starts with two
   slots, while `repeat(Step, 3, Pair)` starts with one slot even if `Pair`
   evaluates to multiple values.  Use explicit selections such as `Pair:0,
   Pair:1` when the intended initial state is two slots.

   DotCall lexical fallback (`Step.repeat(...)` / `Step.while(...)`) injects
   the receiver as the step argument and keeps the remaining explicit args in
   the same boundary-preserving form after structural property lookup.

   Step outputs still define the state slots for the next iteration by emitted
   top-level output boundaries.  To keep one structured slot across iterations,
   return a sequence-value step result; multi-output steps intentionally
   become many next-state slots.

   Expr.capture semantics
   ----------------------
   No tuple constructor exists in the Lean core AST; written sequence-value
   construction is expressed via `Expr.capture` over an OutputBundle of row
   expressions.  Free identifiers inside a capture bubble up to the enclosing
   algorithm through ParameterDetector, because a capture owns no scope.

   Examples
   --------
     while(Step, 5, 0)       -- initial state has two slots
     repeat(Step, 3, 0, 0)   -- initial state has two slots
     Step.while(x, 0)        -- initial state has two slots
     Step.repeat(3, x, 0)    -- initial state has two slots
     Step.while((x, 0))      -- initial state has one sequence-value slot
     while(Step, init)        -- initial state has one slot
     repeat(Step, n, init)    -- initial state has one slot -/

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
   algorithm, which is essential for higher-order binding via AlgEnv.
   (Per-expression Algorithm resolution remains separate from value
   evaluation, and the runtime may still construct one-expression
   Algorithm adapters — `Algorithm.ofExpr`, `countedArgAlgorithm`, the
   capture value thunk — for deferred/lazy evaluation of individual
   slots; those adapters are runtime machinery, not the source AST.)

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
   3. `tryResolveArgAlgs` calls `resolveAlg(Expr.algorithmExpr inlineAlg)` on
      that bundle slot, which returns `inlineAlg` (wired to caller scope).
   4. The callee's `func` parameter is bound in AlgEnv to `inlineAlg`.
   5. When the callee evaluates `func(9)`, the value `9` is bound to `a` and
      the output `a + 1` evaluates to `10`.

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

def runResultM (e : Expr) : EvalM Result := do
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      if (Algorithm.params wired).length = 0 then
        evalProgramOutput wired ctx []
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => eval e ctx []

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
def index (a i : Expr) : Expr := .index a i
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

/-- Elaboration errors for load directives (distinct from runtime EvalM errors).
    These are reported during the elaboration pass, before evaluation. -/
inductive LoadError where
  | domainNotAllowed : String -> LoadError           -- host not in allowlist
  | invalidUrl       : String -> LoadError           -- malformed URL
  | notHttps         : String -> LoadError           -- non-HTTPS scheme
  | urlNotLiteral    : LoadError                     -- non-constant URL expression
  | runtimePosition  : LoadError                     -- load in non-allowed position
  | cycleDetected    : List String -> LoadError      -- URL cycle stack
  | fetchFailed      : String -> String -> LoadError -- url, reason
  | sizeLimitExceeded : String -> Nat -> LoadError   -- url, size
  | parseError       : String -> LoadError           -- url with parse errors
  deriving Repr

/-- Context for the load elaboration pass. Tracks:
    - allowedHosts: set of permitted domain names
    - cache: previously loaded URLs → their elaborated algorithms
    - inProgress: URLs currently being loaded (for cycle detection)
    - fetch: abstract code fetcher URL → source text -/
structure LoadCtx where
  allowedHosts : List String
  cache        : Assoc String Algorithm
  inProgress   : List String
  fetch        : String -> Option String   -- abstract host acquisition; C# awaits DownloadCode before this model

/-- Positions where load is allowed (compile-time only).
    load is a directive, not a runtime expression. -/
inductive LoadPosition where
  | propertyDef : LoadPosition   -- RHS of Name = load('url')
  | openList    : LoadPosition   -- inside open load('url') or open target1, target2
  deriving Repr, BEq

/- **load elaboration judgment**

  The elaboration pass transforms surface `Call(Resolve("load"), ...)` nodes into
  `Expr.algorithmExpr (parseModule (fetch url))` nodes.  `load` is NOT a core Expr
  constructor — it exists only as surface syntax represented via
  `call (resolve "load") (alg with output = [stringLiteral url])`.
  The elaborator extracts the URL from the stringLiteral argument and enforces:

  2. **Allowed position**: load may only appear in:
     - Property definition RHS: `Lib = load('https://katlang.org/lib.kat')`
     - Open declarations: `open load('https://katlang.org/lib.kat')`
     load in runtime positions (binary expressions, call arguments, if/while
     branches, etc.) is rejected.

  3. **Domain allowlist**: The URL's host must be in `LoadCtx.allowedHosts`
     (default: ["katlang.org"]). Subdomains are permitted.

  4. **HTTPS only**: Only `https://` URLs are accepted.

  5. **Cycle detection**: If URL is in `LoadCtx.inProgress`, elaboration fails
     with `cycleDetected`.

  6. **Caching**: If URL is in `LoadCtx.cache`, the cached algorithm is reused.
     Same URL → same content → same AST (determinism within a run).

  7. **Size limit**: Fetched source must not exceed a reasonable limit.

  **Post-condition (invariant)**: After elaboration completes successfully,
  the resulting AST satisfies `postElabInvariant` / `postElabInvariantAlg`,
  which guarantees:
    1. Runtime `Expr.stringLiteral` nodes may remain as ordinary first-class values.
    2. No unresolved load calls remain (i.e., no `call (resolve "load") _` nodes).
  All load directives have been replaced with `Expr.algorithmExpr` containing the
  parsed and elaborated remote algorithm. The evaluator never sees unresolved
  load calls.

  Formally:
    elaborate(call(resolve("load"), [stringLiteral url])) = block(parseModule(fetch(url)))
    ∀ e ∈ elaborated AST, e ≠ Expr.call (Expr.resolve "load") _
-/
mutual
/-- Post-elaboration invariant: returns true iff the expression tree contains
    no unresolved load calls (`call (resolve "load") _`) and every dot edge
    satisfies the elaborated dot-edge contract. Runtime `Expr.stringLiteral`
    nodes are allowed as ordinary first-class values.
    An AST satisfying this predicate is ready for semantic evaluation. -/
partial def postElabInvariant : Expr -> Bool
  | .stringLiteral _ => true
  | .unary _ e       => postElabInvariant e
  | .binary _ a b    => postElabInvariant a && postElabInvariant b
  | .index a b       => postElabInvariant a && postElabInvariant b
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
  | .mk _ _ opens props output =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      output.all postElabInvariant
  | .conditional _ opens branches =>
      opens.all postElabInvariant &&
      branches.all (fun b => postElabInvariantAlg b.body)
end

end KatLang
